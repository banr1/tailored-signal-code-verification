/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaProof
public import VerifiedLibraries.Mallocng.Proofs.TryAvailHelpers

/-!
# Invariant Helpers for Placed `alloc_group`

Proves `MallocngWFInflight` congruence and domain-extension lemmas (`activeWf_after_allocGroup`,
`slotWf_congr`, `unchanged_outside_claimed_slot`, `extendDom`, `extendDom_spec`) for
`alloc_group` inside placed `alloc_slot`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## `ActiveClassWf` and `SlotWf` congruence after `alloc_group` -/

theorem activeWf_after_allocGroup {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st st' : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {sc : Nat} (hscA : sc < st.ctx.active.length) (hscL : sc < st.activeLists.length)
    (hEmptyAct : st.activeLists[sc]'hscL = [])
    {m : BitVec 64} (hmNe : m ≠ 0#64) (hmFresh : m ∉ st.groups.map (·.metaPtr))
    {cg : GroupDesc} (hcgMeta : cg.metaPtr = m) (hcgPrev : cg.prev = m) (hcgNext : cg.next = m)
    (hcgSc : cg.sc = sc) (hcgActPos : cg.activeIdx < cg.lastIdx → 0 < sc)
    {f : GroupDesc → GroupDesc}
    (hfFields : ∀ g ∈ st.groups,
      (f g).metaPtr = g.metaPtr ∧ (f g).prev = g.prev ∧ (f g).next = g.next ∧
      (f g).sc = g.sc ∧ (f g).availMask = g.availMask ∧ (f g).freedMask = g.freedMask ∧
      (f g).activeByte = g.activeByte ∧ (f g).lastIdx = g.lastIdx)
    (hstGroups : st'.groups = cg :: st.groups.map f)
    (hstAct : st'.ctx.active = st.ctx.active.set sc m)
    (hstLists : st'.activeLists = st.activeLists.set sc [m])
    (sc₀ : Nat) (h1 : sc₀ < st'.ctx.active.length) (h2 : sc₀ < st'.activeLists.length) :
    ActiveClassWf st' sc₀ (st'.ctx.active[sc₀]'h1) (st'.activeLists[sc₀]'h2) := by
  have hFindMap : ∀ {x : BitVec 64} {gs : List GroupDesc},
      (∀ g ∈ gs, (f g).metaPtr = g.metaPtr ∧ (f g).prev = g.prev ∧ (f g).next = g.next) →
      ((gs.map f).find? (·.metaPtr == x)).map (fun g => (g.metaPtr, g.prev, g.next)) =
      (gs.find? (·.metaPtr == x)).map (fun g => (g.metaPtr, g.prev, g.next)) := by
    intro x gs hfg
    induction gs with
    | nil => rfl
    | cons g rest ih =>
      obtain ⟨hm0, hp0, hn0⟩ := hfg g (List.Mem.head _)
      simp only [List.map_cons, List.find?_cons, hm0]
      cases g.metaPtr == x with
      | true => simp [hm0, hp0, hn0]
      | false => exact ih (fun y hy => hfg y (List.Mem.tail _ hy))
  by_cases hEq : sc = sc₀
  · subst hEq
    have hOld := hwf.active_wf sc hscA hscL
    rw [hEmptyAct] at hOld
    have hHead : st'.ctx.active[sc]'h1 = m := by simp [hstAct]
    have hList : st'.activeLists[sc]'h2 = [m] := by simp [hstLists]
    rw [hHead, hList]
    have hFindM : findGroupByMeta st' m = some cg := by
      simp [findGroupByMeta, hstGroups, hcgMeta]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [List.mem_singleton.mp hx]
      exact ⟨cg, by simp [hstGroups], hcgMeta, hcgSc⟩
    · simpa [hFindM, hcgMeta, hcgPrev, hcgNext] using CircularDllWf.singleton hmNe
    · simp [hFindM]
    · intro g' hg' hg'Sc
      rw [hstGroups, List.mem_cons] at hg'
      rcases hg' with rfl | hg'Map
      · simp [hcgMeta, hcgPrev, hcgNext, hmNe]
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'Map
        obtain ⟨hmG, hpG, hnG, hscG, havG, hfrG, hactBG, hlastG⟩ := hfFields g hg
        have hgSc : g.sc = sc := hscG ▸ hg'Sc
        have hgNeM : g.metaPtr ≠ m := fun h => hmFresh (h ▸ List.mem_map_of_mem hg)
        have hNotIn : (f g).metaPtr ∉ ([m] : List (BitVec 64)) := by simp [hmG, hgNeM]
        have hOldG := hOld.2.2.2.1 g hg hgSc
        have hNotNil : g.metaPtr ∉ ([] : List (BitVec 64)) := List.not_mem_nil
        have hpn0 := hOldG.1.mp hNotNil
        obtain ⟨hav0, hfr0, hact0⟩ := hOldG.2 hNotNil
        have hActEq : (f g).activeIdx = (f g).lastIdx := by
          unfold GroupDesc.activeIdx at hact0 ⊢; rw [hactBG, hlastG]; exact hact0
        exact ⟨⟨fun _ => ⟨hpG.trans hpn0.1, hnG.trans hpn0.2⟩, fun _ => hNotIn⟩,
          fun _ => ⟨havG.trans hav0, hfrG.trans hfr0, hActEq⟩⟩
    · intro i hi hpos; simp at hi; omega
    · intro g₁ hg₁ g₂ hg₂ hs₁ hs₂ ha₁ ha₂
      have hIsCg : ∀ g' ∈ st'.groups, g'.sc = sc → g'.activeIdx < g'.lastIdx → g'.metaPtr = m := by
        intro g' hg' hsc' hlt'; rw [hstGroups, List.mem_cons] at hg'
        rcases hg' with rfl | hg'Map
        · exact hcgMeta
        · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'Map
          obtain ⟨_, _, _, hscG, _, _, hactBG, hlastG⟩ := hfFields g hg
          have hOldG := ((hOld.2.2.2.1 g hg (hscG ▸ hsc')).2 List.not_mem_nil).2.2
          unfold GroupDesc.activeIdx at hlt' hOldG; rw [hactBG, hlastG] at hlt'; omega
      rw [hIsCg g₁ hg₁ hs₁ ha₁, hIsCg g₂ hg₂ hs₂ ha₂]
    · intro g' hg' hsc' hlt'; rw [hstGroups, List.mem_cons] at hg'
      rcases hg' with rfl | hg'Map
      · exact ⟨by simp [hcgMeta], hcgActPos hlt'⟩
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'Map
        obtain ⟨_, _, _, hscG, _, _, hactBG, hlastG⟩ := hfFields g hg
        have hOldG := ((hOld.2.2.2.1 g hg (hscG ▸ hsc')).2 List.not_mem_nil).2.2
        unfold GroupDesc.activeIdx at hlt' hOldG; rw [hactBG, hlastG] at hlt'; omega
  · have h1Old : sc₀ < st.ctx.active.length := by simpa [hstAct] using h1
    have h2Old : sc₀ < st.activeLists.length := by simpa [hstLists] using h2
    have hHead : st'.ctx.active[sc₀]'h1 = st.ctx.active[sc₀]'h1Old := by simp [hstAct, List.getElem_set_ne hEq]
    have hList : st'.activeLists[sc₀]'h2 = st.activeLists[sc₀]'h2Old := by simp [hstLists, List.getElem_set_ne hEq]
    rw [hHead, hList]; have hOld := hwf.active_wf sc₀ h1Old h2Old
    have hFmAux : ∀ (xs : List (BitVec 64)), (∀ x ∈ xs, ∃ g ∈ st.groups, g.metaPtr = x ∧ g.sc = sc₀) →
        (xs.filterMap fun x => (findGroupByMeta st' x).map fun g => (g.metaPtr, g.prev, g.next)) =
        (xs.filterMap fun x => (findGroupByMeta st x).map fun g => (g.metaPtr, g.prev, g.next)) := by
      intro xs hxs; induction xs with
      | nil => rfl
      | cons x rest ih =>
        obtain ⟨gx, hgx, hgxM, _⟩ := hxs x (List.Mem.head _)
        have hBeqF : (cg.metaPtr == x) = false :=
          beq_false_of_ne (by rw [hcgMeta]; exact fun h => hmFresh (h ▸ hgxM ▸ List.mem_map_of_mem hgx))
        have hHeadEq : ((findGroupByMeta st' x).map fun g => (g.metaPtr, g.prev, g.next)) =
            ((findGroupByMeta st x).map fun g => (g.metaPtr, g.prev, g.next)) := by
          simp only [findGroupByMeta, hstGroups, List.find?_cons, hBeqF]
          exact hFindMap (fun g hg => ⟨(hfFields g hg).1, (hfFields g hg).2.1, (hfFields g hg).2.2.1⟩)
        simp only [List.filterMap_cons, hHeadEq, ih (fun y hy => hxs y (List.Mem.tail _ hy))]
    have hFmEq := hFmAux _ hOld.1
    refine ⟨?_, hFmEq ▸ hOld.2.1, hFmEq ▸ hOld.2.2.1, ?_, ?_, ?_, ?_⟩
    · intro x hx; obtain ⟨g, hg, hgm, hgs⟩ := hOld.1 x hx; obtain ⟨hmG, _, _, hscG, _⟩ := hfFields g hg
      exact ⟨f g, by rw [hstGroups]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hg), hmG.trans hgm, hscG.trans hgs⟩
    · intro g' hg' hg'Sc; rw [hstGroups, List.mem_cons] at hg'
      rcases hg' with rfl | hg'Map
      · exact absurd (hcgSc.symm.trans hg'Sc) hEq
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'Map
        obtain ⟨hmG, hpG, hnG, hscG, havG, hfrG, hactBG, hlastG⟩ := hfFields g hg
        have hActEq : (f g).activeIdx = g.activeIdx := by unfold GroupDesc.activeIdx; rw [hactBG]
        rw [hmG, hpG, hnG, havG, hfrG, hActEq, hlastG]; exact hOld.2.2.2.1 g hg (hscG ▸ hg'Sc)
    · intro i hi hpos g' hg' hg'M; rw [hstGroups, List.mem_cons] at hg'
      rcases hg' with rfl | hg'Map
      · obtain ⟨gx, hgx, hgxM, _⟩ := hOld.1 _ (List.getElem_mem hi)
        exact absurd (hgxM.trans (hg'M.symm.trans hcgMeta)) (fun h => hmFresh (h ▸ List.mem_map_of_mem hgx))
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'Map; obtain ⟨hmG, _, _, _, havG, hfrG, _, _⟩ := hfFields g hg
        rw [havG, hfrG]; exact hOld.2.2.2.2.1 i hi hpos g hg (hmG ▸ hg'M)
    · intro g₁ hg₁ g₂ hg₂ hs₁ hs₂ ha₁ ha₂; rw [hstGroups, List.mem_cons] at hg₁ hg₂
      rcases hg₁ with rfl | hg₁Map
      · exact absurd (hcgSc.symm.trans hs₁) hEq
      · rcases hg₂ with rfl | hg₂Map
        · exact absurd (hcgSc.symm.trans hs₂) hEq
        · obtain ⟨g1, hg1, rfl⟩ := List.mem_map.mp hg₁Map; obtain ⟨g2, hg2, rfl⟩ := List.mem_map.mp hg₂Map
          obtain ⟨hm1, _, _, hsc1, _, _, hab1, hl1⟩ := hfFields g1 hg1
          obtain ⟨hm2, _, _, hsc2, _, _, hab2, hl2⟩ := hfFields g2 hg2
          unfold GroupDesc.activeIdx at ha₁ ha₂; rw [hab1, hl1] at ha₁; rw [hab2, hl2] at ha₂; rw [hm1, hm2]
          exact hOld.2.2.2.2.2.1 g1 hg1 g2 hg2 (hsc1 ▸ hs₁) (hsc2 ▸ hs₂) ha₁ ha₂
    · intro g' hg' hs' ha'; rw [hstGroups, List.mem_cons] at hg'
      rcases hg' with rfl | hg'Map
      · exact absurd (hcgSc.symm.trans hs') hEq
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'Map; obtain ⟨hmG, _, _, hscG, _, _, habG, hlG⟩ := hfFields g hg
        unfold GroupDesc.activeIdx at ha'; rw [habG, hlG] at ha'; rw [hmG]
        exact hOld.2.2.2.2.2.2 g hg (hscG ▸ hs') ha'

theorem slotWf_congr {st st' : MallocngSt} {g g' : GroupDesc}
    (hgWf : GroupWf st g) {idx : Nat} (hIdx : idx < g.slots.length) {s : SlotState}
    (hFields : g'.metaPtr = g.metaPtr ∧ g'.mem = g.mem ∧ g'.sc = g.sc ∧ g'.maplen = g.maplen ∧
      g'.lastIdx = g.lastIdx ∧ g'.availMask = g.availMask ∧ g'.freedMask = g.freedMask ∧
      g'.activeByte = g.activeByte)
    (hOld : SlotWf st g idx s)
    (hZStart : st'.byteVal (g.slotStart idx - 4#64) = st.byteVal (g.slotStart idx - 4#64))
    (hNested : ∀ cm, s = .liveNested cm →
      ∀ cg₀ ∈ st.groups, cg₀.metaPtr = cm → cg₀.parentMeta = some g.metaPtr →
        (∀ a : BitVec 64, InRegion (cg₀.mem - 4#64) 4 a → st'.byteVal a = st.byteVal a) ∧
        ∃ cg₁ ∈ st'.groups, cg₁.metaPtr = cg₀.metaPtr ∧ cg₁.parentMeta = cg₀.parentMeta ∧
          cg₁.mem = cg₀.mem ∧ cg₁.nestedCap = cg₀.nestedCap)
    (hUser : ∀ u r e, s = .liveUser u r e →
      ∀ a : BitVec 64, InRegion (g.slotStart idx - 4#64) g.stride a → st'.byteVal a = st.byteVal a)
    (hOv : ∀ u r e, s = .liveUser u r e → st'.liveMap.ov u = st.liveMap.ov u := by intros; rfl) :
    SlotWf st' g' idx s := by
  obtain ⟨hmG, hmemG, hscG, hmapG, hlastG, havG, hfrG, hactBG⟩ := hFields
  have hStrideG : g'.stride = g.stride := by unfold GroupDesc.stride; rw [hlastG, hmapG, hscG]
  have hStorG : g'.storage = g.storage := by unfold GroupDesc.storage; rw [hmemG]
  have hStartG : g'.slotStart idx = g.slotStart idx := by unfold GroupDesc.slotStart; rw [hStorG, hStrideG]
  have hEndG : g'.slotEnd idx = g.slotEnd idx := by unfold GroupDesc.slotEnd; rw [hStartG, hStrideG]
  have hActIdxG : g'.activeIdx = g.activeIdx := by unfold GroupDesc.activeIdx; rw [hactBG]
  have hGs := group_slot_toNat hgWf; have hIdxCnt : idx < g.cnt := by rw [← hgWf.2.2.1]; exact hIdx
  obtain ⟨hStartEq, hEndEq, _⟩ := hGs.2.2.2.2.2 idx hIdxCnt
  have hStride16 : 16 ≤ g.stride := hGs.1; have hStorEq : g.storage.toNat = g.mem.toNat + 16 := hGs.2.2.1
  have hMem4096 : 4096 ≤ g.mem.toNat := hgWf.2.2.2.2.1
  have hEndLim : (g.slotEnd idx).toNat ≤ 2 ^ 48 := by
    have : (idx + 1) * g.stride ≤ g.cnt * g.stride := Nat.mul_le_mul_right _ hIdxCnt
    have := hGs.2.2.2.1; have := hGs.2.2.2.2.1; have := hgWf.2.2.2.2.2.2.1; omega
  clear hgWf hGs
  obtain ⟨hZ0, hAv0, hFr0, hInact0, hBody⟩ := hOld
  refine ⟨by rw [hStartG, hZStart]; exact hZ0, by rw [havG]; exact hAv0,
    by rw [hfrG]; exact hFr0, by rw [hActIdxG]; exact hInact0, ?_⟩
  cases s with
  | freeAvail | freeInactive | claimed => trivial
  | liveNested cm =>
    obtain ⟨hsc48, cg₀, hcg₀, hcm, hpar, hlo, hal, hhi, hcap, hoff, hb4, hb3, hb2⟩ := hBody
    obtain ⟨hCgBytes, cg₁, hcg₁, hm1, hp1, hmem1, hcap1⟩ := hNested cm rfl cg₀ hcg₀ hcm hpar
    have hSub4 := sub_ofNat_toNat (x := cg₀.mem) (k := 4) (by omega)
    have hSub3 := sub_ofNat_toNat (x := cg₀.mem) (k := 3) (by omega)
    have hSub2 := sub_ofNat_toNat (x := cg₀.mem) (k := 2) (by omega)
    have hIn4 : InRegion (cg₀.mem - 4#64) 4 (cg₀.mem - 4#64) := (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩
    have hIn3 : InRegion (cg₀.mem - 4#64) 4 (cg₀.mem - 3#64) := (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩
    have hRead2 : readBytesFromMap st'.byteVal (cg₀.mem - 2#64) 2 = readBytesFromMap st.byteVal (cg₀.mem - 2#64) 2 :=
      readBytesFromMap_congr (by decide) fun a ha => by
        have haB := (inRegion_bounds (by omega)).mp ha
        exact hCgBytes a ((inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩)
    exact ⟨hscG ▸ hsc48, cg₁, hcg₁, hm1.trans hcm, by rw [hp1, hmG]; exact hpar,
      by rw [hStartG, hmem1]; exact hlo, by rw [hStartG, hmem1]; exact hal,
      by rw [hmem1, hcap1, hEndG]; exact hhi, by rw [hcap1, hscG]; exact hcap,
      by rw [hmem1, hStorG]; exact hoff, by rw [hmem1, hCgBytes _ hIn4]; exact hb4,
      by rw [hmem1, hCgBytes _ hIn3]; exact hb3, by rw [hmem1, hStorG, hRead2]; exact hb2⟩
  | liveUser u r e =>
    have hU := hUser u r e rfl
    have hStartSub4 := sub_ofNat_toNat (x := g.slotStart idx) (k := 4) (by omega)
    have hSpan : ∀ a : BitVec 64, (g.slotStart idx).toNat - 4 ≤ a.toNat → a.toNat < (g.slotEnd idx).toNat →
        st'.byteVal a = st.byteVal a := fun a h1 h2 => by
      have : idx * g.stride + g.stride = (idx + 1) * g.stride := by rw [Nat.add_mul, Nat.one_mul]
      exact hU a ((inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩)
    obtain ⟨hBlk, hLoU, hHiU, hMaxE, hOffB, hRes31, hNom, hSc63, hb3, hOffBr, hRes1, hRes5⟩ := hBody
    have hUSub3 := sub_ofNat_toNat (x := u) (k := 3) (by omega)
    have hUSub4 := sub_ofNat_toNat (x := u) (k := 4) (by omega)
    have hUSub2 := sub_ofNat_toNat (x := u) (k := 2) (by omega)
    have hInU3 := hSpan (u - 3#64) (by omega) (by omega)
    have hInU4 := hSpan (u - 4#64) (by omega) (by omega)
    have hReadU2 : readBytesFromMap st'.byteVal (u - 2#64) 2 = readBytesFromMap st.byteVal (u - 2#64) 2 :=
      readBytesFromMap_congr (by decide) fun a ha => by
        have haB := (inRegion_bounds (by omega)).mp ha; exact hSpan a (by omega) (by omega)
    simp only [hStartG, hEndG, hStorG, hscG, hmapG]
    refine ⟨hBlk, hLoU, hHiU, hMaxE, by rw [hOv u r e rfl]; exact hOffB, hRes31, hNom, hSc63,
      hInU3 ▸ hb3, ?_, ?_, ?_⟩
    · by_cases hOffLe : (u.toNat - g.storage.toNat) / 16 ≤ 65535
      · simp only [hOffLe, ↓reduceIte] at hOffBr ⊢; exact ⟨hInU4 ▸ hOffBr.1, hReadU2 ▸ hOffBr.2⟩
      · simp only [hOffLe, ↓reduceIte] at hOffBr ⊢
        have hIdx0 : idx = 0 := hOffBr.2.1; have hUGe16 : g.storage.toNat + 16 ≤ u.toNat := by omega
        have hUSub8 := sub_ofNat_toNat (x := u) (k := 8) (by omega)
        have hReadU8 : readBytesFromMap st'.byteVal (u - 8#64) 4 = readBytesFromMap st.byteVal (u - 8#64) 4 :=
          readBytesFromMap_congr (by decide) fun a ha => by
            have haB := (inRegion_bounds (by omega)).mp ha; exact hSpan a (by subst hIdx0; omega) (by omega)
        exact ⟨hOffBr.1, hOffBr.2.1, hOffBr.2.2.1, hInU4 ▸ hOffBr.2.2.2.1,
          hReadU2 ▸ hOffBr.2.2.2.2.1, hReadU8 ▸ hOffBr.2.2.2.2.2⟩
    · intro hR1; have hUAddR := add_ofNat_toNat (x := u) (k := r) (by omega)
      exact (hSpan (u + BitVec.ofNat 64 r) (by omega) (by omega)) ▸ hRes1 hR1
    · intro hR5
      have hESub5 := sub_ofNat_toNat (x := g.slotEnd idx) (k := 5) (by omega)
      have hESub4 := sub_ofNat_toNat (x := g.slotEnd idx) (k := 4) (by omega)
      have hEqE5 := hSpan (g.slotEnd idx - 5#64) (by omega) (by omega)
      have hReadE4 : readBytesFromMap st'.byteVal (g.slotEnd idx - 4#64) 4 =
          readBytesFromMap st.byteVal (g.slotEnd idx - 4#64) 4 :=
        readBytesFromMap_congr (by decide) fun a ha => by
          have haB := (inRegion_bounds (by omega)).mp ha; exact hSpan a (by omega) (by omega)
      exact ⟨hEqE5 ▸ (hRes5 hR5).1, hReadE4 ▸ (hRes5 hR5).2⟩

/-! ## Disjointness outside claimed slot and `extendDom` -/

theorem unchanged_outside_claimed_slot {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {m : BitVec 64} (hm : m ∈ st.reservedMetas) {pg : GroupDesc} (hpg : pg ∈ st.groups)
    {pIdx : Nat} (hpIdx : pIdx < pg.slots.length) (hClaimed : pg.slots[pIdx]'hpIdx = .claimed)
    {val' : BitVec 64 → BitVec 8}
    (hValOut : ∀ a : BitVec 64, ¬ InRegion m 40 a →
      ¬ ((pg.slotStart pIdx - 4#64).toNat < a.toNat ∧ a.toNat < (pg.slotEnd pIdx).toNat) →
      val' a = st.byteVal a) :
    (∀ ma ∈ st.metaAreas, readBytesFromMap val' ma.base 24 = readBytesFromMap st.byteVal ma.base 24) ∧
    (∀ ap ∈ st.availMetaPages, readBytesFromMap val' ap 4096 = readBytesFromMap st.byteVal ap 4096) ∧
    (∀ fm ∈ st.freeMetas, readBytesFromMap val' fm.ptr 40 = readBytesFromMap st.byteVal fm.ptr 40) ∧
    (∀ bm ∈ st.bumpMetas, readBytesFromMap val' bm 40 = readBytesFromMap st.byteVal bm 40) ∧
    (∀ g ∈ st.groups,
      readBytesFromMap val' g.metaPtr 40 = readBytesFromMap st.byteVal g.metaPtr 40 ∧
      readBytesFromMap val' g.mem 8 = readBytesFromMap st.byteVal g.mem 8 ∧
      val' (g.mem + 8#64) = st.byteVal (g.mem + 8#64) ∧
      val' (g.slotEnd g.lastIdx) = st.byteVal (g.slotEnd g.lastIdx) ∧
      ∀ idx : Nat, (hIdx : idx < g.slots.length) →
        val' (g.slotStart idx - 4#64) = st.byteVal (g.slotStart idx - 4#64) ∧
        (∀ cm, g.slots[idx]'hIdx = .liveNested cm →
          ∀ cg₀ ∈ st.groups, cg₀.metaPtr = cm → cg₀.parentMeta = some g.metaPtr →
            ∀ a : BitVec 64, InRegion (cg₀.mem - 4#64) 4 a → val' a = st.byteVal a) ∧
        (∀ u r e, g.slots[idx]'hIdx = .liveUser u r e →
          ∀ a : BitVec 64, InRegion (g.slotStart idx - 4#64) g.stride a → val' a = st.byteVal a)) := by
  have hpgWf := hwf.groups_wf pg hpg; have hpCnt : pIdx < pg.cnt := by rw [← hpgWf.2.2.1]; exact hpIdx
  have hpgGs := group_slot_toNat hpgWf; obtain ⟨hpgStartEq, hpgEndEq, _⟩ := hpgGs.2.2.2.2.2 pIdx hpCnt
  have hpgMem4096 := hpgWf.2.2.2.2.1
  have hpgStartSub4 := sub_ofNat_toNat (x := pg.slotStart pIdx) (k := 4) (by omega)
  have hpgEndM : (pg.slotEnd pIdx).toNat ≤ (pg.slotEnd pg.lastIdx).toNat := by
    have : (pIdx + 1) * pg.stride ≤ pg.cnt * pg.stride := Nat.mul_le_mul_right _ hpCnt; omega
  obtain ⟨grPg, hgrPg, hgrPgPos, hGrPgLo, _, hGrPgStrict⟩ := group_root_containment hwf hpg
  have hGrPgBound := (hwf.groups_wf grPg hgrPg).2.2.2.2.2.2.1
  have hGrPgTot : grPg.totalBytes = grPg.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPgPos]
  obtain ⟨hmLo, _, hmHi, hmNotGrp, ⟨maM, hmaM, hInMaM⟩, _, _, _, hResDisjGrp⟩ := reservedMeta_info hwf hm
  obtain ⟨_, _, _, _, hUsedNd, hUsedAll⟩ := hwf.free_bump_metas_wf
  have hmAll : m ∈ allMetaSlots st := (hUsedAll m).mp (List.mem_append_right _ hm)
  obtain ⟨_, _, _, _, hDisjAllSlots⟩ := allMetaSlots_info hwf hmAll
  have hInGrPg : ∀ a : BitVec 64, (pg.slotStart pIdx - 4#64).toNat < a.toNat ∧ a.toNat < (pg.slotEnd pIdx).toNat →
      InRegion grPg.mem (grPg.maplen * 4096) a ∧ GroupContains pg a.toNat :=
    fun a ⟨_, _⟩ => ⟨(inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hMetaPageOut : ∀ ma ∈ st.metaAreas, ∀ a : BitVec 64, InRegion ma.base 4096 a →
      ¬ ((pg.slotStart pIdx - 4#64).toNat < a.toNat ∧ a.toNat < (pg.slotEnd pIdx).toNat) :=
    fun ma hma a ha hInt => DisjointRegions.not_both
      (metaArea_disjoint_rootGroup hwf hma hgrPg hgrPgPos) ha (hInGrPg a hInt).1
  have hSlotNeM : ∀ p ∈ allMetaSlots st, p ≠ m →
      readBytesFromMap val' p 40 = readBytesFromMap st.byteVal p 40 := fun p hp hpNe => by
    obtain ⟨_, _, _, ⟨maP, hmaP, hInMaP⟩, _⟩ := allMetaSlots_info hwf hp
    exact readBytesFromMap_congr (by decide) fun a ha => hValOut a
      (fun haM => DisjointRegions.not_both (hDisjAllSlots p hp hpNe) haM ha)
      (hMetaPageOut maP hmaP a (hInMaP a ha))
  have hSlotEq : ∀ {g : GroupDesc}, GroupWf st g → ∀ {i j : Nat}, i < g.cnt → j < g.cnt →
      (g.slotStart i).toNat - 4 < (g.slotEnd j).toNat →
      (g.slotStart j).toNat - 4 < (g.slotEnd i).toNat → i = j := by
    intro g hgW i j hi hj h1 h2
    have hGs := group_slot_toNat hgW; have := hgW.2.2.2.2.1; have := hGs.1
    have := hGs.2.2.2.2.2 i hi; have := hGs.2.2.2.2.2 j hj
    by_cases hlt : i < j
    · have : (i + 1) * g.stride ≤ j * g.stride := Nat.mul_le_mul_right _ hlt; omega
    · by_cases hgt : j < i
      · have : (j + 1) * g.stride ≤ i * g.stride := Nat.mul_le_mul_right _ hgt; omega
      · omega
  have hGrpElemNoM : ∀ g ∈ st.groups, ∀ a : BitVec 64,
      g.mem.toNat ≤ a.toNat → a.toNat ≤ (g.slotEnd g.lastIdx).toNat → ¬ InRegion m 40 a := by
    intro g hg a hlo hhi haM
    obtain ⟨gr, hgr, hgrPos, _, _, _⟩ := group_root_containment hwf hg
    have hGrB := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
    have hGrT : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPos]
    exact (hResDisjGrp gr hgr).2 a haM (by rw [hGrT]; exact (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ma hma
    obtain ⟨_, hmaAl, hmaHi, _⟩ := hwf.metaAreas_wf.2.1 ma hma
    unfold allMetaSlots at hmAll
    obtain ⟨ma0, hma0, hmem0⟩ := List.mem_flatMap.mp hmAll
    obtain ⟨k0, hk0, hmEqSlot⟩ := List.mem_map.mp hmem0
    have hk101 := List.mem_range.mp hk0
    obtain ⟨hma0Lo, hma0Al, hma0Hi, _⟩ := hwf.metaAreas_wf.2.1 ma0 hma0
    have hSlot0Eq := (slotAddr_bounds hma0Lo hma0Al hma0Hi hk101).1
    refine readBytesFromMap_congr (by decide) fun a ha => ?_
    have haB := (inRegion_bounds (by omega)).mp ha
    refine hValOut a (fun haM => ?_) (hMetaPageOut ma hma a ((inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩))
    have haMB := (inRegion_bounds (by omega)).mp haM
    rw [← hmEqSlot, hSlot0Eq] at haMB
    have haPage0 : ma0.base.toNat + 24 ≤ a.toNat ∧ a.toNat < ma0.base.toNat + 4096 := by omega
    clear hk0 hk101 hSlot0Eq hmEqSlot haMB haM ha; omega
  · intro ap hap
    have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd
    rw [List.append_assoc, List.append_assoc, PairwiseDisjointRegions.append_iff] at hpd
    have hpd2 := (PairwiseDisjointRegions.append_iff.mp hpd.2.1).2.1
    rw [PairwiseDisjointRegions.append_iff] at hpd2
    have hApMem : (ap, 4096) ∈ st.availMetaPages.map (fun x => (x, 4096)) := List.mem_map_of_mem hap
    have hGrF : grPg ∈ st.groups.filter (fun g => decide (0 < g.maplen)) :=
      List.mem_filter.mpr ⟨hgrPg, decide_eq_true hgrPgPos⟩
    have hDisjMaAp := hpd.2.2 (maM.base, 4096) (List.mem_map_of_mem hmaM) (ap, 4096)
      (List.mem_append_right _ (List.mem_append_left _ hApMem))
    have hDisjApGr := hpd2.2.2 (ap, 4096) hApMem (grPg.mem, grPg.maplen * 4096) (List.mem_map_of_mem hGrF)
    exact readBytesFromMap_congr (by decide) fun a ha => hValOut a
      (fun haM => DisjointRegions.not_both hDisjMaAp (hInMaM a haM) ha)
      (fun hInt => DisjointRegions.not_both hDisjApGr ha (hInGrPg a hInt).1)
  · intro fm hfm
    have hfmMem : fm.ptr ∈ st.freeMetas.map (·.ptr) := List.mem_map_of_mem hfm
    rw [List.nodup_append] at hUsedNd
    exact hSlotNeM fm.ptr ((hUsedAll fm.ptr).mp (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hfmMem)))) fun h =>
      hUsedNd.2.2 fm.ptr (List.mem_append_left _ (List.mem_append_right _ hfmMem)) m hm h
  · intro bm hbm
    rw [List.nodup_append] at hUsedNd
    exact hSlotNeM bm ((hUsedAll bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm))) fun h =>
      hUsedNd.2.2 bm (List.mem_append_right _ hbm) m hm h
  · intro g hg
    have hgWf := hwf.groups_wf g hg; have hgGs := group_slot_toNat hgWf
    have hgMem4096 := hgWf.2.2.2.2.1; have hgStride16 := hgGs.1; have hgEndEq := hgGs.2.2.2.1
    have hgEndLim : (g.slotEnd g.lastIdx).toNat ≤ 2 ^ 48 := by
      have := hgGs.2.2.2.2.1; have := hgWf.2.2.2.2.2.2.1; omega
    have hgMemLeEnd : g.mem.toNat + 16 ≤ (g.slotEnd g.lastIdx).toNat := by
      have : 1 * 16 ≤ g.cnt * g.stride := Nat.mul_le_mul hgGs.2.1 hgStride16; omega
    have hgMetaAll := (hUsedAll g.metaPtr).mp (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map_of_mem hg))))
    have hClassify : ∀ a : BitVec 64,
        g.mem.toNat ≤ a.toNat → a.toNat ≤ (g.slotEnd g.lastIdx).toNat →
        (pg.slotStart pIdx - 4#64).toNat < a.toNat ∧ a.toNat < (pg.slotEnd pIdx).toNat →
        g = pg ∨ ∃ ch ∈ st.groups, ∃ k : Nat, ∃ hk : k < g.slots.length,
          g.slots[k]'hk = .liveNested ch.metaPtr ∧ (g.slotStart k).toNat ≤ ch.mem.toNat ∧
          ch.mem.toNat ≤ pg.mem.toNat ∧ (pg.slotEnd pIdx).toNat ≤ (g.slotEnd k).toNat := by
      intro a hlo hhi hInt
      rcases comparable_of_groupContains hwf hpg hg (hInGrPg a hInt).2 ⟨hlo, hhi⟩ with rfl | hAncPgG | hAncGPg
      · exact Or.inl rfl
      · obtain ⟨_, _, k, hk, hsK, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncPgG hpg
        have hkC := hpgGs.2.2.2.2.2 k (hpgWf.2.2.1 ▸ hk)
        have hkEq := hSlotEq hpgWf (hpgWf.2.2.1 ▸ hk) hpCnt (by omega) (by omega)
        subst hkEq; rw [hClaimed] at hsK; cases hsK
      · obtain ⟨ch, hch, k, hk, hsK, hLoK, hMemChPg, _, _⟩ := strictAncestor_slot_bounds hwf hAncGPg hg
        exact Or.inr ⟨ch, hch, k, hk, hsK, hLoK, hMemChPg, by omega⟩
    refine ⟨hSlotNeM g.metaPtr hgMetaAll (fun h => hmNotGrp (h ▸ List.mem_map_of_mem hg)), ?_, ?_, ?_, ?_⟩
    · refine readBytesFromMap_congr (by decide) fun a ha => ?_
      have haB := (inRegion_bounds (by omega)).mp ha
      refine hValOut a (hGrpElemNoM g hg a (by omega) (by omega)) fun hInt => ?_
      rcases hClassify a (by omega) (by omega) hInt with rfl | ⟨_, _, k, hk, _, _, _, _⟩
      · omega
      · have := (hgGs.2.2.2.2.2 k (hgWf.2.2.1 ▸ hk)).1; omega
    · have hAdd8 := add_ofNat_toNat (x := g.mem) (k := 8) (by omega)
      refine hValOut _ (hGrpElemNoM g hg _ (by omega) (by omega)) fun hInt => ?_
      rcases hClassify _ (by omega) (by omega) hInt with rfl | ⟨_, _, k, hk, _, _, _, _⟩
      · omega
      · have := (hgGs.2.2.2.2.2 k (hgWf.2.2.1 ▸ hk)).1; omega
    · refine hValOut _ (hGrpElemNoM g hg _ (by omega) (by omega)) fun hInt => ?_
      rcases hClassify _ (by omega) (by omega) hInt with rfl | ⟨_, _, k, hk, _, _, _, _⟩
      · omega
      · have hkCnt : k < g.cnt := hgWf.2.2.1 ▸ hk
        have := (hgGs.2.2.2.2.2 k hkCnt).2.1
        have : (k + 1) * g.stride ≤ g.cnt * g.stride := Nat.mul_le_mul_right _ hkCnt; omega
    · intro idx hIdx
      have hIdxCnt : idx < g.cnt := hgWf.2.2.1 ▸ hIdx
      obtain ⟨hIdxStart, hIdxEnd, hSub4⟩ := hgGs.2.2.2.2.2 idx hIdxCnt
      have hIdxEndLe : (g.slotEnd idx).toNat ≤ (g.slotEnd g.lastIdx).toNat := by
        have : (idx + 1) * g.stride ≤ g.cnt * g.stride := Nat.mul_le_mul_right _ hIdxCnt; omega
      have hIdxBound : g.mem.toNat ≤ (g.slotStart idx - 4#64).toNat ∧
          (g.slotStart idx - 4#64).toNat ≤ (g.slotEnd g.lastIdx).toNat := by
        have : idx * g.stride ≤ g.cnt * g.stride := Nat.mul_le_mul_right _ (Nat.le_of_lt hIdxCnt); omega
      refine ⟨?_, ?_, ?_⟩
      · refine hValOut _ (hGrpElemNoM g hg _ hIdxBound.1 hIdxBound.2) fun hInt => ?_
        rcases hClassify _ hIdxBound.1 hIdxBound.2 hInt with rfl | ⟨_, _, k, hk, _, _, _, _⟩
        · by_cases hle : idx ≤ pIdx
          · have : idx * g.stride ≤ pIdx * g.stride := Nat.mul_le_mul_right _ hle; omega
          · have : (pIdx + 1) * g.stride ≤ idx * g.stride := Nat.mul_le_mul_right _ (by omega); omega
        · obtain ⟨_, _, _⟩ := hgGs.2.2.2.2.2 k (hgWf.2.2.1 ▸ hk)
          by_cases hle : idx ≤ k
          · have : idx * g.stride ≤ k * g.stride := Nat.mul_le_mul_right _ hle; omega
          · have : (k + 1) * g.stride ≤ idx * g.stride := Nat.mul_le_mul_right _ (by omega); omega
      · intro cm hSlot cg₀ hcg₀ hcm _ a ha
        have hBody := (GroupWf.slot_wf hgWf idx hIdx).2.2.2.2; rw [hSlot] at hBody
        obtain ⟨_, cgW, hcgW, hcmW, _, hloW, _, hhiW, _⟩ := hBody
        cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg₀ hcgW (hcm.trans hcmW.symm)
        have hCgSub4 := sub_ofNat_toNat (x := cg₀.mem) (k := 4) (by omega)
        have haB := (inRegion_bounds (by omega)).mp ha
        refine hValOut a (hGrpElemNoM g hg a (by omega) (by omega)) fun hInt => ?_
        rcases hClassify a (by omega) (by omega) hInt with rfl | ⟨ch, hch, k, hk, hsK, _, _, _⟩
        · have hkEq := hSlotEq hpgWf hIdxCnt hpCnt (by omega) (by omega)
          subst hkEq; rw [hClaimed] at hSlot; cases hSlot
        · obtain ⟨_, _, _⟩ := hgGs.2.2.2.2.2 k (hgWf.2.2.1 ▸ hk)
          have hkEq := hSlotEq hgWf hIdxCnt (hgWf.2.2.1 ▸ hk) (by omega) (by omega)
          subst hkEq; rw [hSlot] at hsK; injection hsK with hcmCh
          cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg₀ hch (hcm.trans hcmCh); omega
      · intro u r e hSlot a ha
        have hMul : idx * g.stride + g.stride = (idx + 1) * g.stride := by rw [Nat.add_mul, Nat.one_mul]
        have haB := (inRegion_bounds (by omega)).mp ha
        refine hValOut a (hGrpElemNoM g hg a (by omega) (by omega)) fun hInt => ?_
        rcases hClassify a (by omega) (by omega) hInt with rfl | ⟨_, _, k, hk, hsK, _, _, _⟩
        · have hkEq := hSlotEq hpgWf hIdxCnt hpCnt (by omega) (by omega)
          subst hkEq; rw [hClaimed] at hSlot; cases hSlot
        · obtain ⟨_, _, _⟩ := hgGs.2.2.2.2.2 k (hgWf.2.2.1 ▸ hk)
          have hkEq := hSlotEq hgWf hIdxCnt (hgWf.2.2.1 ▸ hk) (by omega) (by omega)
          subst hkEq; rw [hSlot] at hsK; cases hsK

def extendDom (dom : List (BitVec 64)) (b : BitVec 64) (n : Nat) : List (BitVec 64) :=
  dom ++ (rangeAddrs b n).filter (fun a => !decide (a ∈ dom))

theorem extendDom_spec {st : MallocngSt} {dom : List (BitVec 64)}
    (hNd0 : dom.Nodup)
    (hCov : ∀ a : BitVec 64, (OwnedRwByte st a ∨ OwnedProtNoneByte st a ∨ OwnedMappedByte st a) → a ∈ dom)
    (b : BitVec 64) {n : Nat} (hFit : b.toNat + n ≤ 2 ^ 64) :
    let dom' := extendDom dom b n
    dom'.Nodup ∧
    (∀ a : BitVec 64, a ∈ dom' ↔ a ∈ dom ∨ InRegion b n a) ∧
    ByteMap dom (OwnedRwByte st) st.byteVal = ByteMap dom' (OwnedRwByte st) st.byteVal ∧
    ProtNoneByteMap dom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap dom' (OwnedProtNoneByte st) st.byteVal ∧
    MappedSet dom (OwnedMappedByte st) = MappedSet dom' (OwnedMappedByte st) := by
  have hn : n ≤ 2 ^ 64 := by omega
  have hNotDom : ∀ a ∈ (rangeAddrs b n).filter (fun x => !decide (x ∈ dom)), a ∉ dom := by
    intro a ha; simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at ha
    exact ha.2
  have hNd : (extendDom dom b n).Nodup :=
    List.nodup_append.mpr ⟨hNd0, (nodup_rangeAddrs b hn).filter _,
      fun a haDom c haFilt hEq => hNotDom c haFilt (hEq ▸ haDom)⟩
  have hMem : ∀ a : BitVec 64, a ∈ extendDom dom b n ↔ a ∈ dom ∨ InRegion b n a := fun a => by
    unfold extendDom; rw [List.mem_append, List.mem_filter, mem_rangeAddrs_iff_inRegion b hn]
    by_cases ha : a ∈ dom <;> simp [ha]
  refine ⟨hNd, hMem,
    (SetSep_append_right_empty _ fun a ha h => hNotDom a ha (hCov a (Or.inl h))).symm,
    (SetSep_append_right_empty _ fun a ha h => hNotDom a ha (hCov a (Or.inr (Or.inl h)))).symm,
    (SetSep_append_right_empty _ fun a ha h => hNotDom a ha (hCov a (Or.inr (Or.inr h)))).symm⟩

end VerifiedLibraries.Mallocng.Proofs
