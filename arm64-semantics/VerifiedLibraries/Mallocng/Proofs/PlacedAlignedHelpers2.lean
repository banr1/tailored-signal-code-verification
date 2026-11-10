/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAlignedHelpers
public import VerifiedLibraries.Mallocng.Proofs.InternalPlaced

/-!
# `ByteMap` Focus and Reframe Helpers for `aligned_alloc` and `posix_memalign`

Defines `libcMallocImplPlacedSpec24` (the placed `__libc_malloc_impl` contract with size-class
`24..26` and `63` bounds) and proves `ByteMap` focus, absorption, and exit-reframe lemmas for
`aligned_alloc` and `posix_memalign`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

def libcMallocImplPlacedSpec24 [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat) : Spec Unit :=
  let ok := decide (req ≤ MallocngMaxAllocSize)
  let bf := mallocngAllocBudget ok req b
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜(s0.readReg64 .x0).toNat = req⌝ ∗ stackFrame s0 704 ∗
      MallocngEnv mallocngIface γ maddrs tp brkStart b ivs0 s0
    post := fun _ s0 sf =>
      ⌜MallocngProcPreserved s0 sf ∧
       MallocngMappedDelta 16 (MallocngTightStepBound (if ok then req else 0) b.peakCount) s0.mem sf.mem⌝ ∗
      stackFrame s0 704 ∗
      if req ≤ MallocngMaxAllocSize then
        ∃∗ p : BitVec 64, ∃∗ bs : List (BitVec 8), ∃∗ st' : MallocngSt,
          ⌜sf.readReg64 .x0 = p ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
           MallocngBlockWf p req ∧ bs.length = req ∧
           MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngCountIvsWF bf (dynamicRootRegions st') st' ∧
           ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
             g'.slots[idx]'hIdx = .liveUser p req (max req MallocngMinBlockCost) ∧
             p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
             (g'.isMmapped = true → bs = List.replicate req 0#8) ∧
             (24 ≤ g'.sc ∧ g'.sc ≤ 26 → nominalSlotCap 23 < req) ∧
             (g'.sc = 63 → g'.maplen * 4096 ≤ req + 4115)⌝ ∗
          MallocngRoTablesA maddrs ∗
          MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
          MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ mallocngIface.Block γ p req
      else
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf
    onOom := fun _ s0 sf => ⌜MallocngTightOomCond msvc (if ok then req else 0) b.peakCount s0 sf⌝
  }

def LibcMallocImplPlaced24Stmt : Prop :=
  ∀ [MallocngMultiPlacement] (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9)
      (libcMallocImplPlacedSpec24 γ tp brkStart b ivs0 req)

def alignedSlotKeep (st : MallocngSt) (p : BitVec 64) (eff : Nat) (a : BitVec 64) : Prop :=
  OwnedRwByte st a ∨ InRegion p eff a

instance (st : MallocngSt) (p : BitVec 64) (eff : Nat) : DecidablePred (alignedSlotKeep st p eff) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

theorem alignedAlloc_absorb_user_pre {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {eff effCost : Nat} (hSlot : g.slots[idx]'hIdx = .liveUser p eff effCost)
    {bs : List (BitVec 8)} (hBsLen : bs.length = eff) :
    let bv0 := writeBytesToMap st.byteVal p bs
    ((p ↦ₛ bs) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal) =
      ByteMap st.masterDom (alignedSlotKeep st p eff) bv0 ∧
    (∀ a : BitVec 64, InRegion (g.slotStart idx - 3#64) (g.stride - 1) a →
      alignedSlotKeep st p eff a ∧ a ∈ st.masterDom) ∧
    (∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bv0 a = st.byteVal a) ∧
    (∀ a : BitVec 64, a.toNat < p.toNat → bv0 a = st.byteVal a) := by
  dsimp only []
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hGWf := hwf.groups_wf g hg
  have ⟨_, _, hStNat, hSub4Nat, hEnNat, _, hEn48, _, _⟩ := group_slot_bounds hGWf hIdx
  have ⟨hStrGe16, _⟩ := group_stride_pos_and_align hGWf
  have hSMG : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hSub3Nat := bv64_sub_toNat (a := g.slotStart idx) (n := 3) (by omega)
  have hSWf := hGWf.slot_wf idx hIdx; rw [hSlot] at hSWf
  have hPLo := hSWf.2.2.2.2.2.1; have hPHi := hSWf.2.2.2.2.2.2.1
  obtain ⟨rg, hrg, hRgMp, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
  have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hRgMp]
  have hRg48 : rg.mem.toNat + rg.totalBytes ≤ 2 ^ 48 := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
  have hPInDom : ∀ a : BitVec 64, InRegion p bs.length a → a ∈ st.masterDom := fun a ha => by
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp (hBsLen ▸ ha)
    exact hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rg, hrg, hRgMp, (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩⟩)))))
  have hPDisjOwn : ∀ a : BitVec 64, InRegion p bs.length a → ¬ OwnedRwByte st a :=
    fun a ha hOwn => hOwn.2.1 ⟨g, hg, .liveUser p eff effCost, hSlot ▸ List.getElem_mem hIdx, hBsLen ▸ ha⟩
  have hAbsEq : ((p ↦ₛ bs) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal) =
      ByteMap st.masterDom (alignedSlotKeep st p eff) (writeBytesToMap st.byteVal p bs) := by
    rw [ByteMap_absorb_slice hwf.masterDom_wf.1 st.byteVal p bs (by omega) hPInDom hPDisjOwn]
    exact SetSep_congr (fun a _ => by simp [alignedSlotKeep, hBsLen]) (fun _ _ _ => rfl)
  have hBand := liveUser_band_ownedRw hwf hg hIdx hSlot
  refine ⟨hAbsEq, fun a ha => ?_, fun a hNotBand => ?_, fun a hLtP => ?_⟩
  · by_cases hInP : InRegion p eff a
    · exact ⟨Or.inr hInP, hPInDom a (hBsLen.symm ▸ hInP)⟩
    · have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
      have ⟨hOwn, hDom⟩ := hBand.2.2.2 a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩) hInP
      exact ⟨Or.inl hOwn, hDom⟩
  · apply writeBytesToMap_out; intro hInP
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp (hBsLen ▸ hInP)
    exact hNotBand ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
  · apply writeBytesToMap_out; intro hInP
    have ⟨h1, _⟩ := (inRegion_iff_toNat (by omega) a).mp (hBsLen ▸ hInP); omega

theorem MallocngWFInflight.mono_peakCost {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost peakCost' : Nat} {st : MallocngSt} (hle : peakCost ≤ peakCost')
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    MallocngWFInflight inflight base brkStart brk liveCost peakCost' st :=
  { hwf with live_le_peak := Nat.le_trans hwf.live_le_peak hle
             meta_pages_bound := ⟨Nat.le_trans hwf.meta_pages_bound.1
               (Nat.add_le_add_left (Nat.div_le_div_right hle) 2), hwf.meta_pages_bound.2⟩ }

theorem alignedAlloc_reframe_bounds {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length) {p align len : BitVec 64}
    (hSlot : g.slots[idx]'hIdx = .liveUser p (mallocngAlignedEffSize align.toNat len.toNat)
      (max (mallocngAlignedEffSize align.toNat len.toNat) MallocngMinBlockCost))
    (hOff255 : p.toNat - (g.slotStart idx).toNat ≤ 255 * 16)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ mallocngAlignedEffSize align.toNat len.toNat + 4115)
    (hAlignOk : alignedAllocAlignOk align = true) (hAlignMax : align.toNat ≤ MaxAlignedAllocAlign)
    (hNoOvf : len.toNat + align.toNat < 2 ^ 64) :
    let a16 : BitVec 64 := if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64
    let delta : BitVec 64 := (0#64 - p) &&& (a16 - 1#64)
    let new_p : BitVec 64 := p + delta
    let tot' : Nat := (new_p.toNat - g.storage.toNat) / 16
    let res' : Nat := (g.slotEnd idx).toNat - (new_p.toNat + len.toNat)
    res' < 2 ^ 31 ∧ (¬ tot' ≤ 0xffff → g.sc = 63 ∧ idx = 0 ∧ tot' < 2 ^ 27) := by
  intro a16 delta new_p tot' res'
  let eff := mallocngAlignedEffSize align.toNat len.toNat
  have hGWf := hwf.groups_wf g hg
  have ⟨_, hStorNat, hStNat, _, hEnNat, hEnLeTot, _, _, _⟩ := group_slot_bounds hGWf hIdx
  have hSWf := hGWf.slot_wf idx hIdx; rw [hSlot] at hSWf
  have hBlkP : MallocngBlockWf p eff := hSWf.2.2.2.2.1
  have hPLo : (g.slotStart idx).toNat ≤ p.toNat := hSWf.2.2.2.2.2.1
  have hPHi : p.toNat + eff ≤ (g.slotEnd idx).toNat := hSWf.2.2.2.2.2.2.1
  obtain ⟨_, _, hDeltaLe, hNewNat, hNewFitEff, hAlignDvd, _, _⟩ := alignedAlloc_snap_props hAlignOk hAlignMax hNoOvf hBlkP
  change delta.toNat ≤ max align.toNat 16 - 16 at hDeltaLe; change new_p.toNat = p.toNat + delta.toNat at hNewNat
  change new_p.toNat + len.toNat ≤ p.toNat + eff at hNewFitEff; change max align.toNat 16 ∣ new_p.toNat at hAlignDvd
  have hMaxVal : MaxAlignedAllocAlign = 2 ^ 31 := rfl
  have hEffEq : eff = len.toNat + (max align.toNat 16 - 16) := by dsimp only [eff]; unfold mallocngAlignedEffSize; split <;> omega
  rcases hGWf.1 with hSc48 | h63
  · have hTotLe1M : g.totalBytes ≤ 1048576 := by
      by_cases hMp : 0 < g.maplen
      · rw [show g.totalBytes = g.maplen * 4096 by simp [GroupDesc.totalBytes, hMp]]
        exact ((hGWf.2.2.2.2.2.2.2.2.2.2.2.1 hMp).2.2.2 hSc48).1
      · have hMp0 : g.maplen = 0 := by omega
        obtain ⟨_, pg, _, _, _, _, _, _, hPgLe24, _, _, _, hCapEq⟩ := hGWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hMp0
        have hPgSc : sizeClass pg.sc ≤ 146 := by
          by_cases hEq24 : pg.sc = 24
          · rw [hEq24]; decide
          · have hlt := sizeClass_strictMono (by omega : pg.sc < 24) (by decide)
            have h24 : sizeClass 24 = 146 := by decide
            omega
        have : g.totalBytes = 16 * sizeClass pg.sc - 4 := by simp [GroupDesc.totalBytes, hMp0, hCapEq, slotStride]
        omega
    have hTotLe65535 : tot' ≤ 0xffff := by dsimp only [tot']; omega
    exact ⟨by dsimp only [res']; omega, fun hNot => False.elim (hNot hTotLe65535)⟩
  · obtain ⟨hLast0, hMp, _, _⟩ := hGWf.2.2.2.1 h63
    have hIdx0 : idx = 0 := by have hLen := hGWf.2.2.1; unfold GroupDesc.cnt at hLen; omega
    subst hIdx0
    have hSt0 : (g.slotStart 0).toNat = g.mem.toNat + 16 := by simpa using hStNat
    have hMem4096 : g.mem.toNat % 4096 = 0 := (hGWf.2.2.2.2.2.2.2.2.2.2.2.1 hMp).1
    have hMap4115 := hSc63 h63
    have hEn0 : (g.slotEnd 0).toNat = g.mem.toNat + g.maplen * 4096 - 4 := by
      rw [hEnNat, show g.stride = g.maplen * 4096 - 16 by simp [GroupDesc.stride, hLast0, hMp]]; omega
    have ⟨hResLt, hTotLt27⟩ : res' < 2 ^ 31 ∧ tot' < 2 ^ 27 := by
      by_cases hLe4096 : align.toNat ≤ 4096
      · exact ⟨by dsimp only [res']; omega, by dsimp only [tot']; omega⟩
      · have hPow : IsPow2Align align := ((alignOk_iff_zero_or_isPow2 align).mp hAlignOk).resolve_left (by rintro rfl; simp at hLe4096)
        obtain ⟨k, hk64, _, hkNat⟩ := exists_shift_of_isPow2Align hPow
        have hkGe13 : 13 ≤ k := Classical.byContradiction fun hlt => by
          have : 2 ^ k ≤ 2 ^ 12 := Nat.pow_le_pow_right (by omega) (by omega); omega
        have h2kDvd4096 : 4096 ∣ 2 ^ k :=
          ⟨2 ^ (k - 12), by show 2 ^ k = 2 ^ 12 * 2 ^ (k - 12); rw [← Nat.pow_add, show 12 + (k - 12) = k by omega]⟩
        have h4096Dvd : 4096 ∣ new_p.toNat := Nat.dvd_trans h2kDvd4096 (by rwa [show max align.toNat 16 = 2 ^ k by omega] at hAlignDvd)
        have := Nat.mod_eq_zero_of_dvd h4096Dvd; have := Nat.mod_eq_zero_of_dvd h2kDvd4096
        have := Nat.div_add_mod g.mem.toNat 4096; have := Nat.div_add_mod new_p.toNat 4096; have := Nat.div_add_mod (2 ^ k) 4096
        exact ⟨by dsimp only [res']; omega, by dsimp only [tot']; omega⟩
    exact ⟨hResLt, fun _ => ⟨h63, rfl, hTotLt27⟩⟩

private def mkAlignedReframedGroup (g : GroupDesc) (idx : Nat) (new_p : BitVec 64)
    (align len : Nat) : GroupDesc :=
  let effCost' := max len MallocngMinBlockCost + (max align 16 - 16)
  { g with slots := g.slots.set idx (.liveUser new_p len effCost'), freshZero := false }

private def mkAlignedReframedSt (st : MallocngSt) (g : GroupDesc) (idx : Nat)
    (p new_p : BitVec 64) (align len : Nat) (bv : BitVec 64 → BitVec 8) : MallocngSt :=
  let g2 := mkAlignedReframedGroup g idx new_p align len
  { st with groups := replaceGroupByMeta st.groups g.metaPtr g2, byteVal := bv,
            liveMap := (st.liveMap.erase p).insert new_p len (max align 16 - 16) }

set_option maxHeartbeats 400000 in
private theorem alignedAlloc_reframe_spatial {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} (γ : GhostName)
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p new_p : BitVec 64} {eff effCost align len : Nat} (hSlot : g.slots[idx]'hIdx = .liveUser p eff effCost)
    (hpLeNew : p.toNat ≤ new_p.toNat) (hNewFitEff : new_p.toNat + len ≤ p.toNat + eff) (hBlkNew : MallocngBlockWf new_p len)
    {bv : BitVec 64 → BitVec 8}
    (hOutBand : ∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bv a = st.byteVal a) :
    let st2 := mkAlignedReframedSt st g idx p new_p align len bv
    (∀ a : BitVec 64, OwnedRwByte st2 a ↔ (alignedSlotKeep st p eff a ∧ ¬ InRegion new_p len a)) ∧
    (∀ a : BitVec 64, OwnedRwByte st2 a → a ∈ st.masterDom) ∧
    ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧
    MappedSet st2.masterDom (OwnedMappedByte st2) = MappedSet st.masterDom (OwnedMappedByte st) ∧
    (∀ q r, st2.liveMap q = some r ↔
      ∃ h' ∈ st2.groups, ∃ j : Nat, ∃ hj : j < h'.slots.length, ∃ c : Nat, h'.slots[j]'hj = .liveUser q r c) ∧
    (∀ h0 ∈ st.groups, ∀ j (hj : j < h0.slots.length) r c, (h0 ≠ g ∨ j ≠ idx) →
      h0.slots[j]'hj ≠ .liveUser new_p r c) ∧
    (MallocngLiveAuth γ st.liveMap ∗ MallocngBlockToken γ p eff ∗
      ByteMap st.masterDom (alignedSlotKeep st p eff) bv ⊢
      |==> (MallocngLiveAuth γ st2.liveMap ∗ MallocngTightBlock γ new_p len (max align 16) ∗
        memRegion new_p len ∗ ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal)) := by
  dsimp only []; have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  let g2 := mkAlignedReframedGroup g idx new_p align len
  let st2 := mkAlignedReframedSt st g idx p new_p align len bv
  have hGWf := hwf.groups_wf g hg
  have ⟨_, _, hStNat, hSub4Nat, hEnNat, _, hEn48, _, hEnMod12⟩ := group_slot_bounds hGWf hIdx
  have ⟨hStrGe16, _⟩ := group_stride_pos_and_align hGWf
  have hSMG : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hSub3Nat := bv64_sub_toNat (a := g.slotStart idx) (n := 3) (by omega)
  have hSWf := hGWf.slot_wf idx hIdx; rw [hSlot] at hSWf
  have hBlkP : MallocngBlockWf p eff := hSWf.2.2.2.2.1
  have hPLo : (g.slotStart idx).toNat ≤ p.toNat := hSWf.2.2.2.2.2.1
  have hPHi : p.toNat + eff ≤ (g.slotEnd idx).toNat := hSWf.2.2.2.2.2.2.1
  have hNoRes : st.reservedMetas = [] := by
    have h := hwf.inflight_wf; cases hR : st.reservedMetas with | nil => rfl | cons _ _ => simp [hR] at h
  have hRep := replaceGroupByMeta_props hwf.groups_nodup.1 hg rfl rfl rfl rfl rfl (g1 := g2)
  obtain ⟨rg, hrg, hRgMp, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
  have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hRgMp]
  have hRg48 : rg.mem.toNat + rg.totalBytes ≤ 2 ^ 48 := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
  have hSlotInRg : ∀ a : BitVec 64, InRegion (g.slotStart idx - 4#64) g.stride a → InRegion rg.mem (rg.maplen * 4096) a :=
    fun a ha => by have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) a).mp ha; exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hPInSlot : ∀ a : BitVec 64, InRegion p eff a → InRegion (g.slotStart idx - 4#64) g.stride a :=
    fun a ha => by have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) a).mp ha; exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hNewInP : ∀ a : BitVec 64, InRegion new_p len a → InRegion p eff a :=
    fun a ha => by have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) a).mp ha; exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hOtherSlotDisj : ∀ {h0 : GroupDesc} (hh0 : h0 ∈ st.groups) {j : Nat} (hj0 : j < h0.slots.length)
      {u : BitVec 64} {r c : Nat}, (h0 ≠ g ∨ j ≠ idx) → h0.slots[j]'hj0 = .liveUser u r c →
      ∀ a : BitVec 64, InRegion (g.slotStart idx - 4#64) g.stride a → ¬ InRegion u r a := by
    intro h0 hh0 j hj0 u r c hDiff hSlot0 a haG hInU
    have hSWf0 := (hwf.groups_wf h0 hh0).slot_wf j hj0; rw [hSlot0] at hSWf0
    have ⟨_, _, hSt0, hSub4_0, hEn0, _, h48_0, _, _⟩ := group_slot_bounds (hwf.groups_wf h0 hh0) hj0
    have hSM0 : (j + 1) * h0.stride = j * h0.stride + h0.stride := Nat.succ_mul j h0.stride
    have hULo := hSWf0.2.2.2.2.2.1; have hUHi := hSWf0.2.2.2.2.2.2.1
    have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) a).mp hInU
    exact nonNested_slotSlice_disjoint hwf hg hIdx (by simp [hSlot]) hh0 hj0 (by simp [hSlot0])
      (hDiff.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm)) haG ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
  have hRootEq : ∀ a : BitVec 64,
      (∃ h ∈ st2.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) ↔
      (∃ h ∈ st.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) := fun a =>
    ⟨fun ⟨h, hh, hMp, hIn⟩ => (hRep.2.2.2.2.2.1 h hh).elim (fun hE => by subst hE; exact ⟨g, hg, hMp, hIn⟩) fun ⟨hh0, _⟩ => ⟨h, hh0, hMp, hIn⟩,
     fun ⟨h, hh, hMp, hIn⟩ => if hEq : h.metaPtr = g.metaPtr then
       by rw [mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hg hEq] at hMp hIn; exact ⟨g2, hRep.2.2.2.2.1, hMp, hIn⟩
     else ⟨h, hRep.2.2.2.2.2.2.1 h hh hEq, hMp, hIn⟩⟩
  have hOwnIff : ∀ a : BitVec 64, OwnedRwByte st2 a ↔ (alignedSlotKeep st p eff a ∧ ¬ InRegion new_p len a) := by
    intro a
    have hCM2 : ¬ CarvedMetaByte st2 a := by simp [CarvedMetaByte, st2, mkAlignedReframedSt, hNoRes]
    have hCM0 : ¬ CarvedMetaByte st a := by simp [CarvedMetaByte, hNoRes]
    constructor
    · rintro ⟨hSrc2, hNC2, _⟩
      have hSrc0 := hSrc2.imp id (hRootEq a).mp
      have hNotNew : ¬ InRegion new_p len a := fun hInN => by
        have hIdx2 : idx < g2.slots.length := by simp [g2, mkAlignedReframedGroup, hIdx]
        have hGet2 : g2.slots[idx]'hIdx2 =
            .liveUser new_p len (max len MallocngMinBlockCost + (max align 16 - 16)) := by
          simp [g2, mkAlignedReframedGroup]
        exact hNC2 ⟨g2, hRep.2.2.2.2.1, _, hGet2 ▸ List.getElem_mem hIdx2, hInN⟩
      refine ⟨?_, hNotNew⟩
      by_cases hInP : InRegion p eff a
      · exact Or.inr hInP
      · refine Or.inl ⟨hSrc0, fun ⟨h0, hh0, s, hs, hSub⟩ => ?_, hCM0⟩
        obtain ⟨j, hj0, hEqS⟩ := List.getElem_of_mem hs
        by_cases hSame : h0.metaPtr = g.metaPtr ∧ j = idx
        · rcases hSame with ⟨hM, rfl⟩
          have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hM; subst hE
          rw [← hEqS, hSlot] at hSub; exact hInP hSub
        · apply hNC2; by_cases hM : h0.metaPtr = g.metaPtr
          · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hM; subst hE
            have hjNe : j ≠ idx := fun hJ => hSame ⟨rfl, hJ⟩
            have hj2 : j < g2.slots.length := by simp [g2, mkAlignedReframedGroup, hj0]
            have hGet2 : g2.slots[j]'hj2 = s := by
              simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte, hEqS]
            exact ⟨g2, hRep.2.2.2.2.1, s, hGet2 ▸ List.getElem_mem hj2, hSub⟩
          · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hM, s, hs, hSub⟩
    · rintro ⟨hKeep, hNotNew⟩
      have hSrc0 : (∃ ma ∈ st.metaAreas, InRegion ma.base 4096 a) ∨
          (∃ h ∈ st.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) :=
        hKeep.elim (fun hOwn => hOwn.1) (fun hInP => Or.inr ⟨rg, hrg, hRgMp, hSlotInRg a (hPInSlot a hInP)⟩)
      refine ⟨hSrc0.imp id (hRootEq a).mpr, fun ⟨h', hh', s, hs, hSub⟩ => ?_, hCM2⟩
      obtain ⟨j, hj', hEqS⟩ := List.getElem_of_mem hs
      rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, hNeM⟩
      · have hj0 : j < g.slots.length := by simpa [g2, mkAlignedReframedGroup] using hj'
        by_cases hjEq : j = idx
        · subst hjEq; simp only [g2, mkAlignedReframedGroup, List.getElem_set_self] at hEqS
          rw [← hEqS] at hSub; exact hNotNew hSub
        · simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hEqS
          rcases hKeep with hOwn | hInP
          · exact hOwn.2.1 ⟨g, hg, s, hEqS ▸ List.getElem_mem hj0, hSub⟩
          · cases hS : s with
            | liveUser u r c => rw [hS] at hEqS hSub; exact hOtherSlotDisj hg hj0 (Or.inr hjEq) hEqS a (hPInSlot a hInP) hSub
            | _ => simp [hS] at hSub
      · rcases hKeep with hOwn | hInP
        · exact hOwn.2.1 ⟨h', hh0, s, hs, hSub⟩
        · cases hS : s with
          | liveUser u r c =>
            rw [hS] at hEqS hSub
            exact hOtherSlotDisj hh0 hj' (Or.inl fun hE => hNeM (congrArg GroupDesc.metaPtr hE)) hEqS a (hPInSlot a hInP) hSub
          | _ => simp [hS] at hSub
  have hDom2 : ∀ a : BitVec 64, OwnedRwByte st2 a → a ∈ st.masterDom := fun a hOwn2 =>
    ((hOwnIff a).mp hOwn2).1.elim (fun hOwn => hwf.masterDom_wf.2.1 a (Or.inl hOwn)) fun hInP =>
      hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rg, hrg, hRgMp, hSlotInRg a (hPInSlot a hInP)⟩)))))
  have hProtEq : ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal := by
    unfold ProtNoneByteMap
    refine SetSep_congr (fun _ _ => Iff.rfl) fun a _ hProt => congrArg (a ↦₈ₙ ·) (hOutBand a fun hBand => ?_)
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hBand
    have hInRg := hSlotInRg a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
    have ⟨_, _, hCross⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
    rcases hProt with ⟨gp, hgp, haGp⟩ | ⟨ap, hap, haAp⟩
    · exact not_both_inRegion_of_disjointRegions
        (hCross (gp, 4096) (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hgp)))
          (rg.mem, rg.maplen * 4096) (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hRgMp⟩))) haGp hInRg
    · exact not_both_inRegion_of_disjointRegions
        (hCross (ap, 4096) (List.mem_append_right _ (List.mem_map_of_mem hap))
          (rg.mem, rg.maplen * 4096) (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hRgMp⟩))) haAp hInRg
  have hMapSetEq : MappedSet st2.masterDom (OwnedMappedByte st2) = MappedSet st.masterDom (OwnedMappedByte st) := by
    refine SetSep_congr (fun a _ => ?_) (fun _ _ _ => rfl); unfold OwnedMappedByte
    change (_ ∨ _ ∨ _ ∨ (∃ h ∈ st2.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a)) ↔ _
    rw [hRootEq a]; exact Iff.rfl
  have hNoOtherPtr : ∀ {h0 : GroupDesc} (hh0 : h0 ∈ st.groups) {j : Nat} (hj0 : j < h0.slots.length)
      {q : BitVec 64} {r c : Nat}, (h0 ≠ g ∨ j ≠ idx) → (q = p ∨ q = new_p) →
      h0.slots[j]'hj0 ≠ .liveUser q r c := by
    intro h0 hh0 j hj0 q r c hDiff hQ hSlot0
    have hSWf0 := (hwf.groups_wf h0 hh0).slot_wf j hj0; rw [hSlot0] at hSWf0
    have ⟨_, _, hSt0, hSub4_0, hEn0, _, h48_0, _, hMod12_0⟩ := group_slot_bounds (hwf.groups_wf h0 hh0) hj0
    have hSM0 : (j + 1) * h0.stride = j * h0.stride + h0.stride := Nat.succ_mul j h0.stride
    have hQMod0 : q.toNat % 16 = 0 := Nat.mod_eq_zero_of_dvd hSWf0.2.2.2.2.1.2.1
    have := hSWf0.2.2.2.2.2.1; have := hSWf0.2.2.2.2.2.2.1
    have : q.toNat < (g.slotEnd idx).toNat := by rcases hQ with rfl | rfl <;> omega
    have : (g.slotStart idx).toNat ≤ q.toNat := by rcases hQ with rfl | rfl <;> omega
    exact nonNested_slotSlice_disjoint hwf hg hIdx (by simp [hSlot]) hh0 hj0 (by simp [hSlot0])
      (hDiff.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm))
      ((inRegion_iff_toNat (by omega) q).mpr ⟨by omega, by omega⟩)
      ((inRegion_iff_toNat (by omega) q).mpr ⟨by omega, by omega⟩)
  have hLiveMap2 : ∀ q r, st2.liveMap q = some r ↔
      ∃ h' ∈ st2.groups, ∃ j : Nat, ∃ hj : j < h'.slots.length, ∃ c : Nat,
        h'.slots[j]'hj = .liveUser q r c := by
    intro q r; have hIdx2 : idx < g2.slots.length := by simp [g2, mkAlignedReframedGroup, hIdx]
    by_cases hqNew : q = new_p
    · cases hqNew; simp only [st2, mkAlignedReframedSt, MallocngLiveMap.insert_req, ↓reduceIte, Option.some.injEq]
      refine ⟨fun hr => hr ▸ ⟨g2, hRep.2.2.2.2.1, idx, hIdx2, max len MallocngMinBlockCost + (max align 16 - 16),
        by simp [g2, mkAlignedReframedGroup]⟩, fun ⟨h', hh', j, hj', c, hSlot'⟩ => ?_⟩
      rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, hNeM⟩
      · by_cases hjEq : j = idx
        · subst hjEq; simp only [g2, mkAlignedReframedGroup, List.getElem_set_self, SlotState.liveUser.injEq] at hSlot'
          exact hSlot'.2.1
        · have hj0 : j < g.slots.length := by simpa [g2, mkAlignedReframedGroup] using hj'
          simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hSlot'
          exact False.elim (hNoOtherPtr hg hj0 (Or.inr hjEq) (Or.inr rfl) hSlot')
      · exact False.elim (hNoOtherPtr hh0 hj' (Or.inl fun hE => hNeM (congrArg GroupDesc.metaPtr hE)) (Or.inr rfl) hSlot')
    · by_cases hqp : q = p
      · cases hqp; simp only [st2, mkAlignedReframedSt, MallocngLiveMap.insert_req, MallocngLiveMap.erase_req, hqNew, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨h', hh', j, hj', c, hSlot'⟩
        rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, hNeM⟩
        · by_cases hjEq : j = idx
          · subst hjEq; simp only [g2, mkAlignedReframedGroup, List.getElem_set_self, SlotState.liveUser.injEq] at hSlot'
            exact hqNew hSlot'.1.symm
          · have hj0 : j < g.slots.length := by simpa [g2, mkAlignedReframedGroup] using hj'
            simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hSlot'
            exact hNoOtherPtr hg hj0 (Or.inr hjEq) (Or.inl rfl) hSlot'
        · exact hNoOtherPtr hh0 hj' (Or.inl fun hE => hNeM (congrArg GroupDesc.metaPtr hE)) (Or.inl rfl) hSlot'
      · simp only [st2, mkAlignedReframedSt, MallocngLiveMap.insert_req, MallocngLiveMap.erase_req, hqNew, hqp, ↓reduceIte, hwf.liveMap_wf q r]; constructor
        · rintro ⟨h0, hh0, j, hj0, c, hSlot0⟩
          by_cases hM : h0.metaPtr = g.metaPtr
          · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hM; subst hE
            have hjNe : j ≠ idx := fun hJ => by subst hJ; rw [hSlot] at hSlot0; injection hSlot0 with hE; exact hqp hE.symm
            have hj2 : j < g2.slots.length := by simp [g2, mkAlignedReframedGroup, hj0]
            exact ⟨g2, hRep.2.2.2.2.1, j, hj2, c, by simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte, hSlot0]⟩
          · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hM, j, hj0, c, hSlot0⟩
        · rintro ⟨h', hh', j, hj', c, hSlot'⟩
          rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
          · have hjNe : j ≠ idx := fun hJ => by
              subst hJ; simp only [g2, mkAlignedReframedGroup, List.getElem_set_self, SlotState.liveUser.injEq] at hSlot'
              exact hqNew hSlot'.1.symm
            have hj0 : j < g.slots.length := by simpa [g2, mkAlignedReframedGroup] using hj'
            simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte] at hSlot'
            exact ⟨g, hg, j, hj0, c, hSlot'⟩
          · exact ⟨h', hh0, j, hj', c, hSlot'⟩
  refine ⟨hOwnIff, hDom2, hProtEq, hMapSetEq, hLiveMap2,
    fun h0 hh0 j hj r c hDiff => hNoOtherPtr hh0 hj hDiff (Or.inr rfl), ?_⟩
  let L1 : MallocngLiveMap := st.liveMap.erase p
  have hL1None : L1 new_p = none := by
    show (st.liveMap.erase p).req new_p = none
    rw [MallocngLiveMap.erase_req]; by_cases hEq : new_p = p
    · simp [hEq]
    · simp only [hEq, ↓reduceIte]
      cases hLk : st.liveMap new_p with
      | none => rfl
      | some r =>
        obtain ⟨h0, hh0, j, hj0, c, hSlot0⟩ := (hwf.liveMap_wf new_p r).mp hLk
        have hDiff : h0 ≠ g ∨ j ≠ idx :=
          if hG : h0 = g then Or.inr fun hJ => by subst hG hJ; rw [hSlot] at hSlot0; injection hSlot0 with hE; exact hEq hE.symm
          else Or.inl hG
        exact False.elim (hNoOtherPtr hh0 hj0 hDiff (Or.inr rfl) hSlot0)
  have hNewDom : ∀ a : BitVec 64, InRegion new_p len a → a ∈ st.masterDom := fun a ha =>
    hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rg, hrg, hRgMp, hSlotInRg a (hPInSlot a (hNewInP a ha))⟩)))))
  have hRemEq : ByteMap st.masterDom (fun a => alignedSlotKeep st p eff a ∧ ¬ InRegion new_p len a) bv =
      ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal :=
    SetSep_congr (fun a _ => (hOwnIff a).symm) (fun _ _ _ => rfl)
  have hExtEq : ByteMap st.masterDom (alignedSlotKeep st p eff) bv =
      ((new_p ↦ₛ readBytesFromMap bv new_p len) ∗ ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal) := by
    have hLen64 : len ≤ 2 ^ 64 := by have := hBlkNew.2.2.1; omega
    rw [ByteMap_extract_slice (keep := alignedSlotKeep st p eff) hwf.masterDom_wf.1 bv new_p
      hLen64 hNewDom (fun a ha => Or.inr (hNewInP a ha)), hRemEq]
  have hMemReg : (new_p ↦ₛ readBytesFromMap bv new_p len) ⊢ memRegion new_p len := by
    have h := pointsToBytes_entails_memRegion new_p (readBytesFromMap bv new_p len)
    rwa [readBytesFromMap_length] at h
  have hGhost : MallocngLiveAuth γ st.liveMap ∗ MallocngBlockToken γ p eff ⊢
      |==> (MallocngLiveAuth γ st2.liveMap ∗ MallocngTightBlock γ new_p len (max align 16)) :=
    Entails.trans (mallocngBlock_delete_bupd γ st.liveMap p eff)
      (Entails.trans (bupd_mono (Entails.trans
          (mallocngBlockK_alloc_bupd γ L1 new_p len (max align 16 - 16) hBlkNew hL1None)
          (bupd_mono (sepConj_mono_right (mallocngBlockTokenK_to_tight γ new_p len _ _ (Nat.le_refl _))))))
        (bupd_trans _))
  rw [hExtEq, ← sepConj_assoc]
  refine Entails.trans (sepConj_mono hGhost (sepConj_mono_left hMemReg))
    (Entails.trans (bupd_frame_r _ _) (bupd_mono ?_))
  dsimp only [st2]; exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 400000 in
private theorem alignedAlloc_reframe_wf {base brkStart brk : BitVec 64}
    {liveCost peakCost liveCost' peakCost' eff effCost align len : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p new_p : BitVec 64}
    (hSlot : g.slots[idx]'hIdx = .liveUser p eff effCost)
    (hOff255 : p.toNat - (g.slotStart idx).toNat ≤ 255 * 16)
    (hpLeNew : p.toNat ≤ new_p.toNat) (hNewSubP : new_p.toNat - p.toNat ≤ max align 16 - 16)
    (hNewFitEff : new_p.toNat + len ≤ p.toNat + eff) (hBlkNew : MallocngBlockWf new_p len)
    (hResLt31 : (g.slotEnd idx).toNat - (new_p.toNat + len) < 2 ^ 31)
    (hLargeProps : ¬ (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff →
      g.sc = 63 ∧ idx = 0 ∧ (new_p.toNat - g.storage.toNat) / 16 < 2 ^ 27)
    (hTotSc48 : g.sc < 48 → (new_p.toNat - g.storage.toNat) / 16 < (idx + 1) * sizeClass g.sc)
    (hOldLeNewEff : effCost ≤ max len MallocngMinBlockCost + (max align 16 - 16))
    (hPeakLe : peakCost ≤ peakCost') (hLiveLePeak' : liveCost' ≤ peakCost')
    (hLiveStep : liveCost + (max len MallocngMinBlockCost + (max align 16 - 16)) = liveCost' + effCost)
    (hAlignMax : align ≤ MaxAlignedAllocAlign) {bv : BitVec 64 → BitVec 8}
    (hOutBand : ∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bv a = st.byteVal a)
    (hHdr3 : bv (new_p - 3#64) = BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (new_p.toNat + len)) 5 <<< 5) ||| idx))
    (hHdrOff : let tot' := (new_p.toNat - g.storage.toNat) / 16
      if tot' ≤ 0xffff then bv (new_p - 4#64) = 0#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = unpack16 (BitVec.ofNat 16 tot')
      else bv (new_p - 4#64) = 1#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = [0#8, 0#8] ∧
        readBytesFromMap bv (new_p - 8#64) 4 = unpack32 (BitVec.ofNat 32 tot'))
    (hTrl1 : 1 ≤ (g.slotEnd idx).toNat - (new_p.toNat + len) → bv (new_p + BitVec.ofNat 64 len) = 0#8)
    (hTrl5 : 5 ≤ (g.slotEnd idx).toNat - (new_p.toNat + len) →
      bv (g.slotEnd idx - 5#64) = 0#8 ∧ readBytesFromMap bv (g.slotEnd idx - 4#64) 4 =
        unpack32 (BitVec.ofNat 32 ((g.slotEnd idx).toNat - (new_p.toNat + len))))
    (hDom2 : ∀ a : BitVec 64, OwnedRwByte (mkAlignedReframedSt st g idx p new_p align len bv) a → a ∈ st.masterDom)
    (hLiveMap2 : ∀ q r, (mkAlignedReframedSt st g idx p new_p align len bv).liveMap q = some r ↔
      ∃ h' ∈ (mkAlignedReframedSt st g idx p new_p align len bv).groups,
        ∃ j : Nat, ∃ hj : j < h'.slots.length, ∃ c : Nat, h'.slots[j]'hj = .liveUser q r c)
    (hNoNew : ∀ h0 ∈ st.groups, ∀ j (hj : j < h0.slots.length) r c, (h0 ≠ g ∨ j ≠ idx) →
      h0.slots[j]'hj ≠ .liveUser new_p r c) :
    let st2 := mkAlignedReframedSt st g idx p new_p align len bv
    MallocngWF base brkStart brk liveCost' peakCost' st2 ∧
    totalLiveCount st2 = totalLiveCount st ∧ dynamicRootRegions st2 = dynamicRootRegions st := by
  dsimp only []
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMaxVal : MaxAlignedAllocAlign = 2 ^ 31 := rfl
  let effCost' := max len MallocngMinBlockCost + (max align 16 - 16)
  let g2 := mkAlignedReframedGroup g idx new_p align len
  let st2 := mkAlignedReframedSt st g idx p new_p align len bv
  have hGWf := hwf.groups_wf g hg
  have ⟨_, hStorNat, hStNat, hSub4Nat, hEnNat, hEnLeTot, hEn48, _, _⟩ := group_slot_bounds hGWf hIdx
  have ⟨hStrGe16, _⟩ := group_stride_pos_and_align hGWf
  have hSMG : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hSub3Nat := bv64_sub_toNat (a := g.slotStart idx) (n := 3) (by omega)
  have hBvOut : ∀ a : BitVec 64, ¬ SlotWriteMod g idx a → bv a = st.byteVal a := fun a hNotMod =>
    hOutBand a fun hBand => by
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hBand
      exact hNotMod (Or.inr ⟨(inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩,
        fun hEq => by have := congrArg BitVec.toNat hEq; omega⟩)
  obtain ⟨_, _, _, ⟨maG, hmaG, hInMaG⟩, _⟩ := allMetaSlots_info hwf
    ((hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg)))))
  obtain ⟨rgG, hrgG, hRgMp, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
  have hRgTot : rgG.totalBytes = rgG.maplen * 4096 := by simp [GroupDesc.totalBytes, hRgMp]
  have hRg48 : rgG.mem.toNat + rgG.totalBytes ≤ 2 ^ 48 := (hwf.groups_wf rgG hrgG).2.2.2.2.2.2.1
  have hMetaBytes : readBytesFromMap bv g2.metaPtr 40 = g2.metaBytes := by
    refine (readBytesFromMap_eq_of_inRegion (v₁ := bv) (v₂ := st.byteVal) (b := g.metaPtr) (n := 40)
      (by omega) fun a ha => hOutBand a fun hBand => ?_).trans hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hBand
    exact not_both_inRegion_of_disjointRegions (metaArea_disjoint_root_group hwf hmaG hrgG hRgMp)
      (hInMaG a ha) ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
  have hSWf := hGWf.slot_wf idx hIdx; rw [hSlot] at hSWf
  have hPLo := hSWf.2.2.2.2.2.1; have hPHi := hSWf.2.2.2.2.2.2.1
  have hRep := replaceGroupByMeta_props hwf.groups_nodup.1 hg rfl rfl rfl rfl rfl (g1 := g2)
  have hSlot2Wf : SlotWf st2 g2 idx (.liveUser new_p len effCost') := by
    dsimp only [SlotWf]
    rw [show g2.slotStart idx = g.slotStart idx from rfl, show g2.slotEnd idx = g.slotEnd idx from rfl,
      show g2.storage = g.storage from rfl, show g2.sc = g.sc from rfl,
      show g2.availMask = g.availMask from rfl, show g2.freedMask = g.freedMask from rfl,
      show g2.activeIdx = g.activeIdx from rfl, show st2.byteVal = bv from rfl]
    refine ⟨(hOutBand (g.slotStart idx - 4#64) fun hB => by
        have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) (g.slotStart idx - 4#64)).mp hB; omega).trans hSWf.1,
      by simp [hSWf.2.1], by simp [hSWf.2.2.1],
      fun hLt => False.elim (by have := hSWf.2.2.2.1 hLt; cases this),
      hBlkNew, by omega, by omega, by dsimp only [effCost']; omega,
      ⟨by dsimp only [effCost']; omega, by dsimp only [effCost']; omega,
        by simp only [st2, mkAlignedReframedSt, MallocngLiveMap.insert_ov, ↓reduceIte, effCost']; omega⟩,
      hResLt31,
      ⟨fun h2_48 => Nat.lt_of_lt_of_le (hSWf.2.2.2.2.2.2.2.2.2.2.1.1 h2_48) hOldLeNewEff, hTotSc48⟩,
      fun h63 => Nat.le_trans (hSWf.2.2.2.2.2.2.2.2.2.2.2.1 h63) (Nat.add_le_add_right hOldLeNewEff 8195),
      hHdr3, ?_, hTrl1, hTrl5⟩
    by_cases hTotLe : (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff
    · simpa [hTotLe] using hHdrOff
    · have ⟨h63, hI0, hLt27⟩ := hLargeProps hTotLe
      have hH : bv (new_p - 4#64) = 1#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = [0#8, 0#8] ∧
          readBytesFromMap bv (new_p - 8#64) 4 = unpack32 (BitVec.ofNat 32 ((new_p.toNat - g.storage.toNat) / 16)) := by
        simpa [hTotLe] using hHdrOff
      simp [hTotLe, h63, hI0, hLt27, hH.1, hH.2.1, hH.2.2]
  have hClaimEq : totalClaimedSlots st2 = totalClaimedSlots st := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg (fun h => (h.slots.filter SlotState.isClaimed).length) (g1 := g2)
    have hS := list_set_filter_len g.slots hIdx (.liveUser new_p len effCost') SlotState.isClaimed
    rw [hSlot] at hS; unfold totalClaimedSlots
    simp only [st2, mkAlignedReframedSt, g2, mkAlignedReframedGroup, effCost', SlotState.isClaimed, Bool.false_eq_true, ↓reduceIte] at hG hS ⊢; omega
  have hEffSum : totalLiveEffCost st2 + effCost = totalLiveEffCost st + effCost' := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg (fun h => (h.slots.map slotEffCost).sum) (g1 := g2)
    have hS := list_set_map_sum g.slots hIdx (.liveUser new_p len effCost') slotEffCost
    rw [hSlot] at hS; unfold totalLiveEffCost
    simp only [st2, mkAlignedReframedSt, g2, mkAlignedReframedGroup, effCost', slotEffCost] at hG hS ⊢; omega
  have hCountEq : totalLiveCount st2 = totalLiveCount st := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg (fun h => (h.slots.map slotLiveCount).sum) (g1 := g2)
    have hS := list_set_map_sum g.slots hIdx (.liveUser new_p len effCost') slotLiveCount
    rw [hSlot] at hS; unfold totalLiveCount
    simp only [st2, mkAlignedReframedSt, g2, mkAlignedReframedGroup, effCost', slotLiveCount] at hG hS ⊢; omega
  have hDynEq : dynamicRootRegions st2 = dynamicRootRegions st := by
    unfold dynamicRootRegions; dsimp only [st2, mkAlignedReframedSt, g2] at hRep ⊢; rw [hRep.2.2.1]
  let hwf0 := hwf.mono_peakCost hPeakLe
  have hNotNested : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm := by simp [hSlot]
  have hDisj := slotWriteMod_disjoint hwf0 hg hIdx hNotNested
  have hNestedMap : ∀ cg ∈ st.groups, cg.maplen = 0 →
      ∃ cg' ∈ st2.groups, cg'.metaPtr = cg.metaPtr ∧ cg'.parentMeta = cg.parentMeta ∧
        cg'.mem = cg.mem ∧ cg'.nestedCap = cg.nestedCap := fun cg hcg _ => by
    by_cases hEq : cg.metaPtr = g.metaPtr
    · rw [mem_groups_eq_of_metaPtr hwf0.groups_nodup.1 hcg hg hEq]; exact ⟨g2, hRep.2.2.2.2.1, rfl, rfl, rfl, rfl⟩
    · exact ⟨cg, hRep.2.2.2.2.2.2.1 cg hcg hEq, rfl, rfl, rfl, rfl⟩
  have hParentLift : ∀ h0 ∈ st.groups, h0.maplen = 0 →
      1 ≤ h0.lastIdx ∧ ∃ pg' ∈ st2.groups, ∃ pIdx : Nat, ∃ hp' : pIdx < pg'.slots.length,
        h0.parentMeta = some pg'.metaPtr ∧ pg'.sc < 48 ∧ h0.sc < pg'.sc ∧ pg'.sc ≤ 24 ∧
        pg'.slots[pIdx]'hp' = .liveNested h0.metaPtr ∧ (pg'.slotStart pIdx).toNat ≤ h0.mem.toNat ∧
        h0.mem.toNat + h0.nestedCap ≤ (pg'.slotEnd pIdx).toNat ∧ h0.nestedCap = slotStride pg'.sc - 4 :=
    fun h0 hh0 hM0 => by
      obtain ⟨hL1, pg, hpg, pIdx, hp, hPM, hPSc, hLtSc, hLe24, hPSlot, hPLo0, hPHi0, hPCap⟩ :=
        (hwf0.groups_wf h0 hh0).2.2.2.2.2.2.2.2.2.2.2.2.1 hM0
      refine ⟨hL1, ?_⟩; by_cases hEq : pg.metaPtr = g.metaPtr
      · have hPgEq := mem_groups_eq_of_metaPtr hwf0.groups_nodup.1 hpg hg hEq; subst hPgEq
        have hpNe : pIdx ≠ idx := fun hJ => by subst hJ; exact hNotNested h0.metaPtr hPSlot
        have hp2 : pIdx < g2.slots.length := by simp [g2, mkAlignedReframedGroup, hp]
        exact ⟨g2, hRep.2.2.2.2.1, pIdx, hp2, hPM, hPSc, hLtSc, hLe24,
          by simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hpNe, ↓reduceIte, hPSlot],
          hPLo0, hPHi0, hPCap⟩
      · exact ⟨pg, hRep.2.2.2.2.2.2.1 pg hpg hEq, pIdx, hp, hPM, hPSc, hLtSc, hLe24, hPSlot, hPLo0, hPHi0, hPCap⟩
  have hwf2 : MallocngWF base brkStart brk liveCost' peakCost' st2 :=
    { base_wf := trivial, brk_bounds := hwf0.brk_bounds, ctx_lens := hwf0.ctx_lens, initDone_wf := hwf0.initDone_wf
      initZero_wf := fun h0 => by have hE := (hwf0.initZero_wf h0).2.2.2.2.2.2.2.2.2.1; rw [hE] at hg; cases hg
      bounces_wf := hwf0.bounces_wf
      usage_wf := fun sc hsc => (hwf0.usage_wf sc hsc).trans (hRep.2.2.2.1 sc).symm
      brk_mode_wf := hwf0.brk_mode_wf
      metaAreas_wf := ⟨hwf0.metaAreas_wf.1, fun ma hma =>
        let hMa := hwf0.metaAreas_wf.2.1 ma hma
        ⟨hMa.1, hMa.2.1, hMa.2.2.1, (readBytesFromMap_eq_of_inRegion (by decide)
          fun a ha => hBvOut a (hDisj.1 ma hma a ha)).trans hMa.2.2.2⟩, hwf0.metaAreas_wf.2.2⟩
      guard_avail_wf := ⟨hwf0.guard_avail_wf.1, hwf0.guard_avail_wf.2.1, hwf0.guard_avail_wf.2.2.1, fun ap hap => by
        have hAp := hwf0.guard_avail_wf.2.2.2 ap hap
        have ⟨hABC, _, hCrossCD⟩ := pairwiseDisjoint_append hwf0.regions_disjoint.1
        have ⟨_, _, hCrossABC⟩ := pairwiseDisjoint_append hABC
        have hDisjMaAp := hCrossABC (maG.base, 4096) (List.mem_append_left _ (List.mem_map_of_mem hmaG))
          (ap, 4096) (List.mem_map_of_mem hap)
        have hDisjApRg := hCrossCD (ap, 4096) (List.mem_append_right _ (List.mem_map_of_mem hap))
          (rgG.mem, rgG.maplen * 4096) (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrgG, decide_eq_true hRgMp⟩))
        refine ⟨hAp.1, hAp.2.1, hAp.2.2.1, (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a fun hMod => ?_).trans hAp.2.2.2⟩
        rcases hMod with hM | ⟨hS, _⟩
        · exact not_both_inRegion_of_disjointRegions hDisjMaAp (hInMaG a hM) ha
        · have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hS
          have hInRg : InRegion rgG.mem (rgG.maplen * 4096) a := (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
          exact not_both_inRegion_of_disjointRegions hDisjApRg ha hInRg⟩
      inflight_wf := by have := hwf0.inflight_wf; dsimp only [st2, mkAlignedReframedSt, g2] at hClaimEq ⊢; omega
      free_bump_metas_wf := by
        have ⟨hDll, hFmB, hBump, hBmB, hUfNd, hUfIff⟩ := hwf0.free_bump_metas_wf
        have ⟨hNd123, _, _⟩ := List.nodup_append.mp hUfNd
        have ⟨hNd12, _, hDisjBm⟩ := List.nodup_append.mp hNd123
        have ⟨_, _, hDisjFm⟩ := List.nodup_append.mp hNd12
        refine ⟨hDll, fun fm hfm => ?_, hBump, fun bm hbm => ?_,
          by change ((replaceGroupByMeta st.groups g.metaPtr g2).map (·.metaPtr) ++ _ ++ _ ++ _).Nodup; rw [hRep.1]; exact hUfNd,
          fun m => by change m ∈ (replaceGroupByMeta st.groups g.metaPtr g2).map (·.metaPtr) ++ _ ++ _ ++ _ ↔ m ∈ allMetaSlots st; rw [hRep.1]; exact hUfIff m⟩
        · have hNe : fm.ptr ≠ g.metaPtr := fun hE => hDisjFm g.metaPtr (List.mem_map_of_mem hg) fm.ptr (List.mem_map_of_mem hfm) hE.symm
          have hAll := (hUfIff fm.ptr).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hfm))))
          exact (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a (hDisj.2.1 fm.ptr hAll hNe a ha)).trans (hFmB fm hfm)
        · have hNe : bm ≠ g.metaPtr := fun hE => hDisjBm g.metaPtr (List.mem_append_left _ (List.mem_map_of_mem hg)) bm hbm hE.symm
          have hAll := (hUfIff bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm))
          exact (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a (hDisj.2.1 bm hAll hNe a ha)).trans (hBmB bm hbm)
      groups_nodup := ⟨hRep.1 ▸ hwf0.groups_nodup.1, hRep.2.1 ▸ hwf0.groups_nodup.2⟩
      groups_wf := fun h' hh' => by
        rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, hNeM⟩
        · have hHdrDisj := hDisj.2.2.1 g hg
          have hGMem48 : g.mem.toNat + 9 ≤ 2 ^ 64 := by have := hGWf.2.2.2.2.2.2.1; have := hGWf.2.2.2.2.2.2.2.1; omega
          refine ⟨hGWf.1, hGWf.2.1, by simp [g2, mkAlignedReframedGroup, hGWf.2.2.1], hGWf.2.2.2.1,
            hGWf.2.2.2.2.1, hGWf.2.2.2.2.2.1, hGWf.2.2.2.2.2.2.1, hGWf.2.2.2.2.2.2.2.1, hGWf.2.2.2.2.2.2.2.2.1,
            (hBvOut _ hHdrDisj.2).trans hGWf.2.2.2.2.2.2.2.2.2.1, hGWf.2.2.2.2.2.2.2.2.2.2.1,
            hGWf.2.2.2.2.2.2.2.2.2.2.2.1, hParentLift g hg, hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hMetaBytes,
            (readBytesFromMap_eq_of_inRegion (b := g.mem) (n := 8) (by decide) fun a ha => hBvOut a (hHdrDisj.1 a
              ((inRegion_iff_toNat (by omega) a).mpr (by have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) a).mp ha; omega)))).trans
              hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            (hBvOut (g.mem + 8#64) (hHdrDisj.1 (g.mem + 8#64) ((inRegion_iff_toNat (by omega) (g.mem + 8#64)).mpr
              ⟨by rw [bv64_add_toNat (by omega)]; omega, by rw [bv64_add_toNat (by omega)]; omega⟩))).trans
              hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, fun j hj2 => ?_⟩
          have hj : j < g.slots.length := by simpa [g2, mkAlignedReframedGroup] using hj2
          by_cases hjEq : j = idx
          · subst hjEq; simpa [g2, mkAlignedReframedGroup] using hSlot2Wf
          · have hGet2 : g2.slots[j]'hj2 = g.slots[j]'hj := by simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte]
            rw [hGet2]
            exact slotWf_other_of_slotSet hwf0 hg hIdx hNotNested hBvOut hNestedMap hg hj (Or.inr hjEq) rfl rfl rfl rfl rfl rfl rfl rfl rfl
              (hOv := fun u r e hS => by
                have hNe : u ≠ new_p := fun hE => hNoNew g hg j hj r e (Or.inr hjEq) (by rw [← hE]; exact hS)
                simp only [st2, mkAlignedReframedSt, MallocngLiveMap.insert_ov, MallocngLiveMap.erase_ov, hNe, ↓reduceIte])
        · have hHWf := hwf0.groups_wf h' hh0
          have hHdrDisj := hDisj.2.2.1 h' hh0
          have hHMem48 : h'.mem.toNat + 9 ≤ 2 ^ 64 := by have := hHWf.2.2.2.2.2.2.1; have := hHWf.2.2.2.2.2.2.2.1; omega
          have hAllH := (hwf0.free_bump_metas_wf.2.2.2.2.2 h'.metaPtr).mp
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hh0))))
          refine ⟨hHWf.1, hHWf.2.1, hHWf.2.2.1, hHWf.2.2.2.1, hHWf.2.2.2.2.1, hHWf.2.2.2.2.2.1,
            hHWf.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.2.1,
            (hBvOut _ hHdrDisj.2).trans hHWf.2.2.2.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.2.2.2.1,
            hHWf.2.2.2.2.2.2.2.2.2.2.2.1, hParentLift h' hh0, hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a (hDisj.2.1 h'.metaPtr hAllH hNeM a ha)).trans
              hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a (hHdrDisj.1 a
              ((inRegion_iff_toNat (by omega) a).mpr (by have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) a).mp ha; omega)))).trans
              hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            (hBvOut (h'.mem + 8#64) (hHdrDisj.1 (h'.mem + 8#64) ((inRegion_iff_toNat (by omega) (h'.mem + 8#64)).mpr
              ⟨by rw [bv64_add_toNat (by omega)]; omega, by rw [bv64_add_toNat (by omega)]; omega⟩))).trans
              hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            fun j hj => slotWf_other_of_slotSet hwf0 hg hIdx hNotNested hBvOut hNestedMap hh0 hj (Or.inl hNeM) rfl rfl rfl rfl rfl rfl rfl rfl rfl
              (hOv := fun u r e hS => by
                have hNe : u ≠ new_p := fun hE => hNoNew h' hh0 j hj r e
                  (Or.inl fun hG => hNeM (congrArg GroupDesc.metaPtr hG)) (by rw [← hE]; exact hS)
                simp only [st2, mkAlignedReframedSt, MallocngLiveMap.insert_ov, MallocngLiveMap.erase_ov, hNe, ↓reduceIte])⟩
      regions_disjoint := ⟨hDynEq ▸ hwf0.regions_disjoint.1, trivial⟩
      active_wf := fun sc h1 h2 => by
        have hAct := hwf0.active_wf sc h1 h2
        obtain ⟨pre, _, hGsSplit, hPreNe, _, _⟩ := split_groups_at_mem hwf0.groups_nodup.1 hg
        have hPreNone : pre.find? (·.metaPtr == g.metaPtr) = none :=
          List.find?_eq_none.mpr fun h hh hE => hPreNe h hh (beq_iff_eq.mp hE)
        have hFindG : st.groups.find? (·.metaPtr == g.metaPtr) = some g := by
          rw [hGsSplit, List.find?_append, List.find?_cons, hPreNone]; simp
        have hFMapEq : ((st.activeLists[sc]'h2).filterMap fun m => (findGroupByMeta st2 m).map fun h => (h.metaPtr, h.prev, h.next)) =
            ((st.activeLists[sc]'h2).filterMap fun m => (findGroupByMeta st m).map fun h => (h.metaPtr, h.prev, h.next)) := by
          congr 1; funext m; unfold findGroupByMeta
          change ((replaceGroupByMeta st.groups g.metaPtr g2).find? (·.metaPtr == m)).map _ = _
          rw [hRep.2.2.2.2.2.2.2 m]; by_cases hm : m == g.metaPtr
          · have hmEq := beq_iff_eq.mp hm; subst hmEq; simp [hFindG]; exact ⟨rfl, rfl, rfl⟩
          · simp [hm]
        refine ⟨fun m hm => ?_, hFMapEq ▸ hAct.2.1, hFMapEq ▸ hAct.2.2.1,
          fun h' hh' hSc' => (hRep.2.2.2.2.2.1 h' hh').elim (fun hE => by subst hE; exact hAct.2.2.2.1 g hg hSc') (fun ⟨hh0, _⟩ => hAct.2.2.2.1 h' hh0 hSc'),
          fun i hi hPos h' hh' hEqM => (hRep.2.2.2.2.2.1 h' hh').elim (fun hE => by subst hE; exact hAct.2.2.2.2.1 i hi hPos g hg hEqM) (fun ⟨hh0, _⟩ => hAct.2.2.2.2.1 i hi hPos h' hh0 hEqM),
          fun h₁ hh₁ h₂ hh₂ hSc₁ hSc₂ hLt₁ hLt₂ => ?_,
          fun h' hh' hSc' hLt => (hRep.2.2.2.2.2.1 h' hh').elim (fun hE => by subst hE; exact hAct.2.2.2.2.2.2 g hg hSc' hLt) (fun ⟨hh0, _⟩ => hAct.2.2.2.2.2.2 h' hh0 hSc' hLt)⟩
        · obtain ⟨h0, hh0, hM0, hSc0⟩ := hAct.1 m hm; by_cases hEq : h0.metaPtr = g.metaPtr
          · rw [mem_groups_eq_of_metaPtr hwf0.groups_nodup.1 hh0 hg hEq] at hM0 hSc0; exact ⟨g2, hRep.2.2.2.2.1, hM0, hSc0⟩
          · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hEq, hM0, hSc0⟩
        · have ⟨h₁0, hh₁0, hM₁, hSc₁0, hLt₁0⟩ : ∃ h₁0 ∈ st.groups, h₁.metaPtr = h₁0.metaPtr ∧ h₁0.sc = sc ∧ h₁0.activeIdx < h₁0.lastIdx :=
            (hRep.2.2.2.2.2.1 h₁ hh₁).elim (fun hE => by subst hE; exact ⟨g, hg, rfl, hSc₁, hLt₁⟩) fun ⟨hh0, _⟩ => ⟨h₁, hh0, rfl, hSc₁, hLt₁⟩
          have ⟨h₂0, hh₂0, hM₂, hSc₂0, hLt₂0⟩ : ∃ h₂0 ∈ st.groups, h₂.metaPtr = h₂0.metaPtr ∧ h₂0.sc = sc ∧ h₂0.activeIdx < h₂0.lastIdx :=
            (hRep.2.2.2.2.2.1 h₂ hh₂).elim (fun hE => by subst hE; exact ⟨g, hg, rfl, hSc₂, hLt₂⟩) fun ⟨hh0, _⟩ => ⟨h₂, hh0, rfl, hSc₂, hLt₂⟩
          exact hM₁.trans ((hAct.2.2.2.2.2.1 h₁0 hh₁0 h₂0 hh₂0 hSc₁0 hSc₂0 hLt₁0 hLt₂0).trans hM₂.symm)
      liveMap_wf := hLiveMap2, live_le_peak := hLiveLePeak'
      effCost_le_live := by have := hwf0.effCost_le_live; dsimp only [st2, mkAlignedReframedSt, g2, effCost'] at hEffSum ⊢; omega
      meta_pages_bound := hwf0.meta_pages_bound
      empty_groups_bound := by
        have hNE : ¬ g2.isEmpty = true := fun hE => by
          have hI : idx < g2.slots.length := by simp [g2, mkAlignedReframedGroup, hIdx]
          have hF := List.all_eq_true.mp hE _ (List.getElem_mem hI); simp [g2, mkAlignedReframedGroup, SlotState.isFree] at hF
        intro h' hh' hEmp; rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
        · exact False.elim (hNE hEmp)
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hwf0.empty_groups_bound h' hh0 hEmp
          exact ⟨e1, e2, e3, e4, e5, fun y hy hEy hSc => (hRep.2.2.2.2.2.1 y hy).elim
            (fun r => False.elim (hNE (r ▸ hEy))) (fun ⟨hy0, _⟩ => e6 y hy0 hEy hSc), e7⟩
      masterDom_wf := ⟨hwf0.masterDom_wf.1, fun a hAny => hAny.elim (hDom2 a) fun hRest =>
        hRest.elim (fun hP => hwf0.masterDom_wf.2.1 a (Or.inr (Or.inl hP))) fun hMap => by
          refine hwf0.masterDom_wf.2.1 a (Or.inr (Or.inr ?_)); unfold OwnedMappedByte at hMap ⊢
          exact hMap.imp id (Or.imp id (Or.imp id fun ⟨h', hh', hMp', hIn'⟩ =>
            (hRep.2.2.2.2.2.1 h' hh').elim (fun hE => by subst hE; exact ⟨g, hg, hMp', hIn'⟩) fun ⟨hh0, _⟩ => ⟨h', hh0, hMp', hIn'⟩)),
        fun a ha => hDynEq.symm ▸ hwf0.masterDom_wf.2.2 a ha⟩ }
  exact ⟨hwf2, hCountEq, hDynEq⟩

private theorem effCost_le_aligned (a l c : Nat) :
    max (mallocngAlignedEffSize a l) c ≤ max l c + (max a 16 - 16) := by
  unfold mallocngAlignedEffSize; split <;> omega

private theorem alignedAlloc_reframe_pure_props {base brkStart brk : BitVec 64} {liveCost peakCost : Nat}
    {st : MallocngSt} (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length) {p new_p align len : BitVec 64}
    (hSlot : g.slots[idx]'hIdx = .liveUser p (mallocngAlignedEffSize align.toNat len.toNat)
      (max (mallocngAlignedEffSize align.toNat len.toNat) MallocngMinBlockCost))
    (hOff255 : p.toNat - (g.slotStart idx).toNat ≤ 255 * 16)
    (hSc24_26 : 24 ≤ g.sc ∧ g.sc ≤ 26 → nominalSlotCap 23 < mallocngAlignedEffSize align.toNat len.toNat)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ mallocngAlignedEffSize align.toNat len.toNat + 4115)
    (hAlignOk : alignedAllocAlignOk align = true) (hAlignMax : align.toNat ≤ MaxAlignedAllocAlign)
    (hNoOvf : len.toNat + align.toNat < 2 ^ 64)
    (hNewEq : new_p = p + ((0#64 - p) &&&
      ((if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64) - 1#64))) :
    p.toNat ≤ new_p.toNat ∧ new_p.toNat - p.toNat ≤ max align.toNat 16 - 16 ∧
    new_p.toNat + len.toNat ≤ p.toNat + mallocngAlignedEffSize align.toNat len.toNat ∧ MallocngBlockWf new_p len.toNat ∧
    (g.slotEnd idx).toNat - (new_p.toNat + len.toNat) < 2 ^ 31 ∧
    (¬ (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff →
      g.sc = 63 ∧ idx = 0 ∧ (new_p.toNat - g.storage.toNat) / 16 < 2 ^ 27) ∧
    (g.sc < 48 → (new_p.toNat - g.storage.toNat) / 16 < (idx + 1) * sizeClass g.sc) := by
  subst hNewEq
  have hBlkP : MallocngBlockWf p (mallocngAlignedEffSize align.toNat len.toNat) := by
    have h := (hwf.groups_wf g hg).slot_wf idx hIdx; rw [hSlot] at h; exact h.2.2.2.2.1
  obtain ⟨_, _, hDeltaLe, hNewNat, hNewFit, _, hBlkNew, _⟩ := alignedAlloc_snap_props hAlignOk hAlignMax hNoOvf hBlkP
  have hBnd := alignedAlloc_reframe_bounds hwf hg hIdx hSlot hOff255 hSc63 hAlignOk hAlignMax hNoOvf
  exact ⟨by omega, by omega, hNewFit, hBlkNew, hBnd.1, hBnd.2,
    fun h48 => alignedAlloc_totalOff_lt_sizeClass hwf hg hIdx hSlot hOff255 hSc24_26 hAlignOk hAlignMax hNoOvf h48⟩

set_option maxHeartbeats 400000 in
theorem alignedAlloc_reframe_finish {A : MallocngAddrs} {brkStart brk : BitVec 64} {b1 b2 : MallocngBudget}
    {st : MallocngSt} (γ : GhostName) (hwf : MallocngWF A.base brkStart brk b1.liveCost b1.peakCost st)
    (hCntIvs : MallocngCountIvsWF b1 (dynamicRootRegions st) st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length) {p new_p align len : BitVec 64}
    (hSlot : g.slots[idx]'hIdx = .liveUser p (mallocngAlignedEffSize align.toNat len.toNat)
      (max (mallocngAlignedEffSize align.toNat len.toNat) MallocngMinBlockCost))
    (hOff255 : p.toNat - (g.slotStart idx).toNat ≤ 255 * 16)
    (hSc24_26 : 24 ≤ g.sc ∧ g.sc ≤ 26 → nominalSlotCap 23 < mallocngAlignedEffSize align.toNat len.toNat)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ mallocngAlignedEffSize align.toNat len.toNat + 4115)
    (hAlignOk : alignedAllocAlignOk align = true) (hAlignMax : align.toNat ≤ MaxAlignedAllocAlign)
    (hNoOvf : len.toNat + align.toNat < 2 ^ 64)
    (hNewEq : new_p = p + ((0#64 - p) &&&
      ((if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64) - 1#64)))
    (hPeakLe : b1.peakCost ≤ b2.peakCost) (hLiveLePeak2 : b2.liveCost ≤ b2.peakCost)
    (hLiveStep : b1.liveCost + (max len.toNat MallocngMinBlockCost + (max align.toNat 16 - 16)) =
      b2.liveCost + max (mallocngAlignedEffSize align.toNat len.toNat) MallocngMinBlockCost)
    (hLiveCount : b2.liveCount = b1.liveCount) (hPeakCount : b1.peakCount ≤ b2.peakCount)
    {bv : BitVec 64 → BitVec 8}
    (hOutBand : ∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bv a = st.byteVal a)
    (hHdr3 : bv (new_p - 3#64) = BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (new_p.toNat + len.toNat)) 5 <<< 5) ||| idx))
    (hHdrOff : let tot' := (new_p.toNat - g.storage.toNat) / 16
      if tot' ≤ 0xffff then bv (new_p - 4#64) = 0#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = unpack16 (BitVec.ofNat 16 tot')
      else bv (new_p - 4#64) = 1#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = [0#8, 0#8] ∧
        readBytesFromMap bv (new_p - 8#64) 4 = unpack32 (BitVec.ofNat 32 tot'))
    (hTrl1 : 1 ≤ (g.slotEnd idx).toNat - (new_p.toNat + len.toNat) → bv (new_p + len) = 0#8)
    (hTrl5 : 5 ≤ (g.slotEnd idx).toNat - (new_p.toNat + len.toNat) →
      bv (g.slotEnd idx - 5#64) = 0#8 ∧ readBytesFromMap bv (g.slotEnd idx - 4#64) 4 =
        unpack32 (BitVec.ofNat 32 ((g.slotEnd idx).toNat - (new_p.toNat + len.toNat)))) :
    (MallocngRoTablesA A ∗ MallocngLiveAuth γ st.liveMap ∗
      MallocngBlockToken γ p (mallocngAlignedEffSize align.toNat len.toNat) ∗
      ByteMap st.masterDom (alignedSlotKeep st p (mallocngAlignedEffSize align.toNat len.toNat)) bv ∗
      (A.ctx ↦ₛ st.ctx.toBytes) ∗ (A.lock ↦₃₂ 0#32) ∗ (A.replaced ↦₃₂ 0#32) ∗
      (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)) ⊢
    |==> (MallocngCoreImpl γ A brkStart brk b2 (dynamicRootRegions st) ∗
      MallocngTightBlock γ new_p len.toNat (max align.toNat 16) ∗ memRegion new_p len.toNat) := by
  let eff := mallocngAlignedEffSize align.toNat len.toNat
  let st2 := mkAlignedReframedSt st g idx p new_p align.toNat len.toNat bv
  obtain ⟨hpLeNew, hNewSubP, hNewFit, hBlkNew, hRes31, hLarge, hTotSc48⟩ :=
    alignedAlloc_reframe_pure_props hwf hg hIdx hSlot hOff255 hSc24_26 hSc63 hAlignOk hAlignMax hNoOvf hNewEq
  have ⟨_, hDom2, hProtEq, hMapSetEq, hLiveMap2, hNoNew, hBupd⟩ :=
    alignedAlloc_reframe_spatial γ hwf hg hIdx (align := align.toNat) (len := len.toNat) hSlot hpLeNew hNewFit hBlkNew hOutBand
  have ⟨hwf2, hCountEq, hDynEq⟩ :=
    alignedAlloc_reframe_wf hwf hg hIdx (align := align.toNat) (len := len.toNat) hSlot hOff255 hpLeNew hNewSubP
      hNewFit hBlkNew hRes31 hLarge hTotSc48 (effCost_le_aligned align.toNat len.toNat MallocngMinBlockCost)
      hPeakLe hLiveLePeak2 hLiveStep hAlignMax hOutBand hHdr3 hHdrOff (by rwa [BitVec.ofNat_toNat]) hTrl5 hDom2 hLiveMap2 hNoNew
  have hCntIvs2 : MallocngCountIvsWF b2 (dynamicRootRegions st) st2 := by
    obtain ⟨h1, h2, _, h4, h5, h6⟩ := hCntIvs
    have h6' : Cost.GroupsGrpBound (b2.peakCount + 6) st2.groups :=
      (h6.mono (by omega)).map_ite g.metaPtr
        (g1 := mkAlignedReframedGroup g idx new_p align.toNat len.toNat)
        fun hm hs => (h6.mono (by omega)) g hg hm hs
    dsimp only [st2] at hCountEq hDynEq h6' ⊢
    exact ⟨by omega, by omega, hDynEq.symm, by omega,
      Nat.le_trans h5 (Nat.add_le_add_left (Nat.div_le_div_right (by omega)) 1), h6'⟩
  have hRearrPre : ∀ (P1 P2 P3 P4 R0 : SepProp), (P1 ∗ P2 ∗ P3 ∗ P4 ∗ R0) = ((P2 ∗ P3 ∗ P4) ∗ (P1 ∗ R0)) := fun _ _ _ _ _ => by ac_rfl
  rw [hRearrPre (MallocngRoTablesA A) (MallocngLiveAuth γ st.liveMap) (MallocngBlockToken γ p eff)
    (ByteMap st.masterDom (alignedSlotKeep st p eff) bv)]
  refine Entails.trans (sepConj_mono_left hBupd) (Entails.trans (bupd_frame_r _ _) (bupd_mono ?_))
  change _ ⊢ MallocngCoreImpl γ A brkStart brk b2 (dynamicRootRegions st) ∗ MallocngTightBlock γ new_p len.toNat (max align.toNat 16) ∗ memRegion new_p len.toNat
  rw [MallocngCoreImpl_eq]
  refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_right
    (Entails.sepExists_right st2 (Entails.of_eq (pure_sepConj_of_true hCntIvs2 _).symm))))
  unfold MallocngCoreStA MallocngCoreStInflightA; rw [pure_sepConj_of_true hwf2, hProtEq, hMapSetEq]
  rw [show st2.ctx = st.ctx from rfl, show st2.auxvPtr = st.auxvPtr from rfl, show st2.auxvSnap = st.auxvSnap from rfl]
  generalize MallocngRoTablesA A = P1, MallocngLiveAuth γ st2.liveMap = P2,
    MallocngTightBlock γ new_p len.toNat (max align.toNat 16) = P3, memRegion new_p len.toNat = P4,
    ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal = P5, (A.ctx ↦ₛ st.ctx.toBytes) = P6,
    (A.lock ↦₃₂ 0#32) = P7, (A.replaced ↦₃₂ 0#32) = P8, (A.aaReplaced ↦₃₂ 0#32) = P9,
    ((A.libc + 8#64) ↦₆₄ st.auxvPtr) = P10, MallocngAuxvState γ st.auxvPtr st.auxvSnap = P11,
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal = P12, MappedSet st.masterDom (OwnedMappedByte st) = P13
  exact Entails.of_eq (by ac_rfl)

end VerifiedLibraries.Mallocng.Proofs
