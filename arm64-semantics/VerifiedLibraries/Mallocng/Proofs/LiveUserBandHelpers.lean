/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Common
public import VerifiedLibraries.Mallocng.Proofs.Accounting
public import VerifiedLibraries.Mallocng.Proofs.AllocMetaHelpers
public import VerifiedLibraries.Mallocng.Proofs.TryAvailHelpers
public import VerifiedLibraries.Mallocng.Proofs.EnframeUserHelpers

/-!
# `.liveUser` Band Ownership and `ByteMap` Slice Focus

Proves reflexive post-call accounting lemmas, `OwnedRwByte` ownership of `MetaAreaDesc` headers
and `.liveUser` header/trailer bands, and `ByteMap` slice-focus lemmas for short headers, long
headers, and 5-byte trailers.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

theorem mallocngNoOrphanMappings_refl (ivs : List (BitVec 64 × Nat)) (m : Memory) :
    MallocngNoOrphanMappings ivs ivs m m := by
  rintro a hm (hf | hin)
  · rw [hm] at hf; cases hf
  · exact hin

theorem mallocngMappedDelta_refl (maxIvs maxBytes : Nat) (m : Memory) :
    MallocngMappedDelta maxIvs maxBytes m m :=
  ⟨[], Nat.zero_le _, Nat.zero_le _, fun _ hm => Or.inl hm⟩

theorem mallocngCallAccounting_refl {s0 sf : State}
    (hProc : MallocngProcPreserved s0 sf) (hMem : sf.mem = s0.mem)
    (maxIvs maxBytes : Nat) :
    MallocngCallAccounting maxIvs maxBytes s0 sf := by
  refine ⟨hProc, ?_⟩
  rw [hMem]
  exact mallocngMappedDelta_refl maxIvs maxBytes s0.mem

theorem mallocngEnv_to_postEnv_refl (J : MallocngIface) (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    {s0 sf : State}
    (hMem : sf.mem = s0.mem) (hBrk : sf.brk = s0.brk)
    (hTp : sf.tpidrEl0 = s0.tpidrEl0) (hBrkS : sf.brkStart = s0.brkStart) :
    MallocngEnv J γ A tp brkStart b ivs0 s0 ⊢
      MallocngPostEnv J γ A tp brkStart b ivs0 s0 sf := by
  unfold MallocngPostEnv MallocngEnv
  rw [hMem, hBrk, hTp, hBrkS]
  refine Entails.trans
    (Entails.pure_right (mallocngNoOrphanMappings_refl ivs0 s0.mem) (Entails.refl _)) ?_
  exact Entails.sepExists_intro
    (P := fun ivsf =>
      ⌜MallocngNoOrphanMappings ivs0 ivsf s0.mem s0.mem⌝ ∗
      (⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
       J.MallocngHeap γ A tp brkStart s0.brk b ivsf))
    ivs0

theorem readBytesFromMap_split {v : BitVec 64 → BitVec 8} (b : BitVec 64) (m n : Nat) :
    readBytesFromMap v b (m + n) =
      readBytesFromMap v b m ++ readBytesFromMap v (b + BitVec.ofNat 64 m) n := by
  unfold readBytesFromMap rangeAddrs
  rw [List.range_add, List.map_append, List.map_append]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _; dsimp only [Function.comp]
  congr 1
  rw [Nat.add_comm m i]
  change b + BitVec.ofNat 64 (i + m) = b + BitVec.ofNat 64 m + BitVec.ofNat 64 i
  rw [Nat.add_comm i m, BitVec.ofNat_add, ← BitVec.add_assoc]

theorem readBytesFromMap_one (v : BitVec 64 → BitVec 8) (b : BitVec 64) :
    readBytesFromMap v b 1 = [v b] := by
  simp [readBytesFromMap, rangeAddrs]

theorem metaArea_header_ownedRw {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {ma : MetaAreaDesc} (hma : ma ∈ st.metaAreas) :
    4096 ≤ ma.base.toNat ∧ ma.base.toNat % 4096 = 0 ∧ ma.base.toNat + 4096 ≤ 2 ^ 48 ∧
    readBytesFromMap st.byteVal ma.base 8 = unpack64 st.ctx.secret ∧
    (∀ a : BitVec 64, InRegion ma.base 24 a → OwnedRwByte st a ∧ a ∈ st.masterDom) := by
  have ⟨hLo, hMod, hHi, hHdr24⟩ := hwf.metaAreas_wf.2.1 ma hma
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hHdr8 : readBytesFromMap st.byteVal ma.base 8 = unpack64 st.ctx.secret := by
    have hSplit : readBytesFromMap st.byteVal ma.base 24 =
        readBytesFromMap st.byteVal ma.base 8 ++
          readBytesFromMap st.byteVal (ma.base + BitVec.ofNat 64 8) 16 :=
      readBytesFromMap_split ma.base 8 16
    rw [hSplit, List.append_assoc, List.append_assoc] at hHdr24
    have hLenL : (readBytesFromMap st.byteVal ma.base 8).length = 8 := by
      simp [readBytesFromMap, rangeAddrs]
    have hLenR : (unpack64 st.ctx.secret).length = 8 := unpack64_length _
    have hTake := congrArg (List.take 8) hHdr24
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at hTake
    exact hTake
  refine ⟨hLo, hMod, hHi, hHdr8, fun a ha => ?_⟩
  have ⟨haLo, haHi⟩ := (inRegion_iff_toNat (by omega) a).mp ha
  have haMa : InRegion ma.base 4096 a := (inRegion_iff_toNat (by omega) a).mpr ⟨haLo, by omega⟩
  have hNoUser : ¬ CarvedUserByte st a := fun hCu => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, gr, hgr, hgrPos, haGr⟩ :=
      carvedUserByte_witness hwf hCu
    exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hma hgr hgrPos) haMa haGr
  have hNoMeta : ¬ CarvedMetaByte st a := fun ⟨mr, hmr, haMr⟩ => by
    have hmAll : mr ∈ allMetaSlots st :=
      (hwf.free_bump_metas_wf.2.2.2.2.2 mr).mp (List.mem_append_right _ hmr)
    obtain ⟨ma', hma', k, hk, rfl, hSlotNat, _, h48'⟩ := metaSlot_in_metaArea hwf hmAll
    have ⟨hmLo, hmHi⟩ := (inRegion_iff_toNat (by omega) a).mp haMr
    by_cases hEqB : ma'.base = ma.base
    · rw [hEqB] at hSlotNat; omega
    · have hP := hwf.regions_disjoint.1
      unfold dynamicRootRegions at hP
      rw [List.append_assoc, List.append_assoc] at hP
      have ⟨hPMa, _, _⟩ := pairwiseDisjoint_append hP
      have hDisj := pairwiseDisjoint_map_ne hPMa hma' hma hEqB
      dsimp only at hDisj
      exact not_both_inRegion_of_disjointRegions hDisj
        ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩) haMa
  have hOwn : OwnedRwByte st a := ⟨Or.inl ⟨ma, hma, haMa⟩, hNoUser, hNoMeta⟩
  exact ⟨hOwn, hwf.masterDom_wf.2.1 a (Or.inl hOwn)⟩

theorem liveUser_band_ownedRw {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {n effCost : Nat}
    (hSlot : g.slots[idx]'hIdx = .liveUser p n effCost) :
    st.byteVal (g.slotStart idx - 4#64) = 0#8 ∧
    st.byteVal (g.slotEnd idx) = 0#8 ∧
    st.byteVal (p + BitVec.ofNat 64 n) = 0#8 ∧
    (∀ a : BitVec 64,
      InRegion (g.slotStart idx - 4#64) (g.stride + 1) a →
      ¬ InRegion p n a →
      OwnedRwByte st a ∧ a ∈ st.masterDom) := by
  have hgWf := hwf.groups_wf g hg
  have hIdxCnt : idx < g.cnt := hgWf.2.2.1 ▸ hIdx
  have hGs := group_slot_toNat hgWf
  have hSlotCalc := hGs.2.2.2.2.2 idx hIdxCnt
  have hSWf := GroupWf.slot_wf hgWf idx hIdx
  rw [hSlot] at hSWf
  have hStartLeP : (g.slotStart idx).toNat ≤ p.toNat := hSWf.2.2.2.2.2.1
  have hPEnd : p.toNat + n ≤ (g.slotEnd idx).toNat := hSWf.2.2.2.2.2.2.1
  have hEndMono : (g.slotEnd idx).toNat ≤ (g.slotEnd g.lastIdx).toNat := by
    have : (idx + 1) * g.stride ≤ g.cnt * g.stride := Nat.mul_le_mul_right _ hIdxCnt
    omega
  have hZEnd : st.byteVal (g.slotEnd idx) = 0#8 := by
    by_cases hNext : idx + 1 < g.cnt
    · have := hGs.2.2.2.2.2 (idx + 1) hNext
      rw [show g.slotEnd idx = g.slotStart (idx + 1) - 4#64 from BitVec.eq_of_toNat_eq (by omega)]
      exact (GroupWf.slot_wf hgWf (idx + 1) (hgWf.2.2.1.symm ▸ hNext)).1
    · rw [show idx = g.lastIdx by unfold GroupDesc.cnt at hNext hIdxCnt; omega]
      exact hgWf.2.2.2.2.2.2.2.2.2.1
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have ⟨_, _, _, _, _, _, h48G, _, _⟩ := group_slot_bounds hgWf hIdx
  have hZReqEnd : st.byteVal (p + BitVec.ofNat 64 n) = 0#8 := by
    by_cases hResPos : 1 ≤ (g.slotEnd idx).toNat - (p.toNat + n)
    · exact hSWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hResPos
    · have hEqEnd : p + BitVec.ofNat 64 n = g.slotEnd idx := by
        apply BitVec.eq_of_toNat_eq
        have := bv64_add_toNat (a := p) (n := n) (by omega)
        omega
      rw [hEqEnd]; exact hZEnd
  obtain ⟨gr, hgr, hgrPos, hGrLo, _, hGrStrict⟩ := group_root_containment hwf hg
  have hGrBound := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
  have hGrTot : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPos]
  refine ⟨hSWf.1, hZEnd, hZReqEnd, fun a ha hNotPN => ?_⟩
  have : idx * g.stride + g.stride = (idx + 1) * g.stride := by rw [Nat.add_mul, Nat.one_mul]
  have haRange := (inRegion_bounds (by omega)).mp ha
  have haGr : InRegion gr.mem (gr.maplen * 4096) a :=
    (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩
  have hNoMeta : ¬ CarvedMetaByte st a := fun ⟨mr, hmr, haMr⟩ => by
    obtain ⟨_, _, _, ⟨ma, hma, hInMa⟩, _⟩ := allMetaSlots_info hwf
      ((hwf.free_bump_metas_wf.2.2.2.2.2 mr).mp (List.mem_append_right _ hmr))
    exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hma hgr hgrPos)
      (hInMa a haMr) haGr
  have hNoUser : ¬ CarvedUserByte st a := fun hCu => by
    obtain ⟨h, hh, sJ, hsJMem, haInS⟩ := hCu
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hsJMem
    cases hSlotJ : h.slots[j]'hj with
    | freeAvail | freeInactive | claimed | liveNested _ =>
      simp [hSlotJ] at haInS
    | liveUser u' r' c' =>
      simp only [hSlotJ] at haInS
      have hhWf := hwf.groups_wf h hh
      have hjCnt : j < h.cnt := hhWf.2.2.1 ▸ hj
      have hhGs := group_slot_toNat hhWf
      have hhSlotCalc := hhGs.2.2.2.2.2 j hjCnt
      have hhSWf := GroupWf.slot_wf hhWf j hj
      rw [hSlotJ] at hhSWf
      have hULo : (h.slotStart j).toNat ≤ u'.toNat := hhSWf.2.2.2.2.2.1
      have hUHi : u'.toNat + r' ≤ (h.slotEnd j).toNat := hhSWf.2.2.2.2.2.2.1
      have hTot48H : h.mem.toNat + h.totalBytes ≤ 2 ^ 48 := hhWf.2.2.2.2.2.2.1
      have hEndLeLastH : (h.slotEnd j).toNat ≤ (h.slotEnd h.lastIdx).toNat := by
        have : (j + 1) * h.stride ≤ h.cnt * h.stride := Nat.mul_le_mul_right _ hjCnt
        omega
      have ⟨haULo, haUHi⟩ := (inRegion_iff_toNat (by omega) a).mp haInS
      have hhCont : GroupContains h a.toNat := ⟨by omega, by omega⟩
      rcases comparable_of_groupContains hwf hg hh ⟨by omega, by omega⟩ hhCont with
        rfl | hAncGH | hAncHG
      · rcases Nat.lt_trichotomy j idx with hlt | rfl | hgt
        · have : (j + 1) * g.stride ≤ idx * g.stride := Nat.mul_le_mul_right _ hlt; omega
        · rw [hSlot] at hSlotJ
          injection hSlotJ with hu hr _
          subst hu; subst hr
          exact hNotPN haInS
        · have : (idx + 1) * g.stride ≤ j * g.stride := Nat.mul_le_mul_right _ hgt; omega
      · obtain ⟨_, _, k, hk, hsK, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncGH hg
        have := hGs.2.2.2.2.2 k (hgWf.2.2.1 ▸ hk)
        rcases Nat.lt_trichotomy k idx with hlt | rfl | hgt
        · have : (k + 1) * g.stride ≤ idx * g.stride := Nat.mul_le_mul_right _ hlt; omega
        · rw [hSlot] at hsK; cases hsK
        · have : (idx + 1) * g.stride ≤ k * g.stride := Nat.mul_le_mul_right _ hgt; omega
      · obtain ⟨_, _, k, hk, hsK, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncHG hh
        cases closed_slots_disjoint (x := a.toNat) hhWf hk hj
          ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        rw [hsK] at hSlotJ; cases hSlotJ
  have hOwn : OwnedRwByte st a := ⟨Or.inr ⟨gr, hgr, hgrPos, haGr⟩, hNoUser, hNoMeta⟩
  exact ⟨hOwn, hwf.masterDom_wf.2.1 a (Or.inl hOwn)⟩

theorem bv64_and_15_of_mod {p : BitVec 64} (h : p.toNat % 16 = 0) :
    p &&& 0xf#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change p.toNat &&& 15 = 0
  rw [show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact h

theorem bv64_page_mask_eq {m base : BitVec 64} {off : Nat}
    (hMod : base.toNat % 4096 = 0) (hOff : off < 4096)
    (hEq : m.toNat = base.toNat + off) :
    m &&& 0xfffffffffffff000#64 = base := by
  have hSplit : m &&& 0xfffffffffffff000#64 = m - (m &&& 0xfff#64) := by bv_bits
  rw [hSplit]
  have hLow : (m &&& 0xfff#64).toNat = off := by
    rw [BitVec.toNat_and]
    change m.toNat &&& 4095 = off
    rw [show (4095 : Nat) = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, hEq]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hLow]; omega), hLow]
  omega

theorem focus_hdr_short_of {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {p : BitVec 64} {n : Nat}
    (hNodup : st.masterDom.Nodup)
    (hStartSub4 : (g.slotStart idx - 4#64).toNat = g.mem.toNat + 12 + idx * g.stride)
    (hEnd : (g.slotEnd idx).toNat = g.mem.toNat + 12 + (idx + 1) * g.stride)
    (hEnd48 : (g.slotEnd idx).toNat ≤ 2 ^ 48)
    (hStartLeP : (g.slotStart idx).toNat ≤ p.toNat)
    (hStart : (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride)
    (hMemGe : 4096 ≤ g.mem.toNat)
    (hpN48 : p.toNat + n ≤ 2 ^ 48)
    (hPNLeEnd : p.toNat + n ≤ (g.slotEnd idx).toNat)
    (hBandOwn : ∀ a : BitVec 64,
      InRegion (g.slotStart idx - 4#64) (g.stride + 1) a →
      ¬ InRegion p n a → OwnedRwByte st a ∧ a ∈ st.masterDom)
    (hM4 : st.byteVal (p - 4#64) = 0#8)
    (hM3 : st.byteVal (p - 3#64) =
      BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (p.toNat + n)) 5 <<< 5) ||| idx))
    (hM2 : readBytesFromMap st.byteVal (p - 2#64) 2 =
      unpack16 (BitVec.ofNat 16 ((p.toNat - g.storage.toNat) / 16))) :
    let r5 := min ((g.slotEnd idx).toNat - (p.toNat + n)) 5
    let tot := (p.toNat - g.storage.toNat) / 16
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      (((p - 4#64) ↦₈ 0#8) ∗
       ((p - 3#64) ↦₈ BitVec.ofNat 8 ((r5 <<< 5) ||| idx)) ∗
       ((p - 2#64) ↦₁₆ BitVec.ofNat 16 tot) ∗
       ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion (p - 4#64) 4 a) st.byteVal) := by
  dsimp only
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hpLeEnd : p.toNat ≤ (g.slotEnd idx).toNat := by omega
  have hpSub4Nat : (p - 4#64).toNat = p.toNat - 4 := bv64_sub_toNat (n := 4) (by omega)
  have hInBand : ∀ a, InRegion (p - 4#64) 4 a →
      InRegion (g.slotStart idx - 4#64) (g.stride + 1) a ∧ ¬ InRegion p n a := by
    intro a ha
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    refine ⟨(inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩, fun hPN => ?_⟩
    have := (inRegion_iff_toNat (by omega) a).mp hPN; omega
  have h4Le : (4 : Nat) ≤ 2 ^ 64 := by omega
  have hRead4 : readBytesFromMap st.byteVal (p - 4#64) 4 =
      0#8 :: BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (p.toNat + n)) 5 <<< 5) ||| idx) ::
        unpack16 (BitVec.ofNat 16 ((p.toNat - g.storage.toNat) / 16)) := by
    have hs1 := readBytesFromMap_split (v := st.byteVal) (p - 4#64) 1 3
    have hs2 := readBytesFromMap_split (v := st.byteVal) (p - 4#64 + BitVec.ofNat 64 1) 1 2
    have ha1 : p - 4#64 + BitVec.ofNat 64 1 = p - 3#64 := by bv_omega
    have ha2 : p - 3#64 + BitVec.ofNat 64 1 = p - 2#64 := by bv_omega
    rw [ha1] at hs1 hs2
    rw [ha2] at hs2
    change readBytesFromMap st.byteVal (p - 4#64) (1 + 3) = _
    rw [hs1, hs2, readBytesFromMap_one, readBytesFromMap_one, hM4, hM3, hM2,
      List.singleton_append, List.singleton_append]
  rw [ByteMap_extract_slice hNodup st.byteVal (p - 4#64) h4Le
    (fun a ha => (hBandOwn a (hInBand a ha).1 (hInBand a ha).2).2)
    (fun a ha => (hBandOwn a (hInBand a ha).1 (hInBand a ha).2).1),
    hRead4, pointsToBytes_cons, pointsToBytes_cons, ← pointsTo16_eq_pointsToBytes,
    show p - 4#64 + 1#64 = p - 3#64 by bv_omega,
    show p - 3#64 + 1#64 = p - 2#64 by bv_omega,
    sepConj_assoc, sepConj_assoc]

theorem focus_hdr_long_of {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {p : BitVec 64} {n : Nat}
    (hNodup : st.masterDom.Nodup)
    (hStartSub4 : (g.slotStart idx - 4#64).toNat = g.mem.toNat + 12 + idx * g.stride)
    (hEnd : (g.slotEnd idx).toNat = g.mem.toNat + 12 + (idx + 1) * g.stride)
    (hEnd48 : (g.slotEnd idx).toNat ≤ 2 ^ 48)
    (hPGeStart8 : (g.slotStart idx).toNat + 8 ≤ p.toNat)
    (hStart : (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride)
    (hMemGe : 4096 ≤ g.mem.toNat)
    (hpN48 : p.toNat + n ≤ 2 ^ 48)
    (hPNLeEnd : p.toNat + n ≤ (g.slotEnd idx).toNat)
    (hBandOwn : ∀ a : BitVec 64,
      InRegion (g.slotStart idx - 4#64) (g.stride + 1) a →
      ¬ InRegion p n a → OwnedRwByte st a ∧ a ∈ st.masterDom)
    (hM8 : readBytesFromMap st.byteVal (p - 8#64) 4 =
      unpack32 (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)))
    (hM4 : st.byteVal (p - 4#64) = 1#8)
    (hM3 : st.byteVal (p - 3#64) =
      BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (p.toNat + n)) 5 <<< 5) ||| idx))
    (hM2 : readBytesFromMap st.byteVal (p - 2#64) 2 = [0#8, 0#8]) :
    let r5 := min ((g.slotEnd idx).toNat - (p.toNat + n)) 5
    let tot := (p.toNat - g.storage.toNat) / 16
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      (((p - 8#64) ↦₃₂ BitVec.ofNat 32 tot) ∗
       ((p - 4#64) ↦₈ 1#8) ∗
       ((p - 3#64) ↦₈ BitVec.ofNat 8 ((r5 <<< 5) ||| idx)) ∗
       ((p - 2#64) ↦₁₆ 0#16) ∗
       ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion (p - 8#64) 8 a) st.byteVal) := by
  dsimp only
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hpSub8Nat : (p - 8#64).toNat = p.toNat - 8 := bv64_sub_toNat (n := 8) (by omega)
  have hInBand : ∀ a, InRegion (p - 8#64) 8 a →
      InRegion (g.slotStart idx - 4#64) (g.stride + 1) a ∧ ¬ InRegion p n a := by
    intro a ha
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    refine ⟨(inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩, fun hPN => ?_⟩
    have := (inRegion_iff_toNat (by omega) a).mp hPN; omega
  have h8Le : (8 : Nat) ≤ 2 ^ 64 := by omega
  have hUnp0 : ([0#8, 0#8] : List (BitVec 8)) = unpack16 0#16 := rfl
  have hRead8 : readBytesFromMap st.byteVal (p - 8#64) 8 =
      unpack32 (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)) ++
        (1#8 :: BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (p.toNat + n)) 5 <<< 5) ||| idx) ::
          unpack16 0#16) := by
    have hs0 := readBytesFromMap_split (v := st.byteVal) (p - 8#64) 4 4
    have hs1 := readBytesFromMap_split (v := st.byteVal) (p - 4#64) 1 3
    have hs2 := readBytesFromMap_split (v := st.byteVal) (p - 3#64) 1 2
    have ha0 : p - 8#64 + BitVec.ofNat 64 4 = p - 4#64 := by bv_omega
    have ha1 : p - 4#64 + BitVec.ofNat 64 1 = p - 3#64 := by bv_omega
    have ha2 : p - 3#64 + BitVec.ofNat 64 1 = p - 2#64 := by bv_omega
    rw [ha0] at hs0
    rw [ha1] at hs1
    rw [ha2] at hs2
    change readBytesFromMap st.byteVal (p - 8#64) (4 + 4) = _
    rw [hs0, hM8]
    congr 1
    change readBytesFromMap st.byteVal (p - 4#64) (1 + 3) = _
    rw [hs1, hs2, readBytesFromMap_one, readBytesFromMap_one, hM4, hM3, hM2, hUnp0,
      List.singleton_append, List.singleton_append]
  rw [ByteMap_extract_slice hNodup st.byteVal (p - 8#64) h8Le
    (fun a ha => (hBandOwn a (hInBand a ha).1 (hInBand a ha).2).2)
    (fun a ha => (hBandOwn a (hInBand a ha).1 (hInBand a ha).2).1),
    hRead8, pointsToBytes_append, unpack32_length, ← pointsTo32_eq_pointsToBytes,
    show p - 8#64 + BitVec.ofNat 64 4 = p - 4#64 by bv_omega,
    pointsToBytes_cons, pointsToBytes_cons, ← pointsTo16_eq_pointsToBytes,
    show p - 4#64 + 1#64 = p - 3#64 by bv_omega,
    show p - 3#64 + 1#64 = p - 2#64 by bv_omega,
    sepConj_assoc, sepConj_assoc, sepConj_assoc]

theorem focus_trailer5_of {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {p : BitVec 64} {n : Nat}
    (hNodup : st.masterDom.Nodup)
    (hStartSub4 : (g.slotStart idx - 4#64).toNat = g.mem.toNat + 12 + idx * g.stride)
    (hEnd : (g.slotEnd idx).toNat = g.mem.toNat + 12 + (idx + 1) * g.stride)
    (hEnd48 : (g.slotEnd idx).toNat ≤ 2 ^ 48)
    (hStartLeP : (g.slotStart idx).toNat ≤ p.toNat)
    (hStart : (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride)
    (hMemGe : 4096 ≤ g.mem.toNat)
    (hpN48 : p.toNat + n ≤ 2 ^ 48)
    (hGe5 : 5 ≤ (g.slotEnd idx).toNat - (p.toNat + n))
    (hBandOwn : ∀ a : BitVec 64,
      InRegion (g.slotStart idx - 4#64) (g.stride + 1) a →
      ¬ InRegion p n a → OwnedRwByte st a ∧ a ∈ st.masterDom)
    (hEndM5 : st.byteVal (g.slotEnd idx - 5#64) = 0#8)
    (hEndM4 : readBytesFromMap st.byteVal (g.slotEnd idx - 4#64) 4 =
      unpack32 (BitVec.ofNat 32 ((g.slotEnd idx).toNat - (p.toNat + n)))) :
    let res := (g.slotEnd idx).toNat - (p.toNat + n)
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      (((g.slotEnd idx - 5#64) ↦₈ 0#8) ∗
       ((g.slotEnd idx - 4#64) ↦₃₂ BitVec.ofNat 32 res) ∗
       ByteMap st.masterDom
         (fun a => OwnedRwByte st a ∧ ¬ InRegion (g.slotEnd idx - 5#64) 5 a) st.byteVal) := by
  dsimp only
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hEndSub5Nat : (g.slotEnd idx - 5#64).toNat = (g.slotEnd idx).toNat - 5 :=
    bv64_sub_toNat (n := 5) (by omega)
  have hInBand : ∀ a, InRegion (g.slotEnd idx - 5#64) 5 a →
      InRegion (g.slotStart idx - 4#64) (g.stride + 1) a ∧ ¬ InRegion p n a := by
    intro a ha
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    refine ⟨(inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩, fun hPN => ?_⟩
    have := (inRegion_iff_toNat (by omega) a).mp hPN; omega
  have h5Le : (5 : Nat) ≤ 2 ^ 64 := by omega
  have hRead5 : readBytesFromMap st.byteVal (g.slotEnd idx - 5#64) 5 =
      0#8 :: unpack32 (BitVec.ofNat 32 ((g.slotEnd idx).toNat - (p.toNat + n))) := by
    have hs1 := readBytesFromMap_split (v := st.byteVal) (g.slotEnd idx - 5#64) 1 4
    have ha1 : g.slotEnd idx - 5#64 + BitVec.ofNat 64 1 = g.slotEnd idx - 4#64 := by bv_omega
    rw [ha1] at hs1
    change readBytesFromMap st.byteVal (g.slotEnd idx - 5#64) (1 + 4) = _
    rw [hs1, readBytesFromMap_one, hEndM5, hEndM4, List.singleton_append]
  rw [ByteMap_extract_slice hNodup st.byteVal (g.slotEnd idx - 5#64) h5Le
    (fun a ha => (hBandOwn a (hInBand a ha).1 (hInBand a ha).2).2)
    (fun a ha => (hBandOwn a (hInBand a ha).1 (hInBand a ha).2).1),
    hRead5, pointsToBytes_cons, ← pointsTo32_eq_pointsToBytes,
    show g.slotEnd idx - 5#64 + 1#64 = g.slotEnd idx - 4#64 by bv_omega,
    sepConj_assoc]

end VerifiedLibraries.Mallocng.Proofs
