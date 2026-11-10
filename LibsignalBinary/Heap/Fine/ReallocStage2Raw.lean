/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocStage2
public import LibsignalBinary.Heap.Fine.MallocLargeTraceHelpers
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Raw-State Placed `__libc_realloc` Stage 2 In-Place `set_size`

Verifies Stage 2 (`+0x2cc → ret`) of placed `__libc_realloc` (`blk14`), exposing the concrete
post-state `(st', g', newEff, live', peak')` and `FineGroupSameGeom` slot/group equations needed to
preserve `MallocngFineInv`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Coarse Budget Synthesis and Raw Environment Split -/

/-- `synthCoarseBudgetRaw` satisfies `MallocngCountIvsWF` given `Cost.GroupsGrpBound 128 st.groups`. -/
theorem synthCoarseBudgetRaw_countIvsWF (liveCost peakCost : Nat) (st : MallocngSt)
    (hGrp : Cost.GroupsGrpBound 128 st.groups) :
    MallocngCountIvsWF (synthCoarseBudgetRaw liveCost peakCost st) (dynamicRootRegions st) st := by
  dsimp only [MallocngCountIvsWF, synthCoarseBudgetRaw]
  exact ⟨by omega, Nat.le_refl _, rfl, by omega, by omega, hGrp.mono (by omega)⟩

/-- Exact `SepProp` equality splitting raw `(MallocngRoTablesA ∗ MallocngCoreStA ∗ MallocngRuntime)`
    into the `reallocReadPre` components used by `PlacedReallocStage1` and `PlacedReallocSizeToClass`. -/
theorem mallocngRawEnv_eq_readRest (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) (liveCost peakCost : Nat) (st : MallocngSt)
    (hGrp : Cost.GroupsGrpBound 128 st.groups) :
    (MallocngRoTablesA A ∗ MallocngCoreStA γ A brkStart brk liveCost peakCost st ∗
      MallocngRuntime A tp) =
    (MallocngRoTablesAt A ∗ (A.ctx ↦ₛ st.ctx.toBytes) ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
      MallocngReadRest γ A tp brkStart brk
        (synthCoarseBudgetRaw liveCost peakCost st) (dynamicRootRegions st) st) := by
  have hCount := synthCoarseBudgetRaw_countIvsWF liveCost peakCost st hGrp
  have hPureEq :
      (MallocngCountIvsWF (synthCoarseBudgetRaw liveCost peakCost st) (dynamicRootRegions st) st ∧
        MallocngWF A.base brkStart brk
          (synthCoarseBudgetRaw liveCost peakCost st).liveCost
          (synthCoarseBudgetRaw liveCost peakCost st).peakCost st) =
      MallocngWFInflight 0 A.base brkStart brk liveCost peakCost st :=
    propext ⟨fun h => h.2, fun h => ⟨hCount, h⟩⟩
  unfold MallocngRoTablesA MallocngCoreStA MallocngCoreStInflightA MallocngReadRest
  rw [hPureEq]
  generalize (MallocngRoTablesAt A) = PRo
  generalize (MallocngRuntime A tp) = PRt
  generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
  ac_rfl

/-! ## In-Place `set_size` Separation-Logic Absorption -/

set_option maxHeartbeats 400000 in
theorem reallocInPlace_absorb_raw (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (st : MallocngSt)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff newSz : Nat}
    (origBs tailBs : List (BitVec 8))
    (_hOrigLen : origBs.length ≤ oldSz) (_hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hNewMax : newSz ≤ 131051)
    (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    (slotBsFinal : List (BitVec 8)) (hFinalLen : slotBsFinal.length = g.stride)
    (hKeepUser : ∀ i, i < p.toNat - (g.slotStart idx).toNat + 4 + min origBs.length newSz →
      i ≠ p.toNat - (g.slotStart idx).toNat + 1 →
      slotBsFinal.getD i 0#8 =
        (mkLiveUserSlotBs st.byteVal g idx oldSz p (origBs ++ tailBs)).getD i 0#8)
    (hHdrP3 : slotBsFinal.getD (p.toNat - (g.slotStart idx).toNat + 1) 0#8 =
      BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
    (hRes1 : 1 ≤ (g.slotEnd idx).toNat - (p.toNat + newSz) →
      slotBsFinal.getD (p.toNat - (g.slotStart idx).toNat + 4 + newSz) 0#8 = 0#8)
    (hRes5 : 5 ≤ (g.slotEnd idx).toNat - (p.toNat + newSz) →
      slotBsFinal.getD (g.stride - 5) 0#8 = 0#8 ∧
      ∀ j < 4, slotBsFinal.getD (g.stride - 4 + j) 0#8 =
        (BitVec.ofNat 32 ((g.slotEnd idx).toNat - (p.toNat + newSz))).extractLsb' (8 * j) 8) :
    let bf := mallocngReallocBudget true (some (oldSz, origBs)) newSz b
    let keptBs := origBs.take newSz
    let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
    let g' : GroupDesc := { g with slots := g.slots.set idx (.liveUser p newSz newEff) }
    let val' := writeBytesToMap st.byteVal (g.slotStart idx - 4#64) slotBsFinal
    let liveMap' := (st.liveMap.erase p).insert p newSz (st.liveMap.ov p)
    let st' : MallocngSt :=
      { st with
        groups := VerifiedLibraries.Mallocng.Proofs.replaceGroup st.groups g.metaPtr g'
        byteVal := val'
        liveMap := liveMap' }
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ st.ctx.toBytes) ∗
    ByteMap st.masterDom
      (fun a => OwnedRwByte st a ∧ ¬ InRegion (g.slotStart idx - 4#64) g.stride a) st.byteVal ∗
    ((g.slotStart idx - 4#64) ↦ₛ slotBsFinal) ∗
    MallocngReadRest γ A tp brkStart brk b ivs0 st ∗
    MallocngBlockToken γ p oldSz ⊢
      |==> (MallocngRoTablesA A ∗
            MallocngCoreStA γ A brkStart brk bf.liveCost bf.peakCost st' ∗
            MallocngRuntime A tp ∗
            ⌜(MallocngInitBlock mallocngIface γ).pureWf p (newSz, keptBs)⌝ ∗
            (MallocngInitBlock mallocngIface γ).interp p (newSz, keptBs)) := by
  intro bf keptBs newEff g' val' liveMap' st'
  unfold MallocngReadRest
  refine Entails.trans (Entails.of_eq (by
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
    ac_rfl : _ =
      ⌜MallocngCountIvsWF b ivs0 st ∧ MallocngWF A.base brkStart brk b.liveCost b.peakCost st⌝ ∗
      ((MallocngLiveAuth γ st.liveMap ∗ MallocngBlockToken γ p oldSz) ∗
       (MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        (((g.slotStart idx - 4#64) ↦ₛ slotBsFinal) ∗
         ByteMap st.masterDom
           (fun a => OwnedRwByte st a ∧ ¬ InRegion (g.slotStart idx - 4#64) g.stride a) st.byteVal) ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
        MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st) ∗
        MallocngRuntime A tp)))) ?_
  refine Entails.pure_left fun ⟨hCount, hwf⟩ => ?_
  have hgw := hwf.groups_wf g hg
  have ⟨_, _, hSt, hSub4, hEn, hEndLe, h48G, _, _⟩ := group_slot_bounds hgw hIdx
  have hStrPos := (group_stride_pos_and_align hgw).1
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hLo : (g.slotStart idx).toNat ≤ p.toNat :=
    (by have h := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx; rw [hSlot] at h; exact h.2.2.2.2.2.1)
  have hKeepPre : ∀ i, i < p.toNat - (g.slotStart idx).toNat + 4 →
      i ≠ p.toNat - (g.slotStart idx).toNat + 1 →
      slotBsFinal.getD i 0#8 = st.byteVal ((g.slotStart idx - 4#64) + BitVec.ofNat 64 i) := by
    intro i hi hiNe
    rw [hKeepUser i (by omega) hiNe]
    dsimp only [mkLiveUserSlotBs]
    rw [List.getD_eq_getElem?_getD, List.append_assoc,
      List.getElem?_append_left (by rw [readBytesFromMap_length]; omega),
      List.getElem?_eq_getElem (by rw [readBytesFromMap_length]; exact hi),
      Option.getD_some, readBytesFromMap_getElem]
  obtain ⟨hNewBWf, _, hwf', hRwOut, hRwIn⟩ :=
    reallocInPlace_wf hCount hwf hg hIdx origBs hSlot hNewMax hFit hScLe
      slotBsFinal hFinalLen hKeepPre hHdrP3 hRes1 hRes5
  have hAbs := ByteMap_absorb_slice hwf.masterDom_wf.1
    (keep := fun a => OwnedRwByte st a ∧ ¬ InRegion (g.slotStart idx - 4#64) g.stride a)
    st.byteVal (g.slotStart idx - 4#64) slotBsFinal (by omega)
    (fun a ha => (hRwIn a (by rwa [hFinalLen] at ha)).1)
    (fun a ha ⟨_, hN⟩ => hN (by rwa [hFinalLen] at ha))
  have hSubU : ∀ a, InRegion p newSz a → InRegion (g.slotStart idx - 4#64) g.stride a := fun a ha => by
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hExtU := ByteMap_extract_slice hwf.masterDom_wf.1
    (keep := fun a => (OwnedRwByte st a ∧ ¬ InRegion (g.slotStart idx - 4#64) g.stride a) ∨
      InRegion (g.slotStart idx - 4#64) slotBsFinal.length a)
    val' p (n := newSz) (by omega)
    (fun a ha => (hRwIn a (hSubU a ha)).1)
    (fun a ha => Or.inr (by rw [hFinalLen]; exact hSubU a ha))
  have hByteEq : ByteMap st.masterDom
      (fun a => ((OwnedRwByte st a ∧ ¬ InRegion (g.slotStart idx - 4#64) g.stride a) ∨
        InRegion (g.slotStart idx - 4#64) slotBsFinal.length a) ∧ ¬ InRegion p newSz a) val' =
      ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal := by
    unfold ByteMap
    refine SetSep_congr (fun a _ => ?_) (fun _ _ _ => rfl)
    dsimp only [st', g', val', liveMap', newEff]
    rw [hFinalLen]
    by_cases hS : InRegion (g.slotStart idx - 4#64) g.stride a
    · simp [hS, (hRwIn a hS).2]
    · have hNU : ¬ InRegion p newSz a := fun hU => hS (hSubU a hU)
      simp [hS, hNU, (hRwOut a hS).symm]
  have hPnEq : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal := by
    unfold ProtNoneByteMap
    refine SetSep_congr (fun _ _ => Iff.rfl) (fun a _ hPn => ?_)
    obtain ⟨hmDisjAp, hmDisjGp⟩ :=
      VerifiedLibraries.Mallocng.Proofs.protNone_disjoint_slotWriteMod hwf hg hIdx
    have hNotS : ¬ InRegion (g.slotStart idx - 4#64) slotBsFinal.length a := by
      rw [hFinalLen]; intro hS
      by_cases hEq0 : a = g.slotStart idx - 4#64
      · subst hEq0
        obtain ⟨rg, hrg, hMpRg, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
        have hRg48 := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
        have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRg]
        obtain ⟨_, _, hC123Rg⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
        have hRgMem : (rg.mem, rg.maplen * 4096) ∈
            (st.groups.filter fun x => decide (0 < x.maplen)).map (fun x => (x.mem, x.maplen * 4096)) :=
          List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hMpRg⟩)
        have hInRg : InRegion rg.mem (rg.maplen * 4096) (g.slotStart idx - 4#64) :=
          (inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩
        rcases hPn with ⟨gp, hgp, haGp⟩ | ⟨ap, hap, haAp⟩
        · exact not_both_inRegion_of_disjointRegions
            (hC123Rg _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hgp))) _ hRgMem)
            haGp hInRg
        · exact not_both_inRegion_of_disjointRegions
            (hC123Rg _ (List.mem_append_right _ (List.mem_map_of_mem hap)) _ hRgMem)
            haAp hInRg
      · rcases hPn with ⟨gp, hgp, haGp⟩ | ⟨ap, hap, haAp⟩
        · exact hmDisjGp gp hgp a haGp (Or.inr ⟨hS, hEq0⟩)
        · exact hmDisjAp ap hap a haAp (Or.inr ⟨hS, hEq0⟩)
    congr 1; exact (writeBytesToMap_out st.byteVal _ slotBsFinal hNotS).symm
  have hMpSetEq : MappedSet st.masterDom (OwnedMappedByte st) =
      MappedSet st'.masterDom (OwnedMappedByte st') := by
    obtain ⟨hg'Mem, hGsCases, hGsKeep, _, _, _⟩ :=
      VerifiedLibraries.Mallocng.Proofs.replaceGroup_props st.groups g g' hg hwf.groups_nodup.1 rfl
    unfold MappedSet
    refine SetSep_congr (fun a _ => ?_) (fun _ _ _ => rfl)
    unfold OwnedMappedByte
    have h1 : (∃ x ∈ st.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a) ↔
        (∃ x ∈ st'.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a) :=
      ⟨fun ⟨x, hx, hp, hi⟩ => if hE : x.metaPtr = g.metaPtr then
          by have rflX := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE; subst rflX; exact ⟨g', hg'Mem, hp, hi⟩
        else ⟨x, hGsKeep x hx hE, hp, hi⟩,
       fun ⟨x, hx, hp, hi⟩ => (hGsCases x hx).elim (fun hE => by subst hE; exact ⟨g, hg, hp, hi⟩)
          (fun ⟨_, hxO⟩ => ⟨x, hxO, hp, hi⟩)⟩
    dsimp only [st'] at h1 ⊢; rw [h1]
  have hKeptLen : keptBs.length = min origBs.length newSz := by simp [keptBs]; omega
  have hReadUser : (readBytesFromMap val' p newSz).take keptBs.length = keptBs := by
    apply List.ext_getElem
    · rw [List.length_take, readBytesFromMap_length, hKeptLen]; omega
    · intro k hk1 _
      rw [List.length_take, readBytesFromMap_length, hKeptLen] at hk1
      have hkMin : k < min origBs.length newSz := by omega
      rw [List.getElem_take]
      have hReadK : (readBytesFromMap val' p newSz)[k]'(by rw [readBytesFromMap_length]; omega) =
          val' (p + BitVec.ofNat 64 k) := readBytesFromMap_getElem _ _ _ _ _
      have hAddrK : p + BitVec.ofNat 64 k =
          (g.slotStart idx - 4#64) + BitVec.ofNat 64 (p.toNat - (g.slotStart idx).toNat + 4 + k) := by
        apply BitVec.eq_of_toNat_eq
        rw [bv64_add_toNat (by omega), bv64_add_toNat (by omega)]; omega
      have hValK : val' (p + BitVec.ofNat 64 k) =
          slotBsFinal.getD (p.toNat - (g.slotStart idx).toNat + 4 + k) 0#8 := by
        rw [hAddrK]
        have hiL : p.toNat - (g.slotStart idx).toNat + 4 + k < slotBsFinal.length := by omega
        have hW := writeBytesToMap_in st.byteVal (g.slotStart idx - 4#64) slotBsFinal hiL (by omega)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL]; exact hW
      rw [hReadK, hValK, hKeepUser _ (by omega) (by omega)]
      dsimp only [mkLiveUserSlotBs]
      rw [List.getD_eq_getElem?_getD, List.append_assoc,
        List.getElem?_append_right (by rw [readBytesFromMap_length]; omega)]
      have hSubOff : p.toNat - (g.slotStart idx).toNat + 4 + k -
          (readBytesFromMap st.byteVal (g.slotStart idx - 4#64) (p.toNat - (g.slotStart idx).toNat + 4)).length = k := by
        rw [readBytesFromMap_length]; omega
      rw [hSubOff, List.append_assoc,
        List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
      simp [keptBs, List.getElem_take]
  have hUserInit : (p ↦ₛ readBytesFromMap val' p newSz) ⊢
      (p ↦ₛ keptBs) ∗ memRegion (p + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) := by
    have hSplit : readBytesFromMap val' p newSz =
        keptBs ++ (readBytesFromMap val' p newSz).drop keptBs.length :=
      (List.take_append_drop keptBs.length (readBytesFromMap val' p newSz)).symm.trans
        (congrArg (· ++ _) hReadUser)
    rw [hSplit, pointsToBytes_append p keptBs _]
    refine sepConj_mono_right ?_
    have hDropLen : ((readBytesFromMap val' p newSz).drop keptBs.length).length = newSz - keptBs.length := by
      rw [List.length_drop, readBytesFromMap_length]
    have hEnt := (IsBlock.pointsToBytes (p + BitVec.ofNat 64 keptBs.length)
      ((readBytesFromMap val' p newSz).drop keptBs.length)).entails_memRegion
    rwa [hDropLen] at hEnt
  have hPureInit : (MallocngInitBlock mallocngIface γ).pureWf p (newSz, keptBs) :=
    ⟨hNewBWf.1, hNewBWf.2.1, Nat.lt_of_le_of_lt hNewBWf.2.2.1 (by decide), by omega⟩
  have hCoreEq : MallocngCoreStA γ A brkStart brk bf.liveCost bf.peakCost st' =
      (MallocngLiveAuth γ st'.liveMap ∗ (A.ctx ↦ₛ st'.ctx.toBytes) ∗ (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗
       MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
       ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
       ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
       MappedSet st'.masterDom (OwnedMappedByte st')) := by
    have hwfInf : MallocngWFInflight 0 A.base brkStart brk bf.liveCost bf.peakCost st' := hwf'
    dsimp only [MallocngCoreStA, MallocngCoreStInflightA]
    rw [propext ⟨fun _ => trivial, fun _ => hwfInf⟩, pure_true, emp_sepConj]
  refine Entails.trans (sepConj_mono_left
      (mallocngBlock_replaceOv_bupd γ st.liveMap p oldSz p newSz hNewBWf (Or.inl rfl)))
    (Entails.trans (bupd_frame_r _ _) (bupd_mono ?_))
  rw [hAbs, hExtU, hByteEq, hPnEq, hMpSetEq]
  refine Entails.trans (Entails.of_eq (by
    change _ = _
    have hLiveEq : (st.liveMap.erase p).insert p newSz (st.liveMap.ov p) =
        st'.liveMap := rfl
    rw [show st.ctx = st'.ctx from rfl, show st.auxvPtr = st'.auxvPtr from rfl,
        show st.auxvSnap = st'.auxvSnap from rfl, hLiveEq]
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngRuntime A tp) = PRt
    generalize (MallocngAuxvState γ st'.auxvPtr st'.auxvSnap) = PAu
    ac_rfl : _ =
      (MallocngRoTablesAt A ∗
       (MallocngLiveAuth γ st'.liveMap ∗ (A.ctx ↦ₛ st'.ctx.toBytes) ∗ (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗
        MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
        ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
        ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
        MappedSet st'.masterDom (OwnedMappedByte st')) ∗
       MallocngRuntime A tp) ∗
      (MallocngBlockToken γ p newSz ∗ (p ↦ₛ readBytesFromMap val' p newSz)))) ?_
  rw [← hCoreEq, show MallocngRoTablesAt A = MallocngRoTablesA A from rfl]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right hUserInit)) ?_
  rw [pure_sepConj_of_true hPureInit]
  show (MallocngRoTablesA A ∗ MallocngCoreStA γ A brkStart brk bf.liveCost bf.peakCost st' ∗
      MallocngRuntime A tp) ∗
    (MallocngBlockToken γ p newSz ∗
     ((p ↦ₛ keptBs) ∗ memRegion (p + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length))) ⊢
    MallocngRoTablesA A ∗ MallocngCoreStA γ A brkStart brk bf.liveCost bf.peakCost st' ∗
    MallocngRuntime A tp ∗
    (MallocngBlockToken γ p newSz ∗ (p ↦ₛ keptBs) ∗
     memRegion (p + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length))
  generalize (MallocngRoTablesA A) = PRo
  generalize (MallocngCoreStA γ A brkStart brk bf.liveCost bf.peakCost st') = PCore
  generalize (MallocngRuntime A tp) = PRt
  exact Entails.of_eq (by ac_rfl)

/-! ## Reconvergence Tail and Stage 2 Entry -/

set_option maxHeartbeats 400000 in
/-- Shared reconvergence tail (`+0x2fc` → `ret`) for all 3 branches of in-place `set_size`,
    exposing concrete `(st' : MallocngSt) (g' : GroupDesc) (newEff live' peak' : Nat)`. -/
theorem realloc_s2_finish_raw_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff newSz : Nat} (origBs tailBs : List (BitVec 8))
    (hOrigLen : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hNewMax : newSz ≤ 131051) (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    (hSc48 : g.sc < 48) (hNodupMeta : (st.groups.map (·.metaPtr)).Nodup)
    {bsCur : List (BitVec 8)} {Frame : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x2fc#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hbrk : s.brk = s0.brk) (hproc : MallocngProcPreserved s0 s)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = p)
    (hw4 : (s.readReg32 .x4).truncate 8 =
      BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
    (hcs : ReallocUntouchedCS s0 s)
    (hBs0Len : (mkLiveUserSlotBs st.byteVal g idx oldSz p (origBs ++ tailBs)).length = g.stride)
    (hCurLen : bsCur.length = g.stride)
    (hLo : (g.slotStart idx).toNat ≤ p.toNat) (hSt4 : 4 ≤ (g.slotStart idx).toNat)
    (hEn : (g.slotEnd idx).toNat = (g.slotStart idx - 4#64).toNat + g.stride)
    (h48 : (g.slotStart idx - 4#64).toNat + g.stride ≤ 2 ^ 48)
    (hPost : SetSizeSlicePost (mkLiveUserSlotBs st.byteVal g idx oldSz p (origBs ++ tailBs))
      (p.toNat - (g.slotStart idx).toNat + 1) g.stride newSz
      (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
      (ByteSlice.write8 bsCur (p.toNat - (g.slotStart idx).toNat + 1)
        (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx)))) :
    let sp1 := s0.sp - 80#64
    let base := g.slotStart idx - 4#64
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      ((base ↦ₛ bsCur) ∗
       (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
        MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
        MallocngBlockToken γ p oldSz ∗ Frame))
      (fun sf Pf =>
        sf.mem.perm = s0.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = p ∧
        ∃ (st' : MallocngSt) (g' : GroupDesc) (newEff live' peak' : Nat),
          (Pf ⊢ stackFrame s0 800 ∗ MallocngRoTablesA maddrs ∗
            MallocngCoreStA γ maddrs brkStart sf.brk live' peak' st' ∗
            MallocngRuntime maddrs tp ∗
            ⌜(MallocngInitBlock mallocngIface γ).pureWf p (newSz, keptBs)⌝ ∗
            (MallocngInitBlock mallocngIface γ).interp p (newSz, keptBs) ∗ Frame) ∧
          g.sc < 48 ∧
          FineGroupSameGeom g' g ∧
          g'.slots = g.slots.set idx (.liveUser p newSz newEff) ∧
          newEff = (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost ∧
          st'.groups = st.groups.map (fun x => if x.metaPtr == g.metaPtr then g' else x) ∧
          st'.metaAreas = st.metaAreas ∧
          (∀ k, st'.liveMap k = if k = p then some newSz else st.liveMap k) ∧
          MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem)
      oom := by
  intro sp1 base keptBs
  have _ := hb
  let hdrOff := p.toNat - (g.slotStart idx).toNat + 1
  obtain ⟨_, hAddrP3Neg, _, _⟩ := slot_set_size_addrs hLo hSt4 hEn h48 hFit
  have hspAlign1 : (s0.sp - 80#64) &&& 15#64 = 0#64 := sp_sub80_align16 hsp0
  let bsFinal := ByteSlice.write8 bsCur hdrOff
    (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
  let bf := mallocngReallocBudget true (some (oldSz, origBs)) newSz bgt
  let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
  let g' : GroupDesc := { g with slots := g.slots.set idx (.liveUser p newSz newEff) }
  let val' := writeBytesToMap st.byteVal base bsFinal
  let liveMap' := (st.liveMap.erase p).insert p newSz (st.liveMap.ov p)
  let st' : MallocngSt :=
    { st with
      groups := VerifiedLibraries.Mallocng.Proofs.replaceGroup st.groups g.metaPtr g'
      byteVal := val'
      liveMap := liveMap' }
  have hLiveSimp : ∀ k, st'.liveMap k = if k = p then some newSz else st.liveMap k := fun k => by
    change ((st.liveMap.erase p).insert p newSz (st.liveMap.ov p)).req k = _
    simp only [MallocngLiveMap.insert_req, MallocngLiveMap.erase_req]
    by_cases hk : k = p <;> simp [hk]
  have hDynEq : dynamicRootRegions st' = dynamicRootRegions st := by
    have ⟨_, hRoots⟩ := replaceGroup_preserves_mem_and_roots st.groups g g' hg hNodupMeta rfl rfl
    dsimp only [dynamicRootRegions, st']
    rw [hRoots]
  have hTail : ∀ {m1 : Memory} {s2 : State},
      m1.perm = s.mem.perm →
      s2.pc = b + 0x294#64 → s2.status = .Running → s2.mem = m1 → s2.brk = s0.brk →
      MallocngProcPreserved s0 s2 → s2.sp = s0.sp - 80#64 → s2.spAligned = true →
      s2.readReg64 .x20 = p →
      s2.readReg64 .x23 = s0.readReg64 .x23 → s2.readReg64 .x24 = s0.readReg64 .x24 →
      s2.readReg64 .x25 = s0.readReg64 .x25 → s2.readReg64 .x26 = s0.readReg64 .x26 →
      ReallocUntouchedCS s0 s2 →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s2
        ((base ↦ₛ bsFinal) ∗
         (ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 720 ∗
          (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
           ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
           MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
           MallocngBlockToken γ p oldSz ∗ Frame)))
        (fun sf Pf =>
          sf.mem.perm = s0.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = p ∧
          ∃ (st' : MallocngSt) (g' : GroupDesc) (newEff live' peak' : Nat),
            (Pf ⊢ stackFrame s0 800 ∗ MallocngRoTablesA maddrs ∗
              MallocngCoreStA γ maddrs brkStart sf.brk live' peak' st' ∗
              MallocngRuntime maddrs tp ∗
              ⌜(MallocngInitBlock mallocngIface γ).pureWf p (newSz, keptBs)⌝ ∗
              (MallocngInitBlock mallocngIface γ).interp p (newSz, keptBs) ∗ Frame) ∧
            g.sc < 48 ∧
            FineGroupSameGeom g' g ∧
            g'.slots = g.slots.set idx (.liveUser p newSz newEff) ∧
            newEff = (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost ∧
            st'.groups = st.groups.map (fun x => if x.metaPtr == g.metaPtr then g' else x) ∧
            st'.metaAreas = st.metaAreas ∧
            (∀ k, st'.liveMap k = if k = p then some newSz else st.liveMap k) ∧
            MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem)
        oom := by
    intro m1 s2 hm1Perm hpc2 hrun2 hmem2 hbrk2 hproc2 hsp2 hal2 hx20_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2
    have hm1Perm0 : m1.perm = s0.mem.perm := hm1Perm.trans hPerm
    refine SepWP.weaken_pre (P' :=
        ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
        stackFrameAt (s0.sp - 80#64) 720 ∗
        (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
         ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
         (base ↦ₛ bsFinal) ∗ MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
         MallocngBlockToken γ p oldSz) ∗ Frame)
      (Entails.of_eq (by
        dsimp only [base]
        generalize (MallocngRoTablesAt maddrs) = PRo
        generalize (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) = PRest
        ac_rfl)) ?_
    apply sepWP_bupd_pre (Q :=
        ReallocSavedLo s0 (s0.sp - 80#64) ∗
        (memRegion (s0.sp - 80#64 + 48#64) 8 ∗ memRegion (s0.sp - 80#64 + 56#64) 8 ∗
         memRegion (s0.sp - 80#64 + 64#64) 8 ∗ memRegion (s0.sp - 80#64 + 72#64) 8) ∗
        stackFrameAt (s0.sp - 80#64) 720 ∗
        (MallocngRoTablesA maddrs ∗
         MallocngCoreStA γ maddrs brkStart s0.brk bf.liveCost bf.peakCost st' ∗
         MallocngRuntime maddrs tp ∗
         ⌜(MallocngInitBlock mallocngIface γ).pureWf p (newSz, keptBs)⌝ ∗
         (MallocngInitBlock mallocngIface γ).interp p (newSz, keptBs) ∗ Frame))
    · have hSub4 : (g.slotStart idx - 4#64).toNat = (g.slotStart idx).toNat - 4 :=
        bv64_sub_toNat (by omega)
      have hAbs := reallocInPlace_absorb_raw γ maddrs tp brkStart s0.brk bgt ivs0
        st hg hIdx origBs tailBs hOrigLen hTailLen hSlot hNewMax hFit hScLe
        bsFinal (hPost.1.trans hBs0Len)
        (fun i hi hiNe => hPost.2.1 i (by omega) hiNe)
        hPost.2.2.1
        (fun h1 => by
          have h1' : bsFinal.getD (p.toNat - (g.slotStart idx).toNat + 1 + 3 + newSz) 0#8 = 0#8 :=
            hPost.2.2.2.1 (by omega)
          rwa [show p.toNat - (g.slotStart idx).toNat + 1 + 3 + newSz =
            p.toNat - (g.slotStart idx).toNat + 4 + newSz by omega] at h1')
        (fun h5 => by
          obtain ⟨h5a, h5b⟩ := hPost.2.2.2.2.1 (by omega)
          refine ⟨h5a, fun j hj => ?_⟩
          have h5bj : bsFinal.getD (g.stride - 4 + j) 0#8 = _ := h5b j hj
          rwa [show g.stride - (p.toNat - (g.slotStart idx).toNat + 1 + 3 + newSz) =
            (g.slotEnd idx).toNat - (p.toNat + newSz) by omega] at h5bj)
      refine Entails.trans (sepConj_mono_right (sepConj_mono (reallocSavedHi_entails_memRegions s0 _)
        (sepConj_mono_right (sepConj_mono_left hAbs)))) ?_
      refine Entails.trans bupd_frame_mid (bupd_mono ?_)
      generalize (MallocngRoTablesA maddrs) = PRo
      generalize (MallocngCoreStA γ maddrs brkStart s0.brk bf.liveCost bf.peakCost st') = PCore
      generalize (MallocngRuntime maddrs tp) = PRt
      generalize ((MallocngInitBlock mallocngIface γ).interp p (newSz, keptBs)) = PInit
      exact Entails.of_eq (by ac_rfl)
    · refine SepWP.mono (realloc_epilogue_ok hb hpc2 hrun2 hsp2 hal2 hsp0
        hx20_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2) ?_
      intro sf Pf _ _ ⟨hsfMem, hsfBrk, hsfProc, hsfSp, hsfCS, hsfX0, hPf⟩
      have hMemM1 : sf.mem = m1 := hsfMem.trans hmem2
      have hPerm0 : sf.mem.perm = s0.mem.perm := hMemM1 ▸ hm1Perm0
      have hBrk0 : sf.brk = s0.brk := hsfBrk.trans hbrk2
      have hProc0 : MallocngProcPreserved s0 sf := by
        obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hproc2
        obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hsfProc
        exact ⟨q1.trans p1, q2.trans p2, q3.trans p3, q4.trans p4, q5.trans p5, q6.trans p6, q7.trans p7⟩
      have hNoOrph : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem := by
        rw [hDynEq]
        exact noOrphanMappings_refl_of_delta_zero (mallocngMappedDelta_of_perm_eq hPerm0)
      refine ⟨hPerm0, hBrk0, hProc0, hsfSp, hsfCS, hsfX0,
        st', g', newEff, bf.liveCost, bf.peakCost, Entails.trans hPf ?_,
        hSc48, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, hLiveSimp, hNoOrph⟩
      rw [hBrk0]
      generalize (MallocngRoTablesA maddrs) = PRo
      generalize (MallocngCoreStA γ maddrs brkStart s0.brk bf.liveCost bf.peakCost st') = PCore
      generalize (MallocngRuntime maddrs tp) = PRt
      generalize ((MallocngInitBlock mallocngIface γ).interp p (newSz, keptBs)) = PInit
      exact Entails.of_eq (by ac_rfl)
  conv => arg 4; dsimp only [sp1]
  generalize hRestEnv : (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
    ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
    MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
    MallocngBlockToken γ p oldSz ∗ Frame) = RestEnv
  refine (fun {P post} (h : ∀ post', post' = post →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s P post' oom) => h post rfl) ?_
  intro postGoal hPostGoal
  wp_str8_slice m1 hm1Perm hdrOff
    (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
    (by
      have hw4' := hw4
      try dsimp only [Reg.x4] at hw4'
      try simp only [wp_norm, arm64_norm] at hw4' ⊢
      exact hw4')
    (by rw [← hAddrP3Neg])
    (by have := bv64_sub_toNat hSt4; rw [hCurLen]; dsimp only [hdrOff]; omega)
  conv => arg 4; rw [reallocSavedHi_eq s0]
  wp_step; wp_step; wp_step; wp_step
  conv => arg 4; rw [← reallocSavedHi_eq s0]
  subst hPostGoal; rw [← hRestEnv]
  exact hTail hm1Perm (by simp) (by simp [hrun]) (by simp) (by simp [hbrk])
    ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
     by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
    (by simp [hsp]) (by simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩

set_option maxHeartbeats 400000 in
/-- Stage 2 (`+0x2cc` → `ret`) over the split `MallocngReadRest` precondition produced by
    `PlacedReallocStage1.realloc_stage1_read_ok` + `PlacedReallocSizeToClass.realloc_sizeToClass_ok`. -/
theorem realloc_stage2_inplace_readRest_raw_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff newSz : Nat} (origBs tailBs : List (BitVec 8))
    (hOrigLen : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hNewMax : newSz ≤ 131051) (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    {Frame : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x2cc#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hbrk : s.brk = s0.brk) (hproc : MallocngProcPreserved s0 s)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat))
    (hx4 : s.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx5 : s.readReg64 .x5 = g.slotEnd idx)
    (hx19 : s.readReg64 .x19 = p)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hcs : ReallocUntouchedCS s0 s) :
    let sp1 := s0.sp - 80#64
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
       MallocngBlockToken γ p oldSz ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)
      (fun sf Pf =>
        sf.mem.perm = s0.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = p ∧
        ∃ (st' : MallocngSt) (g' : GroupDesc) (newEff live' peak' : Nat),
          (Pf ⊢ stackFrame s0 800 ∗ MallocngRoTablesA maddrs ∗
            MallocngCoreStA γ maddrs brkStart sf.brk live' peak' st' ∗
            MallocngRuntime maddrs tp ∗
            ⌜(MallocngInitBlock mallocngIface γ).pureWf p (newSz, keptBs)⌝ ∗
            (MallocngInitBlock mallocngIface γ).interp p (newSz, keptBs) ∗ Frame) ∧
          g.sc < 48 ∧
          FineGroupSameGeom g' g ∧
          g'.slots = g.slots.set idx (.liveUser p newSz newEff) ∧
          newEff = (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost ∧
          st'.groups = st.groups.map (fun x => if x.metaPtr == g.metaPtr then g' else x) ∧
          st'.metaAreas = st.metaAreas ∧
          (∀ k, st'.liveMap k = if k = p then some newSz else st.liveMap k) ∧
          MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem)
      oom := by
  intro sp1 keptBs
  have _ := hb
  apply sepWP_pure_of_sat (fun R hm =>
    satisfies_readRest_wf (Rest := ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
      stackFrameAt sp1 720 ∗ MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
      MallocngBlockToken γ p oldSz ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame ∗ R)
      (Satisfies.mono (Entails.of_eq (by
        generalize (MallocngRoTablesAt maddrs) = PRo
        generalize (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) = PRest
        ac_rfl)) hm))
  rintro ⟨_, hwf⟩
  have hSc48 : g.sc < 48 :=
    (inPlace_sc_eff_bound (extraEff := 0) hNewMax (hwf.groups_wf g hg).1 hScLe).1
  have hNodupMeta : (st.groups.map (·.metaPtr)).Nodup := hwf.groups_nodup.1
  obtain ⟨hLo, _, hSt4, _hSub4, hEn, h48, _hCapMax, hIdx31, hBs0Hdr⟩ :=
    inPlace_oldCap_bounds hwf hg hIdx hSlot hNewMax hScLe (origBs ++ tailBs)
  obtain ⟨hBs0Len, hSliceEq⟩ := liveUser_slotSlice_split hwf hg hIdx hSlot (origBs ++ tailBs)
    (by rw [List.length_append, hTailLen]; omega)
  let base := g.slotStart idx - 4#64
  let hdrOff := p.toNat - (g.slotStart idx).toNat + 1
  generalize hbs0 : mkLiveUserSlotBs st.byteVal g idx oldSz p (origBs ++ tailBs) = bs0 at hBs0Hdr hBs0Len hSliceEq
  let oldCap := (g.slotEnd idx).toNat - p.toNat
  let res := (g.slotEnd idx).toNat - (p.toNat + newSz)
  have hResEq : oldCap - newSz = res := by dsimp only [oldCap, res]; omega
  obtain ⟨hSub32, hEq32⟩ := subs32_cap_newSz (cap := oldCap) (newSz := newSz)
    (by dsimp only [oldCap]; omega) (by dsimp only [oldCap]; omega) (by dsimp only [oldCap]; omega)
  rw [hResEq] at hSub32 hEq32
  obtain ⟨hAddrP3Sub, _, hAddrZeroOf, hAddrEndOf⟩ := slot_set_size_addrs hLo hSt4 hEn h48 hFit
  refine SepWP.weaken_pre (P' :=
      (base ↦ₛ bs0) ∗
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
       MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
       MallocngBlockToken γ p oldSz ∗ Frame))
    (Entails.of_eq (by
      have hAssoc : (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
          (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
           MallocngBlockToken γ p oldSz ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)) =
        ((ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ (p ↦ₛ (origBs ++ tailBs))) ∗
          MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
          MallocngBlockToken γ p oldSz ∗ Frame) := by
        generalize (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) = PRest
        ac_rfl
      rw [hAssoc, hSliceEq]
      dsimp only [base]
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) = PRest
      ac_rfl)) ?_
  have hCapFold : (g.slotStart idx).toNat - 4 + g.stride - p.toNat = oldCap := by
    dsimp only [oldCap]; omega
  have halOf : ∀ s' : State, s'.sp = s.sp → s'.spAligned = true := fun s' hsp' => by
    simp only [State.spAligned, hsp'] at hal ⊢; exact hal
  apply sepWP_abstract_env; intro RestS2 postGoal hRestS2 hPostGoal
  wp_step; wp_step
  wp_if heq
  ·
    have hRes0 : res = 0 := by
      try rw [hx3] at heq
      try rw [hx21] at heq
      try rw [hCapFold] at heq
      exact hEq32.mp heq
    subst hPostGoal hRestS2 hbs0
    exact realloc_s2_finish_raw_ok hb γ tp brkStart bgt ivs0 s0 _ st hg hIdx origBs tailBs
      hOrigLen hTailLen hSlot hNewMax hFit hScLe hSc48 hNodupMeta
      (bsCur := mkLiveUserSlotBs st.byteVal g idx oldSz p (origBs ++ tailBs))
      (by simp) (by simp [hrun]) (by simpa using hPerm) (by simpa using hbrk)
      ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
       by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
      (by simp [hsp]) (halOf _ (by simp)) hsp0 (by simp [hx19])
      (by try simp only [wp_norm, arm64_norm]; try rw [hx4]; exact idx_trunc8_eq_hdr0 hRes0 hIdx31)
      ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
      hBs0Len hBs0Len hLo hSt4 hEn h48
      (setSize_case0 _ hdrOff g.stride newSz _ (by dsimp only [hdrOff, res] at hRes0 ⊢; omega)
        (by omega))
  ·
    have hResPos : 1 ≤ res := by
      have hNe0 : res ≠ 0 := fun h0 => heq (by
        try rw [hx3]
        try rw [hx21]
        try rw [hCapFold]
        exact hEq32.mpr h0)
      omega
    wp_step; wp_step
    have hSub32z : BitVec.zeroExtend 32 (BitVec.ofNat 64 oldCap) -
        BitVec.zeroExtend 32 (BitVec.ofNat 64 newSz) = BitVec.ofNat 32 res := hSub32
    have hAddrZero := hAddrZeroOf hResPos (by omega)
    wp_str8_slice m1 hm1Perm (hdrOff + 3 + newSz) 0#8 rfl
      (by try simp only [wp_norm, arm64_norm]
          try rw [hx5]
          try rw [hx3]
          try rw [hx21]
          try rw [hCapFold]
          try rw [hSub32]
          try rw [hSub32z]
          try rw [BitVec.zero_sub]
          try rw [BitVec.shiftLeft_zero]
          first | rfl | exact hAddrZero)
      (by rw [hBs0Len]; dsimp only [hdrOff, res] at hResPos ⊢; omega)
    let bs1 := ByteSlice.write8 bs0 (hdrOff + 3 + newSz) 0#8
    have hBs1Len : bs1.length = g.stride :=
      (ByteSlice.write8_length _ _ _ (by rw [hBs0Len]; dsimp only [hdrOff, res] at hResPos ⊢; omega)).trans hBs0Len
    wp_step
    wp_if hle4
    ·
      have hRes4 : res ≤ 4 := by
        try rw [hx3] at hle4
        try rw [hx21] at hle4
        try rw [hCapFold] at hle4
        try rw [hSub32] at hle4
        try rw [hSub32z] at hle4
        rw [show (4#32 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
            bv32_sle_iff_of_lt31 (by dsimp only [res]; omega) (by decide),
            decide_eq_true_eq] at hle4
        exact hle4
      have hBs1Hdr : bs1.getD hdrOff 0#8 = bs0.getD hdrOff 0#8 := by
        dsimp only [bs1]
        rw [ByteSlice.getD_write8 _ _ _ _ _ (by rw [hBs0Len]; dsimp only [hdrOff, res] at hResPos ⊢; omega)]
        simp only [show hdrOff ≠ hdrOff + 3 + newSz by omega, ↓reduceIte]
      conv => arg 4; arg 1; rw [pointsToBytes_focus8 base bs1 hdrOff (by rw [hBs1Len]; dsimp only [hdrOff]; omega)]
      wp_step; wp_step; wp_step; wp_step; wp_step
      conv => arg 4; arg 1; rw [← pointsToBytes_focus8 base bs1 hdrOff (by rw [hBs1Len]; dsimp only [hdrOff]; omega)]
      have hPost1 := setSize_case1to4 bs0 hdrOff g.stride newSz
        (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
        (by dsimp only [hdrOff, res] at hResPos ⊢; omega)
        (by dsimp only [hdrOff, res] at hRes4 ⊢; omega) (by omega)
      refine (fun {sFin P post} (h : ∀ s', s' = sFin →
          SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s' P post oom) => h sFin rfl) ?_
      intro sFin hsFin
      have hpcF : sFin.pc = b + 0x2fc#64 := by subst hsFin; simp
      have hrunF : sFin.status = .Running := by subst hsFin; simp [hrun]
      have hPermF : sFin.mem.perm = s0.mem.perm := by subst hsFin; exact hm1Perm.trans hPerm
      have hbrkF : sFin.brk = s0.brk := by subst hsFin; simpa using hbrk
      have hprocF : MallocngProcPreserved s0 sFin := by
        subst hsFin
        exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
               by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
      have hspF : sFin.sp = s0.sp - 80#64 := by subst hsFin; simp [hsp]
      have halF : sFin.spAligned = true := halOf _ (by subst hsFin; simp)
      have hx19F : sFin.readReg64 .x19 = p := by subst hsFin; simp [hx19]
      have hw4F : (sFin.readReg32 .x4).truncate 8 =
          BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx) := by
        subst hsFin
        try simp only [wp_norm, arm64_norm]
        try rw [hx3]
        try rw [hx21]
        try rw [hCapFold]
        try rw [hSub32]
        try rw [hSub32z]
        try rw [hBs1Hdr]
        exact hdrByte_res1to4 hBs0Hdr hIdx31 hRes4
      have hcsF : ReallocUntouchedCS s0 sFin := by
        subst hsFin
        exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
      clear hsFin
      subst hPostGoal hRestS2 hbs0
      exact realloc_s2_finish_raw_ok hb γ tp brkStart bgt ivs0 s0 sFin st hg hIdx origBs tailBs
        hOrigLen hTailLen hSlot hNewMax hFit hScLe hSc48 hNodupMeta (bsCur := bs1)
        hpcF hrunF hPermF hbrkF hprocF hspF halF hsp0 hx19F hw4F hcsF
        hBs0Len hBs1Len hLo hSt4 hEn h48 hPost1
    ·
      have hRes5 : 5 ≤ res := by
        try rw [hx3] at hle4
        try rw [hx21] at hle4
        try rw [hCapFold] at hle4
        try rw [hSub32] at hle4
        try rw [hSub32z] at hle4
        rw [show (4#32 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
            bv32_sle_iff_of_lt31 (by dsimp only [res]; omega) (by decide),
            decide_eq_true_eq] at hle4
        omega
      obtain ⟨hAddrEnd5, hAddrEnd4⟩ := hAddrEndOf hRes5
      wp_str8_slice m2 hm2Perm (g.stride - 5) 0#8 rfl
        (by rw [← hAddrEnd5])
        (by rw [hBs1Len]; omega)
      let bs2 := ByteSlice.write8 bs1 (g.stride - 5) 0#8
      have hBs2Len : bs2.length = g.stride :=
        (ByteSlice.write8_length _ _ _ (by rw [hBs1Len]; omega)).trans hBs1Len
      wp_str32_slice m3 hm3Perm (g.stride - 4) (BitVec.ofNat 32 res)
        (by simp only [wp_norm, arm64_norm])
        (by rw [← hAddrEnd4])
        (by rw [hBs2Len]; omega)
      let bs3 := ByteSlice.write32 bs2 (g.stride - 4) (BitVec.ofNat 32 res)
      have hBs3Len : bs3.length = g.stride :=
        (ByteSlice.write32_length _ _ _ (by rw [hBs2Len]; omega)).trans hBs2Len
      have hBs3Hdr : bs3.getD hdrOff 0#8 = bs0.getD hdrOff 0#8 := by
        dsimp only [bs3, bs2, bs1]
        rw [ByteSlice.getD_write32 _ _ _ _ _ (by rw [hBs2Len]; omega),
            ByteSlice.getD_write8 _ _ _ _ _ (by rw [hBs1Len]; omega),
            ByteSlice.getD_write8 _ _ _ _ _ (by rw [hBs0Len]; dsimp only [hdrOff, res] at hRes5 ⊢; omega)]
        simp only [show ¬ (g.stride - 4 ≤ hdrOff ∧ hdrOff < g.stride - 4 + 4) by dsimp only [hdrOff, res] at hRes5 ⊢; omega,
          show hdrOff ≠ g.stride - 5 by dsimp only [hdrOff, res] at hRes5 ⊢; omega,
          show hdrOff ≠ hdrOff + 3 + newSz by omega, ↓reduceIte]
      conv => arg 4; arg 1; rw [pointsToBytes_focus8 base bs3 hdrOff (by rw [hBs3Len]; dsimp only [hdrOff]; omega)]
      wp_step; wp_step; wp_step; wp_step
      conv => arg 4; arg 1; rw [← pointsToBytes_focus8 base bs3 hdrOff (by rw [hBs3Len]; dsimp only [hdrOff]; omega)]
      have hResStride : g.stride - (hdrOff + 3 + newSz) = res := by
        dsimp only [hdrOff, res]; omega
      have hPost5 := setSize_case5up bs0 hdrOff g.stride newSz
        (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
        (BitVec.ofNat 32 res) (by rw [hResStride]; exact hRes5) (by rw [hResStride]) (by omega)
      refine (fun {sFin P post} (h : ∀ s', s' = sFin →
          SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s' P post oom) => h sFin rfl) ?_
      intro sFin hsFin
      have hpcF : sFin.pc = b + 0x2fc#64 := by subst hsFin; simp
      have hrunF : sFin.status = .Running := by subst hsFin; simp [hrun]
      have hPermF : sFin.mem.perm = s0.mem.perm := by
        subst hsFin; exact hm3Perm.trans (hm2Perm.trans (hm1Perm.trans hPerm))
      have hbrkF : sFin.brk = s0.brk := by subst hsFin; simpa using hbrk
      have hprocF : MallocngProcPreserved s0 sFin := by
        subst hsFin
        exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
               by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
      have hspF : sFin.sp = s0.sp - 80#64 := by subst hsFin; simp [hsp]
      have halF : sFin.spAligned = true := halOf _ (by subst hsFin; simp)
      have hx19F : sFin.readReg64 .x19 = p := by subst hsFin; simp [hx19]
      have hw4F : (sFin.readReg32 .x4).truncate 8 =
          BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx) := by
        subst hsFin
        try simp only [wp_norm, arm64_norm]
        try rw [hBs3Hdr]
        exact hdrByte_res5up hBs0Hdr hIdx31 hRes5
      have hcsF : ReallocUntouchedCS s0 sFin := by
        subst hsFin
        exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
      clear hsFin
      subst hPostGoal hRestS2 hbs0
      exact realloc_s2_finish_raw_ok hb γ tp brkStart bgt ivs0 s0 sFin st hg hIdx origBs tailBs
        hOrigLen hTailLen hSlot hNewMax hFit hScLe hSc48 hNodupMeta (bsCur := bs3)
        hpcF hrunF hPermF hbrkF hprocF hspF halF hsp0 hx19F hw4F hcsF
        hBs0Len hBs3Len hLo hSt4 hEn h48 hPost5

/-- Complete raw-state Stage 2 (`+0x2cc` → `ret`) directly over
    `(MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart s0.brk liveCost peakCost st ∗ MallocngRuntime maddrs tp)`,
    without any `MallocngBudget` or `MallocngCountIvsWF` input. -/
theorem realloc_stage2_inplace_raw_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (liveCost peakCost : Nat)
    (s0 s : State) (st : MallocngSt) (hGrp : Cost.GroupsGrpBound 128 st.groups)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff newSz : Nat} (origBs tailBs : List (BitVec 8))
    (hOrigLen : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hNewMax : newSz ≤ 131051) (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    {Frame : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x2cc#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hbrk : s.brk = s0.brk) (hproc : MallocngProcPreserved s0 s)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat))
    (hx4 : s.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx5 : s.readReg64 .x5 = g.slotEnd idx)
    (hx19 : s.readReg64 .x19 = p)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hcs : ReallocUntouchedCS s0 s) :
    let sp1 := s0.sp - 80#64
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart s0.brk liveCost peakCost st ∗
       MallocngRuntime maddrs tp ∗
       MallocngBlockToken γ p oldSz ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)
      (fun sf Pf =>
        sf.mem.perm = s0.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = p ∧
        ∃ (st' : MallocngSt) (g' : GroupDesc) (newEff live' peak' : Nat),
          (Pf ⊢ stackFrame s0 800 ∗ MallocngRoTablesA maddrs ∗
            MallocngCoreStA γ maddrs brkStart sf.brk live' peak' st' ∗
            MallocngRuntime maddrs tp ∗
            ⌜(MallocngInitBlock mallocngIface γ).pureWf p (newSz, keptBs)⌝ ∗
            (MallocngInitBlock mallocngIface γ).interp p (newSz, keptBs) ∗ Frame) ∧
          g.sc < 48 ∧
          FineGroupSameGeom g' g ∧
          g'.slots = g.slots.set idx (.liveUser p newSz newEff) ∧
          newEff = (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost ∧
          st'.groups = st.groups.map (fun x => if x.metaPtr == g.metaPtr then g' else x) ∧
          st'.metaAreas = st.metaAreas ∧
          (∀ k, st'.liveMap k = if k = p then some newSz else st.liveMap k) ∧
          MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem)
      oom := by
  intro sp1 keptBs
  let bgt := synthCoarseBudgetRaw liveCost peakCost st
  let ivs0 := dynamicRootRegions st
  refine SepWP.weaken_pre (Entails.of_eq ?_)
    (realloc_stage2_inplace_readRest_raw_ok hb γ tp brkStart bgt ivs0 s0 s st hg hIdx origBs tailBs
      hOrigLen hTailLen hSlot hNewMax hFit hScLe hpc hrun hPerm hbrk hproc hsp hal hsp0
      hx3 hx4 hx5 hx19 hx21 hcs)
  have hSplit := mallocngRawEnv_eq_readRest γ maddrs tp brkStart s0.brk liveCost peakCost st hGrp
  dsimp only [bgt, ivs0]
  have hLhsAssoc :
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart s0.brk liveCost peakCost st ∗
       MallocngRuntime maddrs tp ∗
       MallocngBlockToken γ p oldSz ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame) =
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       (MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart s0.brk liveCost peakCost st ∗
        MallocngRuntime maddrs tp) ∗
       MallocngBlockToken γ p oldSz ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame) := by
    generalize (MallocngRoTablesA maddrs) = PRo
    generalize (MallocngCoreStA γ maddrs brkStart s0.brk liveCost peakCost st) = PCore
    generalize (MallocngRuntime maddrs tp) = PRt
    ac_rfl
  rw [hLhsAssoc, hSplit]
  generalize (MallocngRoTablesAt maddrs) = PRo
  generalize (MallocngReadRest γ maddrs tp brkStart s0.brk
    (synthCoarseBudgetRaw liveCost peakCost st) (dynamicRootRegions st) st) = PRest
  ac_rfl

end LibsignalBinary.Heap.Fine
