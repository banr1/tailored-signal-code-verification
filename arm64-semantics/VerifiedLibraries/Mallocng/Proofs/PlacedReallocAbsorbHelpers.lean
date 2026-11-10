/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocWfHelpers2

/-!
# In-Place `set_size` Absorption and Byte-Slice Helpers

Byte-slice lemmas (`SetSizeSlicePost`, `setSize_case0`, `setSize_case1to4`, `setSize_case5up`,
`metaBytes_write_mem_packedWord`) and separation-logic absorption (`reallocInPlace_absorb`) for
in-place `set_size` in `__libc_realloc`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Byte-Slice `set_size` and `metaBytes` Lemmas -/

/-- Byte-slice postcondition of `set_size(p, end, newSz)` on slice `bs0`, where `hdrOff` is the
    slice offset of `p - 3` and `endOff` is the slice offset of `slotEnd`
    (`hdrOff + 3 + newSz <= endOff <= bs0.length`). -/
def SetSizeSlicePost (bs0 : List (BitVec 8)) (hdrOff endOff newSz : Nat)
    (hdrByte : BitVec 8) (bsFinal : List (BitVec 8)) : Prop :=
  let res := endOff - (hdrOff + 3 + newSz)
  bsFinal.length = bs0.length ∧
  (∀ i, i < hdrOff + 3 + newSz → i ≠ hdrOff → bsFinal.getD i 0#8 = bs0.getD i 0#8) ∧
  bsFinal.getD hdrOff 0#8 = hdrByte ∧
  (1 ≤ res → bsFinal.getD (hdrOff + 3 + newSz) 0#8 = 0#8) ∧
  (5 ≤ res →
    bsFinal.getD (endOff - 5) 0#8 = 0#8 ∧
    ∀ j < 4, bsFinal.getD (endOff - 4 + j) 0#8 =
      (BitVec.ofNat 32 res).extractLsb' (8 * j) 8) ∧
  (∀ i, endOff ≤ i → bsFinal.getD i 0#8 = bs0.getD i 0#8)

theorem setSize_case0 (bs0 : List (BitVec 8)) (hdrOff endOff newSz : Nat) (hdrByte : BitVec 8)
    (hEndEq : hdrOff + 3 + newSz = endOff) (hEndLe : endOff ≤ bs0.length) :
    SetSizeSlicePost bs0 hdrOff endOff newSz hdrByte (ByteSlice.write8 bs0 hdrOff hdrByte) := by
  refine ⟨ByteSlice.write8_length bs0 hdrOff hdrByte (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro i _ hiNe
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
    simp only [hiNe, ↓reduceIte]
  · rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
    simp only [↓reduceIte]
  · intro h1; omega
  · intro h5; omega
  · intro i hi
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
    simp only [show i ≠ hdrOff by omega, ↓reduceIte]

theorem setSize_case1to4 (bs0 : List (BitVec 8)) (hdrOff endOff newSz : Nat) (hdrByte : BitVec 8)
    (h1 : 1 ≤ endOff - (hdrOff + 3 + newSz))
    (h4 : endOff - (hdrOff + 3 + newSz) ≤ 4)
    (hEndLe : endOff ≤ bs0.length) :
    SetSizeSlicePost bs0 hdrOff endOff newSz hdrByte
      (ByteSlice.write8 (ByteSlice.write8 bs0 (hdrOff + 3 + newSz) 0#8) hdrOff hdrByte) := by
  have hLen1 : (ByteSlice.write8 bs0 (hdrOff + 3 + newSz) 0#8).length = bs0.length :=
    ByteSlice.write8_length _ _ _ (by omega)
  refine ⟨(ByteSlice.write8_length _ _ _ (by omega)).trans hLen1, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hiLt hiNe
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega), ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
    simp only [hiNe, show i ≠ hdrOff + 3 + newSz by omega, ↓reduceIte]
  · rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
    simp only [↓reduceIte]
  · intro _
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega), ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
    simp only [show hdrOff + 3 + newSz ≠ hdrOff by omega, ↓reduceIte]
  · intro h5; omega
  · intro i hi
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega), ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
    simp only [show i ≠ hdrOff by omega, show i ≠ hdrOff + 3 + newSz by omega, ↓reduceIte]

theorem setSize_case5up (bs0 : List (BitVec 8)) (hdrOff endOff newSz : Nat) (hdrByte : BitVec 8)
    (res32 : BitVec 32)
    (h5 : 5 ≤ endOff - (hdrOff + 3 + newSz))
    (hRes32 : res32 = BitVec.ofNat 32 (endOff - (hdrOff + 3 + newSz)))
    (hEndLe : endOff ≤ bs0.length) :
    let bs1 := ByteSlice.write8 bs0 (hdrOff + 3 + newSz) 0#8
    let bs2 := ByteSlice.write8 bs1 (endOff - 5) 0#8
    let bs3 := ByteSlice.write32 bs2 (endOff - 4) res32
    SetSizeSlicePost bs0 hdrOff endOff newSz hdrByte (ByteSlice.write8 bs3 hdrOff hdrByte) := by
  intro bs1 bs2 bs3
  have hL1 : bs1.length = bs0.length := ByteSlice.write8_length _ _ _ (by omega)
  have hL2 : bs2.length = bs0.length := (ByteSlice.write8_length _ _ _ (by omega)).trans hL1
  have hL3 : bs3.length = bs0.length := (ByteSlice.write32_length _ _ _ (by omega)).trans hL2
  refine ⟨(ByteSlice.write8_length _ _ _ (by omega)).trans hL3, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hiLt hiNe
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega), ByteSlice.getD_write32 _ _ _ _ _ (by omega),
      ByteSlice.getD_write8 _ _ _ _ _ (by omega), ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
    simp only [hiNe, show ¬ (endOff - 4 ≤ i ∧ i < endOff - 4 + 4) by omega,
      show i ≠ endOff - 5 by omega, show i ≠ hdrOff + 3 + newSz by omega, ↓reduceIte]
  · rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
    simp only [↓reduceIte]
  · intro _
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega), ByteSlice.getD_write32 _ _ _ _ _ (by omega)]
    simp only [show hdrOff + 3 + newSz ≠ hdrOff by omega,
      show ¬ (endOff - 4 ≤ hdrOff + 3 + newSz ∧ hdrOff + 3 + newSz < endOff - 4 + 4) by omega,
      ↓reduceIte]
    by_cases hEq5 : hdrOff + 3 + newSz = endOff - 5
    · rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
      simp only [hEq5, ↓reduceIte]
    · rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega), ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
      simp only [hEq5, ↓reduceIte]
  · intro _
    refine ⟨?_, ?_⟩
    · rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega), ByteSlice.getD_write32 _ _ _ _ _ (by omega),
        ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
      simp only [show endOff - 5 ≠ hdrOff by omega,
        show ¬ (endOff - 4 ≤ endOff - 5 ∧ endOff - 5 < endOff - 4 + 4) by omega, ↓reduceIte]
    · intro j hj
      rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega), ByteSlice.getD_write32 _ _ _ _ _ (by omega),
        hRes32]
      have hSub : endOff - 4 + j - (endOff - 4) = j := by omega
      simp only [show endOff - 4 + j ≠ hdrOff by omega,
        show endOff - 4 ≤ endOff - 4 + j ∧ endOff - 4 + j < endOff - 4 + 4 by omega,
        and_self, ↓reduceIte, hSub]
  · intro i hi
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega), ByteSlice.getD_write32 _ _ _ _ _ (by omega),
      ByteSlice.getD_write8 _ _ _ _ _ (by omega), ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
    simp only [show i ≠ hdrOff by omega,
      show ¬ (endOff - 4 ≤ i ∧ i < endOff - 4 + 4) by omega,
      show i ≠ endOff - 5 by omega, show i ≠ hdrOff + 3 + newSz by omega, ↓reduceIte]

theorem metaBytes_write_mem_packedWord (g : GroupDesc) (newMem : BitVec 64) (newMaplen : Nat)
    (newPw : BitVec 64)
    (hPwEq : newPw = ({ g with mem := newMem, maplen := newMaplen } : GroupDesc).packedWord) :
    ByteSlice.write64 (ByteSlice.write64 g.metaBytes 16 newMem) 32 newPw =
      ({ g with mem := newMem, maplen := newMaplen } : GroupDesc).metaBytes := by
  subst hPwEq
  rfl

/-! ## In-Place `set_size` Separation-Logic Absorption -/

set_option maxHeartbeats 400000 in
theorem reallocInPlace_absorb (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 sf : State) (st : MallocngSt)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff newSz al : Nat}
    (origBs tailBs : List (BitVec 8))
    (_hOrigLen : origBs.length ≤ oldSz) (_hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hNewMax : newSz ≤ 131051)
    (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    (hTp : sf.tpidrEl0 = tp) (hBrkStart : sf.brkStart = brkStart)
    (hDelta : MallocngMappedDelta 0 0 s0.mem sf.mem)
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
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ st.ctx.toBytes) ∗
    ByteMap st.masterDom
      (fun a => OwnedRwByte st a ∧ ¬ InRegion (g.slotStart idx - 4#64) g.stride a) st.byteVal ∗
    ((g.slotStart idx - 4#64) ↦ₛ slotBsFinal) ∗
    MallocngReadRest γ A tp brkStart sf.brk b ivs0 st ∗
    MallocngTightBlock γ p oldSz al ⊢
      |==> (MallocngPostEnv mallocngIface γ A tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngTightInitBlock γ al).pureWf p (newSz, keptBs)⌝ ∗
            (MallocngTightInitBlock γ al).interp p (newSz, keptBs)) := by
  intro bf keptBs
  unfold MallocngReadRest
  refine Entails.trans (Entails.of_eq (by
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
    ac_rfl : _ =
      ⌜MallocngCountIvsWF b ivs0 st ∧ MallocngWF A.base brkStart sf.brk b.liveCost b.peakCost st⌝ ∗
      ((MallocngLiveAuth γ st.liveMap ∗ MallocngTightBlock γ p oldSz al) ∗
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
  obtain ⟨hNewBWf, hCount', hwf', hRwOut, hRwIn⟩ :=
    reallocInPlace_wf hCount hwf hg hIdx origBs hSlot hNewMax hFit hScLe
      slotBsFinal hFinalLen hKeepPre hHdrP3 hRes1 hRes5
  let val' := writeBytesToMap st.byteVal (g.slotStart idx - 4#64) slotBsFinal
  let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
  let g' := { g with slots := g.slots.set idx (.liveUser p newSz newEff) }
  let liveMap' := (st.liveMap.erase p).insert p newSz (st.liveMap.ov p)
  let st' : MallocngSt :=
    { st with groups := replaceGroup st.groups g.metaPtr g', byteVal := val', liveMap := liveMap' }
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
    obtain ⟨hmDisjAp, hmDisjGp⟩ := protNone_disjoint_slotWriteMod hwf hg hIdx
    have hNotS : ¬ InRegion (g.slotStart idx - 4#64) slotBsFinal.length a := by
      rw [hFinalLen]; intro hS
      by_cases hEq0 : a = g.slotStart idx - 4#64
      · subst hEq0
        obtain ⟨rg, hrg, hMpRg, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
        have hRg48 := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
        have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRg]
        obtain ⟨hP123, _, hC123Rg⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
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
    obtain ⟨hg'Mem, hGsCases, hGsKeep, _, _, _⟩ := replaceGroup_props st.groups g g' hg hwf.groups_nodup.1 rfl
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
    · intro k hk1 hk2
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
  have hPureInit : (MallocngTightInitBlock γ al).pureWf p (newSz, keptBs) :=
    ⟨hNewBWf.1, hNewBWf.2.1, Nat.lt_of_le_of_lt hNewBWf.2.2.1 (by decide), by omega⟩
  have hNoOrph : MallocngNoOrphanMappings ivs0 ivs0 s0.mem sf.mem :=
    noOrphanMappings_refl_of_delta_zero hDelta
  refine Entails.trans (sepConj_mono_left
      (mallocngTightBlock_replaceOv_bupd γ st.liveMap p oldSz p newSz al hNewBWf (Or.inl rfl)))
    (Entails.trans (bupd_frame_r _ _) (bupd_mono ?_))
  rw [hAbs, hExtU, hByteEq, hPnEq, hMpSetEq]
  have hRepack := mallocngHeap_read_liveUser_repack γ A tp brkStart sf.brk bf ivs0 st'
  unfold MallocngReadRest at hRepack
  refine Entails.trans (Entails.of_eq (by
    change _ = _
    rw [show st.auxvPtr = st'.auxvPtr from rfl, show st.auxvSnap = st'.auxvSnap from rfl]
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngAuxvState γ st'.auxvPtr st'.auxvSnap) = PAu
    ac_rfl : _ =
      (MallocngRoTablesAt A ∗
       (A.ctx ↦ₛ st'.ctx.toBytes) ∗
       ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
       (MallocngLiveAuth γ st'.liveMap ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        ((A.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗
        MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
        ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
        MappedSet st'.masterDom (OwnedMappedByte st') ∗
        MallocngRuntime A tp)) ∗
      (MallocngTightBlock γ p newSz al ∗ (p ↦ₛ readBytesFromMap val' p newSz)))) ?_
  refine Entails.trans (sepConj_mono
    (Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (Entails.pure_right ⟨hCount', hwf'⟩ (Entails.refl _))))) hRepack)
    (sepConj_mono_right hUserInit)) ?_
  unfold MallocngPostEnv MallocngEnv
  refine Entails.trans ?_ (sepConj_mono_left (Entails.sepExists_intro ivs0))
  rw [pure_sepConj_of_true hNoOrph, pure_sepConj_of_true ⟨hTp, hBrkStart⟩, pure_sepConj_of_true hPureInit]
  show (mallocngIface.MallocngHeap γ A tp brkStart sf.brk bf ivs0 ∗
    (MallocngTightBlock γ p newSz al ∗
     ((p ↦ₛ keptBs) ∗ memRegion (p + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length)))) ⊢
    mallocngIface.MallocngHeap γ A tp brkStart sf.brk bf ivs0 ∗
    (MallocngTightBlock γ p newSz al ∗ (p ↦ₛ keptBs) ∗
     memRegion (p + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length))
  exact Entails.of_eq (by ac_rfl)

end VerifiedLibraries.Mallocng.Proofs
