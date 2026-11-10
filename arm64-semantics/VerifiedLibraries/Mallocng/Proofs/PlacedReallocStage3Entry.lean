/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocStage4

/-!
# Placed `__libc_realloc` Stage 3 Entry

Proves `realloc_stage3_mremap_ok` from `+0x324` to `ret`: falls back to Stage 4 (`+0x260`) when
`g.sc < 48 ∨ newSz ≤ 131051` or when `__mremap` returns `MAP_FAILED`, and otherwise resizes an
individual-`mmap` group (`g.sc = 63 ∧ 131051 < newSz`) in place or via `placed_mremapWrapper_perm_ok`
and `realloc_s3_post_mremap_ok`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Bitvector and Spatial Repack Helpers -/

theorem sepWP_abstract_all {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ (P' : SepProp) (post' : State → SepProp → Prop) (oom' : State → SepProp),
      P' = P → post' = post → oom' = oom → SepWP prog target_pc s P' post' oom') :
    SepWP prog target_pc s P post oom :=
  h P post oom rfl rfl rfl

set_option maxRecDepth 20000 in
private theorem mremap_tight_oom_bounds {newSz extra oldSz maplen phys peakCount : Nat}
    (hNewLo : 131051 < newSz)
    (hOldFit : 16 + extra + oldSz + 4 ≤ maplen * 4096)
    (hPhys : phys + maplen * 4096 < (newSz + extra + 4115) / 4096 * 4096) :
    PAGE_SIZE ≤ pageAlignUp newSz ∧
    pageAlignUp newSz % PAGE_SIZE = 0 ∧
    pageAlignUp newSz ≤ MallocngTightStepBound newSz peakCount ∧
    ([].map (@Prod.snd (BitVec 64) Nat)).sum + pageAlignUp newSz ≤
      MallocngTightTotalBound newSz peakCount ∧
    phys < pageAlignUp newSz := by
  have h1 : newSz + extra + 4115 ≤ (newSz + 4095) + maplen * 4096 := by omega
  have h2 : (newSz + extra + 4115) / 4096 ≤ (newSz + 4095) / 4096 + maplen := by
    have hd := Nat.div_le_div_right (c := 4096) h1
    rwa [Nat.add_mul_div_right _ _ (by decide : 0 < 4096)] at hd
  have hNeedLe : (newSz + extra + 4115) / 4096 * 4096 ≤ pageAlignUp newSz + maplen * 4096 := by
    unfold pageAlignUp PAGE_SIZE
    simpa [Nat.add_mul] using Nat.mul_le_mul_right 4096 h2
  have hPgGe : PAGE_SIZE ≤ pageAlignUp newSz := by unfold pageAlignUp PAGE_SIZE; omega
  have hPgMod : pageAlignUp newSz % PAGE_SIZE = 0 := Nat.mul_mod_left _ 4096
  rw [List.map_nil, List.sum_nil, Nat.zero_add]
  have hPA : pageAlignUp newSz ≤ newSz + 4095 := by unfold pageAlignUp PAGE_SIZE; omega
  have hPhysLt : phys < pageAlignUp newSz := by omega
  rw [MallocngTightStepBound_eq, MallocngTightTotalBound_eq]
  exact ⟨hPgGe, hPgMod, Nat.le_trans (by omega) (Nat.le_max_right _ _),
    Nat.le_trans (by omega) (Nat.le_max_right _ _), hPhysLt⟩

private theorem mremap_needed_le_tight {newSz extra over ov al peakCount : Nat}
    (hOffLe : extra ≤ over + 255 * 16) (hOverLe : over ≤ MaxAlignedAllocAlign - 16)
    (hOverOv : over ≤ ov) (hOvAl : ov ≤ al - 16) :
    (newSz + extra + 4115) / 4096 * 4096 ≤
      MallocngTightStepBound (mallocngReallocRes al newSz) peakCount := by
  rw [MallocngTightStepBound_eq]
  unfold mallocngReallocRes
  have hMaxVal : MaxAlignedAllocAlign = 2 ^ 31 := rfl
  have hDiv : (newSz + extra + 4115) / 4096 * 4096 ≤ newSz + extra + 4115 := Nat.div_mul_le_self _ _
  omega

private theorem entails_pure_of_pair {A B C Q : SepProp} {φ : Prop}
    (hAB : A ∗ B ⊢ ⌜φ⌝ ∗ A ∗ B) (h : φ → (A ∗ B ∗ C ⊢ Q)) : A ∗ B ∗ C ⊢ Q := by
  refine Entails.trans (Entails.of_eq (sepConj_assoc A B C).symm) ?_
  refine Entails.trans (sepConj_mono_left hAB) ?_
  refine Entails.trans (Entails.of_eq (sepConj_assoc _ _ C)) ?_
  refine Entails.pure_left fun hφ => ?_
  exact Entails.trans (Entails.of_eq (sepConj_assoc A B C)) (h hφ)

private theorem packedWord_sc63_mask_trunc (g : GroupDesc) (hLast : g.lastIdx ≤ 31)
    (hSc63 : g.sc = 63) (hMap : g.maplen < 2 ^ 52) :
    BitVec.truncate 32 ((g.packedWord.extractLsb' 0 16).zeroExtend 64 &&& 17317308141504#64) =
      0xfc0#32 := by
  have hTr : ∀ x : BitVec 16,
      BitVec.truncate 32 (x.zeroExtend 64 &&& 17317308141504#64) = x.zeroExtend 32 &&& 0xfc0#32 :=
    fun _ => by bv_robdd
  rw [hTr]; exact packedWord_sc63_mask g hLast hSc63 hMap

private theorem extract_to_mremap [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 : State) {st : MallocngSt}
    (hwf : MallocngWF maddrs.base brkStart s0.brk bgt.liveCost bgt.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff al : Nat} (origBs tailBs : List (BitVec 8))
    (hUserLen : (origBs ++ tailBs).length = oldSz)
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    (sp1 : BitVec 64) (Frame : SepProp) :
    (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
     MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
     ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
     MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
     MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame) ⊢
      ⌜st.liveMap.ov p ≤ al - 16⌝ ∗
      ∃∗ errnoVal : BitVec 32,
        (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)) ∗
        ((g.metaPtr ↦ₛ g.metaBytes) ∗
         memMapped g.mem (g.maplen * 4096) ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
         ReallocMremapFrame maddrs tp st g ∗
         ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
         MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
         MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
         (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
         ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
         MallocngTightBlock γ p oldSz al ∗ Frame) := by
  unfold MallocngReadRest
  have hExt := reallocMremap_extract maddrs tp hwf hg hIdx0 (origBs ++ tailBs)
    hUserLen hSlot0 hSc63
  refine Entails.trans (Q :=
      ⌜MallocngCountIvsWF bgt ivs0 st ∧
        MallocngWF maddrs.base brkStart s0.brk bgt.liveCost bgt.peakCost st⌝ ∗
      ((ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st) ∗
        MallocngRuntime maddrs tp ∗ (p ↦ₛ (origBs ++ tailBs))) ∗
       (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
        (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MallocngTightBlock γ p oldSz al ∗ Frame)))
    (Entails.of_eq (by
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngRuntime maddrs tp) = PRt
      generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
      ac_rfl)) ?_
  refine Entails.pure_left fun _ => ?_
  refine Entails.trans (Q := MallocngLiveAuth γ st.liveMap ∗ MallocngTightBlock γ p oldSz al ∗
      (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st) ∗
        MallocngRuntime maddrs tp ∗ (p ↦ₛ (origBs ++ tailBs))) ∗
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        (maddrs.lock ↦₃₂ 0#32) ∗
        (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ Frame))
    (Entails.of_eq (by
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngRuntime maddrs tp) = PRt
      generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
      ac_rfl)) ?_
  refine entails_pure_of_pair (mallocngTightBlock_lookup γ st.liveMap p oldSz al)
    fun ⟨_, _, hOv⟩ => Entails.pure_right hOv ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hExt))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_mono fun errnoVal => Entails.of_eq ?_
  generalize (MallocngRoTablesAt maddrs) = PRo
  generalize (ReallocMremapFrame maddrs tp st g) = PFr
  generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
  ac_rfl

private theorem not_add_one_eq_zero_of_le_48 {x : BitVec 64}
    (h : x.toNat ≤ 2 ^ 48) (heq : x + 1#64 = 0#64) : False := by
  have ht := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
  omega

theorem unsplit_user_bytes (p : BitVec 64) (origBs tailBs : List (BitVec 8)) (oldSz : Nat)
    (hTailLen : tailBs.length = oldSz - origBs.length) :
    (p ↦ₛ (origBs ++ tailBs)) ⊢
      (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) := by
  rw [pointsToBytes_append]
  refine sepConj_mono_right ?_
  simpa [hTailLen] using (IsBlock.pointsToBytes (p + BitVec.ofNat 64 origBs.length) tailBs).entails_memRegion

theorem repack_read_to_stage4 [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    {p : BitVec 64} {oldSz al : Nat} (origBs tailBs : List (BitVec 8))
    (hTailLen : tailBs.length = oldSz - origBs.length)
    (hbrk : s.brk = s0.brk) (htp : s.tpidrEl0 = tp) (hbrks : s.brkStart = brkStart)
    (sp1 : BitVec 64) (Frame : SepProp) :
    (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
     MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
     ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
     MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
     MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame) ⊢
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s ∗
       MallocngTightBlock γ p oldSz al ∗
       (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ∗
       Frame) := by
  have hHeap := mallocngHeap_read_liveUser_repack γ maddrs tp brkStart s0.brk bgt ivs0 st
  have hEnv : mallocngIface.MallocngHeap γ maddrs tp brkStart s0.brk bgt ivs0 ⊢
      MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s := by
    unfold MallocngEnv
    rw [hbrk]; exact Entails.pure_right ⟨htp, hbrks⟩ (Entails.refl _)
  have hUser := unsplit_user_bytes p origBs tailBs oldSz hTailLen
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.trans (Q :=
      (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) ∗
      MallocngTightBlock γ p oldSz al ∗
      (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)
    (Entails.of_eq (by
      show _ = (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) ∗
        MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) = PRest
      ac_rfl)) ?_
  refine sepConj_mono (Entails.trans hHeap hEnv) (sepConj_mono_right ?_)
  exact Entails.trans (sepConj_mono_left hUser) (Entails.of_eq (by ac_rfl))

private theorem unextract_to_stage4 [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) {st : MallocngSt}
    (hCount : MallocngCountIvsWF bgt ivs0 st)
    (hwf : MallocngWF maddrs.base brkStart s0.brk bgt.liveCost bgt.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff al : Nat} (origBs tailBs : List (BitVec 8))
    (hUserLen : (origBs ++ tailBs).length = oldSz)
    (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    (hbrk : s.brk = s0.brk) (htp : s.tpidrEl0 = tp) (hbrks : s.brkStart = brkStart)
    (sp1 : BitVec 64) (Frame : SepProp) :
    (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
     ((tp - 0xa4#64) ↦₃₂ 12#32) ∗
     (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)) ∗
     memMapped g.mem (g.maplen * 4096) ∗
     (g.metaPtr ↦ₛ g.metaBytes) ∗
     MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
     ReallocMremapFrame maddrs tp st g ∗
     MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
     (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
     ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
     ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
     MallocngTightBlock γ p oldSz al ∗ Frame) ⊢
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s ∗
       MallocngTightBlock γ p oldSz al ∗
       (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ∗
       Frame) := by
  have hUn := reallocMremap_unextract γ maddrs tp brkStart s0.brk bgt ivs0
    hCount hwf hg hIdx0 (origBs ++ tailBs) hUserLen hSlot0 hSc63 12#32
  have hEnv : mallocngIface.MallocngHeap γ maddrs tp brkStart s0.brk bgt ivs0 ⊢
      MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s := by
    unfold MallocngEnv
    rw [hbrk]; exact Entails.pure_right ⟨htp, hbrks⟩ (Entails.refl _)
  have hUser := unsplit_user_bytes p origBs tailBs oldSz hTailLen
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.trans (Q :=
      (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       (g.metaPtr ↦ₛ g.metaBytes) ∗
       (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)) ∗
       memMapped g.mem (g.maplen * 4096) ∗
       ((tp - 0xa4#64) ↦₃₂ 12#32) ∗
       ReallocMremapFrame maddrs tp st g ∗
       MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
       (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
       ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) ∗
      MallocngTightBlock γ p oldSz al ∗ Frame)
    (Entails.of_eq (by
      show _ = _ ∗ MallocngTightBlock γ p oldSz al ∗ Frame
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (ReallocMremapFrame maddrs tp st g) = PFr
      generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
      ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hUn) ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono hEnv hUser)) ?_
  exact Entails.of_eq (by
    generalize (MallocngEnv mallocngIface γ maddrs tp brkStart bgt ivs0 s) = PEnv
    ac_rfl)

/-! ## Stage 3 Entry -/

set_option maxHeartbeats 400000 in
/-- Stage 3 of `__libc_realloc` from `+0x324` to `ret`: falls back to Stage 4 (`+0x260`) when
    `g.sc < 48 ∨ newSz ≤ 131051` or when `__mremap` returns `-1`, and resizes individual-`mmap`
    allocations (`g.sc = 63 ∧ 131051 < newSz`) via `realloc_s3_post_mremap_ok`. -/
theorem realloc_stage3_mremap_ok [MallocngMultiPlacement]
    (hImpl : LibcMallocImplPlacedTightKStmt) (hFree : LibcFreePlacedStmt)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    {p : BitVec 64} {oldSz oldEff newSz al : Nat}
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (origBs tailBs : List (BitVec 8))
    (hpNe : p ≠ 0#64)
    (hOrigLe : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hF : LiveUserBlockFacts st g idx p oldSz oldEff)
    (hNewMax : newSz ≤ MallocngMaxAllocSize)
    {Frame : SepProp}
    (hpc : s.pc = b + 0x324#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hbrk : s.brk = s0.brk)
    (hproc : MallocngProcPreserved s0 s)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = g.mem)
    (hx1 : s.readReg64 .x1 = g.packedWord)
    (hx2 : s.readReg64 .x2 = 131051#64)
    (hx6 : s.readReg64 .x6 = BitVec.ofNat 64 g.sc)
    (hx7 : s.readReg64 .x7 = (g.packedWord.extractLsb' 0 16).zeroExtend 64)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = g.slotStart idx)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hx22 : s.readReg64 .x22 = g.metaPtr)
    (hx23 : s.readReg64 .x23 = p + BitVec.ofNat 64 oldSz)
    (hx24 : s.readReg64 .x24 = 0#64)
    (hcs : ReallocUntouchedCS s0 s)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem) :
    let sp1 := s0.sp - 80#64
    let bf := mallocngReallocBudget true (some (oldSz, origBs)) newSz bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
       MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)
      (fun sf Pf =>
        ∃ q : BitVec 64,
          MallocngCallAccounting 16
            (MallocngTightStepBound (mallocngReallocRes al newSz) bgt.peakCount) s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
          (Pf ⊢ stackFrame s0 800 ∗
            MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngTightInitBlock γ al).pureWf q (newSz, keptBs)⌝ ∗
            (MallocngTightInitBlock γ al).interp q (newSz, keptBs) ∗
            Frame))
      (fun sf => ⌜MallocngTightOomCond msvc newSz bgt.peakCount s0 sf⌝) := by
  intro sp1 bf keptBs; have _ := hb
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMaxLt64 : MallocngMaxAllocSize < 2 ^ 64 := maxAllocSize_lt_pow64
  have hpOld48 : p.toNat + oldSz ≤ 2 ^ 48 :=
    Nat.le_trans hF.p_add_n_le_end hF.stride_bounds.2.2.2.2.2
  have hUserLen : (origBs ++ tailBs).length = oldSz := by simp [hTailLen]; omega
  apply sepWP_abstract_all; intro PGoal1 postGoal1 oomGoal1 hPG1 hPostG1 hOomG1
  wp_step; wp_step; wp_step
  wp_if hls
  ·
    subst hPG1 hPostG1 hOomG1
    apply sepWP_bind_state; intro sA hsA
    have hbrkA : sA.brk = s0.brk := by rw [hsA]; simpa using hbrk
    have htpA : sA.tpidrEl0 = tp := by rw [hsA]; simpa [htp0] using hproc.2.2.1
    have hbrksA : sA.brkStart = brkStart := by rw [hsA]; simpa [hbrks0] using hproc.2.2.2.1
    refine SepWP.weaken_pre
      (repack_read_to_stage4 (al := al) γ tp brkStart bgt ivs0 s0 sA st origBs tailBs hTailLen
        hbrkA htpA hbrksA sp1 Frame) ?_
    exact realloc_stage4_oop_ok (al := al) hImpl hFree hb γ tp brkStart bgt ivs0 s0 sA origBs
      hpNe hpOld48 hOrigLe hNewMax
      (by rw [hsA]; simp only [wp_norm, arm64_norm, hb])
      (by rw [hsA]; simp [hrun])
      (by rw [hsA]; simpa using hPerm)
      ⟨by rw [hsA]; simpa using hproc.1, by rw [hsA]; simpa using hproc.2.1,
       by rw [hsA]; simpa using hproc.2.2.1, by rw [hsA]; simpa using hproc.2.2.2.1,
       by rw [hsA]; simpa using hproc.2.2.2.2.1, by rw [hsA]; simpa using hproc.2.2.2.2.2.1,
       by rw [hsA]; simpa using hproc.2.2.2.2.2.2⟩
      (by rw [hsA]; simpa using hsp)
      (by rw [hsA]; simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal)
      hsp0
      (by rw [hsA]; simpa using hx19)
      (by rw [hsA]; simpa using hx21)
      (by rw [hsA]; simpa using hx23)
      ⟨by rw [hsA]; simpa using hcs.1, by rw [hsA]; simpa using hcs.2.1,
       by rw [hsA]; simpa [calleeSavedVRegs] using hcs.2.2⟩
      (by rw [hsA]; simpa using hcl)
  ·
    have ⟨hSc63, hNewLo⟩ : g.sc = 63 ∧ 131051 < newSz := by
      have hw6 : BitVec.truncate 32 (BitVec.ofNat 64 g.sc) = BitVec.ofNat 32 g.sc := by bv_omega
      rw [hw6] at hls
      rcases hF.sc_cases with h48 | h63
      · exfalso; apply hls
        have hUltF : (47#32).ult (BitVec.ofNat 32 g.sc) = false := by
          rw [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
          change ¬ 47 < g.sc % 4294967296; omega
        rw [hUltF]; simp only [Bool.false_eq_true, ↓reduceIte]; decide
      · refine ⟨h63, Classical.byContradiction fun hLe => hls ?_⟩
        have hUltT : (47#32).ult (BitVec.ofNat 32 63) = true := by decide
        rw [h63, hUltT]; simp only [↓reduceIte, BitVec.ule, decide_eq_true_eq, BitVec.toNat_ofNat]
        omega
    subst hPG1 hPostG1 hOomG1
    apply sepWP_pure_of_sat (fun R hm =>
      satisfies_readRest_wf (Rest := ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
        stackFrameAt sp1 720 ∗ MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame ∗ R)
        (Satisfies.mono (Entails.of_eq (by
          generalize (MallocngRoTablesAt maddrs) = PRo
          generalize (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) = PRest
          ac_rfl)) hm))
    rintro ⟨hCount, hwf⟩
    obtain ⟨hIdxEq0, _hLast0, _, hMpPos, _, _, _, _,
            hMemGe, hMemDvd, hMemFit, _, _, _, hLoP, _, hExtraBound,
            hOldSlotFit, _hNewSlotFit, _, hPageIdem, _hNeedLo, _hNeedDvd,
            _hNeedMax, _hStep, _⟩ :=
      sc63_liveUser_bounds hCount hwf hg hIdx hSlot hSc63 hNewLo hNewMax
    subst hIdxEq0
    let extra := p.toNat - (g.slotStart 0).toNat
    let oldLen := g.maplen * 4096
    let needed := ((newSz + extra + 4115) / 4096) * 4096
    let oldMapBs := mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)
    have hOldMapLen : oldMapBs.length = oldLen :=
      mkSc63OldMapBs_length st.byteVal g p oldSz (origBs ++ tailBs) hUserLen
        (Nat.le_trans (by have ⟨_, _, hSt, _, _, _, _, _, _⟩ := group_slot_bounds (hwf.groups_wf g hg) hIdx; omega) hLoP)
        (by omega)
    refine SepWP.weaken_pre
      (extract_to_mremap (al := al) γ tp brkStart bgt ivs0 s0 hwf hg hIdx origBs tailBs hUserLen hSlot hSc63 sp1 Frame) ?_
    apply SepWP.pure_elim; intro hOvAl
    have hStepT : needed ≤ MallocngTightStepBound (mallocngReallocRes al newSz) bgt.peakCount := by
      have hsw := (hwf.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 hIdx
      rw [hSlot] at hsw
      obtain ⟨_, _, _, _, _, _, _, _, ⟨hOffLe, hOverLe, hOverOv⟩, _⟩ := hsw
      exact mremap_needed_le_tight hOffLe hOverLe hOverOv hOvAl
    apply SepWP.exists_left; intro errnoVal
    apply sepWP_pure_of_sat (φ := ∀ x, InRegion g.mem oldLen x → s0.mem.perm x = some Perm.rw)
      (fun R hm => by
        intro x hx
        rw [sepConj_assoc] at hm
        have hRw := (IsBlock.pointsToBytes g.mem oldMapBs).perm_rw hm
          (by simpa [hOldMapLen] using hx)
        simpa [hPerm] using hRw)
    intro hOldRw
    have hMapLt52 : g.maplen < 2 ^ 52 := by
      have hgw := hwf.groups_wf g hg
      have hTot : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpPos]
      have hFit := hgw.2.2.2.2.2.2.1
      omega
    have hSubExtra : p - g.slotStart 0 = BitVec.ofNat 64 extra := by
      dsimp only [extra]; bv_omega
    have hAdd25a : BitVec.ofNat 64 newSz + 4115#64 = BitVec.ofNat 64 (newSz + 4115) := by bv_omega
    have hAdd25b : BitVec.ofNat 64 (newSz + 4115) + BitVec.ofNat 64 extra =
        BitVec.ofNat 64 (newSz + extra + 4115) := by
      dsimp only [extra] at hExtraBound ⊢; bv_omega
    have hMapMask : g.packedWord &&& -4096#64 = BitVec.ofNat 64 oldLen :=
      packedWord_maplen_mask g hF.last_le_31 (hSc63 ▸ by decide) (Nat.le_trans (Nat.le_add_left _ _) hMemFit)
    have hNeedMask : BitVec.ofNat 64 (newSz + extra + 4115) &&& -4096#64 = BitVec.ofNat 64 needed :=
      and_neg4096_eq_pageMul (by dsimp only [extra] at hExtraBound ⊢; omega)
    apply sepWP_abstract_all; intro PGoal2 postGoal2 oomGoal2 hPG2 hPostG2 hOomG2
    wp_step; wp_step; wp_step
    wp_if hne7
    · exfalso
      exact hne7 (packedWord_sc63_mask_trunc g hF.last_le_31 hSc63 hMapLt52)
    ·
      wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
      wp_if hneLen
      ·
        wp_step; wp_step; wp_step
        subst hPG2 hPostG2 hOomG2
        apply sepWP_bind_state; intro sCall hsCall
        have hspCall : sCall.sp = sp1 := by rw [hsCall]; simpa using hsp
        have hmemCall : sCall.mem = s.mem := by rw [hsCall]; simp
        have htpCall : sCall.tpidrEl0 = tp := by rw [hsCall]; simpa [htp0] using hproc.2.2.1
        have hx0Call : sCall.readReg64 .x0 = g.mem := by
          rw [hsCall]; dsimp only [Reg.x0] at hx0 ⊢; simpa using hx0
        have hx1Call : (sCall.readReg64 .x1).toNat = oldLen := by
          have hx1v : sCall.readReg64 .x1 = BitVec.ofNat 64 oldLen := by
            rw [hsCall]; simp only [wp_norm, arm64_norm]
          rw [hx1v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hx2Call : (sCall.readReg64 .x2).toNat = needed := by
          have hx2v : sCall.readReg64 .x2 = BitVec.ofNat 64 needed := by
            rw [hsCall]; simp only [wp_norm, arm64_norm]
          rw [hx2v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hx3Call : sCall.readReg32 .x3 = 1#32 := by rw [hsCall]; simp [wp_norm, arm64_norm]
        have hclCall : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sCall.mem := by rwa [hmemCall]
        have hSf144 : stackFrameAt sp1 720 = (stackFrame sCall 144 ∗ stackFrameAt (sp1 - 144#64) 576) := by
          rw [stackFrameAt_720_split sp1 144 576 (by decide),
              ← stackFrame_eq_stackFrameAt_720 144 (by decide) hspCall]
        have hMrSpec := placed_mremapWrapper_perm_ok (P := blkPC_b14.rebase b (fun _ => none))
          tp g.mem errnoVal oldMapBs oldLen needed hOldMapLen
          (by dsimp only [oldLen]; omega) (Nat.dvd_mul_left 4096 g.maplen)
          hMemDvd hMemFit (by omega) (by intro pc; simp) rfl
        refine SepWP.call_subroutine_frame hMrSpec (x := ())
          (F := stackFrameAt (sp1 - 144#64) 576 ∗
            (g.metaPtr ↦ₛ g.metaBytes) ∗ ReallocMremapFrame maddrs tp st g ∗
            ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
            MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
            MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
            (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
            ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
            ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
            MallocngTightBlock γ p oldSz al ∗ Frame)
          (ret_pc := b + 0x3e0#64)
          (by rw [hsCall]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
          (by rw [hsCall]; simp [hrun])
          (by rw [hsCall]; simpa [State.spAligned] using hal)
          (by rw [hsCall]; simp)
          (fun R' hm => by
            dsimp only [withCL]
            refine Satisfies.mono ?_ hm
            rw [hSf144]
            refine Entails.trans (Q :=
                (stackFrame sCall 144 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
                 (g.mem ↦ₛ oldMapBs) ∗ memMapped g.mem oldLen) ∗
                (stackFrameAt (sp1 - 144#64) 576 ∗
                 (g.metaPtr ↦ₛ g.metaBytes) ∗ ReallocMremapFrame maddrs tp st g ∗
                 ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
                 MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
                 MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                 (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
                 ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
                 ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                 MallocngTightBlock γ p oldSz al ∗ Frame) ∗ R')
              (Entails.of_eq (by
                generalize (MallocngRoTablesAt maddrs) = PRo
                generalize (ReallocMremapFrame maddrs tp st g) = PFr
                generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
                ac_rfl)) ?_
            refine sepConj_mono_left ?_
            rw [sepConj_comm _ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sCall.mem⌝]
            exact Entails.pure_right hclCall
              (Entails.pure_right ⟨htpCall, hx0Call, hx1Call, hx2Call, hx3Call⟩ (Entails.refl _)))
          (fun _ _ _ hp => not_satisfies_false_sepConj hp)
          (fun _ _ _ _ he => not_satisfies_false_sepConj he)
          ?_
          (fun R' sf _ ho => by
            dsimp only [withCL] at ho
            rw [sepConj_assoc, satisfies_pure_sepConj] at ho
            obtain ⟨⟨hfsO, htrO, hsigO, hpermO, _, hphysO⟩, hmO⟩ := ho
            have hpermCall : sCall.mem.perm = s0.mem.perm := by rwa [hmemCall]
            have hfsCall : sCall.fs = s0.fs := by rw [hsCall]; simpa using hproc.1
            have htrCall : sCall.trace = s0.trace := by rw [hsCall]; simpa using hproc.2.1
            have hsigCall : sCall.sigActions = s0.sigActions := by rw [hsCall]; simpa using hproc.2.2.2.2.2.2
            rw [hPageIdem] at hphysO
            obtain ⟨hPgGe, hPgMod, hPgStep, hPgTot, hPhysNew⟩ :=
              mremap_tight_oom_bounds (peakCount := bgt.peakCount) hNewLo hOldSlotFit hphysO
            have hpermSf : sf.mem.perm = s0.mem.perm := hpermO.trans hpermCall
            exact Satisfies.pure_intro
              ⟨hfsO.trans hfsCall, htrO.trans htrCall, hsigO.trans hsigCall,
               [], Nat.zero_le _, Nat.zero_le _, fun a ha => Or.inl (hpermSf ▸ ha),
               fun _ => ⟨pageAlignUp newSz, hPgGe, hPgMod, hPgStep, hPgTot, Or.inr hPhysNew⟩⟩
              (Satisfies.drop_left (Satisfies.drop_left hmO)))
        intro sMr hpcMr hrunMr hspMr hcsMr
        obtain ⟨h19Mr, h20Mr, h21Mr, h22Mr, h23Mr, h24Mr, h25Mr, h26Mr, h27Mr, h28Mr, _, hVrMr⟩ := hcsMr
        have hx19Mr : sMr.readReg64 .x19 = p := by
          rw [h19Mr, hsCall]; dsimp only [Reg.x19] at hx19 ⊢; simpa using hx19
        have hx20Mr : sMr.readReg64 .x20 = BitVec.ofNat 64 extra := by
          rw [h20Mr, hsCall]; simp only [wp_norm, arm64_norm]
        have hx21Mr : sMr.readReg64 .x21 = BitVec.ofNat 64 newSz := by
          rw [h21Mr, hsCall]; dsimp only [Reg.x21] at hx21 ⊢; simpa using hx21
        have hx22Mr : sMr.readReg64 .x22 = g.metaPtr := by
          rw [h22Mr, hsCall]; dsimp only [Reg.x22] at hx22 ⊢; simpa using hx22
        have hx23Mr : sMr.readReg64 .x23 = p + BitVec.ofNat 64 oldSz := by
          rw [h23Mr, hsCall]; dsimp only [Reg.x23] at hx23 ⊢; simpa using hx23
        have hx24Mr : sMr.readReg64 .x24 = 0#64 := by
          rw [h24Mr, hsCall]; dsimp only [Reg.x24] at hx24 ⊢; simpa using hx24
        have hx25Mr : sMr.readReg64 .x25 = BitVec.ofNat 64 (newSz + extra + 4115) := by
          rw [h25Mr, hsCall]; simp only [wp_norm, arm64_norm]
        have hx26Mr : sMr.readReg64 .x26 = BitVec.ofNat 64 needed := by
          rw [h26Mr, hsCall]; simp only [wp_norm, arm64_norm]
        have hcs0Mr : ReallocUntouchedCS s0 sMr :=
          ⟨by rw [h27Mr, hsCall]; dsimp only [Reg.x27]; simpa using hcs.1,
           by rw [h28Mr, hsCall]; dsimp only [Reg.x28]; simpa using hcs.2.1,
           by rw [hVrMr, hsCall]; simpa [calleeSavedVRegs] using hcs.2.2⟩
        have hProc0Call : MallocngProcPreserved s0 sCall :=
          ⟨by rw [hsCall]; simpa using hproc.1, by rw [hsCall]; simpa using hproc.2.1,
           by rw [hsCall]; simpa using hproc.2.2.1, by rw [hsCall]; simpa using hproc.2.2.2.1,
           by rw [hsCall]; simpa using hproc.2.2.2.2.1, by rw [hsCall]; simpa using hproc.2.2.2.2.2.1,
           by rw [hsCall]; simpa using hproc.2.2.2.2.2.2⟩
        have hbrkCall : sCall.brk = s0.brk := by rw [hsCall]; simpa using hbrk
        dsimp only [withCL]
        by_cases hFail : sMr.readReg64 .x0 = BitVec.allOnes 64
        ·
          simp only [hFail, ↓reduceIte]
          refine SepWP.weaken_pre (P' :=
              ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sMr.mem ∧
               MallocngProcPreserved sCall sMr ∧ sMr.brk = sCall.brk ∧
               sMr.mem.perm = sCall.mem.perm⌝ ∗
              (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
               ((tp - 0xa4#64) ↦₃₂ 12#32) ∗ (g.mem ↦ₛ oldMapBs) ∗ memMapped g.mem oldLen ∗
               (g.metaPtr ↦ₛ g.metaBytes) ∗ MallocngRoTablesAt maddrs ∗
               (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ ReallocMremapFrame maddrs tp st g ∗
               MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
               (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
               ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
               ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
               MallocngTightBlock γ p oldSz al ∗ Frame))
            (by
              refine Entails.trans (Q :=
                  ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sMr.mem⌝ ∗
                  ⌜MallocngProcPreserved sCall sMr ∧ sMr.brk = sCall.brk⌝ ∗
                  ⌜sMr.mem.perm = sCall.mem.perm ∧ MallocngMappedDelta 0 0 sCall.mem sMr.mem⌝ ∗
                  ((stackFrame sCall 144 ∗ stackFrameAt (sp1 - 144#64) 576) ∗
                   ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
                   ((tp - 0xa4#64) ↦₃₂ 12#32) ∗ (g.mem ↦ₛ oldMapBs) ∗ memMapped g.mem oldLen ∗
                   (g.metaPtr ↦ₛ g.metaBytes) ∗ MallocngRoTablesAt maddrs ∗
                   (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ ReallocMremapFrame maddrs tp st g ∗
                   MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                   (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
                   ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
                   ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                   MallocngTightBlock γ p oldSz al ∗ Frame))
                (Entails.of_eq (by
                  generalize (MallocngRoTablesAt maddrs) = PRo
                  generalize (ReallocMremapFrame maddrs tp st g) = PFr
                  generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
                  ac_rfl)) ?_
              rw [← hSf144]
              refine Entails.pure_left fun hclM => Entails.pure_left fun ⟨hpM, hbM⟩ =>
                Entails.pure_left fun ⟨hpmM, _⟩ => ?_
              exact Entails.pure_right ⟨hclM, hpM, hbM, hpmM⟩ (Entails.of_eq (by
                generalize (MallocngRoTablesAt maddrs) = PRo
                generalize (ReallocMremapFrame maddrs tp st g) = PFr
                generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
                ac_rfl))) ?_
          apply SepWP.pure_elim; rintro ⟨hclMr, hProcMr, hBrkMr, hPermMr⟩
          clear hsCall
          apply sepWP_abstract_all; intro PGoal4 postGoal4 oomGoal4 hPG4 hPostG4 hOomG4
          wp_step; wp_step; wp_step
          subst hPG4 hPostG4 hOomG4
          apply sepWP_bind_state; intro sF hsF
          have hProcMrF : MallocngProcPreserved sMr sF :=
            ⟨by rw [hsF]; simp, by rw [hsF]; simp, by rw [hsF]; simp, by rw [hsF]; simp,
             by rw [hsF]; simp, by rw [hsF]; simp, by rw [hsF]; simp⟩
          have hProc0F : MallocngProcPreserved s0 sF :=
            mallocngProcPreserved_trans (mallocngProcPreserved_trans hProc0Call hProcMr) hProcMrF
          have hBrkF : sF.brk = sMr.brk := by rw [hsF]; simp
          have hMemF : sF.mem = sMr.mem := by rw [hsF]; simp
          have hBrk0F : sF.brk = s0.brk := hBrkF.trans (hBrkMr.trans hbrkCall)
          have hPerm0F : sF.mem.perm = s0.mem.perm :=
            (congrArg Memory.perm hMemF).trans (hPermMr.trans (by rw [hmemCall]; exact hPerm))
          refine SepWP.weaken_pre
            (unextract_to_stage4 (al := al) γ tp brkStart bgt ivs0 s0 sF hCount hwf hg hIdx
              origBs tailBs hUserLen hTailLen hSlot hSc63
              hBrk0F (hProc0F.2.2.1.trans htp0) (hProc0F.2.2.2.1.trans hbrks0) sp1 Frame) ?_
          exact realloc_stage4_oop_ok (al := al) hImpl hFree hb γ tp brkStart bgt ivs0 s0 sF origBs
            hpNe hpOld48 hOrigLe hNewMax
            (by rw [hsF]; simp only [wp_norm, arm64_norm, hb])
            (by rw [hsF]; simp [hrunMr])
            hPerm0F hProc0F
            (by rw [hsF]; simpa [hspCall] using hspMr)
            (spAligned_of_sub80 (by rw [hsF]; simpa [hspCall] using hspMr) hsp0)
            hsp0
            (by rw [hsF]; simpa using hx19Mr)
            (by rw [hsF]; simpa using hx21Mr)
            (by rw [hsF]; simpa using hx23Mr)
            ⟨by rw [hsF]; simpa using hcs0Mr.1, by rw [hsF]; simpa using hcs0Mr.2.1,
             by rw [hsF]; simpa [calleeSavedVRegs] using hcs0Mr.2.2⟩
            (by rw [hMemF]; exact hclMr)
        ·
          have hPageIdem' : pageAlignUp needed = needed := hPageIdem
          simp only [hFail, ↓reduceIte, hPageIdem']
          refine SepWP.weaken_pre (P' :=
              ∃∗ newBase : BitVec 64,
                ⌜MallocngProcPreserved sCall sMr ∧ sMr.brk = sCall.brk ∧
                 sMr.readReg64 .x0 = newBase ∧ newBase ≠ 0#64 ∧ newBase ≠ BitVec.allOnes 64 ∧
                 4096 ∣ newBase.toNat ∧ newBase.toNat + needed ≤ 2 ^ 48 ∧
                 MallocngMappedDelta 1 needed sCall.mem sMr.mem ∧
                 (∃ m1 : Memory, m1.perm = sCall.mem.perm ∧
                   sMr.mem.perm = (m1.remapRw g.mem oldLen newBase needed).perm)⌝ ∗
                ((g.metaPtr ↦ₛ g.metaBytes) ∗
                 (newBase ↦ₛ (oldMapBs.take needed ++ List.replicate (needed - oldLen) 0#8)) ∗
                 (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
                  MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
                  memMapped newBase needed ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
                  ReallocMremapFrame maddrs tp st g ∗
                  MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                  (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
                  ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
                  ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                  MallocngTightBlock γ p oldSz al ∗ Frame)))
            (by
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              refine Entails.sepExists_mono fun newBase => ?_
              refine Entails.trans (Q :=
                  ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sMr.mem⌝ ∗
                  ⌜MallocngProcPreserved sCall sMr ∧ sMr.brk = sCall.brk⌝ ∗
                  ⌜sMr.readReg64 .x0 = newBase ∧ newBase ≠ 0#64 ∧ newBase ≠ BitVec.allOnes 64 ∧
                   4096 ∣ newBase.toNat ∧ newBase.toNat + needed ≤ 2 ^ 48 ∧
                   MallocngMappedDelta 1 needed sCall.mem sMr.mem ∧
                   (∃ m1 : Memory, m1.perm = sCall.mem.perm ∧
                     sMr.mem.perm = (m1.remapRw g.mem oldLen newBase needed).perm)⌝ ∗
                  ((stackFrame sCall 144 ∗ stackFrameAt (sp1 - 144#64) 576) ∗
                   (g.metaPtr ↦ₛ g.metaBytes) ∗
                   (newBase ↦ₛ (oldMapBs.take needed ++ List.replicate (needed - oldLen) 0#8)) ∗
                   (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
                    MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
                    memMapped newBase needed ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
                    ReallocMremapFrame maddrs tp st g ∗
                    MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                    (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
                    ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
                    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                    MallocngTightBlock γ p oldSz al ∗ Frame)))
                (Entails.of_eq (by
                  generalize (MallocngRoTablesAt maddrs) = PRo
                  generalize (ReallocMremapFrame maddrs tp st g) = PFr
                  generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
                  ac_rfl)) ?_
              rw [← hSf144]
              refine Entails.pure_left fun _ => Entails.pure_left fun ⟨hpM, hbM⟩ =>
                Entails.pure_left fun hRest => ?_
              exact Entails.pure_right ⟨hpM, hbM, hRest⟩ (Entails.of_eq (by
                generalize (MallocngRoTablesAt maddrs) = PRo
                generalize (ReallocMremapFrame maddrs tp st g) = PFr
                generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
                ac_rfl))) ?_
          apply SepWP.exists_left; intro newBase
          apply SepWP.pure_elim
          rintro ⟨hProcMr, hBrkMr, hx0Mr, hNbNe0, hNbNe1, hNbDvd, hNbFit, hDeltaMr, m1, hm1P, hMrP⟩
          clear hsCall
          have hNbGe : 4096 ≤ newBase.toNat := by
            obtain ⟨k, hk⟩ := hNbDvd
            have hk0 : k ≠ 0 := fun h0 => hNbNe0 (BitVec.eq_of_toNat_eq (by simp [hk, h0]))
            omega
          apply sepWP_abstract_all; intro PGoal5 postGoal5 oomGoal5 hPG5 hPostG5 hOomG5
          wp_step; wp_step; wp_step
          wp_if heqNeg1
          · exfalso
            try rw [show sMr.readReg64 (Reg.gpr 0#5) = newBase from hx0Mr] at heqNeg1
            try rw [hx0Mr] at heqNeg1
            exact not_add_one_eq_zero_of_le_48 (Nat.le_trans (Nat.le_add_right _ _) hNbFit) heqNeg1
          · subst hPG5 hPostG5 hOomG5
            apply sepWP_bind_state; intro sPost hsPost
            have hProcMrP : MallocngProcPreserved sMr sPost :=
              ⟨by rw [hsPost]; simp, by rw [hsPost]; simp, by rw [hsPost]; simp, by rw [hsPost]; simp,
               by rw [hsPost]; simp, by rw [hsPost]; simp, by rw [hsPost]; simp⟩
            have hProc0P : MallocngProcPreserved s0 sPost :=
              mallocngProcPreserved_trans (mallocngProcPreserved_trans hProc0Call hProcMr) hProcMrP
            have hMemPost : sPost.mem = sMr.mem := by rw [hsPost]; simp
            have hBrkPost : sPost.brk = sMr.brk := by rw [hsPost]; simp
            have hPermCall0 : sCall.mem.perm = s0.mem.perm := by rw [hmemCall]; exact hPerm
            have hPermRelP :
                (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ sPost.mem.perm = s0.mem.perm) ∨
                (∃ m1' : Memory, m1'.perm = s0.mem.perm ∧
                  sPost.mem.perm = (m1'.remapRw g.mem (g.maplen * 4096) newBase needed).perm) :=
              Or.inr ⟨m1, hm1P.trans hPermCall0, (congrArg Memory.perm hMemPost).trans hMrP⟩
            refine SepWP.mono
              (realloc_s3_post_mremap_ok (al := al) hb γ tp brkStart bgt ivs0 s0 sPost st
                hCount hwf hg hIdx origBs tailBs hOrigLe hTailLen hSlot hSc63
                (newBase := newBase) (needed := needed) (newSz := newSz) errnoVal
                hNewLo hNewMax rfl hNbGe (Nat.mod_eq_zero_of_dvd hNbDvd) hNbFit hOldRw hPermRelP
                (by rw [hsPost]; simp only [wp_norm, arm64_norm, hb])
                (by rw [hsPost]; simp [hrunMr])
                (hBrkPost.trans (hBrkMr.trans hbrkCall))
                hProc0P htp0 hbrks0
                (by rw [hsPost]; simpa [hspCall] using hspMr)
                (spAligned_of_sub80 (by rw [hsPost]; simpa [hspCall] using hspMr) hsp0)
                hsp0
                (by rw [hsPost]; simpa using hx0Mr)
                (by rw [hsPost]; simpa using hx20Mr)
                (by rw [hsPost]; simpa using hx21Mr)
                (by rw [hsPost]; simpa using hx22Mr)
                (by rw [hsPost]; simpa using hx24Mr)
                (by rw [hsPost]; simpa using hx25Mr)
                (by rw [hsPost]; simpa using hx26Mr)
                ⟨by rw [hsPost]; simpa using hcs0Mr.1, by rw [hsPost]; simpa using hcs0Mr.2.1,
                 by rw [hsPost]; simpa [calleeSavedVRegs] using hcs0Mr.2.2⟩) ?_
            intro sf Pf _ _ ⟨newQ, hsfPerm, _, hsfProc, hsfSp, hsfCS, hsfX0, hPf⟩
            have hsfPermMr : sf.mem.perm = sMr.mem.perm :=
              hsfPerm.trans (congrArg Memory.perm hMemPost)
            have hDelta0Sf : MallocngMappedDelta 16
                (MallocngTightStepBound (mallocngReallocRes al newSz) bgt.peakCount) s0.mem sf.mem :=
              mappedDelta_mono_bounds (by decide : 1 ≤ 16) hStepT
                (mappedDelta_trans_zero_right
                  (mappedDelta_zero_trans_left
                    (mallocngMappedDelta_of_perm_eq hPermCall0) hDeltaMr)
                  (mallocngMappedDelta_of_perm_eq hsfPermMr))
            exact ⟨newQ, ⟨hsfProc, hDelta0Sf⟩, hsfSp, hsfCS, hsfX0, hPf⟩
      ·
        have hNeedEqOld : needed = oldLen := by
          have h := congrArg BitVec.toNat hneLen
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
          exact h.symm
        wp_step; wp_step
        wp_if heqNeg1
        · exfalso
          try rw [show s.readReg64 (Reg.gpr 0#5) = g.mem from hx0] at heqNeg1
          try rw [hx0] at heqNeg1
          exact not_add_one_eq_zero_of_le_48 (Nat.le_trans (Nat.le_add_right _ _) hMemFit) heqNeg1
        · subst hPG2 hPostG2 hOomG2
          apply sepWP_bind_state; intro sPost hsPost
          have hProc0P : MallocngProcPreserved s0 sPost :=
            ⟨by rw [hsPost]; simpa using hproc.1, by rw [hsPost]; simpa using hproc.2.1,
             by rw [hsPost]; simpa using hproc.2.2.1, by rw [hsPost]; simpa using hproc.2.2.2.1,
             by rw [hsPost]; simpa using hproc.2.2.2.2.1, by rw [hsPost]; simpa using hproc.2.2.2.2.2.1,
             by rw [hsPost]; simpa using hproc.2.2.2.2.2.2⟩
          have hPerm0P : sPost.mem.perm = s0.mem.perm := by rw [hsPost]; simpa using hPerm
          have hBsEq : oldMapBs =
              oldMapBs.take needed ++ List.replicate (needed - g.maplen * 4096) 0#8 := by
            rw [hNeedEqOld]; dsimp only [oldLen]
            rw [List.take_of_length_le (Nat.le_of_eq hOldMapLen), Nat.sub_self,
                List.replicate_zero, List.append_nil]
          refine SepWP.weaken_pre (P' :=
              (g.metaPtr ↦ₛ g.metaBytes) ∗
              (g.mem ↦ₛ (oldMapBs.take needed ++ List.replicate (needed - g.maplen * 4096) 0#8)) ∗
              (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
               MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
               memMapped g.mem needed ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
               ReallocMremapFrame maddrs tp st g ∗
               MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
               (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
               ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
               ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
               MallocngTightBlock γ p oldSz al ∗ Frame))
            (Entails.of_eq (by
              rw [← hBsEq, hNeedEqOld]
              generalize (MallocngRoTablesAt maddrs) = PRo
              generalize (ReallocMremapFrame maddrs tp st g) = PFr
              generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
              ac_rfl)) ?_
          refine SepWP.mono
            (realloc_s3_post_mremap_ok (al := al) hb γ tp brkStart bgt ivs0 s0 sPost st
              hCount hwf hg hIdx origBs tailBs hOrigLe hTailLen hSlot hSc63
              (newBase := g.mem) (needed := needed) (newSz := newSz) errnoVal
              hNewLo hNewMax rfl hMemGe (Nat.mod_eq_zero_of_dvd hMemDvd)
              (by rw [hNeedEqOld]; exact hMemFit) hOldRw
              (Or.inl ⟨rfl, hNeedEqOld, hPerm0P⟩)
              (by rw [hsPost]; simp only [wp_norm, arm64_norm, hb])
              (by rw [hsPost]; simp [hrun])
              (by rw [hsPost]; simpa using hbrk)
              hProc0P htp0 hbrks0
              (by rw [hsPost]; simpa using hsp)
              (spAligned_of_sub80 (by rw [hsPost]; simp [hsp]) hsp0)
              hsp0
              (by rw [hsPost]; dsimp only [Reg.x0] at hx0 ⊢; simpa using hx0)
              (by rw [hsPost]; simp only [wp_norm, arm64_norm]; rfl)
              (by rw [hsPost]; dsimp only [Reg.x21] at hx21 ⊢; simpa using hx21)
              (by rw [hsPost]; dsimp only [Reg.x22] at hx22 ⊢; simpa using hx22)
              (by rw [hsPost]; dsimp only [Reg.x24] at hx24 ⊢; simpa using hx24)
              (by rw [hsPost]; simp only [wp_norm, arm64_norm]; rfl)
              (by rw [hsPost]; simp only [wp_norm, arm64_norm])
              ⟨by rw [hsPost]; simpa using hcs.1, by rw [hsPost]; simpa using hcs.2.1,
               by rw [hsPost]; simpa [calleeSavedVRegs] using hcs.2.2⟩) ?_
          intro sf Pf _ _ ⟨newQ, hsfPerm, _, hsfProc, hsfSp, hsfCS, hsfX0, hPf⟩
          exact ⟨newQ, ⟨hsfProc, mappedDelta_mono_bounds (Nat.zero_le _) (Nat.zero_le _)
            (mallocngMappedDelta_of_perm_eq (hsfPerm.trans hPerm0P))⟩,
            hsfSp, hsfCS, hsfX0, hPf⟩

end VerifiedLibraries.Mallocng.Proofs
