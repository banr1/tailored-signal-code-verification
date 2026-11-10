/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ReallocStagesFine
public import LibsignalBinary.Heap.Fine.ReallocStage3Raw
public import LibsignalBinary.Heap.Fine.MallocImplFine
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocStage3Entry
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocStage3

/-!
# Fine-Grained Placed `__libc_realloc` Stage 3 Entry

Verifies Stage 3 (`+0x324 → ret`) of placed `__libc_realloc` (`blk14`) over `FineBudget`: falls
back to Stage 4 when `g.sc < 48 ∨ newSz ≤ 131,051` or when `__mremap` returns `MAP_FAILED`, and
commits the resized `sc = 63` mapping via `realloc_s3_post_mremap_fine_of_raw` otherwise.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Bitvector and Spatial Extraction Helpers -/

private theorem sepWP_bind_state_s3 {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ sFin, sFin = s → SepWP prog ret sFin P post oom) : SepWP prog ret s P post oom :=
  h s rfl

private theorem packedWord_sc63_mask_trunc_fine (g : GroupDesc) (hLast : g.lastIdx ≤ 31)
    (hSc63 : g.sc = 63) (hMap : g.maplen < 2 ^ 52) :
    BitVec.truncate 32 ((g.packedWord.extractLsb' 0 16).zeroExtend 64 &&& 17317308141504#64) =
      0xfc0#32 := by
  have hTr : ∀ x : BitVec 16,
      BitVec.truncate 32 (x.zeroExtend 64 &&& 17317308141504#64) = x.zeroExtend 32 &&& 0xfc0#32 :=
    fun _ => by bv_robdd
  rw [hTr]; exact VerifiedLibraries.Mallocng.Proofs.packedWord_sc63_mask g hLast hSc63 hMap

private theorem not_add_one_eq_zero_of_le_48_fine {x : BitVec 64}
    (h : x.toNat ≤ 2 ^ 48) (heq : x + 1#64 = 0#64) : False := by
  have ht := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
  omega

private theorem extract_to_mremap_fine [MallocngMultiPlacement]
    (γb : GhostName) (tp brkStart : BitVec 64) (bCoarse : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (s0 : State) {st : MallocngSt}
    (hwf : MallocngWF maddrs.base brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff : Nat} (origBs tailBs : List (BitVec 8))
    (hUserLen : (origBs ++ tailBs).length = oldSz)
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    (sp1 : BitVec 64) (FrameAl : SepProp) :
    (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
     MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
     ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
     MallocngReadRest γb maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
     MallocngBlockToken γb p oldSz ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ FrameAl) ⊢
      ∃∗ errnoVal : BitVec 32,
        (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)) ∗
        ((g.metaPtr ↦ₛ g.metaBytes) ∗
         memMapped g.mem (g.maplen * 4096) ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
         ReallocMremapFrame maddrs tp st g ∗
         ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
         MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
         MallocngLiveAuth γb st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
         (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
         ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γb st.auxvPtr st.auxvSnap ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
         MallocngBlockToken γb p oldSz ∗ FrameAl) := by
  unfold MallocngReadRest
  have hExt := reallocMremap_extract maddrs tp hwf hg hIdx0 (origBs ++ tailBs)
    hUserLen hSlot0 hSc63
  refine Entails.trans (Q :=
      ⌜MallocngCountIvsWF bCoarse ivs0 st ∧
        MallocngWF maddrs.base brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st⌝ ∗
      ((ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st) ∗
        MallocngRuntime maddrs tp ∗ (p ↦ₛ (origBs ++ tailBs))) ∗
       (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        MallocngLiveAuth γb st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
        (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γb st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MallocngBlockToken γb p oldSz ∗ FrameAl)))
    (Entails.of_eq (by
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngRuntime maddrs tp) = PRt
      generalize (MallocngAuxvState γb st.auxvPtr st.auxvSnap) = PAu
      ac_rfl)) ?_
  refine Entails.pure_left fun _ => ?_
  refine Entails.trans (sepConj_mono_left hExt) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_mono fun errnoVal => Entails.of_eq ?_
  generalize (MallocngRoTablesAt maddrs) = PRo
  generalize (ReallocMremapFrame maddrs tp st g) = PFr
  generalize (MallocngAuxvState γb st.auxvPtr st.auxvSnap) = PAu
  ac_rfl

private theorem unextract_to_stage4_fine [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget) (live0 peak0 : Nat)
    (ivs0 : List (BitVec 64 × Nat)) (s0 s : State)
    {st : MallocngSt} (alignMap0 : BitVec 64 → Option Nat)
    (hInv0 : MallocngFineInv 0 bgt ivs0 alignMap0 st)
    (hCount : MallocngCountIvsWF (synthCoarseBudget live0 peak0 st) ivs0 st)
    (hwf : MallocngWF maddrs.base brkStart s0.brk
      (synthCoarseBudget live0 peak0 st).liveCost
      (synthCoarseBudget live0 peak0 st).peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz align oldEff : Nat} (origBs tailBs : List (BitVec 8))
    (hUserLen : (origBs ++ tailBs).length = oldSz)
    (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    (hbrk : s.brk = s0.brk) (htp : s.tpidrEl0 = tp) (hbrks : s.brkStart = brkStart)
    (sp1 : BitVec 64) (Frame : SepProp) :
    let γb := fineBaseGam γ
    (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
     ((tp - 0xa4#64) ↦₃₂ 12#32) ∗
     (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)) ∗
     memMapped g.mem (g.maplen * 4096) ∗
     (g.metaPtr ↦ₛ g.metaBytes) ∗
     MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
     ReallocMremapFrame maddrs tp st g ∗
     MallocngLiveAuth γb st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
     (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
     ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γb st.auxvPtr st.auxvSnap ∗
     ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
     MallocngBlockToken γb p oldSz ∗
     (ghostMapAuth (fineAlignGam γ) alignMap0 ∗
      ghostMapElem (fineAlignGam γ) p (max align 16) ∗ Frame)) ⊢
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       FineEnv γ maddrs tp brkStart bgt ivs0 s ∗
       FineBlock γ p oldSz (max align 16) ∗
       (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ∗
       Frame) := by
  intro γb
  let bCoarse := synthCoarseBudget live0 peak0 st
  have hgw := hwf.groups_wf g hg
  have hMpPos := (hgw.2.2.2.1 hSc63).2.1
  have hTotEq : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpPos]
  have hMemFit : g.mem.toNat + g.maplen * 4096 ≤ 2 ^ 48 := by
    have h := hgw.2.2.2.2.2.2.1; rwa [hTotEq] at h
  obtain ⟨_, _, hMemOwn⟩ := sc63_metaPtr_and_mem_owned hwf hg hIdx0 hSlot0 hSc63
  have hExtMp := MappedSet_extract_slice hwf.masterDom_wf.1 (keep := OwnedMappedByte st)
    g.mem (n := g.maplen * 4096) (by omega)
    (fun a ha => (hMemOwn a ha).1) (fun a ha => (hMemOwn a ha).2.1)
  have hSplitRw := sc63_rw_split_eq hwf hg hIdx0 (origBs ++ tailBs) hUserLen hSlot0 hSc63
  have hCoreUn :
      (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       (g.metaPtr ↦ₛ g.metaBytes) ∗
       (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)) ∗
       memMapped g.mem (g.maplen * 4096) ∗
       ((tp - 0xa4#64) ↦₃₂ 12#32) ∗
       ReallocMremapFrame maddrs tp st g ∗
       MallocngLiveAuth γb st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
       (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
       ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γb st.auxvPtr st.auxvSnap ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) ⊢
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngReadRest γb maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
        (p ↦ₛ (origBs ++ tailBs)) := by
    unfold ReallocMremapFrame MallocngReadRest
    have hErrno : ((tp - 0xa4#64) ↦₃₂ 12#32) ⊢
        ∃∗ ev : BitVec 32, (tp - 0xa4#64) ↦₃₂ ev := Entails.sepExists_intro 12#32
    refine Entails.trans (Entails.of_eq (by
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngAuxvState γb st.auxvPtr st.auxvSnap) = PAu
      ac_rfl : _ =
        (((tp - 0xa4#64) ↦₃₂ 12#32) ∗
         ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ∗
        (((g.metaPtr ↦ₛ g.metaBytes) ∗
          (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)) ∗
          ByteMap st.masterDom
            (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a ∧
              ¬ InRegion g.mem (g.maplen * 4096) a) st.byteVal) ∗
         (memMapped g.mem (g.maplen * 4096) ∗
          MappedSet st.masterDom
            (fun a => OwnedMappedByte st a ∧ ¬ InRegion g.mem (g.maplen * 4096) a)) ∗
         MallocngRoTablesAt maddrs ∗
         (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
         MallocngLiveAuth γb st.liveMap ∗
         (maddrs.lock ↦₃₂ 0#32) ∗
         (maddrs.replaced ↦₃₂ 0#32) ∗
         (maddrs.aaReplaced ↦₃₂ 0#32) ∗
         ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
         MallocngAuxvState γb st.auxvPtr st.auxvSnap ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal))) ?_
    refine Entails.trans (sepConj_mono_left (sepConj_mono_left hErrno)) ?_
    change (MallocngRuntime maddrs tp ∗ _) ⊢ _
    rw [← hSplitRw, ← hExtMp]
    refine Entails.trans (Entails.of_eq (by
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngRuntime maddrs tp) = PRt
      generalize (MallocngAuxvState γb st.auxvPtr st.auxvSnap) = PAu
      ac_rfl : _ =
        MallocngRoTablesAt maddrs ∗
        (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        (MallocngLiveAuth γb st.liveMap ∗
         (maddrs.lock ↦₃₂ 0#32) ∗
         (maddrs.replaced ↦₃₂ 0#32) ∗
         (maddrs.aaReplaced ↦₃₂ 0#32) ∗
         ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
         MallocngAuxvState γb st.auxvPtr st.auxvSnap ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
         MappedSet st.masterDom (OwnedMappedByte st) ∗
         MallocngRuntime maddrs tp) ∗
        (p ↦ₛ (origBs ++ tailBs)))) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (Entails.pure_right ⟨hCount, hwf⟩ (Entails.refl _)))))
  refine Entails.trans ?_
    (repack_fine_read_to_stage4 (align := align) γ tp brkStart bgt ivs0 s0 s st alignMap0
      live0 peak0 hInv0 origBs tailBs hTailLen hbrk htp hbrks sp1 Frame)
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.trans (Q :=
      (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       (g.metaPtr ↦ₛ g.metaBytes) ∗
       (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)) ∗
       memMapped g.mem (g.maplen * 4096) ∗
       ((tp - 0xa4#64) ↦₃₂ 12#32) ∗
       ReallocMremapFrame maddrs tp st g ∗
       MallocngLiveAuth γb st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
       (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
       ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γb st.auxvPtr st.auxvSnap ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) ∗
      (MallocngBlockToken γb p oldSz ∗
       ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       ghostMapElem (fineAlignGam γ) p (max align 16) ∗ Frame))
    (Entails.of_eq (by
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (ReallocMremapFrame maddrs tp st g) = PFr
      generalize (MallocngAuxvState γb st.auxvPtr st.auxvSnap) = PAu
      ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hCoreUn) ?_
  exact Entails.of_eq (by
    dsimp only [γb, bCoarse]
    generalize (MallocngRoTablesAt maddrs) = PRo
    generalize (MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk
      (synthCoarseBudget live0 peak0 st) ivs0 st) = PRest
    ac_rfl)

/-! ## Stage 3 Entry (`+0x324 → ret`) -/

set_option maxHeartbeats 400000 in
/-- Full Fine Stage 3 (`+0x324` → `ret`), parameterized only by `ReallocS3PostMremapRawStmt`. -/
theorem realloc_stage3_fine_of_raw
    (hPostRaw : ReallocS3PostMremapRawStmt) :
    ReallocStage3FineStmt := by
  intro _ b hb γ tp brkStart bgt ivs0 s0 s st alignMap0 live0 peak0
    p oldSz align oldEff newSz g hg idx hIdx origBs tailBs
    hInv0 hwf0 hAlign0 hpNe hOrigLe hTailLen hSlot hF hNewMax Frame
    hpc hrun hPerm hbrk hproc htp0 hbrks0 hsp hal hsp0
    hx0 hx1 hx2 hx6 hx7 hx19 hx20 hx21 hx22 hx23 hx24 hcs hcl
    sp1 bCoarse bf stepB keptBs
  have _ := hb
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
    apply sepWP_bind_state_s3; intro sA hsA
    have hbrkA : sA.brk = s0.brk := by rw [hsA]; simpa using hbrk
    have htpA : sA.tpidrEl0 = tp := by rw [hsA]; simpa [htp0] using hproc.2.2.1
    have hbrksA : sA.brkStart = brkStart := by rw [hsA]; simpa [hbrks0] using hproc.2.2.2.1
    refine SepWP.weaken_pre
      (repack_fine_read_to_stage4 (align := align) γ tp brkStart bgt ivs0 s0 sA st alignMap0
        live0 peak0 hInv0 origBs tailBs hTailLen hbrkA htpA hbrksA sp1 Frame) ?_
    exact realloc_stage4_oop_fine_ok placed_libcMallocImpl_raw_fine_ok (align := align)
      hb γ tp brkStart bgt ivs0 s0 sA origBs hpNe hpOld48 hOrigLe hNewMax
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
    have hNeedLeStep :
        ((newSz + (p.toNat - (g.slotStart 0).toNat) + 4115) / 4096) * 4096 ≤ stepB :=
      mremap_needed_le_fineStepReserve hInv0 hwf0 hg hSc63 hIdx hSlot hAlign0
    let FrameAl := ghostMapAuth (fineAlignGam γ) alignMap0 ∗
      ghostMapElem (fineAlignGam γ) p (max align 16) ∗ Frame
    refine SepWP.weaken_pre (P' :=
        ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
        MallocngBlockToken (fineBaseGam γ) p oldSz ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ FrameAl)
      (Entails.of_eq (by
        dsimp only [FrameAl]
        generalize (MallocngRoTablesAt maddrs) = PRo
        generalize (MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
        ac_rfl)) ?_
    apply sepWP_pure_of_sat (fun R hm =>
      satisfies_readRest_wf (Rest := ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
        stackFrameAt sp1 720 ∗ MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngBlockToken (fineBaseGam γ) p oldSz ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ FrameAl ∗ R)
        (Satisfies.mono (Entails.of_eq (by
          generalize (MallocngRoTablesAt maddrs) = PRo
          generalize (MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
          ac_rfl)) hm))
    rintro ⟨hCount, hwf⟩
    obtain ⟨hIdxEq0, _hLast0, _, hMpPos, _, _, _, _,
            hMemGe, hMemDvd, hMemFit, _, _, _, hLoP, _, hExtraBound,
            hOldSlotFit, _hNewSlotFit, _, hPageIdem, hNeedLo, hNeedDvd,
            _hNeedMax, _hStepCoarse, _⟩ :=
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
      (extract_to_mremap_fine (fineBaseGam γ) tp brkStart bCoarse ivs0 s0 hwf hg hIdx
        origBs tailBs hUserLen hSlot hSc63 sp1 FrameAl) ?_
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
      VerifiedLibraries.Mallocng.Proofs.packedWord_maplen_mask g hF.last_le_31 (hSc63 ▸ by decide)
        (Nat.le_trans (Nat.le_add_left _ _) hMemFit)
    have hNeedMask : BitVec.ofNat 64 (newSz + extra + 4115) &&& -4096#64 = BitVec.ofNat 64 needed :=
      and_neg4096_eq_pageMul (by dsimp only [extra] at hExtraBound ⊢; omega)
    apply sepWP_abstract_all; intro PGoal2 postGoal2 oomGoal2 hPG2 hPostG2 hOomG2
    wp_step; wp_step; wp_step
    wp_if hne7
    · exfalso
      exact hne7 (packedWord_sc63_mask_trunc_fine g hF.last_le_31 hSc63 hMapLt52)
    ·
      wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
      wp_if hneLen
      ·
        wp_step; wp_step; wp_step
        subst hPG2 hPostG2 hOomG2
        apply sepWP_bind_state_s3; intro sCall hsCall
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
            MallocngLiveAuth (fineBaseGam γ) st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
            (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
            ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
            MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap ∗
            ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
            MallocngBlockToken (fineBaseGam γ) p oldSz ∗ FrameAl)
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
                 MallocngLiveAuth (fineBaseGam γ) st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                 (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
                 ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
                 MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap ∗
                 ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                 MallocngBlockToken (fineBaseGam γ) p oldSz ∗ FrameAl) ∗ R')
              (Entails.of_eq (by
                generalize (MallocngRoTablesAt maddrs) = PRo
                generalize (ReallocMremapFrame maddrs tp st g) = PFr
                generalize (MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap) = PAu
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
            have hpermSf : sf.mem.perm = s0.mem.perm := hpermO.trans hpermCall
            exact Satisfies.pure_intro
              ⟨hfsO.trans hfsCall, htrO.trans htrCall, hsigO.trans hsigCall,
               ⟨[], Nat.zero_le _, Nat.zero_le _, fun a ha => Or.inl (hpermSf ▸ ha)⟩,
               fun _ => ⟨needed, hNeedLo, Nat.mod_eq_zero_of_dvd hNeedDvd, hNeedLeStep,
                 Or.inr (Nat.lt_of_add_right_lt hphysO)⟩⟩
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
               MallocngLiveAuth (fineBaseGam γ) st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
               (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
               ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
               MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap ∗
               ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
               MallocngBlockToken (fineBaseGam γ) p oldSz ∗ FrameAl))
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
                   MallocngLiveAuth (fineBaseGam γ) st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                   (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
                   ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
                   MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap ∗
                   ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                   MallocngBlockToken (fineBaseGam γ) p oldSz ∗ FrameAl))
                (Entails.of_eq (by
                  generalize (MallocngRoTablesAt maddrs) = PRo
                  generalize (ReallocMremapFrame maddrs tp st g) = PFr
                  generalize (MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap) = PAu
                  ac_rfl)) ?_
              rw [← hSf144]
              refine Entails.pure_left fun hclM => Entails.pure_left fun ⟨hpM, hbM⟩ =>
                Entails.pure_left fun ⟨hpmM, _⟩ => ?_
              exact Entails.pure_right ⟨hclM, hpM, hbM, hpmM⟩ (Entails.of_eq (by
                generalize (MallocngRoTablesAt maddrs) = PRo
                generalize (ReallocMremapFrame maddrs tp st g) = PFr
                generalize (MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap) = PAu
                ac_rfl))) ?_
          apply SepWP.pure_elim; rintro ⟨hclMr, hProcMr, hBrkMr, hPermMr⟩
          clear hsCall
          apply sepWP_abstract_all; intro PGoal4 postGoal4 oomGoal4 hPG4 hPostG4 hOomG4
          wp_step; wp_step; wp_step
          subst hPG4 hPostG4 hOomG4
          apply sepWP_bind_state_s3; intro sF hsF
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
            (unextract_to_stage4_fine (align := align) γ tp brkStart bgt live0 peak0 ivs0 s0 sF
              alignMap0 hInv0 hCount hwf hg hIdx origBs tailBs hUserLen hTailLen hSlot hSc63
              hBrk0F (hProc0F.2.2.1.trans htp0) (hProc0F.2.2.2.1.trans hbrks0) sp1 Frame) ?_
          exact realloc_stage4_oop_fine_ok placed_libcMallocImpl_raw_fine_ok (align := align)
            hb γ tp brkStart bgt ivs0 s0 sF origBs hpNe hpOld48 hOrigLe hNewMax
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
                  MallocngLiveAuth (fineBaseGam γ) st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                  (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
                  ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
                  MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap ∗
                  ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                  MallocngBlockToken (fineBaseGam γ) p oldSz ∗ FrameAl)))
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
                    MallocngLiveAuth (fineBaseGam γ) st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                    (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
                    ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
                    MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap ∗
                    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                    MallocngBlockToken (fineBaseGam γ) p oldSz ∗ FrameAl)))
                (Entails.of_eq (by
                  generalize (MallocngRoTablesAt maddrs) = PRo
                  generalize (ReallocMremapFrame maddrs tp st g) = PFr
                  generalize (MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap) = PAu
                  ac_rfl)) ?_
              rw [← hSf144]
              refine Entails.pure_left fun _ => Entails.pure_left fun ⟨hpM, hbM⟩ =>
                Entails.pure_left fun hRest => ?_
              exact Entails.pure_right ⟨hpM, hbM, hRest⟩ (Entails.of_eq (by
                generalize (MallocngRoTablesAt maddrs) = PRo
                generalize (ReallocMremapFrame maddrs tp st g) = PFr
                generalize (MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap) = PAu
                ac_rfl))) ?_
          apply SepWP.exists_left; intro newBase
          apply SepWP.pure_elim
          rintro ⟨hProcMr, hBrkMr, hx0Mr, hNbNe0, _hNbNe1, hNbDvd, hNbFit, hDeltaMr, m1, hm1P, hMrP⟩
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
            exact not_add_one_eq_zero_of_le_48_fine (Nat.le_trans (Nat.le_add_right _ _) hNbFit) heqNeg1
          · subst hPG5 hPostG5 hOomG5
            apply sepWP_bind_state_s3; intro sPost hsPost
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
              (realloc_s3_post_mremap_fine_of_raw hPostRaw hb γ tp brkStart bgt bCoarse ivs0
                s0 sPost st alignMap0 hInv0 hCount hwf hg hIdx origBs tailBs hAlign0
                hOrigLe hTailLen hSlot hSc63
                (newBase := newBase) (needed := needed) (newSz := newSz) errnoVal
                (Frame := Frame)
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
            have hDelta0Sf : MallocngMappedDelta 16 stepB s0.mem sf.mem :=
              mappedDelta_mono_bounds (by decide : 1 ≤ 16) hNeedLeStep
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
          exact not_add_one_eq_zero_of_le_48_fine (Nat.le_trans (Nat.le_add_right _ _) hMemFit) heqNeg1
        · subst hPG2 hPostG2 hOomG2
          apply sepWP_bind_state_s3; intro sPost hsPost
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
               MallocngLiveAuth (fineBaseGam γ) st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
               (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
               ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
               MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap ∗
               ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
               MallocngBlockToken (fineBaseGam γ) p oldSz ∗ FrameAl))
            (Entails.of_eq (by
              rw [← hBsEq, hNeedEqOld]
              generalize (MallocngRoTablesAt maddrs) = PRo
              generalize (ReallocMremapFrame maddrs tp st g) = PFr
              generalize (MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap) = PAu
              ac_rfl)) ?_
          refine SepWP.mono
            (realloc_s3_post_mremap_fine_of_raw hPostRaw hb γ tp brkStart bgt bCoarse ivs0
              s0 sPost st alignMap0 hInv0 hCount hwf hg hIdx origBs tailBs hAlign0
              hOrigLe hTailLen hSlot hSc63
              (newBase := g.mem) (needed := needed) (newSz := newSz) errnoVal
              (Frame := Frame)
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

theorem realloc_s3_post_mremap_raw_stmt_ok : ReallocS3PostMremapRawStmt := by
  intro _ b hb γ tp brkStart bgt ivs0 s0 s st hCount hwf
    g hg hIdx0 p oldSz oldEff origBs tailBs hOrigLe hTailLen hSlot0 hSc63
    newBase needed newSz errnoVal Frame oom
    hNewLo hNewHi hNeedEq hNewBaseGe hNewBaseAl hNewBaseFit hOldRw hPermRel
    hpc hrun hbrk hproc _htp0 _hbrks0 hsp hal hsp0 hx0 hx20 hx21 hx22 hx24 hx25 hx26 hcs
    sp1 keptBs bsRemap0
  refine SepWP.mono
    (realloc_s3_post_mremap_raw_ok hb γ tp brkStart bgt ivs0 s0 s st hCount hwf
      hg hIdx0 origBs tailBs hOrigLe hTailLen hSlot0 hSc63 errnoVal
      (Frame := Frame) (oom := oom)
      hNewLo hNewHi hNeedEq hNewBaseGe hNewBaseAl hNewBaseFit hOldRw hPermRel
      hpc hrun hbrk hproc hsp hal hsp0 hx0 hx20 hx21 hx22 hx24 hx25 hx26 hcs) ?_
  intro sf Pf _ _ ⟨st', g', newQ, newEff, live', peak',
    hPermSf, hBrkSf, hProcSf, hSpSf, hCsSf, hX0Sf, hPf,
    hgMeta, hgSc, _, _, _, _, hgMap, hgSlots, _, hEffDiff, _, hFreshQ,
    hGroups', hMeta', hLiveMap', hNoOrph⟩
  exact ⟨st', g', newQ, newEff, live', peak',
    hPermSf, hBrkSf, hProcSf, hSpSf, hCsSf, hX0Sf,
    hgMeta, hgSc, hgMap, hgSlots, hEffDiff, hFreshQ,
    hGroups', hMeta', hLiveMap', hNoOrph, hPf⟩

theorem realloc_stage3_fine_ok : ReallocStage3FineStmt :=
  realloc_stage3_fine_of_raw realloc_s3_post_mremap_raw_stmt_ok

end LibsignalBinary.Heap.Fine
