/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ReallocStage2Raw
public import LibsignalBinary.Heap.Fine.FreeReallocInvFine
public import LibsignalBinary.Heap.Fine.MallocEntryFine
public import LibsignalBinary.Heap.Fine.ReallocNullStage4Fine
public import LibsignalBinary.Heap.Fine.ReallocNonNullFine

/-!
# Fine-Grained Placed `__libc_realloc` Stages 2 and 3 Bridges

Connects the raw-state Stage 2 (`ReallocStage2Raw`) and Stage 3 (`ReallocStage3Raw`) `__libc_realloc`
proofs with `realloc_inplace_preserves_fineInv`, `realloc_mremap_preserves_fineInv`, and
`fineAlignGam` ghost-map updates.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## `FineInitBlockSem` and Ghost-Move Helpers -/

theorem rawInitBlock_to_fineInitBlock (γ : GhostName) (q : BitVec 64)
    (sz align : Nat) (bs : List (BitVec 8)) :
    (MallocngInitBlock mallocngIface (fineBaseGam γ)).interp q (sz, bs) ∗
      ghostMapElem (fineAlignGam γ) q (max align 16) ⊢
      (FineInitBlockSem γ).interp q (sz, max align 16, bs) := by
  have hal16 : 16 ≤ max align 16 := Nat.le_max_right align 16
  have hMaxIdem : max (max align 16) 16 = max align 16 := Nat.max_eq_left hal16
  dsimp only [MallocngInitBlock, FineInitBlockSem, mallocngIface]
  rw [hMaxIdem]
  unfold FineBlock
  rw [pure_sepConj_of_true hal16]
  exact Entails.of_eq (by ac_rfl)

theorem ghostMap_move_bupd (γ : GhostName)
    (alignMap0 : BitVec 64 → Option Nat) (p newQ : BitVec 64) (al : Nat)
    (hFresh : newQ ≠ p → alignMap0 newQ = none) :
    ghostMapAuth γ alignMap0 ∗ ghostMapElem γ p al ⊢
      |==> (ghostMapAuth γ (fun k =>
        if k = newQ then some al else if k = p then none else alignMap0 k) ∗
        ghostMapElem γ newQ al) := by
  let alignDel : BitVec 64 → Option Nat := fun k => if k = p then none else alignMap0 k
  have hDel := ghostMap_delete γ alignMap0 p al
  have hNone : alignDel newQ = none := by
    by_cases hEq : newQ = p
    · simp [alignDel, hEq]
    · simp [alignDel, hEq, hFresh hEq]
  have hIns := ghostMap_alloc γ alignDel newQ al hNone
  exact Entails.trans (Entails.trans hDel (bupd_mono hIns)) (bupd_trans _)

/-! ## Stage 2 In-Place `set_size` Commit -/

theorem realloc_stage2_fine_core_ok [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt) (alignMap0 : BitVec 64 → Option Nat) (live0 peak0 : Nat)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz align oldEff newSz : Nat} (origBs tailBs : List (BitVec 8))
    (hInv0 : MallocngFineInv 0 bgt ivs0 alignMap0 st)
    (hwf0 : MallocngWF maddrs.base brkStart s0.brk live0 peak0 st)
    (hAlign0 : alignMap0 p = some (max align 16))
    (_hpNe : p ≠ 0#64)
    (hOrigLen : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (_hF : LiveUserBlockFacts st g idx p oldSz oldEff)
    (hNewMax : newSz ≤ 131051) (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    {Frame : SepProp}
    (hpc : s.pc = b + 0x2cc#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hbrk : s.brk = s0.brk)
    (hproc : MallocngProcPreserved s0 s)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat))
    (hx4 : s.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx5 : s.readReg64 .x5 = g.slotEnd idx)
    (hx19 : s.readReg64 .x19 = p)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hcs : ReallocUntouchedCS s0 s)
    (_hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem) :
    let sp1 := s0.sp - 80#64
    let bCoarse := synthCoarseBudget live0 peak0 st
    let bf := FineBudget.stepRealloc align oldSz newSz bgt
    let stepB := fineStepReserve (.realloc align oldSz newSz) bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
       MallocngBlockToken (fineBaseGam γ) p oldSz ∗
       ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       ghostMapElem (fineAlignGam γ) p (max align 16) ∗
       (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)
      (fun sf Pf =>
        ∃ q : BitVec 64,
          MallocngCallAccounting 16 stepB s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
          (Pf ⊢ stackFrame s0 800 ∗
            FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(FineInitBlockSem γ).pureWf q (newSz, max align 16, keptBs)⌝ ∗
            (FineInitBlockSem γ).interp q (newSz, max align 16, keptBs) ∗
            Frame))
      (fun sf => ⌜FineStepOomCond msvc stepB s0 sf⌝) := by
  intro sp1 bCoarse bf stepB keptBs
  let alignFrame := ghostMapAuth (fineAlignGam γ) alignMap0 ∗
    ghostMapElem (fineAlignGam γ) p (max align 16) ∗ Frame
  have hPreEq :
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
       MallocngBlockToken (fineBaseGam γ) p oldSz ∗
       ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       ghostMapElem (fineAlignGam γ) p (max align 16) ∗
       (p ↦ₛ (origBs ++ tailBs)) ∗ Frame) =
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
       MallocngBlockToken (fineBaseGam γ) p oldSz ∗
       (p ↦ₛ (origBs ++ tailBs)) ∗ alignFrame) := by
    dsimp only [alignFrame]
    generalize (MallocngRoTablesAt maddrs) = PRo
    generalize (MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
    ac_rfl
  rw [hPreEq]
  refine SepWP.mono
    (realloc_stage2_inplace_readRest_raw_ok hb (fineBaseGam γ) tp brkStart bCoarse ivs0 s0 s st
      hg hIdx origBs tailBs hOrigLen hTailLen hSlot hNewMax hFit hScLe
      (Frame := alignFrame)
      (oom := fun sf => ⌜FineStepOomCond msvc stepB s0 sf⌝)
      hpc hrun hPerm hbrk hproc hsp hal hsp0 hx3 hx4 hx5 hx19 hx21 hcs) ?_
  intro sf Pf _ _ ⟨hPermSf, _, hProcSf, hspSf, hcsSf, hx0Sf,
    st', g', newEff, live', peak', hPf, hgSc, hgSame, hgSlots, _, hGroups', hMeta', hLiveMap', hNoOrph⟩
  refine ⟨p, ⟨hProcSf, mallocngMappedDelta_of_perm_eq hPermSf⟩, hspSf, hcsSf, hx0Sf, ?_⟩
  have hIvs0 : ivs0 = dynamicRootRegions st := hInv0.ivs_eq rfl
  have hNoOrph0 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem := by
    rwa [hIvs0]
  have hInv' : MallocngFineInv 0 bf (dynamicRootRegions st') alignMap0 st' :=
    realloc_inplace_preserves_fineInv hInv0 hwf0 hg hgSc hIdx hSlot hAlign0
      hNewMax hgSame hgSlots hGroups' hMeta' hLiveMap'
  have htpSf : sf.tpidrEl0 = tp := hProcSf.2.2.1.trans htp0
  have hbrksSf : sf.brkStart = brkStart := hProcSf.2.2.2.1.trans hbrks0
  have hCoreEnt :
      ghostMapAuth (fineAlignGam γ) alignMap0 ∗
      MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st' ⊢
        FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
          (dynamicRootRegions st') alignMap0 live' peak' st' := by
    unfold FineCoreStInflightA MallocngCoreStA
    exact Entails.pure_right hInv' (Entails.refl _)
  have hPostEnv :
      MallocngRoTablesA maddrs ∗
      (ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st') ∗
      MallocngRuntime maddrs tp ⊢
        FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left hCoreEnt))
      (pack_finePostEnv γ tp brkStart bf ivs0 st' alignMap0 live' peak' s0 sf
        hNoOrph0 htpSf hbrksSf)
  have hBlkEnt := rawInitBlock_to_fineInitBlock γ p newSz align keptBs
  refine Entails.trans hPf ?_
  dsimp only [alignFrame]
  refine Entails.trans (Q :=
      stackFrame s0 800 ∗
      (MallocngRoTablesA maddrs ∗
       (ghostMapAuth (fineAlignGam γ) alignMap0 ∗
        MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st') ∗
       MallocngRuntime maddrs tp) ∗
      ⌜(FineInitBlockSem γ).pureWf p (newSz, max align 16, keptBs)⌝ ∗
      ((MallocngInitBlock mallocngIface (fineBaseGam γ)).interp p (newSz, keptBs) ∗
       ghostMapElem (fineAlignGam γ) p (max align 16)) ∗
      Frame)
    (Entails.of_eq (by
      dsimp only [MallocngInitBlock, FineInitBlockSem, mallocngIface]
      generalize (MallocngRoTablesA maddrs) = PRo
      generalize (MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st') = PCore
      generalize (MallocngRuntime maddrs tp) = PRt
      ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono hPostEnv
    (sepConj_mono_right (sepConj_mono_left hBlkEnt)))

theorem realloc_stage2_fine_ok : ReallocStage2FineStmt :=
  fun hb => realloc_stage2_fine_core_ok hb

/-! ## Stage 3 `mremap` Reserve Bound and Fine Commit -/

theorem sepWP_bupd_post {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hwp : SepWP prog target_pc s P
      (fun sf Pf => ∃ Q : SepProp, (Pf ⊢ |==> Q) ∧ post sf Q) oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.of_reaches_pc fun R hm hL => by
    rcases SepWP.to_reaches_pc hwp hm hL with
      ⟨sf, hsteps, ⟨hpc, hrun, Pf, hSat, Q, hb, hPost⟩ | hoom⟩
    · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Q,
        (satisfies_bupd (Q ∗ R) sf.mem).mp
          (Satisfies.mono (Entails.trans (sepConj_mono_left hb) (bupd_frame_r Q R)) hSat),
        hPost⟩⟩
    · exact ⟨sf, hsteps, Or.inr hoom⟩

theorem mremap_needed_le_fineStepReserve
    {base brkStart brk0 : BitVec 64} {live0 peak0 : Nat}
    {bgt : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap0 : BitVec 64 → Option Nat} {st0 : MallocngSt}
    {g0 : GroupDesc} {idx0 align oldSz oldEff newSz : Nat} {p : BitVec 64}
    (hInv0 : MallocngFineInv 0 bgt ivs0 alignMap0 st0)
    (hwf0 : MallocngWF base brkStart brk0 live0 peak0 st0)
    (hg0 : g0 ∈ st0.groups) (hg0Sc : g0.sc = 63)
    (hIdx0 : idx0 < g0.slots.length)
    (hSlot0 : g0.slots[idx0]'hIdx0 = .liveUser p oldSz oldEff)
    (hAlign0 : alignMap0 p = some (max align 16)) :
    ((newSz + (p.toNat - (g0.slotStart 0).toNat) + 4115) / 4096) * 4096 ≤
      fineStepReserve (.realloc align oldSz newSz) bgt := by
  have hg0Last0 : g0.lastIdx = 0 := ((hwf0.groups_wf g0 hg0).2.2.2.1 hg0Sc).1
  have hLen1 : g0.slots.length = 1 := by
    rw [(hwf0.groups_wf g0 hg0).2.2.1]; unfold GroupDesc.cnt; omega
  have hIdxEq0 : idx0 = 0 := by omega
  obtain ⟨al0, hAl0, hBnd0⟩ := hInv0.alignMap_wf.2 g0 hg0 idx0 hIdx0 p oldSz oldEff hSlot0
  have hAlEq : al0 = max align 16 := Option.some.inj (hAl0.symm.trans hAlign0)
  subst hAlEq
  have hOldSlack : oldEff - max oldSz MallocngMinBlockCost ≤ max align 16 - 16 := (hBnd0 hg0Sc).1
  have hSWf0 := (hwf0.groups_wf g0 hg0).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx0 hIdx0
  have hOffLe : p.toNat - (g0.slotStart 0).toNat ≤
      (oldEff - max oldSz MallocngMinBlockCost) + 255 * 16 := by
    subst hIdxEq0
    dsimp only [SlotWf] at hSWf0
    rw [hSlot0] at hSWf0
    exact hSWf0.2.2.2.2.2.2.2.2.1.1
  unfold fineStepReserve FineStepBound pageAlignUp PAGE_SIZE
  dsimp only
  omega

theorem commit_stage3_mremap_fine_bupd [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 sf : State) (st0 st' : MallocngSt)
    (alignMap0 : BitVec 64 → Option Nat) (live0 peak0 live' peak' : Nat)
    {g0 g0' : GroupDesc} {idx0 align oldSz oldEff newSz newEff : Nat}
    {p newQ : BitVec 64} (keptBs : List (BitVec 8)) (Frame Pf : SepProp)
    (hInv0 : MallocngFineInv 0 bgt ivs0 alignMap0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s0.brk live0 peak0 st0)
    (hg0 : g0 ∈ st0.groups) (hg0Sc : g0.sc = 63)
    (hIdx0 : idx0 < g0.slots.length)
    (hSlot0 : g0.slots[idx0]'hIdx0 = .liveUser p oldSz oldEff)
    (hAlign0 : alignMap0 p = some (max align 16))
    (hg0'Meta : g0'.metaPtr = g0.metaPtr)
    (hg0'Sc : g0'.sc = 63)
    (hg0'Map : g0'.maplen * 4096 =
      ((newSz + (p.toNat - (g0.slotStart 0).toNat) + 4115) / 4096) * 4096)
    (hg0'Slots : g0'.slots = [.liveUser newQ newSz newEff])
    (hEffDiff : newEff - max newSz MallocngMinBlockCost =
      oldEff - max oldSz MallocngMinBlockCost)
    (hFreshNewQ : newQ ≠ p → st0.liveMap newQ = none)
    (hGroups' : st'.groups = st0.groups.map fun x =>
      if x.metaPtr == g0.metaPtr then g0' else x)
    (hMetaEq : st'.metaAreas = st0.metaAreas)
    (hLiveMap' : ∀ k, st'.liveMap k =
      if k = newQ then some newSz else if k = p then none else st0.liveMap k)
    (hNoOrph : MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st')
      s0.mem sf.mem)
    (htpSf : sf.tpidrEl0 = tp) (hbrksSf : sf.brkStart = brkStart)
    (hPf : Pf ⊢ stackFrame s0 800 ∗ MallocngRoTablesA maddrs ∗
      MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st' ∗
      MallocngRuntime maddrs tp ∗
      ⌜(MallocngInitBlock mallocngIface (fineBaseGam γ)).pureWf newQ (newSz, keptBs)⌝ ∗
      (MallocngInitBlock mallocngIface (fineBaseGam γ)).interp newQ (newSz, keptBs) ∗
      (ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       ghostMapElem (fineAlignGam γ) p (max align 16) ∗ Frame)) :
    let bf := FineBudget.stepRealloc align oldSz newSz bgt
    Pf ⊢ |==> (stackFrame s0 800 ∗
      FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
      ⌜(FineInitBlockSem γ).pureWf newQ (newSz, max align 16, keptBs)⌝ ∗
      (FineInitBlockSem γ).interp newQ (newSz, max align 16, keptBs) ∗
      Frame) := by
  intro bf
  have hIvs0 : ivs0 = dynamicRootRegions st0 := hInv0.ivs_eq rfl
  have hNoOrph0 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem := by
    rwa [hIvs0]
  have hAlignFresh : newQ ≠ p → alignMap0 newQ = none := by
    intro hNe
    cases hAq : alignMap0 newQ with
    | none => rfl
    | some al =>
      obtain ⟨req0, hLq⟩ := (hInv0.alignMap_wf.1 newQ al hAq).2
      rw [hFreshNewQ hNe] at hLq
      cases hLq
  let alignMap' : BitVec 64 → Option Nat := fun k =>
    if k = newQ then some (max align 16) else if k = p then none else alignMap0 k
  have hMove := ghostMap_move_bupd (fineAlignGam γ) alignMap0 p newQ (max align 16) hAlignFresh
  let CoreBody :=
    MallocngLiveAuth (fineBaseGam γ) st'.liveMap ∗
    (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗
    (maddrs.lock ↦₃₂ 0#32) ∗
    (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗
    ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗
    MallocngAuxvState (fineBaseGam γ) st'.auxvPtr st'.auxvSnap ∗
    ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
    ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
    MappedSet st'.masterDom (OwnedMappedByte st')
  have hExtractWf :
      MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk live' peak' st' ⊢
        ⌜MallocngWF maddrs.base brkStart sf.brk live' peak' st'⌝ ∗ CoreBody := by
    unfold MallocngCoreStA MallocngCoreStInflightA MallocngWF
    exact Entails.of_eq rfl
  refine Entails.trans hPf ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hExtractWf))) ?_
  have hPureWfEq :
      (MallocngInitBlock mallocngIface (fineBaseGam γ)).pureWf newQ (newSz, keptBs) =
        (FineInitBlockSem γ).pureWf newQ (newSz, max align 16, keptBs) := rfl
  rw [hPureWfEq]
  let RestNoPure :=
    (ghostMapAuth (fineAlignGam γ) alignMap0 ∗
     ghostMapElem (fineAlignGam γ) p (max align 16)) ∗
    (stackFrame s0 800 ∗ MallocngRoTablesA maddrs ∗ CoreBody ∗
     MallocngRuntime maddrs tp ∗
     ⌜(FineInitBlockSem γ).pureWf newQ (newSz, max align 16, keptBs)⌝ ∗
     (MallocngInitBlock mallocngIface (fineBaseGam γ)).interp newQ (newSz, keptBs) ∗
     Frame)
  refine Entails.trans (Q := ⌜MallocngWF maddrs.base brkStart sf.brk live' peak' st'⌝ ∗ RestNoPure)
    (Entails.of_eq (by
      dsimp only [RestNoPure]
      generalize (MallocngRoTablesA maddrs) = PRo
      generalize CoreBody = PBody
      generalize (MallocngRuntime maddrs tp) = PRt
      generalize ((FineInitBlockSem γ).pureWf newQ (newSz, max align 16, keptBs)) = PPure
      generalize ((MallocngInitBlock mallocngIface (fineBaseGam γ)).interp newQ (newSz, keptBs)) = PInterp
      ac_rfl)) ?_
  refine Entails.pure_left fun hwf' => ?_
  have hInv' : MallocngFineInv 0 bf (dynamicRootRegions st') alignMap' st' :=
    realloc_mremap_preserves_fineInv hInv0 hwf0 hwf' hg0 hg0Sc hIdx0 hSlot0 hAlign0
      hg0'Meta hg0'Sc hg0'Map hg0'Slots hEffDiff hFreshNewQ hGroups' hMetaEq hLiveMap'
  dsimp only [RestNoPure]
  refine Entails.trans (Entails.trans (sepConj_mono_left hMove) (bupd_frame_r _ _)) ?_
  refine bupd_mono ?_
  have hCoreEnt :
      ghostMapAuth (fineAlignGam γ) alignMap' ∗ CoreBody ⊢
        FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
          (dynamicRootRegions st') alignMap' live' peak' st' := by
    unfold FineCoreStInflightA MallocngCoreStInflightA
    rw [pure_sepConj_of_true hInv', pure_sepConj_of_true hwf']
    exact Entails.of_eq rfl
  have hPostEnv :
      MallocngRoTablesA maddrs ∗
      (ghostMapAuth (fineAlignGam γ) alignMap' ∗ CoreBody) ∗
      MallocngRuntime maddrs tp ⊢
        FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left hCoreEnt))
      (pack_finePostEnv γ tp brkStart bf ivs0 st' alignMap' live' peak' s0 sf
        hNoOrph0 htpSf hbrksSf)
  have hBlkEnt := rawInitBlock_to_fineInitBlock γ newQ newSz align keptBs
  refine Entails.trans (Q :=
      stackFrame s0 800 ∗
      (MallocngRoTablesA maddrs ∗
       (ghostMapAuth (fineAlignGam γ) alignMap' ∗ CoreBody) ∗
       MallocngRuntime maddrs tp) ∗
      ⌜(FineInitBlockSem γ).pureWf newQ (newSz, max align 16, keptBs)⌝ ∗
      ((MallocngInitBlock mallocngIface (fineBaseGam γ)).interp newQ (newSz, keptBs) ∗
       ghostMapElem (fineAlignGam γ) newQ (max align 16)) ∗
      Frame)
    (Entails.of_eq (by
      dsimp only [alignMap']
      generalize (MallocngRoTablesA maddrs) = PRo
      generalize CoreBody = PBody
      generalize (MallocngRuntime maddrs tp) = PRt
      generalize ((FineInitBlockSem γ).pureWf newQ (newSz, max align 16, keptBs)) = PPure
      generalize ((MallocngInitBlock mallocngIface (fineBaseGam γ)).interp newQ (newSz, keptBs)) = PInterp
      ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono hPostEnv
    (sepConj_mono_right (sepConj_mono_left hBlkEnt)))

/-- Raw-state Stage-3 post-`mremap` continuation (`+0x364` → `ret`). -/
def ReallocS3PostMremapRawStmt : Prop :=
  ∀ [MallocngMultiPlacement] {b : BitVec 64} (_hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    (_hCount : MallocngCountIvsWF bgt ivs0 st)
    (_hwf : MallocngWF maddrs.base brkStart s0.brk bgt.liveCost bgt.peakCost st)
    {g : GroupDesc} (_hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff : Nat} (origBs tailBs : List (BitVec 8))
    (_hOrigLe : origBs.length ≤ oldSz) (_hTailLen : tailBs.length = oldSz - origBs.length)
    (_hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (_hSc63 : g.sc = 63)
    {newBase : BitVec 64} {needed newSz : Nat}
    (errnoVal : BitVec 32)
    {Frame : SepProp} {oom : State → SepProp}
    (_hNewLo : 131051 < newSz) (_hNewHi : newSz ≤ MallocngMaxAllocSize)
    (_hNeedEq : needed = ((newSz + (p.toNat - (g.slotStart 0).toNat) + 4115) / 4096) * 4096)
    (_hNewBaseGe : 4096 ≤ newBase.toNat) (_hNewBaseAl : newBase.toNat % 4096 = 0)
    (_hNewBaseFit : newBase.toNat + needed ≤ 2 ^ 48)
    (_hOldRw : ∀ x, InRegion g.mem (g.maplen * 4096) x → s0.mem.perm x = some Perm.rw)
    (_hPermRel :
      (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ s.mem.perm = s0.mem.perm) ∨
      (∃ m1 : Memory, m1.perm = s0.mem.perm ∧
        s.mem.perm = (m1.remapRw g.mem (g.maplen * 4096) newBase needed).perm))
    (_hpc : s.pc = b + 0x364#64) (_hrun : s.status = .Running)
    (_hbrk : s.brk = s0.brk) (_hproc : MallocngProcPreserved s0 s)
    (_htp0 : s0.tpidrEl0 = tp) (_hbrks0 : s0.brkStart = brkStart)
    (_hsp : s.sp = s0.sp - 80#64) (_hal : s.spAligned = true) (_hsp0 : s0.sp &&& 15#64 = 0#64)
    (_hx0 : s.readReg64 .x0 = newBase)
    (_hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (p.toNat - (g.slotStart 0).toNat))
    (_hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (_hx22 : s.readReg64 .x22 = g.metaPtr)
    (_hx24 : s.readReg64 .x24 = 0#64)
    (_hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (newSz + (p.toNat - (g.slotStart 0).toNat) + 4115))
    (_hx26 : s.readReg64 .x26 = BitVec.ofNat 64 needed)
    (_hcs : ReallocUntouchedCS s0 s),
    let sp1 := s0.sp - 80#64
    let keptBs := origBs.take newSz
    let bsRemap0 := (mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)).take needed ++
      List.replicate (needed - g.maplen * 4096) 0#8
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      ((g.metaPtr ↦ₛ g.metaBytes) ∗ (newBase ↦ₛ bsRemap0) ∗
       (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ memMapped newBase needed ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ReallocMremapFrame maddrs tp st g ∗
        MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
        (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MallocngBlockToken γ p oldSz ∗ Frame))
      (fun sf Pf =>
        ∃ (st' : MallocngSt) (g' : GroupDesc) (newQ : BitVec 64) (newEff live' peak' : Nat),
          sf.mem.perm = s.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = newQ ∧
          g'.metaPtr = g.metaPtr ∧ g'.sc = 63 ∧ g'.maplen * 4096 = needed ∧
          g'.slots = [.liveUser newQ newSz newEff] ∧
          newEff - max newSz MallocngMinBlockCost = oldEff - max oldSz MallocngMinBlockCost ∧
          (newQ ≠ p → st.liveMap newQ = none) ∧
          st'.groups = st.groups.map (fun x => if x.metaPtr == g.metaPtr then g' else x) ∧
          st'.metaAreas = st.metaAreas ∧
          (∀ k, st'.liveMap k = if k = newQ then some newSz else if k = p then none else st.liveMap k) ∧
          MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem ∧
          (Pf ⊢ stackFrame s0 800 ∗ MallocngRoTablesA maddrs ∗
            MallocngCoreStA γ maddrs brkStart sf.brk live' peak' st' ∗
            MallocngRuntime maddrs tp ∗
            ⌜(MallocngInitBlock mallocngIface γ).pureWf newQ (newSz, keptBs)⌝ ∗
            (MallocngInitBlock mallocngIface γ).interp newQ (newSz, keptBs) ∗ Frame)) oom

/-- Lifts raw `ReallocS3PostMremapRawStmt` (`+0x364` → `ret`) to `FinePostEnv` + `FineInitBlockSem`
    by committing `realloc_mremap_preserves_fineInv` and moving `p → newQ` in `fineAlignGam`. -/
theorem realloc_s3_post_mremap_fine_of_raw [MallocngMultiPlacement]
    (hRaw : ReallocS3PostMremapRawStmt) {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bgt : FineBudget) (bCoarse : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt) (alignMap0 : BitVec 64 → Option Nat)
    (hInv0 : MallocngFineInv 0 bgt ivs0 alignMap0 st)
    (hCount : MallocngCountIvsWF bCoarse ivs0 st)
    (hwf : MallocngWF maddrs.base brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz align oldEff : Nat} (origBs tailBs : List (BitVec 8))
    (hAlign0 : alignMap0 p = some (max align 16))
    (hOrigLe : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    {newBase : BitVec 64} {needed newSz : Nat}
    (errnoVal : BitVec 32)
    {Frame : SepProp} {oom : State → SepProp}
    (hNewLo : 131051 < newSz) (hNewHi : newSz ≤ MallocngMaxAllocSize)
    (hNeedEq : needed = ((newSz + (p.toNat - (g.slotStart 0).toNat) + 4115) / 4096) * 4096)
    (hNewBaseGe : 4096 ≤ newBase.toNat) (hNewBaseAl : newBase.toNat % 4096 = 0)
    (hNewBaseFit : newBase.toNat + needed ≤ 2 ^ 48)
    (hOldRw : ∀ x, InRegion g.mem (g.maplen * 4096) x → s0.mem.perm x = some Perm.rw)
    (hPermRel :
      (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ s.mem.perm = s0.mem.perm) ∨
      (∃ m1 : Memory, m1.perm = s0.mem.perm ∧
        s.mem.perm = (m1.remapRw g.mem (g.maplen * 4096) newBase needed).perm))
    (hpc : s.pc = b + 0x364#64) (hrun : s.status = .Running)
    (hbrk : s.brk = s0.brk) (hproc : MallocngProcPreserved s0 s)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = newBase)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (p.toNat - (g.slotStart 0).toNat))
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hx22 : s.readReg64 .x22 = g.metaPtr)
    (hx24 : s.readReg64 .x24 = 0#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (newSz + (p.toNat - (g.slotStart 0).toNat) + 4115))
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 needed)
    (hcs : ReallocUntouchedCS s0 s) :
    let sp1 := s0.sp - 80#64
    let bf := FineBudget.stepRealloc align oldSz newSz bgt
    let keptBs := origBs.take newSz
    let bsRemap0 := (mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)).take needed ++
      List.replicate (needed - g.maplen * 4096) 0#8
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      ((g.metaPtr ↦ₛ g.metaBytes) ∗ (newBase ↦ₛ bsRemap0) ∗
       (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ memMapped newBase needed ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ReallocMremapFrame maddrs tp st g ∗
        MallocngLiveAuth (fineBaseGam γ) st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
        (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MallocngBlockToken (fineBaseGam γ) p oldSz ∗
        (ghostMapAuth (fineAlignGam γ) alignMap0 ∗
         ghostMapElem (fineAlignGam γ) p (max align 16) ∗ Frame)))
      (fun sf Pf =>
        ∃ newQ : BitVec 64,
          sf.mem.perm = s.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = newQ ∧
          (Pf ⊢ stackFrame s0 800 ∗
            FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(FineInitBlockSem γ).pureWf newQ (newSz, max align 16, keptBs)⌝ ∗
            (FineInitBlockSem γ).interp newQ (newSz, max align 16, keptBs) ∗ Frame)) oom := by
  intro sp1 bf keptBs bsRemap0
  apply sepWP_bupd_post
  refine SepWP.mono
    (hRaw hb (fineBaseGam γ) tp brkStart bCoarse ivs0 s0 s st hCount hwf hg hIdx0
      origBs tailBs hOrigLe hTailLen hSlot0 hSc63 errnoVal
      (Frame := ghostMapAuth (fineAlignGam γ) alignMap0 ∗
        ghostMapElem (fineAlignGam γ) p (max align 16) ∗ Frame)
      (oom := oom)
      hNewLo hNewHi hNeedEq hNewBaseGe hNewBaseAl hNewBaseFit hOldRw hPermRel
      hpc hrun hbrk hproc htp0 hbrks0 hsp hal hsp0 hx0 hx20 hx21 hx22 hx24 hx25 hx26 hcs) ?_
  intro sf Pf _ _ ⟨st', g', newQ, newEff, live', peak',
    hPermSf, hBrkSf, hProcSf, hSpSf, hCsSf, hX0Sf,
    hgMeta, hgSc, hgMap, hgSlots, hEffDiff, hFreshQ, hGroups', hMeta', hLiveMap', hNoOrph, hPf⟩
  refine ⟨stackFrame s0 800 ∗
      FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
      ⌜(FineInitBlockSem γ).pureWf newQ (newSz, max align 16, keptBs)⌝ ∗
      (FineInitBlockSem γ).interp newQ (newSz, max align 16, keptBs) ∗ Frame,
    commit_stage3_mremap_fine_bupd γ tp brkStart bgt ivs0 s0 sf st st'
      alignMap0 bCoarse.liveCost bCoarse.peakCost live' peak' keptBs Frame Pf
      hInv0 hwf hg hSc63 hIdx0 hSlot0 hAlign0
      hgMeta hgSc (hgMap.trans hNeedEq) hgSlots hEffDiff hFreshQ hGroups' hMeta' hLiveMap' hNoOrph
      (hProcSf.2.2.1.trans htp0) (hProcSf.2.2.2.1.trans hbrks0) hPf,
    newQ, hPermSf, hBrkSf, hProcSf, hSpSf, hCsSf, hX0Sf, Entails.refl _⟩

end LibsignalBinary.Heap.Fine
