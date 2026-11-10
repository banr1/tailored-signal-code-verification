/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullProof
public import VerifiedLibraries.Mallocng.Proofs.AccountingHelpers
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullStage1
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullStage2
public import VerifiedLibraries.Mallocng.Proofs.SyscallWrappersProof

/-!
# Fine-Grained `__malloc_alloc_meta` Helpers

Byte bounds (`allocMetaFineByteBound`), postcondition (`AllocMetaFinePost`), exit/activation/`mprotect`
segments, `PROT_NONE` batch allocation, and circular-list pop helpers for `__malloc_alloc_meta`
(`blk07`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open VerifiedLibraries.Mallocng.Proofs.AllocMetaFullH

/-- Tight per-call newly-mapped byte budget for `__malloc_alloc_meta()` indexed by `maxMetaAreas`
    (`32768 * maxMetaAreas`). -/
def allocMetaFineByteBound (maxMetaAreas : Nat) : Nat :=
  32768 * maxMetaAreas

/-! ## `metaAreas.length` and `PROT_NONE` Batch Bounds -/

theorem appendMetaArea_len_le_fine {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost maxGroups maxMetaAreas : Nat} {st : MallocngSt} (ap : BitVec 64)
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hInflight : inflight ≤ 7) (hNoFree : st.freeMetas = []) (hNoBump : st.bumpMetas = [])
    (hGroups : st.groups.length ≤ maxGroups)
    (hMetaStep : 1 + (7 + maxGroups) / 101 ≤ maxMetaAreas) :
    (appendMetaArea st.metaAreas ap).length ≤ maxMetaAreas := by
  have hAppLen : (appendMetaArea st.metaAreas ap).length = st.metaAreas.length + 1 :=
    (appendMetaArea_props st.metaAreas ap).2.1
  let usedAndFree :=
    st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas ++ st.reservedMetas
  have ⟨_, hUfIff⟩ := hwf.free_bump_metas_wf.2.2.2.2
  have hAllSlotsLen : (allMetaSlots st).length = 101 * st.metaAreas.length := by
    unfold allMetaSlots
    induction st.metaAreas with
    | nil => rfl
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range, ih,
        List.length_cons]
      omega
  have hSlotNd : (allMetaSlots st).Nodup := by
    have hSlotEq : ∀ (x : MetaAreaDesc) (k : Nat), x.base.toNat + 4096 ≤ 2 ^ 48 → k < 101 →
        (x.slotAddr k).toNat = x.base.toNat + (24 + 40 * k) := fun x k _ hk => by
      simp only [MetaAreaDesc.slotAddr, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 24 + 40 * k < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : x.base.toNat + (24 + 40 * k) < 2 ^ 64)]
    have hAux : ∀ mas : List MetaAreaDesc, (mas.map (·.base)).Nodup →
        (∀ ma ∈ mas, 4096 ≤ ma.base.toNat ∧ ma.base.toNat % 4096 = 0 ∧ ma.base.toNat + 4096 ≤ 2 ^ 48) →
        (mas.flatMap fun ma => (List.range 101).map ma.slotAddr).Nodup := by
      intro mas hNd hB; induction mas with
      | nil => exact List.nodup_nil
      | cons ma rest ih =>
        simp only [List.map_cons, List.nodup_cons] at hNd; simp only [List.flatMap_cons]
        have hMaB := hB ma List.mem_cons_self
        have hRestB := fun m' (hm' : m' ∈ rest) => hB m' (List.mem_cons_of_mem ma hm')
        have hHeadNd : ((List.range 101).map ma.slotAddr).Nodup := by
          have hMapInj : ∀ {xs : List Nat}, xs.Nodup →
              (∀ a ∈ xs, ∀ b ∈ xs, ma.slotAddr a = ma.slotAddr b → a = b) →
              (xs.map ma.slotAddr).Nodup := by
            intro xs hndX hinjX; induction xs with
            | nil => exact List.nodup_nil
            | cons x tl ihX =>
              simp only [List.map_cons, List.nodup_cons] at hndX ⊢
              refine ⟨fun hm => ?_, ihX hndX.2 (fun a ha b hb h =>
                hinjX a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) h)⟩
              obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
              exact hndX.1 (hinjX x List.mem_cons_self y (List.mem_cons_of_mem x hy) hfy.symm ▸ hy)
          refine hMapInj List.nodup_range (fun k1 hk1 k2 hk2 hEq => ?_)
          have hk1' := List.mem_range.mp hk1; have hk2' := List.mem_range.mp hk2
          have ht := congrArg BitVec.toNat hEq
          rw [hSlotEq ma k1 hMaB.2.2 hk1', hSlotEq ma k2 hMaB.2.2 hk2'] at ht; omega
        refine List.nodup_append.mpr ⟨hHeadNd, ih hNd.2 hRestB, fun a ha b hb hAb => ?_⟩
        subst hAb; obtain ⟨k1, hk1, rfl⟩ := List.mem_map.mp ha
        obtain ⟨ma2, hma2, hb'⟩ := List.mem_flatMap.mp hb; obtain ⟨k2, hk2, hEq⟩ := List.mem_map.mp hb'
        have hk1' := List.mem_range.mp hk1; have hk2' := List.mem_range.mp hk2
        have hMa2B := hRestB ma2 hma2; have ht := congrArg BitVec.toNat hEq
        rw [hSlotEq ma k1 hMaB.2.2 hk1', hSlotEq ma2 k2 hMa2B.2.2 hk2'] at ht
        exact hNd.1 ((BitVec.eq_of_toNat_eq (by omega : ma.base.toNat = ma2.base.toNat)) ▸ List.mem_map_of_mem hma2)
    exact hAux st.metaAreas hwf.metaAreas_wf.1
      (fun ma hma => ⟨(hwf.metaAreas_wf.2.1 ma hma).1, (hwf.metaAreas_wf.2.1 ma hma).2.1, (hwf.metaAreas_wf.2.1 ma hma).2.2.1⟩)
  have hSlotsLeUf : (allMetaSlots st).length ≤ usedAndFree.length :=
    nodup_length_le_of_subset hSlotNd (fun x hx => (hUfIff x).mpr hx)
  have hInf := hwf.inflight_wf
  have hUfLen : usedAndFree.length = st.groups.length + st.reservedMetas.length := by
    simp [usedAndFree, hNoFree, hNoBump]
  have hDiv : st.metaAreas.length ≤ (7 + maxGroups) / 101 :=
    (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  omega

private theorem shift_mmap_bound_check :
    ((List.range 41).all fun m =>
      m == 0 || decide (4096 * 2 ^ (m + 1) + 4096 ≤ 32768 * (2 ^ m - m))) = true := by
  decide +kernel

private theorem metaAreas_mmap_bytes_le_fine
    {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost maxMetaAreas : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hInflight : inflight ≤ 7) (hNoFree : st.freeMetas = [])
    (hNoBump : st.bumpMetas = []) (hNoAvail : st.availMetaPages = [])
    (hMeta0 : st.metaAreas.length ≤ maxMetaAreas)
    (hMetaPos : 1 ≤ maxMetaAreas) :
    let m := st.ctx.metaAllocShift.toNat
    let len := 4096 * 2 ^ (m + 1)
    m ≤ 35 ∧ 8192 ≤ len ∧ len ≤ 2 ^ 48 ∧ 4096 ∣ len ∧ len + 4096 ≤ allocMetaFineByteBound maxMetaAreas := by
  intro m len
  obtain ⟨hmLe35, hGe8192, hLe48, hDvd, _⟩ :=
    slowPathC_prep_bounds hwf hInflight hNoFree hNoBump hNoAvail
  refine ⟨hmLe35, hGe8192, hLe48, hDvd, ?_⟩
  unfold allocMetaFineByteBound
  by_cases hm0 : m = 0
  · dsimp only [len]; rw [hm0]; omega
  · obtain ⟨hm40, h2m, _, _, _⟩ := hwf.meta_pages_bound.2.2 m (by omega) rfl
    have hchk := List.all_eq_true.mp shift_mmap_bound_check m (List.mem_range.mpr (by omega))
    simp only [Bool.or_eq_true, beq_iff_eq, hm0, false_or, decide_eq_true_eq] at hchk
    have hmul : 32768 * (2 ^ m - m) ≤ 32768 * maxMetaAreas :=
      Nat.mul_le_mul_left 32768 (Nat.le_trans h2m hMeta0)
    dsimp only [len]; omega

/-! ## Postcondition and Exit Segments -/

abbrev AllocMetaFinePost [MallocngMultiPlacement] (inflight : Nat) (γ : GhostName)
    (tp brkStart : BitVec 64) (liveCost peakCost maxMetaAreas : Nat) (st : MallocngSt)
    (s0 sf : State) (P_f : SepProp) : Prop :=
  (P_f ⊢ ∃∗ st' : MallocngSt, ∃∗ m : BitVec 64,
    ⌜MallocngProcPreserved s0 sf ∧ sf.readReg64 .x0 = m ∧ m ≠ 0#64 ∧
     4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧
     m ∉ st.reservedMetas ∧ st'.reservedMetas = m :: st.reservedMetas ∧
     st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
     st'.liveMap = st.liveMap ∧ totalLiveCount st' = totalLiveCount st ∧
     st'.metaAreas.length ≤ maxMetaAreas ∧
     st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
     st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧
     st'.ctx.seq = st.ctx.seq ∧
     (∀ g ∈ st.groups, ∀ a : BitVec 64,
       (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) ∧
     MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem ∧
     MallocngMappedDelta 1 (allocMetaFineByteBound maxMetaAreas) s0.mem sf.mem⌝ ∗
    stackFrame s0 224 ∗ MallocngRuntime maddrs tp ∗ (m ↦ₛ List.replicate 40 0#8) ∗
    MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st') ∧
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

theorem allocMetaFinePost_congr [MallocngMultiPlacement] {inflight : Nat} {γ : GhostName}
    {tp brkStart : BitVec 64} {liveCost peakCost maxMetaAreas : Nat} {st1 st2 : MallocngSt}
    {s0 sf : State} {P_f : SepProp}
    (hEq : st1.reservedMetas = st2.reservedMetas ∧ st1.groups = st2.groups ∧ st1.activeLists = st2.activeLists ∧
      st1.liveMap = st2.liveMap ∧ st1.metaAreas = st2.metaAreas ∧ st1.guardPages = st2.guardPages ∧
      st1.availMetaPages = st2.availMetaPages ∧ st1.ctx.active = st2.ctx.active ∧
      st1.ctx.usageByClass = st2.ctx.usageByClass ∧ st1.ctx.unmapSeq = st2.ctx.unmapSeq ∧
      st1.ctx.bounces = st2.ctx.bounces ∧ st1.ctx.seq = st2.ctx.seq ∧ st1.byteVal = st2.byteVal)
    (hPost : AllocMetaFinePost inflight γ tp brkStart liveCost peakCost maxMetaAreas st1 s0 sf P_f) :
    AllocMetaFinePost inflight γ tp brkStart liveCost peakCost maxMetaAreas st2 s0 sf P_f := by
  obtain ⟨r1, r2, r3, r4, rMa, rGp, rAv, r5, r6, r7, r8, r9, r10⟩ := hEq
  have rCnt : totalLiveCount st1 = totalLiveCount st2 := by unfold totalLiveCount; rw [r2]
  have rDyn : dynamicRootRegions st1 = dynamicRootRegions st2 := by
    unfold dynamicRootRegions; rw [rMa, rGp, rAv, r2]
  unfold AllocMetaFinePost at hPost ⊢
  rwa [r1, r2, r3, r4, rCnt, r5, r6, r7, r8, r9, r10, rDyn] at hPost

private theorem sepWP_epilogue_278_fine [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost maxMetaAreas : Nat}
    {st st' : MallocngSt} {m w0 w1 : BitVec 64} {errnoVal : BitVec 32} {s0 s : State} {oom : State → SepProp}
    (hWords : Blk07HasWords116 mallocngFaultSvcAmf) (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (words_ret_off% blk07Words - 16#64)) (hRun : s.status = .Running)
    (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true) (hx19 : s.readReg64 .x19 = m)
    (hCs21 : Cs21Preserved s0 s) (hProc : MallocngProcPreserved s0 s) (hMaBound : st'.metaAreas.length ≤ maxMetaAreas)
    (hNoOrph : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem s.mem)
    (hDelta : MallocngMappedDelta 1 (allocMetaFineByteBound maxMetaAreas) s0.mem s.mem)
    (hmProps : m ≠ 0#64 ∧ 4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.reservedMetas)
    (hWf' : MallocngWFInflight (inflight + 1) maddrs.base brkStart s.brk liveCost peakCost st')
    (hPres : st'.reservedMetas = m :: st.reservedMetas ∧ st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
      st'.liveMap = st.liveMap ∧ st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
      st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq)
    (hGrpPost : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        (m ↦₆₄ w0) ∗ ((m + 8#64) ↦₆₄ w1) ∗ ((m + 16#64) ↦ₛ List.replicate 24 0#8) ∗ CtxCells maddrs.ctx st'.ctx ∗
        ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
        ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st'))))
      (AllocMetaFinePost inflight γ tp brkStart liveCost peakCost maxMetaAreas st s0) oom := by
  have hSpA : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hSp0
  have hSpSub : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 80#64 hSpA
  have hSubAddSp : s0.sp - 80#64 + 80#64 = s0.sp := BitVec.sub_add_cancel s0.sp 80#64
  refine SepWP.mono (sepWP_lift_faultSvcAmf_cl
    (sepPost (fun sf => MallocngProcPreserved s0 sf ∧ sf.brk = s.brk ∧ sf.readReg64 .x0 = m ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦ₛ List.replicate 24 0#8) ∗ CtxCells maddrs.ctx st'.ctx ∗
        ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
        ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl ?_) ?_
  · unfold StackFrameOpen SavedRegs0; simp only [BitVec.reduceSub] at hPc
    wp_sym_steps; simp only [hSubAddSp] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
  · intro sf P_f _ _ ⟨_, hD2, _, ⟨hProcF, hBrkF, hx0F, hSpF, hCsF⟩, hEnt⟩
    refine ⟨Entails.trans hEnt (Entails.sepExists_right st' (Entails.sepExists_right m ?_)), hSpF, hCsF⟩
    have hNoOrphF := noOrphanMappings_of_mappedDelta_zero hNoOrph hD2
    have hDeltaF : MallocngMappedDelta 1 (allocMetaFineByteBound maxMetaAreas) s0.mem sf.mem :=
      MallocngMappedDelta.mono (by decide) (by omega) (MallocngMappedDelta.trans hDelta hD2)
    have ⟨hActL, hUseL, hUnmapL, hBncL, hPadEq, _⟩ := hWf'.ctx_lens
    have hCtxEq := (ctx_toBytes_eq_cells maddrs.ctx st'.ctx hActL hUseL hUnmapL hBncL (by rw [hPadEq]; rfl)).symm
    have hZ40 := (zero40_eq_cells m).symm
    have hWfF : MallocngWFInflight (inflight + 1) maddrs.base brkStart sf.brk liveCost peakCost st' := hBrkF ▸ hWf'
    have hCntEq : totalLiveCount st' = totalLiveCount st := by unfold totalLiveCount; rw [hPres.2.1]
    refine Entails.pure_right ⟨hProcF, hx0F, hmProps.1, hmProps.2.1, hmProps.2.2.1, hmProps.2.2.2.1, hmProps.2.2.2.2,
      hPres.1, hPres.2.1, hPres.2.2.1, hPres.2.2.2.1, hCntEq, hMaBound, hPres.2.2.2.2.1, hPres.2.2.2.2.2.1,
      hPres.2.2.2.2.2.2.1, hPres.2.2.2.2.2.2.2.1, hPres.2.2.2.2.2.2.2.2, hGrpPost, hNoOrphF, hDeltaF⟩ ?_
    refine Entails.trans (sepConj_mono_left (stack224_fold s0)) ?_
    unfold StaticFrameA MallocngCoreStInflightA MallocngRuntime; rw [← hCtxEq, ← hZ40, pure_sepConj_of_true hWfF]; sep_frame

theorem sepWP_epilogue_26c_fine [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost maxMetaAreas : Nat}
    {st st' : MallocngSt} {m oldAv oldCnt : BitVec 64} {errnoVal : BitVec 32} {s0 s : State} {oom : State → SepProp}
    (hWords : Blk07HasWords116 mallocngFaultSvcAmf) (_hRange : Blk07Range116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (words_ret_off% blk07Words - 28#64)) (hRun : s.status = .Running)
    (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true) (hx19 : s.readReg64 .x19 = m)
    (hx0 : s.readReg64 .x0 = st'.ctx.availMetaCount) (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx)
    (hAvEq : st'.ctx.availMeta = m + 40#64) (hCs21 : Cs21Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hMaBound : st'.metaAreas.length ≤ maxMetaAreas)
    (hNoOrph : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem s.mem)
    (hDelta : MallocngMappedDelta 1 (allocMetaFineByteBound maxMetaAreas) s0.mem s.mem)
    (hmProps : m ≠ 0#64 ∧ 4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.reservedMetas)
    (hWf' : MallocngWFInflight (inflight + 1) maddrs.base brkStart s.brk liveCost peakCost st')
    (hPres : st'.reservedMetas = m :: st.reservedMetas ∧ st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
      st'.liveMap = st.liveMap ∧ st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
      st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq)
    (hGrpPost : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        (m ↦ₛ List.replicate 40 0#8) ∗ CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt } ∗
        ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
        ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st'))))
      (AllocMetaFinePost inflight γ tp brkStart liveCost peakCost maxMetaAreas st s0) oom := by
  rw [zero40_eq_cells m]
  refine SepWP.cut_at_off (mbase 7) (words_ret_off% blk07Words - 16#64)
    (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + (words_ret_off% blk07Words - 16#64) ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 .x19 = m ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦ₛ List.replicate 24 0#8) ∗ CtxCells maddrs.ctx st'.ctx ∗
        ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
        ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl ?_) ?_)
  · unfold CtxCells; dsimp only [ctxMiddleBytes]; simp only [BitVec.reduceSub] at hPc; conv => arg 2; simp only [BitVec.reduceSub]
    wp_sym_steps; simp only [← hAvEq] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    exact SepWP.weaken_pre hEnt1 (sepWP_epilogue_278_fine hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hCs1 hProc1
      hMaBound (noOrphanMappings_of_mappedDelta_zero hNoOrph hD1)
      (MallocngMappedDelta.mono (by decide) (by omega) (MallocngMappedDelta.trans hDelta hD1)) hmProps (hBrk1 ▸ hWf') hPres hGrpPost)

theorem sepWP_activate_2a0_fine [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost maxMetaAreas : Nat}
    {st st' : MallocngSt} {ap oldAv oldCnt oldHd oldTl oldAreas : BitVec 64}
    {bv0 bv1 : BitVec 64 → BitVec 8} {errnoVal : BitVec 32} {s0 s : State} {oom : State → SepProp}
    (hWords : Blk07HasWords116 mallocngFaultSvcAmf) (hRange : Blk07Range116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (words_ret_off% blk07Words + 24#64)) (hRun : s.status = .Running)
    (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true) (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx)
    (hx21 : s.readReg64 .x21 = ap) (hCs25 : Cs25Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hMaBound : st'.metaAreas.length ≤ maxMetaAreas)
    (hNoOrph : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem s.mem)
    (hDelta : MallocngMappedDelta 1 (allocMetaFineByteBound maxMetaAreas) s0.mem s.mem)
    (hCtxEqs : st'.ctx.availMeta = ap + 64#64 ∧ st'.ctx.availMetaCount = 100#64 ∧
      st'.ctx.metaAreaTail = ap ∧ st'.ctx.availMetaAreas = ap + 4096#64 ∧
      (st.metaAreas = [] → oldTl = 0#64 ∧ st'.ctx.metaAreaHead = ap) ∧
      (∀ hne : st.metaAreas ≠ [], oldTl = (st.metaAreas.getLast hne).base ∧ oldHd = st'.ctx.metaAreaHead ∧ (oldTl == 0#64) = false))
    (hTailBm : ∀ hne : st.metaAreas ≠ [], let tb := (st.metaAreas.getLast hne).base
      ByteMap st'.masterDom (OwnedRwByte st) bv0 = ((tb ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) ∧
      ((tb ↦ₛ metaHdrBytes st'.ctx.secret ap) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) = ByteMap st'.masterDom (OwnedRwByte st) bv1)
    (hNilBv : st.metaAreas = [] → bv1 = bv0)
    (hApBm : ((ap ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ((ap + 64#64) ↦ₛ List.replicate 4032 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st) bv1) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal)
    (hmProps : (ap + 24#64) ≠ 0#64 ∧ 4096 ≤ (ap + 24#64).toNat ∧ (ap + 24#64).toNat % 8 = 0 ∧ (ap + 24#64).toNat + 40 ≤ 2 ^ 48 ∧ (ap + 24#64) ∉ st.reservedMetas)
    (hWf' : MallocngWFInflight (inflight + 1) maddrs.base brkStart s.brk liveCost peakCost st')
    (hPres : st'.reservedMetas = (ap + 24#64) :: st.reservedMetas ∧ st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
      st'.liveMap = st.liveMap ∧ st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
      st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq)
    (hGrpPost : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        (ap ↦ₛ List.replicate 4096 0#8) ∗ CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := oldHd, metaAreaTail := oldTl, availMetaAreas := oldAreas } ∗
        ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
        ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st'))))
      (AllocMetaFinePost inflight γ tp brkStart liveCost peakCost maxMetaAreas st s0) oom := by
  have hSpA : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hSp0
  have hSpSub : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 80#64 hSpA
  have hCntSub : st'.ctx.availMetaAreaCount + 1#64 - 1#64 = st'.ctx.availMetaAreaCount := BitVec.add_sub_cancel _ _
  have hAv64 : (ap + 24#64) + 40#64 = ap + 64#64 := by bv_arith
  rw [zeroPage_eq_metaArea_cells ap]
  refine SepWP.cut_at_off (mbase 7) (words_ret_off% blk07Words - 28#64)
    (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + (words_ret_off% blk07Words - 28#64) ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 .x19 = ap + 24#64 ∧ s1.readReg64 .x0 = st'.ctx.availMetaCount ∧ s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧
      Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        ((ap + 24#64) ↦ₛ List.replicate 40 0#8) ∗ CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt } ∗
        ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
        ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl ?_) ?_)
  · rw [← hApBm, metaHdrBytes_eq_cells]; unfold StackFrameSlow SavedRegs21 CtxCells; dsimp only [ctxMiddleBytes]
    conv => arg 2; simp only [BitVec.reduceSub]
    cases hMaEq : st.metaAreas with
    | nil =>
      obtain ⟨hTl0, hHdAp⟩ := hCtxEqs.2.2.2.2.1 hMaEq
      rw [hNilBv hMaEq, hTl0]; wp_sym_steps; simp only [hCntSub, ← hHdAp, ← hCtxEqs.2.1] at *
      obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25; wp_done
    | cons hd tl =>
      have hne : st.metaAreas ≠ [] := by simp [hMaEq]
      obtain ⟨hTlEq, hHdEq, hTlBeq⟩ := hCtxEqs.2.2.2.2.2 hne; obtain ⟨hExT, hAbsT⟩ := hTailBm hne
      rw [hExT, ← hAbsT, metaHdrBytes_eq_cells, metaHdrBytes_eq_cells, hTlEq, hHdEq]
      rw [hTlEq] at hTlBeq; simp only [hMaEq] at hTlBeq ⊢
      wp_sym_steps; simp only [hCntSub, ← hCtxEqs.2.1] at *
      obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25; wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hx0_1, hx20_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    exact SepWP.weaken_pre (Entails.trans hEnt1 (sepConj_mono_left (stackSlow_to_open s0)))
      (sepWP_epilogue_26c_fine hWords hRange hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hx0_1 hx20_1 (hCtxEqs.1.trans hAv64.symm) hCs1 hProc1
        hMaBound (noOrphanMappings_of_mappedDelta_zero hNoOrph hD1)
        (MallocngMappedDelta.mono (by decide) (by omega) (MallocngMappedDelta.trans hDelta hD1)) hmProps (hBrk1 ▸ hWf') hPres hGrpPost)

theorem sepWP_mprotect_224_fine [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost maxMetaAreas : Nat}
    {st st' : MallocngSt} {ap oldAv oldCnt oldHd oldTl oldAreas : BitVec 64}
    {bv0 bv1 : BitVec 64 → BitVec 8} {errnoVal : BitVec 32} {s0 s : State}
    (hWords : Blk07HasWords116 mallocngFaultSvcAmf)
    (hRange : Blk07Range116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hMetaPos : 1 ≤ maxMetaAreas)
    (hPc : s.pc = mbase 7 + (reloc_call_off% blk07Relocs "mprotect" - 12#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hTp0 : s0.tpidrEl0 = tp)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx) (hx21 : s.readReg64 .x21 = ap) (hx24 : s.readReg64 .x24 = 4096#64)
    (hApAlign : 4096 ∣ ap.toNat) (hApFit : ap.toNat + 4096 ≤ 2 ^ 48)
    (hCs25 : Cs25Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hMaBound : st'.metaAreas.length ≤ maxMetaAreas)
    (hNoOrph : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem s.mem)
    (hDelta : MallocngMappedDelta 1 (allocMetaFineByteBound maxMetaAreas - 4096) s0.mem s.mem)
    (hCtxEqs : st'.ctx.availMeta = ap + 64#64 ∧ st'.ctx.availMetaCount = 100#64 ∧
      st'.ctx.metaAreaTail = ap ∧ st'.ctx.availMetaAreas = ap + 4096#64 ∧
      (st.metaAreas = [] → oldTl = 0#64 ∧ st'.ctx.metaAreaHead = ap) ∧
      (∀ hne : st.metaAreas ≠ [], oldTl = (st.metaAreas.getLast hne).base ∧ oldHd = st'.ctx.metaAreaHead ∧ (oldTl == 0#64) = false))
    (hTailBm : ∀ hne : st.metaAreas ≠ [], let tb := (st.metaAreas.getLast hne).base
      ByteMap st'.masterDom (OwnedRwByte st) bv0 = ((tb ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) ∧
      ((tb ↦ₛ metaHdrBytes st'.ctx.secret ap) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) = ByteMap st'.masterDom (OwnedRwByte st) bv1)
    (hNilBv : st.metaAreas = [] → bv1 = bv0)
    (hApBm : ((ap ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ((ap + 64#64) ↦ₛ List.replicate 4032 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st) bv1) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal)
    (hmProps : (ap + 24#64) ≠ 0#64 ∧ 4096 ≤ (ap + 24#64).toNat ∧ (ap + 24#64).toNat % 8 = 0 ∧ (ap + 24#64).toNat + 40 ≤ 2 ^ 48 ∧ (ap + 24#64) ∉ st.reservedMetas)
    (hWf' : MallocngWFInflight (inflight + 1) maddrs.base brkStart s.brk liveCost peakCost st')
    (hPres : st'.reservedMetas = (ap + 24#64) :: st.reservedMetas ∧ st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
      st'.liveMap = st.liveMap ∧ st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
      st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq)
    (hGrpPost : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (ap ↦ₙ List.replicate 4096 0#8) ∗
          CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := oldHd, metaAreaTail := oldTl, availMetaAreas := oldAreas } ∗
          ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))
      (AllocMetaFinePost inflight γ tp brkStart liveCost peakCost maxMetaAreas st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (allocMetaFineByteBound maxMetaAreas) s0 sf⌝) := by
  let P_rest := StaticFrameA γ maddrs st'.liveMap ∗
    CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := oldHd, metaAreaTail := oldTl, availMetaAreas := oldAreas } ∗
    ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
    ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
    MappedSet st'.masterDom (OwnedMappedByte st')
  let retPc := mbase 7 + (reloc_call_off% blk07Relocs "mprotect" + 4#64)
  refine SepWP.cut (mid := mbase 17)
    (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 17 ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 Reg.lr = retPc ∧ s1.readReg64 .x0 = ap ∧ s1.readReg64 .x1 = 4096#64 ∧ s1.readReg32 .x2 = 3#32 ∧
      s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s1.readReg64 .x21 = ap ∧
      Cs25Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ ((ap ↦ₙ List.replicate 4096 0#8) ∗ P_rest))))) hcl ?_) ?_)
  · dsimp only [P_rest, retPc] at hPc ⊢
    simp only [BitVec.reduceSub] at hPc; wp_sym_steps
    simp only [show ∀ x y : BitVec 64, x + (y - x) = y from fun _ _ => by bv_arith] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25
    wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hLr1, hx0_1, hx1_1, hx2_1, hx20_1, hx21_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    refine SepWP.weaken_pre hEnt1 ?_
    unfold StackFrameSlow; rw [stack64_split_48 hSp1]
    have hSpA1 : s1.spAligned = true := by rw [State.spAligned, hSp1]; exact spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
    have hTp1 : s1.tpidrEl0 = tp := hProc1.2.2.1.trans hTp0
    have hx1Nat : (s1.readReg64 .x1).toNat = 4096 := by rw [hx1_1]; rfl
    refine call_withCL_frame_auto (x := ())
      (placed_mprotectRwWrapper_ok (P := mallocngBlockProg mmpl 7 msvc) tp ap errnoVal (List.replicate 4096 0#8) 4096 List.length_replicate (by decide) (by decide) hApAlign hApFit (by intro pc; simp) rfl)
      hcl1 hPc1 hRun1 hSpA1 hLr1 (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (h_oom := fun R' sf _ hSatOom => by
        have hDrop := Satisfies.drop_mid hSatOom
        rw [satisfies_pure_sepConj] at hDrop ⊢
        obtain ⟨hFsEq, hTrEq, hSigEq, _, hDMp, hPhysLt⟩ := hDrop.1
        refine ⟨MallocngPlacedOomCond.of_delta (hFsEq.trans hProc1.1) (hTrEq.trans hProc1.2.1)
          (hSigEq.trans hProc1.2.2.2.2.2.2) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta hD1) hDMp)
          (by omega) (by unfold allocMetaFineByteBound; omega)
          (fun _ => ⟨4096, by decide, by decide, by unfold allocMetaFineByteBound; omega, Or.inr hPhysLt⟩), hDrop.2⟩) ?_
    intro s2 hPc2 hRun2 hSp2 hCsCall hcl2
    dsimp only; rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hProcCall, hBrk2, hw0_2, hDCall⟩
    refine SepWP.weaken_pre (Entails.trans
      (Q := (memRegion (s0.sp - 80#64 - 64#64) 16 ∗ stackFrame s1 48) ∗
        (memRegion (s0.sp - 224#64) 80 ∗ SavedRegs0 s0 ∗ SavedRegs21 s0 ∗ cells (s0.sp - 16#64) 2 ∗
          (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₛ List.replicate 4096 0#8) ∗ P_rest))))
      (R := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₛ List.replicate 4096 0#8) ∗ P_rest)))
      (by unfold SavedRegs0 SavedRegs21; dsimp only [P_rest]; sep_frame)
      (by rw [← stack64_split_48 hSp1]; unfold StackFrameSlow; sep_frame)) ?_
    refine SepWP.cut_at_off (mbase 7) (words_ret_off% blk07Words + 24#64)
      (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s3 =>
        s3.pc = mbase 7 + (words_ret_off% blk07Words + 24#64) ∧
        s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧
        s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s3.readReg64 .x21 = ap ∧
        Cs25Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = s.brk)
        (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₛ List.replicate 4096 0#8) ∗ P_rest)))) hcl2 ?_) ?_)
    · dsimp only [retPc] at hPc2
      have hx20_2 : s2.readReg64 .x20 = Obj.pageOf maddrs.ctx := hCsCall.2.1.trans hx20_1
      have hx21_2 : s2.readReg64 .x21 = ap := hCsCall.2.2.1.trans hx21_1
      have hCs2 : Cs25Preserved s0 s2 := ⟨hCsCall.2.2.2.2.2.2.1.trans hCs1.1, hCsCall.2.2.2.2.2.2.2.1.trans hCs1.2.1,
        hCsCall.2.2.2.2.2.2.2.2.1.trans hCs1.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.1.trans hCs1.2.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.2.2.trans hCs1.2.2.2.2⟩
      have hProc2 : MallocngProcPreserved s0 s2 := procPreserved_trans hProc1 hProcCall
      have hw0Cond : (BitVec.zeroExtend 64 (BitVec.truncate 32 (s2.readReg64 (Reg.gpr 0#5))) == 0#64) = true := by
        change (BitVec.zeroExtend 64 (s2.readReg32 .x0) == 0#64) = true; rw [hw0_2]; rfl
      dsimp only [P_rest]; conv => arg 2; simp only [BitVec.reduceAdd]
      wp_sym_steps
      obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs2
      rw [← hBrk1, ← hBrk2]; wp_done
    · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx20_3, hx21_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
      have hD0_s_s3 : MallocngMappedDelta 0 0 s.mem s3.mem :=
        MallocngMappedDelta.mono (by decide) (by decide)
          (MallocngMappedDelta.trans (MallocngMappedDelta.trans hD1 hDCall) hD3)
      have hDTot : MallocngMappedDelta 1 (allocMetaFineByteBound maxMetaAreas) s0.mem s3.mem := by
        refine MallocngMappedDelta.mono ?_ ?_ (MallocngMappedDelta.trans hDelta hD0_s_s3)
        all_goals omega
      exact SepWP.weaken_pre (Entails.trans hEnt3 (by dsimp only [P_rest]; sep_frame))
        (sepWP_activate_2a0_fine hWords hRange hcl3 hPc3 hRun3 hSp3 hSp0
          hx20_3 hx21_3 hCs3 hProc3 hMaBound (noOrphanMappings_of_mappedDelta_zero hNoOrph hD0_s_s3)
          hDTot hCtxEqs hTailBm hNilBv hApBm hmProps (hBrk3 ▸ hWf') hPres hGrpPost)

/-! ## `PROT_NONE` Batch and Circular-List Pop -/

local macro "wp_norm_mbase_pc" : tactic =>
  `(tactic| conv in (mbase _ + _ + _) => rw [BitVec.add_assoc]; simp only [BitVec.reduceAdd])

private abbrev MmapNewInRegionFine (mb : BitVec 64) (len : Nat) (m0 mf : Memory) : Prop :=
  ∀ a : BitVec 64, (mf.perm a).mapped = true → (m0.perm a).mapped = true ∨ InRegion mb len a

private theorem perm_mapZeroProtNone_inRegion_fine {m0 m3 mf : Memory} {mb : BitVec 64} {len : Nat}
    (hm3 : m3.perm = m0.perm) (hmf : mf.perm = ((m3.mapZero mb len).setPermNonFrozen mb len Perm.protNone).perm) :
    MmapNewInRegionFine mb len m0 mf := by
  intro a ha
  have ha' : ((m3.mapZero mb len).perm a).mapped = true := by
    rw [hmf, Memory.perm_setPermNonFrozen] at ha
    split at ha
    · rename_i hc; simp only [Bool.and_eq_true] at hc; exact hc.1.2
    · exact ha
  rw [Memory.perm_mapZero] at ha'
  split at ha'
  · rename_i hc2; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc2; exact Or.inr hc2.1
  · exact Or.inl (hm3 ▸ ha')

set_option maxHeartbeats 400000 in
private theorem placed_mmapProtNone_inRegion_ok_fine [MallocngMultiPlacement] {P : Program}
    (tp : BitVec 64) (errnoVal : BitVec 32) (rawLen : Nat) (hpos : 0 < rawLen) (hmax : rawLen ≤ 2 ^ 62)
    (hext : ∀ pc, P.externAt? pc = none := by intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    let len := pageAlignUp rawLen
    subroutine_ok P (mbase 16) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = 0#64 ∧ (s0.readReg64 .x1).toNat = rawLen ∧
         s0.readReg32 .x2 = 0#32 ∧ s0.readReg32 .x3 = 0x22#32 ∧ s0.readReg32 .x4 = BitVec.allOnes 32 ∧ s0.readReg64 .x5 = 0#64⌝ ∗
        stackFrame s0 64 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal)
      post := fun _ s0 sf => ∃∗ mb : BitVec 64,
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.readReg64 .x0 = mb ∧ mb ≠ 0#64 ∧ mb ≠ BitVec.allOnes 64 ∧
         4096 ∣ mb.toNat ∧ mb.toNat + len ≤ 2 ^ 48 ∧ MallocngMappedDelta 1 len s0.mem sf.mem ∧ MmapNewInRegionFine mb len s0.mem sf.mem⌝ ∗
        stackFrame s0 64 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (mb ↦ₙ List.replicate len 0#8) ∗ memMapped mb len
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧ (MallocngSanitizedSvc msvc → MallocngNoGapOrPhys sf len)⌝
    }) := by
  intro len; refine subroutine_ok_block_to_block (j := 16) (by decide) ?_ hext hsvc; clear hext hsvc P
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have ⟨_hw, _hrange⟩ := hasWords_blk_of_checkSegment (i := 16) (by decide) (ws := mmapFnWords) (R := VerifiedLibraries.mallocng_blk16_mmap.relocs) (by decide +kernel)
  have hsys := placed_syscallRet_perm_ok (P := mallocngBlockProg mmpl 16 msvc) (by intro pc; simp) rfl
  simp only [stackFrame, show (64 : Nat) = 8 * 8 by rfl, memRegion_cells _ 8 (by decide)]; cells_unfold
  wp_init x s0; subst m0 tp
  wp_stp64_cl m1 hm1 hcl0 hcl1; wp_step; wp_step; wp_step
  wp_stp64_cl m2 hm2 hcl1 hcl2; wp_step; wp_step; wp_step; wp_step
  wp_if hhi
  · exfalso; rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat] at hhi; omega
  wp_stp64_cl m3 hm3 hcl2 hcl3; wp_steps
  refine step_svc_mmap_protNone_rawLen (rawLen := rawLen) MallocngMultiPlacement.svcValid
    (by wp_norm_lhs) (by simp [arm64_norm, *]) (by wp_close_fetch_cl) (by simp [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp [arm64_norm, *]) (by simpa [arm64_norm] using ‹(s0.readReg64 (Reg.gpr 1#5)).toNat = rawLen›) hpos ?_ ?_
  · intro mb hmb_ne0 hmb_al hmb_fit
    clear hcl0 hcl1 hcl2; wp_norm_mbase_pc; wp_step; wp_step; wp_step
    wp_if hccmn
    · wp_step; wp_step; wp_step; wp_step
      have hcl4 := hcl3.of_keepsFrozen (Memory.keepsFrozen_mapZero_protNone _ mb len)
      clear hcl3; wp_call hsys; clear hcl4
      have hmble : mb.toNat ≤ 2 ^ 64 - 4096 := by omega
      have _hmb_ne1 : mb ≠ BitVec.allOnes 64 := fun he => by
        rw [he] at hmb_fit; have : (BitVec.allOnes 64).toNat = 2 ^ 64 - 1 := (by decide); omega
      simp only [hmble, ↓reduceIte, MallocngProcPreserved] at *
      have hperm3 : m3.perm = s0.mem.perm := Eq.trans hm3 (Eq.trans hm2 hm1)
      have _hdelta : MallocngMappedDelta 1 len s0.mem _ := mappedDelta_one_step hperm3 (mappedDelta_mapZeroProtNone _ mb len) ‹_›
      have _hinReg : MmapNewInRegionFine mb len s0.mem _ := perm_mapZeroProtNone_inRegion_fine hperm3 ‹_›
      wp_done
    · exfalso; have ht := congrArg BitVec.toNat hccmn; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht; omega
  · intro hno R' hmR
    have hperm3 : m3.perm = s0.mem.perm := Eq.trans hm3 (Eq.trans hm2 hm1)
    exact Satisfies.pure_intro ⟨rfl, rfl, rfl, hperm3, mappedDelta_of_perm_eq hperm3, hno⟩ (Satisfies.drop_left hmR)

private theorem noOrphanMappings_slowPathC_fine {st st' : MallocngSt} {m : Nat} {mb : BitVec 64}
    {m0 m1 m2 m3 : Memory}
    (hAv0 : st.availMetaPages = []) (hPowGe2 : 2 ≤ 2 ^ (m + 1)) (hPowLe36 : 2 ^ (m + 1) ≤ 2 ^ 36)
    (hMbFit : mb.toNat + 4096 * 2 ^ (m + 1) ≤ 2 ^ 48)
    (hMa' : st'.metaAreas = appendMetaArea st.metaAreas (mb + 4096#64))
    (hGp' : st'.guardPages = st.guardPages ++ [mb])
    (hAv' : st'.availMetaPages = (List.range (2 ^ (m + 1) - 2)).map (fun i => ((mb + 4096#64) + 4096#64) + BitVec.ofNat 64 (4096 * i)))
    (hGs' : st'.groups = st.groups)
    (hD01 : MallocngMappedDelta 0 0 m0 m1)
    (hInReg : MmapNewInRegionFine mb (4096 * 2 ^ (m + 1)) m1 m2)
    (hD23 : MallocngMappedDelta 0 0 m2 m3) :
    MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') m0 m3 := by
  let ap := mb + 4096#64
  have hMapBase := (appendMetaArea_props st.metaAreas ap).1
  have hMapMaPair : st'.metaAreas.map (fun ma => (ma.base, 4096)) = st.metaAreas.map (fun ma => (ma.base, 4096)) ++ [(ap, 4096)] := by
    calc st'.metaAreas.map (fun ma => (ma.base, 4096)) = ((appendMetaArea st.metaAreas ap).map MetaAreaDesc.base).map (fun b => (b, 4096)) := by rw [hMa', List.map_map]; rfl
      _ = st.metaAreas.map (fun ma => (ma.base, 4096)) ++ [(ap, 4096)] := by rw [hMapBase, List.map_append, List.map_map]; rfl
  have hSubDyn : ∀ r ∈ dynamicRootRegions st, r ∈ dynamicRootRegions st' := fun r hr => by
    unfold dynamicRootRegions at hr ⊢
    rw [hAv0, List.map_nil, List.append_nil] at hr
    rw [hMapMaPair, hGp', List.map_append, hGs']
    rcases List.mem_append.mp hr with h12 | hRg
    · rcases List.mem_append.mp h12 with hMa | hGp
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hMa)))
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ hGp)))
    · exact List.mem_append_right _ hRg
  intro a hm3 hsrc
  rcases hsrc with hm0f | ⟨r, hr, haR⟩
  · have hm2 := mapped_mono_of_mappedDelta_zero hD23 a hm3
    rcases hInReg a hm2 with hm1 | haMb
    · rw [mapped_mono_of_mappedDelta_zero hD01 a hm1] at hm0f; cases hm0f
    · have hApNat : ap.toNat = mb.toNat + 4096 := by dsimp only [ap]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hAp4096Nat : (ap + 4096#64).toNat = mb.toNat + 8192 := by rw [BitVec.toNat_add, hApNat, BitVec.toNat_ofNat]; omega
      have haN := (inRegion_toNat (by omega)).mp haMb
      let q := (a.toNat - mb.toNat) / 4096
      have hqLt : q < 2 ^ (m + 1) := by dsimp only [q]; omega
      unfold MallocngInIntervals dynamicRootRegions
      rw [hMapMaPair, hGp', List.map_append]
      by_cases hq0 : q = 0
      · exact ⟨(mb, 4096), List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ (List.Mem.head _)))),
          (inRegion_toNat (b := mb) (n := 4096) (by omega)).mpr ⟨by omega, by dsimp only [q] at hq0; omega⟩⟩
      · by_cases hq1 : q = 1
        · exact ⟨(ap, 4096), List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _)))),
            (inRegion_toNat (b := ap) (n := 4096) (by omega)).mpr ⟨by dsimp only [q] at hq1; omega, by dsimp only [q] at hq1; omega⟩⟩
        · let p := (ap + 4096#64) + BitVec.ofNat 64 (4096 * (q - 2))
          have hpMem : p ∈ st'.availMetaPages := by rw [hAv']; exact List.mem_map_of_mem (List.mem_range.mpr (by omega))
          have hpN : p.toNat = mb.toNat + 4096 * q := by
            dsimp only [p]; rw [BitVec.toNat_add, hAp4096Nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
          exact ⟨(p, 4096), List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hpMem)),
            (inRegion_toNat (b := p) (n := 4096) (by omega)).mpr ⟨by omega, by omega⟩⟩
  · exact ⟨r, hSubDyn r hr, haR⟩

theorem sepWP_slowPathC_144_fine [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost maxGroups maxMetaAreas : Nat}
    {st : MallocngSt} {errnoVal : BitVec 32} {s0 s : State}
    (hWords : Blk07HasWords116 mallocngFaultSvcAmf) (hRange : Blk07Range116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hInflight : inflight ≤ 7) (hGroups : st.groups.length ≤ maxGroups)
    (hMeta0 : st.metaAreas.length ≤ maxMetaAreas) (hMetaStep : 1 + (7 + maxGroups) / 101 ≤ maxMetaAreas)
    (hPc : s.pc = mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 0 - 40#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true) (hTp0 : s0.tpidrEl0 = tp)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx) (hx24 : s.readReg64 .x24 = 4096#64)
    (hCs25 : Cs25Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta0 : MallocngMappedDelta 0 0 s0.mem s.mem)
    (hWf : MallocngWFInflight inflight maddrs.base brkStart s.brk liveCost peakCost st)
    (h1 : st.ctx.initDone = 1#32) (hNoFree : st.freeMetas = []) (hNoBump : st.bumpMetas = [])
    (hCnt0 : st.ctx.availMetaAreaCount = 0#64) (hBrkNeg1 : st.ctx.brk = -1#64) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          CtxCells maddrs.ctx st.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st))))
      (AllocMetaFinePost inflight γ tp brkStart liveCost peakCost maxMetaAreas st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (allocMetaFineByteBound maxMetaAreas) s0 sf⌝) := by
  have hMetaPos : 1 ≤ maxMetaAreas := by omega
  have hAv0 : st.availMetaPages = [] := by have h := hWf.guard_avail_wf.2.2.1; rw [hCnt0] at h; exact h
  obtain ⟨hmLe35, hLenGe, hLenLe48, hLenDvd, hLenBound⟩ :=
    metaAreas_mmap_bytes_le_fine hWf hInflight hNoFree hNoBump hAv0 hMeta0 hMetaPos
  let m := st.ctx.metaAllocShift.toNat; let len := 4096 * 2 ^ (m + 1)
  have hmDef : st.ctx.metaAllocShift.toNat = m := rfl; have hLenDef : 4096 * 2 ^ (m + 1) = len := rfl
  rw [hmDef] at hmLe35; rw [hmDef, hLenDef] at hLenGe hLenLe48 hLenDvd hLenBound
  have hPowGe2 : 2 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (n := 2) (i := 1) (by decide) (by omega)
  have hPowLe36 : 2 ^ (m + 1) ≤ 2 ^ 36 := Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
  let retMmap := mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 0 + 4#64)
  let P_rest := StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
    CtxCells maddrs.ctx st.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
    MappedSet st.masterDom (OwnedMappedByte st)
  refine SepWP.cut (mid := mbase 16)
    (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 16 ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 Reg.lr = retMmap ∧ s1.readReg64 .x0 = 0#64 ∧ (s1.readReg64 .x1).toNat = len ∧
      s1.readReg32 .x2 = 0#32 ∧ s1.readReg32 .x3 = 0x22#32 ∧ s1.readReg32 .x4 = BitVec.allOnes 32 ∧ s1.readReg64 .x5 = 0#64 ∧
      s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s1.readReg64 .x22 = BitVec.ofNat 64 (2 ^ (m + 1)) ∧
      s1.readReg64 .x23 = maddrs.ctx ∧ s1.readReg64 .x24 = 4096#64 ∧
      Cs25Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ P_rest))) hcl ?_) ?_)
  · dsimp only [P_rest, CtxCells, retMmap] at *
    simp only [BitVec.reduceSub] at hPc; wp_sym_steps
    have hx22Eq : (2#64 <<< (st.ctx.metaAllocShift.toNat % 64)) = BitVec.ofNat 64 (2 ^ (m + 1)) :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show st.ctx.metaAllocShift.toNat % 64 = m by omega, Nat.shiftLeft_eq, show 2 * 2 ^ m = 2 ^ (m + 1) by rw [Nat.pow_succ]; omega])
    have hx1Eq : (4096#64 * BitVec.ofNat 64 (2 ^ (m + 1))).toNat = len := by
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; dsimp [len]; omega
    simp only [hx22Eq, hx1Eq, show ∀ x y : BitVec 64, x + (y - x) = y from fun _ _ => by bv_arith] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25; wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hLr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx20_1, hx22_1, hx23_1, hx24_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    refine SepWP.weaken_pre hEnt1 ?_
    have hSt64 : ∀ {stx : State}, stx.sp = s0.sp - 80#64 → stackAt (s0.sp - 80#64) 64 = stackFrame stx 64 :=
      fun h => by rw [stackAt_eq_stackFrameAt (s0.sp - 80#64) 64 (by decide), stackFrameAt_eq_memRegion (s0.sp - 80#64) 64 (by decide)]; unfold stackFrame; rw [h]
    unfold StackFrameSlow; rw [hSt64 hSp1]
    have hSpA1 : s1.spAligned = true := by rw [State.spAligned, hSp1]; exact spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
    have hTp1 : s1.tpidrEl0 = tp := hProc1.2.2.1.trans hTp0
    refine call_withCL_frame_auto (x := ())
      (placed_mmapProtNone_inRegion_ok_fine (P := mallocngBlockProg mmpl 7 msvc) tp errnoVal len (by omega) (by omega) (by intro pc; simp) rfl)
      hcl1 hPc1 hRun1 hSpA1 hLr1 (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by sep_frame) ?_
    · intro s2 hPc2 hRun2 hSp2 hCsCall hcl2
      apply SepWP.of_sepExists_left; intro mb
      rw [pageAlignUp_of_dvd hLenDvd, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hProcCall, hBrk2, hx0_2, hMbNe0, hMbNeNeg1, hMbAlign, hMbFit, hDCall, hInRegCall⟩
      rw [← hSt64 hSp1]
      refine SepWP.with_sat fun ⟨R_sat, hmSat⟩ => ?_
      obtain ⟨l1, l2, l3, l4, l5, _⟩ := hWf.ctx_lens
      have l5Len : st.ctx.seqPad.length = 7 := by rw [l5]; rfl
      have hmBatch' : s2.mem ⊨ (mb ↦ₙ List.replicate len 0#8) ∗ memMapped mb len ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st) ∗
          (stackAt (s0.sp - 80#64) 64 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ memRegion (s0.sp - 224#64) 80 ∗
            SavedRegs0 s0 ∗ SavedRegs21 s0 ∗ cells (s0.sp - 16#64) 2 ∗ StaticFrameA γ maddrs st.liveMap ∗
            ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗ R_sat) :=
        Satisfies.of_entails hmSat (by unfold SavedRegs0 SavedRegs21; rw [← ctx_toBytes_eq_cells _ _ l1 l2 l3 l4 l5Len]; sep_frame)
      have hDisjRoot := disjoint_protNone_batch (A := maddrs) hWf hAv0 hMbAlign hLenGe (by simpa [hmDef, hLenDef] using hMbFit) hmBatch'
      obtain ⟨hmProps, hWf', hGrpPost, hPnEq, hTailBm, hRw0Dom, hApBm, hMpEq⟩ :=
        slowPathC_trans hWf hInflight h1 hNoFree hNoBump hCnt0 hBrkNeg1 mb hMbNe0 hMbAlign (by simpa [hmDef, hLenDef] using hMbFit) (by simpa [hmDef, hLenDef] using hDisjRoot)
      let ap := mb + 4096#64
      let cnt' := BitVec.ofNat 64 (2 ^ (m + 1) - 2)
      let newAv := (List.range (2 ^ (m + 1) - 2)).map (fun i => (ap + 4096#64) + BitVec.ofNat 64 (4096 * i))
      let bv0 := writeBytesToMap st.byteVal mb (List.replicate len 0#8)
      let bv1 := if hne : st.metaAreas ≠ [] then writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) else bv0
      let st' : MallocngSt := { st with
        ctx := { st.ctx with availMeta := ap + 64#64, availMetaCount := 100#64, availMetaAreaCount := cnt', metaAllocShift := BitVec.ofNat 64 (m + 1), metaAreaHead := (match st.metaAreas with | [] => ap | hd :: _ => hd.base), metaAreaTail := ap, availMetaAreas := ap + 4096#64 },
        metaAreas := appendMetaArea st.metaAreas ap, mmapMetaAreas := st.mmapMetaAreas ++ [ap], guardPages := st.guardPages ++ [mb], mmapGuardPages := st.mmapGuardPages ++ [mb], availMetaPages := newAv, freeMetas := [],
        bumpMetas := (List.range 100).map (fun j => ({ base := ap, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)), reservedMetas := (ap + 24#64) :: st.reservedMetas, masterDom := st.masterDom ++ rangeAddrs mb len, byteVal := writeBytesToMap bv1 ap (metaHdrBytes st.ctx.secret 0#64) }
      have hApNat : ap.toNat = mb.toNat + 4096 := by dsimp [ap]; omega
      have hApAlign : 4096 ∣ ap.toNat := by rw [hApNat]; exact Nat.dvd_add hMbAlign (Nat.dvd_refl 4096)
      have hApFit : ap.toNat + 4096 ≤ 2 ^ 48 := by omega
      have hPn' : ((mb ↦ₙ List.replicate len 0#8) ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) =
          ((ap ↦ₙ List.replicate 4096 0#8) ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal) := hPnEq
      have hMp' : (memMapped mb len ∗ MappedSet st.masterDom (OwnedMappedByte st)) = MappedSet st'.masterDom (OwnedMappedByte st') := hMpEq
      refine SepWP.weaken_pre (Entails.trans
        (Q := ((ap ↦ₙ List.replicate 4096 0#8) ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal) ∗
          (MappedSet st'.masterDom (OwnedMappedByte st') ∗
            (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
              (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
                CtxCells maddrs.ctx st.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
                ByteMap st'.masterDom (OwnedRwByte st) bv0)))))
        (R := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
          (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
            (ap ↦ₙ List.replicate 4096 0#8) ∗ CtxCells maddrs.ctx st.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
            ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
            MappedSet st'.masterDom (OwnedMappedByte st'))))
        (by rw [← hPn', ← hMp', hRw0Dom]; unfold StackFrameSlow SavedRegs0 SavedRegs21; dsimp only [P_rest, st']; sep_frame)
        (by sep_frame)) ?_
      refine SepWP.cut_at_off (mbase 7) (reloc_call_off% blk07Relocs "mprotect" - 12#64)
        (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s3 =>
          s3.pc = mbase 7 + (reloc_call_off% blk07Relocs "mprotect" - 12#64) ∧
          s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧
          s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s3.readReg64 .x21 = ap ∧ s3.readReg64 .x24 = 4096#64 ∧
          Cs25Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = s.brk)
          (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
            (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
              (ap ↦ₙ List.replicate 4096 0#8) ∗
              CtxCells maddrs.ctx { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := ap } ∗
              ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
              ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
              MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl2 ?_) ?_)
      · dsimp only [retMmap] at hPc2
        have hx20_2 : s2.readReg64 .x20 = Obj.pageOf maddrs.ctx := hCsCall.2.1.trans hx20_1
        have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 (2 ^ (m + 1)) := hCsCall.2.2.2.1.trans hx22_1
        have hx23_2 : s2.readReg64 .x23 = maddrs.ctx := hCsCall.2.2.2.2.1.trans hx23_1
        have hx24_2 : s2.readReg64 .x24 = 4096#64 := hCsCall.2.2.2.2.2.1.trans hx24_1
        have hCs2 : Cs25Preserved s0 s2 := ⟨hCsCall.2.2.2.2.2.2.1.trans hCs1.1, hCsCall.2.2.2.2.2.2.2.1.trans hCs1.2.1,
          hCsCall.2.2.2.2.2.2.2.2.1.trans hCs1.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.1.trans hCs1.2.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.2.2.trans hCs1.2.2.2.2⟩
        have hProc2 : MallocngProcPreserved s0 s2 := procPreserved_trans hProc1 hProcCall
        have hMbAdd1 : (mb + 1#64 == 0#64) = false := beq_false_of_ne fun hEq => hMbNeNeg1
          (BitVec.eq_of_toNat_eq (by have h := congrArg BitVec.toNat hEq; rw [BitVec.toNat_add] at h; simp at h ⊢; omega))
        have hApMask : ((mb + 4096#64) &&& 4095#64 == 0#64) = true := beq_iff_eq.mpr (and_4095_eq_zero_of_dvd hApAlign)
        have hCntAdd : (BitVec.ofNat 64 (2 ^ (m + 1)) - 1#64) * 1#64 = cnt' + 1#64 :=
          BitVec.eq_of_toNat_eq (by rw [BitVec.mul_one, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; simp; omega), BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; dsimp [cnt']; rw [BitVec.toNat_ofNat]; omega)
        have hShiftAdd : st.ctx.metaAllocShift + 1#64 = BitVec.ofNat 64 (m + 1) :=
          BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, hmDef]; simp)
        dsimp only [CtxCells, ctxMiddleBytes, st']; conv => arg 2; simp only [BitVec.reduceSub]
        wp_sym_steps; simp only [hCntAdd, hShiftAdd, ap] at *
        obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs2
        rw [← hBrk1, ← hBrk2]; wp_done
      · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx20_3, hx21_3, hx24_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
        have hD01 : MallocngMappedDelta 0 0 s0.mem s1.mem :=
          MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)
        have hNoOrph3 : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem s3.mem :=
          noOrphanMappings_slowPathC_fine hAv0 hPowGe2 hPowLe36 hMbFit rfl rfl rfl rfl hD01 hInRegCall hD3
        have hDTot : MallocngMappedDelta 1 (allocMetaFineByteBound maxMetaAreas - 4096) s0.mem s3.mem := by
          refine MallocngMappedDelta.mono ?_ ?_ (MallocngMappedDelta.trans (MallocngMappedDelta.trans hD01 hDCall) hD3)
          all_goals omega
        exact SepWP.weaken_pre hEnt3 (sepWP_mprotect_224_fine hWords hRange hcl3 hMetaPos
          hPc3 hRun3 hSp3 hSp0 hTp0 hx20_3 hx21_3 hx24_3 hApAlign hApFit hCs3 hProc3
          (appendMetaArea_len_le_fine ap hWf hInflight hNoFree hNoBump hGroups hMetaStep) hNoOrph3 hDTot
          (metaAreas_ctx_eqs hWf rfl rfl rfl rfl rfl) hTailBm (fun hNil => dite_eq_right_iff.mpr fun h => False.elim (h hNil)) hApBm hmProps
          (hBrk3 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
    · intro R' sf _ hSatOom
      have hDrop := Satisfies.drop_mid hSatOom
      rw [satisfies_pure_sepConj] at hDrop ⊢
      obtain ⟨hFsEq, hTrEq, hSigEq, _, hDMmap, hNoGap⟩ := hDrop.1
      refine ⟨MallocngPlacedOomCond.of_delta (hFsEq.trans hProc1.1) (hTrEq.trans hProc1.2.1)
        (hSigEq.trans hProc1.2.2.2.2.2.2) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) hDMmap)
        (by omega) (by omega)
        (fun hSan => ⟨len, by dsimp [PAGE_SIZE]; omega, Nat.mod_eq_zero_of_dvd hLenDvd, by omega, by rw [← pageAlignUp_of_dvd hLenDvd]; exact hNoGap hSan⟩), hDrop.2⟩

theorem sepWP_fastPath1_028_fine [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost maxMetaAreas : Nat}
    {st : MallocngSt} {fm0 : FreeMetaDesc} {rest : List FreeMetaDesc} {errnoVal : BitVec 32} {s0 s : State} {oom : State → SepProp}
    (_hWords0 : Blk07HasWords0 mallocngFaultSvcAmf)
    (hWords : Blk07HasWords116 mallocngFaultSvcAmf)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hMeta0 : st.metaAreas.length ≤ maxMetaAreas)
    (hPc : s.pc = mbase 7 + (words_insn_off% blk07Words "cbz" 0 + 16#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = maddrs.ctx) (hx19 : s.readReg64 .x19 = fm0.ptr)
    (hCs21 : Cs21Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta0 : MallocngMappedDelta 0 0 s0.mem s.mem)
    (hWf : MallocngWFInflight inflight maddrs.base brkStart s.brk liveCost peakCost st) (hFmEq : st.freeMetas = fm0 :: rest) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          CtxCells maddrs.ctx st.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st))))
      (AllocMetaFinePost inflight γ tp brkStart liveCost peakCost maxMetaAreas st s0) oom := by
  let R_inv := StackFrameOpen s0 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ StaticFrameA γ maddrs st.liveMap ∗
    ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)
  let epOff := words_ret_off% blk07Words - 16#64
  rcases rest with _ | ⟨fm1, _ | ⟨fm2, tl⟩⟩
  · obtain ⟨hLinks, hmProps, hWf', hGrpPost, hRwEx, hPnEq, hMpEq⟩ := fastPath1_singleton_trans hWf hFmEq
    let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := 0#64 }, freeMetas := [], reservedMetas := fm0.ptr :: st.reservedMetas }
    rw [hRwEx, freeMeta_toBytes_eq_cells fm0, hLinks.2.1, hLinks.2.2]
    refine SepWP.weaken_pre (P' := CtxCells maddrs.ctx st.ctx ∗ (fm0.ptr ↦₆₄ fm0.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm0.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ R_inv)
      (by dsimp only [R_inv]; sep_frame) ?_
    refine SepWP.cut_at_off (mbase 7) epOff (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + epOff ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 .x19 = fm0.ptr ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (CtxCells maddrs.ctx st'.ctx ∗ (fm0.ptr ↦₆₄ fm0.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm0.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ R_inv)) hcl ?_) ?_)
    · dsimp only [epOff, st', CtxCells, ctxMiddleBytes]; conv => arg 2; simp only [BitVec.reduceSub]
      wp_sym_steps; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      have hD0Tot : MallocngMappedDelta 0 0 s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)
      have hDTot : MallocngMappedDelta 1 (allocMetaFineByteBound maxMetaAreas) s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by omega) hD0Tot
      refine SepWP.weaken_pre (Entails.trans hEnt1 ?_)
        (sepWP_epilogue_278_fine (st' := st') (w0 := fm0.ptr) (w1 := fm0.ptr) (errnoVal := errnoVal) hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hCs1 hProc1
          hMeta0 (noOrphanMappings_of_same_ivs_delta_zero rfl hD0Tot) hDTot hmProps (hBrk1 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
      dsimp only [R_inv, st']; rw [← hPnEq, ← hMpEq]; sep_frame
  · obtain ⟨hLinks, hmProps, _, hWf', hGrpPost, hRwEx, hRwAbs, hPnEq, hMpEq⟩ := fastPath1_pair_trans hWf hFmEq
    let fm1' : FreeMetaDesc := { ptr := fm1.ptr, prev := fm1.ptr, next := fm1.ptr }
    let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := fm1.ptr }, freeMetas := [fm1'], reservedMetas := fm0.ptr :: st.reservedMetas, byteVal := writeBytesToMap st.byteVal fm1.ptr fm1'.toBytes }
    let R_mid := ByteMap st.masterDom (fun a => (OwnedRwByte st a ∧ ¬ InRegion fm0.ptr 40 a) ∧ ¬ InRegion fm1.ptr 40 a) st.byteVal
    have hSubNe : (fm0.ptr - fm1.ptr == 0#64) = false := beq_false_of_ne (fun h => hLinks.2.2.2 (by bv_omega))
    have hBeqNe : (fm0.ptr == fm1.ptr) = false := beq_false_of_ne hLinks.2.2.2
    rw [hRwEx, freeMeta_toBytes_eq_cells fm0, freeMeta_toBytes_eq_cells fm1, hLinks.2.1, hLinks.2.2.1]
    refine SepWP.weaken_pre (P' := CtxCells maddrs.ctx st.ctx ∗ (fm0.ptr ↦₆₄ fm1.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ (fm1.ptr ↦₆₄ fm1.prev) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.next) ∗
        ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ R_mid ∗ R_inv)
      (by dsimp only [R_inv, R_mid]; sep_frame) ?_
    refine SepWP.cut_at_off (mbase 7) epOff (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + epOff ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 .x19 = fm0.ptr ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (CtxCells maddrs.ctx st'.ctx ∗ (fm0.ptr ↦₆₄ fm1.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ ((fm1.ptr ↦₆₄ fm1.ptr) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) ∗ R_mid ∗ R_inv)) hcl ?_) ?_)
    · dsimp only [epOff, st', CtxCells, ctxMiddleBytes]; rw [hLinks.1]; conv => arg 2; simp only [BitVec.reduceSub]
      wp_sym_steps; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      have hD0Tot : MallocngMappedDelta 0 0 s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)
      have hDTot : MallocngMappedDelta 1 (allocMetaFineByteBound maxMetaAreas) s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by omega) hD0Tot
      have hPack1 : ((fm1.ptr ↦₆₄ fm1.ptr) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.ptr) ∗ ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) = (fm1.ptr ↦ₛ fm1'.toBytes) := (freeMeta_toBytes_eq_cells fm1').symm
      refine SepWP.weaken_pre (Entails.trans hEnt1 ?_)
        (sepWP_epilogue_278_fine (st' := st') (w0 := fm1.ptr) (w1 := fm1.ptr) (errnoVal := errnoVal) hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hCs1 hProc1
          hMeta0 (noOrphanMappings_of_same_ivs_delta_zero rfl hD0Tot) hDTot hmProps (hBrk1 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
      rw [hPack1, ← sepConj_assoc (fm1.ptr ↦ₛ fm1'.toBytes), hRwAbs]; dsimp only [R_inv, st']; rw [← hPnEq, ← hMpEq]; sep_frame
  · let mid := (fm2 :: tl).dropLast; let fmLast := (fm2 :: tl).getLast nofun
    have hFmEq3 : st.freeMetas = fm0 :: fm1 :: (mid ++ [fmLast]) := by rw [hFmEq]; exact congrArg (fm0 :: fm1 :: ·) (List.dropLast_concat_getLast (l := fm2 :: tl) nofun).symm
    obtain ⟨hLinks, hmProps, _, _, hWf', hGrpPost, hRwEx, hRwAbs, hPnEq, hMpEq⟩ := fastPath1_ge3_trans hWf hFmEq3
    let fm1' : FreeMetaDesc := { fm1 with prev := fmLast.ptr }; let fmLast' : FreeMetaDesc := { fmLast with next := fm1.ptr }
    let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := fm1.ptr }, freeMetas := fm1' :: (mid ++ [fmLast']), reservedMetas := fm0.ptr :: st.reservedMetas, byteVal := writeBytesToMap (writeBytesToMap st.byteVal fmLast.ptr fmLast'.toBytes) fm1.ptr fm1'.toBytes }
    let R_mid := ByteMap st.masterDom (fun a => ((OwnedRwByte st a ∧ ¬ InRegion fm0.ptr 40 a) ∧ ¬ InRegion fmLast.ptr 40 a) ∧ ¬ InRegion fm1.ptr 40 a) st.byteVal
    have hSubNe : (fm0.ptr - fm1.ptr == 0#64) = false := beq_false_of_ne (fun h => hLinks.2.2.2 (by bv_omega))
    have hBeqNe : (fm0.ptr == fm1.ptr) = false := beq_false_of_ne hLinks.2.2.2
    rw [hRwEx, freeMeta_toBytes_eq_cells fm0, freeMeta_toBytes_eq_cells fmLast, freeMeta_toBytes_eq_cells fm1, hLinks.2.1, hLinks.2.2.1]
    refine SepWP.weaken_pre (P' := CtxCells maddrs.ctx st.ctx ∗ (fm0.ptr ↦₆₄ fmLast.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ (fmLast.ptr ↦₆₄ fmLast.prev) ∗ ((fmLast.ptr + 8#64) ↦₆₄ fmLast.next) ∗
        ((fmLast.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ (fm1.ptr ↦₆₄ fm1.prev) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.next) ∗
        ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ R_mid ∗ R_inv)
      (by dsimp only [R_inv, R_mid]; sep_frame) ?_
    refine SepWP.cut_at_off (mbase 7) epOff (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + epOff ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 .x19 = fm0.ptr ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (CtxCells maddrs.ctx st'.ctx ∗ (fm0.ptr ↦₆₄ fmLast.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ ((fm1.ptr ↦₆₄ fmLast.ptr) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.next) ∗
        ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) ∗ (((fmLast.ptr ↦₆₄ fmLast.prev) ∗ ((fmLast.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fmLast.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) ∗ R_mid) ∗ R_inv)) hcl ?_) ?_)
    · dsimp only [epOff, st', CtxCells, ctxMiddleBytes]; rw [hLinks.1]; conv => arg 2; simp only [BitVec.reduceSub]
      wp_sym_steps; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      have hD0Tot : MallocngMappedDelta 0 0 s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)
      have hDTot : MallocngMappedDelta 1 (allocMetaFineByteBound maxMetaAreas) s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by omega) hD0Tot
      have hPack1 : ((fm1.ptr ↦₆₄ fmLast.ptr) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.next) ∗ ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) = (fm1.ptr ↦ₛ fm1'.toBytes) := (freeMeta_toBytes_eq_cells fm1').symm
      have hPackL : ((fmLast.ptr ↦₆₄ fmLast.prev) ∗ ((fmLast.ptr + 8#64) ↦₆₄ fm1.ptr) ∗ ((fmLast.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) = (fmLast.ptr ↦ₛ fmLast'.toBytes) := (freeMeta_toBytes_eq_cells fmLast').symm
      refine SepWP.weaken_pre (Entails.trans hEnt1 ?_)
        (sepWP_epilogue_278_fine (st' := st') (w0 := fmLast.ptr) (w1 := fm1.ptr) (errnoVal := errnoVal) hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hCs1 hProc1
          hMeta0 (noOrphanMappings_of_same_ivs_delta_zero rfl hD0Tot) hDTot hmProps (hBrk1 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
      rw [hPack1, hPackL, ← sepConj_assoc (fm1.ptr ↦ₛ fm1'.toBytes), hRwAbs]; dsimp only [R_inv, st']; rw [← hPnEq, ← hMpEq]; sep_frame

end LibsignalBinary.Heap.Fine
