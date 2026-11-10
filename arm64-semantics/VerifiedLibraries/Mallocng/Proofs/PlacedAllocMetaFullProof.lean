/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplHelpers2
import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullStage2

/-!
# Verification of Full Placed `__malloc_alloc_meta`

Proves `placed_allocMeta_full_ok` (`blk07` on `mallocngBlockProg mmpl 7 msvc`) and its cross-block
lift `call_placed_allocMeta_full`, establishing `MallocngNoOrphanMappings` and the `metaAreas`
length bound across `brk`-growth slow paths, lazy initialization, and post-init dispatch.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.AllocMetaFullH

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

private theorem evalInst_svc0_execBrk [MallocngMultiPlacement] {s : State} (hx8 : s.readReg64 .x8 = 214#64) :
    (mallocngBlockProg mmpl 7 msvc).evalInst (.system false 0#16) s = execBrk s := by
  have hAlloc : Syscall.alloc s = execBrk s := by simp [Syscall.alloc, Syscall.dispatch, Syscall.allocTable, hx8]
  have hEq : (mallocngBlockProg mmpl 7 msvc).svc s = Syscall.alloc s := ((MallocngMultiPlacement.svcValid s).1 hx8).trans hAlloc.symm
  rw [Program.evalInst_svc0]
  exact (show evalSvc (mallocngBlockProg mmpl 7 msvc).svc s = evalSvc Syscall.alloc s by unfold evalSvc; rw [hEq]).trans ((evalSvc_alloc s).trans hAlloc)

private theorem post_brk_state {s0 s1 : State} (s2 : State) (pc' v : BitVec 64)
    (hRun1 : s1.status = .Running) (hSp1 : s1.sp = s0.sp - 80#64) (hCs1 : Cs25Preserved s0 s1) (hProc1 : MallocngProcPreserved s0 s1)
    (hEq : s2.pc = pc' ∧ s2.status = s1.status ∧ s2.sp = s1.sp ∧ s2.regs = (s1.writeReg64 .x0 v).regs ∧
      s2.vregs = s1.vregs ∧ s2.fs = s1.fs ∧ s2.trace = s1.trace ∧ s2.tpidrEl0 = s1.tpidrEl0 ∧
      s2.brkStart = s1.brkStart ∧ s2.oracle = s1.oracle ∧ s2.symtab = s1.symtab ∧ s2.sigActions = s1.sigActions) :
    s2.pc = pc' ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧ s2.readReg64 .x0 = v ∧
    (∀ n : BitVec 5, n ≠ 0#5 → n ≠ 31#5 → s2.readReg64 (.gpr n) = s1.readReg64 (.gpr n)) ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 := by
  obtain ⟨hpc, hst, hsp, hrg, hvr, hfs, htr, htp, hbs, hor, hsy, hsig⟩ := hEq
  have hGpr : ∀ n : BitVec 5, n ≠ 0#5 → n ≠ 31#5 → s2.readReg64 (.gpr n) = s1.readReg64 (.gpr n) := fun n hn0 hn31 =>
    (by simp [State.readReg64, hn31, hrg] : s2.readReg64 (.gpr n) = (s1.writeReg64 .x0 v).readReg64 (.gpr n)).trans
      (State.readReg64_writeReg64_gpr_ne s1 .x0 n v (by simp [Reg.isGprIdx, beq_eq_false_iff_ne.mpr hn0.symm]) (beq_eq_false_iff_ne.mpr hn31))
  have hx0 : s2.readReg64 .x0 = v :=
    (by simp [State.readReg64, hrg] : s2.readReg64 .x0 = (s1.writeReg64 .x0 v).readReg64 .x0).trans (State.readReg64_writeReg64_gpr_same s1 .x0 0#5 v rfl rfl)
  exact ⟨hpc, hst.trans hRun1, hsp.trans hSp1, hx0, hGpr,
    ⟨(hGpr 25#5 nofun nofun).trans hCs1.1, (hGpr 26#5 nofun nofun).trans hCs1.2.1,
     (hGpr 27#5 nofun nofun).trans hCs1.2.2.1, (hGpr 28#5 nofun nofun).trans hCs1.2.2.2.1, (by simp [calleeSavedVRegs, hvr] : calleeSavedVRegs s2 = calleeSavedVRegs s1).trans hCs1.2.2.2.2⟩,
    ⟨hfs.trans hProc1.1, htr.trans hProc1.2.1, htp.trans hProc1.2.2.1, hbs.trans hProc1.2.2.2.1,
     hor.trans hProc1.2.2.2.2.1, hsy.trans hProc1.2.2.2.2.2.1, hsig.trans hProc1.2.2.2.2.2.2⟩⟩

private theorem post_brk_grow_state {s0 s1 : State} {m' : Memory} {phys' : Nat} {fn off pc' newBrk : BitVec 64}
    (hPcEq : fn + off + 4#64 = pc') (hRun1 : s1.status = .Running) (hSp1 : s1.sp = s0.sp - 80#64) (hCs1 : Cs25Preserved s0 s1) (hProc1 : MallocngProcPreserved s0 s1) :
    let s2 := ((((s1.setBrk newBrk).setMem m').setPhysMemAvail phys').writeReg64 .x0 newBrk).setPC (fn + off + 4#64)
    s2.pc = pc' ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧ s2.readReg64 .x0 = newBrk ∧
    (∀ n : BitVec 5, n ≠ 0#5 → n ≠ 31#5 → s2.readReg64 (.gpr n) = s1.readReg64 (.gpr n)) ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 ∧ s2.brk = newBrk ∧ s2.mem = m' := by
  intro s2; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := post_brk_state s2 pc' newBrk hRun1 hSp1 hCs1 hProc1 ⟨hPcEq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, rfl, rfl⟩

private theorem post_brk_fail_state {s0 s1 : State} {fn off pc' : BitVec 64}
    (hPcEq : fn + off + 4#64 = pc') (hRun1 : s1.status = .Running) (hSp1 : s1.sp = s0.sp - 80#64) (hCs1 : Cs25Preserved s0 s1) (hProc1 : MallocngProcPreserved s0 s1) :
    let s2 := ((s1.writeReg64 .x0 s1.brk).setPC (fn + off + 4#64))
    s2.pc = pc' ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧ s2.readReg64 .x0 = s1.brk ∧
    (∀ n : BitVec 5, n ≠ 0#5 → n ≠ 31#5 → s2.readReg64 (.gpr n) = s1.readReg64 (.gpr n)) ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 ∧ s2.brk = s1.brk ∧ s2.mem = s1.mem := by
  intro s2; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := post_brk_state s2 pc' s1.brk hRun1 hSp1 hCs1 hProc1 ⟨hPcEq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, rfl, rfl⟩

private theorem post_brk_query_state {s0 s1 : State} {fn off pc' : BitVec 64}
    (hPcEq : fn + off + 4#64 = pc') (hRun1 : s1.status = .Running) (hSp1 : s1.sp = s0.sp - 80#64) (hCs1 : Cs25Preserved s0 s1) (hProc1 : MallocngProcPreserved s0 s1) :
    let s2 := ((s1.writeReg64 .x0 s1.brk).setPC (fn + off + 4#64))
    s2.pc = pc' ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧ s2.readReg64 .x0 = s1.brk ∧
    (∀ n : BitVec 5, n ≠ 0#5 → n ≠ 31#5 → s2.readReg64 (.gpr n) = s1.readReg64 (.gpr n)) ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 ∧ s2.brk = s1.brk ∧ s2.mem = s1.mem := by
  intro s2; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := post_brk_state s2 pc' s1.brk hRun1 hSp1 hCs1 hProc1 ⟨hPcEq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, rfl, rfl⟩

private theorem appendMetaArea_map_pair {mas mas' : List MetaAreaDesc} {ap : BitVec 64} (hMa' : mas' = appendMetaArea mas ap) :
    mas'.map (fun ma => (ma.base, 4096)) = mas.map (fun ma => (ma.base, 4096)) ++ [(ap, 4096)] := by
  calc mas'.map (fun ma => (ma.base, 4096)) = ((appendMetaArea mas ap).map MetaAreaDesc.base).map (fun b => (b, 4096)) := by rw [hMa', List.map_map]; rfl
    _ = mas.map (fun ma => (ma.base, 4096)) ++ [(ap, 4096)] := by rw [(appendMetaArea_props mas ap).1, List.map_append, List.map_map]; rfl

private theorem noOrphanMappings_slowPathA {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st st' : MallocngSt} {m0 m2 : Memory}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (hCntNe : st.ctx.availMetaAreaCount ≠ 0#64)
    (hMa' : st'.metaAreas = appendMetaArea st.metaAreas st.ctx.availMetaAreas) (hGp' : st'.guardPages = st.guardPages)
    (hAv' : st'.availMetaPages = (List.range (st.ctx.availMetaAreaCount - 1#64).toNat).map (fun i => (st.ctx.availMetaAreas + 4096#64) + BitVec.ofNat 64 (4096 * i)))
    (hGs' : st'.groups = st.groups) (hD02 : MallocngMappedDelta 0 0 m0 m2) :
    MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') m0 m2 := by
  let ap := st.ctx.availMetaAreas; let cnt' := st.ctx.availMetaAreaCount - 1#64
  have hCntPos : 0 < st.ctx.availMetaAreaCount.toNat := Nat.pos_of_ne_zero fun h0 => hCntNe (BitVec.eq_of_toNat_eq h0)
  have hCntEq : st.ctx.availMetaAreaCount.toNat = cnt'.toNat + 1 := by
    dsimp only [cnt']; rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; exact hCntPos), BitVec.toNat_ofNat]; omega
  have hAvEq : st.availMetaPages = ap :: st'.availMetaPages := by
    rw [hwf.guard_avail_wf.2.2.1, hCntEq, hAv', List.range_succ_eq_map, List.map_cons, Nat.mul_zero, BitVec.add_zero, List.map_map]
    exact congrArg (List.cons ap) (List.map_congr_left fun i _ => by dsimp only [Function.comp]; rw [Nat.mul_succ, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 (4096 * i)), ← BitVec.add_assoc])
  intro a hm2 hsrc; rcases hsrc with hm0f | ⟨r, hr, haR⟩
  · rw [mapped_mono_of_mappedDelta_zero hD02 a hm2] at hm0f; cases hm0f
  · refine ⟨r, ?_, haR⟩; unfold dynamicRootRegions at hr ⊢
    rw [hAvEq, List.map_cons] at hr; rw [appendMetaArea_map_pair hMa', hGp', hGs']
    rcases List.mem_append.mp hr with h123 | hRg
    · rcases List.mem_append.mp h123 with h12 | hAv
      · rcases List.mem_append.mp h12 with hMa | hGp
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hMa)))
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hGp))
      · rcases List.mem_cons.mp hAv with rfl | hRest
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _))))
        · exact List.mem_append_left _ (List.mem_append_right _ hRest)
    · exact List.mem_append_right _ hRg

private theorem noOrphanMappings_slowPathB2 {st st' : MallocngSt} {ap : BitVec 64} {m0 m1 m2 m3 : Memory}
    (hMa' : st'.metaAreas = appendMetaArea st.metaAreas ap) (hGp' : st'.guardPages = st.guardPages)
    (hAv' : st'.availMetaPages = st.availMetaPages) (hGs' : st'.groups = st.groups)
    (hD01 : MallocngMappedDelta 0 0 m0 m1) (hMem2 : m2 = m1.mapZero ap 4096) (hD23 : MallocngMappedDelta 0 0 m2 m3) :
    MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') m0 m3 := by
  intro a hm3 hsrc; rcases hsrc with hm0f | ⟨r, hr, haR⟩
  · have hm2 := mapped_mono_of_mappedDelta_zero hD23 a hm3
    rw [hMem2, Memory.perm_mapZero] at hm2; split at hm2
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      unfold MallocngInIntervals dynamicRootRegions; rw [appendMetaArea_map_pair hMa']
      exact ⟨(ap, 4096), List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _)))), hc.1⟩
    · rw [mapped_mono_of_mappedDelta_zero hD01 a hm2] at hm0f; cases hm0f
  · refine ⟨r, ?_, haR⟩; unfold dynamicRootRegions at hr ⊢; rw [appendMetaArea_map_pair hMa', hGp', hAv', hGs']
    rcases List.mem_append.mp hr with h123 | hRg
    · rcases List.mem_append.mp h123 with h12 | hAv
      · rcases List.mem_append.mp h12 with hMa | hGp
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hMa)))
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hGp))
      · exact List.mem_append_left _ (List.mem_append_right _ hAv)
    · exact List.mem_append_right _ hRg

private theorem noOrphanMappings_slowPathB1 {st st' : MallocngSt} {brkStart : BitVec 64} {m0 m3 m4 m7 : Memory}
    (hMa0 : st.metaAreas = []) (hGp0 : st.guardPages = []) (hAv0 : st.availMetaPages = []) (hGs0 : st.groups = [])
    (hBsFit8 : brkStart.toNat + 8192 ≤ 2 ^ 48)
    (hMa' : st'.metaAreas = [{ base := brkStart + 4096#64, next := 0#64 }]) (hGp' : st'.guardPages = [brkStart])
    (hD03 : MallocngMappedDelta 0 0 m0 m3) (hMem4 : m4 = m3.mapZero brkStart 8192) (hD47 : MallocngMappedDelta 0 0 m4 m7) :
    MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') m0 m7 := by
  let ap := brkStart + 4096#64
  have hApNat : ap.toNat = brkStart.toNat + 4096 := by dsimp only [ap]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  intro a hm7 hsrc; rcases hsrc with hm0f | ⟨r, hr, _⟩
  · have hm4 := mapped_mono_of_mappedDelta_zero hD47 a hm7
    rw [hMem4, Memory.perm_mapZero] at hm4; split at hm4
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have haN := (inRegion_toNat (by omega)).mp hc.1
      unfold MallocngInIntervals dynamicRootRegions; rw [hMa', hGp']; dsimp only [List.map]
      by_cases hLt : a.toNat < brkStart.toNat + 4096
      · exact ⟨(brkStart, 4096), List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _))),
          (inRegion_toNat (b := brkStart) (n := 4096) (by omega)).mpr ⟨haN.1, hLt⟩⟩
      · exact ⟨(ap, 4096), List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.Mem.head _))),
          (inRegion_toNat (b := ap) (n := 4096) (by omega)).mpr ⟨by omega, by omega⟩⟩
    · rw [mapped_mono_of_mappedDelta_zero hD03 a hm4] at hm0f; cases hm0f
  · unfold dynamicRootRegions at hr; simp [hMa0, hGp0, hAv0, hGs0] at hr

/-! ## Slow paths B2 / B1 and post-init dispatch -/

private theorem sepWP_slowPathB2_118 [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {st : MallocngSt} {errnoVal : BitVec 32} {s0 s : State}
    (hWordsSvc : Blk07HasWords116 msvc) (hRange : Blk07Range116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hInflight : inflight ≤ 7) (hCount : totalLiveCount st ≤ peakCount)
    (hPc : s.pc = mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 0 - 84#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hTp0 : s0.tpidrEl0 = tp) (hBs0 : s0.brkStart = brkStart)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx)
    (hx21 : s.readReg64 .x21 = s.brk) (hx24 : s.readReg64 .x24 = 4096#64)
    (hCs25 : Cs25Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta0 : MallocngMappedDelta 0 0 s0.mem s.mem)
    (hWf : MallocngWFInflight inflight maddrs.base brkStart s.brk liveCost peakCost st)
    (h1 : st.ctx.initDone = 1#32) (hNoFree : st.freeMetas = []) (hNoBump : st.bumpMetas = [])
    (hCnt0 : st.ctx.availMetaAreaCount = 0#64) (hBrkNe : st.ctx.brk ≠ -1#64) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          CtxCells maddrs.ctx st.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st))))
      (AllocMetaFullPost inflight γ tp brkStart liveCost peakCost peakCount st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (allocMetaPlacedByteBound peakCount) s0 sf⌝) := by
  have hWords : Blk07HasWords116 mallocngFaultSvcAmf := Program.hasWords_withSvc_amf hWordsSvc
  let P_all := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
    (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
      CtxCells maddrs.ctx st.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
      MappedSet st.masterDom (OwnedMappedByte st)))
  let svcOff := reloc_call_off% blk07Relocs "__mmap" 0 - 72#64
  refine SepWP.cut_at_off (mbase 7) svcOff (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
    s1.pc = mbase 7 + svcOff ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
    s1.readReg64 .x0 = s.brk + 4096#64 ∧ s1.readReg64 .x8 = 214#64 ∧ s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧
    s1.readReg64 .x21 = s.brk ∧ s1.readReg64 .x22 = s.brk + 4096#64 ∧ s1.readReg64 .x24 = 4096#64 ∧
    Cs25Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk) P_all) hcl ?_) ?_)
  · dsimp only [svcOff, P_all]; simp only [BitVec.reduceSub] at hPc; conv => arg 2; simp only [BitVec.reduceSub]
    wp_sym_steps; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25; wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx0_1, hx8_1, hx20_1, hx21_1, hx22_1, hx24_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    refine SepWP.weaken_pre hEnt1 (SepWP.with_sat fun ⟨R_sat, hmSat⟩ => ?_)
    have ⟨hBrkGe, _, hBrkMod, _, hBrkFit0⟩ := (hBrk1 ▸ hWf).brk_bounds
    let newBrk := s1.brk + 4096#64
    have hNewNat : newBrk.toNat = s1.brk.toNat + 4096 := by dsimp only [newBrk]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hLenEq : newBrk.toNat - s1.brk.toNat = 4096 := by omega
    have hx0_new : s1.readReg64 .x0 = newBrk := by dsimp only [newBrk]; rw [hBrk1]; exact hx0_1
    have hFetch : (mallocngBlockProg mmpl 7 msvc).fetch (mbase 7 + svcOff) = some (.system false 0#16) :=
      Program.fetch_of_hasWords_getElem_decode 44 3556769793#32 hWordsSvc (by dsimp only [svcOff]; simp only [BitVec.reduceSub]; bv_arith) rfl rfl
    refine SepWP.step_svc_brk_grow (newBrk := newBrk) hPc1 hRun1 hFetch hx0_new
      (fun h0 => by rw [h0] at hNewNat; simp at hNewNat) (by rw [hProc1.2.2.2.1, hBs0]; omega) (by omega)
      (Nat.dvd_of_mod_eq_zero hBrkMod) ⟨s1.brk.toNat / 4096 + 1, by omega⟩ (evalInst_svc0_execBrk hx8_1) ?_ ?_ ?_
    · intro m' hFit2 hCanMap hm' hDBrk
      have hmDom : s1.mem ⊨ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
          ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st) ∗
          (StackFrameSlow s0 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ StaticFrameA γ maddrs st.liveMap ∗
            ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ CtxCells maddrs.ctx st.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗ R_sat) :=
        Satisfies.of_entails hmSat (by dsimp only [P_all]; sep_frame)
      have hDisjRoot : ∀ r ∈ dynamicRootRegions st, DisjointRegions r.1 r.2 s1.brk 4096 :=
        disjoint_dynamicRootRegions_of_canMap (hBrk1 ▸ hWf) (hLenEq ▸ hCanMap) (Nat.dvd_of_mod_eq_zero hBrkMod) (by decide) (by omega) hmDom
      obtain ⟨_, hmProps, hWf', hGrpPost, hTailBm, hRw0Dom, hApBm, hPnEq, hMpEq⟩ :=
        slowPathB2_trans (hBrk1 ▸ hWf) hInflight h1 hNoFree hNoBump hBrkNe hFit2 hDisjRoot
      let bv0 := writeBytesToMap st.byteVal s1.brk (List.replicate 4096 0#8)
      let bv1 := if hne : st.metaAreas ≠ [] then writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret s1.brk) else bv0
      let st' : MallocngSt := { st with
        ctx := { st.ctx with availMeta := s1.brk + 64#64, availMetaCount := 100#64, availMetaAreaCount := 0#64, metaAreaHead := (match st.metaAreas with | [] => s1.brk | hd :: _ => hd.base), metaAreaTail := s1.brk, availMetaAreas := s1.brk + 4096#64, brk := s1.brk + 4096#64 },
        metaAreas := appendMetaArea st.metaAreas s1.brk, freeMetas := [], bumpMetas := (List.range 100).map (fun j => ({ base := s1.brk, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)), reservedMetas := (s1.brk + 24#64) :: st.reservedMetas, masterDom := st.masterDom ++ rangeAddrs s1.brk 4096, byteVal := writeBytesToMap bv1 s1.brk (metaHdrBytes st.ctx.secret 0#64) }
      rw [hLenEq]
      have hGrowSt := post_brk_grow_state (m' := m') (phys' := s1.physMemAvail - 4096) (newBrk := newBrk) (fn := mbase 7) (off := svcOff)
        (pc' := mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 0 - 68#64)) (by dsimp only [svcOff]; bv_arith) hRun1 hSp1 hCs1 hProc1
      generalize (((((s1.setBrk newBrk).setMem m').setPhysMemAvail (s1.physMemAvail - 4096)).writeReg64 .x0 newBrk).setPC (mbase 7 + svcOff + 4#64)) = s2 at hGrowSt ⊢
      obtain ⟨hPc2, hRun2, hSp2, hx0_2, hGpr2, hCs2, hProc2, hBrk2, hMem2⟩ := hGrowSt
      have hcl2 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem :=
        hMem2 ▸ hm' ▸ hcl1.of_keepsFrozen (Memory.keepsFrozen_mapZero s1.mem s1.brk _)
      have hx20_2 : s2.readReg64 .x20 = Obj.pageOf maddrs.ctx := (hGpr2 20#5 nofun nofun).trans hx20_1
      have hx21_2 : s2.readReg64 .x21 = s1.brk := (hGpr2 21#5 nofun nofun).trans (hx21_1.trans hBrk1.symm)
      have hx22_2 : s2.readReg64 .x22 = newBrk := (hGpr2 22#5 nofun nofun).trans (by dsimp only [newBrk]; rw [hBrk1]; exact hx22_1)
      have hx24_2 : s2.readReg64 .x24 = 4096#64 := (hGpr2 24#5 nofun nofun).trans hx24_1
      refine SepWP.cut_at_off (mbase 7) (words_ret_off% blk07Words + 24#64)
        (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s3 =>
          s3.pc = mbase 7 + (words_ret_off% blk07Words + 24#64) ∧
          s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧ s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s3.readReg64 .x21 = s1.brk ∧
          Cs25Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = newBrk)
          (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
            (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (s1.brk ↦ₛ List.replicate 4096 0#8) ∗
              CtxCells maddrs.ctx { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := st.ctx.availMetaAreas } ∗
              ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
              ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
              MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl2 ?_) ?_)
      · have hPnEq' : ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal = ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal := hPnEq
        have hMpEq' : MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) := hMpEq
        have hMidB2 : ctxMiddleBytes { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := st.ctx.availMetaAreas } = ctxMiddleBytes st.ctx := rfl
        have hEqNew : (newBrk - newBrk == 0#64) = true := by simp
        dsimp only [P_all, CtxCells]; rw [hRw0Dom, ← hPnEq', ← hMpEq', hMidB2]; dsimp only [st']
        rw [show s1.brk + 4096#64 = newBrk from rfl]; simp only [BitVec.reduceSub] at hPc2
        conv => arg 2; simp only [BitVec.reduceAdd]
        wp_sym_steps; simp only [hEqNew, BitVec.reduceAdd] at *
        obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs2; wp_done
      · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx20_3, hx21_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
        have hD01 : MallocngMappedDelta 0 0 s0.mem s1.mem :=
          MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)
        have hNoOrph3 : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem s3.mem :=
          noOrphanMappings_slowPathB2 rfl rfl rfl rfl hD01 (by rw [hMem2, hm', hLenEq]) hD3
        have hDTot : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem s3.mem := by
          refine MallocngMappedDelta.mono ?_ ?_ (MallocngMappedDelta.trans (MallocngMappedDelta.trans hD01 (hLenEq ▸ hDBrk)) (hMem2 ▸ hD3))
          · decide
          · unfold allocMetaPlacedByteBound; omega
        exact SepWP.weaken_pre hEnt3 (sepWP_activate_2a0 hWords hRange hcl3 hPc3 hRun3 hSp3 hSp0 hx20_3 hx21_3 hCs3 hProc3
          (appendMetaArea_len_le_max s1.brk (hBrk1 ▸ hWf) hInflight hNoFree hNoBump hCount) hNoOrph3 hDTot
          (metaAreas_ctx_eqs (hBrk1 ▸ hWf) rfl rfl rfl rfl rfl) hTailBm (fun hNil => dite_eq_right_iff.mpr fun h => False.elim (h hNil)) hApBm hmProps
          (hBrk3 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
    · obtain ⟨hWfFail, hRwFail, hPnFail, hMpFail⟩ := brk_fail_wf (hBrk1 ▸ hWf) h1
      let stFail : MallocngSt := { st with ctx := { st.ctx with brk := -1#64 } }
      have hFailSt := post_brk_fail_state (fn := mbase 7) (off := svcOff)
        (pc' := mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 0 - 68#64)) (by dsimp only [svcOff]; bv_arith) hRun1 hSp1 hCs1 hProc1
      generalize ((s1.writeReg64 .x0 s1.brk).setPC (mbase 7 + svcOff + 4#64)) = s2 at hFailSt ⊢
      obtain ⟨hPc2, hRun2, hSp2, hx0_2, hGpr2, hCs2, hProc2, hBrk2, hMem2⟩ := hFailSt
      have hcl2 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem := hMem2 ▸ hcl1
      have hx20_2 : s2.readReg64 .x20 = Obj.pageOf maddrs.ctx := (hGpr2 20#5 nofun nofun).trans hx20_1
      have hx22_2 : s2.readReg64 .x22 = s1.brk + 4096#64 := (hGpr2 22#5 nofun nofun).trans (by rw [hBrk1]; exact hx22_1)
      have hx24_2 : s2.readReg64 .x24 = 4096#64 := (hGpr2 24#5 nofun nofun).trans hx24_1
      refine SepWP.cut_at_off (mbase 7) (reloc_call_off% blk07Relocs "__mmap" 0 - 40#64)
        (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s3 =>
          s3.pc = mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 0 - 40#64) ∧
          s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧ s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s3.readReg64 .x24 = 4096#64 ∧
          Cs25Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = s1.brk)
          (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
            (StaticFrameA γ maddrs stFail.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
              CtxCells maddrs.ctx stFail.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ stFail.auxvPtr) ∗ MallocngAuxvState γ stFail.auxvPtr stFail.auxvSnap ∗
              ByteMap stFail.masterDom (OwnedRwByte stFail) stFail.byteVal ∗ ProtNoneByteMap stFail.masterDom (OwnedProtNoneByte stFail) stFail.byteVal ∗
              MappedSet stFail.masterDom (OwnedMappedByte stFail))))) hcl2 ?_) ?_)
      · have hMidFailB2 : ctxMiddleBytes stFail.ctx = ctxMiddleBytes st.ctx := rfl
        rw [hRwFail, hPnFail, hMpFail]; dsimp only [P_all, CtxCells]; rw [hMidFailB2]; dsimp only [stFail]; rw [hCnt0]
        have hNe4096 : ((s1.brk + 4096#64) - s1.brk == 0#64) = false := by rw [show (s1.brk + 4096#64) - s1.brk = 4096#64 by bv_arith]; decide
        simp only [BitVec.reduceSub] at hPc2; conv => arg 2; simp only [BitVec.reduceSub]
        wp_sym_steps; simp only [hNe4096, BitVec.reduceNeg] at *
        obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs2; wp_done
      · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx20_3, hx24_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
        have hD0Tot : MallocngMappedDelta 0 0 s0.mem s3.mem :=
          MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) (hMem2 ▸ hD3))
        exact SepWP.mono (SepWP.weaken_pre hEnt3 (sepWP_slowPathC_144 hWords hRange hcl3 hInflight hCount
          hPc3 hRun3 hSp3 hSp0 hTp0 hx20_3 hx24_3 hCs3 hProc3 hD0Tot (hBrk3 ▸ hWfFail) h1 hNoFree hNoBump hCnt0 rfl))
          fun _ _ _ _ => allocMetaFullPost_congr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro hPhysLt R' hmR
      exact Satisfies.pure_intro
        (MallocngPlacedOomCond.of_delta hProc1.1 hProc1.2.1 hProc1.2.2.2.2.2.2
          (MallocngMappedDelta.trans hDelta0 hD1) (by decide)
          (by unfold allocMetaPlacedByteBound; omega)
          fun _ => ⟨4096, by decide, by decide, by unfold allocMetaPlacedByteBound; omega, Or.inr (by dsimp [State.setStatus]; omega)⟩)
        (Satisfies.drop_left hmR)

set_option maxHeartbeats 400000 in
private theorem sepWP_slowPathB1_1a8 [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {st : MallocngSt} {sec : BitVec 64} {errnoVal : BitVec 32} {s0 s : State}
    (hWordsSvc : Blk07HasWords116 msvc) (hRange : Blk07Range116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hInflight : inflight ≤ 7) (hCount : totalLiveCount st ≤ peakCount)
    (hPc : s.pc = mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 1 - 80#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hTp0 : s0.tpidrEl0 = tp) (hBs0 : s0.brkStart = brkStart) (hx1 : s.readReg64 .x1 = maddrs.ctx)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx) (hx24 : s.readReg64 .x24 = 4096#64)
    (hCs25 : Cs25Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta0 : MallocngMappedDelta 0 0 s0.mem s.mem)
    (hWf : MallocngWFInflight inflight maddrs.base brkStart s.brk liveCost peakCost st) (h0 : st.ctx.initDone = 0#32) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          CtxCells maddrs.ctx { st.ctx with secret := sec, initDone := 1#32 } ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st))))
      (AllocMetaFullPost inflight γ tp brkStart liveCost peakCost peakCount st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (allocMetaPlacedByteBound peakCount) s0 sf⌝) := by
  have hWords : Blk07HasWords116 mallocngFaultSvcAmf := Program.hasWords_withSvc_amf hWordsSvc
  obtain ⟨_, hMa0, _, hGp0, _, hAv0, _, _, _, hGs0, _, hBrkEq⟩ := hWf.initZero_wf h0
  have ⟨hBsGe, hBsMod, _, _, hBsFit0⟩ := hWf.brk_bounds
  let P_rest (c : CtxFields) := StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
    CtxCells maddrs.ctx c ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
    MappedSet st.masterDom (OwnedMappedByte st)
  let svcOff1 := reloc_call_off% blk07Relocs "__mmap" 1 - 72#64
  let svcOff2 := reloc_call_off% blk07Relocs "__mmap" 1 - 40#64
  refine SepWP.cut_at_off (mbase 7) svcOff1 (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
    s1.pc = mbase 7 + svcOff1 ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
    s1.readReg64 .x0 = 0#64 ∧ s1.readReg64 .x1 = maddrs.ctx ∧ s1.readReg64 .x8 = 214#64 ∧
    s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s1.readReg64 .x24 = 4096#64 ∧
    Cs25Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
    (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ P_rest { st.ctx with secret := sec, initDone := 1#32 }))) hcl ?_) ?_)
  · dsimp only [svcOff1, P_rest, CtxCells]; simp only [BitVec.reduceSub] at hPc; conv => arg 2; simp only [BitVec.reduceSub]
    wp_sym_steps; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25; wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx0_1, hx1_1, hx8_1, hx20_1, hx24_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    have hBrk1' : s1.brk = brkStart := hBrk1.trans hBrkEq
    have hFetch1 : (mallocngBlockProg mmpl 7 msvc).fetch (mbase 7 + svcOff1) = some (.system false 0#16) :=
      Program.fetch_of_hasWords_getElem_decode 79 3556769793#32 hWordsSvc (by dsimp only [svcOff1]; simp only [BitVec.reduceSub]; bv_arith) rfl rfl
    refine SepWP.weaken_pre hEnt1 (SepWP.step_svc_brk_query hPc1 hRun1 hFetch1 hx0_1 (evalInst_svc0_execBrk hx8_1) ?_)
    have hQSt := post_brk_query_state (fn := mbase 7) (off := svcOff1)
      (pc' := mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 1 - 68#64)) (by dsimp only [svcOff1]; bv_arith) hRun1 hSp1 hCs1 hProc1
    generalize ((s1.writeReg64 .x0 s1.brk).setPC (mbase 7 + svcOff1 + 4#64)) = s2 at hQSt ⊢
    obtain ⟨hPc2, hRun2, hSp2, hx0_2, hGpr2, hCs2, hProc2, hBrk2, hMem2⟩ := hQSt
    have hcl2 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem := hMem2 ▸ hcl1
    have hx0_2' : s2.readReg64 .x0 = brkStart := hx0_2.trans hBrk1'
    have hx1_2 : s2.readReg64 .x1 = maddrs.ctx := (hGpr2 1#5 nofun nofun).trans hx1_1
    have hx8_2 : s2.readReg64 .x8 = 214#64 := (hGpr2 8#5 nofun nofun).trans hx8_1
    have hx20_2 : s2.readReg64 .x20 = Obj.pageOf maddrs.ctx := (hGpr2 20#5 nofun nofun).trans hx20_1
    have hx24_2 : s2.readReg64 .x24 = 4096#64 := (hGpr2 24#5 nofun nofun).trans hx24_1
    have hNegAnd : (0#64 - brkStart) &&& 4095#64 = 0#64 := by
      rw [BitVec.zero_sub]; exact and_4095_eq_zero_of_dvd ⟨(2 ^ 64 - brkStart.toNat) / 4096, by rw [BitVec.toNat_neg]; have := brkStart.isLt; omega⟩
    have hNegAnd' : (-brkStart) &&& 4095#64 = 0#64 := by simpa only [BitVec.zero_sub] using hNegAnd
    refine SepWP.cut_at_off (mbase 7) svcOff2 (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s3 =>
      s3.pc = mbase 7 + svcOff2 ∧ s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧
      s3.readReg64 .x0 = brkStart + 8192#64 ∧ s3.readReg64 .x1 = maddrs.ctx ∧ s3.readReg64 .x8 = 214#64 ∧
      s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s3.readReg64 .x22 = brkStart + 8192#64 ∧ s3.readReg64 .x24 = 4096#64 ∧
      Cs25Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = s2.brk)
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ P_rest { st.ctx with secret := sec, initDone := 1#32, brk := brkStart }))) hcl2 ?_) ?_)
    · have hMidBrk : ctxMiddleBytes { st.ctx with secret := sec, initDone := 1#32, brk := brkStart } = ctxMiddleBytes { st.ctx with secret := sec, initDone := 1#32 } := rfl
      dsimp only [svcOff2, P_rest, CtxCells]; rw [hMidBrk]; simp only [BitVec.reduceSub] at hPc2; conv => arg 2; simp only [BitVec.reduceSub]
      wp_sym_steps; simp only [hNegAnd, hNegAnd', BitVec.zero_add] at *
      obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs2; wp_done
    · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx0_3, hx1_3, hx8_3, hx20_3, hx22_3, hx24_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
      have hBrk3' : s3.brk = brkStart := hBrk3.trans (hBrk2.trans hBrk1')
      let newBrk := brkStart + 8192#64
      have hBsFit : brkStart.toNat ≤ 2 ^ 48 := hBrkEq ▸ hBsFit0
      have hNewNat : newBrk.toNat = brkStart.toNat + 8192 := by dsimp only [newBrk]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hLenEq : newBrk.toNat - s3.brk.toNat = 8192 := by rw [hBrk3']; omega
      have hFetch2 : (mallocngBlockProg mmpl 7 msvc).fetch (mbase 7 + svcOff2) = some (.system false 0#16) :=
        Program.fetch_of_hasWords_getElem_decode 87 3556769793#32 hWordsSvc (by dsimp only [svcOff2]; simp only [BitVec.reduceSub]; bv_arith) rfl rfl
      refine SepWP.weaken_pre hEnt3 (SepWP.step_svc_brk_grow (newBrk := newBrk) hPc3 hRun3 hFetch2 hx0_3
        (fun hZ => by rw [hZ] at hNewNat; simp at hNewNat) (by rw [hProc3.2.2.2.1, hBs0]; omega) (by rw [hBrk3']; omega)
        (by rw [hBrk3']; exact Nat.dvd_of_mod_eq_zero hBsMod) ⟨brkStart.toNat / 4096 + 2, by omega⟩ (evalInst_svc0_execBrk hx8_3) ?_ ?_ ?_)
      · intro m' hFit2 _ hm' hDBrk
        obtain ⟨⟨_, hBs65536, hBsDvd, hBsFit8⟩, hmProps, hWf', hGrpPost, hRwEmp, hPnEmp, hApBm, hPnEq', hMpEq'⟩ :=
          slowPathB1_trans hWf hInflight h0 sec hFit2
        let ap := brkStart + 4096#64
        let st' : MallocngSt := { st with
          ctx := { st.ctx with secret := sec, initDone := 1#32, availMeta := ap + 64#64, availMetaCount := 100#64, metaAreaHead := ap, metaAreaTail := ap, availMetaAreas := ap + 4096#64, brk := newBrk },
          metaAreas := [{ base := ap, next := 0#64 }], guardPages := [brkStart], bumpMetas := (List.range 100).map (fun j => ({ base := ap, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)),
          reservedMetas := (ap + 24#64) :: st.reservedMetas, masterDom := rangeAddrs brkStart 8192, byteVal := writeBytesToMap (fun _ => 0#8) ap (metaHdrBytes sec 0#64) }
        have hSplit8 : (s3.brk ↦ₛ List.replicate (newBrk.toNat - s3.brk.toNat) 0#8) = ((brkStart ↦ₛ List.replicate 4096 0#8) ∗ (ap ↦ₛ List.replicate 4096 0#8)) := by
          rw [hLenEq, hBrk3', show (8192 : Nat) = 4096 + 4096 from rfl, List.replicate_add, pointsToBytes_append, List.length_replicate]
        rw [hSplit8]
        have hGrowSt := post_brk_grow_state (m' := m') (phys' := s3.physMemAvail - (newBrk.toNat - s3.brk.toNat)) (newBrk := newBrk) (fn := mbase 7) (off := svcOff2)
          (pc' := mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 1 - 36#64)) (by dsimp only [svcOff2]; bv_arith) hRun3 hSp3 hCs3 hProc3
        generalize (((((s3.setBrk newBrk).setMem m').setPhysMemAvail (s3.physMemAvail - (newBrk.toNat - s3.brk.toNat))).writeReg64 .x0 newBrk).setPC (mbase 7 + svcOff2 + 4#64)) = s4 at hGrowSt ⊢
        obtain ⟨hPc4, hRun4, hSp4, hx0_4, hGpr4, hCs4, hProc4, hBrk4, hMem4⟩ := hGrowSt
        have hcl4 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem :=
          hMem4 ▸ hm' ▸ hcl3.of_keepsFrozen (Memory.keepsFrozen_mapZero s3.mem s3.brk _)
        have hx1_4 : s4.readReg64 .x1 = maddrs.ctx := (hGpr4 1#5 nofun nofun).trans hx1_3
        have hx20_4 : s4.readReg64 .x20 = Obj.pageOf maddrs.ctx := (hGpr4 20#5 nofun nofun).trans hx20_3
        have hx22_4 : s4.readReg64 .x22 = newBrk := (hGpr4 22#5 nofun nofun).trans hx22_3
        have hx24_4 : s4.readReg64 .x24 = 4096#64 := (hGpr4 24#5 nofun nofun).trans hx24_3
        let retMmap := mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 1 + 4#64)
        refine SepWP.cut (mid := mbase 16) (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s5 =>
          s5.pc = mbase 16 ∧ s5.status = .Running ∧ s5.sp = s0.sp - 80#64 ∧ s5.readReg64 Reg.lr = retMmap ∧
          s5.readReg64 .x0 = brkStart ∧ (s5.readReg64 .x1).toNat = 4096 ∧ s5.readReg32 .x2 = 0#32 ∧ s5.readReg32 .x3 = 50#32 ∧
          s5.readReg32 .x4 = BitVec.allOnes 32 ∧ s5.readReg64 .x5 = 0#64 ∧ s5.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧
          s5.readReg64 .x21 = ap ∧ s5.readReg64 .x22 = newBrk ∧ s5.readReg64 .x24 = 4096#64 ∧
          Cs25Preserved s0 s5 ∧ MallocngProcPreserved s0 s5 ∧ s5.brk = newBrk)
          (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((brkStart ↦ₛ List.replicate 4096 0#8) ∗ ((ap ↦ₛ List.replicate 4096 0#8) ∗ P_rest { st.ctx with secret := sec, initDone := 1#32, brk := brkStart }))))) hcl4 ?_) ?_)
        · have hEqNew : (newBrk - newBrk == 0#64) = true := by simp
          have hSubAp : newBrk - 4096#64 = ap := by dsimp only [newBrk, ap]; bv_arith
          dsimp only [P_rest, CtxCells, retMmap]; simp only [BitVec.reduceSub] at hPc4
          wp_sym_steps; simp only [resolve_mmapPriv, mbase, mmpl, hEqNew, hSubAp, show ∀ x y : BitVec 64, x + (y - x) = y from fun _ _ => by bv_arith] at *
          obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc4; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs4; wp_done
        · intro s5 P5 hPc5 hRun5 ⟨_, hD5, hcl5, ⟨_, _, hSp5, hLr5, hx0_5, hx1_5, hx2_5, hx3_5, hx4_5, hx5_5, hx20_5, hx21_5, hx22_5, hx24_5, hCs5, hProc5, hBrk5⟩, hEnt5⟩
          refine SepWP.weaken_pre hEnt5 ?_
          have hSt64 : ∀ {stx : State}, stx.sp = s0.sp - 80#64 → stackAt (s0.sp - 80#64) 64 = stackFrame stx 64 :=
            fun h => by rw [stackAt_eq_stackFrameAt (s0.sp - 80#64) 64 (by decide), stackFrameAt_eq_memRegion (s0.sp - 80#64) 64 (by decide)]; unfold stackFrame; rw [h]
          unfold StackFrameSlow; rw [hSt64 hSp5]
          have hSpA5 : s5.spAligned = true := by rw [State.spAligned, hSp5]; exact spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
          have hTp5 : s5.tpidrEl0 = tp := hProc5.2.2.1.trans hTp0
          refine call_withCL_frame_auto (x := ())
            (placed_mmapFixedProtNoneWrapper_ok (P := mallocngBlockProg mmpl 7 msvc) tp brkStart errnoVal (List.replicate 4096 0#8) 4096 List.length_replicate (by decide) (Nat.dvd_refl 4096) hBs65536 hBsDvd (by omega) (by intro pc; simp) rfl)
            hcl5 hPc5 hRun5 hSpA5 hLr5 (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_
          intro s6 hPc6 hRun6 hSp6 hCsCall hcl6
          have hSp6Eq : s6.sp = s0.sp - 80#64 := hSp6.trans hSp5
          rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
          apply SepWP.pure_elim; rintro ⟨hProcCall, hBrk6, _, hDCall⟩
          rw [← hSt64 hSp5]
          have hRw0Emp : ByteMap st'.masterDom (OwnedRwByte st) (fun _ => 0#8) = emp :=
            SetSep_empty _ fun _ _ ⟨hL, _⟩ => hL.elim (fun ⟨_, hm, _⟩ => by rw [hMa0] at hm; cases hm) (fun ⟨_, hg, _⟩ => by rw [hGs0] at hg; cases hg)
          have hApBm' : ((ap ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ((ap + 64#64) ↦ₛ List.replicate 4032 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st) (fun _ => 0#8)) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal := by
            rw [hRw0Emp, sepConj_emp]; exact hApBm
          refine SepWP.weaken_pre (P' := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
            (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₛ List.replicate 4096 0#8) ∗
              CtxCells maddrs.ctx { st.ctx with secret := sec, initDone := 1#32, brk := brkStart } ∗
              ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
              ByteMap st'.masterDom (OwnedRwByte st) (fun _ => 0#8) ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
              MappedSet st'.masterDom (OwnedMappedByte st'))))
            (by dsimp only [P_rest, st']; rw [hRwEmp, hPnEmp, hPnEq', hRw0Emp, hMpEq']; unfold StackFrameSlow; sep_frame) ?_
          have hx20_6 : s6.readReg64 .x20 = Obj.pageOf maddrs.ctx := hCsCall.2.1.trans hx20_5
          have hx21_6 : s6.readReg64 .x21 = ap := hCsCall.2.2.1.trans hx21_5
          have hx22_6 : s6.readReg64 .x22 = newBrk := hCsCall.2.2.2.1.trans hx22_5
          have hx24_6 : s6.readReg64 .x24 = 4096#64 := hCsCall.2.2.2.2.2.1.trans hx24_5
          have hCs6 : Cs25Preserved s0 s6 := ⟨hCsCall.2.2.2.2.2.2.1.trans hCs5.1, hCsCall.2.2.2.2.2.2.2.1.trans hCs5.2.1,
            hCsCall.2.2.2.2.2.2.2.2.1.trans hCs5.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.1.trans hCs5.2.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.2.2.trans hCs5.2.2.2.2⟩
          have hProc6 : MallocngProcPreserved s0 s6 := procPreserved_trans hProc5 hProcCall
          refine SepWP.cut_at_off (mbase 7) (words_ret_off% blk07Words + 24#64)
            (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s7 =>
              s7.pc = mbase 7 + (words_ret_off% blk07Words + 24#64) ∧
              s7.status = .Running ∧ s7.sp = s0.sp - 80#64 ∧ s7.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s7.readReg64 .x21 = ap ∧
              Cs25Preserved s0 s7 ∧ MallocngProcPreserved s0 s7 ∧ s7.brk = s6.brk)
              (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
                (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₛ List.replicate 4096 0#8) ∗
                  CtxCells maddrs.ctx { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := st.ctx.availMetaAreas } ∗
                  ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
                  ByteMap st'.masterDom (OwnedRwByte st) (fun _ => 0#8) ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
                  MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl6 ?_) ?_)
          · have hCtxPre6 : { st.ctx with secret := sec, initDone := 1#32, brk := brkStart } = { emptyCtxFields with secret := sec, initDone := 1#32, brk := brkStart, seq := st.ctx.seq } := by rw [(hWf.initZero_wf h0).1]
            have hCtxPost6 : { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := st.ctx.availMetaAreas } =
                { emptyCtxFields with secret := sec, initDone := 1#32, availMetaAreaCount := 1#64, brk := newBrk, seq := st.ctx.seq } := by dsimp only [st']; rw [(hWf.initZero_wf h0).1]; rfl
            have hMidPre6 : ctxMiddleBytes { emptyCtxFields with secret := sec, initDone := 1#32, brk := brkStart, seq := st.ctx.seq } = ctxMiddleBytes st.ctx := by rw [← hCtxPre6]; rfl
            have hMidPost6 : ctxMiddleBytes { emptyCtxFields with secret := sec, initDone := 1#32, availMetaAreaCount := 1#64, brk := newBrk, seq := st.ctx.seq } = ctxMiddleBytes st.ctx := by rw [(hWf.initZero_wf h0).1]; rfl
            rw [hCtxPre6, hCtxPost6]; dsimp only [CtxCells, retMmap] at hPc6 hx20_6 ⊢; rw [hMidPre6, hMidPost6]; dsimp only [emptyCtxFields]
            clear hCtxPre6 hCtxPost6 hMidPre6 hMidPost6; conv => arg 2; simp only [BitVec.reduceAdd]
            wp_sym_steps; simp only [BitVec.reduceAdd] at *
            obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc6; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs6; wp_done
          · intro s7 P7 hPc7 hRun7 ⟨_, hD7, hcl7, ⟨_, _, hSp7, hx20_7, hx21_7, hCs7, hProc7, hBrk7⟩, hEnt7⟩
            have hBrk7' : s7.brk = newBrk := hBrk7.trans (hBrk6.trans hBrk5)
            have hD03 : MallocngMappedDelta 0 0 s0.mem s3.mem := MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) (hMem2 ▸ hD3))
            have hD47 : MallocngMappedDelta 0 0 s4.mem s7.mem := MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hD5 hDCall) hD7)
            have hNoOrph7 := noOrphanMappings_slowPathB1 (st' := st') hMa0 hGp0 hAv0 hGs0 hBsFit8 rfl rfl hD03 (by rw [hMem4, hm', hLenEq, hBrk3']) hD47
            have hDTot : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem s7.mem :=
              MallocngMappedDelta.mono (by decide) (by unfold allocMetaPlacedByteBound; omega) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hD03 (hLenEq ▸ hDBrk)) (hMem4 ▸ hD47))
            have hMaBound1 : st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101) :=
              Nat.le_trans (by change 1 ≤ 1 + (88 + 8 * peakCount) / 101; omega) (Nat.le_max_right _ _)
            exact SepWP.weaken_pre hEnt7 (sepWP_activate_2a0 hWords hRange hcl7 hPc7 hRun7 hSp7 hSp0 hx20_7 hx21_7 hCs7 hProc7
              hMaBound1 hNoOrph7 hDTot (metaAreas_ctx_eqs hWf rfl rfl rfl rfl (by rw [hMa0])) (fun hne => False.elim (hne hMa0)) (fun _ => rfl) hApBm' hmProps
              (hBrk7' ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
      · obtain ⟨hWfFail, hFmFail, hBmFail, _, hRwFail, hPnFail, hMpFail⟩ := lazyInit_brkFail_wf (sec := sec) hWf h0
        let stFail : MallocngSt := { st with ctx := { emptyCtxFields with secret := sec, initDone := 1#32, brk := -1#64, seq := st.ctx.seq } }
        have hFailSt := post_brk_fail_state (fn := mbase 7) (off := svcOff2)
          (pc' := mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 1 - 36#64)) (by dsimp only [svcOff2]; bv_arith) hRun3 hSp3 hCs3 hProc3
        generalize ((s3.writeReg64 .x0 s3.brk).setPC (mbase 7 + svcOff2 + 4#64)) = s4 at hFailSt ⊢
        obtain ⟨hPc4, hRun4, hSp4, hx0_4, hGpr4, hCs4, hProc4, hBrk4, hMem4⟩ := hFailSt
        have hcl4 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem := hMem4 ▸ hcl3
        have hx20_4 : s4.readReg64 .x20 = Obj.pageOf maddrs.ctx := (hGpr4 20#5 nofun nofun).trans hx20_3
        have hx22_4 : s4.readReg64 .x22 = newBrk := (hGpr4 22#5 nofun nofun).trans hx22_3
        have hx24_4 : s4.readReg64 .x24 = 4096#64 := (hGpr4 24#5 nofun nofun).trans hx24_3
        refine SepWP.cut_at_off (mbase 7) (reloc_call_off% blk07Relocs "__mmap" 0 - 40#64)
          (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s5 =>
            s5.pc = mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 0 - 40#64) ∧ s5.status = .Running ∧ s5.sp = s0.sp - 80#64 ∧
            s5.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s5.readReg64 .x24 = 4096#64 ∧ Cs25Preserved s0 s5 ∧ MallocngProcPreserved s0 s5 ∧ s5.brk = s4.brk)
            (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs stFail.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
              CtxCells maddrs.ctx stFail.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ stFail.auxvPtr) ∗ MallocngAuxvState γ stFail.auxvPtr stFail.auxvSnap ∗
              ByteMap stFail.masterDom (OwnedRwByte stFail) stFail.byteVal ∗ ProtNoneByteMap stFail.masterDom (OwnedProtNoneByte stFail) stFail.byteVal ∗ MappedSet stFail.masterDom (OwnedMappedByte stFail))))) hcl4 ?_) ?_)
        · rw [hRwFail, hPnFail, hMpFail]
          have hNe8192 : (newBrk != brkStart) = true := by
            dsimp only [newBrk]; rw [bne_iff_ne]; intro h; have := congrArg (· - brkStart) h; simp [show brkStart + 8192#64 - brkStart = 8192#64 by bv_arith] at this
          have hCtxR : { st.ctx with secret := sec, initDone := 1#32, brk := brkStart } = { emptyCtxFields with secret := sec, initDone := 1#32, brk := brkStart, seq := st.ctx.seq } := by rw [(hWf.initZero_wf h0).1]
          have hMidPreF : ctxMiddleBytes { emptyCtxFields with secret := sec, initDone := 1#32, brk := brkStart, seq := st.ctx.seq } = ctxMiddleBytes st.ctx := by rw [← hCtxR]; rfl
          have hMidPostF : ctxMiddleBytes stFail.ctx = ctxMiddleBytes st.ctx := by dsimp only [stFail]; rw [(hWf.initZero_wf h0).1]; rfl
          dsimp only [P_rest]; rw [hCtxR]; dsimp only [CtxCells]; rw [hMidPreF, hMidPostF]; dsimp only [stFail, emptyCtxFields]
          clear hCtxR hMidPreF hMidPostF; rw [hBrk3'] at hx0_4; simp only [BitVec.reduceSub] at hPc4; conv => arg 2; simp only [BitVec.reduceSub]
          wp_sym_steps; simp only [hNe8192, BitVec.reduceNeg] at *
          obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc4; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs4; wp_done
        · intro s5 P5 hPc5 hRun5 ⟨_, hD5, hcl5, ⟨_, _, hSp5, hx20_5, hx24_5, hCs5, hProc5, hBrk5⟩, hEnt5⟩
          have hWfFail5 : MallocngWFInflight inflight maddrs.base brkStart s5.brk liveCost peakCost stFail := by rw [hBrk5, hBrk4, hBrk3, hBrk2, hBrk1]; exact hWfFail
          have hD0Tot : MallocngMappedDelta 0 0 s0.mem s5.mem := MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) (hMem2 ▸ hD3)) (hMem4 ▸ hD5))
          exact SepWP.mono (SepWP.weaken_pre hEnt5 (sepWP_slowPathC_144 hWords hRange hcl5 hInflight hCount
            hPc5 hRun5 hSp5 hSp0 hTp0 hx20_5 hx24_5 hCs5 hProc5 hD0Tot hWfFail5 rfl hFmFail hBmFail rfl rfl))
            fun _ _ _ _ => allocMetaFullPost_congr (by dsimp only [stFail]; rw [(hWf.initZero_wf h0).1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      · intro hPhysLt R' hmR
        exact Satisfies.pure_intro
          (MallocngPlacedOomCond.of_delta hProc3.1 hProc3.2.1 hProc3.2.2.2.2.2.2
            (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) (hMem2 ▸ hD3)) (by decide)
            (by unfold allocMetaPlacedByteBound; omega)
            fun _ => ⟨8192, by decide, by decide, by unfold allocMetaPlacedByteBound; omega, Or.inr (by dsimp [State.setStatus]; omega)⟩)
          (Satisfies.drop_left hmR)

set_option maxHeartbeats 400000 in
private theorem sepWP_postInit_01c [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat} {st : MallocngSt} {errnoVal : BitVec 32} {s0 s : State}
    (hWords0 : Blk07HasWords0 mallocngFaultSvcAmf) (hWordsSvc : Blk07HasWords116 msvc) (hRange : Blk07Range116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem) (hInflight : inflight ≤ 7) (hCount : totalLiveCount st ≤ peakCount)
    (hPc : s.pc = mbase 7 + (words_insn_off% blk07Words "cbz" 0 + 4#64)) (hRun : s.status = .Running)
    (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true) (hTp0 : s0.tpidrEl0 = tp) (hBs0 : s0.brkStart = brkStart)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx) (hCs21 : Cs21Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta0 : MallocngMappedDelta 0 0 s0.mem s.mem)
    (hWf : MallocngWFInflight inflight maddrs.base brkStart s.brk liveCost peakCost st) (h1 : st.ctx.initDone = 1#32) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        CtxCells maddrs.ctx st.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st))))
      (AllocMetaFullPost inflight γ tp brkStart liveCost peakCost peakCount st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (allocMetaPlacedByteBound peakCount) s0 sf⌝) := by
  have hWords : Blk07HasWords116 mallocngFaultSvcAmf := Program.hasWords_withSvc_amf hWordsSvc
  have hSpSub : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
  cases hFm : st.freeMetas with
  | cons fm0 rest =>
    have hDll := hWf.free_bump_metas_wf.1; simp only [hFm, List.map_cons, CircularDllWf] at hDll
    have hHdEq : st.ctx.freeMetaHead = fm0.ptr := hDll.1
    have hFmBeq : (fm0.ptr == 0#64) = false := beq_false_of_ne (hDll.2.2.1 (fm0.ptr, fm0.prev, fm0.next) (List.Mem.head _))
    let P_all := StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
      CtxCells maddrs.ctx st.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)))
    refine SepWP.cut_at_off (mbase 7) (words_insn_off% blk07Words "cbz" 0 + 16#64)
      (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
        s1.pc = mbase 7 + (words_insn_off% blk07Words "cbz" 0 + 16#64) ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
        s1.readReg64 .x1 = maddrs.ctx ∧ s1.readReg64 .x19 = fm0.ptr ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk) P_all) hcl ?_) ?_)
    · dsimp only [P_all, CtxCells, ctxMiddleBytes]; rw [hHdEq]; conv => arg 2; simp only [BitVec.reduceAdd]
      wp_sym_steps; simp only [hFmBeq] at *; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx1_1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      exact SepWP.weaken_pre hEnt1 (sepWP_fastPath1_028 hWords0 hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx1_1 hx19_1 hCs1 hProc1
        (MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)) (hBrk1 ▸ hWf) hFm)
  | nil =>
    have hHd0 : st.ctx.freeMetaHead = 0#64 := by have h := hWf.free_bump_metas_wf.1; simpa [hFm, CircularDllWf] using h
    by_cases hAvCnt0 : st.ctx.availMetaCount = 0#64
    · have hNoBump : st.bumpMetas = [] := (hWf.free_bump_metas_wf.2.2.1).elim And.right fun ⟨hPos, _⟩ => by rw [hAvCnt0] at hPos; exact absurd hPos (by decide)
      obtain ⟨hc21, hc22, hc23, hc24, hCs25_0⟩ := hCs21
      unfold StackFrameOpen; rw [cells_split_sub s0.sp 48 16 4 2, cells_sub_succ s0.sp 48 4 (by decide) (by decide), cells_sub_succ s0.sp 40 3 (by decide) (by decide), cells_sub_succ s0.sp 32 2 (by decide) (by decide), cells_sub_succ s0.sp 24 1 (by decide) (by decide)]
      simp only [Nat.reduceSub, cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v48; apply SepWP.exists_elim; intro v40; apply SepWP.exists_elim; intro v32; apply SepWP.exists_elim; intro v24
      let P_slow := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        CtxCells maddrs.ctx st.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)))
      refine SepWP.cut_at_off (mbase 7) (reloc_call_off% blk07Relocs "__mmap" 0 - 104#64)
        (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
          s1.pc = mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 0 - 104#64) ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
          s1.readReg64 .x1 = maddrs.ctx ∧ s1.readReg64 .x2 = st.ctx.availMetaAreaCount ∧ s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s1.readReg64 .x24 = 4096#64 ∧
          Cs25Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk) P_slow) hcl ?_) ?_)
      · dsimp only [P_slow, StackFrameSlow, SavedRegs0, SavedRegs21, CtxCells]; rw [hHd0, hAvCnt0]
        (conv => arg 2; simp only [BitVec.reduceSub]); wp_sym_steps; simp only [hc21, hc22, hc23, hc24] at *
        obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25_0; wp_done
      · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx1_1, hx2_1, hx20_1, hx24_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
        refine SepWP.weaken_pre hEnt1 ?_
        have hWf1 : MallocngWFInflight inflight maddrs.base brkStart s1.brk liveCost peakCost st := hBrk1.symm ▸ hWf
        by_cases hAreaCnt0 : st.ctx.availMetaAreaCount = 0#64
        · by_cases hBrkNeg1 : st.ctx.brk = -1#64
          · refine SepWP.cut_at_off (mbase 7) (reloc_call_off% blk07Relocs "__mmap" 0 - 40#64)
              (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s2 =>
                s2.pc = mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 0 - 40#64) ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧
                s2.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s2.readReg64 .x24 = 4096#64 ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 ∧ s2.brk = s1.brk) P_slow) hcl1 ?_) ?_)
            · dsimp only [P_slow, CtxCells]; rw [hAreaCnt0] at hx2_1; rw [hAreaCnt0, hBrkNeg1]
              simp only [BitVec.reduceSub] at hPc1; (conv => arg 2; simp only [BitVec.reduceSub]); wp_sym_steps
              obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc1; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs1; wp_done
            · intro s2 P2 hPc2 hRun2 ⟨_, hD2, hcl2, ⟨_, _, hSp2, hx20_2, hx24_2, hCs2, hProc2, hBrk2⟩, hEnt2⟩
              exact SepWP.weaken_pre hEnt2 (sepWP_slowPathC_144 hWords hRange hcl2 hInflight hCount
                hPc2 hRun2 hSp2 hSp0 hTp0 hx20_2 hx24_2 hCs2 hProc2 (MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) hD2))
                (hBrk2.symm ▸ hWf1) h1 hFm hNoBump hAreaCnt0 hBrkNeg1)
          · obtain ⟨hBrkEq, hBrkGe, _⟩ := hWf1.brk_mode_wf.1 ⟨h1, hBrkNeg1⟩; have hBrkHi := hWf1.brk_bounds.2.2.2.2
            rw [hBrk1] at hBrkEq hBrkGe hBrkHi
            have hBrkAdd1 : (s.brk + 1#64 == 0#64) = false := beq_false_of_ne fun h => by have := congrArg BitVec.toNat h; rw [BitVec.toNat_add] at this; simp at this; omega
            have hBrkNe0 : (s.brk == 0#64) = false := beq_false_of_ne fun h => by rw [h] at hBrkGe; simp at hBrkGe
            refine SepWP.cut_at_off (mbase 7) (reloc_call_off% blk07Relocs "__mmap" 0 - 84#64)
              (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s2 =>
                s2.pc = mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 0 - 84#64) ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧
                s2.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s2.readReg64 .x21 = s2.brk ∧ s2.readReg64 .x24 = 4096#64 ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 ∧ s2.brk = s.brk) P_slow) hcl1 ?_) ?_)
            · dsimp only [P_slow, CtxCells]; rw [hAreaCnt0] at hx2_1; rw [hAreaCnt0, hBrkEq]
              simp only [BitVec.reduceSub] at hPc1; (conv => arg 2; simp only [BitVec.reduceSub]); wp_sym_steps; simp only [hBrkAdd1, hBrkNe0] at *
              obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc1; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs1; wp_done
            · intro s2 P2 hPc2 hRun2 ⟨_, hD2, hcl2, ⟨_, _, hSp2, hx20_2, hx21_2, hx24_2, hCs2, hProc2, hBrk2⟩, hEnt2⟩
              exact SepWP.weaken_pre hEnt2 (sepWP_slowPathB2_118 hWordsSvc hRange hcl2 hInflight hCount
                hPc2 hRun2 hSp2 hSp0 hTp0 hBs0 hx20_2 hx21_2 hx24_2 hCs2 hProc2 (MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) hD2))
                (hBrk2.symm ▸ hWf) h1 hFm hNoBump hAreaCnt0 hBrkNeg1)
        · obtain ⟨⟨_, hApMod, hApFit⟩, hmProps, hWf', hGrpPost, hPnEx, hTailBm, hApBm, hMpEq⟩ := slowPathA_trans hWf1 hInflight h1 hFm hNoBump hAreaCnt0
          let ap := st.ctx.availMetaAreas; let cnt' := st.ctx.availMetaAreaCount - 1#64; let rest := (List.range cnt'.toNat).map (fun i => (ap + 4096#64) + BitVec.ofNat 64 (4096 * i))
          let bv1 := if hne : st.metaAreas ≠ [] then writeBytesToMap st.byteVal (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) else st.byteVal
          let st' : MallocngSt := { st with ctx := { st.ctx with availMeta := ap + 64#64, availMetaCount := 100#64, availMetaAreaCount := cnt', metaAreaHead := (match st.metaAreas with | [] => ap | hd :: _ => hd.base), metaAreaTail := ap, availMetaAreas := ap + 4096#64 }, metaAreas := appendMetaArea st.metaAreas ap, mmapMetaAreas := ((appendMetaArea st.metaAreas ap).map (·.base)).filter (fun mb => !decide (InRegion brkStart (s1.brk.toNat - brkStart.toNat) mb)), availMetaPages := rest, freeMetas := [], bumpMetas := (List.range 100).map (fun j => ({ base := ap, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)), reservedMetas := (ap + 24#64) :: st.reservedMetas, byteVal := writeBytesToMap bv1 ap (metaHdrBytes st.ctx.secret 0#64) }
          have hApAlign : 4096 ∣ ap.toNat := Nat.dvd_of_mod_eq_zero hApMod
          have hApMask : (ap &&& 4095#64 == 0#64) = true := beq_iff_eq.mpr (and_4095_eq_zero_of_dvd hApAlign)
          have hAreaBne : (st.ctx.availMetaAreaCount != 0#64) = true := bne_iff_ne.mpr hAreaCnt0
          have hAreaBeq : (st.ctx.availMetaAreaCount == 0#64) = false := beq_false_of_ne hAreaCnt0
          have hCtxEqM : { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := st.ctx.availMetaAreas } = st.ctx := by
            dsimp only [st', cnt']; rw [BitVec.sub_add_cancel]
          let P_mprot := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
            (ap ↦ₙ List.replicate 4096 0#8) ∗ CtxCells maddrs.ctx { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := st.ctx.availMetaAreas } ∗
            ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗ ByteMap st'.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st')))
          have hPnEx' : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal = ((ap ↦ₙ List.replicate 4096 0#8) ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal) := hPnEx
          have hMpEq' : MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) := hMpEq
          refine SepWP.weaken_pre (P' := P_mprot) (Entails.of_eq (by
            dsimp only [P_slow, P_mprot]
            rw [hCtxEqM, show st'.liveMap = st.liveMap from rfl, show st'.auxvPtr = st.auxvPtr from rfl, show st'.auxvSnap = st.auxvSnap from rfl,
              show ByteMap st'.masterDom (OwnedRwByte st) st.byteVal = ByteMap st.masterDom (OwnedRwByte st) st.byteVal from rfl, hPnEx', ← hMpEq']
            ac_rfl)) ?_
          refine SepWP.cut_at_off (mbase 7) (reloc_call_off% blk07Relocs "mprotect" - 12#64)
            (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s2 =>
              s2.pc = mbase 7 + (reloc_call_off% blk07Relocs "mprotect" - 12#64) ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧
              s2.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s2.readReg64 .x21 = ap ∧ s2.readReg64 .x24 = 4096#64 ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 ∧ s2.brk = s1.brk) P_mprot) hcl1 ?_) ?_)
          · dsimp only [ap, P_mprot]; rw [hCtxEqM]; dsimp only [CtxCells]
            simp only [BitVec.reduceSub] at hPc1; (conv => arg 2; simp only [BitVec.reduceSub]); wp_sym_steps; simp only [hAreaBne, hAreaBeq, hApMask] at *
            obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc1; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs1; wp_done
          · intro s2 P2 hPc2 hRun2 ⟨_, hD2, hcl2, ⟨_, _, hSp2, hx20_2, hx21_2, hx24_2, hCs2, hProc2, hBrk2⟩, hEnt2⟩
            have hD02 : MallocngMappedDelta 0 0 s0.mem s2.mem :=
              MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) hD2)
            exact SepWP.weaken_pre hEnt2 (sepWP_mprotect_224 hWords hRange hcl2 hPc2 hRun2 hSp2 hSp0 hTp0 hx20_2 hx21_2 hx24_2 hApAlign hApFit hCs2 hProc2
              (appendMetaArea_len_le_max ap hWf1 hInflight hFm hNoBump hCount)
              (noOrphanMappings_slowPathA hWf1 hAreaCnt0 rfl rfl rfl rfl hD02)
              (MallocngMappedDelta.mono (by decide) (by omega) hD02)
              (metaAreas_ctx_eqs hWf1 rfl rfl rfl rfl rfl) hTailBm (fun hNil => dite_eq_right_iff.mpr fun h => False.elim (h hNil)) hApBm hmProps
              (hBrk2.symm ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
    · obtain ⟨hmProps, hWf', hRwEx, hPnEq, hMpEq⟩ := fastPath2_bump_trans hWf hFm hAvCnt0
      let m := st.ctx.availMeta
      let st' : MallocngSt := { st with ctx := { st.ctx with availMeta := m + 40#64, availMetaCount := st.ctx.availMetaCount - 1#64 }, bumpMetas := st.bumpMetas.tail, reservedMetas := m :: st.reservedMetas }
      have hBumpBeq : (st.ctx.availMetaCount == 0#64) = false := beq_false_of_ne hAvCnt0
      refine SepWP.cut_at_off (mbase 7) (words_ret_off% blk07Words - 28#64)
        (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
          s1.pc = mbase 7 + (words_ret_off% blk07Words - 28#64) ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
          s1.readReg64 .x19 = m ∧ s1.readReg64 .x0 = st'.ctx.availMetaCount ∧ s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧
          Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
          (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
            (m ↦ₛ List.replicate 40 0#8) ∗ CtxCells maddrs.ctx { st'.ctx with availMeta := m, availMetaCount := st.ctx.availMetaCount } ∗
            ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
            ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl ?_) ?_)
      · have hMidEq : ctxMiddleBytes { st'.ctx with availMeta := m, availMetaCount := st.ctx.availMetaCount } = ctxMiddleBytes st.ctx := rfl
        rw [hRwEx, ← hPnEq, ← hMpEq]; dsimp only [m, CtxCells]; rw [hMidEq]; dsimp only [st']; rw [hHd0]
        conv => arg 2; simp only [BitVec.reduceSub]
        wp_sym_steps; simp only [hBumpBeq] at *
        obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
      · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hx0_1, hx20_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
        have hD01 : MallocngMappedDelta 0 0 s0.mem s1.mem :=
          MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)
        exact SepWP.weaken_pre hEnt1 (sepWP_epilogue_26c hWords hRange hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hx0_1 hx20_1 rfl hCs1 hProc1
          (Nat.le_max_left _ _) (noOrphanMappings_of_same_ivs_delta_zero rfl hD01)
          (MallocngMappedDelta.mono (by decide) (by omega) hD01)
          hmProps (hBrk1 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ _ _ _ => rfl))

set_option maxHeartbeats 400000 in
private theorem sepWP_lazyInit_to_b1 [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {st : MallocngSt} {sec : BitVec 64} {errnoVal : BitVec 32} {s0 s2 : State}
    (_hWords0 : Blk07HasWords0 mallocngFaultSvcAmf) (hWordsSvc : Blk07HasWords116 msvc) (hRange : Blk07Range116)
    (hcl2 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem) (hInflight : inflight ≤ 7) (hCount : totalLiveCount st ≤ peakCount)
    (hPc2 : s2.pc = mbase 7 + (words_insn_off% blk07Words "cbz" 0 + 4#64)) (hRun2 : s2.status = .Running)
    (hSp2 : s2.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true) (hTp0 : s0.tpidrEl0 = tp) (hBs0 : s0.brkStart = brkStart)
    (hx20_2 : s2.readReg64 .x20 = Obj.pageOf maddrs.ctx) (hCs2 : Cs21Preserved s0 s2) (hProc2 : MallocngProcPreserved s0 s2)
    (hD02 : MallocngMappedDelta 0 0 s0.mem s2.mem)
    (hWf : MallocngWFInflight inflight maddrs.base brkStart s2.brk liveCost peakCost st) (h0 : st.ctx.initDone = 0#32) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s2
      (StackFrameOpen s0 ∗ CtxCells maddrs.ctx { st.ctx with secret := sec, initDone := 1#32 } ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
        (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st)))
      (AllocMetaFullPost inflight γ tp brkStart liveCost peakCost peakCount st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (allocMetaPlacedByteBound peakCount) s0 sf⌝) := by
  have hWords : Blk07HasWords116 mallocngFaultSvcAmf := Program.hasWords_withSvc_amf hWordsSvc
  have hSpSub : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
  obtain ⟨hc21, hc22, hc23, hc24, hCs25_2⟩ := hCs2
  unfold StackFrameOpen; rw [cells_split_sub s0.sp 48 16 4 2, cells_sub_succ s0.sp 48 4 (by decide) (by decide), cells_sub_succ s0.sp 40 3 (by decide) (by decide), cells_sub_succ s0.sp 32 2 (by decide) (by decide), cells_sub_succ s0.sp 24 1 (by decide) (by decide)]
  simp only [Nat.reduceSub, cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v48; apply SepWP.exists_elim; intro v40; apply SepWP.exists_elim; intro v32; apply SepWP.exists_elim; intro v24
  let P_b1 := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
    CtxCells maddrs.ctx { st.ctx with secret := sec, initDone := 1#32 } ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)))
  refine SepWP.cut_at_off (mbase 7) (reloc_call_off% blk07Relocs "__mmap" 1 - 80#64)
    (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s3 =>
      s3.pc = mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 1 - 80#64) ∧ s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧
      s3.readReg64 .x1 = maddrs.ctx ∧ s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s3.readReg64 .x24 = 4096#64 ∧
      Cs25Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = s2.brk) P_b1) hcl2 ?_) ?_)
  · have hCtxSec : { st.ctx with secret := sec, initDone := 1#32 } = { emptyCtxFields with secret := sec, initDone := 1#32, seq := st.ctx.seq } := by rw [(hWf.initZero_wf h0).1]
    have hMidSec : ctxMiddleBytes { emptyCtxFields with secret := sec, initDone := 1#32, seq := st.ctx.seq } = ctxMiddleBytes st.ctx := by rw [← hCtxSec]; rfl
    simp only [BitVec.reduceAdd] at hPc2; dsimp only [P_b1, StackFrameSlow, SavedRegs0, SavedRegs21] at hCtxSec ⊢
    rw [hCtxSec]; dsimp only [CtxCells]; rw [hMidSec]; dsimp only [emptyCtxFields]; clear hCtxSec hMidSec
    (conv => arg 2; simp only [BitVec.reduceSub]); wp_sym_steps; simp only [hc21, hc22, hc23, hc24] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25_2; wp_done
  · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx1_3, hx20_3, hx24_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
    exact SepWP.weaken_pre hEnt3 (sepWP_slowPathB1_1a8 hWordsSvc hRange hcl3 hInflight hCount hPc3 hRun3 hSp3 hSp0 hTp0 hBs0 hx1_3 hx20_3 hx24_3 hCs3 hProc3
      (MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hD02 hD3)) (hBrk3 ▸ hWf) h0)

theorem placed_allocMeta_full_entry : AllocMetaPlacedFullStmt := by
  intro _ inflight hInflight γ tp brkStart liveCost peakCost peakCount st hCount
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have ⟨hWords0Svc, _⟩ := hasWords_blk_seg0 (i := 7) (by decide) (ws := blk07Words0) (R := blk07Relocs0) (by decide +kernel)
  have ⟨hWordsSvc, hRange⟩ := hasWords_blk_seg (i := 7) (by decide) 116 (ws := blk07Words116) (R := blk07Relocs116) (by decide +kernel)
  have hWords0 : Blk07HasWords0 mallocngFaultSvcAmf := Program.hasWords_withSvc_amf hWords0Svc
  have hWords : Blk07HasWords116 mallocngFaultSvcAmf := Program.hasWords_withSvc_amf hWordsSvc
  apply subroutine_ok_of_sepWP_init; intro _ R s0 hPc0 hRun0 hPre0 hSp0; refine ⟨_, hPre0, ?_⟩; dsimp only
  refine SepWP.mono ?_ (fun sf P_f _ _ (hPost : AllocMetaFullPost inflight γ tp brkStart liveCost peakCost peakCount st s0 sf P_f) =>
    ⟨fun hmf => Satisfies.mono (sepConj_mono_left hPost.1) hmf, hPost.2.1, hPost.2.2⟩)
  apply SepWP.pure_elim; rintro rfl; apply SepWP.pure_elim; rintro ⟨hTp0, hBs0⟩
  unfold MallocngCoreStInflightA MallocngRuntime
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]; apply SepWP.exists_elim; intro errnoVal
  simp only [show ∀ (P : SepProp) (φ : Prop) (Q : SepProp), P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) from fun P _ _ => by rw [← sepConj_assoc, sepConj_comm P, sepConj_assoc]]
  apply SepWP.pure_elim; intro hWf
  have hSt224 : stackFrame s0 224 = (memRegion (s0.sp - 224#64) 80 ∗ (stackAt (s0.sp - 80#64) 64 ∗ cells (s0.sp - 80#64) 10)) := by
    unfold stackFrame; rw [← stackFrameAt_eq_memRegion s0.sp 224, ← stackAt_eq_stackFrameAt s0.sp 224]
    exact wrapperFrame_split s0.sp (wrapperStack := 224) (hookStack := 64) 10 (by decide)
  rw [hSt224, cells_split_sub s0.sp 80 48 4 6, cells_sub_succ s0.sp 80 4 (by decide) (by decide), cells_sub_succ s0.sp 72 3 (by decide) (by decide), cells_sub_succ s0.sp 64 2 (by decide) (by decide), cells_sub_succ s0.sp 56 1 (by decide) (by decide)]
  simp only [Nat.reduceSub, cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v80; apply SepWP.exists_elim; intro v72; apply SepWP.exists_elim; intro v64; apply SepWP.exists_elim; intro v56
  obtain ⟨l1, l2, l3, l4, l5, _⟩ := hWf.ctx_lens
  have hCtxCells := ctx_toBytes_eq_cells maddrs.ctx st.ctx l1 l2 l3 l4 (by rw [l5]; rfl)
  have hSpSub : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
  let P_open (c : CtxFields) := StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
    CtxCells maddrs.ctx c ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)))
  refine SepWP.weaken_pre (P' := ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗ ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗ CtxCells maddrs.ctx st.ctx ∗
    (memRegion (s0.sp - 224#64) 80 ∗ stackAt (s0.sp - 80#64) 64 ∗ cells (s0.sp - 48#64) 6 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ StaticFrameA γ maddrs st.liveMap ∗
      ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)))
    (by unfold StaticFrameA; rw [hCtxCells]; sep_frame) ?_
  clear l1 l2 l3 l4 l5 hCtxCells hSt224
  rcases hWf.initDone_wf with h0 | h1
  · refine SepWP.cut_at_off (mbase 7) (reloc_call_off% blk07Relocs "memcpy" - 68#64)
      (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
        s1.pc = mbase 7 + (reloc_call_off% blk07Relocs "memcpy" - 68#64) ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
        s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s0.brk) (P_open st.ctx)) hcl0 ?_) ?_)
    · dsimp only [P_open, StackFrameOpen, SavedRegs0, CtxCells]; rw [h0]; (conv => arg 2; simp only [BitVec.reduceSub]); wp_sym_steps; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx20_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      exact SepWP.weaken_pre (Entails.trans hEnt1 (by dsimp only [P_open]; sep_frame)) (sepWP_lazyInit_05c
        (R_frame := ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st))
        hWords0 hWords hRange hcl1 hPc1 hRun1 hSp1 hSp0 hx20_1 hCs1 hProc1
        fun s2 sec hcl2 hPc2 hRun2 hSp2 hx20_2 hCs2 hProc2 hBrk2 hD2 =>
          sepWP_lazyInit_to_b1 hWords0 hWordsSvc hRange hcl2 hInflight hCount hPc2 hRun2 hSp2 hSp0 hTp0 hBs0 hx20_2 hCs2 hProc2
            (MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hD1 hD2)) ((hBrk2.trans hBrk1) ▸ hWf) h0)
  · refine SepWP.cut_at_off (mbase 7) (words_insn_off% blk07Words "cbz" 0 + 4#64)
      (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
        s1.pc = mbase 7 + (words_insn_off% blk07Words "cbz" 0 + 4#64) ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
        s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s0.brk) (P_open st.ctx)) hcl0 ?_) ?_)
    · dsimp only [P_open, StackFrameOpen, SavedRegs0, CtxCells]; rw [h1]; (conv => arg 2; simp only [BitVec.reduceAdd]); wp_sym_steps; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx20_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      exact SepWP.weaken_pre hEnt1 (sepWP_postInit_01c hWords0 hWordsSvc hRange hcl1 hInflight hCount
        hPc1 hRun1 hSp1 hSp0 hTp0 hBs0 hx20_1 hCs1 hProc1 (MallocngMappedDelta.mono (by decide) (by decide) hD1) (hBrk1 ▸ hWf) h1)

end VerifiedLibraries.Mallocng.Proofs.AllocMetaFullH

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-- Verification of full placed `__malloc_alloc_meta()` (`blk07`) on `mallocngBlockProg mmpl 7 msvc`,
    recording `MallocngNoOrphanMappings` and the `metaAreas.length` bound. -/
theorem placed_allocMeta_full_ok : AllocMetaPlacedFullStmt :=
  AllocMetaFullH.placed_allocMeta_full_entry

/-- Polymorphic cross-block lift of `placed_allocMeta_full_ok` (`blk07`) onto any caller block program `P`. -/
theorem call_placed_allocMeta_full [MallocngMultiPlacement] {P : Program}
    (inflight : Nat) (hInflight : inflight ≤ 7) (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat) (st : MallocngSt) (hCount : totalLiveCount st ≤ peakCount)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 7) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗ stackFrame s0 224 ∗
        MallocngCoreStInflightA inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗ MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        ∃∗ st' : MallocngSt, ∃∗ m : BitVec 64,
          ⌜MallocngProcPreserved s0 sf ∧ sf.readReg64 .x0 = m ∧ m ≠ 0#64 ∧
           4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.reservedMetas ∧
           st'.reservedMetas = m :: st.reservedMetas ∧ st'.groups = st.groups ∧
           st'.activeLists = st.activeLists ∧ st'.liveMap = st.liveMap ∧
           totalLiveCount st' = totalLiveCount st ∧
           st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101) ∧
           st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
           st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq ∧
           (∀ g ∈ st.groups, ∀ a : BitVec 64,
             (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) ∧
           MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem sf.mem⌝ ∗
          stackFrame s0 224 ∗ MallocngRuntime maddrs tp ∗ (m ↦ₛ List.replicate 40 0#8) ∗
          MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'
      onOom := fun _ s0 sf =>
        ⌜MallocngPlacedOomCond msvc 1 (allocMetaPlacedByteBound peakCount) s0 sf⌝
    }) :=
  subroutine_ok_block_to_block (j := 7) (by decide)
    (placed_allocMeta_full_ok inflight hInflight γ tp brkStart liveCost peakCost peakCount st hCount) hext hsvc

end VerifiedLibraries.Mallocng.Proofs
