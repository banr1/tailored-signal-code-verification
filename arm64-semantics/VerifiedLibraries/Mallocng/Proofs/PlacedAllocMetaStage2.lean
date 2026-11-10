/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaStage1

/-!
# Stage 2 Symbolic Execution for Placed `__malloc_alloc_meta`

Proves the `PROT_NONE` batch allocation slow path (`sepWP_slowPathC_144`), auxiliary-vector
scanning (`sepWP_auxv_scan`), lazy `AT_RANDOM` initialization (`sepWP_lazyInit_05c`), and circular
free-list pop (`sepWP_fastPath1_028`) for `blk07` on `mallocngBlockProg mmpl 7 msvc`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Slow path C (`PROT_NONE` batch) and auxiliary-vector scanning -/

theorem sepWP_slowPathC_144 [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {st : MallocngSt} {errnoVal : BitVec 32} {s0 s : State}
    (hWords : Blk07HasWords116 mallocngFaultSvc)
    (hRange : Blk07Range116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hInflight : inflight ≤ 7) (hCount : totalLiveCount st ≤ peakCount)
    (hPc : s.pc = mbase 7 + (reloc_call_off% blk07Relocs "__mmap" 0 - 40#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hTp0 : s0.tpidrEl0 = tp)
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
      (AllocMetaPlacedPost inflight γ tp brkStart liveCost peakCost peakCount st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (allocMetaPlacedByteBound peakCount) s0 sf⌝) := by
  have hAv0 : st.availMetaPages = [] := by have h := hWf.guard_avail_wf.2.2.1; rw [hCnt0] at h; exact h
  obtain ⟨hmLe35, hLenGe, hLenLe48, hLenDvd, hLenBound⟩ :=
    metaAreas_mmap_bytes_le_allocMetaPlacedByteBound hWf hInflight hNoFree hNoBump hAv0 hCount
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
    (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s1 =>
      s1.pc = mbase 16 ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 Reg.lr = retMmap ∧ s1.readReg64 .x0 = 0#64 ∧ (s1.readReg64 .x1).toNat = len ∧
      s1.readReg32 .x2 = 0#32 ∧ s1.readReg32 .x3 = 0x22#32 ∧ s1.readReg32 .x4 = BitVec.allOnes 32 ∧ s1.readReg64 .x5 = 0#64 ∧
      s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s1.readReg64 .x22 = BitVec.ofNat 64 (2 ^ (m + 1)) ∧
      s1.readReg64 .x23 = maddrs.ctx ∧ s1.readReg64 .x24 = 4096#64 ∧
      Cs25Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ P_rest))) hcl ?_) ?_)
  · dsimp only [P_rest, CtxCells, retMmap] at *
    simp only [BitVec.reduceSub] at hPc
    wp_sym_steps
    have hx22Eq : (2#64 <<< (st.ctx.metaAllocShift.toNat % 64)) = BitVec.ofNat 64 (2 ^ (m + 1)) :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show st.ctx.metaAllocShift.toNat % 64 = m by omega, Nat.shiftLeft_eq, show 2 * 2 ^ m = 2 ^ (m + 1) by rw [Nat.pow_succ]; omega])
    have hx1Eq : (4096#64 * BitVec.ofNat 64 (2 ^ (m + 1))).toNat = len := by
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; dsimp [len]; omega
    simp only [hx22Eq, hx1Eq, show ∀ x y : BitVec 64, x + (y - x) = y from fun _ _ => by bv_arith] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25
    wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hLr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx20_1, hx22_1, hx23_1, hx24_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    refine SepWP.weaken_pre hEnt1 ?_
    have hSt64 : ∀ {stx : State}, stx.sp = s0.sp - 80#64 → stackAt (s0.sp - 80#64) 64 = stackFrame stx 64 :=
      fun h => by rw [stackAt_eq_stackFrameAt (s0.sp - 80#64) 64 (by decide), stackFrameAt_eq_memRegion (s0.sp - 80#64) 64 (by decide)]; unfold stackFrame; rw [h]
    unfold StackFrameSlow; rw [hSt64 hSp1]
    have hSpA1 : s1.spAligned = true := by rw [State.spAligned, hSp1]; exact spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
    have hTp1 : s1.tpidrEl0 = tp := hProc1.2.2.1.trans hTp0
    refine call_withCL_frame_auto (x := ())
      (placed_mmapProtNoneWrapper_ok (P := mallocngBlockProg mmpl 7 msvc) tp errnoVal len (by omega) (by omega) (by intro pc; simp) rfl)
      hcl1 hPc1 hRun1 hSpA1 hLr1 (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by sep_frame) ?_
    · intro s2 hPc2 hRun2 hSp2 hCsCall hcl2
      apply SepWP.of_sepExists_left; intro mb
      rw [pageAlignUp_of_dvd hLenDvd, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hProcCall, hBrk2, hx0_2, hMbNe0, hMbNeNeg1, hMbAlign, hMbFit, hDCall⟩
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
        (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s3 =>
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
        have hProc2 : MallocngProcPreserved s0 s2 := MallocngProcPreserved.trans hProc1 hProcCall
        have hMbAdd1 : (mb + 1#64 == 0#64) = false := beq_false_of_ne fun hEq => hMbNeNeg1
          (BitVec.eq_of_toNat_eq (by have h := congrArg BitVec.toNat hEq; rw [BitVec.toNat_add] at h; simp at h ⊢; omega))
        have hApMask : ((mb + 4096#64) &&& 4095#64 == 0#64) = true := beq_iff_eq.mpr (and_4095_eq_zero_of_dvd hApAlign)
        have hCntAdd : (BitVec.ofNat 64 (2 ^ (m + 1)) - 1#64) * 1#64 = cnt' + 1#64 :=
          BitVec.eq_of_toNat_eq (by rw [BitVec.mul_one, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; simp; omega), BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; dsimp [cnt']; rw [BitVec.toNat_ofNat]; omega)
        have hShiftAdd : st.ctx.metaAllocShift + 1#64 = BitVec.ofNat 64 (m + 1) :=
          BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, hmDef]; simp)
        dsimp only [CtxCells, ctxMiddleBytes, st']
        conv => arg 2; simp only [BitVec.reduceSub]
        wp_sym_steps
        simp only [hCntAdd, hShiftAdd, ap] at *
        obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs2
        rw [← hBrk1, ← hBrk2]
        wp_done
      · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx20_3, hx21_3, hx24_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
        have hDTot : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount - 4096) s0.mem s3.mem := by
          refine MallocngMappedDelta.mono ?_ ?_
            (MallocngMappedDelta.trans (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) hDCall) hD3)
          all_goals omega
        exact SepWP.weaken_pre hEnt3 (sepWP_mprotect_224 hWords hRange hcl3
          hPc3 hRun3 hSp3 hSp0 hTp0 hx20_3 hx21_3 hx24_3 hApAlign hApFit hCs3 hProc3 hDTot
          (metaAreas_ctx_eqs hWf rfl rfl rfl rfl rfl) hTailBm (fun hNil => dite_eq_right_iff.mpr fun h => False.elim (h hNil)) hApBm hmProps
          (hBrk3 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
    · intro R' sf _ hSatOom
      have hDrop := Satisfies.drop_mid hSatOom
      rw [satisfies_pure_sepConj] at hDrop ⊢
      obtain ⟨hFsEq, hTrEq, hSigEq, _, hDMmap, hNoGap⟩ := hDrop.1
      exact ⟨MallocngPlacedOomCond.of_delta (hFsEq.trans hProc1.1) (hTrEq.trans hProc1.2.1)
        (hSigEq.trans hProc1.2.2.2.2.2.2) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) hDMmap)
        (by omega) (by omega)
        fun hSan => ⟨len, by dsimp [PAGE_SIZE]; omega, Nat.mod_eq_zero_of_dvd hLenDvd, by omega, by rw [← pageAlignUp_of_dvd hLenDvd]; exact hNoGap hSan⟩, hDrop.2⟩

theorem auxvFlat_len (xs : List (BitVec 64 × BitVec 64)) :
    (xs.flatMap fun (t, v) => [t, v]).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ tl ih => dsimp only [List.flatMap_cons]; simp [ih]; omega

theorem sepWP_auxv_scan [MallocngMultiPlacement]
    {target_pc auxvPtr : BitVec 64} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hWords : Blk07HasWords116 mallocngFaultSvc)
    (_hRange : Blk07Range116)
    (entries : List (BitVec 64 × BitVec 64)) (hTags : ∀ e ∈ entries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) :
    ∀ (idx : Nat) (R_frame : SepProp) (s0 s : State),
      VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem →
      s.pc = mbase 7 + (reloc_call_off% blk07Relocs "memcpy" + 12#64) →
      s.status = .Running → s.sp = s0.sp - 80#64 →
      s.readReg64 .x0 = auxvPtr → s.readReg64 .x19 = BitVec.ofNat 64 (16 * idx) →
      s.readReg64 .x20 = Obj.pageOf maddrs.ctx →
      s.readReg64 .x21 = s0.sp - 8#64 → s.readReg64 .x22 = maddrs.libc →
      Cs23Preserved s0 s → MallocngProcPreserved s0 s →
      (∀ s1 : State,
        VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem →
        s1.pc = mbase 7 + (reloc_call_off% blk07Relocs "memcpy" + 12#64) →
        s1.status = .Running → s1.sp = s0.sp - 80#64 →
        s1.readReg64 .x0 = auxvPtr → s1.readReg64 .x19 = BitVec.ofNat 64 (16 * (idx + entries.length)) →
        s1.readReg64 .x20 = Obj.pageOf maddrs.ctx →
        s1.readReg64 .x21 = s0.sp - 8#64 → s1.readReg64 .x22 = maddrs.libc →
        Cs23Preserved s0 s1 → MallocngProcPreserved s0 s1 → s1.brk = s.brk →
        MallocngMappedDelta 0 0 s.mem s1.mem →
        SepWP (mallocngBlockProg mmpl 7 msvc) target_pc s1 (((auxvPtr + BitVec.ofNat 64 (16 * idx)) ↦₆₄* (entries.flatMap fun (t, v) => [t, v])) ∗ R_frame) post oom) →
      SepWP (mallocngBlockProg mmpl 7 msvc) target_pc s (((auxvPtr + BitVec.ofNat 64 (16 * idx)) ↦₆₄* (entries.flatMap fun (t, v) => [t, v])) ∗ R_frame) post oom := by
  induction entries with
  | nil =>
    intro idx R_frame s0 s hcl hPc hRun hSp hx0 hx19 hx20 hx21 hx22 hCs hProc hCont
    exact hCont s hcl hPc hRun hSp hx0 (by simpa using hx19) hx20 hx21 hx22 hCs hProc rfl (MallocngMappedDelta.refl 0 0 s.mem)
  | cons hd rest ih =>
    intro idx R_frame s0 s hcl hPc hRun hSp hx0 hx19 hx20 hx21 hx22 hCs hProc hCont
    rcases hd with ⟨tag, val⟩
    obtain ⟨hTag0, hTag25⟩ := hTags (tag, val) (List.Mem.head _)
    let p_i := auxvPtr + BitVec.ofNat 64 (16 * idx)
    have hNextOff : BitVec.ofNat 64 (16 * idx) + 16#64 = BitVec.ofNat 64 (16 * (idx + 1)) := by
      rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add, show 16 * idx + 16 = 16 * (idx + 1) by omega]
    have hAdd16 : p_i + 8#64 + 8#64 = auxvPtr + BitVec.ofNat 64 (16 * (idx + 1)) := by
      rw [show p_i + 8#64 + 8#64 = auxvPtr + (BitVec.ofNat 64 (16 * idx) + 16#64) by dsimp only [p_i]; bv_arith, hNextOff]
    have hSplit : ((p_i ↦₆₄* (((tag, val) :: rest).flatMap fun (t, v) => [t, v])) ∗ R_frame) =
        ((p_i ↦₆₄ tag) ∗ ((p_i + 8#64) ↦₆₄ val) ∗ (((auxvPtr + BitVec.ofNat 64 (16 * (idx + 1))) ↦₆₄* (rest.flatMap fun (t, v) => [t, v])) ∗ R_frame)) := by
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, pointsToWords64_cons, hAdd16, sepConj_assoc]
    rw [show auxvPtr + BitVec.ofNat 64 (16 * idx) = p_i from rfl, hSplit]
    refine SepWP.cut_at_off (mbase 7) (reloc_call_off% blk07Relocs "memcpy" + 8#64)
      (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s1 =>
        s1.pc = mbase 7 + (reloc_call_off% blk07Relocs "memcpy" + 8#64) ∧
        s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
        s1.readReg64 .x0 = auxvPtr ∧ s1.readReg64 .x19 = BitVec.ofNat 64 (16 * idx) ∧
        s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧
        s1.readReg64 .x21 = s0.sp - 8#64 ∧ s1.readReg64 .x22 = maddrs.libc ∧
        Cs23Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
        ((p_i ↦₆₄ tag) ∗ ((p_i + 8#64) ↦₆₄ val) ∗ (((auxvPtr + BitVec.ofNat 64 (16 * (idx + 1))) ↦₆₄* (rest.flatMap fun (t, v) => [t, v])) ∗ R_frame))) hcl ?_) ?_)
    · have hNe0 : (tag == 0#64) = false := beq_false_of_ne hTag0
      have hNe25a : (tag == 25#64) = false := beq_false_of_ne hTag25
      have hNe25b : (tag - 25#64 == 0#64) = false := beq_false_of_ne fun h => hTag25 (by have h' : tag = (tag - 25#64) + 25#64 := (by bv_arith); rw [h] at h'; exact h')
      have hNe25c : (tag + ~~~25#64 + 1#64 == 0#64) = false := beq_false_of_ne fun h => hTag25 (by have h' : tag = (tag + ~~~25#64 + 1#64) + 25#64 := (by bv_arith); rw [h] at h'; exact h')
      dsimp only [p_i]
      conv => arg 2; simp only [BitVec.reduceAdd]
      wp_sym_steps
      obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs
      wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      refine SepWP.weaken_pre hEnt1 ?_
      refine SepWP.cut_at_off (mbase 7) (reloc_call_off% blk07Relocs "memcpy" + 12#64)
        (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s2 =>
          s2.pc = mbase 7 + (reloc_call_off% blk07Relocs "memcpy" + 12#64) ∧
          s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧
          s2.readReg64 .x0 = auxvPtr ∧ s2.readReg64 .x19 = BitVec.ofNat 64 (16 * (idx + 1)) ∧
          s2.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧
          s2.readReg64 .x21 = s0.sp - 8#64 ∧ s2.readReg64 .x22 = maddrs.libc ∧
          Cs23Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 ∧ s2.brk = s.brk)
          (((auxvPtr + BitVec.ofNat 64 (16 * (idx + 1))) ↦₆₄* (rest.flatMap fun (t, v) => [t, v])) ∗ ((p_i ↦₆₄ tag) ∗ ((p_i + 8#64) ↦₆₄ val) ∗ R_frame))) hcl1 ?_) ?_)
      · conv => arg 2; simp only [BitVec.reduceAdd]
        wp_sym_steps
        simp only [hNextOff] at *
        obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc1; obtain ⟨hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs1
        rw [← hBrk1]
        wp_done
      · intro s2 P2 hPc2 hRun2 ⟨_, hD2, hcl2, ⟨_, _, hSp2, hx0_2, hx19_2, hx20_2, hx21_2, hx22_2, hCs2, hProc2, hBrk2⟩, hEnt2⟩
        refine SepWP.weaken_pre hEnt2 ?_
        exact ih (fun e he => hTags e (List.Mem.tail _ he)) (idx + 1) ((p_i ↦₆₄ tag) ∗ ((p_i + 8#64) ↦₆₄ val) ∗ R_frame)
          s0 s2 hcl2 hPc2 hRun2 hSp2 hx0_2 hx19_2 hx20_2 hx21_2 hx22_2 hCs2 hProc2 fun s3 hcl3 hPc3 hRun3 hSp3 hx0_3 hx19_3 hx20_3 hx21_3 hx22_3 hCs3 hProc3 hBrk3 hD3 => by
            have hx19_3' : s3.readReg64 .x19 = BitVec.ofNat 64 (16 * (idx + ((tag, val) :: rest).length)) := by
              simpa [Nat.add_assoc, Nat.add_comm 1] using hx19_3
            have hDTot : MallocngMappedDelta 0 0 s.mem s3.mem :=
              MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hD1 hD2) hD3)
            refine SepWP.weaken_pre ?_ (hCont s3 hcl3 hPc3 hRun3 hSp3 hx0_3 hx19_3' hx20_3 hx21_3 hx22_3 hCs3 hProc3 (hBrk3.trans hBrk2) hDTot)
            rw [show auxvPtr + BitVec.ofNat 64 (16 * idx) = p_i from rfl, hSplit]
            sep_frame

/-! ## Lazy `AT_RANDOM` initialization and circular free-list pop -/

private theorem sepWP_lazyInit_05c_concrete [MallocngMultiPlacement]
    {target_pc : BitVec 64} {st : MallocngSt}
    {preEntries : List (BitVec 64 × BitVec 64)} {randPtr : BitVec 64}
    {sufEntries : List (BitVec 64 × BitVec 64)} {nullVal sec : BitVec 64}
    {R_frame : SepProp} {s0 s : State}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hAuxvWf : MallocngAuxvConcreteWf st.auxvPtr preEntries randPtr sufEntries)
    (hWords0 : Blk07HasWords0 mallocngFaultSvc)
    (hWords : Blk07HasWords116 mallocngFaultSvc)
    (hRange : Blk07Range116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (reloc_call_off% blk07Relocs "memcpy" - 68#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx)
    (hCs21 : Cs21Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hCont : ∀ (s_out : State),
      VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_out.mem →
      s_out.pc = mbase 7 + (words_insn_off% blk07Words "cbz" 0 + 4#64) →
      s_out.status = .Running → s_out.sp = s0.sp - 80#64 →
      s_out.readReg64 .x20 = Obj.pageOf maddrs.ctx →
      Cs21Preserved s0 s_out → MallocngProcPreserved s0 s_out → s_out.brk = s.brk →
      MallocngMappedDelta 0 0 s.mem s_out.mem →
      SepWP (mallocngBlockProg mmpl 7 msvc) target_pc s_out
        (StackFrameOpen s0 ∗ CtxCells maddrs.ctx { st.ctx with secret := sec, initDone := 1#32 } ∗
          ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
          ((st.auxvPtr ↦₆₄* ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v])) ∗
            ((randPtr + 8#64) ↦₆₄ sec)) ∗ R_frame) post oom) :
    SepWP (mallocngBlockProg mmpl 7 msvc) target_pc s
      (StackFrameOpen s0 ∗ CtxCells maddrs.ctx st.ctx ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
        ((st.auxvPtr ↦₆₄* ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v])) ∗
          ((randPtr + 8#64) ↦₆₄ sec)) ∗ R_frame) post oom := by
  have hSpA : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hSp0
  have hSpSub : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 80#64 hSpA
  obtain ⟨hc21_0, hc22_0, hCs23_0⟩ := hCs21
  obtain ⟨hPreTags, hSufTags, hLen64, hAuxvFit, hRandFit⟩ := hAuxvWf
  unfold StackFrameOpen
  rw [cells_split_sub s0.sp 48 32 2 4, cells_split_sub s0.sp 32 8 3 1,
    cells_sub_succ s0.sp 48 2 (by decide) (by decide), cells_sub_succ s0.sp 40 1 (by decide) (by decide),
    cells_sub_succ s0.sp 8 1 (by decide) (by decide)]
  simp only [Nat.reduceSub, cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v48; apply SepWP.exists_elim; intro v40
  let p_rand := st.auxvPtr + BitVec.ofNat 64 (16 * preEntries.length)
  let p_suf := st.auxvPtr + BitVec.ofNat 64 (16 * (preEntries.length + 1))
  let p_null := st.auxvPtr + BitVec.ofNat 64 (16 * (preEntries.length + 1 + sufEntries.length))
  have hAuxvSplit : (st.auxvPtr ↦₆₄* ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v])) =
      ((st.auxvPtr ↦₆₄* (preEntries.flatMap fun (t, v) => [t, v])) ∗
        (p_rand ↦₆₄ 25#64) ∗ ((p_rand + 8#64) ↦₆₄ randPtr) ∗
        (p_suf ↦₆₄* (sufEntries.flatMap fun (t, v) => [t, v])) ∗
        (p_null ↦₆₄ 0#64) ∗ ((p_null + 8#64) ↦₆₄ nullVal)) := by
    rw [List.append_assoc, List.append_assoc, List.flatMap_append, List.flatMap_append, List.flatMap_append,
      pointsToWords64_append, auxvFlat_len, show 8 * (2 * preEntries.length) = 16 * preEntries.length by omega,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.cons_append, List.nil_append,
      pointsToWords64_cons, pointsToWords64_cons,
      show p_rand + 8#64 + 8#64 = p_suf by
        dsimp only [p_rand, p_suf]
        rw [show st.auxvPtr + BitVec.ofNat 64 (16 * preEntries.length) + 8#64 + 8#64 = st.auxvPtr + (BitVec.ofNat 64 (16 * preEntries.length) + BitVec.ofNat 64 16) by bv_arith,
          ← BitVec.ofNat_add, show 16 * preEntries.length + 16 = 16 * (preEntries.length + 1) by omega],
      pointsToWords64_append, auxvFlat_len,
      show p_suf + BitVec.ofNat 64 (8 * (2 * sufEntries.length)) = p_null by
        dsimp only [p_suf, p_null]
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * (preEntries.length + 1) + 8 * (2 * sufEntries.length) = 16 * (preEntries.length + 1 + sufEntries.length) by omega],
      List.flatMap_cons, List.flatMap_nil, List.append_nil, pointsToWords64_cons, pointsToWords64_cons, pointsToWords64_nil, sepConj_emp]
  let initSec := (s0.sp - 8#64) * 1103515245#64
  let R_inv := memRegion (s0.sp - 224#64) 80 ∗ stackAt (s0.sp - 80#64) 64 ∗ SavedRegs0 s0 ∗ cells (s0.sp - 32#64) 3 ∗ R_frame
  rw [hAuxvSplit]
  refine SepWP.cut_at_off (mbase 7) (reloc_call_off% blk07Relocs "memcpy" + 12#64)
    (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + (reloc_call_off% blk07Relocs "memcpy" + 12#64) ∧
      s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 .x0 = st.auxvPtr ∧ s1.readReg64 .x19 = 0#64 ∧
      s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s1.readReg64 .x21 = s0.sp - 8#64 ∧ s1.readReg64 .x22 = maddrs.libc ∧
      Cs23Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (((s0.sp - 8#64) ↦₆₄ initSec) ∗
        (((st.auxvPtr + BitVec.ofNat 64 (16 * 0)) ↦₆₄* (preEntries.flatMap fun (t, v) => [t, v])) ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗
            ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ CtxCells maddrs.ctx st.ctx ∗
            (p_rand ↦₆₄ 25#64) ∗ ((p_rand + 8#64) ↦₆₄ randPtr) ∗
            (p_suf ↦₆₄* (sufEntries.flatMap fun (t, v) => [t, v])) ∗
            (p_null ↦₆₄ 0#64) ∗ ((p_null + 8#64) ↦₆₄ nullVal) ∗
            ((randPtr + 8#64) ↦₆₄ sec) ∗ R_inv)))) hcl ?_) ?_)
  · simp only [Nat.mul_zero, BitVec.add_zero]
    dsimp only [initSec, R_inv, SavedRegs0]
    simp only [BitVec.reduceSub] at hPc
    conv => arg 2; simp only [BitVec.reduceSub, BitVec.reduceAdd]
    wp_sym_steps
    refine Obj.MultiPlacedLib.sepWP_relaxablePair (lib := VerifiedLibraries.mallocngLib) (mpl := mmpl)
      (i := 7) (by decide) (off := 108) (rd := 0#5) (X := fun _ => none) (svc := mallocngFaultSvc)
      MallocngMultiPlacement.placeable rfl rfl (by decide) (by decide)
      (by simp [arm64_norm]) (by simp [arm64_norm, hRun]) ?_
    simp only [resolve_libc, show Obj.addSignedAddr maddrs.libc 0 = maddrs.libc from rfl,
      show BitVec.ofNat 64 (108 + 8) = 116#64 from rfl]
    wp_sym_steps
    have hSp72 : s0.sp - 80#64 + 72#64 = s0.sp - 8#64 := by bv_arith
    simp only [hSp72, hc21_0, hc22_0] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs23_0
    wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    refine SepWP.weaken_pre (Entails.trans hEnt1 (by sep_frame))
      (sepWP_auxv_scan hWords hRange preEntries hPreTags 0 _ s0 s1 hcl1 hPc1 hRun1 hSp1 hx0_1 (by simpa using hx19_1) hx20_1 hx21_1 hx22_1 hCs1 hProc1
        fun s2 hcl2 hPc2 hRun2 hSp2 hx0_2 hx19_2 hx20_2 hx21_2 hx22_2 hCs2 hProc2 hBrk2 hD2 => ?_)
    have hx19_2' : s2.readReg64 .x19 = BitVec.ofNat 64 (16 * preEntries.length) := by simpa using hx19_2
    let retMemcpy := mbase 7 + (reloc_call_off% blk07Relocs "memcpy" + 4#64)
    refine SepWP.cut (mid := mbase 20)
      (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s3 =>
        s3.pc = mbase 20 ∧ s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧
        s3.readReg64 Reg.lr = retMemcpy ∧ s3.readReg64 .x0 = s0.sp - 8#64 ∧ s3.readReg64 .x1 = randPtr + 8#64 ∧ s3.readReg64 .x2 = 8#64 ∧
        s3.readReg64 .x19 = BitVec.ofNat 64 (16 * preEntries.length) ∧ s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧
        s3.readReg64 .x21 = s0.sp - 8#64 ∧ s3.readReg64 .x22 = maddrs.libc ∧
        Cs23Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = s.brk)
        (((s0.sp - 8#64) ↦₆₄ initSec) ∗ ((randPtr + 8#64) ↦₆₄ sec) ∗
          ((st.auxvPtr ↦₆₄* (preEntries.flatMap fun (t, v) => [t, v])) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗
            ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ CtxCells maddrs.ctx st.ctx ∗
            (p_rand ↦₆₄ 25#64) ∗ ((p_rand + 8#64) ↦₆₄ randPtr) ∗
            (p_suf ↦₆₄* (sufEntries.flatMap fun (t, v) => [t, v])) ∗
            (p_null ↦₆₄ 0#64) ∗ ((p_null + 8#64) ↦₆₄ nullVal) ∗ R_inv))) hcl2 ?_) ?_)
    · simp only [Nat.mul_zero, BitVec.add_zero]
      dsimp only [p_rand, retMemcpy, R_inv] at hPc2 ⊢
      wp_sym_steps
      simp only [show ∀ x y : BitVec 64, x + (y - x) = y from fun _ _ => by bv_arith] at *
      obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs2
      rw [← hBrk1, ← hBrk2]
      wp_done
    · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hLr3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx21_3, hx22_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
      refine SepWP.weaken_pre hEnt3 ?_
      have hSpA3 : s3.spAligned = true := by rw [State.spAligned, hSp3]; exact hSpSub
      have hDstFit : (s0.sp - 8#64).toNat + 8 ≤ 2 ^ 64 := by
        by_cases h0 : s0.sp.toNat = 0
        · rw [show s0.sp = 0#64 from BitVec.eq_of_toNat_eq h0]; decide
        · have hMod : s0.sp.toNat % 16 = 0 := by
            have h1 : (s0.sp &&& 15#64).toNat = 0 := by rw [beq_iff_eq.mp hSpA]; rfl
            rw [BitVec.toNat_and] at h1; change s0.sp.toNat &&& (2 ^ 4 - 1) = 0 at h1
            rwa [Nat.and_two_pow_sub_one_eq_mod] at h1
          have := s0.sp.isLt; rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega
      have hSrcFit : (randPtr + 8#64).toNat + 8 ≤ 2 ^ 64 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      refine call_withCL_frame_auto (x := ())
        (placed_memcpy8_mapped_ok (P := mallocngBlockProg mmpl 7 msvc) (s0.sp - 8#64) (randPtr + 8#64) initSec sec hDstFit hSrcFit (by intro pc; simp) rfl)
        hcl3 hPc3 hRun3 hSpA3 hLr3 (fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)) (fun _ _ _ _ h => False.elim (not_satisfies_false_sepConj h)) ?_
      intro s4 hPc4 hRun4 hSp4 hCsCall hcl4
      rw [sepConj_assoc, sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hProcCall, hBrk4, _, hDCall⟩
      have hSp4Eq : s4.sp = s0.sp - 80#64 := hSp4.trans hSp3
      have hx19_4 : s4.readReg64 .x19 = BitVec.ofNat 64 (16 * preEntries.length) := hCsCall.1.trans hx19_3
      have hx20_4 : s4.readReg64 .x20 = Obj.pageOf maddrs.ctx := hCsCall.2.1.trans hx20_3
      have hx21_4 : s4.readReg64 .x21 = s0.sp - 8#64 := hCsCall.2.2.1.trans hx21_3
      have hx22_4 : s4.readReg64 .x22 = maddrs.libc := hCsCall.2.2.2.1.trans hx22_3
      have hCs4 : Cs23Preserved s0 s4 := ⟨hCsCall.2.2.2.2.1.trans hCs3.1, hCsCall.2.2.2.2.2.1.trans hCs3.2.1,
        hCsCall.2.2.2.2.2.2.1.trans hCs3.2.2.1, hCsCall.2.2.2.2.2.2.2.1.trans hCs3.2.2.2.1,
        hCsCall.2.2.2.2.2.2.2.2.1.trans hCs3.2.2.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.1.trans hCs3.2.2.2.2.2.1,
        hCsCall.2.2.2.2.2.2.2.2.2.2.2.trans hCs3.2.2.2.2.2.2⟩
      have hProc4 : MallocngProcPreserved s0 s4 := MallocngProcPreserved.trans hProc3 hProcCall
      refine SepWP.cut_at_off (mbase 7) (reloc_call_off% blk07Relocs "memcpy" + 12#64)
        (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s5 =>
          s5.pc = mbase 7 + (reloc_call_off% blk07Relocs "memcpy" + 12#64) ∧
          s5.status = .Running ∧ s5.sp = s0.sp - 80#64 ∧
          s5.readReg64 .x0 = st.auxvPtr ∧ s5.readReg64 .x19 = BitVec.ofNat 64 (16 * (preEntries.length + 1)) ∧
          s5.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s5.readReg64 .x21 = s0.sp - 8#64 ∧ s5.readReg64 .x22 = maddrs.libc ∧
          Cs23Preserved s0 s5 ∧ MallocngProcPreserved s0 s5 ∧ s5.brk = s.brk)
          ((p_suf ↦₆₄* (sufEntries.flatMap fun (t, v) => [t, v])) ∗
            (((s0.sp - 8#64) ↦₆₄ sec) ∗ ((randPtr + 8#64) ↦₆₄ sec) ∗
              (st.auxvPtr ↦₆₄* (preEntries.flatMap fun (t, v) => [t, v])) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗
              ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ CtxCells maddrs.ctx st.ctx ∗
              (p_rand ↦₆₄ 25#64) ∗ ((p_rand + 8#64) ↦₆₄ randPtr) ∗
              (p_null ↦₆₄ 0#64) ∗ ((p_null + 8#64) ↦₆₄ nullVal) ∗ R_inv))) hcl4 ?_) ?_)
      · dsimp only [retMemcpy] at hPc4
        dsimp only [R_inv]
        have hPreNext : BitVec.ofNat 64 (16 * preEntries.length) + 16#64 = BitVec.ofNat 64 (16 * (preEntries.length + 1)) := by
          rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add, show 16 * preEntries.length + 16 = 16 * (preEntries.length + 1) by omega]
        conv => arg 2; simp only [BitVec.reduceAdd]
        wp_sym_steps
        simp only [hPreNext] at *
        obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc4; obtain ⟨hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs4
        rw [← hBrk3, ← hBrk4]
        wp_done
      · intro s5 P5 hPc5 hRun5 ⟨_, hD5, hcl5, ⟨_, _, hSp5, hx0_5, hx19_5, hx20_5, hx21_5, hx22_5, hCs5, hProc5, hBrk5⟩, hEnt5⟩
        refine SepWP.weaken_pre hEnt5
          (sepWP_auxv_scan hWords hRange sufEntries hSufTags (preEntries.length + 1) _ s0 s5 hcl5 hPc5 hRun5 hSp5 hx0_5 hx19_5 hx20_5 hx21_5 hx22_5 hCs5 hProc5
            fun s6 hcl6 hPc6 hRun6 hSp6 hx0_6 hx19_6 hx20_6 hx21_6 hx22_6 hCs6 hProc6 hBrk6 hD6 => ?_)
        refine SepWP.cut_at_off (mbase 7) (words_insn_off% blk07Words "cbz" 0 + 4#64)
          (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s7 =>
            s7.pc = mbase 7 + (words_insn_off% blk07Words "cbz" 0 + 4#64) ∧
            s7.status = .Running ∧ s7.sp = s0.sp - 80#64 ∧ s7.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧
            Cs21Preserved s0 s7 ∧ MallocngProcPreserved s0 s7 ∧ s7.brk = s.brk)
            ((((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ (((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗ (cells (s0.sp - 32#64) 3 ∗ ((s0.sp - 8#64) ↦₆₄ sec)))) ∗
              (CtxCells maddrs.ctx { st.ctx with secret := sec, initDone := 1#32 } ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
                ((st.auxvPtr ↦₆₄* (preEntries.flatMap fun (t, v) => [t, v])) ∗
                  (p_rand ↦₆₄ 25#64) ∗ ((p_rand + 8#64) ↦₆₄ randPtr) ∗
                  (p_suf ↦₆₄* (sufEntries.flatMap fun (t, v) => [t, v])) ∗
                  (p_null ↦₆₄ 0#64) ∗ ((p_null + 8#64) ↦₆₄ nullVal)) ∗
                ((randPtr + 8#64) ↦₆₄ sec) ∗
                (memRegion (s0.sp - 224#64) 80 ∗ stackAt (s0.sp - 80#64) 64 ∗ SavedRegs0 s0 ∗ R_frame)))) hcl6 ?_) ?_)
        · dsimp only [p_suf, p_null, R_inv, CtxCells, ctxMiddleBytes]
          conv => arg 2; simp only [BitVec.reduceAdd]
          wp_sym_steps
          obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc6; obtain ⟨hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs6
          rw [← hBrk5, ← hBrk6]
          wp_done
        · intro s7 P7 hPc7 hRun7 ⟨_, hD7, hcl7, ⟨_, _, hSp7, hx20_7, hCs7, hProc7, hBrk7⟩, hEnt7⟩
          have hCellsFold : (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ (((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗ (cells (s0.sp - 32#64) 3 ∗ ((s0.sp - 8#64) ↦₆₄ sec)))) ⊢ cells (s0.sp - 48#64) 6 := by
            rw [cells_split_sub s0.sp 48 32 2 4, cells_split_sub s0.sp 32 8 3 1, ← sepConj_assoc]
            refine sepConj_mono (cells_sub_succ_entails 48 2 (by simpa [cells_zero, sepConj_emp] using cells_sub_succ_entails (sp := s0.sp) (v := s0.readReg64 .x22) 40 1 (Entails.refl _))) ?_
            exact sepConj_mono_right (by simpa [cells_zero, sepConj_emp] using cells_sub_succ_entails (sp := s0.sp) (v := sec) 8 1 (Entails.refl _))
          have hAuxvPack : ((st.auxvPtr ↦₆₄* (preEntries.flatMap fun (t, v) => [t, v])) ∗
              (p_rand ↦₆₄ 25#64) ∗ ((p_rand + 8#64) ↦₆₄ randPtr) ∗
              (p_suf ↦₆₄* (sufEntries.flatMap fun (t, v) => [t, v])) ∗
              (p_null ↦₆₄ 0#64) ∗ ((p_null + 8#64) ↦₆₄ nullVal)) ∗ ((randPtr + 8#64) ↦₆₄ sec) ⊢
              ((st.auxvPtr ↦₆₄* ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v])) ∗
                ((randPtr + 8#64) ↦₆₄ sec)) := by
            rw [← hAuxvSplit]; exact Entails.refl _
          have hDTot : MallocngMappedDelta 0 0 s.mem s7.mem :=
            MallocngMappedDelta.mono (by decide) (by decide)
              (MallocngMappedDelta.trans (MallocngMappedDelta.trans (MallocngMappedDelta.trans (MallocngMappedDelta.trans (MallocngMappedDelta.trans (MallocngMappedDelta.trans hD1 hD2) hD3) hDCall) hD5) hD6) hD7)
          have hAuxvRest : ((st.auxvPtr ↦₆₄* (preEntries.flatMap fun (t, v) => [t, v])) ∗
              (p_rand ↦₆₄ 25#64) ∗ ((p_rand + 8#64) ↦₆₄ randPtr) ∗
              (p_suf ↦₆₄* (sufEntries.flatMap fun (t, v) => [t, v])) ∗
              (p_null ↦₆₄ 0#64) ∗ ((p_null + 8#64) ↦₆₄ nullVal)) ∗
              (((randPtr + 8#64) ↦₆₄ sec) ∗ (memRegion (s0.sp - 224#64) 80 ∗ stackAt (s0.sp - 80#64) 64 ∗ SavedRegs0 s0 ∗ R_frame)) ⊢
              ((st.auxvPtr ↦₆₄* ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v])) ∗
                ((randPtr + 8#64) ↦₆₄ sec)) ∗ (memRegion (s0.sp - 224#64) 80 ∗ stackAt (s0.sp - 80#64) 64 ∗ SavedRegs0 s0 ∗ R_frame) := by
            rw [← sepConj_assoc]; exact sepConj_mono_left hAuxvPack
          refine SepWP.weaken_pre (Entails.trans hEnt7 (Entails.trans (sepConj_mono hCellsFold (sepConj_mono_right (sepConj_mono_right hAuxvRest))) ?_))
            (hCont s7 hcl7 hPc7 hRun7 hSp7 hx20_7 hCs7 hProc7 hBrk7 hDTot)
          unfold StackFrameOpen SavedRegs0; sep_frame

theorem sepWP_lazyInit_05c [MallocngMultiPlacement]
    {γ : GhostName} {target_pc : BitVec 64} {st : MallocngSt} {R_frame : SepProp} {s0 s : State}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hWords0 : Blk07HasWords0 mallocngFaultSvc)
    (hWords : Blk07HasWords116 mallocngFaultSvc)
    (hRange : Blk07Range116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (reloc_call_off% blk07Relocs "memcpy" - 68#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx)
    (hCs21 : Cs21Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hCont : ∀ (s_out : State) (sec : BitVec 64),
      VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_out.mem →
      s_out.pc = mbase 7 + (words_insn_off% blk07Words "cbz" 0 + 4#64) →
      s_out.status = .Running → s_out.sp = s0.sp - 80#64 →
      s_out.readReg64 .x20 = Obj.pageOf maddrs.ctx →
      Cs21Preserved s0 s_out → MallocngProcPreserved s0 s_out → s_out.brk = s.brk →
      MallocngMappedDelta 0 0 s.mem s_out.mem →
      SepWP (mallocngBlockProg mmpl 7 msvc) target_pc s_out
        (StackFrameOpen s0 ∗ CtxCells maddrs.ctx { st.ctx with secret := sec, initDone := 1#32 } ∗
          ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗ R_frame) post oom) :
    SepWP (mallocngBlockProg mmpl 7 msvc) target_pc s
      (StackFrameOpen s0 ∗ CtxCells maddrs.ctx st.ctx ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗ R_frame) post oom := by
  unfold MallocngAuxvState
  rcases hSnap : st.auxvSnap with _ | ⟨preEntries, randPtr, sufEntries, nullVal, sec⟩
  · dsimp only; unfold MallocngAuxvAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro preEntries; apply SepWP.exists_elim; intro sufEntries
    apply SepWP.exists_elim; intro randPtr; apply SepWP.exists_elim; intro nullVal
    apply SepWP.exists_elim; intro secretBytes
    simp only [sepConj_assoc, show ∀ (P : SepProp) (φ : Prop) (Q : SepProp), P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) from
      fun P _ _ => by rw [← sepConj_assoc, sepConj_comm P, sepConj_assoc]]
    apply SepWP.pure_elim; rintro ⟨hPreTags, hSufTags, hLen64, hAuxvFit, hRandFit, hSecLen⟩
    let sec := pack64 (secretBytes.getD 0 0#8) (secretBytes.getD 1 0#8) (secretBytes.getD 2 0#8) (secretBytes.getD 3 0#8)
      (secretBytes.getD 4 0#8) (secretBytes.getD 5 0#8) (secretBytes.getD 6 0#8) (secretBytes.getD 7 0#8)
    have hSecEq : ((randPtr + 8#64) ↦ₛ secretBytes) = ((randPtr + 8#64) ↦₆₄ sec) := by
      have hdt : (secretBytes.drop 0).take 8 = secretBytes := by rw [List.drop_zero, List.take_of_length_le (by omega)]
      simpa only [hdt] using pointsToBytes_take8_eq_pointsTo64 (randPtr + 8#64) secretBytes 0 (by omega)
    refine SepWP.weaken_pre (P' := StackFrameOpen s0 ∗ CtxCells maddrs.ctx st.ctx ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
        ((st.auxvPtr ↦₆₄* ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v])) ∗
          ((randPtr + 8#64) ↦₆₄ sec)) ∗
        (ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap st.auxvPtr none) ∗ R_frame))
      (by rw [hSecEq]; sep_frame) ?_
    refine sepWP_lazyInit_05c_concrete ⟨hPreTags, hSufTags, hLen64, hAuxvFit, hRandFit⟩
      hWords0 hWords hRange hcl hPc hRun hSp hSp0 hx20 hCs21 hProc (fun s_out hcl' hPc' hRun' hSp' hx20' hCs' hProc' hBrk' hD' => ?_)
    refine SepWP.weaken_pre ?_ (hCont s_out sec hcl' hPc' hRun' hSp' hx20' hCs' hProc' hBrk' hD')
    have hPackNone :
        ((st.auxvPtr ↦₆₄* ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v])) ∗
          ((randPtr + 8#64) ↦₆₄ sec)) ⊢ MallocngAuxvAt st.auxvPtr := by
      rw [← hSecEq]; unfold MallocngAuxvAt
      exact Entails.sepExists_right preEntries (Entails.sepExists_right sufEntries (Entails.sepExists_right randPtr
        (Entails.sepExists_right nullVal (Entails.sepExists_right secretBytes
          (Entails.pure_right ⟨hPreTags, hSufTags, hLen64, hAuxvFit, hRandFit, hSecLen⟩ (Entails.refl _))))))
    unfold MallocngAuxvState; rw [hSnap]; dsimp only
    exact Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hPackNone)))) (by sep_frame)
  · dsimp only
    simp only [sepConj_assoc, show ∀ (P : SepProp) (φ : Prop) (Q : SepProp), P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) from
      fun P _ _ => by rw [← sepConj_assoc, sepConj_comm P, sepConj_assoc]]
    apply SepWP.pure_elim; intro hConcreteWf
    refine SepWP.weaken_pre (P' := StackFrameOpen s0 ∗ CtxCells maddrs.ctx st.ctx ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
        ((st.auxvPtr ↦₆₄* ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v])) ∗
          ((randPtr + 8#64) ↦₆₄ sec)) ∗
        (ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap st.auxvPtr (some (preEntries, randPtr, sufEntries, nullVal, sec))) ∗ R_frame))
      (by sep_frame) ?_
    refine sepWP_lazyInit_05c_concrete hConcreteWf
      hWords0 hWords hRange hcl hPc hRun hSp hSp0 hx20 hCs21 hProc (fun s_out hcl' hPc' hRun' hSp' hx20' hCs' hProc' hBrk' hD' => ?_)
    refine SepWP.weaken_pre ?_ (hCont s_out sec hcl' hPc' hRun' hSp' hx20' hCs' hProc' hBrk' hD')
    unfold MallocngAuxvState; rw [hSnap]; dsimp only
    rw [pure_sepConj_of_true hConcreteWf]; sep_frame

theorem sepWP_fastPath1_028 [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {st : MallocngSt} {fm0 : FreeMetaDesc} {rest : List FreeMetaDesc} {errnoVal : BitVec 32} {s0 s : State} {oom : State → SepProp}
    (hWords0 : Blk07HasWords0 mallocngFaultSvc)
    (hWords : Blk07HasWords116 mallocngFaultSvc)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (words_insn_off% blk07Words "cbz" 0 + 16#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = maddrs.ctx) (hx19 : s.readReg64 .x19 = fm0.ptr)
    (hCs21 : Cs21Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem s.mem)
    (hWf : MallocngWFInflight inflight maddrs.base brkStart s.brk liveCost peakCost st) (hFmEq : st.freeMetas = fm0 :: rest) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          CtxCells maddrs.ctx st.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st))))
      (AllocMetaPlacedPost inflight γ tp brkStart liveCost peakCost peakCount st s0) oom := by
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
    refine SepWP.cut_at_off (mbase 7) epOff (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + epOff ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 .x19 = fm0.ptr ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (CtxCells maddrs.ctx st'.ctx ∗ (fm0.ptr ↦₆₄ fm0.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm0.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ R_inv)) hcl ?_) ?_)
    · dsimp only [epOff, st', CtxCells, ctxMiddleBytes]
      conv => arg 2; simp only [BitVec.reduceSub]
      wp_sym_steps; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      have hDTot : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by omega) (MallocngMappedDelta.trans hDelta hD1)
      refine SepWP.weaken_pre (Entails.trans hEnt1 ?_)
        (sepWP_epilogue_278 (st' := st') (w0 := fm0.ptr) (w1 := fm0.ptr) (errnoVal := errnoVal) hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hCs1 hProc1 hDTot hmProps (hBrk1 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
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
    refine SepWP.cut_at_off (mbase 7) epOff (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + epOff ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 .x19 = fm0.ptr ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (CtxCells maddrs.ctx st'.ctx ∗ (fm0.ptr ↦₆₄ fm1.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ ((fm1.ptr ↦₆₄ fm1.ptr) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) ∗ R_mid ∗ R_inv)) hcl ?_) ?_)
    · dsimp only [epOff, st', CtxCells, ctxMiddleBytes]
      rw [hLinks.1]; conv => arg 2; simp only [BitVec.reduceSub]
      wp_sym_steps; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      have hDTot : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by omega) (MallocngMappedDelta.trans hDelta hD1)
      have hPack1 : ((fm1.ptr ↦₆₄ fm1.ptr) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.ptr) ∗ ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) = (fm1.ptr ↦ₛ fm1'.toBytes) := (freeMeta_toBytes_eq_cells fm1').symm
      refine SepWP.weaken_pre (Entails.trans hEnt1 ?_)
        (sepWP_epilogue_278 (st' := st') (w0 := fm1.ptr) (w1 := fm1.ptr) (errnoVal := errnoVal) hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hCs1 hProc1 hDTot hmProps (hBrk1 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
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
    refine SepWP.cut_at_off (mbase 7) epOff (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + epOff ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 .x19 = fm0.ptr ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (CtxCells maddrs.ctx st'.ctx ∗ (fm0.ptr ↦₆₄ fmLast.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ ((fm1.ptr ↦₆₄ fmLast.ptr) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.next) ∗
        ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) ∗ (((fmLast.ptr ↦₆₄ fmLast.prev) ∗ ((fmLast.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fmLast.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) ∗ R_mid) ∗ R_inv)) hcl ?_) ?_)
    · dsimp only [epOff, st', CtxCells, ctxMiddleBytes]
      rw [hLinks.1]; conv => arg 2; simp only [BitVec.reduceSub]
      wp_sym_steps; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      have hDTot : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by omega) (MallocngMappedDelta.trans hDelta hD1)
      have hPack1 : ((fm1.ptr ↦₆₄ fmLast.ptr) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.next) ∗ ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) = (fm1.ptr ↦ₛ fm1'.toBytes) := (freeMeta_toBytes_eq_cells fm1').symm
      have hPackL : ((fmLast.ptr ↦₆₄ fmLast.prev) ∗ ((fmLast.ptr + 8#64) ↦₆₄ fm1.ptr) ∗ ((fmLast.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) = (fmLast.ptr ↦ₛ fmLast'.toBytes) := (freeMeta_toBytes_eq_cells fmLast').symm
      refine SepWP.weaken_pre (Entails.trans hEnt1 ?_)
        (sepWP_epilogue_278 (st' := st') (w0 := fmLast.ptr) (w1 := fm1.ptr) (errnoVal := errnoVal) hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hCs1 hProc1 hDTot hmProps (hBrk1 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
      rw [hPack1, hPackL, ← sepConj_assoc (fm1.ptr ↦ₛ fm1'.toBytes), hRwAbs]; dsimp only [R_inv, st']; rw [← hPnEq, ← hMpEq]; sep_frame

end VerifiedLibraries.Mallocng.Proofs
