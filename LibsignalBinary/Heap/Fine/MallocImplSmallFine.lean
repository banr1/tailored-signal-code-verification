/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.MallocImplJoinFine
public import LibsignalBinary.Heap.Fine.MallocImplSmallSteps
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Fine-Grained Small and Medium `__libc_malloc_impl` Branch

Verifies the small/medium branch (`req ≤ MmapThresholdReq = 131,051`, `+0x03c → ret`) of placed
`__libc_malloc_impl` (`blk09`), returning `MallocImplFineRawSuccessPost`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Small and Medium Allocation Branch -/

set_option maxHeartbeats 400000 in
theorem mallocImpl_allocSlot_slow_raw_fine [MallocngMultiPlacement]
    {γ : GhostName} {tp brkStart : BitVec 64} {b : FineBudget} {bud : MallocngBudget}
    {ivs0 : List (BitVec 64 × Nat)} {alignMap0 : BitVec 64 → Option Nat}
    {req sc : Nat} {st0 : MallocngSt} {s0 s : State}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0)
    (hSmall : req ≤ MmapThresholdReq)
    (hReqMax : req ≤ MallocngMaxAllocSize)
    (hSc48 : sc < 48)
    (hScAlt : sc = sizeToClassUnits ((req + 3) / 16) ∨
      sc = coarseAlt (sizeToClassUnits ((req + 3) / 16)))
    (hFitSc : req ≤ nominalSlotCap sc)
    (hSc2 : 2 ≤ sc ∧ sc < 48 → nominalSlotCap (sc - 2) < max req 16)
    (hSc24 : sc = 24 → nominalSlotCap 23 < req)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hPerm0 : s.mem.perm = s0.mem.perm)
    (hpc : s.pc = mbase 9 + miOff_alloc_prep) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx19 : s.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx24 : s.readReg64 (.gpr 24#5) = pageOf maddrs.lock)
    (hx25 : s.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ MallocImplFineRawSuccessPost γ tp brkStart b ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜FineStepOomCond msvc (fineStepReserve (.alloc req) b) s0 sf⌝) := by
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b9 at hpc ⊢
  have hb : BlkBase 9 b9 := hb_eq.symm
  have hReqLt64 : req < 2 ^ 64 := by
    have := mallocngMaxAllocSize_eq; omega
  have hSpAl : s.spAligned = true := by
    dsimp [State.spAligned]; rw [hsp]; exact sp_sub_80_aligned hsp_align
  have hDepth3 := allocSlotDepthBound_le_three sc
  have hDepthLe6 : 0 + allocSlotDepthBound sc ≤ 6 := by omega
  let stkNeed := (allocSlotDepthBound sc + 1) * 96 + 224
  have hStkLe : stkNeed ≤ 624 := by dsimp [stkNeed]; omega
  have hGroups0 : st0.groups.length ≤ fineMaxGroups b := groups_fine_length_le hwf0 hInv0
  have hMeta0 : st0.metaAreas.length ≤ fineMaxMetaAreas b := hInv0.metaAreas_le
  have hMetaStep : 1 + (7 + fineMaxGroups b) / 101 ≤ fineMaxMetaAreas b := Nat.le_refl _
  have hNoRes0 : st0.reservedMetas = [] := by
    have hInf := hwf0.inflight_wf
    cases hR : st0.reservedMetas with
    | nil => rfl
    | cons _ _ => rw [hR] at hInf; simp at hInf
  dsimp only [miOff_alloc_prep] at hpc
  wp_steps 3
  have hSlotCall := call_placed_allocSlot_trace
    (P := blkPC_b09.rebase b9 (fun _ => none))
    allocMeta_fine_param_ok rootSizeSelect_fine_param_ok
    sc req 0 hSc48 hFitSc hDepthLe6 (fineBaseGam γ) tp brkStart
    bud.liveCost bud.peakCost (fineMaxGroups b) (fineMaxMetaAreas b) st0
    hGroups0 hMeta0 hMetaStep
  rw [at_bl_target_b09_fine hb 8 miOff_call_slot] at hSlotCall
  let slotFrame :=
    stackFrameAt ((s0.sp - 80#64) - BitVec.ofNat 64 stkNeed) (624 - stkNeed) ∗
    MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
    ghostMapAuth (fineAlignGam γ) alignMap0
  refine SepWP.call_subroutine_frame (F := slotFrame) (x := ()) (ret_pc := b9 + miOff_after_slot)
    hSlotCall rfl
    (by simp [arm64_norm, hrun])
    (by simpa [State.spAligned, arm64_norm] using hSpAl)
    (by dsimp only [miOff_call_slot, miOff_after_slot, Reg.lr]; simp [arm64_norm])
    (fun R' hm => by
      refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
      dsimp only [withCL, slotFrame]
      rw [stackFrame_eq_stackFrameAt_fine stkNeed (by omega) (by simpa [arm64_norm] using hsp),
          stackFrameAt_624_eq_fine (s0.sp - 80#64) stkNeed hStkLe]
      simp only [sepConj_assoc]
      refine Entails.pure_right
        ⟨by simpa [arm64_norm] using hProc.2.2.1.trans htp0,
         by simpa [arm64_norm] using hProc.2.2.2.1.trans hbrkS0,
         by simp [arm64_norm]; omega,
         by simp [arm64_norm]; exact hReqLt64⟩ ?_
      have hPureCL : (emp : SepProp) ⊢ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem⌝ := by
        simpa [sepConj_emp] using Entails.pure_right hcl (Entails.refl emp)
      refine Entails.trans (Entails.trans (Entails.of_eq (emp_sepConj _).symm) (sepConj_mono_left hPureCL)) (Entails.of_eq ?_)
      dsimp only [State.setPC, State.writeReg64]
      generalize ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem⌝ = pCL,
        stackFrameAt (s0.sp - 80#64) stkNeed = pS1,
        stackFrameAt ((s0.sp - 80#64) - BitVec.ofNat 64 stkNeed) (624 - stkNeed) = pS2,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRoTablesA maddrs = pRo,
        ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
        MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s.brk bud.liveCost bud.peakCost st0 = pCr,
        MallocngRuntime maddrs tp = pRt
      ac_rfl)
    (fun R' sf _ hp => by dsimp only [withCL] at hp; exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by dsimp only [withCL] at he; exact not_satisfies_false_sepConj he)
    (fun sm hpc_m hrun_m hsp_m hcs_m => ?_)
    (fun R' sf _ hoom => by
      dsimp only [withCL] at hoom
      rw [satisfies_pure_sepConj] at hoom
      refine Satisfies.pure_intro
        (fineStepOomCond_of_allocSlot ?_ hPerm0 hoom.1)
        (Satisfies.drop_left hoom.2)
      dsimp only [MallocngProcPreserved] at hProc ⊢
      simp [arm64_norm, hProc])
  dsimp only [withCL]
  rw [sepConj_assoc, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro st1
  rw [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro idx
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  rintro ⟨hProc_m0, hRes1, hLiveMap1, _hEff1, _hCnt1, hMetaLen1, _hActBelow, hx0_m, hIdx31,
    ⟨g, hg1, hAct1, hIdxLt, hGsc, hFitG, hMetaEq, hClaimed1, hZeroMm1⟩, hTrace, hNoOrph_st, hDelta_m⟩
  have hsp_sm : sm.sp = s0.sp - 80#64 := by simpa [arm64_norm] using hsp_m.trans hsp
  rw [stackFrame_eq_stackFrameAt_fine stkNeed (by omega) (by simpa [arm64_norm] using hsp)]
  let coreRest1 :=
    MallocngLiveAuth (fineBaseGam γ) st1.liveMap ∗
    (maddrs.lock ↦₃₂ 0#32) ∗
    (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗
    ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗
    MallocngAuxvState (fineBaseGam γ) st1.auxvPtr st1.auxvSnap ∗
    ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
    MappedSet st1.masterDom (OwnedMappedByte st1)
  have hPullAll :
      ((stackFrameAt (s0.sp - 80#64) stkNeed ∗ MallocngRoTablesA maddrs ∗
        MallocngRuntime maddrs tp ∗
        MallocngCoreStInflightA 1 (fineBaseGam γ) maddrs brkStart sm.brk bud.liveCost bud.peakCost st1) ∗
       ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗ slotFrame) =
      (⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
       ⌜MallocngWFInflight 1 maddrs.base brkStart sm.brk bud.liveCost bud.peakCost st1⌝ ∗
       ((maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗
        (coreRest1 ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
         MallocngRuntime maddrs tp))) := by
    dsimp only [slotFrame, MallocngCoreStInflightA, coreRest1]
    rw [stackFrameAt_624_eq_fine (s0.sp - 80#64) stkNeed hStkLe]
    generalize ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ = pCL,
      ⌜MallocngWFInflight 1 maddrs.base brkStart sm.brk bud.liveCost bud.peakCost st1⌝ = pWf1,
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx,
      MallocngLiveAuth (fineBaseGam γ) st1.liveMap = pGm,
      ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
      (maddrs.lock ↦₃₂ 0#32) = pLk,
      (maddrs.replaced ↦₃₂ 0#32) = pRp,
      (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
      ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = pLb8,
      MallocngAuxvState (fineBaseGam γ) st1.auxvPtr st1.auxvSnap = pAx,
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal = pRw,
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
      MappedSet st1.masterDom (OwnedMappedByte st1) = pMs,
      stackFrameAt (s0.sp - 80#64) stkNeed = pS1,
      stackFrameAt ((s0.sp - 80#64) - BitVec.ofNat 64 stkNeed) (624 - stkNeed) = pS2,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      MallocngRoTablesA maddrs = pRo,
      MallocngRuntime maddrs tp = pRt
    ac_rfl
  rw [hPullAll]
  apply SepWP.pure_elim; intro hcl_m
  apply SepWP.pure_elim; intro hwf1
  obtain ⟨hActLen1, hUseLen1, hUnmLen1, hBncLen1, hPadLen1, _⟩ := hwf1.ctx_lens
  have hPadLen1_7 : st1.ctx.seqPad.length = 7 := by rw [hPadLen1]; rfl
  have hCtxOps1 := ctxBytes_ops st1.ctx hActLen1 hUseLen1 hUnmLen1 hBncLen1 hPadLen1_7
  have hCtxLen1 : st1.ctx.toBytes.length = 928 := by
    have hFL : ∀ xs : List (BitVec 64), (xs.flatMap unpack64).length = 8 * xs.length := fun xs => by
      induction xs with | nil => rfl | cons _ _ ih => simp [ih]; omega
    simp [CtxFields.toBytes, hFL, hActLen1, hUseLen1, hUnmLen1, hBncLen1, hPadLen1_7]
  have hGetAct1 := hCtxOps1.2.2.1 sc hSc48
  have hGetMmc1 := hCtxOps1.1
  clear hCtxOps1
  generalize hCtx1Gen : st1.ctx.toBytes = ctx1Bs at hCtxLen1 hGetAct1 hGetMmc1 ⊢
  have ⟨hc19, hc20, _, _, _, hc24, hc25, _⟩ := hcs_m
  have hx19_sm : sm.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc := by
    simpa [arm64_norm] using hc19.trans (by simp [arm64_norm, hx19])
  have hx20_sm : sm.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req := by
    simpa [arm64_norm] using hc20.trans (by simp [arm64_norm, hx20])
  have hx24_sm : sm.readReg64 (.gpr 24#5) = pageOf maddrs.lock := by
    simpa [arm64_norm] using hc24.trans (by simp [arm64_norm, hx24])
  have hProc_sm : MallocngProcPreserved s0 sm := by
    refine procPres_trans ?_ hProc_m0
    dsimp only [MallocngProcPreserved] at hProc ⊢
    simp [arm64_norm, hProc]
  have hcsHi_sm : MallocImplUntouchedCS s0 sm :=
    untouchedCS_of_calleeSaved_fine
      (untouchedCS_step hcsHi rfl rfl rfl rfl)
      hcs_m
  obtain ⟨hBit31_g, hBit31_e, hZIdx⟩ := bit31_false_of_readReg32_ofNat_fine hx0_m hIdx31
  obtain ⟨hExtSc3, hShlSc3⟩ := sc_sxtw_shl3_bv_fine hSc48
  have hSxMSc := sxtw_sbfm_ofNat hSc48
  have hZ32 : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 idx)) = BitVec.ofNat 64 idx := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have hIdxB31 : (BitVec.ofNat 64 idx).getLsbD 31 = false := by
    have hAll : (List.range 32).all (fun k => decide ((BitVec.ofNat 64 k).getLsbD 31 = false)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr (by omega)))
  refine SepWP.seq (mid := b9 + miOff_slot_ldr22)
    (Mid := fun s2 P2 =>
      (s2.sp = s0.sp - 80#64 ∧ s2.brk = sm.brk ∧ s2.mem = sm.mem ∧
       MallocngProcPreserved s0 s2 ∧ MallocImplUntouchedCS s0 s2 ∧
       s2.readReg64 (.gpr 2#5) = maddrs.ctx + BitVec.ofNat 64 (8 * sc) ∧
       s2.readReg64 (.gpr 19#5) = BitVec.zeroExtend 64 st1.ctx.mmapCounter ∧
       s2.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
       s2.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx ∧
       s2.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx ∧
       s2.readReg64 (.gpr 24#5) = pageOf maddrs.lock) ∧
      (P2 ⊢ (maddrs.ctx ↦ₛ ctx1Bs) ∗
        (coreRest1 ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
         MallocngRuntime maddrs tp))) ?_ ?_
  · dsimp only [miOff_after_slot, miOff_slot_ldr22] at hpc_m ⊢
    dsimp only [Reg.x0] at hBit31_g hBit31_e hZIdx
    wp_steps
    apply SepWP.done
    · simp
    · simp [hrun_m]
    · refine ⟨⟨by simp [hsp_sm], rfl, rfl,
        by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc_sm,
        untouchedCS_step hcsHi_sm (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
        by simp [arm64_norm],
        by simp [arm64_norm],
        by simpa using hx20_sm,
        by simp only [arm64_norm, BitVec.ushiftRight_zero]; rw [and_u32_eq_zeroExtend_truncate_fine, hZ32, BitVec.or_zero],
        by simp only [arm64_norm],
        by simpa using hx24_sm⟩, Entails.refl _⟩
  · rintro s2 P2 hpc2 hrun2 ⟨⟨hsp2, hbrk2, hmem2, hProc2, hcs2, hx2_2, hx19_2, hx20_2, hx21_2, hx23_2, hx24_2⟩, hP2⟩
    apply SepWP.weaken_pre hP2
    have hAddr80 : (maddrs.ctx + BitVec.ofNat 64 (8 * sc)) + 80#64 =
        maddrs.ctx + BitVec.ofNat 64 (80 + 8 * sc) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine SepWP.step_ldr64
      (s' := (s2.writeReg64 (.gpr 22#5) g.metaPtr).setPC (b9 + miOff_slot_b19c))
      hpc2 hrun2 (by dsimp only [miOff_slot_ldr22]; simp only [arm64_norm]; rfl) rfl
      (ea := maddrs.ctx + BitVec.ofNat 64 (80 + 8 * sc)) (wb := none)
      (by simp [evalAddrMode, hx2_2, hAddr80])
      (SepLoad64.of_pointsToBytes rfl (by omega) rfl)
      (by simp only [applyWriteback, hGetAct1, ← hMetaEq, BitVec.add_assoc]; rfl) ?_
    refine SepWP.seq (mid := b9 + miOff_call_unlock)
      (Mid := fun s_u P_u =>
        (s_u.sp = s0.sp - 80#64 ∧ s_u.brk = sm.brk ∧ s_u.mem = sm.mem ∧
         MallocngProcPreserved s0 s_u ∧ MallocImplUntouchedCS s0 s_u ∧
         s_u.readReg64 (.gpr 0#5) = maddrs.lock ∧
         s_u.readReg64 (.gpr 19#5) = BitVec.zeroExtend 64 st1.ctx.mmapCounter ∧
         s_u.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
         s_u.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx ∧
         s_u.readReg64 (.gpr 22#5) = g.metaPtr ∧
         s_u.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) ∧
        (P_u ⊢ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
          MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
          MallocngCoreStInflightA 1 (fineBaseGam γ) maddrs brkStart sm.brk bud.liveCost bud.peakCost st1 ∗
          MallocngRuntime maddrs tp)) ?_ ?_
    · dsimp only [miOff_slot_b19c, miOff_call_unlock]
      wp_steps
      apply SepWP.done
      · simp
      · simp [hrun2]
      · refine ⟨⟨by simp [hsp2], hbrk2, hmem2,
          by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_writeReg64); exact hProc2,
          untouchedCS_step hcs2 (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
          by simp [arm64_norm],
          by simpa using hx19_2,
          by simpa using hx20_2,
          by simpa using hx21_2,
          by simp [arm64_norm, hMetaEq],
          by simpa using hx23_2⟩, Entails.of_eq ?_⟩
        rw [← hCtx1Gen]
        dsimp only [MallocngCoreStInflightA, coreRest1]
        rw [propext ⟨fun _ => trivial, fun _ => hwf1⟩, pure_true, emp_sepConj]
        generalize (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx,
          MallocngLiveAuth (fineBaseGam γ) st1.liveMap = pGm,
          ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
          (maddrs.lock ↦₃₂ 0#32) = pLk,
          (maddrs.replaced ↦₃₂ 0#32) = pRp,
          (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
          ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = pLb8,
          MallocngAuxvState (fineBaseGam γ) st1.auxvPtr st1.auxvSnap = pAx,
          ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal = pRw,
          ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
          MappedSet st1.masterDom (OwnedMappedByte st1) = pMs,
          MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
          stackFrameAt (s0.sp - 80#64) 624 = pSf,
          MallocngRoTablesA maddrs = pRo,
          MallocngRuntime maddrs tp = pRt
        ac_rfl
    · rintro s_u P_u hpc_u hrun_u ⟨⟨hsp_u, hbrk_u, hmem_u, hProc_u, hcs_u,
        hx0_u, hx19_u, hx20_u, hx21_u, hx22_u, hx23_u⟩, hPu⟩
      apply SepWP.weaken_pre hPu
      have hwf1_u : MallocngWFInflight 1 maddrs.base brkStart s_u.brk bud.liveCost bud.peakCost st1 :=
        hbrk_u ▸ hwf1
      have hcl_u : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_u.mem := hmem_u ▸ hcl_m
      have hNoRes1 : st1.reservedMetas = [] := hRes1.trans hNoRes0
      have hIvs0Eq : ivs0 = dynamicRootRegions st0 := hInv0.ivs_eq rfl
      have hNoOrph1 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s_u.mem :=
        mallocngNoOrphanMappings_congr_perm hIvs0Eq.symm rfl hPerm0 (congrArg Memory.perm hmem_u) hNoOrph_st
      obtain ⟨hCntLe, hByteLe⟩ := allocSlotFineByteBound_le_stepReserve sc req b
      have hDelta_u : MallocngMappedDelta 16 (fineStepReserve (.alloc req) b) s0.mem s_u.mem := by
        obtain ⟨ivsD, hLenD, hSumD, hCovD⟩ := hDelta_m
        exact ⟨ivsD, Nat.le_trans hLenD hCntLe, Nat.le_trans hSumD hByteLe,
          fun a ha => (hCovD a (hmem_u ▸ ha)).imp (fun h => hPerm0 ▸ h) id⟩
      obtain ⟨pk, pkSC, pkSB, hPk⟩ := hInv0.small_witness
      have hInitPres : AllocSlotInvPres sc pk alignMap0 st0 st0 :=
        allocSlotInvPres_of_witness hInv0 hPk sc
      have hPres1 : AllocSlotInvPres sc pk alignMap0 st0 st1 :=
        allocSlotInvPres_of_trace hTrace hSc48 (by omega) hInitPres hPk.2.1 hwf1.groups_nodup.1
      subst hb_eq
      rw [← hbrk_u, ← mallocngBlockProg_eq_b09]
      exact mallocImpl_join_epilogue_raw_fine hcl_u hInv0 hLiveMap1 hMetaLen1 hNoOrph1 hwf1_u hNoRes1
        hg1 hIdxLt hClaimed1 hReqMax hFitG
        (fun h => by rw [hGsc] at h ⊢; exact hSc2 h)
        (fun h => hSc24 (hGsc ▸ h))
        (fun h => by rw [hGsc] at h; omega)
        (fun h => by rw [hGsc] at h; omega)
        hZeroMm1
        (fun p val' liveMap' => by
          rw [dite_eq_left hSmall]
          exact ⟨sc, pk, pkSC, pkSB, st1, g, sm.brk, bud.liveCost, bud.peakCost,
            hSc48, hScAlt, hPk, hPres1, hwf1, hg1, hGsc, ⟨hIdxLt, hClaimed1⟩,
            ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩)
        htp0 hbrkS0 hDelta_u
        hpc_u hrun_u hsp_u hsp_align hProc_u hcs_u
        hx0_u hx19_u hx20_u hx21_u hx22_u hx23_u

set_option maxHeartbeats 400000 in
theorem mallocImpl_tryAvail_or_slow_raw_fine [MallocngMultiPlacement]
    {γ : GhostName} {tp brkStart : BitVec 64} {b : FineBudget} {bud : MallocngBudget}
    {ivs0 : List (BitVec 64 × Nat)} {alignMap0 : BitVec 64 → Option Nat}
    {req sc : Nat} {st0 : MallocngSt} {s0 s : State}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0)
    (hSmall : req ≤ MmapThresholdReq)
    (hReqMax : req ≤ MallocngMaxAllocSize)
    (hSc48 : sc < 48) (hAct : sc < st0.ctx.active.length)
    (hScAlt : sc = sizeToClassUnits ((req + 3) / 16) ∨
      sc = coarseAlt (sizeToClassUnits ((req + 3) / 16)))
    (hFitSc : req ≤ nominalSlotCap sc)
    (hSc2 : 2 ≤ sc ∧ sc < 48 → nominalSlotCap (sc - 2) < max req 16)
    (hSc24 : sc = 24 → nominalSlotCap 23 < req)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hPerm0 : s.mem.perm = s0.mem.perm)
    (hpc : s.pc = mbase 9 + miOff_try_avail) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx19 : s.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx22 : s.readReg64 (.gpr 22#5) = st0.ctx.active[sc]'hAct)
    (hx24 : s.readReg64 (.gpr 24#5) = pageOf maddrs.lock)
    (hx25 : s.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ MallocImplFineRawSuccessPost γ tp brkStart b ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜FineStepOomCond msvc (fineStepReserve (.alloc req) b) s0 sf⌝) := by
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b9 at hpc ⊢
  have hb : BlkBase 9 b9 := hb_eq.symm
  by_cases hActZero : st0.ctx.active[sc]'hAct = 0#64
  · refine tryAvail_cbz_step_fine hb hpc hrun hProc hcsHi (hx22.trans hActZero) ?_
    intro s' hpc' hrun' hsp' hbrk' hmem' hProc' hcs' hx19' hx20' hx24' hx25'
    rw [← hbrk', ← hb_eq, ← mallocngBlockProg_eq_b09]
    exact mallocImpl_allocSlot_slow_raw_fine (hmem' ▸ hcl) hInv0 (by rw [hbrk']; exact hwf0)
      hSmall hReqMax hSc48 hScAlt hFitSc hSc2 hSc24 htp0 hbrkS0 (by rw [hmem']; exact hPerm0)
      (by rwa [hb_eq]) hrun' (hsp'.trans hsp) hsp_align hProc' hcs'
      (hx19'.trans hx19) (hx20'.trans hx20) (hx24'.trans hx24) (hx25'.trans hx25)
  · have hActNe : st0.ctx.active[sc]'hAct ≠ 0#64 := hActZero
    obtain ⟨hActLen, hUseLen, hUnmLen, hBncLen, hPadLen, _⟩ := hwf0.ctx_lens
    have hActL : sc < st0.activeLists.length := by have := hwf0.ctx_lens.2.2.2.2.2; omega
    obtain ⟨g, hg, hMetaEq, hGsc, _⟩ := active_head_group_of_nonzero hwf0 hAct hActL hActNe
    have hMetaNe : g.metaPtr ≠ 0#64 := hMetaEq ▸ hActNe
    have hNoRes0 : st0.reservedMetas = [] := by
      have hInf := hwf0.inflight_wf
      cases hR : st0.reservedMetas with
      | nil => rfl
      | cons _ _ => rw [hR] at hInf; simp at hInf
    have hExt0 := meta_extract hwf0 hNoRes0 hg
    obtain ⟨_, hPkAv, _, _, _, _, hWrAv⟩ :=
      metaBytes_ops g (ctz32DeBruijn g.availMask) (g.availMask - ((-g.availMask) &&& g.availMask)) .claimed
    have hmLen : g.metaBytes.length = 40 := by simp [GroupDesc.metaBytes]
    have hPadLen7 : st0.ctx.seqPad.length = 7 := by rw [hPadLen]; rfl
    have hGetMmc0 := (ctxBytes_ops st0.ctx hActLen hUseLen hUnmLen hBncLen hPadLen7).1
    have hCtxLen0 : st0.ctx.toBytes.length = 928 := by
      have hFL : ∀ xs : List (BitVec 64), (xs.flatMap unpack64).length = 8 * xs.length := fun xs => by
        induction xs with | nil => rfl | cons _ _ ih => simp [ih]; omega
      simp [CtxFields.toBytes, hFL, hActLen, hUseLen, hUnmLen, hBncLen, hPadLen7]
    have hDebLen : mallocngDebruijn32Table.length = 32 := debruijn32Table_length
    generalize hRoOther :
      ((maddrs.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
       (maddrs.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) ∗
       (maddrs.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
       (maddrs.smallCntTab ↦ᵣ mallocngSmallCntTabBytes)) = roOther
    have hRoSplit : MallocngRoTablesA maddrs = ((maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗ roOther) := by
      rw [← hRoOther]
      dsimp only [MallocngRoTablesA, MallocngRoTablesAt]
      generalize (maddrs.sizeClasses ↦ᵣ mallocngSizeClassBytes) = p1,
        (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) = p2,
        (maddrs.medCntTab ↦ᵣ mallocngMedCntTabBytes) = p3,
        (maddrs.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) = p4,
        (maddrs.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) = p5
      ac_rfl
    generalize hCoreTail :
      (MallocngLiveAuth (fineBaseGam γ) st0.liveMap ∗
       (maddrs.lock ↦₃₂ 0#32) ∗
       (maddrs.replaced ↦₃₂ 0#32) ∗
       (maddrs.aaReplaced ↦₃₂ 0#32) ∗
       ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗
       MallocngAuxvState (fineBaseGam γ) st0.auxvPtr st0.auxvSnap ∗
       ByteMap st0.masterDom (fun a => OwnedRwByte st0 a ∧ ¬ InRegion g.metaPtr 40 a) st0.byteVal ∗
       ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∗
       MappedSet st0.masterDom (OwnedMappedByte st0)) = coreTail0
    have hCoreSplit0 :
        MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s.brk bud.liveCost bud.peakCost st0 =
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗ coreTail0) := by
      rw [← hCoreTail]
      have hwf0' : MallocngWFInflight 0 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0 := hwf0
      dsimp only [MallocngCoreStInflightA]
      rw [propext ⟨fun _ => trivial, fun _ => hwf0'⟩, pure_true, emp_sepConj, hExt0]
      generalize (g.metaPtr ↦ₛ g.metaBytes) = pM,
        (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
        MallocngLiveAuth (fineBaseGam γ) st0.liveMap = pGm,
        (maddrs.lock ↦₃₂ 0#32) = pLk,
        (maddrs.replaced ↦₃₂ 0#32) = pRp,
        (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
        ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) = pLb8,
        MallocngAuxvState (fineBaseGam γ) st0.auxvPtr st0.auxvSnap = pAx,
        ByteMap st0.masterDom (fun a => OwnedRwByte st0 a ∧ ¬ InRegion g.metaPtr 40 a) st0.byteVal = pRw,
        ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
        MappedSet st0.masterDom (OwnedMappedByte st0) = pMs
      ac_rfl
    have hPreFocus :
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
         MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
         MallocngRuntime maddrs tp) =
        ((g.metaPtr ↦ₛ g.metaBytes) ∗
         (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
         (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
         (roOther ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗ coreTail0 ∗
          MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 624 ∗ MallocngRuntime maddrs tp)) := by
      rw [hCoreSplit0, hRoSplit]
      generalize (g.metaPtr ↦ₛ g.metaBytes) = pM,
        (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
        (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) = pDeb,
        ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreFocus]
    refine tryAvail_nonnull_step_fine hb hMetaNe hmLen hCtxLen0 hDebLen hPkAv hGetMmc0
      hcl hpc hrun hProc hcsHi (hx22.trans hMetaEq.symm) hx24 hx25 ?_ ?_
    · intro s' hpc' hrun' hsp' hbrk' hmem' hProc' hcs' hx19' hx20' hx24' hx25'
      rw [← hPreFocus, ← hbrk', ← hb_eq, ← mallocngBlockProg_eq_b09]
      exact mallocImpl_allocSlot_slow_raw_fine (hmem' ▸ hcl) hInv0 (by rw [hbrk']; exact hwf0)
        hSmall hReqMax hSc48 hScAlt hFitSc hSc2 hSc24 htp0 hbrkS0 (by rw [hmem']; exact hPerm0)
        (by rwa [hb_eq]) hrun' (hsp'.trans hsp) hsp_align hProc' hcs'
        (hx19'.trans hx19) (hx20'.trans hx20) hx24' hx25'
    · intro hAvNe s_u hcl_u hpc_u hrun_u hsp_u hbrk_u hperm_u hProc_u hcs_u
        hx0_u hx19_u hx20_u hx21_u hx22_u hx23_u
      clear hRoOther hDebLen
      obtain ⟨pk, pkSC, pkSB, hPk⟩ := hInv0.small_witness
      have hInitPres : AllocSlotInvPres sc pk alignMap0 st0 st0 :=
        allocSlotInvPres_of_witness hInv0 hPk sc
      have hPres1 := claimFreeAvail_allocSlotInvPres hwf0 hInitPres hg hAvNe
      obtain ⟨hIdxSlots, hIdx32, hg'Mm, hMetaLen1, _hCnt1, hDynEq1, hwf1, hg'Mem,
        _, hRwAbsorb, hPnEq, hMpEq⟩ := claimFreeAvail_absorb hwf0 hg hAvNe
      have hIdxEq : (mallocngDebruijn32Table.getD (((((-g.availMask) &&& g.availMask) * 0x076be629#32) >>> 27).toNat) 0#8).toNat =
          ctz32DeBruijn g.availMask := rfl
      rw [hIdxEq] at hx21_u hx23_u
      dsimp only at hPres1
      generalize hIdxGen : ctz32DeBruijn g.availMask = idx at hWrAv hIdxSlots hIdx32 hg'Mm hMetaLen1 hDynEq1 hwf1 hg'Mem hRwAbsorb hPnEq hMpEq hx21_u hx23_u hPres1
      let newAvail := g.availMask - ((-g.availMask) &&& g.availMask)
      let g1 := mkReplaceSlotGroup g idx newAvail .claimed
      let val1 := writeBytesToMap st0.byteVal g.metaPtr g1.metaBytes
      let st1 := mkReplaceSlotSt st0 g idx newAvail .claimed val1 st0.liveMap
      have hPostEq :
          ((g.metaPtr ↦ₛ ByteSlice.write32 g.metaBytes 24 (g.availMask - ((-g.availMask) &&& g.availMask))) ∗
           (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗ (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
           (roOther ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗ coreTail0 ∗
            MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
            stackFrameAt (s0.sp - 80#64) 624 ∗ MallocngRuntime maddrs tp)) =
          (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
           MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
           MallocngCoreStInflightA 1 (fineBaseGam γ) maddrs brkStart s_u.brk bud.liveCost bud.peakCost st1 ∗
           MallocngRuntime maddrs tp) := by
        have hCore1Eq :
            MallocngCoreStInflightA 1 (fineBaseGam γ) maddrs brkStart s_u.brk bud.liveCost bud.peakCost st1 =
            ((g.metaPtr ↦ₛ g1.metaBytes) ∗ (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗ coreTail0) := by
          rw [hbrk_u, ← hCoreTail]
          have hwf1' : MallocngWFInflight 1 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st1 := hwf1
          dsimp only [MallocngCoreStInflightA]
          rw [propext ⟨fun _ => trivial, fun _ => hwf1'⟩, pure_true, emp_sepConj]
          dsimp only [st1]
          rw [← hRwAbsorb, ← hPnEq, ← hMpEq]
          dsimp only [mkReplaceSlotSt]
          change (MallocngLiveAuth (fineBaseGam γ) st0.liveMap ∗ (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
            (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
            ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗
            MallocngAuxvState (fineBaseGam γ) st0.auxvPtr st0.auxvSnap ∗
            ((g.metaPtr ↦ₛ g1.metaBytes) ∗
              ByteMap st0.masterDom (fun a => OwnedRwByte st0 a ∧ ¬ InRegion g.metaPtr 40 a) st0.byteVal) ∗
            ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∗
            MappedSet st0.masterDom (OwnedMappedByte st0)) = _
          generalize (g.metaPtr ↦ₛ g1.metaBytes) = pM,
            (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
            MallocngLiveAuth (fineBaseGam γ) st0.liveMap = pGm,
            (maddrs.lock ↦₃₂ 0#32) = pLk,
            (maddrs.replaced ↦₃₂ 0#32) = pRp,
            (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
            ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) = pLb8,
            MallocngAuxvState (fineBaseGam γ) st0.auxvPtr st0.auxvSnap = pAx,
            ByteMap st0.masterDom (fun a => OwnedRwByte st0 a ∧ ¬ InRegion g.metaPtr 40 a) st0.byteVal = pRw,
            ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
            MappedSet st0.masterDom (OwnedMappedByte st0) = pMs
          ac_rfl
        change ((g.metaPtr ↦ₛ ByteSlice.write32 g.metaBytes 24 newAvail) ∗ _) = _
        rw [hWrAv, hCore1Eq, hRoSplit]
        generalize (g.metaPtr ↦ₛ g1.metaBytes) = pM,
          (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
          (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) = pDeb,
          ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
          MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
          stackFrameAt (s0.sp - 80#64) 624 = pSf,
          MallocngRuntime maddrs tp = pRt
        ac_rfl
      rw [hPostEq]
      clear hPostEq hPreFocus hRoSplit hCoreTail hIdxEq hIdxGen
      have hwf1_u : MallocngWFInflight 1 maddrs.base brkStart s_u.brk bud.liveCost bud.peakCost st1 :=
        hbrk_u.symm ▸ hwf1
      have hPerm_u : s_u.mem.perm = s0.mem.perm := hperm_u.trans hPerm0
      have hMetaLe1 : st1.metaAreas.length ≤ fineMaxMetaAreas b := by
        rw [hMetaLen1]; exact hInv0.metaAreas_le
      have hNoOrph1 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s_u.mem :=
        mallocngNoOrphanMappings_of_perm_eq (hDynEq1.trans (hInv0.ivs_eq rfl).symm) hPerm_u
      have hDelta_u : MallocngMappedDelta 16 (fineStepReserve (.alloc req) b) s0.mem s_u.mem :=
        ⟨[], Nat.zero_le _, Nat.zero_le _, fun a ha => Or.inl (hPerm_u ▸ ha)⟩
      have hIdxSlots' : idx < g1.slots.length := by
        simpa [g1, mkReplaceSlotGroup] using hIdxSlots
      have hClaimed' : g1.slots[idx]'hIdxSlots' = .claimed := by
        dsimp [g1, mkReplaceSlotGroup]; exact List.getElem_set_self _
      have hG1Sc : g1.sc = sc := by
        simpa [g1, mkReplaceSlotGroup] using hGsc
      have hFitG' : req + 4 ≤ g1.stride := by
        have hStrGe : slotStride sc ≤ g.stride :=
          hGsc ▸ active_group_stride_ge_fine hwf0 hg (hGsc ▸ hSc48) hAvNe
        have hStrEq : g1.stride = g.stride := rfl
        have hSzPos := (sizeClass_bounds (sc := sc) hSc48).1
        dsimp [nominalSlotCap, slotStride] at hFitSc hStrGe
        omega
      subst hb_eq
      rw [← mallocngBlockProg_eq_b09]
      exact mallocImpl_join_epilogue_raw_fine hcl_u hInv0 rfl hMetaLe1 hNoOrph1 hwf1_u hNoRes0
        hg'Mem hIdxSlots' hClaimed' hReqMax hFitG'
        (fun h => by rw [hG1Sc] at h ⊢; exact hSc2 h)
        (fun h => hSc24 (hG1Sc ▸ h))
        (fun h => by rw [hG1Sc] at h; omega)
        (fun h => by rw [hG1Sc] at h; omega)
        (fun hMm => by rw [hg'Mm] at hMm; cases hMm)
        (fun p val' liveMap' => by
          rw [dite_eq_left hSmall]
          exact ⟨sc, pk, pkSC, pkSB, st1, g1, s_u.brk, bud.liveCost, bud.peakCost,
            hSc48, hScAlt, hPk, hPres1, hwf1_u, hg'Mem, hG1Sc, ⟨hIdxSlots', hClaimed'⟩,
            ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩)
        htp0 hbrkS0 hDelta_u
        hpc_u hrun_u (hsp_u.trans hsp) hsp_align hProc_u hcs_u
        hx0_u hx19_u (hx20_u.trans hx20) hx21_u hx22_u hx23_u

set_option maxHeartbeats 400000 in
/-- Raw fine small/medium branch of `__libc_malloc_impl` (`req ≤ MmapThresholdReq = 131051`,
    `+0x03c .. RET`), returning `MallocImplFineRawSuccessPost`. -/
theorem mallocImpl_small_med_raw_fine_ok [MallocngMultiPlacement]
    {γ : GhostName} {tp brkStart : BitVec 64} {b : FineBudget} {bud : MallocngBudget}
    {ivs0 : List (BitVec 64 × Nat)} {alignMap0 : BitVec 64 → Option Nat}
    {req : Nat} {st0 : MallocngSt} {s0 s : State}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0)
    (hSmall : req ≤ MmapThresholdReq)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hPerm0 : s.mem.perm = s0.mem.perm)
    (hpc : s.pc = mbase 9 + miOff_small_entry) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ MallocImplFineRawSuccessPost γ tp brkStart b ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜FineStepOomCond msvc (fineStepReserve (.alloc req) b) s0 sf⌝) := by
  have hReq131 : req ≤ 131051 := hSmall
  have hReqMax : req ≤ MallocngMaxAllocSize := by
    have := mallocngMaxAllocSize_eq; dsimp [MmapThresholdReq] at hSmall; omega
  obtain ⟨hsc0_lt, _, _⟩ := sizeToClass_spec hReq131
  let stcFrame :=
    MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
    ghostMapAuth (fineAlignGam γ) alignMap0 ∗
    MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s.brk bud.liveCost bud.peakCost st0
  have hPreStc :
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp) =
      (MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗ stcFrame) := by
    dsimp only [stcFrame]
    generalize MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      stackFrameAt (s0.sp - 80#64) 624 = pSf,
      MallocngRoTablesA maddrs = pRo,
      ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
      MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart s.brk bud.liveCost bud.peakCost st0 = pCr,
      MallocngRuntime maddrs tp = pRt
    ac_rfl
  rw [hPreStc]
  refine sepWP_seq_cl (mid := mbase 9 + miOff_after_lock) hcl ?_
  refine SepWP.mono
    (mallocImpl_sizeToClass_lock_step (F := stcFrame) hReq131 rfl hpc hrun hsp hProc hcsHi hx20) ?_
    (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
  rintro s1 P1 hpc1 hrun1 ⟨⟨hsp1, hbrk1, hperm1, hProc1, hcs1, hx19_1, hx20_1, hx21_1, hx24_1⟩, hP1⟩ hcl1
  apply SepWP.weaken_pre hP1
  have hwf1_0 : MallocngWF maddrs.base brkStart s1.brk bud.liveCost bud.peakCost st0 :=
    hbrk1 ▸ hwf0
  let coarseRest :=
    MallocngLiveAuth (fineBaseGam γ) st0.liveMap ∗
    (maddrs.lock ↦₃₂ 0#32) ∗
    (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗
    ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗
    MallocngAuxvState (fineBaseGam γ) st0.auxvPtr st0.auxvSnap ∗
    ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∗
    MappedSet st0.masterDom (OwnedMappedByte st0) ∗
    MallocngRoTablesA maddrs ∗
    ghostMapAuth (fineAlignGam γ) alignMap0 ∗
    MallocngRuntime maddrs tp ∗
    MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
    stackFrameAt (s0.sp - 80#64) 624
  have hCoreToCoarse :
      (MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗ stcFrame) =
      ((maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
       ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗ coarseRest) := by
    have hwf0' : MallocngWFInflight 0 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0 := hwf0
    dsimp only [stcFrame, MallocngCoreStInflightA, coarseRest]
    rw [propext ⟨fun _ => trivial, fun _ => hwf0'⟩, pure_true, emp_sepConj]
    generalize (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
      ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal = pRw,
      MallocngLiveAuth (fineBaseGam γ) st0.liveMap = pGm,
      ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
      (maddrs.lock ↦₃₂ 0#32) = pLk,
      (maddrs.replaced ↦₃₂ 0#32) = pRp,
      (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
      ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) = pLb8,
      MallocngAuxvState (fineBaseGam γ) st0.auxvPtr st0.auxvSnap = pAx,
      ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
      MappedSet st0.masterDom (OwnedMappedByte st0) = pMs,
      MallocngRoTablesA maddrs = pRo,
      MallocngRuntime maddrs tp = pRt,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      stackFrameAt (s0.sp - 80#64) 624 = pSf
    ac_rfl
  have hCoarseBack : ∀ (brk' : BitVec 64)
      (_hwf' : MallocngWF maddrs.base brkStart brk' bud.liveCost bud.peakCost st0),
      ((maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
       ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗ coarseRest) =
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       MallocngCoreStInflightA 0 (fineBaseGam γ) maddrs brkStart brk' bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp) := by
    intro brk' hwf'
    have hwf'' : MallocngWFInflight 0 maddrs.base brkStart brk' bud.liveCost bud.peakCost st0 := hwf'
    dsimp only [MallocngCoreStInflightA, coarseRest]
    rw [propext ⟨fun _ => trivial, fun _ => hwf''⟩, pure_true, emp_sepConj]
    generalize (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
      ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal = pRw,
      MallocngLiveAuth (fineBaseGam γ) st0.liveMap = pGm,
      ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
      (maddrs.lock ↦₃₂ 0#32) = pLk,
      (maddrs.replaced ↦₃₂ 0#32) = pRp,
      (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
      ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) = pLb8,
      MallocngAuxvState (fineBaseGam γ) st0.auxvPtr st0.auxvSnap = pAx,
      ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
      MappedSet st0.masterDom (OwnedMappedByte st0) = pMs,
      MallocngRoTablesA maddrs = pRo,
      MallocngRuntime maddrs tp = pRt,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      stackFrameAt (s0.sp - 80#64) 624 = pSf
    ac_rfl
  rw [hCoreToCoarse]
  exact mallocImpl_coarse_step hwf1_0 hsc0_lt hpc1 hrun1 hsp1 hProc1 hcs1 hx19_1 hx20_1 hx21_1 hx24_1
    (fun sc s_t P_t hChoice hScLt hAct hpc_t hrun_t hsp_t hbrk_t hmem_t hProc_t hcs_t
         hx19_t hx20_t hx22_t hx24_t hx25_t hPt => by
      obtain ⟨_, hFitSc, hSc2, hSc24, _⟩ := coarseBump_sc_props hReq131 hChoice
      have hScAlt := coarseBump_choice_to_coarseAlt hChoice
      have hwf_t : MallocngWF maddrs.base brkStart s_t.brk bud.liveCost bud.peakCost st0 :=
        hbrk_t ▸ hwf1_0
      have hcl_t : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_t.mem := hmem_t ▸ hcl1
      have hPerm_t : s_t.mem.perm = s0.mem.perm := by
        rw [hmem_t]; exact hperm1.trans hPerm0
      apply SepWP.weaken_pre (Entails.trans hPt (Entails.of_eq (hCoarseBack s_t.brk hwf_t)))
      exact mallocImpl_tryAvail_or_slow_raw_fine hcl_t hInv0 hwf_t hSmall hReqMax hScLt hAct
        hScAlt hFitSc hSc2 hSc24 htp0 hbrkS0 hPerm_t
        hpc_t hrun_t hsp_t hsp_align hProc_t hcs_t
        hx19_t hx20_t hx22_t hx24_t hx25_t)
    (fun sc s_p P_p hChoice hScLt hpc_p hrun_p hsp_p hbrk_p hmem_p hProc_p hcs_p
         hx19_p hx20_p hx24_p hx25_p hPp => by
      obtain ⟨_, hFitSc, hSc2, hSc24, _⟩ := coarseBump_sc_props hReq131 hChoice
      have hScAlt := coarseBump_choice_to_coarseAlt hChoice
      have hwf_p : MallocngWF maddrs.base brkStart s_p.brk bud.liveCost bud.peakCost st0 :=
        hbrk_p ▸ hwf1_0
      have hcl_p : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_p.mem := hmem_p ▸ hcl1
      have hPerm_p : s_p.mem.perm = s0.mem.perm := by
        rw [hmem_p]; exact hperm1.trans hPerm0
      apply SepWP.weaken_pre (Entails.trans hPp (Entails.of_eq (hCoarseBack s_p.brk hwf_p)))
      exact mallocImpl_allocSlot_slow_raw_fine hcl_p hInv0 hwf_p hSmall hReqMax hScLt
        hScAlt hFitSc hSc2 hSc24 htp0 hbrkS0 hPerm_p
        hpc_p hrun_p hsp_p hsp_align hProc_p hcs_p
        hx19_p hx20_p hx24_p hx25_p)

end LibsignalBinary.Heap.Fine
