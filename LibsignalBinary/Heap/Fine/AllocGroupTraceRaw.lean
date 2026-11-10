/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.AllocGroupTraceDefs

/-!
# Fine-Trace Verification of Placed `alloc_group`

Verifies placed `alloc_group` (`blk08`, `+0x280`) with explicit `(maxGroups, maxMetaAreas)` bounds
and `allocSlotFineByteBound sc maxMetaAreas`, exporting an inductive `AllocSlotFineTrace`
derivation that records `st_ag.ctx.active[sc] = 0#64` at group creation together with root/nested
geometry and `SameGroupsSlotKind` preservation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

arm64_proof_prelude

/-! ## Root `mmap` Path -/

set_option maxHeartbeats 800000 in
private theorem wp_allocGroup_root_trace [MallocngMultiPlacement] {rootParamPred : Nat → Nat → Nat → Prop}
    (hRootSel : RootSizeSelectParamStmt rootParamPred)
    (sc req inflight cnt' : Nat) (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    (hlo : 1 ≤ cnt') (hhi : cnt' ≤ 32) (hgt2048 : 2048 < cnt' * slotStride sc + 16)
    (hprod : cnt' * slotStride sc ≤ 1048575) (h25 : sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536)
    (hsm : sc ≤ 8 → ∃ j, j < 3 ∧ cnt' = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat)
    (use : BitVec 64) (hcnt' : cnt' = Cost.cntSel sc use.toNat)
    (γ : GhostName) (tp brkStart brk_ag m : BitVec 64) (liveCost peakCost maxMetaAreas : Nat)
    (st0 st_ag st1 : MallocngSt) (s0 sr : State)
    (hw564 : Blk08HasWords564 mallocngFaultSvc) (hw768 : Blk08HasWords768 mallocngFaultSvc) (hr768 : Blk08Range768)
    (hSame0 : SameGroupsSlotKind st_ag.groups st0.groups)
    (hwfAg : MallocngWFInflight inflight maddrs.base brkStart brk_ag liveCost peakCost st_ag)
    (hAct0_ag : ∀ h : sc < st_ag.ctx.active.length, st_ag.ctx.active[sc]'h = 0#64)
    (hGrp1_ag : st1.groups = st_ag.groups)
    (hAct0 : ∀ h : sc < st1.ctx.active.length, st1.ctx.active[sc]'h = 0#64)
    (hActLow1 : ∀ k : Nat, k < sc → ∀ hk1 : k < st1.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length,
      st1.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0)
    (hRes1 : st1.reservedMetas = m :: st0.reservedMetas)
    (hRel1 : st1.liveMap = st0.liveMap ∧ totalLiveEffCost st1 = totalLiveEffCost st0 ∧
      totalLiveCount st1 = totalLiveCount st0 ∧ st1.metaAreas.length ≤ maxMetaAreas)
    (hOrph1 : MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st1) s0.mem sr.mem)
    (hDelta1 : MallocngMappedDelta 1 (32768 * maxMetaAreas) s0.mem sr.mem)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sr.mem)
    (hpc : sr.pc = mbase 8 + allocSlotOff_root) (hrun : sr.status = .Running)
    (hsp : sr.sp = s0.sp - 96#64) (hsAl : sr.spAligned = true) (htp0 : s0.tpidrEl0 = tp)
    (hProc : MallocngProcPreserved s0 sr) (hvr0 : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hx4 : sr.readReg64 .x4 = 4096#64) (hx19 : sr.readReg64 .x19 = m)
    (hx20 : sr.readReg64 .x20 = BitVec.ofNat 64 cnt') (hx21 : sr.readReg64 .x21 = BitVec.ofNat 64 sc)
    (hx22 : sr.readReg64 .x22 = Obj.pageOf maddrs.ctx) (hx23 : sr.readReg64 .x23 = BitVec.ofNat 64 sc)
    (hx24 : sr.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (hx25 : sr.readReg64 .x25 = BitVec.ofNat 64 req)
    (hx27 : sr.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc))
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc)) (hx2 : sr.readReg64 .x2 = use)
    (hx6 : sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt')) :
    SepWP (mallocngBlockProg mmpl 8 msvc) (s0.readReg64 .x30) sr
      (AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19)
        (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23)
        (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28) ∗
       stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗
       (m ↦ₛ List.replicate 40 0#8) ∗
       MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sr.brk liveCost peakCost st1 ∗ MallocngRuntime maddrs tp)
      (AllocSlotFineTracePost rootParamPred sc req inflight γ tp brkStart liveCost peakCost maxMetaAreas st0 s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1)) (allocSlotFineByteBound sc maxMetaAreas) s0 sf⌝) := by
  have hsc_pos : 0 < sc := root_sc_pos hhi hgt2048
  unfold MallocngCoreStInflightA MallocngRuntime
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro errnoVal
  simp only [show ∀ (P : SepProp) (φ : Prop) (Q : SepProp), P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) from
    fun P _ _ => by rw [← sepConj_assoc, sepConj_comm P, sepConj_assoc]]
  apply SepWP.pure_elim; intro hwf1
  obtain ⟨hActL, hUseL, hUnmL, hBncL, _, hLstL⟩ := hwf1.ctx_lens
  obtain ⟨CtxRest, hCtxSp, hCtxFd⟩ := ctx_split_fields maddrs.ctx st1.ctx hActL hUseL hUnmL hBncL
  let Saved := AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19)
    (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23)
    (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28)
  let RestCore := MallocngLiveAuth γ st1.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗ ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗
    MallocngAuxvState γ st1.auxvPtr st1.auxvSnap ∗ ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗ MappedSet st1.masterDom (OwnedMappedByte st1) ∗
    ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
  let BaseF := Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗
    MallocngRoTablesA maddrs ∗ (m ↦ₛ List.replicate 40 0#8) ∗
    ((maddrs.ctx + 12#64) ↦₃₂ st1.ctx.mmapCounter) ∗ ((maddrs.ctx + 80#64) ↦₆₄* st1.ctx.active) ∗ CtxRest ∗ RestCore
  refine SepWP.weaken_pre (P' := ((maddrs.ctx + 848#64) ↦ₛ st1.ctx.unmapSeq) ∗
      ((maddrs.ctx + 880#64) ↦ₛ st1.ctx.bounces) ∗ ((maddrs.ctx + 912#64) ↦₈ st1.ctx.seq) ∗
      ((maddrs.ctx + 464#64) ↦₆₄* st1.ctx.usageByClass) ∗ BaseF)
    (Entails.of_eq (by dsimp only [Saved, RestCore, BaseF]; rw [hCtxSp]; ac_rfl)) ?_
  have h_pre : SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 16) sr
      (((maddrs.ctx + 848#64) ↦ₛ st1.ctx.unmapSeq) ∗ ((maddrs.ctx + 880#64) ↦ₛ st1.ctx.bounces) ∗
       ((maddrs.ctx + 912#64) ↦₈ st1.ctx.seq) ∗ ((maddrs.ctx + 464#64) ↦₆₄* st1.ctx.usageByClass) ∗ BaseF)
      (fun sc0 Pc0 => ∃ cnt_f len bounces' unmapSeq' seq',
        RootMmapParamsOk sc cnt_f len ∧ rootParamPred sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧
        bounces'.length = 32 ∧ (∀ b ∈ bounces', b.toNat ≤ 150) ∧ unmapSeq'.length = 32 ∧
        sc0.sp = sr.sp ∧ sc0.spAligned = sr.spAligned ∧ PureStatePres sr sc0 ∧
        sc0.readReg64 .x0 = 0#64 ∧ sc0.readReg64 .x1 = BitVec.ofNat 64 len ∧
        sc0.readReg32 .x2 = 3#32 ∧ sc0.readReg32 .x3 = 0x22#32 ∧
        sc0.readReg32 .x4 = BitVec.allOnes 32 ∧ sc0.readReg64 .x5 = 0#64 ∧
        sc0.readReg64 .lr = mbase 8 + allocSlotOff_after_mmap ∧
        sc0.readReg64 .x19 = m ∧ sc0.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧
        sc0.readReg64 .x21 = BitVec.ofNat 64 sc ∧ sc0.readReg64 .x22 = Obj.pageOf maddrs.ctx ∧
        sc0.readReg64 .x23 = BitVec.ofNat 64 sc ∧ sc0.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧
        sc0.readReg64 .x26 = BitVec.ofNat 64 len ∧
        Pc0 = (((maddrs.ctx + 464#64) ↦₆₄* st1.ctx.usageByClass) ∗ ((maddrs.ctx + 848#64) ↦ₛ unmapSeq') ∗
          ((maddrs.ctx + 912#64) ↦₈ seq') ∗ (((maddrs.ctx + 880#64) ↦ₛ bounces') ∗ BaseF)))
      (fun _ => ⌜False⌝) := by
    refine SepWP.seq (wp_root_bounces sr sc st1.ctx.unmapSeq st1.ctx.bounces st1.ctx.seq _
      hw768 hr768 hsc hUnmL hBncL hwf1.bounces_wf hpc hrun hx22 hx21) ?_
    rintro s1 P1 hpc1 hrun1 ⟨bounces', hBncL', hBnc', _, hsp1, hal1, hpsp1, hx1_1, hr1, h39_1, hP1⟩; rw [hP1]
    refine SepWP.weaken_pre (Entails.of_eq (show (((maddrs.ctx + 848#64) ↦ₛ st1.ctx.unmapSeq) ∗
        ((maddrs.ctx + 880#64) ↦ₛ bounces') ∗ ((maddrs.ctx + 912#64) ↦₈ st1.ctx.seq) ∗
        ((maddrs.ctx + 464#64) ↦₆₄* st1.ctx.usageByClass) ∗ BaseF) =
        (((maddrs.ctx + 464#64) ↦₆₄* st1.ctx.usageByClass) ∗ ((maddrs.ctx + 848#64) ↦ₛ st1.ctx.unmapSeq) ∗
         ((maddrs.ctx + 912#64) ↦₈ st1.ctx.seq) ∗ (((maddrs.ctx + 880#64) ↦ₛ bounces') ∗ BaseF)) by ac_rfl)) ?_
    refine SepWP.seq (wp_root_seq_usage s1 sc st1.ctx.usageByClass st1.ctx.unmapSeq st1.ctx.seq _
        hw768 hr768 hsc hUseL hUnmL hpc1 hrun1 hx1_1
        (by rw [hr1 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx22])
        (by rw [hr1 .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx21])) ?_
    rintro s2 P2 hpc2 hrun2 ⟨unmapSeq', seq', hUnmL', _, hsp2, hal2, hpsp2, hr2, hx2_2, hP2⟩; rw [hP2]
    have h2_reg : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x5 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 →
        s2.readReg64 r = sr.readReg64 r :=
      fun r a1 a2 a3 a5 a7 a8 a9 => (hr2 r a1 a2 a3).trans (hr1 r a1 a3 a5 a7 a8 a9)
    refine SepWP.seq (hRootSel s2 sc req cnt' use _ hw768 hsc hReq hlo hhi hgt2048 hprod h25 hcnt' hpc2 hrun2
        (by rw [h2_reg .x0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx0])
        (by rw [h2_reg .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx4])
        (by rw [h2_reg .x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx6])
        (fun h => (hr2 .x7 (by decide) (by decide) (by decide)).trans (h39_1 h).2)
        (by rw [h2_reg .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx20])
        (by rw [h2_reg .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx21])
        (by rw [h2_reg .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx24])
        (by rw [h2_reg .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx25])
        (by rw [h2_reg .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx27])
        (fun h => ⟨by rw [hx2_2 (by omega), hr1 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx2],
          by rw [hr2 .x5 (by decide) (by decide) (by decide), (h39_1 h).1]⟩)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨cnt_f, len, hOk, hRootP0, hRq, _, hsp3, hal3, hpsp3, hx20_3, hx26_3, hr3, hP3⟩; rw [hP3]
    refine SepWP.mono (wp_mmap_call_prep s3 len _ hw768 hr768 hpc3 hrun3 hx26_3) ?_
    rintro sc0 Pc0 _ _ ⟨_, hsp4, hal4, hpsp4, h0c, h1c, h2c, h3c, h4c, h5c, hlr_c, hr4, hPc0⟩
    have hkeep : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x8 →
        r ≠ .x9 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → r ≠ .x30 → sc0.readReg64 r = sr.readReg64 r :=
      fun r a0 a1 a2 a3 a4 a5 a7 a8 a9 a20 a25 a26 a27 a30 =>
        (hr4 r a0 a1 a2 a3 a4 a5 a30).trans ((hr3 r a0 a1 a3 a20 a25 a26 a27).trans (h2_reg r a1 a2 a3 a5 a7 a8 a9))
    exact ⟨cnt_f, len, bounces', unmapSeq', seq', hOk, hRootP0, hRq, hBncL', hBnc', hUnmL',
      hsp4.trans (hsp3.trans (hsp2.trans hsp1)), hal4.trans (hal3.trans (hal2.trans hal1)),
      hpsp1.trans (hpsp2.trans (hpsp3.trans hpsp4)), h0c, h1c, h2c, h3c, h4c, h5c, hlr_c,
      (hkeep .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx19,
      (hr4 .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20_3,
      (hkeep .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx21,
      (hkeep .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22,
      (hkeep .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23,
      (hkeep .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24,
      (hr4 .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26_3, hPc0⟩
  refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 16) hcl (SepWP.mono h_pre ?_)
  rintro sc0 Pc0 hpcc0 hrc0 ⟨cnt_f, len, bounces', unmapSeq', seq', hOk, hRootP0, hRq, hBncL', hBnc', hUnmL',
    hspc0, halc0, hpspc0, h0c, h1c, h2c, h3c, h4c, h5c, hlr_c, h19c, h20c, h21c, h22c, h23c, h24c, h26c, hPc0⟩
    hpermc0 hclc0; subst hPc0
  obtain ⟨hcf_lo, hcf_hi, hlen4096, hdvd_len, hlen1M, hlen25, hlen0, hcap_lt⟩ := hOk
  have hAlignEq : pageAlignUp len = len := by obtain ⟨k, rfl⟩ := hdvd_len; unfold pageAlignUp PAGE_SIZE; omega
  have hd_sz : allocSlotDepthBound sc ≤ 3 := by unfold allocSlotDepthBound; repeat (first | split | omega)
  have hsp_c : sc0.sp = s0.sp - 96#64 := hspc0.trans hsp; have hal_c : sc0.spAligned = true := halc0.trans hsAl
  have hProc_c : MallocngProcPreserved s0 sc0 := MallocngProcPreserved.trans hProc hpspc0.1
  have htp_c : sc0.tpidrEl0 = tp := hProc_c.2.2.1.trans htp0; have hlen_mod : len % PAGE_SIZE = 0 := Nat.mod_eq_zero_of_dvd hdvd_len
  have hx1_nat : (sc0.readReg64 .x1).toNat = len := by rw [h1c, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hStkSp : stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) =
      (stackFrame sc0 64 ∗ stackFrameAt (s0.sp - 96#64 - 64#64) (allocSlotDepthBound sc * 96 + 224 - 64)) := by
    rw [stackFrameAt_split_top (s0.sp - 96#64) 64 _ (by omega) (by omega),
        solver_stackFrameAt_eq_memRegion (s0.sp - 96#64) 64 (by omega)]; unfold stackFrame; rw [hsp_c]
  refine call_withCL_frame_auto (x := ()) (placed_mmapRw_large_ok (P := mallocngBlockProg mmpl 8 msvc) tp errnoVal len
      (by omega) (by rw [mallocngMaxAllocSize_eq]; omega)) hclc0 hpcc0 hrc0 hal_c hlr_c
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_
    (by intro R h; dsimp only; dsimp +zeta only [BaseF, RestCore] at h
        rw [pure_sepConj_of_true ⟨htp_c, h0c, hx1_nat, h2c, h3c, h4c, h5c⟩]; rw [hStkSp] at h; revert R h; sep_frame)
    (fun R' sf _ ho => by
      have ho' := Satisfies.drop_mid ho; rw [satisfies_pure_sepConj] at ho' ⊢
      obtain ⟨⟨hfs, htr, hsig, hpm, _, hgap⟩, hR'⟩ := ho'; rw [hAlignEq] at hgap
      have hbd := allocMetaFineByteBound_le_allocSlot sc maxMetaAreas
      have hlenB : 32768 * maxMetaAreas + len ≤ allocSlotFineByteBound sc maxMetaAreas := by
        unfold allocSlotFineByteBound
        have := Nat.mul_le_mul_right (5 * 1024 * 1024 + 32768 * maxMetaAreas) (by omega : 1 ≤ allocSlotDepthBound sc + 1); omega
      exact ⟨MallocngPlacedOomCond.of_delta (k' := 2 * (allocSlotDepthBound sc + 1))
        (hfs.trans hProc_c.1) (htr.trans hProc_c.2.1) (hsig.trans hProc_c.2.2.2.2.2.2)
        (mappedDelta_perm_right hDelta1 (hpm.trans hpermc0)) (by omega) hbd
        fun hsan => ⟨len, by dsimp [PAGE_SIZE]; omega, hlen_mod, hlenB, hgap hsan⟩, hR'⟩)
  intro sm hpc_m hrun_m hsp_m hcs_m hcl_m; dsimp only; rw [hAlignEq]; simp only [sepConj_assoc, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro mb; apply SepWP.pure_elim
  rintro ⟨hProc_m, hbrk_m, hx0_m, hMbNe0, hMbNeg1, hMbDvd, hMbHi, hDMmap, hNewMmap⟩
  let maplen := len / 4096; have hMapEq : maplen * 4096 = len := Nat.div_mul_cancel hdvd_len
  have hMapLo : 1 ≤ maplen := by omega
  have hMapHi : maplen ≤ 256 := by omega
  have hMapPos : 0 < maplen := Nat.lt_of_lt_of_le Nat.zero_lt_one hMapLo
  have hMbAl : mb.toNat % 4096 = 0 := Nat.mod_eq_zero_of_dvd hMbDvd
  have hsp_m0 : sm.sp = s0.sp - 96#64 := hsp_m.trans hsp_c
  have hal_m : sm.spAligned = true := by rw [State.spAligned, hsp_m]; simpa [State.spAligned] using hal_c
  apply SepWP.with_sat; rintro ⟨R_sat, hm_sat⟩
  have ⟨R_disj, hm_disj⟩ : ∃ R_disj, sm.mem ⊨ (mb ↦ₛ List.replicate (maplen * 4096) 0#8) ∗
      memMapped mb (maplen * 4096) ∗ ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
      MappedSet st1.masterDom (OwnedMappedByte st1) ∗ (R_disj ∗ R_sat) :=
    ⟨?_, by revert R_sat hm_sat; rw [hMapEq]; sep_frame⟩
  obtain ⟨hMbLo, hDisjRoot⟩ := fresh_mmap_disjoint_placed hwf1 hMapPos hMbNe0 hMbDvd (hMapEq ▸ hMbHi) hm_disj
  let PostMmapF := Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗
    ((m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦₆₄ 0#64) ∗ ((m + 24#64) ↦₃₂ 0#32) ∗ ((m + 28#64) ↦₃₂ 0#32)) ∗
    ((maddrs.ctx + 80#64) ↦₆₄* st1.ctx.active) ∗ ((maddrs.ctx + 464#64) ↦₆₄* st1.ctx.usageByClass) ∗
    ((maddrs.ctx + 848#64) ↦ₛ unmapSeq') ∗ ((maddrs.ctx + 880#64) ↦ₛ bounces') ∗ ((maddrs.ctx + 912#64) ↦₈ seq') ∗
    CtxRest ∗ (mb ↦ₛ List.replicate (maplen * 4096) 0#8) ∗ memMapped mb (maplen * 4096) ∗ RestCore
  refine SepWP.weaken_pre (P' := ((maddrs.ctx + 12#64) ↦₃₂ st1.ctx.mmapCounter) ∗ ((m + 32#64) ↦₆₄ 0#64) ∗ PostMmapF)
    (Entails.of_eq (by dsimp +zeta only [PostMmapF, RestCore, Saved]; rw [hStkSp, split_rep40_zero m, hMapEq]; ac_rfl)) ?_
  refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 8 + allocSlotOff_pub_add) hcl_m
    (SepWP.mono (wp_root_after_mmap sm m mb st1.ctx.mmapCounter sc cnt_f maplen PostMmapF
      hw768 hr768 hsc hcf_lo hcf_hi hMapLo hMapHi hMbNeg1 hpc_m hrun_m hx0_m
      (hcs_m.1.trans h19c) (hcs_m.2.1.trans h20c) (hcs_m.2.2.2.1.trans h22c)
      (hcs_m.2.2.2.2.2.1.trans h24c) (hcs_m.2.2.2.2.2.2.2.1.trans (hMapEq ▸ h26c)))
      fun spub Ppub hpcpub hrpub ⟨_, hsp_p, hal_p, hpsp_p, hx0_p, hx1_p, hx2_p, hx28_p, hr_p, hPpub⟩ hperm_p _ => ?_)
  subst hPpub
  let lastIdx := cnt_f - 1; let activeIdx := min (4080 / slotStride sc - 1) (cnt_f - 1)
  have hscA : sc < st1.ctx.active.length := by omega
  have hscU : sc < st1.ctx.usageByClass.length := by omega
  have hscL : sc < st1.activeLists.length := by omega
  obtain ⟨ActRest, hActSp, hActUp⟩ := words64_focus_set (maddrs.ctx + 80#64) st1.ctx.active sc hscA
  obtain ⟨UseRest, hUseSp, hUseUp⟩ := words64_focus_set (maddrs.ctx + 464#64) st1.ctx.usageByClass sc hscU
  let PubF := ((maddrs.ctx + 12#64) ↦₃₂ (st1.ctx.mmapCounter + 1#32)) ∗ ActRest ∗ UseRest ∗
    ((maddrs.ctx + 848#64) ↦ₛ unmapSeq') ∗ ((maddrs.ctx + 880#64) ↦ₛ bounces') ∗ ((maddrs.ctx + 912#64) ↦₈ seq') ∗
    CtxRest ∗ ((mb + 9#64) ↦ₛ List.replicate (maplen * 4096 - 9) 0#8) ∗ memMapped mb (maplen * 4096) ∗
    stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗ RestCore
  refine SepWP.weaken_pre (P' := ((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ 0#64) ∗
      ((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ (st1.ctx.usageByClass[sc]'hscU)) ∗
      (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦₆₄ 0#64) ∗ ((m + 24#64) ↦₃₂ 0#32) ∗ ((m + 28#64) ↦₃₂ 0#32) ∗
      ((m + 32#64) ↦₆₄ (BitVec.ofNat 64 maplen <<< 12)) ∗ (mb ↦₆₄ 0#64) ∗ ((mb + 8#64) ↦₈ 0#8) ∗
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗ ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x19) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x27) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x28) ∗ PubF)
    (Entails.of_eq (by dsimp only [PostMmapF, Saved, AllocSlotSaved12, PubF]
                       rw [hActSp, hAct0 hscA, hUseSp, split_mmap_hdr9 mb (n := maplen * 4096) (by omega)]; ac_rfl)) ?_
  refine SepWP.mono (wp_publish_new_group s0.sp (s0.readReg64 .x30) m mb (st1.ctx.usageByClass[sc]'hscU)
      0#64 0#64 0#32 0#32 0#8 (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27)
      (s0.readReg64 .x28) (s0.readReg64 .x29) sc activeIdx lastIdx maplen none 0 true PubF _
      hw564 hw768 hr768 hsc (by omega) (Nat.min_le_right _ _) hpcpub hrpub (hsp_p.trans hsp_m0) (hal_p.trans hal_m)
      ((hr_p .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hcs_m.2.2.2.1.trans h22c))
      ((hr_p .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hcs_m.2.2.2.2.1.trans h23c))
      ((hr_p .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hcs_m.2.2.1.trans h21c))
      ((hr_p .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hcs_m.1.trans h19c))
      hx0_p hx1_p hx2_p hx28_p) ?_
  rintro sf P_f _ _ ⟨_, hsp_f, _, hpsp_f, hperm_f, hx0_f, h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, _, actB, hActB, hPf⟩
  have hbrk_f : sf.brk = sr.brk := hpsp_f.2.1.trans (hpsp_p.2.1.trans (hbrk_m.trans hpspc0.2.1))
  have hwf1' : MallocngWFInflight (inflight + 1) maddrs.base brkStart sf.brk liveCost peakCost st1 := hbrk_f.symm ▸ hwf1
  have hcap_lt' : 12 + (lastIdx + 1) * (if lastIdx == 0 && 0 < maplen then maplen * 4096 - 16 else slotStride sc) < maplen * 4096 := by
    dsimp only [lastIdx, maplen]; rw [Nat.sub_add_cancel hcf_lo, hMapEq]; exact hcap_lt
  obtain ⟨hwf', hCost', hCount', hBmRw, hBmPn, hMpEq, hZeroSl0⟩ :=
    wf_alloc_root_mmap (mmapCtr' := st1.ctx.mmapCounter + 1#32) (unmapSeq' := unmapSeq') (bounces' := bounces') (seq' := seq')
      hwf1' hsc hscA hscL hscU (hAct0 hscA) hRes1 hMapPos hMbLo hMbAl (hMapEq ▸ hMbHi) (hMapEq ▸ hlen25) (hMapEq ▸ hlen1M)
      (fun hl0 => by have : cnt_f - 1 = 0 := hl0; exact hMapEq ▸ hlen0 (by omega))
      (by omega : lastIdx ≤ 31) (by rw [hActB]; exact Nat.min_le_right _ _) (fun _ => hsc_pos) hcap_lt' hDisjRoot hUnmL' hBncL' hBnc'
  let initAvail : BitVec 32 := (2#32 <<< BitVec.ofNat 32 ((actB &&& 0x1f#8).toNat)) - 1#32
  let cg : GroupDesc := {
    metaPtr := m, prev := m, next := m, mem := mb, availMask := initAvail - 1#32,
    freedMask := (2#32 <<< BitVec.ofNat 32 lastIdx) + ~~~initAvail, lastIdx := lastIdx, sc := sc, maplen := maplen,
    activeByte := actB, parentMeta := none, nestedCap := 0, slots := newGroupSlots lastIdx ((actB &&& 0x1f#8).toNat), freshZero := true }
  let ctx' : CtxFields := { st1.ctx with
    mmapCounter := st1.ctx.mmapCounter + 1#32, active := st1.ctx.active.set sc m,
    usageByClass := st1.ctx.usageByClass.set sc (st1.ctx.usageByClass[sc]'hscU + BitVec.ofNat 64 cg.cnt),
    unmapSeq := unmapSeq', bounces := bounces', seq := seq' }
  let grpBs : List (BitVec 8) := unpack64 m ++ [actB] ++ List.replicate (maplen * 4096 - 9) 0#8
  let st' : MallocngSt := { st1 with
    ctx := ctx', reservedMetas := st0.reservedMetas, groups := cg :: st1.groups,
    activeLists := st1.activeLists.set sc [m], masterDom := extendDom (extendDom st1.masterDom m 40) mb (maplen * 4096),
    byteVal := writeBytesToMap (writeBytesToMap st1.byteVal mb grpBs) m cg.metaBytes }
  have hProc_f : MallocngProcPreserved s0 sf :=
    MallocngProcPreserved.trans (MallocngProcPreserved.trans (MallocngProcPreserved.trans hProc_c hProc_m) hpsp_p.1) hpsp_f.1
  have hvr_f : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
    hpsp_f.2.2.trans (hpsp_p.2.2.trans (hcs_m.2.2.2.2.2.2.2.2.2.2.2.trans (hpspc0.2.2.trans hvr0)))
  refine ⟨?_, hsp_f, calleeSaved_of_epilogue h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvr_f⟩
  refine Entails.trans ?_ (Entails.sepExists_intro st')
  refine Entails.trans ?_ (Entails.sepExists_intro 0)
  have hDynEq : dynamicRootRegions st' = st1.metaAreas.map (fun ma => (ma.base, 4096)) ++
      st1.guardPages.map (fun gp => (gp, 4096)) ++ st1.availMetaPages.map (fun ap => (ap, 4096)) ++
      ((mb, len) :: (st1.groups.filter fun g => decide (0 < g.maplen)).map (fun g => (g.mem, g.maplen * 4096))) := by
    dsimp +zeta only [dynamicRootRegions, st', cg]; simp [hMapPos, hMapEq]
  have hOrph' : MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st') s0.mem sf.mem := by
    refine mallocngNoOrphanMappings_root_step rfl hOrph1 hpermc0 hNewMmap (hperm_f.trans hperm_p) ?_ ?_
    · intro iv hiv; rw [hDynEq]; unfold dynamicRootRegions at hiv; simp only [List.mem_append, List.mem_cons] at hiv ⊢
      rcases hiv with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
    · rw [hDynEq]; simp only [List.mem_append, List.mem_cons]; exact Or.inr (Or.inl trivial)
  have hRootP_cg : rootParamPred sc cg.cnt (cg.maplen * 4096) := by
    have hCntEq : cg.cnt = cnt_f := by dsimp [GroupDesc.cnt, cg, lastIdx]; omega
    rwa [hCntEq, hMapEq]
  have hTrace : AllocSlotFineTrace rootParamPred maddrs.base brkStart liveCost peakCost inflight sc req st0 st' 0 :=
    .rootGroup hSame0 hwfAg hAct0_ag ⟨hlo, hhi, hgt2048, hprod, h25, hsm⟩ hRootP_cg
      ⟨hMapPos, rfl, rfl, rfl, Nat.min_le_right _ _, by dsimp +zeta only [cg]; rw [hActB]⟩
      (by dsimp [st']; rw [hGrp1_ag])
  rw [pure_sepConj_of_true (by
    refine ⟨hProc_f, rfl, hRel1.1, hCost'.trans hRel1.2.1, hCount'.trans hRel1.2.2.1, hRel1.2.2.2,
      (fun k hk hk1 hk0 => ?_), by simp [State.readReg32, hx0_f], by omega,
      ⟨cg, List.Mem.head _, show sc < (st1.ctx.active.set sc m).length by simp [hscA],
        show 0 < (newGroupSlots lastIdx _).length by simp [newGroupSlots], rfl,
        root_stride_ge_req hsc hReq hMapPos (fun hl0 => by have : cnt_f - 1 = 0 := hl0; exact hMapEq ▸ hRq (by omega)),
        show m = (st1.ctx.active.set sc m)[sc]'_ by simp, rfl, fun _ => hZeroSl0⟩,
      hTrace, hOrph', root_mappedDelta_combine_fine hDelta1 hpermc0 hDMmap (hperm_f.trans hperm_p) hlen1M⟩
    dsimp +zeta only [st', ctx'] at hk1 ⊢; rw [List.getElem_set_ne (by omega : sc ≠ k)]
    exact hActLow1 k hk (by simpa using hk1) hk0)]
  have hcg_meta : cg = {
      metaPtr := m, prev := m, next := m, mem := mb,
      availMask := ((2#32 <<< BitVec.ofNat 32 activeIdx) - 1#32) - 1#32,
      freedMask := (2#32 <<< BitVec.ofNat 32 lastIdx) + ~~~((2#32 <<< BitVec.ofNat 32 activeIdx) - 1#32),
      lastIdx := lastIdx, sc := sc, maplen := maplen, activeByte := actB,
      parentMeta := none, nestedCap := 0, slots := newGroupSlots lastIdx activeIdx, freshZero := true } := by
    dsimp +zeta only [cg, initAvail]; rw [hActB]
  dsimp only at hPf; rw [← hcg_meta] at hPf; subst hPf
  have hCtxEq : (((maddrs.ctx + 12#64) ↦₃₂ (st1.ctx.mmapCounter + 1#32)) ∗
      (((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ m) ∗ ActRest) ∗
      (((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ (st1.ctx.usageByClass[sc]'hscU + BitVec.ofNat 64 (lastIdx + 1))) ∗ UseRest) ∗
      ((maddrs.ctx + 848#64) ↦ₛ unmapSeq') ∗ ((maddrs.ctx + 880#64) ↦ₛ bounces') ∗
      ((maddrs.ctx + 912#64) ↦₈ seq') ∗ CtxRest) = (maddrs.ctx ↦ₛ ctx'.toBytes) := by
    rw [hActUp, hUseUp]; exact hCtxFd _ _ _ _ _ _ (by simp [hActL]) (by simp [hUseL]) hUnmL' hBncL'
  unfold MallocngCoreStInflightA MallocngRuntime; rw [pure_sepConj_of_true hwf']
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_left (Entails.sepExists_intro (P := fun v => (tp - 0xa4#64) ↦₃₂ v) errnoVal)))))
  have hJoin := saved12_rejoin_stackFrame s0 sc (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19)
    (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
    (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28)
  dsimp only [AllocSlotSaved12] at hJoin; have hHdrEq := fold_mmap_hdr9 mb m actB (maplen * 4096 - 9)
  refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left hJoin)
  rw [← hCtxEq, ← hBmRw, ← hHdrEq, ← hBmPn, ← hMpEq]; dsimp only [PubF, RestCore, st', cg, initAvail, lastIdx]; ac_rfl

/-! ## Nested `alloc_slot` and `enframe` Path -/

private theorem enframe_slot_bytes_wf (val : BitVec 64 → BitVec 8) (pg : GroupDesc)
    (pIdx off sc cnt' : Nat) (m : BitVec 64) (actB : BitVec 8) (bs2 bs3 bs' : List (BitVec 8))
    (hcnt2 : 2 ≤ cnt') (hFit : 16 * off + 16 + cnt' * slotStride sc ≤ pg.stride) (hStrHi : pg.stride ≤ 65524)
    (hSbEnd : (pg.slotStart pIdx - 4#64) + BitVec.ofNat 64 pg.stride = pg.slotEnd pIdx)
    (hSbMb4 : (pg.slotStart pIdx - 4#64) + BitVec.ofNat 64 (16 * off + 4) = pg.slotStart pIdx + BitVec.ofNat 64 (16 * off))
    (hbs2L : bs2.length = pg.stride + 1) (hbs2_0 : bs2.getD 0 0#8 = 0#8) (hbs2_off : bs2.getD (16 * off) 0#8 = 0#8)
    (hbs2_2 : bs2.getD (16 * off + 2) 0#8 = (unpack16 (BitVec.ofNat 16 (((pg.slotStart pIdx + BitVec.ofNat 64 (16 * off)).toNat - pg.storage.toNat) / 16))).getD 0 0#8)
    (hbs2_3 : bs2.getD (16 * off + 3) 0#8 = (unpack16 (BitVec.ofNat 16 (((pg.slotStart pIdx + BitVec.ofNat 64 (16 * off)).toNat - pg.storage.toNat) / 16))).getD 1 0#8)
    (hbs2_end : bs2.getD pg.stride 0#8 = 0#8) (hbs3L : bs3.length = bs2.length)
    (hbs3_1 : bs3.getD (16 * off + 1) 0#8 = BitVec.ofNat 8 ((6 <<< 5) ||| pIdx))
    (hbs3_out : ∀ idx, idx ≠ 16 * off + 1 → bs3.getD idx 0#8 = bs2.getD idx 0#8)
    (hbs'L : bs'.length = bs3.length)
    (hbs'Z : ∀ j, 0 ≤ j → j ≤ cnt' → bs'.getD (16 * off + 16 + j * slotStride sc) 0#8 = 0#8)
    (hbs'Out : ∀ idx, (∀ j, 0 ≤ j → j ≤ cnt' → idx ≠ 16 * off + 16 + j * slotStride sc) → bs'.getD idx 0#8 = bs3.getD idx 0#8) :
    let slotBase := pg.slotStart pIdx - 4#64
    let mb := pg.slotStart pIdx + BitVec.ofNat 64 (16 * off)
    let slotBs' := replaceSlice bs' (16 * off + 4) (unpack64 m ++ [actB])
    let lastIdx := cnt' - 1
    slotBs'.length = pg.stride + 1 ∧ writeBytesToMap val slotBase slotBs' slotBase = 0#8 ∧
    writeBytesToMap val slotBase slotBs' (pg.slotEnd pIdx) = 0#8 ∧
    writeBytesToMap val slotBase slotBs' (mb - 4#64) = 0#8 ∧
    writeBytesToMap val slotBase slotBs' (mb - 3#64) = BitVec.ofNat 8 ((6 <<< 5) ||| pIdx) ∧
    readBytesFromMap (writeBytesToMap val slotBase slotBs') (mb - 2#64) 2 =
      unpack16 (BitVec.ofNat 16 ((mb.toNat - pg.storage.toNat) / 16)) ∧
    readBytesFromMap (writeBytesToMap val slotBase slotBs') mb 8 = unpack64 m ∧
    writeBytesToMap val slotBase slotBs' (mb + 8#64) = actB ∧
    writeBytesToMap val slotBase slotBs' (mb + BitVec.ofNat 64 (12 + (lastIdx + 1) * slotStride sc)) = 0#8 ∧
    (∀ idx : Nat, idx < lastIdx + 1 → writeBytesToMap val slotBase slotBs' (mb + BitVec.ofNat 64 (12 + idx * slotStride sc)) = 0#8) := by
  intro slotBase mb slotBs' lastIdx
  have hSbMb4' : slotBase + BitVec.ofNat 64 (16 * off + 4) = mb := hSbMb4
  have hu64L : (unpack64 m).length = 8 := rfl
  have hSub9L : (unpack64 m ++ [actB]).length = 9 := by simp [hu64L]
  have hLen' : bs'.length = pg.stride + 1 := hbs'L.trans (hbs3L.trans hbs2L)
  have hFit9 : (16 * off + 4) + (unpack64 m ++ [actB]).length ≤ bs'.length := by rw [hSub9L, hLen']; omega
  have hSlotL : slotBs'.length = pg.stride + 1 := (replaceSlice_length hFit9).trans hLen'
  have hSlot64 : slotBs'.length ≤ 2 ^ 64 := by rw [hSlotL]; omega
  have hPre : ∀ idx, idx < 16 * off + 4 → slotBs'.getD idx 0#8 = bs3.getD idx 0#8 := fun idx hi =>
    (replaceSlice_getD_out hFit9 (Or.inl hi)).trans (hbs'Out idx (fun _ _ _ => by omega))
  have hEndZ : slotBs'.getD pg.stride 0#8 = 0#8 := by
    rw [replaceSlice_getD_out hFit9 (Or.inr (by rw [hSub9L]; omega))]
    by_cases hHit : ∃ j, 0 ≤ j ∧ j ≤ cnt' ∧ pg.stride = 16 * off + 16 + j * slotStride sc
    · obtain ⟨j, hj0, hj1, hEq⟩ := hHit; rw [hEq]; exact hbs'Z j hj0 hj1
    · rw [hbs'Out _ (fun j hj0 hj1 hEq => hHit ⟨j, hj0, hj1, hEq⟩), hbs3_out _ (by omega), hbs2_end]
  have hZeroAt : ∀ j, j ≤ cnt' → writeBytesToMap val slotBase slotBs' (mb + BitVec.ofNat 64 (12 + j * slotStride sc)) = 0#8 := fun j hj => by
    have hjLe : j * slotStride sc ≤ cnt' * slotStride sc := Nat.mul_le_mul_right _ hj
    have hAd : mb + BitVec.ofNat 64 (12 + j * slotStride sc) = slotBase + BitVec.ofNat 64 (16 * off + 16 + j * slotStride sc) := by
      rw [← hSbMb4', BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    rw [hAd, writeBytesToMap_getD val slotBase slotBs' (by rw [hSlotL]; omega) hSlot64,
        replaceSlice_getD_out hFit9 (Or.inr (by rw [hSub9L]; omega)), hbs'Z j (Nat.zero_le _) hj]
  refine ⟨hSlotL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h0 := writeBytesToMap_getD val slotBase slotBs' (i := 0) (by rw [hSlotL]; omega) hSlot64
    rw [BitVec.add_zero, hPre 0 (by omega), hbs3_out 0 (by omega), hbs2_0] at h0; exact h0
  · rw [← hSbEnd, writeBytesToMap_getD val slotBase slotBs' (by rw [hSlotL]; omega) hSlot64, hEndZ]
  · have ha : mb - 4#64 = slotBase + BitVec.ofNat 64 (16 * off) := by
      rw [← hSbMb4', BitVec.ofNat_add, ← BitVec.add_assoc]; exact BitVec.add_sub_cancel _ _
    rw [ha, writeBytesToMap_getD val slotBase slotBs' (by rw [hSlotL]; omega) hSlot64,
        hPre _ (by omega), hbs3_out _ (by omega), hbs2_off]
  · have ha : mb - 3#64 = slotBase + BitVec.ofNat 64 (16 * off + 1) := by
      rw [← hSbMb4', show 16 * off + 4 = (16 * off + 1) + 3 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
      exact BitVec.add_sub_cancel _ _
    rw [ha, writeBytesToMap_getD val slotBase slotBs' (by rw [hSlotL]; omega) hSlot64, hPre _ (by omega), hbs3_1]
  · have ha : mb - 2#64 = slotBase + BitVec.ofNat 64 (16 * off + 2) := by
      rw [← hSbMb4', show 16 * off + 4 = (16 * off + 2) + 2 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
      exact BitVec.add_sub_cancel _ _
    let u16 := BitVec.ofNat 16 ((mb.toNat - pg.storage.toNat) / 16)
    have hu16L : (unpack16 u16).length = 2 := rfl
    rw [ha]; change readBytesFromMap _ _ (unpack16 u16).length = unpack16 u16
    refine readBytesFromMap_sub_writeBytesToMap val slotBase slotBs' (unpack16 u16) (by rw [hu16L, hSlotL]; omega) hSlot64 ?_
    intro j hj; rw [hu16L] at hj; rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rw [Nat.add_zero, hPre _ (by omega), hbs3_out _ (by omega)]; exact hbs2_2
    · rw [show 16 * off + 2 + 1 = 16 * off + 3 by omega, hPre _ (by omega), hbs3_out _ (by omega)]; exact hbs2_3
  · rw [← hSbMb4']; change readBytesFromMap _ _ (unpack64 m).length = unpack64 m
    refine readBytesFromMap_sub_writeBytesToMap val slotBase slotBs' (unpack64 m) (by rw [hu64L, hSlotL]; omega) hSlot64 ?_
    intro j hj; rw [hu64L] at hj
    rw [show slotBs'.getD (16 * off + 4 + j) 0#8 = (unpack64 m ++ [actB]).getD j 0#8 from
        replaceSlice_getD_in hFit9 (by rw [hSub9L]; omega),
        List.getD, List.getD, List.getElem?_append_left (by rw [hu64L]; exact hj)]
  · have ha : mb + 8#64 = slotBase + BitVec.ofNat 64 (16 * off + 4 + 8) := by
      rw [← hSbMb4', BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [ha, writeBytesToMap_getD val slotBase slotBs' (by rw [hSlotL]; omega) hSlot64,
        show slotBs'.getD (16 * off + 4 + 8) 0#8 = (unpack64 m ++ [actB]).getD 8 0#8 from
        replaceSlice_getD_in hFit9 (by rw [hSub9L]; omega)]; rfl
  · rw [show lastIdx + 1 = cnt' by omega]; exact hZeroAt cnt' (Nat.le_refl _)
  · intro idx hidx; exact hZeroAt idx (by omega)

set_option maxHeartbeats 800000 in
private theorem wp_allocGroup_nested_trace [MallocngMultiPlacement] {rootParamPred : Nat → Nat → Nat → Prop}
    (sc req inflight cnt' : Nat) (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    (hInflight : inflight + allocSlotDepthBound sc ≤ 6)
    (hRec : ∀ pSc, pSc < 48 → allocSlotDepthBound pSc < allocSlotDepthBound sc →
      AllocSlotAtDepthFineTraceStmt rootParamPred pSc)
    (hv : ValidNestedCnt sc cnt') (γ : GhostName) (tp brkStart brk_ag m : BitVec 64)
    (liveCost peakCost maxGroups maxMetaAreas : Nat) (st0 st_ag st1 : MallocngSt) (s0 sn : State)
    (hw564 : Blk08HasWords564 mallocngFaultSvc) (hw768 : Blk08HasWords768 mallocngFaultSvc) (hr768 : Blk08Range768)
    (hSame0 : SameGroupsSlotKind st_ag.groups st0.groups)
    (hwfAg : MallocngWFInflight inflight maddrs.base brkStart brk_ag liveCost peakCost st_ag)
    (hAct0_ag : ∀ h : sc < st_ag.ctx.active.length, st_ag.ctx.active[sc]'h = 0#64)
    (hGrp1_ag : st1.groups = st_ag.groups) (hGroups1 : st1.groups.length ≤ maxGroups)
    (hMetaStep : 1 + (7 + maxGroups) / 101 ≤ maxMetaAreas) (hActL1 : st1.ctx.active.length = 48)
    (hAct0 : ∀ h : sc < st1.ctx.active.length, st1.ctx.active[sc]'h = 0#64)
    (hActLow1 : ∀ k : Nat, k < sc → ∀ hk1 : k < st1.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length,
      st1.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0)
    (hRes1 : st1.reservedMetas = m :: st0.reservedMetas)
    (hRel1 : st1.liveMap = st0.liveMap ∧ totalLiveEffCost st1 = totalLiveEffCost st0 ∧
      totalLiveCount st1 = totalLiveCount st0 ∧ st1.metaAreas.length ≤ maxMetaAreas)
    (hOrph1 : MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st1) s0.mem sn.mem)
    (hDelta1 : MallocngMappedDelta 1 (32768 * maxMetaAreas) s0.mem sn.mem)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sn.mem)
    (hpc : sn.pc = mbase 8 + allocSlotOff_nested) (hrun : sn.status = .Running)
    (hsp : sn.sp = s0.sp - 96#64) (hsAl : sn.spAligned = true) (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hProc : MallocngProcPreserved s0 sn) (hvr0 : calleeSavedVRegs sn = calleeSavedVRegs s0)
    (hx0 : sn.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc)) (hx19 : sn.readReg64 .x19 = m)
    (hx20 : sn.readReg64 .x20 = BitVec.ofNat 64 cnt') (hx21 : sn.readReg64 .x21 = BitVec.ofNat 64 sc)
    (hx22 : sn.readReg64 .x22 = Obj.pageOf maddrs.ctx) (hx23 : sn.readReg64 .x23 = BitVec.ofNat 64 sc)
    (hx24 : sn.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (hx26 : sn.readReg64 .x26 = Obj.pageOf maddrs.sizeClasses)
    (hx28 : sn.readReg64 .x28 = BitVec.ofNat 64 cnt') :
    SepWP (mallocngBlockProg mmpl 8 msvc) (s0.readReg64 .x30) sn
      (AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19) (s0.readReg64 .x20)
        (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25)
        (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28) ∗
       stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗
       (m ↦ₛ List.replicate 40 0#8) ∗
       MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sn.brk liveCost peakCost st1 ∗ MallocngRuntime maddrs tp)
      (AllocSlotFineTracePost rootParamPred sc req inflight γ tp brkStart liveCost peakCost maxMetaAreas st0 s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1)) (allocSlotFineByteBound sc maxMetaAreas) s0 sf⌝) := by
  let u := cnt' * sizeClass sc; let pSc := sizeToClassUnits u; let needed := cnt' * slotStride sc + 12
  obtain ⟨hsc19, _, hscLtP, hpSc24, hNeedNom, hDepthLt⟩ :
      sc ≤ 19 ∧ (needed + 3) / 16 = u ∧ sc < pSc ∧ pSc ≤ 24 ∧
      needed ≤ nominalSlotCap pSc ∧ allocSlotDepthBound pSc < allocSlotDepthBound sc :=
    nestedParentSc_spec hsc hv
  have hpSc48 : pSc < 48 := by omega
  have hcnt2 : 2 ≤ cnt' := hv.1; have hcnt32 : cnt' ≤ 32 := hv.2.1
  have ⟨hStrScLo, _⟩ := slotStride_bounds_48 hsc
  have hStrSc2032 : slotStride sc ≤ 2032 := by have := Nat.mul_le_mul_right (slotStride sc) hcnt2; have := hv.2.2.1; omega
  have hd_sz : allocSlotDepthBound sc ≤ 3 := by unfold allocSlotDepthBound; repeat (first | split | omega)
  let Saved := AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19)
    (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23)
    (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28)
  let RoRest := (maddrs.medCntTab ↦ᵣ medCntTabBytes) ∗ (maddrs.smallCntTab ↦ᵣ smallCntTabBytes) ∗
    (maddrs.debruijnAlloc ↦ᵣ debruijn32Table)
  have hRoSplit : MallocngRoTablesA maddrs =
      ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ RoRest) := by
    unfold MallocngRoTablesA MallocngRoTablesAt; dsimp only [RoRest]
  let PrepF := RoRest ∗ Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗
    (m ↦ₛ List.replicate 40 0#8) ∗
    MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sn.brk liveCost peakCost st1 ∗ MallocngRuntime maddrs tp
  refine SepWP.weaken_pre (P' := (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
      (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ PrepF)
    (Entails.of_eq (by rw [hRoSplit]; dsimp only [PrepF, Saved]; ac_rfl)) ?_
  refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 8) hcl
    (SepWP.mono (wp_nested_call_prep sn sc cnt' PrepF hw768 hr768 hsc hv hpc hrun hx0 hx26) ?_)
  rintro sc0 Pc0 hpcc0 hrc0 ⟨_, hspc0, halc0, hpspc0, hw0_c0, hx1_c0, hw25_c0, hlr_c0, hregs_c0, hPc0⟩ hpermc0 hclc0
  refine SepWP.weaken_pre hPc0 ?_
  let subFr := (allocSlotDepthBound pSc + 1) * 96 + 224; let remFr := allocSlotDepthBound sc * 96 + 224 - subFr
  have hsp_c0 : sc0.sp = s0.sp - 96#64 := hspc0.trans hsp
  have hal_c0 : sc0.spAligned = true := halc0.trans hsAl
  have hProc_c0 : MallocngProcPreserved s0 sc0 := MallocngProcPreserved.trans hProc hpspc0.1
  have htp_c0 : sc0.tpidrEl0 = tp := hProc_c0.2.2.1.trans htp0
  have hbrkS_c0 : sc0.brkStart = brkStart := by obtain ⟨_, _, _, _, _, _, _⟩ := hProc_c0; simp_all
  have hw0_nat : (sc0.readReg32 .x0).toNat = pSc := by
    rw [hw0_c0, BitVec.toNat_ofNat]; dsimp only [pSc, u] at hpSc24 ⊢; exact Nat.mod_eq_of_lt (by omega)
  have hx1_nat : (sc0.readReg64 .x1).toNat = needed := by
    rw [hx1_c0, BitVec.toNat_ofNat]; dsimp only [needed]; exact Nat.mod_eq_of_lt (by have := hv.2.2.1; omega)
  have hStkSp : stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) =
      (stackFrame sc0 subFr ∗ stackFrameAt (s0.sp - 96#64 - BitVec.ofNat 64 subFr) remFr) := by
    rw [stackFrameAt_split_top (s0.sp - 96#64) subFr _ (by dsimp only [subFr]; omega) (by omega),
        solver_stackFrameAt_eq_memRegion (s0.sp - 96#64) subFr (by dsimp only [subFr]; omega)]; unfold stackFrame; rw [hsp_c0]
  have h19c := (hregs_c0 .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx19
  have h20c := (hregs_c0 .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20
  have h21c := (hregs_c0 .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx21
  have h22c := (hregs_c0 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22
  have h23c := (hregs_c0 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23
  have h24c := (hregs_c0 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24
  have h26c := (hregs_c0 .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26
  have h28c := (hregs_c0 .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx28
  have hPreFold : ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ PrepF) =
      (stackFrame sc0 subFr ∗ MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sc0.brk liveCost peakCost st1 ∗
       MallocngRuntime maddrs tp ∗ Saved ∗ stackFrameAt (s0.sp - 96#64 - BitVec.ofNat 64 subFr) remFr ∗
       (m ↦ₛ List.replicate 40 0#8)) := by
    dsimp only [PrepF]; rw [hStkSp, ← hpspc0.2.1, hRoSplit]; ac_rfl
  refine call_withCL_frame_auto (x := ())
    (hRec pSc hpSc48 hDepthLt needed (inflight + 1) hpSc48 hNeedNom (by omega) γ tp brkStart
      liveCost peakCost maxGroups maxMetaAreas st1 hGroups1 hRel1.2.2.2 hMetaStep)
    hclc0 hpcc0 hrc0 hal_c0 hlr_c0 (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_
    (by intro R h; dsimp only; rw [hPreFold] at h
        rw [pure_sepConj_of_true ⟨htp_c0, hbrkS_c0, hw0_nat, hx1_nat⟩]; revert R h; sep_frame)
    (fun R' sf _ ho => by
      have ho' := Satisfies.drop_mid ho; rw [satisfies_pure_sepConj] at ho' ⊢
      exact ⟨oom_from_recAllocSlot_fine (by omega) hProc_c0 (mappedDelta_perm_right hDelta1 hpermc0) ho'.1, ho'.2⟩)
  intro s_ret hpc_r hrun_r hsp_r hcs_r hcl_r; dsimp only; simp only [sepConj_assoc, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro st2; apply SepWP.exists_elim; intro pIdx; apply SepWP.pure_elim
  rintro ⟨hProc_r, hRes2_1, hLive2_1, hCost2_1, hCnt2_1, hMa2_1, hActLow2, hw0_r, _,
    ⟨pg, hpg, hpScA, hpIdx, hpSc, _, hPgMetaEq, hClaimed, _⟩, hParentTrace1, hOrph2, hDelta2⟩
  have hsp_r0 : s_ret.sp = s0.sp - 96#64 := hsp_r.trans hsp_c0
  have hal_r : s_ret.spAligned = true := by rw [State.spAligned, hsp_r]; simpa [State.spAligned] using hal_c0
  have hw25_r : s_ret.readReg32 .x25 = BitVec.ofNat 32 pSc := by simp only [State.readReg32, hcs_r.2.2.2.2.2.2.1]; exact hw25_c0
  have h19r := hcs_r.1.trans h19c; have h20r := hcs_r.2.1.trans h20c; have h21r := hcs_r.2.2.1.trans h21c
  have h22r := hcs_r.2.2.2.1.trans h22c; have h23r := hcs_r.2.2.2.2.1.trans h23c
  have h24r := hcs_r.2.2.2.2.2.1.trans h24c; have h26r := hcs_r.2.2.2.2.2.2.2.1.trans h26c
  have h28r := hcs_r.2.2.2.2.2.2.2.2.2.1.trans h28c
  unfold MallocngCoreStInflightA MallocngRuntime
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro errnoVal
  simp only [show ∀ (P : SepProp) (φ : Prop) (Q : SepProp), P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) from
    fun P _ _ => by rw [← sepConj_assoc, sepConj_comm P, sepConj_assoc]]
  apply SepWP.pure_elim; intro hwf2
  obtain ⟨hActL2, hUseL2, hUnmL2, hBncL2, _, hLstL2⟩ := hwf2.ctx_lens
  obtain ⟨CtxRest, hCtxSp, hCtxFd⟩ := ctx_split_fields maddrs.ctx st2.ctx hActL2 hUseL2 hUnmL2 hBncL2
  obtain ⟨hpIdx31, hpLast31, hMap52, hpgNested, hMapHi, hpStrLo, hpStrDiv, hStrLe, hStrHi, hStrDiv,
    hEndStor, hpStNat, hpEnNat, hpSbNat, hpStorNat, hMemHi, hSbEnd, hbsLen, hbs0, hbsEnd, PgRest, hBmSplit, hPgResid⟩ :=
    claimed_parent_extract hwf2 hpg hpIdx hClaimed hpSc hpSc24
  let slotBase := pg.slotStart pIdx - 4#64; let bs := readBytesFromMap st2.byteVal slotBase (pg.stride + 1)
  obtain ⟨ActPRest, hActPSp, hActPUp⟩ := words64_focus_set (maddrs.ctx + 80#64) st2.ctx.active pSc hpScA
  let RestCore := MallocngLiveAuth γ st2.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗ ((maddrs.libc + 8#64) ↦₆₄ st2.auxvPtr) ∗
    MallocngAuxvState γ st2.auxvPtr st2.auxvSnap ∗ ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal ∗
    MappedSet st2.masterDom (OwnedMappedByte st2) ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
    ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
  let MHead := (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦₆₄ 0#64) ∗ ((m + 24#64) ↦₃₂ 0#32) ∗ ((m + 28#64) ↦₃₂ 0#32)
  let CtxTail := ((maddrs.ctx + 464#64) ↦₆₄* st2.ctx.usageByClass) ∗ ((maddrs.ctx + 848#64) ↦ₛ st2.ctx.unmapSeq) ∗
    ((maddrs.ctx + 880#64) ↦ₛ st2.ctx.bounces) ∗ ((maddrs.ctx + 912#64) ↦₈ st2.ctx.seq) ∗ CtxRest
  let InvTail := Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MHead ∗ CtxTail ∗ RestCore
  let PostLoadTail := ((maddrs.ctx + 12#64) ↦₃₂ st2.ctx.mmapCounter) ∗ ((maddrs.ctx + 80#64) ↦₆₄* st2.ctx.active) ∗ MallocngRoTablesA maddrs ∗ InvTail
  let Resid := ByteMap st2.masterDom (fun a => OwnedRwByte st2 a ∧ ¬ InRegion slotBase (pg.stride + 1) a) st2.byteVal
  let LoadF := ActPRest ∗ ((maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ RoRest) ∗ (slotBase ↦ₛ bs) ∗ PgRest ∗ ((m + 32#64) ↦₆₄ 0#64) ∗ InvTail
  have hActPFold : (((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * pSc)) ↦₆₄ pg.metaPtr) ∗ ActPRest) =
      ((maddrs.ctx + 80#64) ↦₆₄* st2.ctx.active) := by rw [hActPUp pg.metaPtr, hPgMetaEq, List.set_getElem_self]
  refine SepWP.weaken_pre (P' := ((maddrs.ctx + 12#64) ↦₃₂ st2.ctx.mmapCounter) ∗
      ((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * pSc)) ↦₆₄ pg.metaPtr) ∗
      (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (pg.metaPtr ↦ₛ pg.metaBytes) ∗ LoadF)
    (Entails.of_eq (by
      dsimp only [subFr, remFr, pSc, u] at hStkSp
      dsimp only [LoadF, InvTail, CtxTail, MHead, RestCore, Saved, bs, slotBase, subFr, remFr, pSc, u]
      rw [hStkSp, hRoSplit, hCtxSp, hActPSp, ← hPgMetaEq, hBmSplit, split_rep40_zero m]; ac_rfl)) ?_
  refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 8 + allocSlotOff_pub_add) hcl_r ?_
  refine SepWP.seq (wp_nested_enframe_load s_ret st2.ctx.mmapCounter pSc pIdx pg LoadF
      hw768 hr768 hpSc24 hpIdx31 hpSc hpLast31 hMap52 hpgNested hMapHi hpc_r hrun_r hw0_r hw25_r h22r h26r) ?_
  rintro sA PA hpcA hrunA ⟨_, hspA, halA, hpspA, hx1A, _, hx3A, hw5A, hx6A, hx7A, hrA, hPA⟩; rw [hPA]
  have h19A := (hrA .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h19r
  have h20A := (hrA .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h20r
  have h21A := (hrA .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h21r
  have h22A := (hrA .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22r
  have h23A := (hrA .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23r
  have h24A := (hrA .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24r
  have h28A := (hrA .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28r
  let OffF := PgRest ∗ ((m + 32#64) ↦₆₄ 0#64) ∗ PostLoadTail
  refine SepWP.weaken_pre (P' := (pg.metaPtr ↦ₛ pg.metaBytes) ∗ (slotBase ↦ₛ bs) ∗ OffF)
    (Entails.of_eq (by dsimp only [LoadF, OffF, PostLoadTail]; rw [← hActPFold, hRoSplit]; ac_rfl)) ?_
  refine SepWP.seq (wp_nested_enframe_off sA pSc pIdx pg bs OffF hw768 hr768 hpIdx31 hpStrLo hStrLe hStrHi hbsLen hbs0 hpcA hrunA hx1A hx3A hw5A hx6A hx7A) ?_
  rintro sB PB hpcB hrunB ⟨off, hoffLe, _, hspB, halB, hpspB, hx0B, hx1B, hx2B, hx4B, hw5B, hx6B, hx7B, hx8B, hrB, hPB⟩; rw [hPB]
  obtain ⟨hNoWrap, hFit, hSbMb16, hSbMb4, hMbLo, hMbAl, hMbEnd, hOffUnits, hCapLe⟩ :=
    enframe_geom_bounds pg pSc pIdx off sc cnt' hpStNat hpEnNat hpSbNat hpStorNat hMemHi hpStrLo hStrLe hStrHi hEndStor hoffLe hNeedNom
  let mb := pg.slotStart pIdx + BitVec.ofNat 64 (16 * off)
  have h19B := (hrB .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h19A
  have h20B := (hrB .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h20A
  have h21B := (hrB .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h21A
  have h22B := (hrB .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22A
  have h23B := (hrB .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23A
  have h24B := (hrB .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24A
  have h28B := (hrB .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28A
  refine SepWP.seq (wp_enframe_step_off sB pSc pIdx off pg bs OffF hw768 hr768 hpStrLo hStrLe hStrHi hoffLe hbsLen hbs0 hbsEnd hpcB hrunB hx0B hx1B hx2B hx4B hw5B hx6B hx7B hx8B) ?_
  rintro sC PC hpcC hrunC ⟨_, hspC, halC, hpspC, hx0C, hx1C, hx4C, hw5C, hx6C, hx8C, hrC, bs1, hbs1L, hbs1_0, hbs1_off, hbs1_end, hPC⟩; rw [hPC]
  have h19C := (hrC .x19 (by decide) (by decide) (by decide)).trans h19B; have h20C := (hrC .x20 (by decide) (by decide) (by decide)).trans h20B
  have h21C := (hrC .x21 (by decide) (by decide) (by decide)).trans h21B; have h22C := (hrC .x22 (by decide) (by decide) (by decide)).trans h22B
  have h23C := (hrC .x23 (by decide) (by decide) (by decide)).trans h23B; have h24C := (hrC .x24 (by decide) (by decide) (by decide)).trans h24B
  have h28C := (hrC .x28 (by decide) (by decide) (by decide)).trans h28B
  let RsvF := ((m + 32#64) ↦₆₄ 0#64) ∗ Resid ∗ PostLoadTail
  refine SepWP.weaken_pre (P' := (slotBase ↦ₛ bs1) ∗ RsvF)
    (Entails.of_eq (by dsimp only [OffF, RsvF, Resid, slotBase]; rw [← hPgResid]; ac_rfl)) ?_
  refine SepWP.seq (wp_enframe_step_rsv sC pSc pIdx off pg bs1 RsvF hw768 hr768 hpIdx31 hpStrLo hpStrDiv hStrHi hStrDiv hoffLe hStrLe hNoWrap hbs1L hbs1_0 hbs1_off hbs1_end hpcC hrunC hx0C hx1C hx4C hw5C hx6C hx8C) ?_
  rintro sD PD hpcD hrunD ⟨_, hspD, halD, hpspD, hx0D, hw1D, hw6D, hrD, bs2, hbs2L, hbs2_0, hbs2_off, _, hbs2_2, hbs2_3, hbs2_end, hPD⟩; rw [hPD]
  have h19D := (hrD .x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h19C
  have h20D := (hrD .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h20C
  have h21D := (hrD .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h21C
  have h22D := (hrD .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22C
  have h23D := (hrD .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23C
  have h24D := (hrD .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24C
  have h28D := (hrD .x28 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28C
  let FinF := Resid ∗ PostLoadTail
  refine SepWP.weaken_pre (P' := ((m + 32#64) ↦₆₄ 0#64) ∗ (slotBase ↦ₛ bs2) ∗ FinF)
    (Entails.of_eq (by dsimp only [RsvF, FinF]; ac_rfl)) ?_
  refine SepWP.seq (wp_enframe_step_fin sD pIdx off cnt' m pg bs2 FinF hw768 hr768 hpIdx31 hcnt32 (by rw [hbs2L]; omega) hpcD hrunD hx0D hw1D hw6D h19D h20D) ?_
  rintro sE PE hpcE hrunE ⟨_, hspE, halE, hpspE, hx0E, hx1E, hw2E, hw3E, hrE, hbs3L, hbs3_1, hbs3_out, hPE⟩; rw [hPE]
  let bTag := BitVec.ofNat 8 ((6 <<< 5) ||| pIdx); let bs3 := replaceSlice bs2 (16 * off + 1) [bTag]
  have h19E := (hrE .x19 (by decide) (by decide) (by decide) (by decide)).trans h19D
  have h20E := (hrE .x20 (by decide) (by decide) (by decide) (by decide)).trans h20D
  have h21E := (hrE .x21 (by decide) (by decide) (by decide) (by decide)).trans h21D
  have h22E := (hrE .x22 (by decide) (by decide) (by decide) (by decide)).trans h22D
  have h23E := (hrE .x23 (by decide) (by decide) (by decide) (by decide)).trans h23D
  have h24E := (hrE .x24 (by decide) (by decide) (by decide) (by decide)).trans h24D
  have h28E := (hrE .x28 (by decide) (by decide) (by decide) (by decide)).trans h28D
  refine SepWP.weaken_pre (P' := (slotBase ↦ₛ bs3) ∗ RsvF)
    (Entails.of_eq (by dsimp only [FinF, RsvF, slotBase, bs3, bTag]; ac_rfl)) ?_
  refine SepWP.mono (wp_nested_zero_loop (cnt' + 1) 0 cnt' (slotStride sc) (16 * off + 16) sE slotBase mb bs3 RsvF
      hw768 (by omega) (by omega) hcnt2 hcnt32 hStrScLo hStrSc2032 hSbMb16
      (by rw [hbs3L, hbs2L]; omega) (by rw [hbs3L, hbs2L]; omega)
      hpcE hrunE (by simpa using hx1E) hw2E hw3E h20E h24E) ?_
  rintro spub Ppub hpcpub hrpub ⟨_, hspF, halF, hpspF, hx1_p, hx2_p, hrF, bs', hbs'L, hbs'Z, hbs'Out, hPpub⟩ hperm_p _
  refine SepWP.weaken_pre hPpub ?_
  have hsp_pub : spub.sp = s0.sp - 96#64 := hspF.trans (hspE.trans (hspD.trans (hspC.trans (hspB.trans (hspA.trans hsp_r0)))))
  have hal_pub : spub.spAligned = true := halF.trans (halE.trans (halD.trans (halC.trans (halB.trans (halA.trans hal_r)))))
  have hpsp_pub : PureStatePres s_ret spub := hpspA.trans (hpspB.trans (hpspC.trans (hpspD.trans (hpspE.trans hpspF))))
  have hx0_p : spub.readReg64 .x0 = mb := (hrF .x0 (by decide) (by decide)).trans hx0E
  have h19_p := (hrF .x19 (by decide) (by decide)).trans h19E; have h21_p := (hrF .x21 (by decide) (by decide)).trans h21E
  have h22_p := (hrF .x22 (by decide) (by decide)).trans h22E; have h23_p := (hrF .x23 (by decide) (by decide)).trans h23E
  have h28_p := (hrF .x28 (by decide) (by decide)).trans h28E
  let lastIdx := cnt' - 1
  have hscA2 : sc < st2.ctx.active.length := by omega
  have hscU2 : sc < st2.ctx.usageByClass.length := by omega
  have hscL2 : sc < st2.activeLists.length := by omega
  have hAct2_sc0 : st2.ctx.active[sc]'hscA2 = 0#64 := (hActLow2 sc hscLtP hscA2 (by omega)).trans (hAct0 (by omega))
  have hbs'LenEq : bs'.length = pg.stride + 1 := hbs'L.trans (hbs3L.trans hbs2L)
  obtain ⟨ActRest, hActSp, hActUp⟩ := words64_focus_set (maddrs.ctx + 80#64) st2.ctx.active sc hscA2
  obtain ⟨UseRest, hUseSp, hUseUp⟩ := words64_focus_set (maddrs.ctx + 464#64) st2.ctx.usageByClass sc hscU2
  have hHdrFit : (16 * off + 4) + 9 ≤ bs'.length := by rw [hbs'LenEq]; omega
  obtain ⟨mb0, b8Old, hSlotHdrSp⟩ := split_slot_hdr9 slotBase bs' hHdrFit; rw [hSbMb4] at hSlotHdrSp
  let PubF := ((maddrs.ctx + 12#64) ↦₃₂ st2.ctx.mmapCounter) ∗ ActRest ∗ UseRest ∗
    ((maddrs.ctx + 848#64) ↦ₛ st2.ctx.unmapSeq) ∗ ((maddrs.ctx + 880#64) ↦ₛ st2.ctx.bounces) ∗
    ((maddrs.ctx + 912#64) ↦₈ st2.ctx.seq) ∗ CtxRest ∗ (slotBase ↦ₛ bs'.take (16 * off + 4)) ∗
    ((slotBase + BitVec.ofNat 64 (16 * off + 4 + 9)) ↦ₛ bs'.drop (16 * off + 4 + 9)) ∗
    Resid ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗ RestCore
  refine SepWP.weaken_pre (P' := ((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ 0#64) ∗
      ((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ (st2.ctx.usageByClass[sc]'hscU2)) ∗
      (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦₆₄ 0#64) ∗ ((m + 24#64) ↦₃₂ 0#32) ∗ ((m + 28#64) ↦₃₂ 0#32) ∗
      ((m + 32#64) ↦₆₄ (BitVec.ofNat 64 0 <<< 12)) ∗ (mb ↦₆₄ mb0) ∗ ((mb + 8#64) ↦₈ b8Old) ∗
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x27) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x28) ∗ PubF)
    (Entails.of_eq (by
      rw [show (BitVec.ofNat 64 0 <<< 12) = 0#64 by decide]
      dsimp only [RsvF, PostLoadTail, InvTail, CtxTail, MHead, Saved, AllocSlotSaved12, PubF, mb]
      rw [hActSp, hAct2_sc0, hUseSp, hSlotHdrSp]; ac_rfl)) ?_
  refine SepWP.mono (wp_publish_new_group s0.sp (s0.readReg64 .x30) m mb (st2.ctx.usageByClass[sc]'hscU2)
      0#64 mb0 0#32 0#32 b8Old (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27)
      (s0.readReg64 .x28) (s0.readReg64 .x29) sc lastIdx lastIdx 0 (some pg.metaPtr) (slotStride pg.sc - 4) false PubF _
      hw564 hw768 hr768 hsc (by omega) (Nat.le_refl _) hpcpub hrpub hsp_pub hal_pub h22_p h23_p h21_p h19_p
      hx0_p hx1_p hx2_p (by dsimp only [lastIdx]; rw [Nat.sub_add_cancel (by omega)]; exact h28_p)) ?_
  rintro sf P_f _ _ ⟨_, hsp_f, _, hpsp_f, hperm_f, hx0_f, h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, _, actB, hActB, hPf⟩
  have hbrk_f : sf.brk = s_ret.brk := hpsp_f.2.1.trans hpsp_pub.2.1
  have hwf2' : MallocngWFInflight ((inflight + 1) + 1) maddrs.base brkStart sf.brk liveCost peakCost st2 := hbrk_f.symm ▸ hwf2
  let slotBs' := replaceSlice bs' (16 * off + 4) (unpack64 m ++ [actB])
  obtain ⟨hSlotL, hVStart, hVEnd, hVMb4, hVMb3, hVMb2, hVMb0, hVMb8, hVCgEnd, hVCgHdr⟩ :=
    enframe_slot_bytes_wf st2.byteVal pg pIdx off sc cnt' m actB bs2 bs3 bs' hcnt2 hFit hStrHi
      hSbEnd hSbMb4 hbs2L hbs2_0 hbs2_off hbs2_2 hbs2_3 hbs2_end hbs3L hbs3_1 hbs3_out hbs'L hbs'Z hbs'Out
  obtain ⟨hwf', hCost', hCount', hNotMmap, hBmRw, hBmPn, hMpEq⟩ :=
    wf_alloc_nested hwf2' hsc hscA2 hscL2 hscU2 hAct2_sc0 (hRes2_1.trans hRes1) hpg hpIdx hClaimed
      (hpSc ▸ hpSc24) (hpSc ▸ hscLtP) (by omega : 1 ≤ lastIdx) (by omega : lastIdx ≤ 31)
      (by rw [hActB]; exact Nat.le_refl _) (by rw [hActB]; omega) hMbLo hMbAl (hpSc ▸ hMbEnd) hOffUnits
      (by dsimp only [lastIdx]; rw [Nat.sub_add_cancel (by omega), hpSc]; exact hCapLe)
      hSlotL hVStart hVEnd hVMb4 hVMb3 hVMb2 hVMb0 hVMb8 hVCgEnd hVCgHdr
  let initAvail : BitVec 32 := (2#32 <<< BitVec.ofNat 32 ((actB &&& 0x1f#8).toNat)) - 1#32
  let cg : GroupDesc := {
    metaPtr := m, prev := m, next := m, mem := mb, availMask := initAvail - 1#32,
    freedMask := (2#32 <<< BitVec.ofNat 32 lastIdx) + ~~~initAvail, lastIdx := lastIdx, sc := sc, maplen := 0,
    activeByte := actB, parentMeta := some pg.metaPtr, nestedCap := slotStride pg.sc - 4,
    slots := newGroupSlots lastIdx ((actB &&& 0x1f#8).toNat), freshZero := false }
  let f : GroupDesc → GroupDesc := fun g =>
    if g.metaPtr == pg.metaPtr then { pg with slots := pg.slots.set pIdx (.liveNested m) } else g
  let ctx' : CtxFields := { st2.ctx with
    active := st2.ctx.active.set sc m,
    usageByClass := st2.ctx.usageByClass.set sc (st2.ctx.usageByClass[sc]'hscU2 + BitVec.ofNat 64 cg.cnt) }
  let st' : MallocngSt := { st2 with
    ctx := ctx', reservedMetas := st0.reservedMetas, groups := cg :: st2.groups.map f,
    activeLists := st2.activeLists.set sc [m], masterDom := extendDom st2.masterDom m 40,
    byteVal := writeBytesToMap (writeBytesToMap st2.byteVal slotBase slotBs') m cg.metaBytes }
  have hProc_f : MallocngProcPreserved s0 sf :=
    MallocngProcPreserved.trans (MallocngProcPreserved.trans (MallocngProcPreserved.trans hProc_c0 hProc_r) hpsp_pub.1) hpsp_f.1
  have hvr_f : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
    hpsp_f.2.2.trans (hpsp_pub.2.2.trans (hcs_r.2.2.2.2.2.2.2.2.2.2.2.trans (hpspc0.2.2.trans hvr0)))
  refine ⟨?_, hsp_f, calleeSaved_of_epilogue h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvr_f⟩
  refine Entails.trans ?_ (Entails.sepExists_intro st')
  refine Entails.trans ?_ (Entails.sepExists_intro 0)
  have hDynEq : dynamicRootRegions st' = dynamicRootRegions st2 := by
    dsimp +zeta only [dynamicRootRegions, st', cg, f]
    rw [List.filter_cons_of_neg (by simp), groups_set_claimed_roots st2.groups hwf2.groups_nodup.1 hpg pIdx m]
  have hOrph1' : MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st1) s0.mem sc0.mem :=
    fun a ha hsrc => hOrph1 a (hpermc0 ▸ ha) hsrc
  have hOrph2' : MallocngNoOrphanMappings (dynamicRootRegions st1) (dynamicRootRegions st') sc0.mem sf.mem :=
    fun a ha hsrc => hDynEq ▸ hOrph2 a ((hperm_f.trans hperm_p) ▸ ha) hsrc
  have hParentTrace : AllocSlotFineTrace rootParamPred maddrs.base brkStart liveCost peakCost
      (inflight + 1) (sizeToClassUnits (cnt' * sizeClass sc)) (cnt' * slotStride sc + 12) st_ag st2 pIdx :=
    AllocSlotFineTrace.prepend_sameGroups (hGrp1_ag ▸ SameGroupsSlotKind.refl st_ag.groups) hParentTrace1
  have hTrace : AllocSlotFineTrace rootParamPred maddrs.base brkStart liveCost peakCost inflight sc req st0 st' 0 :=
    .nestedGroup hSame0 hwfAg hAct0_ag hv hParentTrace ⟨hpg, hpSc, hpIdx, hClaimed⟩
      ⟨rfl, rfl, rfl, rfl, rfl, by dsimp +zeta only [cg, lastIdx]; rw [hActB]⟩ rfl
  rw [pure_sepConj_of_true (by
    refine ⟨hProc_f, rfl, hLive2_1.trans hRel1.1, hCost'.trans (hCost2_1.trans hRel1.2.1),
      hCount'.trans (hCnt2_1.trans hRel1.2.2.1), hMa2_1, (fun k hk hk1 hk0 => ?_),
      by simp [State.readReg32, hx0_f], by omega,
      ⟨cg, List.Mem.head _, show sc < (st2.ctx.active.set sc m).length by simp [hscA2],
        show 0 < (newGroupSlots lastIdx _).length by simp [newGroupSlots], rfl,
        by simp [GroupDesc.stride, cg]; rw [show nominalSlotCap sc = slotStride sc - 4 from rfl] at hReq; omega,
        show m = (st2.ctx.active.set sc m)[sc]'_ by simp, rfl, fun hm => by rw [hNotMmap] at hm; cases hm⟩,
      hTrace, mallocngNoOrphanMappings_trans hOrph1' hOrph2',
      nested_mappedDelta_combine_fine (by omega) hDelta1 hpermc0 hDelta2 (hperm_f.trans hperm_p)⟩
    dsimp +zeta only [st', ctx'] at hk1 ⊢; rw [List.getElem_set_ne (by omega : sc ≠ k)]
    exact (hActLow2 k (by omega) (by simpa using hk1) (by omega)).trans (hActLow1 k hk (by omega) hk0))]
  have hcg_meta : cg = {
      metaPtr := m, prev := m, next := m, mem := mb,
      availMask := ((2#32 <<< BitVec.ofNat 32 lastIdx) - 1#32) - 1#32,
      freedMask := (2#32 <<< BitVec.ofNat 32 lastIdx) + ~~~((2#32 <<< BitVec.ofNat 32 lastIdx) - 1#32),
      lastIdx := lastIdx, sc := sc, maplen := 0, activeByte := actB,
      parentMeta := some pg.metaPtr, nestedCap := slotStride pg.sc - 4,
      slots := newGroupSlots lastIdx lastIdx, freshZero := false } := by
    dsimp +zeta only [cg, initAvail]; rw [hActB]
  dsimp only at hPf; rw [← hcg_meta] at hPf; subst hPf
  have hCtxEq : (((maddrs.ctx + 12#64) ↦₃₂ st2.ctx.mmapCounter) ∗
      (((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ m) ∗ ActRest) ∗
      (((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ (st2.ctx.usageByClass[sc]'hscU2 + BitVec.ofNat 64 (lastIdx + 1))) ∗ UseRest) ∗
      ((maddrs.ctx + 848#64) ↦ₛ st2.ctx.unmapSeq) ∗ ((maddrs.ctx + 880#64) ↦ₛ st2.ctx.bounces) ∗
      ((maddrs.ctx + 912#64) ↦₈ st2.ctx.seq) ∗ CtxRest) = (maddrs.ctx ↦ₛ ctx'.toBytes) := by
    rw [hActUp, hUseUp]; exact hCtxFd _ _ _ _ _ _ (by simp [hActL2]) (by simp [hUseL2]) hUnmL2 hBncL2
  have hHdrEq : ((mb ↦₆₄ m) ∗ ((mb + 8#64) ↦₈ actB) ∗ (slotBase ↦ₛ bs'.take (16 * off + 4)) ∗
      ((slotBase + BitVec.ofNat 64 (16 * off + 4 + 9)) ↦ₛ bs'.drop (16 * off + 4 + 9))) = (slotBase ↦ₛ slotBs') := by
    have h := fold_slot_hdr9 slotBase bs' hHdrFit m actB; rwa [hSbMb4] at h
  unfold MallocngCoreStInflightA MallocngRuntime; rw [pure_sepConj_of_true hwf']
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_left (Entails.sepExists_intro (P := fun v => (tp - 0xa4#64) ↦₃₂ v) errnoVal)))))
  have hJoin := saved12_rejoin_stackFrame s0 sc (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19)
    (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
    (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28)
  dsimp only [AllocSlotSaved12] at hJoin; refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left hJoin)
  dsimp only [PubF, RestCore, Resid, slotBase, slotBs', mb, st', ctx', cg, initAvail, lastIdx] at hCtxEq hHdrEq ⊢
  rw [← hCtxEq, ← hBmRw, ← hHdrEq, ← hBmPn, ← hMpEq]; ac_rfl

/-! ## Placed `alloc_group` Trace Theorem -/

set_option maxHeartbeats 800000 in
/-- Verification of placed `alloc_group` (`blk08`, `+0x280`), parameterized by
    `AllocMetaFineParamStmt` and `RootSizeSelectParamStmt rootParamPred`, exporting
    `AllocSlotFineTrace` and `allocSlotFineByteBound sc maxMetaAreas`. -/
theorem wp_placed_allocGroup_trace {rootParamPred : Nat → Nat → Nat → Prop}
    (hMeta : AllocMetaFineParamStmt) (hRootSel : RootSizeSelectParamStmt rootParamPred) :
    AllocGroupAtOffFineTraceStmt rootParamPred := by
  intro _ sc req inflight hsc hReq hInflight hRec γ tp brkStart liveCost peakCost maxGroups maxMetaAreas
    st0 st hGroups0 hMeta0 hMetaStep hAct0 hStRel s0 s hcl hpc hrun hsp hsAl htp hbrkS hpsp hperm hx22 hx23 hx21 hx25
  obtain ⟨hSame0, hRes0, hLive0, hCost0, hCnt0, hMa0, hDyn0, hActLow0⟩ := hStRel
  obtain ⟨_, _, ⟨hw564, hr564⟩, ⟨hw712, _⟩, ⟨hw768, hr768⟩⟩ := blk08_segments_noSyscalls
  have hw768_msvc : Blk08HasWords768Msvc := blk08_seg768_msvc.1
  have hd_sz : allocSlotDepthBound sc ≤ 3 := by unfold allocSlotDepthBound; repeat (first | split | omega)
  let Saved := AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19)
    (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23)
    (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28)
  refine SepWP.weaken_pre (P' := (Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗
      MallocngRoTablesA maddrs) ∗ MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
      MallocngRuntime maddrs tp) (Entails.of_eq (by dsimp only [Saved]; ac_rfl)) ?_
  apply sepWP_extract_coreSt_wf; intro hwfAg
  let RoTail := (maddrs.medCntTab ↦ᵣ medCntTabBytes) ∗ (maddrs.smallCntTab ↦ᵣ smallCntTabBytes) ∗
    (maddrs.debruijnAlloc ↦ᵣ debruijn32Table) ∗ (maddrs.debruijnFree ↦ᵣ debruijn32Table)
  have hRoEq : MallocngRoTablesA maddrs = ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ RoTail) := by
    unfold MallocngRoTablesA MallocngRoTablesAt; dsimp only [RoTail]; ac_rfl
  let EntryF := RoTail ∗ Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗
    MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ MallocngRuntime maddrs tp
  refine SepWP.weaken_pre (P' := (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ EntryF)
    (Entails.of_eq (by rw [hRoEq]; dsimp only [EntryF, Saved]; ac_rfl)) ?_
  refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 7) hcl
    (SepWP.mono (wp_ag_entry s sc EntryF hw564 hr564 hsc hpc hrun hx23) ?_)
  rintro scm Pcm hpccm hrcm ⟨_, hspcm, halcm, hpspcm, hx24cm, hx26cm, hx27cm, hlrcm, hregcm, hPcm⟩ hpermcm hclcm
  refine SepWP.weaken_pre (Entails.of_eq hPcm) ?_
  have hsp_cm : scm.sp = s0.sp - 96#64 := hspcm.trans hsp; have hal_cm : scm.spAligned = true := halcm.trans hsAl
  have hpsp_cm : PureStatePres s0 scm := hpsp.trans hpspcm; have hProc_cm : MallocngProcPreserved s0 scm := hpsp_cm.1
  have htp_cm : scm.tpidrEl0 = tp := hProc_cm.2.2.1.trans htp; have hperm_cm0 : scm.mem.perm = s0.mem.perm := hpermcm.trans hperm
  have hbrkS_cm : scm.brkStart = brkStart := by obtain ⟨_, _, _, _, _, _, _⟩ := hProc_cm; simp_all
  have hx21cm := (hregcm .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx21
  have hx22cm := (hregcm .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22
  have hx23cm := (hregcm .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23
  have hx25cm := (hregcm .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25
  have hStkSp : stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) =
      (stackFrame scm 224 ∗ stackFrameAt (s0.sp - 96#64 - 224#64) (allocSlotDepthBound sc * 96)) := by
    rw [stackFrameAt_split_top (s0.sp - 96#64) 224 _ (by omega) (by omega),
        solver_stackFrameAt_eq_memRegion (s0.sp - 96#64) 224 (by omega)]
    unfold stackFrame; rw [hsp_cm, show allocSlotDepthBound sc * 96 + 224 - 224 = allocSlotDepthBound sc * 96 by omega]
  have hGroups_st : st.groups.length ≤ maxGroups := hSame0.length_eq.symm ▸ hGroups0
  have hMeta_st : st.metaAreas.length ≤ maxMetaAreas := hMa0.symm ▸ hMeta0
  have hMeta8 := hMeta (P := mallocngBlockProg mmpl 8 msvc) inflight (by omega) γ tp brkStart
    liveCost peakCost maxGroups maxMetaAreas st hGroups_st hMeta_st hMetaStep (by intro pc; simp) rfl
  have hPreMeta : ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ EntryF) =
      (stackFrame scm 224 ∗ MallocngCoreStInflightA inflight γ maddrs brkStart scm.brk liveCost peakCost st ∗
       MallocngRuntime maddrs tp ∗ MallocngRoTablesA maddrs ∗ Saved ∗
       stackFrameAt (s0.sp - 96#64 - 224#64) (allocSlotDepthBound sc * 96)) := by
    dsimp only [EntryF]; rw [hStkSp, ← hpspcm.2.1, hRoEq]; ac_rfl
  refine call_withCL_frame_auto (x := ()) hMeta8 hclcm hpccm hrcm hal_cm hlrcm
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_
    (by intro R h; dsimp only; rw [hPreMeta] at h; rw [pure_sepConj_of_true ⟨htp_cm, hbrkS_cm⟩]; revert R h; sep_frame)
    (fun R' sf _ ho => by
      have ho' := Satisfies.drop_mid ho; rw [satisfies_pure_sepConj] at ho' ⊢
      exact ⟨oom_from_allocMeta_fine hProc_cm hperm_cm0 ho'.1, ho'.2⟩)
  intro sam hpc_am hrun_am hsp_am hcs_am hcl_am; dsimp only; simp only [sepConj_assoc, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro st1; apply SepWP.exists_elim; intro m; apply SepWP.pure_elim
  rintro ⟨hProc_am, hx0_am, hmNe0, _, _, _, _, hRes1_st, hGrp1_st, _, hLive1_st, hCnt1_st, hMa1_st,
    hAct1_st, _, _, _, _, _, hOrph_am, hDelta_am⟩
  have hsp_am0 : sam.sp = s0.sp - 96#64 := hsp_am.trans hsp_cm
  have hProc_am0 : MallocngProcPreserved s0 sam := MallocngProcPreserved.trans hProc_cm hProc_am
  have hvr_am : calleeSavedVRegs sam = calleeSavedVRegs s0 := hcs_am.2.2.2.2.2.2.2.2.2.2.2.trans hpsp_cm.2.2
  have hal_am : sam.spAligned = true := by rw [State.spAligned, hsp_am]; simpa [State.spAligned] using hal_cm
  have hx21_am := hcs_am.2.2.1.trans hx21cm; have hx22_am := hcs_am.2.2.2.1.trans hx22cm
  have hx23_am := hcs_am.2.2.2.2.1.trans hx23cm; have hx24_am := hcs_am.2.2.2.2.2.1.trans hx24cm
  have hx25_am := hcs_am.2.2.2.2.2.2.1.trans hx25cm; have hx26_am := hcs_am.2.2.2.2.2.2.2.1.trans hx26cm
  have hx27_am := hcs_am.2.2.2.2.2.2.2.2.1.trans hx27cm
  have hRes1 : st1.reservedMetas = m :: st0.reservedMetas := hRes1_st.trans (congrArg (m :: ·) hRes0)
  have hGroups1 : st1.groups.length ≤ maxGroups := hGrp1_st.symm ▸ hGroups_st
  have hCost1_st : totalLiveEffCost st1 = totalLiveEffCost st := by unfold totalLiveEffCost; rw [hGrp1_st]
  have hRel1 : st1.liveMap = st0.liveMap ∧ totalLiveEffCost st1 = totalLiveEffCost st0 ∧
      totalLiveCount st1 = totalLiveCount st0 ∧ st1.metaAreas.length ≤ maxMetaAreas :=
    ⟨hLive1_st.trans hLive0, hCost1_st.trans hCost0, hCnt1_st.trans hCnt0, hMa1_st⟩
  have hAct0_1 : ∀ h : sc < st1.ctx.active.length, st1.ctx.active[sc]'h = 0#64 :=
    fun h => by have h' : sc < st.ctx.active.length := hAct1_st ▸ h; simpa [hAct1_st] using hAct0 h'
  have hActLow1 : ∀ k : Nat, k < sc → ∀ hk1 : k < st1.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length,
      st1.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0 :=
    fun k hk hk1 hk0 => by have hk' : k < st.ctx.active.length := hAct1_st ▸ hk1; simpa [hAct1_st] using hActLow0 k hk hk' hk0
  have hOrph_am0 : MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st1) s0.mem sam.mem :=
    fun a ha hsrc => hOrph_am a ha (by rw [hDyn0, hperm_cm0]; exact hsrc)
  have hDelta_am0 : MallocngMappedDelta 1 (32768 * maxMetaAreas) s0.mem sam.mem := mappedDelta_perm_left hperm_cm0 hDelta_am
  unfold MallocngCoreStInflightA
  simp only [sepConj_assoc, show ∀ (P : SepProp) (φ : Prop) (Q : SepProp), P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) from
    fun P _ _ => by rw [← sepConj_assoc, sepConj_comm P, sepConj_assoc]]
  apply SepWP.pure_elim; intro hwf1
  obtain ⟨hActL1, hUseL1, hUnmL1, hBncL1, _, _⟩ := hwf1.ctx_lens
  have hscU1 : sc < st1.ctx.usageByClass.length := by omega
  obtain ⟨CtxRest1, hCtxSp1, _⟩ := ctx_split_fields maddrs.ctx st1.ctx hActL1 hUseL1 hUnmL1 hBncL1
  obtain ⟨UseRest1, hUseSp1, _⟩ := words64_focus_set (maddrs.ctx + 464#64) st1.ctx.usageByClass sc hscU1
  let CoreRest1 := MallocngLiveAuth γ st1.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗ ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗ MallocngAuxvState γ st1.auxvPtr st1.auxvSnap ∗
    ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗ ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
    MappedSet st1.masterDom (OwnedMappedByte st1)
  let CntF := (∃∗ v : BitVec 32, (tp - 0xa4#64) ↦₃₂ v) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗
    ((maddrs.ctx + 12#64) ↦₃₂ st1.ctx.mmapCounter) ∗ ((maddrs.ctx + 80#64) ↦₆₄* st1.ctx.active) ∗
    UseRest1 ∗ ((maddrs.ctx + 848#64) ↦ₛ st1.ctx.unmapSeq) ∗ ((maddrs.ctx + 880#64) ↦ₛ st1.ctx.bounces) ∗
    ((maddrs.ctx + 912#64) ↦₈ st1.ctx.seq) ∗ CtxRest1 ∗ CoreRest1 ∗ (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
    (maddrs.debruijnAlloc ↦ᵣ debruijn32Table) ∗ (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗
    (m ↦ₛ List.replicate 40 0#8) ∗ Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224)
  refine SepWP.weaken_pre (P' := ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
      ((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ (st1.ctx.usageByClass[sc]'hscU1)) ∗
      (maddrs.medCntTab ↦ᵣ medCntTabBytes) ∗ (maddrs.smallCntTab ↦ᵣ smallCntTabBytes) ∗ CntF)
    (Entails.of_eq (by
      unfold MallocngRuntime MallocngRoTablesA MallocngRoTablesAt
      dsimp only [CntF, CoreRest1, Saved, AllocSlotSaved12]; rw [hStkSp, hCtxSp1, hUseSp1]; ac_rfl)) ?_
  refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 8 + allocSlotOff_cnt_join) hcl_am
    (SepWP.mono (wp_alloc_group_cnt_join sam m (st1.ctx.usageByClass[sc]'hscU1) sc CntF
      hw564 hr564 hw712 hw768 hsc hmNe0 hpc_am hrun_am hx0_am hx22_am hx21_am hx23_am hx24_am hx27_am) ?_)
  rintro scj Pcj hpccj hrcj ⟨cnt, hlo, hhi, hprod, h25, hsm, hc1, hcntRaw, _, hspcj, halcj, hpspcj,
    hx19cj, hx2cj, hx4cj, hx20cj, hx21cj, hx23cj, hx22cj, hx24cj, hx27cj, hregcj, hPcj⟩ hpermcj hclcj; rw [hPcj]
  have hx25cj := (hregcj .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25_am
  have hx26cj := (hregcj .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26_am
  have hwf1_cj : MallocngWFInflight (inflight + 1) maddrs.base brkStart scj.brk liveCost peakCost st1 := hpspcj.2.1.symm ▸ hwf1
  let JoinP := Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗
    (m ↦ₛ List.replicate 40 0#8) ∗ MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart scj.brk liveCost peakCost st1 ∗
    MallocngRuntime maddrs tp
  refine SepWP.weaken_pre (P' := JoinP) (Entails.of_eq (by
      dsimp only [JoinP, CntF, CoreRest1, Saved]
      unfold MallocngCoreStInflightA MallocngRuntime MallocngRoTablesA MallocngRoTablesAt
      rw [pure_sepConj_of_true hwf1_cj, hCtxSp1, hUseSp1]; ac_rfl)) ?_
  refine wp_cnt_dispatch_mem_fine (s0.readReg64 .x30) scj sc cnt JoinP hw768_msvc hsc hlo hhi hprod h25 hsm hc1
    hpccj hrcj hx20cj hx24cj hx4cj ?_ ?_
  · intro cnt' sn hp_n hr_n hm_n hsp_n hal_n hpsp_n hv hx0_n hx20_n hx28_n hrg_n
    have hperm_n : sn.mem.perm = sam.mem.perm := (congrArg Memory.perm hm_n).trans hpermcj
    rw [show JoinP = (Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗
        MallocngRoTablesA maddrs ∗ (m ↦ₛ List.replicate 40 0#8) ∗
        MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sn.brk liveCost peakCost st1 ∗
        MallocngRuntime maddrs tp) by dsimp only [JoinP]; rw [hpsp_n.2.1]]
    exact wp_allocGroup_nested_trace sc req inflight cnt' hsc hReq hInflight hRec hv γ tp brkStart s.brk m
      liveCost peakCost maxGroups maxMetaAreas st0 st st1 s0 sn hw564 hw768 hr768 hSame0 hwfAg hAct0 hGrp1_st
      hGroups1 hMetaStep hActL1 hAct0_1 hActLow1 hRes1 hRel1
      (fun a ha hsrc => hOrph_am0 a (hperm_n ▸ ha) hsrc) (mappedDelta_perm_right hDelta_am0 hperm_n)
      (hm_n ▸ hclcj) hp_n hr_n (hsp_n.trans (hspcj.trans hsp_am0)) (hal_n.trans (halcj.trans hal_am)) htp hbrkS
      (MallocngProcPreserved.trans (MallocngProcPreserved.trans hProc_am0 hpspcj.1) hpsp_n.1)
      (hpsp_n.2.2.trans (hpspcj.2.2.trans hvr_am)) hx0_n
      ((hrg_n .x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx19cj) hx20_n
      ((hrg_n .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx21cj)
      ((hrg_n .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22cj)
      ((hrg_n .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23cj)
      ((hrg_n .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24cj)
      ((hrg_n .x26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26cj) hx28_n
  · intro cnt' sr hp_r hr_r hm_r hsp_r hal_r hpsp_r hbump hlo_r hhi_r hgt_r hpr_r h25_r hsm_r hx0_r hx6_r hx20_r _ hrg_r
    have hperm_r : sr.mem.perm = sam.mem.perm := (congrArg Memory.perm hm_r).trans hpermcj
    rw [show JoinP = (Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗
        MallocngRoTablesA maddrs ∗ (m ↦ₛ List.replicate 40 0#8) ∗
        MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sr.brk liveCost peakCost st1 ∗
        MallocngRuntime maddrs tp) by dsimp only [JoinP]; rw [hpsp_r.2.1]]
    exact wp_allocGroup_root_trace hRootSel sc req inflight cnt' hsc hReq hlo_r hhi_r hgt_r hpr_r h25_r hsm_r
      (st1.ctx.usageByClass[sc]'hscU1) (by rw [hbump, hcntRaw]; rfl)
      γ tp brkStart s.brk m liveCost peakCost maxMetaAreas st0 st st1 s0 sr
      hw564 hw768 hr768 hSame0 hwfAg hAct0 hGrp1_st hAct0_1 hActLow1 hRes1 hRel1
      (fun a ha hsrc => hOrph_am0 a (hperm_r ▸ ha) hsrc) (mappedDelta_perm_right hDelta_am0 hperm_r)
      (hm_r ▸ hclcj) hp_r hr_r (hsp_r.trans (hspcj.trans hsp_am0)) (hal_r.trans (halcj.trans hal_am)) htp
      (MallocngProcPreserved.trans (MallocngProcPreserved.trans hProc_am0 hpspcj.1) hpsp_r.1)
      (hpsp_r.2.2.trans (hpspcj.2.2.trans hvr_am))
      ((hrg_r .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx4cj)
      ((hrg_r .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx19cj) hx20_r
      ((hrg_r .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx21cj)
      ((hrg_r .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22cj)
      ((hrg_r .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23cj)
      ((hrg_r .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24cj)
      ((hrg_r .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25cj)
      ((hrg_r .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27cj)
      hx0_r ((hrg_r .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx2cj) hx6_r

end LibsignalBinary.Heap.Fine

