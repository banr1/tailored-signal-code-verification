/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplStage2
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Placed `__libc_malloc_impl` Stage 2b

Proves the small and medium allocation path (`req ≤ 131051`) of `__libc_malloc_impl`, covering
the inline `availMask` fast-path claim (`mallocImpl_tryAvail_or_slow`) and the `alloc_slot` slow
path (`mallocImpl_allocSlot_slow`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Symbolic Offsets and Pure Helpers -/

abbrev miOff_try_str        : BitVec 64 := words_insn_off% mallocImplWords 0xb9001ac1#32 0
abbrev miOff_try_ldrb       : BitVec 64 := words_insn_off% mallocImplWords 0x38604877#32 0
abbrev miOff_try_after_ldrb : BitVec 64 := words_insn_off% mallocImplWords 0x92401ef5#32 0
abbrev miOff_slot_ldr22     : BitVec 64 := words_insn_off% mallocImplWords 0xf9402856#32 0
abbrev miOff_slot_b19c      : BitVec 64 := words_insn_off% mallocImplWords 0x17ffffa0#32 0

private theorem at_bl_target_b09 [MallocngMultiPlacement] {b : BitVec 64}
    (_hb : BlkBase 9 b) (j : Nat) (off : BitVec 64) :
    mbase j = b + off + (mbase j - b - off) := by bv_arith

private theorem stackFrame_eq_stackFrameAt {s : State} {sp1 : BitVec 64} (k : Nat)
    (hk : k < 2 ^ 64) (hsp : s.sp = sp1) :
    stackFrame s k = stackFrameAt sp1 k := by
  unfold stackFrame
  rw [hsp, ← stackFrameAt_eq_memRegion sp1 k (hn := Nat.le_of_lt hk)]

private theorem stackFrameAt_624_eq (sp1 : BitVec 64) (k : Nat) (hk : k ≤ 624) :
    stackFrameAt sp1 624 = (stackFrameAt sp1 k ∗ stackFrameAt (sp1 - BitVec.ofNat 64 k) (624 - k)) := by
  have hEq : (624 : Nat) = k + (624 - k) := by omega
  conv => lhs; rw [hEq]
  exact stackFrameAt_split sp1 k (624 - k)

private theorem untouchedCS_of_calleeSaved {s0 s1 s2 : State}
    (h1 : MallocImplUntouchedCS s0 s1) (h2 : CalleeSavedPreserved s1 s2) :
    MallocImplUntouchedCS s0 s2 := by
  obtain ⟨_, _, _, _, _, _, _, h26, h27, h28, _, hv⟩ := h2
  exact ⟨h26.trans h1.1, h27.trans h1.2.1, h28.trans h1.2.2.1, hv.trans h1.2.2.2⟩

private theorem bit31_all_32 :
    (List.range 32).all (fun k => decide ((BitVec.ofNat 32 k).getLsbD 31 = false)) = true := by
  decide

private theorem bit31_false_of_readReg32_ofNat {v : BitVec 64} {idx : Nat}
    (h32 : BitVec.truncate 32 v = BitVec.ofNat 32 idx) (hIdx : idx ≤ 31) :
    v.getLsbD 31 = false ∧
    v[31] = false ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 v) = BitVec.ofNat 64 idx := by
  have h1 : (BitVec.truncate 32 v).getLsbD 31 = v.getLsbD 31 := by
    simp
  have h2 : (BitVec.ofNat 32 idx).getLsbD 31 = false :=
    of_decide_eq_true (List.all_eq_true.mp bit31_all_32 idx (List.mem_range.mpr (by omega)))
  have hg : v.getLsbD 31 = false := by rw [← h1, h32, h2]
  have hz : BitVec.zeroExtend 64 (BitVec.truncate 32 v) = BitVec.ofNat 64 idx := by
    rw [h32]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  exact ⟨hg, hg, hz⟩

private theorem and_u32_eq_zeroExtend_truncate (v : BitVec 64) :
    v &&& 4294967295#64 = BitVec.zeroExtend 64 (BitVec.truncate 32 v) := by
  bv_bits

private theorem sc_sxtw_shl3_all :
    (List.range 48).all (fun k =>
      decide (
        (BitVec.signExtend 64 (BitVec.ofNat 32 k) <<< 3) = BitVec.ofNat 64 (8 * k) ∧
        (BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 k)) <<< 3) =
          BitVec.ofNat 64 (8 * k))) = true := by
  decide

private theorem sc_sxtw_shl3_bv {sc : Nat} (hsc : sc < 48) :
    (BitVec.signExtend 64 (BitVec.ofNat 32 sc) <<< 3) = BitVec.ofNat 64 (8 * sc) ∧
    (BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 sc)) <<< 3) =
      BitVec.ofNat 64 (8 * sc) :=
  of_decide_eq_true (List.all_eq_true.mp sc_sxtw_shl3_all sc (List.mem_range.mpr hsc))

private theorem tryAvail_bv_props {av : BitVec 32} (hAvNe : av ≠ 0#32) :
    let iso := (-av) &&& av
    let hashIdx := ((iso * 0x076be629#32) >>> 27).toNat
    hashIdx < 32 ∧
    BitVec.zeroExtend 64
      ((0#32 + (0#32 - (0#32 - av &&& av) &&& (0#32 - av &&& av)) * 0x076be629#32) >>> 27) =
      BitVec.ofNat 64 hashIdx ∧
    BitVec.truncate 32 (BitVec.zeroExtend 64 av - BitVec.zeroExtend 64 (0#32 - av &&& av)) =
      av - iso ∧
    (∀ b : BitVec 8, (BitVec.ofNat 64 b.toNat) &&& 255#64 = BitVec.ofNat 64 b.toNat) := by
  dsimp only
  obtain ⟨_, _, hHashLt, _, hNegIso, _, _, _⟩ := ctz32DeBruijn_spec hAvNe
  have hSub0 : ∀ x : BitVec 32, 0#32 - x = -x := BitVec.zero_sub
  have hZ : BitVec.zeroExtend 64
      ((0#32 + (0#32 - (0#32 - av &&& av) &&& (0#32 - av &&& av)) * 0x076be629#32) >>> 27) =
      BitVec.ofNat 64 ((((-av) &&& av) * 0x076be629#32) >>> 27).toNat := by
    rw [hSub0 av, hSub0 ((-av) &&& av), BitVec.zero_add, hNegIso]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hTrSub : BitVec.truncate 32 (BitVec.zeroExtend 64 av - BitVec.zeroExtend 64 (0#32 - av &&& av)) =
      av - ((-av) &&& av) := by
    rw [hSub0 av]
    bv_bits
  have hB : ∀ b : BitVec 8, (BitVec.ofNat 64 b.toNat) &&& 255#64 = BitVec.ofNat 64 b.toNat := by
    intro b
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    change b.toNat &&& (2 ^ 8 - 1) = b.toNat
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt hb
  exact ⟨hHashLt, hZ, hTrSub, hB⟩

private theorem bv32_le_or (a b : BitVec 32) : a.toNat ≤ (a ||| b).toNat := by
  change a ≤ a ||| b
  bv_bits

private theorem active_group_stride_ge {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hg : g ∈ st.groups) (_hSc : g.sc < 48) (hAvNe : g.availMask ≠ 0#32) :
    slotStride g.sc ≤ g.stride := by
  by_cases hZ : (g.lastIdx == 0 && decide (0 < g.maplen)) = true
  · have hZ' : g.lastIdx = 0 ∧ 0 < g.maplen := by simpa using hZ
    have hgWf := hwf.groups_wf g hg
    have hCnt1 : g.cnt = 1 := by dsimp [GroupDesc.cnt]; omega
    have hLen1 : g.slots.length = 1 := hgWf.2.2.1.trans hCnt1
    have hOrLt : (g.availMask ||| g.freedMask).toNat < 2 := by
      have h := hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [hCnt1] at h; exact h
    have hAvLt : g.availMask.toNat < 2 := Nat.lt_of_le_of_lt (bv32_le_or _ _) hOrLt
    have hAv1 : g.availMask = 1#32 := by
      apply BitVec.eq_of_toNat_eq
      have h0 : g.availMask.toNat ≠ 0 := fun hz =>
        hAvNe (BitVec.eq_of_toNat_eq (by simpa using hz))
      change g.availMask.toNat = 1; omega
    have hBit0 : g.availMask.getLsbD 0 = true := by rw [hAv1]; decide
    have hSlot0 := (hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 (by omega)).2.1.mp hBit0
    have hEmp : g.isEmpty = true := by
      unfold GroupDesc.isEmpty
      rcases hS : g.slots with _ | ⟨s_hd, _ | _⟩
      · simp [hS] at hLen1
      · simp only [hS, List.getElem_cons_zero] at hSlot0
        subst hSlot0; rfl
      · simp [hS] at hLen1
    have hMapGe := (hwf.empty_groups_bound g hg hEmp).2.2.2.2.2.2 hZ'.1
    have hStr : g.stride = g.maplen * 4096 - 16 := by
      unfold GroupDesc.stride; rw [ite_eq_left hZ]
    omega
  · have hZF : (g.lastIdx == 0 && decide (0 < g.maplen)) = false := by
      cases hB : (g.lastIdx == 0 && decide (0 < g.maplen)) <;> simp_all
    have hStr : g.stride = 16 * sizeClass g.sc := by
      unfold GroupDesc.stride; rw [ite_eq_right (by simp [hZF])]; rfl
    dsimp [slotStride]; omega

/-! ## `alloc_slot` Slow Path -/

set_option maxHeartbeats 400000 in
theorem mallocImpl_allocSlot_slow [MallocngMultiPlacement]
    (hSlot : AllocSlotPlacedFullStmt) (hMetaInv : MallocngMetaCountInv)
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget}
    {ivs0 : List (BitVec 64 × Nat)} {req sc : Nat}
    {st0 : MallocngSt} {s0 s : State}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hCount0 : MallocngCountIvsWF bud ivs0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0)
    (hReqMax : req ≤ MallocngMaxAllocSize)
    (hSc48 : sc < 48) (hFitSc : req ≤ nominalSlotCap sc)
    (hSc2 : 2 ≤ sc ∧ sc < 48 → nominalSlotCap (sc - 2) < max req 16)
    (hSc24 : sc = 24 → nominalSlotCap 23 < req)
    (hSc24M : sc = 24 → nominalSlotCap 23 < max req MallocngMinBlockCost)
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
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ mallocImplSuccessPost24 γ tp brkStart bud ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜MallocngTightOomCond msvc req bud.peakCount s0 sf⌝) := by
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b at hpc ⊢
  have hb : BlkBase 9 b := hb_eq.symm
  have hReqLt64 : req < 2 ^ 64 := by
    have := mallocngMaxAllocSize_eq; omega
  have hSpAl : s.spAligned = true := by
    dsimp [State.spAligned]; rw [hsp]; exact sp_sub_80_aligned hsp_align
  have hDepthLe : 0 + allocSlotDepthBound sc ≤ 6 := by
    have := allocSlotDepthBound_le_three sc; omega
  let stkNeed := (allocSlotDepthBound sc + 1) * 96 + 224
  have hStkLe : stkNeed ≤ 624 := by
    have := allocSlotDepthBound_le_three sc; dsimp [stkNeed]; omega
  have hLiveCntLe : totalLiveCount st0 ≤ bud.peakCount := by
    have := hCount0.1; have := hCount0.2.1; omega
  dsimp only [miOff_alloc_prep] at hpc
  wp_steps 3
  have hSlotCall := subroutine_ok_block_to_block (P := blkPC_b09.rebase b (fun _ => none))
    (j := 8) (by decide)
    (hSlot sc req 0 hSc48 hFitSc hDepthLe γ tp brkStart bud.liveCost bud.peakCost bud.peakCount st0 hLiveCntLe)
  rw [at_bl_target_b09 hb 8 miOff_call_slot] at hSlotCall
  let slotFrame :=
    stackFrameAt ((s0.sp - 80#64) - BitVec.ofNat 64 stkNeed) (624 - stkNeed) ∗
    MallocImplSavedRegs s0 (s0.sp - 80#64)
  refine SepWP.call_subroutine_frame (F := slotFrame) (x := ()) (ret_pc := b + miOff_after_slot)
    hSlotCall rfl
    (by simp [arm64_norm, hrun])
    (by simpa [State.spAligned, arm64_norm] using hSpAl)
    (by dsimp only [miOff_call_slot, miOff_after_slot, Reg.lr]; simp [arm64_norm])
    (fun R' hm => by
      refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
      dsimp only [withCL, slotFrame]
      rw [stackFrame_eq_stackFrameAt stkNeed (by omega) (by simpa [arm64_norm] using hsp),
          stackFrameAt_624_eq (s0.sp - 80#64) stkNeed hStkLe]
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
        MallocngCoreStInflightA 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 = pCr,
        MallocngRuntime maddrs tp = pRt
      ac_rfl)
    (fun R' sf _ hp => by dsimp only [withCL] at hp; exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by dsimp only [withCL] at he; exact not_satisfies_false_sepConj he)
    (fun sm hpc_m hrun_m hsp_m hcs_m => ?_)
    (fun R' sf _ hoom => by
      dsimp only [withCL] at hoom
      rw [satisfies_pure_sepConj] at hoom
      refine Satisfies.pure_intro
        (oomCond_of_allocSlot ?_ hPerm0 hoom.1)
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
  rintro ⟨hProc_m0, hRes1, _hLiveMap1, _hEff1, hCnt1, hMetaLen1, hx0_m, hIdx31,
    ⟨g, hg1, hAct1, hIdxLt, hGsc, hFitG, hMetaEq, hClaimed1, hZeroMm1⟩, hNoOrph_st, hDelta_m, hGrpT⟩
  have hsp_sm : sm.sp = s0.sp - 80#64 := by simpa [arm64_norm] using hsp_m.trans hsp
  rw [stackFrame_eq_stackFrameAt stkNeed (by omega) (by simpa [arm64_norm] using hsp)]
  let coreRest1 :=
    MallocngLiveAuth γ st1.liveMap ∗
    (maddrs.lock ↦₃₂ 0#32) ∗
    (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗
    ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗
    MallocngAuxvState γ st1.auxvPtr st1.auxvSnap ∗
    ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
    MappedSet st1.masterDom (OwnedMappedByte st1)
  have hPullAll :
      ((stackFrameAt (s0.sp - 80#64) stkNeed ∗ MallocngRoTablesA maddrs ∗
        MallocngRuntime maddrs tp ∗
        MallocngCoreStInflightA 1 γ maddrs brkStart sm.brk bud.liveCost bud.peakCost st1) ∗
       ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗ slotFrame) =
      (⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
       ⌜MallocngWFInflight 1 maddrs.base brkStart sm.brk bud.liveCost bud.peakCost st1⌝ ∗
       ((maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗
        (coreRest1 ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp))) := by
    dsimp only [slotFrame, MallocngCoreStInflightA, coreRest1]
    rw [stackFrameAt_624_eq (s0.sp - 80#64) stkNeed hStkLe]
    generalize ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ = pCL,
      ⌜MallocngWFInflight 1 maddrs.base brkStart sm.brk bud.liveCost bud.peakCost st1⌝ = pWf1,
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx,
      MallocngLiveAuth γ st1.liveMap = pGm,
      (maddrs.lock ↦₃₂ 0#32) = pLk,
      (maddrs.replaced ↦₃₂ 0#32) = pRp,
      (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
      ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = pLb8,
      MallocngAuxvState γ st1.auxvPtr st1.auxvSnap = pAx,
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
  have hcs_m' := hcs_m
  obtain ⟨hc19, hc20, _, _, _, hc24, hc25, _⟩ := hcs_m'
  have hx19_sm : sm.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc := by
    simpa [arm64_norm] using hc19.trans (by simp [arm64_norm, hx19])
  have hx20_sm : sm.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req := by
    simpa [arm64_norm] using hc20.trans (by simp [arm64_norm, hx20])
  have hx24_sm : sm.readReg64 (.gpr 24#5) = pageOf maddrs.lock := by
    simpa [arm64_norm] using hc24.trans (by simp [arm64_norm, hx24])
  have hx25_sm : sm.readReg64 (.gpr 25#5) = pageOf maddrs.ctx := by
    simpa [arm64_norm] using hc25.trans (by simp [arm64_norm, hx25])
  have hProc_sm : MallocngProcPreserved s0 sm := by
    refine procPres_trans ?_ hProc_m0
    dsimp only [MallocngProcPreserved] at hProc ⊢
    simp [arm64_norm, hProc]
  have hcsHi_sm : MallocImplUntouchedCS s0 sm :=
    untouchedCS_of_calleeSaved
      (untouchedCS_step hcsHi (by first | rfl | simp [arm64_norm])
        (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
        (by first | rfl | simp [calleeSavedVRegs, arm64_norm]))
      hcs_m
  obtain ⟨hBit31_g, hBit31_e, hZIdx⟩ := bit31_false_of_readReg32_ofNat hx0_m hIdx31
  obtain ⟨hExtSc3, hShlSc3⟩ := sc_sxtw_shl3_bv hSc48
  have hSxMSc := sxtw_sbfm_ofNat hSc48
  have hZ32 : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 idx)) = BitVec.ofNat 64 idx := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have hIdxB31 : (BitVec.ofNat 64 idx).getLsbD 31 = false := by
    have hAll : (List.range 32).all (fun k => decide ((BitVec.ofNat 64 k).getLsbD 31 = false)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr (by omega)))
  refine SepWP.seq (mid := b + miOff_slot_ldr22)
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
         MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp))) ?_ ?_
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
        by simp only [arm64_norm, BitVec.ushiftRight_zero]; rw [and_u32_eq_zeroExtend_truncate, hZ32, BitVec.or_zero],
        by simp only [arm64_norm],
        by simpa using hx24_sm⟩, Entails.refl _⟩
  · rintro s2 P2 hpc2 hrun2 ⟨⟨hsp2, hbrk2, hmem2, hProc2, hcs2, hx2_2, hx19_2, hx20_2, hx21_2, hx23_2, hx24_2⟩, hP2⟩
    apply SepWP.weaken_pre hP2
    have hAddr80 : (maddrs.ctx + BitVec.ofNat 64 (8 * sc)) + 80#64 =
        maddrs.ctx + BitVec.ofNat 64 (80 + 8 * sc) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine SepWP.step_ldr64
      (s' := (s2.writeReg64 (.gpr 22#5) g.metaPtr).setPC (b + miOff_slot_b19c))
      hpc2 hrun2 (by dsimp only [miOff_slot_ldr22]; simp only [arm64_norm]; rfl) rfl
      (ea := maddrs.ctx + BitVec.ofNat 64 (80 + 8 * sc)) (wb := none)
      (by simp [evalAddrMode, hx2_2, hAddr80])
      (SepLoad64.of_pointsToBytes rfl (by omega) rfl)
      (by rw [applyWriteback, hGetAct1, ← hMetaEq, BitVec.add_assoc]; rfl) ?_
    refine SepWP.seq (mid := b + miOff_call_unlock)
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
          MallocngRoTablesA maddrs ∗
          MallocngCoreStInflightA 1 γ maddrs brkStart sm.brk bud.liveCost bud.peakCost st1 ∗
          MallocngRuntime maddrs tp)) ?_ ?_
    · dsimp only [miOff_slot_b19c, miOff_call_unlock]
      wp_steps
      apply SepWP.done
      · simp
      · simp [hrun2]
      · refine ⟨⟨by simp [hsp2], hbrk2, hmem2,
          by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc2,
          untouchedCS_step hcs2 (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
            (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [calleeSavedVRegs, arm64_norm]),
          by first | simp [arm64_norm] | simp [hx24_2, arm64_norm] | simp [State.readReg64, State.writeReg64, State.setPC, RegFile.read, RegFile.write, hx24_2, arm64_norm],
          by first | simpa using hx19_2 | simpa [State.readReg64, State.writeReg64, State.setPC, RegFile.read, RegFile.write, arm64_norm] using hx19_2,
          by first | simpa using hx20_2 | simpa [State.readReg64, State.writeReg64, State.setPC, RegFile.read, RegFile.write, arm64_norm] using hx20_2,
          by first | simpa using hx21_2 | simpa [State.readReg64, State.writeReg64, State.setPC, RegFile.read, RegFile.write, arm64_norm] using hx21_2,
          by simp [arm64_norm, hMetaEq],
          by first | simpa using hx23_2 | simpa [State.readReg64, State.writeReg64, State.setPC, RegFile.read, RegFile.write, arm64_norm] using hx23_2⟩, ?_⟩
        rw [← hCtx1Gen]
        dsimp only [MallocngCoreStInflightA, coreRest1]
        rw [propext ⟨fun _ => trivial, fun _ => hwf1⟩, pure_true, emp_sepConj]
        refine Entails.of_eq ?_
        generalize (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx,
          MallocngLiveAuth γ st1.liveMap = pGm,
          (maddrs.lock ↦₃₂ 0#32) = pLk,
          (maddrs.replaced ↦₃₂ 0#32) = pRp,
          (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
          ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = pLb8,
          MallocngAuxvState γ st1.auxvPtr st1.auxvSnap = pAx,
          ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal = pRw,
          ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
          MappedSet st1.masterDom (OwnedMappedByte st1) = pMs,
          MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
          stackFrameAt (s0.sp - 80#64) 624 = pSf,
          MallocngRoTablesA maddrs = pRo,
          MallocngRuntime maddrs tp = pRt
        ac_rfl
    · rintro s_u P_u hpc_u hrun_u ⟨⟨hsp_u, hbrk_u, hmem_u, hProc_u, hcs_u, hx0_u, hx19_u, hx20_u, hx21_u, hx22_u, hx23_u⟩, hPu⟩
      rw [← hbrk_u] at hPu
      apply SepWP.weaken_pre hPu
      have hcl_u : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_u.mem := hmem_u ▸ hcl_m
      have hwf1_u : MallocngWFInflight 1 maddrs.base brkStart s_u.brk bud.liveCost bud.peakCost st1 :=
        hbrk_u ▸ hwf1
      have hNoRes0 : st0.reservedMetas = [] := by
        have hInf := hwf0.inflight_wf
        cases hR : st0.reservedMetas with
        | nil => rfl
        | cons _ _ => rw [hR] at hInf; simp at hInf
      have hNoRes1 : st1.reservedMetas = [] := hRes1.trans hNoRes0
      have hMetaLe1 : st1.metaAreas.length ≤
          1 + (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101 := by
        have hMeta0 := hMetaInv bud ivs0 st0 hCount0
        have hPeakLe : bud.peakCount ≤ (mallocngAllocBudget true req bud).peakCount := by
          dsimp [mallocngAllocBudget]; omega
        have hDivLe : (88 + 8 * bud.peakCount) / 101 ≤
            (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101 :=
          Nat.div_le_div_right (by omega)
        omega
      dsimp only [State.setPC, State.writeReg64] at hNoOrph_st hDelta_m
      have hNoOrph1 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s_u.mem := by
        rw [hCount0.2.2.1, hmem_u]
        unfold MallocngNoOrphanMappings at hNoOrph_st ⊢
        simpa [hPerm0] using hNoOrph_st
      have hDelta_u : MallocngMappedDelta 16 (MallocngTightStepBound req bud.peakCount) s0.mem s_u.mem := by
        rw [hmem_u]
        have hbStep : allocSlotPlacedByteBound sc bud.peakCount ≤
            MallocngTightStepBound req bud.peakCount := by
          have hb0 := allocSlotPlacedByteBound_le_slotReserve sc bud.peakCount
          unfold Cost.mallocngSlotReserve Cost.mallocngMetaStep at hb0
          rw [MallocngTightStepBound_eq]
          exact Nat.le_trans hb0 (Nat.le_max_left _ _)
        obtain ⟨ivs, hl, hs, hc⟩ := hDelta_m
        exact ⟨ivs, by omega, Nat.le_trans hs hbStep,
          fun a ha => (hc a ha).imp (fun hm => hPerm0 ▸ hm) id⟩
      subst hb_eq
      rw [← mallocngBlockProg_eq_b09]
      have hGrp1 : Cost.GroupsGrpBound ((mallocngAllocBudget true req bud).peakCount + 6) st1.groups :=
        (hGrpT (by have := hwf0.inflight_wf; omega) (bud.peakCount + 6) (by omega) hCount0.2.2.2.2.2).mono
          (by dsimp [mallocngAllocBudget]; omega)
      exact mallocImpl_join_epilogue hcl_u hCount0 hCnt1 hMetaLe1 hGrp1 hNoOrph1 hwf1_u hNoRes1
        hg1 hIdxLt hClaimed1 hReqMax hFitG
        (fun h => by rw [hGsc] at h ⊢; exact hSc2 h)
        (fun h => hSc24 (hGsc ▸ h))
        (fun h => hSc24M (hGsc ▸ h))
        (fun h => by rw [hGsc] at h; omega)
        (fun h => by rw [hGsc] at h; omega)
        hZeroMm1 htp0 hbrkS0 hDelta_u
        hpc_u hrun_u hsp_u hsp_align hProc_u hcs_u
        hx0_u hx19_u hx20_u hx21_u hx22_u hx23_u

/-! ## Inline `try_avail` and Small/Medium Branch -/

private theorem tryAvail_cbz_step [MallocngMultiPlacement] {b target : BitVec 64}
    (hb : BlkBase 9 b) {s0 s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = b + miOff_try_avail) (hrun : s.status = .Running)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx22 : s.readReg64 (.gpr 22#5) = 0#64)
    (hSlow : ∀ s' : State, s'.pc = b + miOff_alloc_prep → s'.status = .Running →
      s'.sp = s.sp → s'.brk = s.brk → s'.mem = s.mem →
      MallocngProcPreserved s0 s' → MallocImplUntouchedCS s0 s' →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      s'.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) →
      SepWP (blkPC_b09.rebase b (fun _ => none)) target s' P post oom) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) target s P post oom := by
  have _ := hb
  dsimp only [miOff_try_avail] at hpc
  simp [State.readReg64] at hx22
  wp_step
  wp_if hCbz
  · exact hSlow _ rfl (by simp [hrun]) (by simp) rfl rfl
      (by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc)
      (untouchedCS_step hcsHi (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]))
      (by simp) (by simp) (by simp) (by simp)
  · exact absurd hx22 hCbz

set_option maxHeartbeats 400000 in
private theorem tryAvail_nonnull_step [MallocngMultiPlacement] {b target : BitVec 64}
    (hb : BlkBase 9 b) {metaPtr : BitVec 64} (hMetaNe : metaPtr ≠ 0#64)
    {metaBs ctxBs debBs : List (BitVec 8)}
    (hmLen : metaBs.length = 40) (hCtxLen : ctxBs.length = 928) (hDebLen : debBs.length = 32)
    {av mmc : BitVec 32}
    (hPkAv : pack32 (metaBs.getD 24 0#8) (metaBs.getD 25 0#8) (metaBs.getD 26 0#8) (metaBs.getD 27 0#8) = av)
    (hPkMmc : pack32 (ctxBs.getD 12 0#8) (ctxBs.getD 13 0#8) (ctxBs.getD 14 0#8) (ctxBs.getD 15 0#8) = mmc)
    {F : SepProp} {s0 s : State}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hpc : s.pc = b + miOff_try_avail) (hrun : s.status = .Running)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx22 : s.readReg64 (.gpr 22#5) = metaPtr)
    (hx24 : s.readReg64 (.gpr 24#5) = pageOf maddrs.lock)
    (hx25 : s.readReg64 (.gpr 25#5) = pageOf maddrs.ctx)
    (hSlow : ∀ s' : State, s'.pc = b + miOff_alloc_prep → s'.status = .Running →
      s'.sp = s.sp → s'.brk = s.brk → s'.mem = s.mem →
      MallocngProcPreserved s0 s' → MallocImplUntouchedCS s0 s' →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 24#5) = pageOf maddrs.lock →
      s'.readReg64 (.gpr 25#5) = pageOf maddrs.ctx →
      SepWP (blkPC_b09.rebase b (fun _ => none)) target s'
        ((metaPtr ↦ₛ metaBs) ∗ (maddrs.ctx ↦ₛ ctxBs) ∗ (maddrs.debruijnFree ↦ᵣ debBs) ∗ F) post oom)
    (hFast : ∀ (_hAvNe : av ≠ 0#32) (s_u : State),
      VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_u.mem →
      s_u.pc = b + miOff_call_unlock → s_u.status = .Running →
      s_u.sp = s.sp → s_u.brk = s.brk → s_u.mem.perm = s.mem.perm →
      MallocngProcPreserved s0 s_u → MallocImplUntouchedCS s0 s_u →
      s_u.readReg64 (.gpr 0#5) = maddrs.lock →
      s_u.readReg64 (.gpr 19#5) = BitVec.zeroExtend 64 mmc →
      s_u.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s_u.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (debBs.getD (((((-av) &&& av) * 0x076be629#32) >>> 27).toNat) 0#8).toNat →
      s_u.readReg64 (.gpr 22#5) = metaPtr →
      s_u.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (debBs.getD (((((-av) &&& av) * 0x076be629#32) >>> 27).toNat) 0#8).toNat →
      SepWP (blkPC_b09.rebase b (fun _ => none)) target s_u
        ((metaPtr ↦ₛ ByteSlice.write32 metaBs 24 (av - ((-av) &&& av))) ∗
         (maddrs.ctx ↦ₛ ctxBs) ∗ (maddrs.debruijnFree ↦ᵣ debBs) ∗ F) post oom) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) target s
      ((metaPtr ↦ₛ metaBs) ∗ (maddrs.ctx ↦ₛ ctxBs) ∗ (maddrs.debruijnFree ↦ᵣ debBs) ∗ F) post oom := by
  have _ := hb
  dsimp only [miOff_try_avail] at hpc
  wp_step
  wp_if hCbz
  · exfalso
    simp [hMetaNe] at hCbz
  · wp_step
    try rw [hPkAv]
    wp_steps 3
    wp_if hAvZero
    · exact hSlow _ rfl (by simp [hrun]) (by simp) rfl rfl
        (by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc)
        (untouchedCS_step hcsHi (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
          (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [calleeSavedVRegs, arm64_norm]))
        (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
        (by first | exact hx24 | simpa [arm64_norm] using hx24)
        (by first | exact hx25 | simpa [arm64_norm] using hx25)
    · have hAvNe : av ≠ 0#32 := by rintro rfl; simp at hAvZero
      obtain ⟨hHashLt, _, _, hAnd255⟩ := tryAvail_bv_props hAvNe
      obtain ⟨_, _, _, _, hNegIso, _, _, _⟩ := ctz32DeBruijn_spec hAvNe
      have hHashZ : BitVec.zeroExtend 64 ((((-av) &&& av) * 0x076be629#32) >>> 27) =
          BitVec.ofNat 64 ((((-av) &&& av) * 0x076be629#32) >>> 27).toNat := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      generalize hHashEq : ((((-av) &&& av) * 0x076be629#32) >>> 27).toNat = hashIdx at hHashLt hHashZ hFast
      have hZHash : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 hashIdx)) =
          BitVec.ofNat 64 hashIdx := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        have h32 : hashIdx < 2 ^ 32 := Nat.lt_trans hHashLt (by decide : 32 < 2 ^ 32)
        have h64 : hashIdx < 2 ^ 64 := Nat.lt_trans hHashLt (by decide : 32 < 2 ^ 64)
        rw [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64]
      refine SepWP.seq (mid := b + miOff_try_str)
        (Mid := fun s_m Pm =>
          (s_m.sp = s.sp ∧ s_m.brk = s.brk ∧ s_m.mem = s.mem ∧
           MallocngProcPreserved s0 s_m ∧ MallocImplUntouchedCS s0 s_m ∧
           s_m.readReg32 (.gpr 0#5) = ((-av) &&& av) * 0x076be629#32 ∧
           s_m.readReg32 (.gpr 1#5) = av - ((-av) &&& av) ∧
           s_m.readReg64 (.gpr 3#5) = maddrs.debruijnFree ∧
           s_m.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
           s_m.readReg64 (.gpr 22#5) = metaPtr ∧
           s_m.readReg64 (.gpr 24#5) = pageOf maddrs.lock ∧
           s_m.readReg64 (.gpr 25#5) = maddrs.ctx) ∧
          (Pm ⊢ (metaPtr ↦ₛ metaBs) ∗ (maddrs.ctx ↦ₛ ctxBs) ∗ (maddrs.debruijnFree ↦ᵣ debBs) ∗ F)) ?_ ?_
      · dsimp only [miOff_try_str]
        wp_steps
        apply SepWP.done
        · simp
        · simp [hrun]
        · refine ⟨⟨by simp, rfl, rfl,
            by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc,
            untouchedCS_step hcsHi (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
              (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [calleeSavedVRegs, arm64_norm]),
            by simp only [arm64_norm, BitVec.zero_sub, BitVec.zero_add, hNegIso],
            by simp only [arm64_norm, BitVec.zero_sub],
            by simp [arm64_norm],
            by first | rfl | simp [arm64_norm],
            by first | exact hx22 | simpa [arm64_norm] using hx22,
            by first | exact hx24 | simpa [arm64_norm] using hx24,
            by first | simp [arm64_norm] | simp [arm64_norm, hx25]⟩, Entails.refl _⟩
      · rintro s_m Pm hpc_m hrun_m ⟨⟨hsp_m, hbrk_m, hmem_m, hProc_m, hcs_m, hx0_m, hx1_m, hx3_m, hx20_m, hx22_m, hx24_m, hx25_m⟩, hPm⟩
        dsimp only [miOff_try_str] at hpc_m
        apply SepWP.weaken_pre hPm
        have hcl_sm : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_m.mem := hmem_m ▸ hcl
        apply step_str32_perm_kf
        · exact hpc_m
        · exact hrun_m
        · simp only [arm64_norm]; rfl
        · rfl
        · simp only [evalAddrMode, hx22_m]; rfl
        · exact hx1_m
        · wp_sep_access
        · wp_norm_lhs
        intro m_w hm_w _hkf
        have hcl_mw := hcl_sm.of_keepsFrozen _hkf; clear _hkf
        have hPerm1 : m_w.perm = s.mem.perm := hm_w.trans (congrArg Memory.perm hmem_m)
        refine SepWP.step_ldr32
          rfl
          (by simp [hrun_m])
          (by simp only [arm64_norm]; rfl)
          rfl
          (ea := maddrs.ctx + 12#64) (wb := none)
          (by change (s_m.readReg64 (.gpr 25#5) + 12#64, none) = (maddrs.ctx + 12#64, none); rw [hx25_m])
          (SepLoad32.right ((SepLoad32.of_pointsToBytes (off := 12) rfl (by rw [hCtxLen]; decide) rfl).congr_val hPkMmc))
          (by wp_norm_lhs) ?_
        wp_step
        refine SepWP.seq (mid := b + miOff_try_ldrb)
          (Mid := fun s1 P1 =>
            (s1.sp = s.sp ∧ s1.brk = s.brk ∧ s1.mem = m_w ∧
             MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
             s1.readReg64 (.gpr 0#5) = BitVec.ofNat 64 hashIdx ∧
             s1.readReg64 (.gpr 3#5) = maddrs.debruijnFree ∧
             s1.readReg64 (.gpr 19#5) = BitVec.zeroExtend 64 mmc ∧
             s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
             s1.readReg64 (.gpr 22#5) = metaPtr ∧
             s1.readReg64 (.gpr 24#5) = pageOf maddrs.lock) ∧
            (P1 ⊢ (maddrs.debruijnFree ↦ᵣ debBs) ∗
              ((metaPtr ↦ₛ ByteSlice.write32 metaBs 24 (av - ((-av) &&& av))) ∗
               (maddrs.ctx ↦ₛ ctxBs) ∗ F))) ?_ ?_
        · apply SepWP.done
          · dsimp only [miOff_try_ldrb]; simp
          · simp [hrun_m]
          · refine ⟨⟨by simp [hsp_m], hbrk_m, rfl,
              by repeat (first | apply procPres_setMem | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc_m,
              untouchedCS_step hcs_m (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
                (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [calleeSavedVRegs, arm64_norm]),
              by dsimp only [State.readReg32] at hx0_m; simp only [arm64_norm, hx0_m]; exact hHashZ,
              by simpa [arm64_norm] using hx3_m,
              by simp only [arm64_norm],
              by simpa [arm64_norm] using hx20_m,
              by simpa [arm64_norm] using hx22_m,
              by simpa [arm64_norm] using hx24_m⟩, ?_⟩
            refine Entails.of_eq ?_
            generalize (metaPtr ↦ₛ ByteSlice.write32 metaBs 24 (av - ((-av) &&& av))) = pM,
              (maddrs.ctx ↦ₛ ctxBs) = pCtx,
              (maddrs.debruijnFree ↦ᵣ debBs) = pDeb
            ac_rfl
        · rintro s1 P1 hpc1 hrun1 ⟨⟨hsp1, hbrk1, hmem1, hProc1, hcs1, hx0_1, hx3_1, hx19_1, hx20_1, hx22_1, hx24_1⟩, hP1⟩
          apply SepWP.weaken_pre hP1
          have hAndIdx : (BitVec.ofNat 64 (debBs.getD hashIdx 0#8).toNat) &&& 255#64 =
              BitVec.ofNat 64 (debBs.getD hashIdx 0#8).toNat := hAnd255 (debBs.getD hashIdx 0#8)
          generalize hIdxEq : (debBs.getD hashIdx 0#8).toNat = idx at hAndIdx hFast
          refine SepWP.step_ldr8
            (s' := (s1.writeReg64 (.gpr 23#5) (BitVec.ofNat 64 idx)).setPC (b + miOff_try_after_ldrb))
            hpc1 hrun1 (by dsimp only [miOff_try_ldrb]; simp only [arm64_norm]; rfl) rfl
            (ea := maddrs.debruijnFree + BitVec.ofNat 64 hashIdx) (wb := none)
            (by simp only [evalAddrMode, extendVal, hx3_1, hx0_1]; rw [hZHash, BitVec.shiftLeft_zero])
            (SepLoad8.of_pointsToBytesRO rfl (Nat.succ_le_of_lt (hDebLen.symm ▸ hHashLt)) rfl)
            (by dsimp only [miOff_try_ldrb, miOff_try_after_ldrb]; rw [applyWriteback, writeReg_W32_zext8, hIdxEq, BitVec.add_assoc]; rfl) ?_
          dsimp only [miOff_try_after_ldrb]
          wp_steps 2
          have hRest :
              ((maddrs.debruijnFree ↦ᵣ debBs) ∗
               ((metaPtr ↦ₛ ByteSlice.write32 metaBs 24 (av - ((-av) &&& av))) ∗
                (maddrs.ctx ↦ₛ ctxBs) ∗ F)) =
              ((metaPtr ↦ₛ ByteSlice.write32 metaBs 24 (av - ((-av) &&& av))) ∗
               (maddrs.ctx ↦ₛ ctxBs) ∗ (maddrs.debruijnFree ↦ᵣ debBs) ∗ F) := by
            generalize (metaPtr ↦ₛ ByteSlice.write32 metaBs 24 (av - ((-av) &&& av))) = pM,
              (maddrs.ctx ↦ₛ ctxBs) = pCtx,
              (maddrs.debruijnFree ↦ᵣ debBs) = pDeb
            ac_rfl
          rw [hRest]
          exact hFast hAvNe _ (by simpa [hmem1] using hcl_mw)
            (by dsimp only [miOff_call_unlock]; rfl) (by simp [hrun1])
            (by simp [hsp1]) hbrk1 (by simpa [hmem1] using hPerm1)
            (by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc1)
            (untouchedCS_step hcs1 (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
              (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [calleeSavedVRegs, arm64_norm]))
            (by simp only [arm64_norm])
            (by simpa [arm64_norm] using hx19_1)
            (by simpa [arm64_norm] using hx20_1)
            (by simp only [arm64_norm])
            (by simpa [arm64_norm] using hx22_1)
            (by simp only [arm64_norm])

set_option maxHeartbeats 400000 in
theorem mallocImpl_tryAvail_or_slow [MallocngMultiPlacement]
    (hSlot : AllocSlotPlacedFullStmt) (hMetaInv : MallocngMetaCountInv)
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget}
    {ivs0 : List (BitVec 64 × Nat)} {req sc : Nat}
    {st0 : MallocngSt} {s0 s : State}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hCount0 : MallocngCountIvsWF bud ivs0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0)
    (hReqMax : req ≤ MallocngMaxAllocSize)
    (hSc48 : sc < 48) (hAct : sc < st0.ctx.active.length)
    (hFitSc : req ≤ nominalSlotCap sc)
    (hSc2 : 2 ≤ sc ∧ sc < 48 → nominalSlotCap (sc - 2) < max req 16)
    (hSc24 : sc = 24 → nominalSlotCap 23 < req)
    (hSc24M : sc = 24 → nominalSlotCap 23 < max req MallocngMinBlockCost)
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
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ mallocImplSuccessPost24 γ tp brkStart bud ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜MallocngTightOomCond msvc req bud.peakCount s0 sf⌝) := by
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b at hpc ⊢
  have hb : BlkBase 9 b := hb_eq.symm
  by_cases hActZero : st0.ctx.active[sc]'hAct = 0#64
  · refine tryAvail_cbz_step hb hpc hrun hProc hcsHi (hx22.trans hActZero) ?_
    intro s' hpc' hrun' hsp' hbrk' hmem' hProc' hcs' hx19' hx20' hx24' hx25'
    rw [← hbrk', ← hb_eq, ← mallocngBlockProg_eq_b09]
    exact mallocImpl_allocSlot_slow hSlot hMetaInv (hmem' ▸ hcl) hCount0 (by rw [hbrk']; exact hwf0)
      hReqMax hSc48 hFitSc hSc2 hSc24 hSc24M htp0 hbrkS0 (by rw [hmem']; exact hPerm0)
      (by rwa [hb_eq]) hrun' (hsp'.trans hsp) hsp_align hProc' hcs'
      (hx19'.trans hx19) (hx20'.trans hx20) (hx24'.trans hx24) (hx25'.trans hx25)
  · have hActNe : st0.ctx.active[sc]'hAct ≠ 0#64 := hActZero
    obtain ⟨hActLen, hUseLen, hUnmLen, hBncLen, hPadLen, hActLLen⟩ := hwf0.ctx_lens
    have hActL : sc < st0.activeLists.length := by omega
    have hwf_s : MallocngWF maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0 := hwf0
    obtain ⟨g, hg, hMetaEq, hGsc, _⟩ := active_head_group_of_nonzero hwf_s hAct hActL hActNe
    have hMetaNe : g.metaPtr ≠ 0#64 := hMetaEq ▸ hActNe
    have hNoRes0 : st0.reservedMetas = [] := by
      have hInf := hwf0.inflight_wf
      cases hR : st0.reservedMetas with
      | nil => rfl
      | cons _ _ => rw [hR] at hInf; simp at hInf
    have hExt0 := meta_extract hwf_s hNoRes0 hg
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
      (MallocngLiveAuth γ st0.liveMap ∗
       (maddrs.lock ↦₃₂ 0#32) ∗
       (maddrs.replaced ↦₃₂ 0#32) ∗
       (maddrs.aaReplaced ↦₃₂ 0#32) ∗
       ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗
       MallocngAuxvState γ st0.auxvPtr st0.auxvSnap ∗
       ByteMap st0.masterDom (fun a => OwnedRwByte st0 a ∧ ¬ InRegion g.metaPtr 40 a) st0.byteVal ∗
       ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∗
       MappedSet st0.masterDom (OwnedMappedByte st0)) = coreTail0
    have hCoreSplit0 :
        MallocngCoreStInflightA 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 =
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗ coreTail0) := by
      rw [← hCoreTail]
      have hwf0' : MallocngWFInflight 0 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0 := hwf0
      dsimp only [MallocngCoreStInflightA]
      rw [propext ⟨fun _ => trivial, fun _ => hwf0'⟩, pure_true, emp_sepConj, hExt0]
      generalize (g.metaPtr ↦ₛ g.metaBytes) = pM,
        (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
        MallocngLiveAuth γ st0.liveMap = pGm,
        (maddrs.lock ↦₃₂ 0#32) = pLk,
        (maddrs.replaced ↦₃₂ 0#32) = pRp,
        (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
        ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) = pLb8,
        MallocngAuxvState γ st0.auxvPtr st0.auxvSnap = pAx,
        ByteMap st0.masterDom (fun a => OwnedRwByte st0 a ∧ ¬ InRegion g.metaPtr 40 a) st0.byteVal = pRw,
        ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
        MappedSet st0.masterDom (OwnedMappedByte st0) = pMs
      ac_rfl
    have hPreFocus :
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗
         MallocngCoreStInflightA 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
         MallocngRuntime maddrs tp) =
        ((g.metaPtr ↦ₛ g.metaBytes) ∗
         (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
         (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
         (roOther ∗ coreTail0 ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 624 ∗ MallocngRuntime maddrs tp)) := by
      rw [hCoreSplit0, hRoSplit]
      generalize (g.metaPtr ↦ₛ g.metaBytes) = pM,
        (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
        (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) = pDeb,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreFocus]
    refine tryAvail_nonnull_step hb hMetaNe hmLen hCtxLen0 hDebLen hPkAv hGetMmc0
      hcl hpc hrun hProc hcsHi (hx22.trans hMetaEq.symm) hx24 hx25 ?_ ?_
    · intro s' hpc' hrun' hsp' hbrk' hmem' hProc' hcs' hx19' hx20' hx24' hx25'
      rw [← hPreFocus, ← hbrk', ← hb_eq, ← mallocngBlockProg_eq_b09]
      exact mallocImpl_allocSlot_slow hSlot hMetaInv (hmem' ▸ hcl) hCount0 (by rw [hbrk']; exact hwf0)
        hReqMax hSc48 hFitSc hSc2 hSc24 hSc24M htp0 hbrkS0 (by rw [hmem']; exact hPerm0)
        (by rwa [hb_eq]) hrun' (hsp'.trans hsp) hsp_align hProc' hcs'
        (hx19'.trans hx19) (hx20'.trans hx20) hx24' hx25'
    · intro hAvNe s_u hcl_u hpc_u hrun_u hsp_u hbrk_u hperm_u hProc_u hcs_u
        hx0_u hx19_u hx20_u hx21_u hx22_u hx23_u
      clear hRoOther hDebLen
      obtain ⟨hIdxSlots, hIdx32, hg'Mm, hMetaLen1, hCnt1, hDynEq1, hwf1, hg'Mem,
        _, hRwAbsorb, hPnEq, hMpEq⟩ := claimFreeAvail_absorb hwf_s hg hAvNe
      have hIdxEq : (mallocngDebruijn32Table.getD (((((-g.availMask) &&& g.availMask) * 0x076be629#32) >>> 27).toNat) 0#8).toNat =
          ctz32DeBruijn g.availMask := rfl
      rw [hIdxEq] at hx21_u hx23_u
      generalize hIdxGen : ctz32DeBruijn g.availMask = idx at hWrAv hIdxSlots hIdx32 hg'Mm hMetaLen1 hCnt1 hDynEq1 hwf1 hg'Mem hRwAbsorb hPnEq hMpEq hx21_u hx23_u
      let newAvail := g.availMask - ((-g.availMask) &&& g.availMask)
      let g' := mkReplaceSlotGroup g idx newAvail .claimed
      let val' := writeBytesToMap st0.byteVal g.metaPtr g'.metaBytes
      let st1 := mkReplaceSlotSt st0 g idx newAvail .claimed val' st0.liveMap
      have hPostEq :
          ((g.metaPtr ↦ₛ ByteSlice.write32 g.metaBytes 24 (g.availMask - ((-g.availMask) &&& g.availMask))) ∗
           (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗ (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
           (roOther ∗ coreTail0 ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
            stackFrameAt (s0.sp - 80#64) 624 ∗ MallocngRuntime maddrs tp)) =
          (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
           MallocngRoTablesA maddrs ∗
           MallocngCoreStInflightA 1 γ maddrs brkStart s_u.brk bud.liveCost bud.peakCost st1 ∗
           MallocngRuntime maddrs tp) := by
        have hCore1Eq :
            MallocngCoreStInflightA 1 γ maddrs brkStart s_u.brk bud.liveCost bud.peakCost st1 =
            ((g.metaPtr ↦ₛ g'.metaBytes) ∗ (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗ coreTail0) := by
          rw [hbrk_u, ← hCoreTail]
          have hwf1' : MallocngWFInflight 1 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st1 := hwf1
          dsimp only [MallocngCoreStInflightA]
          rw [propext ⟨fun _ => trivial, fun _ => hwf1'⟩, pure_true, emp_sepConj]
          dsimp only [st1]
          rw [← hRwAbsorb, ← hPnEq, ← hMpEq]
          dsimp only [mkReplaceSlotSt]
          change (MallocngLiveAuth γ st0.liveMap ∗ (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
            (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
            ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗ MallocngAuxvState γ st0.auxvPtr st0.auxvSnap ∗
            ((g.metaPtr ↦ₛ g'.metaBytes) ∗
              ByteMap st0.masterDom (fun a => OwnedRwByte st0 a ∧ ¬ InRegion g.metaPtr 40 a) st0.byteVal) ∗
            ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∗
            MappedSet st0.masterDom (OwnedMappedByte st0)) = _
          generalize (g.metaPtr ↦ₛ g'.metaBytes) = pM,
            (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
            MallocngLiveAuth γ st0.liveMap = pGm,
            (maddrs.lock ↦₃₂ 0#32) = pLk,
            (maddrs.replaced ↦₃₂ 0#32) = pRp,
            (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
            ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) = pLb8,
            MallocngAuxvState γ st0.auxvPtr st0.auxvSnap = pAx,
            ByteMap st0.masterDom (fun a => OwnedRwByte st0 a ∧ ¬ InRegion g.metaPtr 40 a) st0.byteVal = pRw,
            ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
            MappedSet st0.masterDom (OwnedMappedByte st0) = pMs
          ac_rfl
        change ((g.metaPtr ↦ₛ ByteSlice.write32 g.metaBytes 24 newAvail) ∗ _) = _
        rw [hWrAv, hCore1Eq, hRoSplit]
        generalize (g.metaPtr ↦ₛ g'.metaBytes) = pM,
          (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
          (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) = pDeb,
          MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
          stackFrameAt (s0.sp - 80#64) 624 = pSf,
          MallocngRuntime maddrs tp = pRt
        ac_rfl
      rw [hPostEq]
      clear hPostEq hPreFocus hRoSplit hCoreTail hIdxEq hIdxGen
      have hwf1_u : MallocngWFInflight 1 maddrs.base brkStart s_u.brk bud.liveCost bud.peakCost st1 :=
        hbrk_u.symm ▸ hwf1
      have hPerm_u : s_u.mem.perm = s0.mem.perm := hperm_u.trans hPerm0
      have hMetaLe1 : st1.metaAreas.length ≤
          1 + (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101 := by
        have hMeta0 := hMetaInv bud ivs0 st0 hCount0
        have hPeakLe : bud.peakCount ≤ (mallocngAllocBudget true req bud).peakCount := by
          dsimp [mallocngAllocBudget]; omega
        have hDivLe : (88 + 8 * bud.peakCount) / 101 ≤
            (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101 :=
          Nat.div_le_div_right (by omega)
        rw [hMetaLen1]; omega
      have hNoOrph1 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s_u.mem :=
        mallocngNoOrphanMappings_of_perm_eq (hDynEq1.trans hCount0.2.2.1.symm) hPerm_u
      have hDelta_u : MallocngMappedDelta 16 (MallocngTightStepBound req bud.peakCount) s0.mem s_u.mem :=
        ⟨[], Nat.zero_le _, Nat.zero_le _, fun a ha => Or.inl (hPerm_u ▸ ha)⟩
      have hIdxSlots' : idx < g'.slots.length := by
        simpa [g', mkReplaceSlotGroup] using hIdxSlots
      have hClaimed' : g'.slots[idx]'hIdxSlots' = .claimed := by
        simp [g', mkReplaceSlotGroup]
      have hG'Sc : g'.sc = sc := by
        simpa [g', mkReplaceSlotGroup] using hGsc
      have hFitG' : req + 4 ≤ g'.stride := by
        have hStrGe : slotStride sc ≤ g.stride :=
          hGsc ▸ active_group_stride_ge hwf_s hg (hGsc ▸ hSc48) hAvNe
        have hStrEq : g'.stride = g.stride := rfl
        have hSzPos := (sizeClass_bounds (sc := sc) hSc48).1
        dsimp [nominalSlotCap, slotStride] at hFitSc hStrGe
        omega
      subst hb_eq
      rw [← mallocngBlockProg_eq_b09]
      have hGrp1 : Cost.GroupsGrpBound ((mallocngAllocBudget true req bud).peakCount + 6) st1.groups := by
        have hG0 := hCount0.2.2.2.2.2.mono (V := (mallocngAllocBudget true req bud).peakCount + 6)
          (by dsimp [mallocngAllocBudget]; omega)
        exact hG0.map_ite g.metaPtr fun hm hs => hG0 g hg hm hs
      exact mallocImpl_join_epilogue hcl_u hCount0 hCnt1 hMetaLe1 hGrp1 hNoOrph1 hwf1_u hNoRes0
        hg'Mem hIdxSlots' hClaimed' hReqMax hFitG'
        (fun h => by rw [hG'Sc] at h ⊢; exact hSc2 h)
        (fun h => hSc24 (hG'Sc ▸ h))
        (fun h => hSc24M (hG'Sc ▸ h))
        (fun h => by rw [hG'Sc] at h; omega)
        (fun h => by rw [hG'Sc] at h; omega)
        (fun hMm => by rw [hg'Mm] at hMm; cases hMm)
        htp0 hbrkS0 hDelta_u
        hpc_u hrun_u (hsp_u.trans hsp) hsp_align hProc_u hcs_u
        hx0_u hx19_u (hx20_u.trans hx20) hx21_u hx22_u hx23_u

set_option maxHeartbeats 400000 in
theorem mallocImpl_small_med_branch [MallocngMultiPlacement]
    (hSlot : AllocSlotPlacedFullStmt) (hMetaInv : MallocngMetaCountInv)
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget}
    {ivs0 : List (BitVec 64 × Nat)} {req : Nat}
    {st0 : MallocngSt} {s0 s : State}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hCount0 : MallocngCountIvsWF bud ivs0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0)
    (hReq : req ≤ 131051)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hPerm0 : s.mem.perm = s0.mem.perm)
    (hpc : s.pc = mbase 9 + miOff_small_entry) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ mallocImplSuccessPost24 γ tp brkStart bud ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜MallocngTightOomCond msvc req bud.peakCount s0 sf⌝) := by
  have hReqMax : req ≤ MallocngMaxAllocSize := by
    have := mallocngMaxAllocSize_eq; omega
  let sc0 := sizeToClassUnits ((req + 3) / 16)
  obtain ⟨hsc0_lt, _, _⟩ := sizeToClass_spec hReq
  let stcFrame :=
    MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
    MallocngCoreStInflightA 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0
  have hPreStc :
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp) =
      (MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗ stcFrame) := by
    dsimp only [stcFrame]
    generalize MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      stackFrameAt (s0.sp - 80#64) 624 = pSf,
      MallocngRoTablesA maddrs = pRo,
      MallocngCoreStInflightA 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 = pCr,
      MallocngRuntime maddrs tp = pRt
    ac_rfl
  rw [hPreStc]
  refine sepWP_seq_cl (mid := mbase 9 + miOff_after_lock) hcl ?_
  refine SepWP.mono
    (mallocImpl_sizeToClass_lock_step (F := stcFrame) hReq rfl hpc hrun hsp hProc hcsHi hx20) ?_
    (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
  rintro s1 P1 hpc1 hrun1 ⟨⟨hsp1, hbrk1, hperm1, hProc1, hcs1, hx19_1, hx20_1, hx21_1, hx24_1⟩, hP1⟩ hcl1
  apply SepWP.weaken_pre hP1
  have hwf1_0 : MallocngWF maddrs.base brkStart s1.brk bud.liveCost bud.peakCost st0 :=
    hbrk1 ▸ hwf0
  let coarseRest :=
    MallocngLiveAuth γ st0.liveMap ∗
    (maddrs.lock ↦₃₂ 0#32) ∗
    (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗
    ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗
    MallocngAuxvState γ st0.auxvPtr st0.auxvSnap ∗
    ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∗
    MappedSet st0.masterDom (OwnedMappedByte st0) ∗
    MallocngRoTablesA maddrs ∗
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
      MallocngLiveAuth γ st0.liveMap = pGm,
      (maddrs.lock ↦₃₂ 0#32) = pLk,
      (maddrs.replaced ↦₃₂ 0#32) = pRp,
      (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
      ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) = pLb8,
      MallocngAuxvState γ st0.auxvPtr st0.auxvSnap = pAx,
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
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA 0 γ maddrs brkStart brk' bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp) := by
    intro brk' hwf'
    have hwf'' : MallocngWFInflight 0 maddrs.base brkStart brk' bud.liveCost bud.peakCost st0 := hwf'
    dsimp only [MallocngCoreStInflightA, coarseRest]
    rw [propext ⟨fun _ => trivial, fun _ => hwf''⟩, pure_true, emp_sepConj]
    generalize (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
      ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal = pRw,
      MallocngLiveAuth γ st0.liveMap = pGm,
      (maddrs.lock ↦₃₂ 0#32) = pLk,
      (maddrs.replaced ↦₃₂ 0#32) = pRp,
      (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
      ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) = pLb8,
      MallocngAuxvState γ st0.auxvPtr st0.auxvSnap = pAx,
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
      obtain ⟨_, hFitSc, hSc2, hSc24, hSc24M⟩ := coarseBump_sc_props hReq hChoice
      have hwf_t : MallocngWF maddrs.base brkStart s_t.brk bud.liveCost bud.peakCost st0 :=
        hbrk_t ▸ hwf1_0
      have hcl_t : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_t.mem := hmem_t ▸ hcl1
      have hPerm_t : s_t.mem.perm = s0.mem.perm := by
        rw [hmem_t]; exact hperm1.trans hPerm0
      apply SepWP.weaken_pre (Entails.trans hPt (Entails.of_eq (hCoarseBack s_t.brk hwf_t)))
      exact mallocImpl_tryAvail_or_slow hSlot hMetaInv hcl_t hCount0 hwf_t hReqMax hScLt hAct
        hFitSc hSc2 hSc24 hSc24M htp0 hbrkS0 hPerm_t
        hpc_t hrun_t hsp_t hsp_align hProc_t hcs_t
        hx19_t hx20_t hx22_t hx24_t hx25_t)
    (fun sc s_p P_p hChoice hScLt hpc_p hrun_p hsp_p hbrk_p hmem_p hProc_p hcs_p
         hx19_p hx20_p hx24_p hx25_p hPp => by
      obtain ⟨_, hFitSc, hSc2, hSc24, hSc24M⟩ := coarseBump_sc_props hReq hChoice
      have hwf_p : MallocngWF maddrs.base brkStart s_p.brk bud.liveCost bud.peakCost st0 :=
        hbrk_p ▸ hwf1_0
      have hcl_p : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_p.mem := hmem_p ▸ hcl1
      have hPerm_p : s_p.mem.perm = s0.mem.perm := by
        rw [hmem_p]; exact hperm1.trans hPerm0
      apply SepWP.weaken_pre (Entails.trans hPp (Entails.of_eq (hCoarseBack s_p.brk hwf_p)))
      exact mallocImpl_allocSlot_slow hSlot hMetaInv hcl_p hCount0 hwf_p hReqMax hScLt
        hFitSc hSc2 hSc24 hSc24M htp0 hbrkS0 hPerm_p
        hpc_p hrun_p hsp_p hsp_align hProc_p hcs_p
        hx19_p hx20_p hx24_p hx25_p)

end VerifiedLibraries.Mallocng.Proofs
