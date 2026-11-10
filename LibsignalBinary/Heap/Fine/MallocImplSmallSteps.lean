/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplStage2b
public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# `__libc_malloc_impl` `try_avail` and Slow-Path Step Helpers

Frame-polymorphic `try_avail` and `alloc_slot` slow-path step lemmas inside `__libc_malloc_impl`
(`blk09`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

theorem at_bl_target_b09_fine [MallocngMultiPlacement] {b : BitVec 64}
    (_hb : BlkBase 9 b) (j : Nat) (off : BitVec 64) :
    mbase j = b + off + (mbase j - b - off) := by bv_arith

theorem stackFrame_eq_stackFrameAt_fine {s : State} {sp1 : BitVec 64} (k : Nat)
    (hk : k < 2 ^ 64) (hsp : s.sp = sp1) :
    stackFrame s k = stackFrameAt sp1 k := by
  unfold stackFrame
  rw [hsp, ← stackFrameAt_eq_memRegion sp1 k (hn := Nat.le_of_lt hk)]

theorem stackFrameAt_624_eq_fine (sp1 : BitVec 64) (k : Nat) (hk : k ≤ 624) :
    stackFrameAt sp1 624 = (stackFrameAt sp1 k ∗ stackFrameAt (sp1 - BitVec.ofNat 64 k) (624 - k)) := by
  have hEq : (624 : Nat) = k + (624 - k) := by omega
  conv => lhs; rw [hEq]
  exact stackFrameAt_split sp1 k (624 - k)

theorem untouchedCS_of_calleeSaved_fine {s0 s1 s2 : State}
    (h1 : MallocImplUntouchedCS s0 s1) (h2 : CalleeSavedPreserved s1 s2) :
    MallocImplUntouchedCS s0 s2 := by
  obtain ⟨_, _, _, _, _, _, _, h26, h27, h28, _, hv⟩ := h2
  exact ⟨h26.trans h1.1, h27.trans h1.2.1, h28.trans h1.2.2.1, hv.trans h1.2.2.2⟩

private theorem bit31_all_32_fine :
    (List.range 32).all (fun k => decide ((BitVec.ofNat 32 k).getLsbD 31 = false)) = true := by
  decide

theorem bit31_false_of_readReg32_ofNat_fine {v : BitVec 64} {idx : Nat}
    (h32 : BitVec.truncate 32 v = BitVec.ofNat 32 idx) (hIdx : idx ≤ 31) :
    v.getLsbD 31 = false ∧
    v[31] = false ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 v) = BitVec.ofNat 64 idx := by
  have h1 : (BitVec.truncate 32 v).getLsbD 31 = v.getLsbD 31 := by
    simp
  have h2 : (BitVec.ofNat 32 idx).getLsbD 31 = false :=
    of_decide_eq_true (List.all_eq_true.mp bit31_all_32_fine idx (List.mem_range.mpr (by omega)))
  have hg : v.getLsbD 31 = false := by rw [← h1, h32, h2]
  have hz : BitVec.zeroExtend 64 (BitVec.truncate 32 v) = BitVec.ofNat 64 idx := by
    rw [h32]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  exact ⟨hg, hg, hz⟩

theorem and_u32_eq_zeroExtend_truncate_fine (v : BitVec 64) :
    v &&& 4294967295#64 = BitVec.zeroExtend 64 (BitVec.truncate 32 v) := by
  bv_bits

private theorem sc_sxtw_shl3_all_fine :
    (List.range 48).all (fun k =>
      decide (
        (BitVec.signExtend 64 (BitVec.ofNat 32 k) <<< 3) = BitVec.ofNat 64 (8 * k) ∧
        (BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 k)) <<< 3) =
          BitVec.ofNat 64 (8 * k))) = true := by
  decide

theorem sc_sxtw_shl3_bv_fine {sc : Nat} (hsc : sc < 48) :
    (BitVec.signExtend 64 (BitVec.ofNat 32 sc) <<< 3) = BitVec.ofNat 64 (8 * sc) ∧
    (BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 sc)) <<< 3) =
      BitVec.ofNat 64 (8 * sc) :=
  of_decide_eq_true (List.all_eq_true.mp sc_sxtw_shl3_all_fine sc (List.mem_range.mpr hsc))

private theorem tryAvail_bv_props_fine {av : BitVec 32} (hAvNe : av ≠ 0#32) :
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

private theorem bv32_le_or_fine (a b : BitVec 32) : a.toNat ≤ (a ||| b).toNat := by
  change a ≤ a ||| b
  bv_bits

theorem active_group_stride_ge_fine {inflight : Nat} {base brkStart brk : BitVec 64}
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
    have hAvLt : g.availMask.toNat < 2 := Nat.lt_of_le_of_lt (bv32_le_or_fine _ _) hOrLt
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

theorem tryAvail_cbz_step_fine [MallocngMultiPlacement] {b target : BitVec 64}
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
theorem tryAvail_nonnull_step_fine [MallocngMultiPlacement] {b target : BitVec 64}
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
      obtain ⟨hHashLt, _, _, hAnd255⟩ := tryAvail_bv_props_fine hAvNe
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

end LibsignalBinary.Heap.Fine
