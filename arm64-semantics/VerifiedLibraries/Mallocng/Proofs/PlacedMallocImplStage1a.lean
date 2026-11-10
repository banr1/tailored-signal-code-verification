/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplHelpers4
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Placed `__libc_malloc_impl` Stage 1a (`enframe` Store Tail)

Defines symbolic instruction offsets `miOff_*` in `blk09` and proves `mallocImpl_enframe_finish`,
stepping the permission-preserving `enframe` tail (`+0x3c4 .. +0x454`) and re-bundling
`mallocImplSuccessBody24`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Symbolic Instruction Offsets in `blk09` -/

abbrev miOff_call_unlock  : BitVec 64 := reloc_call_off% mallocImplRelocs "__unlock" 0
abbrev miOff_after_unlock : BitVec 64 := words_insn_off% mallocImplWords 0x394082c0#32 0
abbrev miOff_tst_mask     : BitVec 64 := words_insn_off% mallocImplWords 0xf274cc9f#32 0
abbrev miOff_enframe_44   : BitVec 64 := words_insn_off% mallocImplWords 0xf9400ac2#32 0
abbrev miOff_enframe_90   : BitVec 64 := words_insn_off% mallocImplWords 0xeb21c0bf#32 0
abbrev miOff_enframe_c4   : BitVec 64 := words_insn_off% mallocImplWords 0x34000121#32 0
abbrev miOff_enframe_e8   : BitVec 64 := words_insn_off% mallocImplWords 0xcb020002#32 0
abbrev miOff_enframe_28   : BitVec 64 := words_insn_off% mallocImplWords 0x12001021#32 0

/-! ## `enframe` Step Lemmas -/

private theorem enframe_bv_aux (n idx totOff16 res : Nat) (hn : n ≤ 255) (hi : idx ≤ 31) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 n)) = 0#64 → n = 0) ∧
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 n)) <<< 4) = BitVec.ofNat 32 n <<< 4 ∧
    BitVec.truncate 16 (BitVec.truncate 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 16 n ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 idx)) &&& 255#64 = BitVec.ofNat 64 idx ∧
    BitVec.zeroExtend 8 (BitVec.ofNat 64 idx) = BitVec.ofNat 8 idx ∧
    BitVec.truncate 16 (BitVec.truncate 32 (BitVec.ofNat 64 totOff16)) = BitVec.ofNat 16 totOff16 ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 idx)) &&& 31#64 = BitVec.ofNat 64 idx ∧
    BitVec.zeroExtend 8 (BitVec.ofNat 64 (min res 5 <<< 5)) + BitVec.zeroExtend 8 (BitVec.ofNat 64 idx) =
      BitVec.truncate 8 (BitVec.ofNat 32 (min res 5 <<< 5) + BitVec.ofNat 32 idx) ∧
    BitVec.zeroExtend 64 (BitVec.ofNat 8 idx) = BitVec.ofNat 64 idx ∧
    BitVec.setWidth 64 (BitVec.ofNat 32 idx) = BitVec.ofNat 64 idx ∧
    (res ≤ 4 → BitVec.zeroExtend 64 (BitVec.truncate 32 ((BitVec.zeroExtend 64 (BitVec.ofNat 32 res) &&& 7#64) <<< 5)) =
      BitVec.ofNat 64 (min res 5 <<< 5)) ∧
    (∀ a b : BitVec 32, a - b = BitVec.ofNat 32 res → res < 1048576 → ((a = b) ↔ res = 0)) := by
  have hI : (List.range 32).all (fun k =>
    decide (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 k)) &&& 255#64 = BitVec.ofNat 64 k ∧
      BitVec.zeroExtend 8 (BitVec.ofNat 64 k) = BitVec.ofNat 8 k ∧
      BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 k)) &&& 31#64 = BitVec.ofNat 64 k ∧
      BitVec.zeroExtend 64 (BitVec.ofNat 8 k) = BitVec.ofNat 64 k ∧
      BitVec.setWidth 64 (BitVec.ofNat 32 k) = BitVec.ofNat 64 k)) = true := by decide
  have hR : (List.range 5).all (fun r =>
    decide (BitVec.zeroExtend 64 (BitVec.truncate 32 ((BitVec.zeroExtend 64 (BitVec.ofNat 32 r) &&& 7#64) <<< 5)) =
      BitVec.ofNat 64 (min r 5 <<< 5))) = true := by decide
  obtain ⟨h4, h5, h7, h9, h10⟩ := of_decide_eq_true (List.all_eq_true.mp hI idx (List.mem_range.mpr (by omega)))
  have hMin : min res 5 ≤ 5 := Nat.min_le_right _ _
  have hShl : BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 n)) <<< 4) =
      BitVec.ofNat 32 n <<< 4 := by apply BitVec.eq_of_toNat_eq; simp [Nat.shiftLeft_eq]
  refine ⟨by bv_omega, hShl, by bv_omega, h4, h5, by bv_omega, h7, by bv_omega, h9, h10,
    fun hLe => of_decide_eq_true (List.all_eq_true.mp hR res (List.mem_range.mpr (by omega))), ?_⟩
  intro a b hab hr; constructor <;> intro h
  · have : BitVec.ofNat 32 res = 0#32 := by rw [← hab, h, BitVec.sub_self]
    bv_omega
  · subst h; bv_omega

private theorem setPC_pres {s0 s : State} (pc : BitVec 64)
    (hP : MallocngProcPreserved s0 s) (hU : MallocImplUntouchedCS s0 s) :
    (s.setPC pc).pc = pc ∧ (s.setPC pc).status = s.status ∧ (s.setPC pc).sp = s.sp ∧
    (s.setPC pc).brk = s.brk ∧ (s.setPC pc).mem.perm = s.mem.perm ∧
    MallocngProcPreserved s0 (s.setPC pc) ∧ MallocImplUntouchedCS s0 (s.setPC pc) := by
  cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, hP, hU⟩

private theorem enframe_step1 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {s0 s : State} {F : SepProp} {oom : State → SepProp}
    {start storage metaPtr : BitVec 64} {stride req idx off : Nat}
    {slotBs metaBytes : List (BitVec 8)}
    (hFit0 : req + 4 ≤ stride) (hFit : 16 * off + req ≤ stride - 4) (hOff255 : off ≤ 255)
    (hSlotLen : slotBs.length = stride) (hMetaLen : metaBytes.length = 40)
    (hMemGet : pack64 (metaBytes.getD 16 0#8) (metaBytes.getD 17 0#8) (metaBytes.getD 18 0#8) (metaBytes.getD 19 0#8)
      (metaBytes.getD 20 0#8) (metaBytes.getD 21 0#8) (metaBytes.getD 22 0#8) (metaBytes.getD 23 0#8) + 16#64 = storage)
    (hOffSE : BitVec.signExtend 64 (BitVec.ofNat 32 off <<< 4) = BitVec.ofNat 64 (16 * off))
    (hpc : s.pc = b + miOff_enframe_c4)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = start) (hx1 : s.readReg64 (.gpr 1#5) = BitVec.ofNat 64 off)
    (hx2 : s.readReg64 (.gpr 2#5) = storage) (hx4 : s.readReg64 (.gpr 4#5) = 0#64)
    (hx6 : s.readReg64 (.gpr 6#5) = start + BitVec.ofNat 64 (stride - 4))
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx22 : s.readReg64 (.gpr 22#5) = metaPtr) (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_enframe_e8) s
      (((start - 4#64) ↦ₛ slotBs) ∗ (metaPtr ↦ₛ metaBytes) ∗ F)
      (fun s1 P1 =>
        (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
         MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
         s1.readReg64 (.gpr 0#5) = start + BitVec.ofNat 64 (16 * off) ∧
         s1.readReg64 (.gpr 2#5) = storage ∧ s1.readReg64 (.gpr 4#5) = 0#64 ∧
         s1.readReg64 (.gpr 6#5) = start + BitVec.ofNat 64 (stride - 4) ∧
         s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧ s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) ∧
        (P1 ⊢ ((start - 4#64) ↦ₛ enframeB1 slotBs off) ∗ (metaPtr ↦ₛ metaBytes) ∗ F))
      oom := by
  have _ := hb
  obtain ⟨hZeroEq, hShlEq, hTr16, _, _, _, _, _, _, _, _, _⟩ := enframe_bv_aux off 0 0 0 hOff255 (Nat.zero_le _)
  wp_steps
  wp_if hcond
  · have hOff0 : off = 0 := hZeroEq hcond
    have hPres := setPC_pres (b + miOff_enframe_e8) hProc hcsHi
    apply SepWP.done; · exact hPres.1
    · exact hPres.2.1.trans hrun
    · refine ⟨⟨hPres.2.2.1.trans hsp, hPres.2.2.2.1, hPres.2.2.2.2.1, hPres.2.2.2.2.2.1, hPres.2.2.2.2.2.2,
        ?_, (State.readReg64_setPC ..).trans hx2, (State.readReg64_setPC ..).trans hx4,
        (State.readReg64_setPC ..).trans hx6, (State.readReg64_setPC ..).trans hx20,
        (State.readReg64_setPC ..).trans hx23⟩, ?_⟩
      · rw [State.readReg64_setPC, hx0, hOff0]; exact (BitVec.add_zero start).symm
      · dsimp only [enframeB1]; rw [ite_eq_left hOff0]; exact Entails.refl _
  · have hOffNe : off ≠ 0 := fun h0 => hcond (by subst h0; rfl)
    wp_steps 2
    wp_str8_perm m1 hm1
    wp_str16_perm m2 hm2
    wp_step
    wp_str8_perm m3 hm3
    wp_steps 2
    apply SepWP.done; · rfl
    · exact hrun
    · refine ⟨⟨by simpa using hsp, rfl, by simpa using hm3.trans (hm2.trans hm1), hProc,
        untouchedCS_step hcsHi (by simp) (by simp) (by simp) rfl,
        by simp, ?_, by simpa using hx4, by simpa using hx6, by simpa using hx20, by simpa using hx23⟩, ?_⟩
      · simp [← ByteSlice.pack64_eq_readLE_8]
        simpa only [List.getD_eq_getElem?_getD] using hMemGet
      · dsimp only [enframeB1]; rw [ite_eq_right hOffNe]; exact Entails.refl _

private theorem enframe_step2 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {s0 s1 : State} {F : SepProp} {oom : State → SepProp}
    {start storage : BitVec 64} {stride req idx off totOff16 res : Nat}
    {bs1 : List (BitVec 8)}
    (hFit0 : req + 4 ≤ stride) (hFit : 16 * off + req ≤ stride - 4) (hIdx31 : idx ≤ 31)
    (hResEq : res = stride - 4 - (16 * off + req)) (hResLt : res < 1048576)
    (hLen1 : bs1.length = stride)
    (hLen2 : (enframeB2 bs1 off idx totOff16).length = stride)
    (hLen3 : (enframeB3 (enframeB2 bs1 off idx totOff16) off req stride res).length = stride)
    (hBs3Idx : (enframeB3 (enframeB2 bs1 off idx totOff16) off req stride res).getD (16 * off + 1) 0#8 = BitVec.ofNat 8 idx)
    (hPS4 : (start + BitVec.ofNat 64 (16 * off) - storage) >>> 4 = BitVec.ofNat 64 totOff16)
    (hSub32 : BitVec.truncate 32 ((start + BitVec.ofNat 64 (stride - 4)) - (start + BitVec.ofNat 64 (16 * off))) -
      BitVec.truncate 32 (BitVec.ofNat 64 req) = BitVec.ofNat 32 res)
    (hNegAddr : res ≠ 0 → (start + BitVec.ofNat 64 (stride - 4)) + BitVec.signExtend 64 (0#32 - BitVec.ofNat 32 res) =
      start - 4#64 + BitVec.ofNat 64 (4 + 16 * off + req))
    (hSle4 : res ≠ 0 → (BitVec.ofNat 32 res).sle 4#32 = decide (res ≤ 4))
    (hpc1 : s1.pc = b + miOff_enframe_e8) (hrun1 : s1.status = .Running)
    (hProc1 : MallocngProcPreserved s0 s1) (hcs1 : MallocImplUntouchedCS s0 s1)
    (hx0_1 : s1.readReg64 (.gpr 0#5) = start + BitVec.ofNat 64 (16 * off))
    (hx2_1 : s1.readReg64 (.gpr 2#5) = storage) (hx4_1 : s1.readReg64 (.gpr 4#5) = 0#64)
    (hx6_1 : s1.readReg64 (.gpr 6#5) = start + BitVec.ofNat 64 (stride - 4))
    (hx20_1 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx23_1 : s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_enframe_28) s1
      (((start - 4#64) ↦ₛ bs1) ∗ F)
      (fun s2 P2 =>
        (s2.sp = s1.sp ∧ s2.brk = s1.brk ∧ s2.mem.perm = s1.mem.perm ∧
         MallocngProcPreserved s0 s2 ∧ MallocImplUntouchedCS s0 s2 ∧
         s2.readReg64 (.gpr 0#5) = start + BitVec.ofNat 64 (16 * off) ∧
         s2.readReg64 (.gpr 1#5) = BitVec.ofNat 64 idx ∧
         s2.readReg64 (.gpr 4#5) = BitVec.ofNat 64 (min res 5 <<< 5)) ∧
        (P2 ⊢ ((start - 4#64) ↦ₛ enframeB3 (enframeB2 bs1 off idx totOff16) off req stride res) ∗ F))
      oom := by
  have _ := hb
  subst hResEq
  obtain ⟨_, _, _, hIdx255, hIdxZ8, hTot16, _, _, hIdxZ64, hIdxSW, hLe4R, hEqRes0⟩ :=
    enframe_bv_aux 0 idx totOff16 (stride - 4 - (16 * off + req)) (Nat.zero_le _) hIdx31
  wp_steps 2
  wp_str8_perm m1 hm1
  wp_steps 2
  wp_str16_perm m2 hm2
  wp_step
  wp_conv_pre => change ((start - 4#64) ↦ₛ enframeB2 bs1 off idx totOff16) ∗ F
  wp_step
  wp_if hBeq
  · have hRes0 : stride - 4 - (16 * off + req) = 0 := (hEqRes0 _ _ hSub32 hResLt).mp hBeq
    apply SepWP.done; · rfl
    · exact hrun1
    · refine ⟨⟨rfl, rfl, by simpa using hm2.trans hm1, hProc1,
        untouchedCS_step hcs1 (by simp) (by simp) (by simp) rfl,
        by simpa using hx0_1, by simp [hIdxSW], ?_⟩, ?_⟩
      · rw [hRes0]; simpa using hx4_1
      · dsimp only [enframeB3]; rw [ite_eq_left hRes0]; exact Entails.refl _
  · have hResNe : stride - 4 - (16 * off + req) ≠ 0 := fun h0 => hBeq ((hEqRes0 _ _ hSub32 hResLt).mpr h0)
    have hAddrN := hNegAddr hResNe
    have hSle := hSle4 hResNe
    wp_steps 2
    wp_str8_perm m3 hm3
    wp_step
    wp_if hLeCond
    · have hLe4 : stride - 4 - (16 * off + req) ≤ 4 := of_decide_eq_true hLeCond
      have hShl4 := hLe4R hLe4
      wp_steps
      have hMinSW : BitVec.setWidth 64 (BitVec.ofNat 32 (min (stride - 4 - (16 * off + req)) 5 <<< 5)) =
          BitVec.ofNat 64 (min (stride - 4 - (16 * off + req)) 5 <<< 5) := by
        have : min (stride - 4 - (16 * off + req)) 5 ≤ 5 := Nat.min_le_right _ _
        bv_omega
      have hB3Eq : enframeB3 (enframeB2 bs1 off idx totOff16) off req stride (stride - 4 - (16 * off + req)) =
          ByteSlice.write8 (enframeB2 bs1 off idx totOff16) (4 + 16 * off + req) 0#8 := by
        dsimp only [enframeB3]; rw [ite_eq_right hResNe, ite_eq_left hLe4]
      apply SepWP.done; · rfl
      · exact hrun1
      · refine ⟨⟨rfl, rfl, by simpa using hm3.trans (hm2.trans hm1), hProc1,
          untouchedCS_step hcs1 (by simp) (by simp) (by simp) rfl,
          by simpa using hx0_1, ?_, by simp [hMinSW]⟩, by rw [hB3Eq]; exact Entails.refl _⟩
        simp only [State.readReg64_setMem, State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64, ← hB3Eq, hBs3Idx]
        exact hIdxZ64
    · have hGe5 : 5 ≤ stride - 4 - (16 * off + req) := by
        have := of_decide_eq_false (Bool.eq_false_of_ne_true hLeCond); omega
      wp_str8_perm m4 hm4
      wp_step
      wp_str32_perm m5 hm5
      wp_step
      have hS5 : stride - 4 - 1 = stride - 5 := by omega
      have hB3Eq : enframeB3 (enframeB2 bs1 off idx totOff16) off req stride (stride - 4 - (16 * off + req)) =
          ByteSlice.write32 (ByteSlice.write8 (ByteSlice.write8 (enframeB2 bs1 off idx totOff16)
            (4 + 16 * off + req) 0#8) (stride - 5) 0#8) (stride - 4)
            (BitVec.ofNat 32 (stride - 4 - (16 * off + req))) := by
        dsimp only [enframeB3]; rw [ite_eq_right hResNe, ite_eq_right (by omega)]
      apply SepWP.done; · rfl
      · exact hrun1
      · refine ⟨⟨rfl, rfl, by simpa using hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1))), hProc1,
          untouchedCS_step hcs1 (by simp) (by simp) (by simp) rfl,
          by simpa using hx0_1, ?_, ?_⟩, by rw [hS5, hB3Eq]; exact Entails.refl _⟩
        · simp only [State.readReg64_setMem, State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64, hS5, ← hB3Eq, hBs3Idx]
          exact hIdxZ64
        · rw [show min (stride - 4 - (16 * off + req)) 5 = 5 by omega]; simp

private theorem enframe_step3 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {s0 s2 : State} {F : SepProp} {oom : State → SepProp}
    {start : BitVec 64} {stride idx off res : Nat}
    {bs3 : List (BitVec 8)}
    (hFit : 16 * off + 4 ≤ stride) (hIdx31 : idx ≤ 31) (hLen3 : bs3.length = stride)
    (hR5Or : BitVec.truncate 8 (BitVec.ofNat 32 (min res 5 <<< 5) + BitVec.ofNat 32 idx) =
      BitVec.ofNat 8 ((min res 5 <<< 5) ||| idx))
    (hpc2 : s2.pc = b + miOff_enframe_28) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc2 : MallocngProcPreserved s0 s2) (hcs2 : MallocImplUntouchedCS s0 s2)
    (hx0_2 : s2.readReg64 (.gpr 0#5) = start + BitVec.ofNat 64 (16 * off))
    (hx1_2 : s2.readReg64 (.gpr 1#5) = BitVec.ofNat 64 idx)
    (hx4_2 : s2.readReg64 (.gpr 4#5) = BitVec.ofNat 64 (min res 5 <<< 5)) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (s0.readReg64 (.gpr 30#5)) s2
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ ((start - 4#64) ↦ₛ bs3) ∗ F)
      (fun sf P_f =>
        sf.sp = s0.sp ∧ sf.brk = s2.brk ∧ sf.mem.perm = s2.mem.perm ∧
        MallocngProcPreserved s0 sf ∧ CalleeSavedPreserved s0 sf ∧
        sf.readReg64 (.gpr 0#5) = start + BitVec.ofNat 64 (16 * off) ∧
        (P_f ⊢ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
          ((start - 4#64) ↦ₛ ByteSlice.write8 bs3 (16 * off + 1) (BitVec.ofNat 8 ((min res 5 <<< 5) ||| idx))) ∗ F))
      oom := by
  have _ := hb
  obtain ⟨_, _, _, _, _, _, hIdx31M, hAdd8, _, _, _, _⟩ := enframe_bv_aux 0 idx 0 res (Nat.zero_le _) hIdx31
  wp_conv_pre => unfold MallocImplSavedRegs; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro vPad
  wp_steps 2
  wp_str8_perm m1 hm1
  wp_steps 6
  apply SepWP.done; · rfl
  · exact hrun2
  refine ⟨rfl, rfl, by simpa using hm1, hProc2, ?_, by simpa using hx0_2, ?_⟩
  · rcases hcs2 with ⟨h26, h27, h28, hv⟩
    refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simpa using h26, by simpa using h27, by simpa using h28, by simp, ?_⟩
    simpa [calleeSavedVRegs] using hv
  · refine sepConj_mono ?_ (Entails.refl _)
    unfold MallocImplSavedRegs
    exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
        (Entails.sepExists_intro vPad)))))))))

/-! ## Composed `mallocImpl_enframe_finish` -/

set_option maxHeartbeats 400000 in
theorem mallocImpl_enframe_finish [MallocngMultiPlacement]
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget} {ivs0 : List (BitVec 64 × Nat)}
    {req idx off : Nat} {st0 st1 : MallocngSt} {g : GroupDesc} {s0 s : State}
    {oom : State → SepProp}
    (hCount0 : MallocngCountIvsWF bud ivs0 st0)
    (hCnt1 : totalLiveCount st1 = totalLiveCount st0)
    (hMetaLe1 : st1.metaAreas.length ≤ 1 + (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101)
    (hGrp1 : Cost.GroupsGrpBound ((mallocngAllocBudget true req bud).peakCount + 6) st1.groups)
    (hNoOrph1 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s.mem)
    (hwf1 : MallocngWFInflight 1 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st1)
    (hNoRes : st1.reservedMetas = [])
    (hg : g ∈ st1.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hReqMax : req ≤ MallocngMaxAllocSize)
    (hFit0 : req + 4 ≤ g.stride) (hOff255 : off ≤ 255) (hFit : 16 * off + req ≤ g.stride - 4)
    (hSc2 : 2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < max req 16)
    (hSc24 : g.sc = 24 → nominalSlotCap 23 < req)
    (hSc24M : g.sc = 24 → nominalSlotCap 23 < max req MallocngMinBlockCost)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ max req MallocngMinBlockCost + 8195)
    (hSc63_4115 : g.sc = 63 → g.maplen * 4096 ≤ req + 4115)
    (hZeroMm : g.isMmapped = true → ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st1.byteVal a = 0#8)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hpc : s.pc = mbase 9 + miOff_enframe_c4) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = g.slotStart idx)
    (hx1 : s.readReg64 (.gpr 1#5) = BitVec.ofNat 64 off)
    (hx2 : s.readReg64 (.gpr 2#5) = g.storage)
    (hx4 : s.readReg64 (.gpr 4#5) = 0#64)
    (hx6 : s.readReg64 (.gpr 6#5) = g.slotEnd idx)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx22 : s.readReg64 (.gpr 22#5) = g.metaPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA 1 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st1 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        sf.sp = s0.sp ∧ sf.brk = s.brk ∧ sf.mem.perm = s.mem.perm ∧
        MallocngProcPreserved s0 sf ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ mallocImplSuccessBody24 γ tp brkStart bud ivs0 req s0 sf))
      oom := by
  rw [mallocngBlockProg_eq_b09]
  have hb : BlkBase 9 (mbase 9) := rfl
  generalize mbase 9 = b at hpc hb ⊢
  have hgw := hwf1.groups_wf g hg
  have hTot48 : g.mem.toNat + g.totalBytes ≤ 2 ^ 48 := hgw.2.2.2.2.2.2.1
  obtain ⟨hStrPos, _⟩ := group_stride_pos_and_align hgw
  obtain ⟨hIdxCnt, _, hStartNat, _, hEndNat, hEndLe, h48G, _, _⟩ := group_slot_bounds hgw hIdx
  have hIdx31 : idx ≤ 31 := by have := hgw.2.1; dsimp [GroupDesc.cnt] at hIdxCnt; omega
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  let start := g.slotStart idx
  let p := start + BitVec.ofNat 64 (16 * off)
  let slotBs := readBytesFromMap st1.byteVal (start - 4#64) g.stride
  let totOff16 := (p.toNat - g.storage.toNat) / 16
  let res := (g.slotEnd idx).toNat - (p.toNat + req)
  have hStartEq : start.toNat = g.mem.toNat + 16 + idx * g.stride := hStartNat
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hFit4 : 16 * off + 4 ≤ g.stride :=
    Nat.le_trans (Nat.add_le_add_right (Nat.le_trans (Nat.le_add_right _ req) hFit) 4)
      (Nat.le_of_eq (Nat.sub_add_cancel (Nat.le_trans (Nat.le_add_left 4 req) hFit0)))
  have hPNat : p.toNat = start.toNat + 16 * off := bv64_add_toNat (by omega)
  have hResEq : res = g.stride - 4 - (16 * off + req) := by dsimp only [res]; omega
  obtain ⟨hBs1L, hBs2L, hBs3L, hNewL, hBs3Idx, hB0, hBP4, hBP3, hBP2, hBR1, hBR5, hZeroU⟩ :=
    enframe_slotBytes_props hgw hIdx hClaimed hOff255 hFit hZeroMm
  obtain ⟨hBlkWf, hFresh, hPOffLe, hSc24_26, hwf2, hg'Mem, hCntEq, hDynEq, hExtSlot, hAbsSlot, hPnEq, hMpEq⟩ :=
    enframeClaimed_absorb (b := bud) hwf1 hg hIdx hClaimed hReqMax hOff255 hFit hSc2 hSc24 hSc63
      hNewL hB0 hBP4 hBP3 hBP2 hBR1 hBR5
  obtain ⟨hSlackLt, _, _, _, _, _, hOffProps⟩ := enframe_bv_props hgw hIdx hFit0 hSc63
  have hResLt : res < 1048576 :=
    Nat.lt_of_le_of_lt (by rw [hResEq]; exact Nat.sub_le_sub_left (Nat.le_add_left _ _) _) hSlackLt
  obtain ⟨hOffSE, _, hPS4, _, _, _, hSub32, _, hNegAddr, hSle4, _, _, hR5Or⟩ := hOffProps off hOff255 hFit
  have hExtMeta := meta_and_slot_extract hwf1 hNoRes hg hIdx hClaimed
  let liveMap' : MallocngLiveMap := st1.liveMap.insert p req 0
  let newSlotBs := ByteSlice.write8 (enframeB3 (enframeB2 (enframeB1 slotBs off) off idx totOff16) off req g.stride res)
    (16 * off + 1) (BitVec.ofNat 8 ((min res 5 <<< 5) ||| idx))
  let val' := writeBytesToMap st1.byteVal (start - 4#64) newSlotBs
  let rwTail := ByteMap st1.masterDom
    (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a) ∧ ¬ InRegion g.metaPtr 40 a) st1.byteVal
  let coreStatic := (maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗ ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗ MallocngAuxvState γ st1.auxvPtr st1.auxvSnap ∗
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗ MappedSet st1.masterDom (OwnedMappedByte st1)
  let envTail := stackFrameAt (s0.sp - 80#64) 624 ∗ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗
    MallocngBlockTokenK γ p req 0 ∗ MallocngLiveAuth γ liveMap' ∗ coreStatic ∗ rwTail
  dsimp only [MallocngCoreStInflightA]
  rw [hExtSlot, hExtMeta]
  wp_conv_pre => simp only [hwf1, pure_true, emp_sepConj]
  refine sepWP_bupd_focus (mallocngBlockK_alloc_bupd γ st1.liveMap p req 0 hBlkWf hFresh) (h := ?_)
  have hPre1 : ((MallocngLiveAuth γ liveMap' ∗ MallocngBlockTokenK γ p req 0) ∗
      MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗ MallocngRoTablesA maddrs ∗
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗
      (maddrs.aaReplaced ↦₃₂ 0#32) ∗ ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗ MallocngAuxvState γ st1.auxvPtr st1.auxvSnap ∗
      ((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗ rwTail ∗
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
      MappedSet st1.masterDom (OwnedMappedByte st1) ∗ MallocngRuntime maddrs tp) =
      (((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ envTail)) := by
    dsimp only [envTail, coreStatic]
    generalize MallocngBlockTokenK γ p req 0 = tok, (MallocngLiveAuth γ liveMap') = gm,
      ((start - 4#64) ↦ₛ slotBs) = sA, (g.metaPtr ↦ₛ g.metaBytes) = mA, rwTail = rT,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, stackFrameAt (s0.sp - 80#64) 624 = sfA,
      MallocngRoTablesA maddrs = roA, MallocngRuntime maddrs tp = rtA,
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) = cA, (maddrs.lock ↦₃₂ 0#32) = lkA,
      (maddrs.replaced ↦₃₂ 0#32) = rpA, (maddrs.aaReplaced ↦₃₂ 0#32) = aaA,
      ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = lbA, MallocngAuxvState γ st1.auxvPtr st1.auxvSnap = axA,
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pnA,
      MappedSet st1.masterDom (OwnedMappedByte st1) = mpA
    ac_rfl
  rw [hPre1]
  refine SepWP.seq_entails_emp
    (enframe_step1 hb hFit0 hFit hOff255 (readBytesFromMap_length ..) (by simp [GroupDesc.metaBytes])
      (by rw [(metaBytes_ops g 0 0#32 .claimed).1]; rfl) hOffSE hpc hrun hsp hProc hcsHi
      hx0 hx1 hx2 hx4 hx6 hx20 hx22 hx23) ?_
  rintro s1 hpc1 hrun1 ⟨hsp1, hbrk1, hperm1, hProc1, hcs1, hx0_1, hx2_1, hx4_1, hx6_1, hx20_1, hx23_1⟩
  have hPre2 : (((start - 4#64) ↦ₛ enframeB1 slotBs off) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ envTail)) =
      (((start - 4#64) ↦ₛ enframeB1 slotBs off) ∗
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) := by
    generalize ((start - 4#64) ↦ₛ enframeB1 slotBs off) = sA, (g.metaPtr ↦ₛ g.metaBytes) = mA,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, envTail = eT
    ac_rfl
  rw [hPre2]
  refine SepWP.seq_entails_emp
    (enframe_step2 hb hFit0 hFit hIdx31 hResEq hResLt hBs1L hBs2L hBs3L hBs3Idx
      hPS4 hSub32 hNegAddr hSle4 hpc1 hrun1 hProc1 hcs1 hx0_1 hx2_1 hx4_1 hx6_1 hx20_1 hx23_1) ?_
  rintro s2 hpc2 hrun2 ⟨hsp2, hbrk2, hperm2, hProc2, hcs2, hx0_2, hx1_2, hx4_2⟩
  have hPre3 : (((start - 4#64) ↦ₛ enframeB3 (enframeB2 (enframeB1 slotBs off) off idx totOff16) off req g.stride res) ∗
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) =
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
        ((start - 4#64) ↦ₛ enframeB3 (enframeB2 (enframeB1 slotBs off) off idx totOff16) off req g.stride res) ∗
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) := by
    generalize ((start - 4#64) ↦ₛ enframeB3 (enframeB2 (enframeB1 slotBs off) off idx totOff16) off req g.stride res) = sA,
      (g.metaPtr ↦ₛ g.metaBytes) = mA, MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, envTail = eT
    ac_rfl
  rw [hPre3]
  refine SepWP.mono
    (enframe_step3 hb hFit4 hIdx31 hBs3L hR5Or hpc2 hrun2 (hsp2.trans hsp1) hsp_align
      hProc2 hcs2 hx0_2 hx1_2 hx4_2) ?_
  rintro sf P_f _ _ ⟨hsf_sp, hsf_brk, hsf_perm, hsf_proc, hsf_cs, hsf_x0, hPf⟩
  have hBrkEq : sf.brk = s.brk := hsf_brk.trans (hbrk2.trans hbrk1)
  have hPermEq : sf.mem.perm = s.mem.perm := hsf_perm.trans (hperm2.trans hperm1)
  refine ⟨hsf_sp, hBrkEq, hPermEq, hsf_proc, hsf_cs, Entails.trans hPf ?_⟩
  let effCost := max req MallocngMinBlockCost
  let st2 := mkReplaceSlotSt st1 g idx g.availMask (.liveUser p req effCost) val' liveMap'
  let g' := mkReplaceSlotGroup g idx g.availMask (.liveUser p req effCost)
  let bf := mallocngAllocBudget true req bud
  have hReasm : (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ ((start - 4#64) ↦ₛ newSlotBs) ∗
      ((g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) =
      ((MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624) ∗
       (MallocngRoTablesA maddrs ∗
        (MallocngLiveAuth γ st2.liveMap ∗ (maddrs.ctx ↦ₛ st2.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗
         (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗ ((maddrs.libc + 8#64) ↦₆₄ st2.auxvPtr) ∗
         MallocngAuxvState γ st2.auxvPtr st2.auxvSnap ∗ ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal ∗
         ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal ∗
         MappedSet st2.masterDom (OwnedMappedByte st2)) ∗
        MallocngRuntime maddrs tp ∗ (p ↦ₛ readBytesFromMap val' p req) ∗ MallocngBlockTokenK γ p req 0)) := by
    have hM1 : ((start - 4#64) ↦ₛ newSlotBs) ∗ ((g.metaPtr ↦ₛ g.metaBytes) ∗ rwTail) =
        (p ↦ₛ readBytesFromMap val' p req) ∗ ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal := by
      dsimp only [rwTail]; rw [← hExtMeta]; exact hAbsSlot
    have hLAdj : (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ ((start - 4#64) ↦ₛ newSlotBs) ∗
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) =
        (((start - 4#64) ↦ₛ newSlotBs) ∗ ((g.metaPtr ↦ₛ g.metaBytes) ∗ rwTail)) ∗
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗
         MallocngBlockTokenK γ p req 0 ∗ MallocngLiveAuth γ liveMap' ∗ coreStatic) := by
      dsimp only [envTail]
      generalize MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, ((start - 4#64) ↦ₛ newSlotBs) = nA,
        (g.metaPtr ↦ₛ g.metaBytes) = mA, stackFrameAt (s0.sp - 80#64) 624 = sfA,
        MallocngRoTablesA maddrs = roA, MallocngRuntime maddrs tp = rtA,
        MallocngBlockTokenK γ p req 0 = tok, MallocngLiveAuth γ liveMap' = gm, coreStatic = cS, rwTail = rT
      ac_rfl
    have hSt2F : st2.liveMap = liveMap' ∧ st2.ctx = st1.ctx ∧ st2.auxvPtr = st1.auxvPtr ∧ st2.auxvSnap = st1.auxvSnap := ⟨rfl, rfl, rfl, rfl⟩
    rw [hLAdj, hM1]; dsimp only [coreStatic]
    rw [hPnEq, hMpEq, hSt2F.1, hSt2F.2.1, hSt2F.2.2.1, hSt2F.2.2.2]
    generalize (p ↦ₛ readBytesFromMap val' p req) = uA,
      ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal = rw2A,
      (MallocngLiveAuth γ liveMap') = gm, MallocngBlockTokenK γ p req 0 = tok,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, stackFrameAt (s0.sp - 80#64) 624 = sfA,
      MallocngRoTablesA maddrs = roA, MallocngRuntime maddrs tp = rtA,
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) = cA, (maddrs.lock ↦₃₂ 0#32) = lkA,
      (maddrs.replaced ↦₃₂ 0#32) = rpA, (maddrs.aaReplaced ↦₃₂ 0#32) = aaA,
      ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = lbA, MallocngAuxvState γ st1.auxvPtr st1.auxvSnap = axA,
      ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal = pnA,
      MappedSet st2.masterDom (OwnedMappedByte st2) = mpA
    ac_rfl
  change _ ⊢ mallocImplSuccessBody24 γ tp brkStart bud ivs0 req s0 sf
  rw [hReasm]; unfold mallocImplSuccessBody24
  refine sepConj_mono (savedRegs_entails_stackFrame s0) ?_
  refine Entails.trans ?_ (Entails.sepExists_intro p)
  refine Entails.trans ?_ (Entails.sepExists_intro (readBytesFromMap val' p req))
  refine Entails.trans ?_ (Entails.sepExists_intro st2)
  have hNoOrph2 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st2) s0.mem sf.mem :=
    mallocngNoOrphanMappings_congr_perm rfl hDynEq rfl hPermEq hNoOrph1
  have hCountIvs2 : MallocngCountIvsWF bf (dynamicRootRegions st2) st2 :=
    mallocngCountIvsWF_after_alloc hCount0 (hCntEq.trans (congrArg (· + 1) hCnt1)) hMetaLe1 hwf2
      (by exact hGrp1.map_ite g.metaPtr fun hm hs => hGrp1 g hg hm hs)
  have hPure : sf.readReg64 .x0 = p ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
      MallocngBlockWf p req ∧ (readBytesFromMap val' p req).length = req ∧
      MallocngNoOrphanMappings ivs0 (dynamicRootRegions st2) s0.mem sf.mem ∧
      MallocngCountIvsWF bf (dynamicRootRegions st2) st2 ∧
      ∃ g' ∈ st2.groups, ∃ idx' : Nat, ∃ hIdx' : idx' < g'.slots.length,
        g'.slots[idx']'hIdx' = .liveUser p req effCost ∧
        p.toNat - (g'.slotStart idx').toNat ≤ 255 * 16 ∧
        (g'.isMmapped = true → readBytesFromMap val' p req = List.replicate req 0#8) ∧
        (24 ≤ g'.sc ∧ g'.sc ≤ 26 → nominalSlotCap 23 < req) ∧
        (g'.sc = 24 → nominalSlotCap 23 < effCost) ∧
        (g'.sc = 63 → g'.maplen * 4096 ≤ req + 4115) :=
    ⟨hsf_x0, hsf_proc.2.2.1.trans htp0, hsf_proc.2.2.2.1.trans hbrkS0, hBlkWf,
      readBytesFromMap_length .., hNoOrph2, hCountIvs2, g', hg'Mem, idx,
      by simpa [g', mkReplaceSlotGroup] using hIdx,
      by simp [g', mkReplaceSlotGroup], hPOffLe, hZeroU, hSc24_26, hSc24M,
      by simpa [g', mkReplaceSlotGroup] using hSc63_4115⟩
  have hCoreEq : MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st2 =
      (MallocngLiveAuth γ st2.liveMap ∗ (maddrs.ctx ↦ₛ st2.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗
       (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗ ((maddrs.libc + 8#64) ↦₆₄ st2.auxvPtr) ∗
       MallocngAuxvState γ st2.auxvPtr st2.auxvSnap ∗ ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal ∗
       ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal ∗
       MappedSet st2.masterDom (OwnedMappedByte st2)) := by
    have hwf2' : MallocngWFInflight 0 maddrs.base brkStart s.brk bf.liveCost bf.peakCost st2 := hwf2
    rw [hBrkEq]; dsimp only [MallocngCoreStA, MallocngCoreStInflightA]
    rw [propext ⟨fun _ => trivial, fun _ => hwf2'⟩, pure_true, emp_sepConj]
  rw [propext ⟨fun _ => trivial, fun _ => hPure⟩, pure_true, emp_sepConj, hCoreEq]
  exact Entails.refl _

end VerifiedLibraries.Mallocng.Proofs
