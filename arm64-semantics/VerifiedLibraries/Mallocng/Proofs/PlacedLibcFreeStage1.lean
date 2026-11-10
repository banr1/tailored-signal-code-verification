/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch0
public import VerifiedLibraries.Mallocng.Proofs.GetMetaHelpers
public import VerifiedLibraries.Mallocng.Proofs.PlacedLibcFreeHelpers

/-!
# Placed `__libc_free` Stage 1 (`+0x000` to `+0x200`)

Verifies `__libc_free` (`blk06`) on non-null `p` from entry through the 48-byte prologue spill and
read-only metadata, size-class, stride, and canary checks up to the in-band header clear at
`b + 0x200#64` (`libcFree_stage1_ok`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Frame Preservation and Stack-Spill Bundles -/

def CalleeSaved22_28 (s0 s : State) : Prop :=
  s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem calleeSaved22_28_refl (s : State) : CalleeSaved22_28 s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem calleeSaved22_28_trans {s0 s1 s2 : State}
    (h01 : CalleeSaved22_28 s0 s1) (h12 : CalleeSaved22_28 s1 s2) :
    CalleeSaved22_28 s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2⟩

theorem procPreserved_trans' {s0 s1 s2 : State}
    (h01 : MallocngProcPreserved s0 s1) (h12 : MallocngProcPreserved s1 s2) :
    MallocngProcPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

/-- Pure state preservation across read-only basic blocks (`+0x028` to `+0x200`) of `__libc_free`. -/
def LibcFreeReadPres (s0 s : State) : Prop :=
  s.mem = s0.mem ∧ s.brk = s0.brk ∧ MallocngProcPreserved s0 s ∧
  s.sp = s0.sp ∧ s.spAligned = s0.spAligned ∧ CalleeSaved22_28 s0 s

theorem libcFreeReadPres_trans {s0 s1 s2 : State}
    (h01 : LibcFreeReadPres s0 s1) (h12 : LibcFreeReadPres s1 s2) :
    LibcFreeReadPres s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, procPreserved_trans' h01.2.2.1 h12.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   calleeSaved22_28_trans h01.2.2.2.2.2 h12.2.2.2.2.2⟩

/-- Saved 48-byte prologue spill slots (`x29, x30, x19, x20, x21` and unused slot `w5`). -/
def LibcFreeSpillSlots (sp0 : BitVec 64) (s0 : State) (w5 : BitVec 64) : SepProp :=
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((sp0 - 8#64) ↦₆₄ w5)

/-- Spatial precondition used during read-only stages (`+0x028` to `+0x200`). -/
def libcFreeReadPre (A : MallocngAddrs) (st : MallocngSt) (Rest : SepProp) : SepProp :=
  MallocngRoTablesAt A ∗ (A.ctx ↦ₛ st.ctx.toBytes) ∗
  ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Rest

/-! ## Read-Only Basic-Block Stages -/

private theorem libcFree_hdr_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 6 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p : BitVec 64} {n effCost : Nat}
    (hF : LiveUserBlockFacts st g idx p n effCost) (Rest : SepProp)
    {s1 : State} (hpc : s1.pc = b + 0x28#64) (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = p) :
    let res := (g.slotEnd idx).toNat - (p.toNat + n)
    let r5 := min res 5
    let tot := (p.toNat - g.storage.toNat) / 16
    let hdrB : BitVec 8 := BitVec.ofNat 8 ((r5 <<< 5) ||| idx)
    let P := libcFreeReadPre maddrs st Rest
    SepWP (blkPC_b06.rebase b (fun _ => none)) (b + 0x60#64) s1 P
      (sepPost (fun s2 => LibcFreeReadPres s1 s2 ∧ s2.readReg64 .x0 = p ∧
        s2.readReg64 .x2 = hdrB.zeroExtend 64 ∧
        s2.readReg64 .x4 = (BitVec.ofNat 32 tot).zeroExtend 64 ∧
        s2.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) P) (fun _ => ⌜False⌝) := by
  intro res r5 tot hdrB P
  have _ := hb
  have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
  have ⟨hHdrIdx, _, _, _⟩ := hdrByte_extract r5 idx (Nat.min_le_right _ _) hIdx31
  by_cases hShort : tot ≤ 0xffff
  · conv => arg 4; dsimp only [P, libcFreeReadPre]; rw [hF.focus_hdr_short hShort]
    wp_steps
    conv => arg 4; rw [← hF.focus_hdr_short hShort]
    refine SepWP.done rfl (by simp [hrun]) ⟨⟨?_, by simp [hx0], ?_, ?_, ?_⟩, Entails.refl _⟩
    · exact ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [CalleeSaved22_28, calleeSavedVRegs]⟩
    · simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]; rfl
    · simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]
      change BitVec.zeroExtend 64 (BitVec.ofNat 16 tot) = (BitVec.ofNat 32 tot).zeroExtend 64; bv_omega
    · simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]
      exact hdrB_mask64 hdrB hHdrIdx
  · have hLong : 0xffff < tot := by omega
    have hTotLt27 := hF.totalOff_lt_27
    have hSleF : (BitVec.ofNat 32 tot).sle 0xffff#32 = false := by
      rw [show (0xffff#32 : BitVec 32) = BitVec.ofNat 32 0xffff from rfl, bv32_sle_iff_of_lt31 (by omega) (by omega)]
      simp [show ¬ (tot ≤ 0xffff) by omega]
    have hSltT : (0xffff#32).slt (BitVec.ofNat 32 tot) = true := by
      rw [show (0xffff#32 : BitVec 32) = BitVec.ofNat 32 0xffff from rfl, bv32_slt_iff_of_lt31 (by omega) (by omega)]
      simp [hLong]
    conv => arg 4; dsimp only [P, libcFreeReadPre]; rw [hF.focus_hdr_long hLong]
    wp_steps
    conv => arg 4; rw [← hF.focus_hdr_long hLong]
    refine SepWP.done rfl (by simp [hrun]) ⟨⟨?_, by simp [hx0], ?_, ?_, ?_⟩, Entails.refl _⟩
    · exact ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [CalleeSaved22_28, calleeSavedVRegs]⟩
    · simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]; rfl
    · simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]; rfl
    · simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]
      exact hdrB_mask64 hdrB hHdrIdx

private theorem libcFree_meta_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 6 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p : BitVec 64} {n effCost : Nat}
    {hdrB : BitVec 8} (hF : LiveUserBlockFacts st g idx p n effCost) (Rest : SepProp)
    {s2 : State} (hpc : s2.pc = b + 0x60#64) (hrun : s2.status = .Running)
    (hx0 : s2.readReg64 .x0 = p) (hx2 : s2.readReg64 .x2 = hdrB.zeroExtend 64)
    (hx4 : s2.readReg64 .x4 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64)
    (hx20 : s2.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) :
    let P := libcFreeReadPre maddrs st Rest
    SepWP (blkPC_b06.rebase b (fun _ => none)) (b + 0x100#64) s2 P
      (sepPost (fun s3 => LibcFreeReadPres s2 s3 ∧ s3.readReg64 .x0 = p ∧
        s3.readReg64 .x2 = hdrB.zeroExtend 64 ∧
        s3.readReg64 .x4 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64 ∧
        s3.readReg64 .x5 = g.mem ∧
        s3.readReg64 .x7 = (g.packedWord.extractLsb' 0 8).zeroExtend 64 ∧
        s3.readReg64 .x9 = BitVec.ofNat 64 g.lastIdx ∧
        s3.readReg64 .x19 = g.metaPtr ∧
        s3.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) P) (fun _ => ⌜False⌝) := by
  intro P
  have _ := hb
  have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
  have hMemAddr : p + (-16#64 - ((BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16) <<< 4).signExtend 64)) = g.mem :=
    group_mem_addr_of_totalOff hF.totalOff_lt_27
      (by have := hF.p_add_n_48; rw [← hF.p_eq_storage_off]; omega) hF.p_eq_storage_off
  have hMemAddrU : p + (0xfffffffffffffff0#64 - ((BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16) <<< 4).signExtend 64)) = g.mem :=
    hMemAddr
  have ⟨hByte32, hByte64⟩ := packedWord_byte0_and31 g hF.last_le_31
  have hByteMask := hdrB_mask64 (g.packedWord.extractLsb' 0 8) hByte32
  have ⟨hAv1, hAv2⟩ := mask_ushiftRight_bit0_false g.availMask hIdx31 hF.avail_bit_false
  have ⟨hFr1, hFr2⟩ := mask_ushiftRight_bit0_false g.freedMask hIdx31 hF.freed_bit_false
  obtain ⟨ma, _, hMaBase, hFocusMa⟩ := hF.meta_page_base
  have hMaBase' : g.metaPtr &&& -4096#64 = ma.base := hMaBase
  obtain ⟨ctxRest, hCtxSplit⟩ := ctx_toBytes_split_secret maddrs.ctx st.ctx
  have hPageCtx := pageOf_add_lo12Of maddrs.ctx
  conv => arg 4; dsimp only [P, libcFreeReadPre]; rw [hF.focus_group_mem]
  wp_step; wp_step; wp_step; wp_step; wp_step
  conv => arg 4; rw [← hF.focus_group_mem, hF.focus_meta, pointsTo64_split_lo8 (g.metaPtr + 32#64) g.packedWord]
  wp_steps
  wp_if hle
  · wp_steps
    conv => arg 4; rw [← pointsTo64_split_lo8 (g.metaPtr + 32#64) g.packedWord, ← hF.focus_meta, hFocusMa, hCtxSplit]
    wp_steps
    conv => arg 4; rw [← hCtxSplit, ← hFocusMa]
    refine SepWP.done rfl (by simp [hrun])
      ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [CalleeSaved22_28, calleeSavedVRegs]⟩,
        by simp [hx0], by simp [hx2], by simp [hx4], by simp, by simp, ?_, by simp, by simp [hx20]⟩, Entails.refl _⟩
    simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64, Reg.gpr.injEq, BitVec.reduceEq, reduceIte]
    exact hByte64
  · exfalso; have := hF.last_le_31; have := hF.idx_le_last
    rw [bv32_sle_iff_of_lt31 (by omega) (by omega), decide_eq_true_eq] at hle; omega

private theorem libcFree_sc_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 6 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p : BitVec 64} {n effCost : Nat}
    {hdrB : BitVec 8} (hF : LiveUserBlockFacts st g idx p n effCost) (Rest : SepProp)
    {s3 : State} (hpc : s3.pc = b + 0x100#64) (hrun : s3.status = .Running)
    (hx0 : s3.readReg64 .x0 = p) (hx2 : s3.readReg64 .x2 = hdrB.zeroExtend 64)
    (hx4 : s3.readReg64 .x4 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64)
    (hx5 : s3.readReg64 .x5 = g.mem)
    (hx7 : s3.readReg64 .x7 = (g.packedWord.extractLsb' 0 8).zeroExtend 64)
    (hx9 : s3.readReg64 .x9 = BitVec.ofNat 64 g.lastIdx)
    (hx19 : s3.readReg64 .x19 = g.metaPtr)
    (hx20 : s3.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) :
    let P := libcFreeReadPre maddrs st Rest
    SepWP (blkPC_b06.rebase b (fun _ => none)) (b + 0x164#64) s3 P
      (sepPost (fun s4 => LibcFreeReadPres s3 s4 ∧ s4.readReg64 .x0 = p ∧
        s4.readReg64 .x2 = hdrB.zeroExtend 64 ∧
        s4.readReg64 .x4 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64 ∧
        s4.readReg64 .x5 = g.mem ∧
        s4.readReg64 .x7 = (g.packedWord.extractLsb' 0 8).zeroExtend 64 ∧
        s4.readReg64 .x8 = BitVec.ofNat 64 g.sc ∧
        s4.readReg64 .x9 = BitVec.ofNat 64 g.lastIdx ∧
        s4.readReg64 .x19 = g.metaPtr ∧
        s4.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) P) (fun _ => ⌜False⌝) := by
  intro P
  have _ := hb
  have hSc64 : g.sc < 64 := by rcases hF.sc_cases with h | h <;> omega
  have hUbfxSc := packedWord_ubfx_sc g hF.last_le_31 hSc64 hF.maplen_lt_52
  conv => arg 4; dsimp only [P, libcFreeReadPre]; rw [hF.focus_meta, pointsTo64_split_lo16 (g.metaPtr + 32#64) g.packedWord]
  wp_step; wp_step; wp_step; wp_step
  conv => arg 4; rw [← pointsTo64_split_lo16 (g.metaPtr + 32#64) g.packedWord, ← hF.focus_meta]
  rcases hF.sc_cases with hsc48 | hsc63
  · wp_if hhi
    · exfalso
      rw [show (BitVec.ofNat 64 g.sc).truncate 32 = BitVec.ofNat 32 g.sc by bv_omega,
        BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hhi
      change 47 < g.sc % 4294967296 at hhi; omega
    · obtain ⟨roRest, hRoSplit⟩ := split_sizeClass_roTablesAt maddrs hsc48
        ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Rest)
      have hOffSc := sxtw_lsl1_sc hsc48
      have hSbfmSc := sxtw_sbfm_sc hsc48
      have ⟨_, huMax, _, _⟩ := sizeClass_bounds hsc48
      have ⟨hLow, hHigh⟩ := hF.sc_lt_48_off hsc48
      have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
      have hMulB1 : idx * sizeClass g.sc ≤ 31 * 8191 := Nat.mul_le_mul hIdx31 huMax
      have hMulB2 : (idx + 1) * sizeClass g.sc ≤ 32 * 8191 := Nat.mul_le_mul (by omega) huMax
      have hTot27 := hF.totalOff_lt_27
      conv => arg 4; dsimp only [P, libcFreeReadPre]; rw [hRoSplit]
      wp_steps
      wp_if hge
      · wp_steps
        wp_if hlt
        · conv => arg 4; rw [← hRoSplit]
          refine SepWP.done rfl (by simp [hrun])
            ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [CalleeSaved22_28, calleeSavedVRegs]⟩,
              by simp [hx0], by simp [hx2], by simp [hx4], by simp [hx5], by simp [hx7],
              by simp, by simp [hx9], by simp [hx19], by simp [hx20]⟩, Entails.refl _⟩
        · exfalso
          rw [add32_sc_madd (by omega), bv32_slt_iff_of_lt31 (by omega) (by omega), decide_eq_true_eq] at hlt; omega
      · exfalso
        rw [madd32_idx_sc (by omega), bv32_sle_iff_of_lt31 (by omega) (by omega)] at hge
        simp [show idx * sizeClass g.sc ≤ (p.toNat - g.storage.toNat) / 16 by omega] at hge
  · wp_if hhi
    · have hSc63Mask := packedWord_sc63_mask g hF.last_le_31 hsc63 hF.maplen_lt_52
      wp_steps
      refine SepWP.done rfl (by simp [hrun])
        ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [CalleeSaved22_28, calleeSavedVRegs]⟩,
          by simp [hx0], by simp [hx2], by simp [hx4], by simp [hx5], by simp [hx7],
          by simp [hsc63], by simp [hx9], by simp [hx19], by simp [hx20]⟩, Entails.refl _⟩
    · exfalso
      rw [hsc63] at hhi; simp [BitVec.ult] at hhi

private theorem libcFree_stride_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 6 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p : BitVec 64} {n effCost : Nat}
    {hdrB : BitVec 8} (hF : LiveUserBlockFacts st g idx p n effCost) (Rest : SepProp)
    {s4 : State} (hpc : s4.pc = b + 0x164#64) (hrun : s4.status = .Running)
    (hx0 : s4.readReg64 .x0 = p) (hx2 : s4.readReg64 .x2 = hdrB.zeroExtend 64)
    (hx4 : s4.readReg64 .x4 = (BitVec.ofNat 32 ((p.toNat - g.storage.toNat) / 16)).zeroExtend 64)
    (hx5 : s4.readReg64 .x5 = g.mem)
    (hx7 : s4.readReg64 .x7 = (g.packedWord.extractLsb' 0 8).zeroExtend 64)
    (hx8 : s4.readReg64 .x8 = BitVec.ofNat 64 g.sc)
    (hx9 : s4.readReg64 .x9 = BitVec.ofNat 64 g.lastIdx)
    (hx19 : s4.readReg64 .x19 = g.metaPtr)
    (hx20 : s4.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) :
    let P := libcFreeReadPre maddrs st Rest
    SepWP (blkPC_b06.rebase b (fun _ => none)) (b + 0x320#64) s4 P
      (sepPost (fun s5 => LibcFreeReadPres s4 s5 ∧ s5.readReg64 .x0 = p ∧
        s5.readReg64 .x2 = hdrB.zeroExtend 64 ∧
        s5.readReg64 .x3 = BitVec.ofNat 64 g.stride ∧
        s5.readReg64 .x5 = g.mem ∧
        s5.readReg64 .x9 = BitVec.ofNat 64 g.lastIdx ∧
        s5.readReg64 .x19 = g.metaPtr ∧
        s5.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) P) (fun _ => ⌜False⌝) := by
  intro P
  have _ := hb
  have hSc64 : g.sc < 64 := by rcases hF.sc_cases with h | h <;> omega
  have hMapMask := packedWord_maplen_mask g hF.last_le_31 hSc64 hF.maplen_bytes_48
  have ⟨_, hByte64⟩ := packedWord_byte0_and31 g hF.last_le_31
  conv => arg 4; dsimp only [P, libcFreeReadPre]; rw [hF.focus_meta]
  wp_step; wp_step; wp_step
  conv => arg 4; rw [← hF.focus_meta]
  by_cases hMap0 : g.maplen = 0
  · have ⟨hsc48, _⟩ := hF.maplen_zero_sc hMap0
    have hStride : g.stride = 16 * sizeClass g.sc := by simp [GroupDesc.stride, slotStride, hMap0]
    have hOffSc := sxtw_lsl1_sc hsc48
    have hSbfmSc := sxtw_sbfm_sc hsc48
    have ⟨_, huMax, _, _⟩ := sizeClass_bounds hsc48
    obtain ⟨roRest, hRoSplit⟩ := split_sizeClass_roTablesAt maddrs hsc48
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Rest)
    wp_if heq
    · conv => arg 4; dsimp only [P, libcFreeReadPre]; rw [hRoSplit]
      wp_steps
      conv => arg 4; rw [← hRoSplit]
      refine SepWP.done rfl (by simp [hrun])
        ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [CalleeSaved22_28, calleeSavedVRegs]⟩,
          by simp [hx0], by simp [hx2], ?_, by simp [hx5], by simp [hx9], by simp [hx19], by simp [hx20]⟩, Entails.refl _⟩
      simp [hStride, sc16_ubfiz_shl4 hsc48]
    · exfalso; rw [hMap0] at heq; exact heq rfl
  · have hMapPos : 0 < g.maplen := Nat.pos_of_ne_zero hMap0
    have hMap48 := hF.maplen_bytes_48; have hTot27 := hF.totalOff_lt_27; have hMapOff := hF.maplen_pos_off hMapPos
    wp_if heq
    · exfalso
      have h0 : (BitVec.ofNat 64 (g.maplen * 4096)).toNat = 0 := by rw [heq]; rfl
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
    · wp_steps
      wp_if hhs
      · wp_steps
        by_cases hLast0 : g.lastIdx = 0
        · have hStride : g.stride = g.maplen * 4096 - 16 := by simp [GroupDesc.stride, hLast0, hMapPos]
          wp_if hlastEq
          · refine SepWP.done rfl (by simp [hrun])
              ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [CalleeSaved22_28, calleeSavedVRegs]⟩,
                by simp [hx0], by simp [hx2], ?_, by simp [hx5], by simp [hx9], by simp [hx19], by simp [hx20]⟩, Entails.refl _⟩
            simp [hStride]; bv_omega
          · exfalso; rw [hLast0] at hlastEq; exact hlastEq rfl
        · have hsc48 : g.sc < 48 := by
            rcases hF.sc_cases with h | h; · exact h
            · exact absurd (hF.sc_63_props h).1 hLast0
          have hStride : g.stride = 16 * sizeClass g.sc := by simp [GroupDesc.stride, slotStride, hLast0]
          have hOffSc := sxtw_lsl1_sc hsc48
          have hSbfmSc := sxtw_sbfm_sc hsc48
          have ⟨_, huMax, _, _⟩ := sizeClass_bounds hsc48
          obtain ⟨roRest, hRoSplit⟩ := split_sizeClass_roTablesAt maddrs hsc48
            ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Rest)
          wp_if hlastEq
          · exfalso; have := hF.last_le_31
            have h0 : (BitVec.ofNat 64 g.lastIdx).toNat = 0 := by rw [hlastEq]; rfl
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
          · conv => arg 4; dsimp only [P, libcFreeReadPre]; rw [hRoSplit]
            wp_steps
            conv => arg 4; rw [← hRoSplit]
            refine SepWP.done rfl (by simp [hrun])
              ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [CalleeSaved22_28, calleeSavedVRegs]⟩,
                by simp [hx0], by simp [hx2], ?_, by simp [hx5], by simp [hx9], by simp [hx19], by simp [hx20]⟩, Entails.refl _⟩
            simp [hStride, sc16_ubfiz_shl4 hsc48]
      · exfalso
        have hFalse := maplen_shr4_sub1_ult_false hMapPos hMap48 hTot27 hMapOff
        revert hFalse hhs; bv_robdd

private theorem libcFree_canaries_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 6 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p : BitVec 64} {n effCost : Nat}
    (hF : LiveUserBlockFacts st g idx p n effCost) (Rest : SepProp)
    {s6 : State} (hpc : s6.pc = b + 0x1bc#64) (hrun : s6.status = .Running)
    (hx0 : s6.readReg64 .x0 = p)
    (hx2 : s6.readReg64 .x2 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - (p.toNat + n)))
    (hx4 : s6.readReg64 .x4 = g.slotEnd idx)
    (hx53 : s6.readReg64 .x5 + s6.readReg64 .x3 = g.slotEnd idx)
    (hx9 : s6.readReg64 .x9 = BitVec.ofNat 64 g.lastIdx)
    (hx19 : s6.readReg64 .x19 = g.metaPtr)
    (hx20 : s6.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) :
    let P := libcFreeReadPre maddrs st Rest
    SepWP (blkPC_b06.rebase b (fun _ => none)) (b + 0x200#64) s6 P
      (sepPost (fun s7 => LibcFreeReadPres s6 s7 ∧ s7.readReg64 .x0 = p ∧
        s7.readReg64 .x9 = BitVec.ofNat 64 g.lastIdx ∧
        s7.readReg64 .x19 = g.metaPtr ∧
        s7.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) P) (fun _ => ⌜False⌝) := by
  intro P
  have _ := hb
  have ⟨_, _, _, _, _, hEnd48⟩ := hF.stride_bounds
  have hP48 := hF.p_add_n_48
  have hPLeEnd := hF.p_add_n_le_end
  have hEndSubP : g.slotEnd idx - p = BitVec.ofNat 64 (n + ((g.slotEnd idx).toNat - (p.toNat + n))) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega)), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hEndSubRes :
      g.slotEnd idx - BitVec.ofNat 64 ((g.slotEnd idx).toNat - (p.toNat + n)) = p + BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    have hLe : BitVec.ofNat 64 ((g.slotEnd idx).toNat - (p.toNat + n)) ≤ g.slotEnd idx := by
      rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [BitVec.toNat_sub_of_le hLe, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  wp_steps
  wp_if hhs
  · wp_step
    conv => arg 4; dsimp only [P, libcFreeReadPre]; rw [hF.focus_end_req]
    wp_step; wp_step
    conv => arg 4; rw [← hF.focus_end_req, hF.focus_slot_end]
    wp_steps
    conv => arg 4; rw [← hF.focus_slot_end]
    refine SepWP.done rfl (by simp [hrun])
      ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [CalleeSaved22_28, calleeSavedVRegs]⟩,
        by simp [hx0], by simp [hx9], by simp [hx19], by simp [hx20]⟩, Entails.refl _⟩
  · exfalso
    have hMod1 : (BitVec.ofNat 64 (n + ((g.slotEnd idx).toNat - (p.toNat + n)))).toNat =
        n + ((g.slotEnd idx).toNat - (p.toNat + n)) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hMod2 : (BitVec.ofNat 64 ((g.slotEnd idx).toNat - (p.toNat + n))).toNat =
        (g.slotEnd idx).toNat - (p.toNat + n) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    revert hhs
    simp [BitVec.ule, hMod1, hMod2]

private theorem sepWP_chain_read {prog : Program} {tgt : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → Prop}
    (hpres : LibcFreeReadPres s0 s)
    (h : SepWP prog tgt s P (sepPost (fun sf => LibcFreeReadPres s sf ∧ Q sf) P) (fun _ => ⌜False⌝)) :
    SepWP prog tgt s P (sepPost (fun sf => LibcFreeReadPres s0 sf ∧ Q sf) P) (fun _ => ⌜False⌝) :=
  SepWP.mono h fun _ _ _ _ ⟨⟨hf, hq⟩, he⟩ => ⟨⟨libcFreeReadPres_trans hpres hf, hq⟩, he⟩

private theorem libcFree_trailer5_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 6 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p : BitVec 64} {n effCost : Nat}
    (hF : LiveUserBlockFacts st g idx p n effCost)
    (hGe5 : 5 ≤ (g.slotEnd idx).toNat - (p.toNat + n)) (Rest : SepProp)
    {s5' : State} (hpc : s5'.pc = b + 0x344#64) (hrun : s5'.status = .Running)
    (hx0 : s5'.readReg64 .x0 = p) (hx4 : s5'.readReg64 .x4 = g.slotEnd idx)
    (hx53 : s5'.readReg64 .x5 + s5'.readReg64 .x3 = g.slotEnd idx)
    (hx7 : s5'.readReg64 .x7 = 5#64)
    (hx9 : s5'.readReg64 .x9 = BitVec.ofNat 64 g.lastIdx)
    (hx19 : s5'.readReg64 .x19 = g.metaPtr)
    (hx20 : s5'.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) :
    let P := libcFreeReadPre maddrs st Rest
    SepWP (blkPC_b06.rebase b (fun _ => none)) (b + 0x200#64) s5' P
      (sepPost (fun s7 => LibcFreeReadPres s5' s7 ∧ s7.readReg64 .x0 = p ∧
        s7.readReg64 .x9 = BitVec.ofNat 64 g.lastIdx ∧
        s7.readReg64 .x19 = g.metaPtr ∧
        s7.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) P) (fun _ => ⌜False⌝) := by
  intro P
  have _ := hb
  have hRes31 := hF.reserved_lt_31
  wp_step; wp_step
  conv => arg 4; dsimp only [P, libcFreeReadPre]; rw [hF.focus_trailer5 hGe5]
  wp_steps
  have hZx : (BitVec.ofNat 32 ((g.slotEnd idx).toNat - (p.toNat + n))).zeroExtend 64 =
      BitVec.ofNat 64 ((g.slotEnd idx).toNat - (p.toNat + n)) := by
    generalize (g.slotEnd idx).toNat - (p.toNat + n) = res at hRes31 ⊢; bv_omega
  wp_if hhi
  · wp_step; wp_step
    conv => arg 4; rw [← hF.focus_trailer5 hGe5]
    refine sepWP_chain_read
      ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [CalleeSaved22_28, calleeSavedVRegs]⟩ ?_
    apply libcFree_canaries_ok hb hF Rest
    · rfl
    · simp [hrun]
    · simp [hx0]
    · simp [wp_norm, arm64_norm]
    · simp [hx4]
    · simp [hx53]
    · simp [hx9]
    · simp [hx19]
    · simp [hx20]
  · exfalso
    revert hhi
    simp [hZx, BitVec.ult,
      Nat.mod_eq_of_lt (by omega : (g.slotEnd idx).toNat - (p.toNat + n) < 2 ^ 64)]
    omega

set_option maxRecDepth 20000 in
private theorem libcFree_nominal_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 6 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p : BitVec 64} {n effCost : Nat}
    (hF : LiveUserBlockFacts st g idx p n effCost) (Rest : SepProp)
    {s5 : State} (hpc : s5.pc = b + 0x320#64) (hrun : s5.status = .Running)
    (hx0 : s5.readReg64 .x0 = p)
    (hx2 : s5.readReg64 .x2 =
      (BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (p.toNat + n)) 5 <<< 5) ||| idx)).zeroExtend 64)
    (hx3 : s5.readReg64 .x3 = BitVec.ofNat 64 g.stride) (hx5 : s5.readReg64 .x5 = g.mem)
    (hx9 : s5.readReg64 .x9 = BitVec.ofNat 64 g.lastIdx)
    (hx19 : s5.readReg64 .x19 = g.metaPtr)
    (hx20 : s5.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) :
    let P := libcFreeReadPre maddrs st Rest
    SepWP (blkPC_b06.rebase b (fun _ => none)) (b + 0x200#64) s5 P
      (sepPost (fun s7 => LibcFreeReadPres s5 s7 ∧ s7.readReg64 .x0 = p ∧
        s7.readReg64 .x9 = BitVec.ofNat 64 g.lastIdx ∧
        s7.readReg64 .x19 = g.metaPtr ∧
        s7.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64) P) (fun _ => ⌜False⌝) := by
  intro P
  have _ := hb
  let res := (g.slotEnd idx).toNat - (p.toNat + n); let r5 := min res 5
  have hIdx31 : idx ≤ 31 := Nat.le_trans hF.idx_le_last hF.last_le_31
  have ⟨_, hHdrShr, hHdrUbfx, hHdrUle⟩ := hdrByte_extract r5 idx (Nat.min_le_right _ _) hIdx31
  have hIdxMask : (BitVec.ofNat 32 idx).zeroExtend 64 &&& 0xff#64 = BitVec.ofNat 64 idx := by
    rw [show BitVec.ofNat 64 idx = (BitVec.ofNat 32 idx).zeroExtend 64 by bv_omega]
    have hlt : (BitVec.ofNat 32 idx).ult 32#32 = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change idx % 4294967296 < 32; omega
    revert hlt; bv_robdd
  have hSlotEnd : (g.mem + 16#64) +
      ((BitVec.ofNat 64 g.stride - 4#64) + BitVec.ofNat 64 idx * BitVec.ofNat 64 g.stride) = g.slotEnd idx := by
    have ⟨hStr16, _, _, _, hEndNat, hEnd48⟩ := hF.stride_bounds
    exact free_slotEnd_eq hStr16 hEnd48 (by rw [hEndNat, Nat.add_mul, Nat.one_mul]; omega)
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  have ⟨h9f1, h9f2, h9f3, hShr8⟩ := hdr8_ule_0x9f (BitVec.ofNat 8 ((r5 <<< 5) ||| idx))
  by_cases hLt5 : res < 5
  · have hr5Eq : r5 = res := Nat.min_eq_left (by omega)
    wp_if hls
    · refine sepWP_chain_read
        ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [CalleeSaved22_28, calleeSavedVRegs]⟩ ?_
      apply libcFree_canaries_ok hb hF Rest
      · rfl
      · simp [hrun]
      · simp [hx0]
      · simp only [wp_norm, arm64_norm]; dsimp only [r5, res] at hHdrUbfx hr5Eq
        simpa [hr5Eq] using hHdrUbfx
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hSlotEnd]
      · simp [hx9]
      · simp [hx19]
      · simp [hx20]
    · exfalso; dsimp only [r5, res] at hHdrUle h9f1 h9f2 h9f3
      try rw [h9f3] at hls; try rw [h9f2] at hls; try rw [h9f1] at hls
      exact hls (hHdrUle.mpr (by omega))
  · have hGe5 : 5 ≤ res := by omega
    have hr5Eq : r5 = 5 := Nat.min_eq_right hGe5
    wp_if hls
    · exfalso; dsimp only [r5, res] at hHdrUle h9f1 h9f2 h9f3
      try rw [h9f3] at hls; try rw [h9f2] at hls; try rw [h9f1] at hls
      exact absurd (hHdrUle.mp hls) (by omega)
    · refine sepWP_chain_read
        ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [CalleeSaved22_28, calleeSavedVRegs]⟩ ?_
      apply libcFree_trailer5_ok hb hF hGe5 Rest
      · rfl
      · simp [hrun]
      · simp [hx0]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hSlotEnd]
      · simp only [wp_norm, arm64_norm]; dsimp only [r5, res] at hShr8 hHdrShr hr5Eq
        rw [hShr8, hHdrShr, hr5Eq]; rfl
      · simp [hx9]
      · simp [hx19]
      · simp [hx20]

/-! ## Combined Non-Null Stage 1 -/

private theorem sepWP_bind_read {prog : Program} {mid tgt : BitVec 64} {s : State} {P : SepProp}
    {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (sepPost Q P) (fun _ => ⌜False⌝))
    (h2 : ∀ s', s'.pc = mid → s'.status = .Running → Q s' → SepWP prog tgt s' P post (fun _ => ⌜False⌝)) :
    SepWP prog tgt s P post (fun _ => ⌜False⌝) :=
  SepWP.seq h1 fun s' _ hpc hrun ⟨hq, hent⟩ => SepWP.weaken_pre hent (h2 s' hpc hrun hq)

set_option maxRecDepth 20000 in
/-- Combined Stage 1 (`+0x000` to `+0x200`) on non-null `p`: checks 16-byte alignment, spills the
    48-byte prologue frame (`x29, x30, x19, x20, x21`), and validates all group, `meta`, and canary
    invariants up to `b + 0x200#64`. -/
theorem libcFree_stage1_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 6 b)
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {p sp0 : BitVec 64} {n effCost : Nat}
    (hF : LiveUserBlockFacts st g idx p n effCost) (Rest : SepProp)
    {s0 : State} (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem)
    (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = p) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true) :
    SepWP (blkPC_b06.rebase b (fun _ => none)) (b + 0x200#64) s0
      ((MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Rest) ∗ stackFrameAt sp0 272)
      (fun s7 P7 => ∃ w5 : BitVec 64,
        (P7 ⊢ MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Rest ∗
          stackFrameAt (sp0 - 48#64) 224 ∗ LibcFreeSpillSlots sp0 s0 w5) ∧
        VerifiedLibraries.mallocngLib.CodeLoaded mmpl s7.mem ∧
        s7.mem.perm = s0.mem.perm ∧ s7.brk = s0.brk ∧
        MallocngProcPreserved s0 s7 ∧
        s7.sp = sp0 - 48#64 ∧ s7.spAligned = true ∧
        CalleeSaved22_28 s0 s7 ∧
        s7.readReg64 .x0 = p ∧
        s7.readReg64 .x9 = BitVec.ofNat 64 g.lastIdx ∧
        s7.readReg64 .x19 = g.metaPtr ∧
        s7.readReg64 .x20 = (BitVec.ofNat 32 idx).zeroExtend 64)
      (fun _ => ⌜False⌝) := by
  have _ := hb
  have hpNe0 : p ≠ 0#64 := hF.p_ne_zero
  have hAnd15 := hF.p_and_15
  apply SepWP.weaken_pre (sepConj_mono_right (stackFrameAt_272_split_48 sp0))
  simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  have ha1 : sp0 + (-48#64) = sp0 - 48#64 := by bv_arith
  have ha2 : sp0 - 48#64 + 8#64 = sp0 - 40#64 := by bv_arith
  have ha3 : sp0 - 48#64 + 16#64 = sp0 - 32#64 := by bv_arith
  have ha4 : sp0 - 32#64 + 8#64 = sp0 - 24#64 := by bv_arith
  have ha5 : sp0 - 48#64 + 32#64 = sp0 - 16#64 := by bv_arith
  have hspAl0' : (sp0 &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp0] using hspAl0
  have hspAl48 : ((sp0 - 48#64) &&& 15#64 == 0#64) = true := by revert hspAl0'; bv_robdd
  wp_step; wp_step; wp_step
  wp_stp64_cl m1 hm1 hcl0 hcl1; wp_step
  wp_stp64_cl m2 hm2 hcl1 hcl2
  wp_str64_cl m3 hm3 hcl2 hcl3
  let R1 := Rest ∗ stackFrameAt (sp0 - 48#64) 224 ∗ LibcFreeSpillSlots sp0 s0 w5
  have hPreEq :
      ((MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Rest) ∗
        stackFrameAt (sp0 - 48#64) 224 ∗
        ((sp0 - 48#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
        ((sp0 - 40#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
        ((sp0 - 32#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
        ((sp0 - 24#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
        ((sp0 - 16#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
        ((sp0 - 8#64) ↦₆₄ w5)) =
      libcFreeReadPre maddrs st R1 := by
    dsimp only [libcFreeReadPre, R1, LibcFreeSpillSlots]; ac_rfl
  rw [hPreEq]
  refine sepWP_bind_read
    (libcFree_hdr_ok hb hF R1 (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simpa [arm64_norm] using hx0)) ?_
  rintro s2 hpc2 hrun2 ⟨hp12, hx0_2, hx2_2, hx4_2, hx20_2⟩
  refine sepWP_bind_read (libcFree_meta_ok hb hF R1 hpc2 hrun2 hx0_2 hx2_2 hx4_2 hx20_2) ?_
  rintro s3 hpc3 hrun3 ⟨hp23, hx0_3, hx2_3, hx4_3, hx5_3, hx7_3, hx9_3, hx19_3, hx20_3⟩
  refine sepWP_bind_read (libcFree_sc_ok hb hF R1 hpc3 hrun3 hx0_3 hx2_3 hx4_3 hx5_3 hx7_3 hx9_3 hx19_3 hx20_3) ?_
  rintro s4 hpc4 hrun4 ⟨hp34, hx0_4, hx2_4, hx4_4, hx5_4, hx7_4, hx8_4, hx9_4, hx19_4, hx20_4⟩
  refine sepWP_bind_read (libcFree_stride_ok hb hF R1 hpc4 hrun4 hx0_4 hx2_4 hx4_4 hx5_4 hx7_4 hx8_4 hx9_4 hx19_4 hx20_4) ?_
  rintro s5 hpc5 hrun5 ⟨hp45, hx0_5, hx2_5, hx3_5, hx5_5, hx9_5, hx19_5, hx20_5⟩
  refine SepWP.mono (libcFree_nominal_ok hb hF R1 hpc5 hrun5 hx0_5 hx2_5 hx3_5 hx5_5 hx9_5 hx19_5 hx20_5) ?_
  rintro s7 P7 _ _ ⟨⟨hp57, hx0_7, hx9_7, hx19_7, hx20_7⟩, hent7⟩
  have ⟨hmem7, hbrk7, hproc7, hsp7, hspAl7, hcs7⟩ :=
    libcFreeReadPres_trans hp12 (libcFreeReadPres_trans hp23
      (libcFreeReadPres_trans hp34 (libcFreeReadPres_trans hp45 hp57)))
  refine ⟨w5, hent7, hmem7 ▸ hcl3, ?_, hbrk7, ?_, ?_, ?_, ?_, hx0_7, hx9_7, hx19_7, hx20_7⟩
  · rw [hmem7]; exact hm3.trans (hm2.trans hm1)
  · exact procPreserved_trans' ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩ hproc7
  · simpa [arm64_norm, hsp0] using hsp7
  · rw [hspAl7]; simpa [State.spAligned, arm64_norm, hsp0] using hspAl48
  · refine calleeSaved22_28_trans ?_ hcs7
    exact ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
           by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩

end VerifiedLibraries.Mallocng.Proofs
