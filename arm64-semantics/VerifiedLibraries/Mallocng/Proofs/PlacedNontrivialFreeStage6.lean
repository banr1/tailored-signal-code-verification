/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.PlacedNontrivialFreeStage5

set_option autoImplicit false
set_option maxRecDepth 20000

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic ProofLib.ProgramReflection VerifiedLibraries.Mallocng

/-!
# Placed `nontrivial_free` Nested-Group Retirement

Proves `sepWP_nf_retire_nested` for retiring an empty nested group (`g.maplen = 0`) in `blk05`:
parent-group validation, zeroing `[g.mem]`, recursive `bl nontrivial_free`, and `free_meta` into
`NfFuelPost`.
-/

set_option maxHeartbeats 800000 in
theorem sepWP_nf_retire_nested [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel' : Nat} (hFuel : fuel' + 1 ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {bud : MallocngBudget}
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {active1 usage1 : List (BitVec 64)} {actLists1 : List (List (BitVec 64))}
    {gsDeq : List GroupDesc} {bvDeq : BitVec 64 → BitVec 8}
    {s0 s : State}
    (hpc : s.pc = b + 0x1d4#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st)
    (hKeep : EmptyGroupKeepWf st) (hFull : FullQueueKeepWf st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hAllFree : (g.availMask ||| g.freedMask) + (1#32 <<< idx) = (2#32 <<< g.lastIdx) - 1#32)
    (hMap0 : g.maplen = 0)
    (hBound : groupNestBound g ≤ fuel' + 1)
    (hDeq : DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq)
    (hRec : ∀ (st1 : MallocngSt) (pg1 : GroupDesc) (pIdx : Nat),
      groupNestBound pg1 ≤ fuel' → EmptyGroupKeepWf st1 → FullQueueKeepWf st1 →
      subroutine_ok (blkPC_b05.rebase b (fun _ => none)) b
        (nontrivialFreeFuelPlainSpec (k + 1) fuel' γ brkStart bud st1 pg1 pIdx)) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      ((maddrs.ctx ↦ₛ { st.ctx with active := active1, usageByClass := usage1 }.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) bvDeq ∗
       NfAllFreeFrame (fuel' + 1) γ st s0)
      (NfFuelPost k (fuel' + 1) γ brkStart bud st s0) (fun _ => ⌜False⌝) := by
  have _ := hb
  let gZero : GroupDesc := { g with prev := 0#64, next := 0#64 }
  let keepAfterMeta : BitVec 64 → Prop := fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a
  let cDeq : CtxFields := { st.ctx with active := active1, usageByClass := usage1 }
  obtain ⟨pg0, pIdx, tot, maPg,
          hCarveMeta, hMemAnd15, hpLeLast, hPgLast31, hPgSc24, hTotLe,
          hHdrPIdx, hSubPgMem, hPgLow5, ⟨hAvLsb, _⟩, ⟨hFrLsb, _⟩,
          hMaBase, hPgScExtr, hTotLo, hTotHi, hPgMapMask, hPgMapPosProps,
          ⟨R_hdr, hFocusHdr⟩, ⟨R_pgMem, hFocusPgMem⟩, ⟨R_pgCells, hFocusPgCells⟩,
          ⟨R_pg8, hFocusPg8⟩, ⟨R_pg16, hFocusPg16⟩, ⟨R_sec, hFocusSec⟩,
          ⟨R_gMem, hFocusGMem, hWriteGMem⟩,
          hProt1, hMap1, hWf1, hKeep1, hFull1, hPg1Mem, hPg1Claimed,
          hPg1MetaEq, hNestLt, hmRes1, hResErase1, hCnt1, hDyn1, hPgDeq⟩ :=
    free_retire_nestedGroup hwf hKeep hFull hg hIdx hClaimed hAllFree hMap0 hDeq
  have hpIdx31 : pIdx ≤ 31 := Nat.le_trans hpLeLast hPgLast31
  have hPgSc48 : pg0.sc < 48 := by omega
  have hPgSxtw := sc48_sxtw_props ⟨pg0.sc, hPgSc48⟩
  have hPw : gZero.packedWord = g.packedWord := rfl
  have hGZeroMem : gZero.mem = g.mem := rfl
  have hGZeroMeta : gZero.metaPtr = g.metaPtr := rfl
  have hPwMask0 : g.packedWord &&& -4096#64 = 0#64 := by
    rw [packedWord_and_neg4096 g, hMap0]
  rw [hCarveMeta, metaBytes_eq_cells gZero, hPw, hGZeroMem, hGZeroMeta]
  apply step_ldr64_fast (b + 0x1d4#64) (b + 0x1d8#64) (g.metaPtr + 32#64) g.packedWord
  · exact hpc
  · exact hrun
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, arm64_norm, hx19]
  · wp_sep_access_fast
  · bv_omega
  wp_step
  wp_step
  ·
    apply step_ldr64_fast (b + 0x304#64) (b + 0x308#64) (g.metaPtr + 16#64) g.mem
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrun]
    · wp_close_fetch_cl
    · rfl
    · simp only [evalAddrMode, arm64_norm, hx19]
    · wp_sep_access_fast
    · bv_omega
    rw [← hGZeroMeta, ← hGZeroMem, ← hPw, ← metaBytes_eq_cells gZero]
    wp_step
    wp_step
    ·
      rw [hFocusHdr]
      apply step_ldr8_fast (b + 0x318#64) (b + 0x31c#64) (g.mem - 4#64) 0#8
      · simp only [arm64_norm]
      · simp only [arm64_norm, hrun]
      · wp_close_fetch_cl
      · rfl
      · simp only [evalAddrMode, arm64_norm]
      · wp_sep_access_fast
      · bv_omega
      apply step_ldr8_fast (b + 0x31c#64) (b + 0x320#64) (g.mem - 3#64)
        (BitVec.ofNat 8 ((6 <<< 5) ||| pIdx))
      · rfl
      · simp only [arm64_norm, hrun]
      · wp_close_fetch_cl
      · rfl
      · simp only [evalAddrMode, arm64_norm]
      · wp_sep_access_fast
      · bv_omega
      apply step_ldr16_fast (b + 0x320#64) (b + 0x324#64) (g.mem - 2#64) (BitVec.ofNat 16 tot)
      · rfl
      · simp only [arm64_norm, hrun]
      · wp_close_fetch_cl
      · rfl
      · simp only [evalAddrMode, arm64_norm]
      · wp_sep_access_fast
      · bv_omega
      rw [← hFocusHdr]
      have hTotZ32 : (BitVec.ofNat 16 tot).zeroExtend 32 = BitVec.ofNat 32 tot := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        change (tot % 65536) % (2 ^ 32) = tot % (2 ^ 32)
        rw [Nat.mod_eq_of_lt (by omega : tot < 65536)]
      have hPIdxZ64 : ((BitVec.ofNat 8 ((6 <<< 5) ||| pIdx)).zeroExtend 64) &&& 0x1f#64 =
          BitVec.ofNat 64 pIdx := by
        have hEq32 := hHdrPIdx
        have hL : ∀ v : BitVec 8, ((v.zeroExtend 64) &&& 0x1f#64) =
            ((v.zeroExtend 32) &&& 0x1f#32).zeroExtend 64 := by decide
        rw [hL, hEq32]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        change (pIdx % (2 ^ 32)) % (2 ^ 64) = pIdx % (2 ^ 64)
        rw [Nat.mod_eq_of_lt (by omega : pIdx < 2 ^ 32)]
      have hShiftTot : ∀ v : BitVec 32,
          BitVec.truncate 32 (BitVec.zeroExtend 64 v <<< 4) = v <<< 4 := by
        intro v; bv_bits
      wp_step
      wp_step
      wp_step
      wp_step
      wp_step
      wp_step
      rw [hFocusPgMem]
      apply step_ldr64_fast (b + 0x358#64) (b + 0x35c#64) pg0.mem pg0.metaPtr
      · rfl
      · simp only [arm64_norm, hrun]
      · wp_close_fetch_cl
      · rfl
      · simp only [evalAddrMode, extendVal, arm64_norm, hShiftTot]
        rw [show (0xfffffffffffffff0#64 : BitVec 64) = -16#64 by decide]
        exact Prod.ext hSubPgMem rfl
      · wp_sep_access_fast
      · bv_omega
      rw [← hFocusPgMem]
      rw [hFocusPgCells]
      apply step_ldr64_fast (b + 0x35c#64) (b + 0x360#64) (pg0.metaPtr + 16#64) pg0.mem
      · rfl
      · simp only [arm64_norm, hrun]
      · wp_close_fetch_cl
      · rfl
      · simp only [evalAddrMode, arm64_norm]
      · wp_sep_access_fast
      · bv_omega
      rw [← hFocusPgCells]
      wp_step
      wp_step
      wp_if_nd hPgMemNeTrap
      · exfalso
        simp only [arm64_norm, hShiftTot, bne_iff_ne, ne_eq] at hPgMemNeTrap
        rw [show (0xfffffffffffffff0#64 : BitVec 64) = -16#64 by decide] at hPgMemNeTrap
        exact hPgMemNeTrap hSubPgMem
      ·
        rw [hFocusPg8]
        apply step_ldr8_fast (b + 0x368#64) (b + 0x36c#64)
          (pg0.metaPtr + 32#64) (pg0.packedWord.truncate 8)
        · simp only [arm64_norm]
        · simp only [arm64_norm, hrun]
        · wp_close_fetch_cl
        · rfl
        · simp only [evalAddrMode, arm64_norm]
        · wp_sep_access_fast
        · bv_omega
        rw [← hFocusPg8]
        have hAnd31_32 : ∀ v : BitVec 8,
            BitVec.truncate 32 (BitVec.zeroExtend 64 v &&& 0x1f0000001f#64) =
            BitVec.zeroExtend 32 v &&& 31#32 := by decide
        have hMask192_64 : ∀ v : BitVec 8,
            (192#64 ||| BitVec.setWidth 64 v) &&& 0x1f0000001f#64 =
            (192#64 ||| BitVec.setWidth 64 v) &&& 31#64 := by decide
        have hHdrPIdx192 :
            BitVec.zeroExtend 32 (BitVec.ofNat 8 (192 ||| pIdx)) &&& 31#32 =
            BitVec.ofNat 32 pIdx := hHdrPIdx
        have hPIdxMod : (BitVec.ofNat 32 pIdx).toNat % 32 = pIdx := by
          simp only [BitVec.toNat_ofNat]; omega
        have hToInt32 : ∀ a : Nat, a < 2 ^ 31 → (BitVec.ofNat 32 a).toInt = (a : Int) := by
          intro a ha
          rw [BitVec.toInt_eq_toNat_of_lt
                (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : a < 2 ^ 32)]; omega),
              BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : a < 2 ^ 32)]
        wp_step
        wp_step
        wp_step
        wp_if_nd hPIdxGtTrap
        · exfalso
          simp only [hAnd31_32, hPgLow5, hHdrPIdx192] at hPIdxGtTrap
          rw [BitVec.slt, decide_eq_true_eq,
              hToInt32 pg0.lastIdx (by omega), hToInt32 pIdx (by omega)] at hPIdxGtTrap
          omega
        ·
          rw [hFocusPgCells]
          apply step_ldr32_fast (b + 0x378#64) (b + 0x37c#64)
            (pg0.metaPtr + 24#64) pg0.availMask
          · simp only [arm64_norm]
          · simp only [arm64_norm, hrun]
          · wp_close_fetch_cl
          · rfl
          · simp only [evalAddrMode, arm64_norm]
          · wp_sep_access_fast
          · bv_omega
          wp_step
          wp_step
          wp_if_nd hAvTrap
          · exfalso
            have hAvF : pg0.availMask.getLsbD pIdx = false := by
              have h := hAvLsb
              rw [BitVec.ushiftRight_eq'] at h
              simp only [BitVec.toNat_ofNat, BitVec.getLsbD_ushiftRight, Nat.add_zero] at h
              rwa [Nat.mod_eq_of_lt (by omega : pIdx < 2 ^ 32)] at h
            simp only [hAnd31_32, hHdrPIdx192, hPIdxMod] at hAvTrap
            rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, Nat.add_zero, hAvF] at hAvTrap
            exact absurd hAvTrap (by decide)
          ·
            apply step_ldr32_fast (b + 0x384#64) (b + 0x388#64)
              (pg0.metaPtr + 28#64) pg0.freedMask
            · simp only [arm64_norm]
            · simp only [arm64_norm, hrun]
            · wp_close_fetch_cl
            · rfl
            · simp only [evalAddrMode, arm64_norm]
            · wp_sep_access_fast
            · bv_omega
            rw [← hFocusPgCells]
            wp_step
            wp_step
            wp_if_nd hFrTrap
            · exfalso
              have hFrF : pg0.freedMask.getLsbD pIdx = false := by
                have h := hFrLsb
                rw [BitVec.ushiftRight_eq'] at h
                simp only [BitVec.toNat_ofNat, BitVec.getLsbD_ushiftRight, Nat.add_zero] at h
                rwa [Nat.mod_eq_of_lt (by omega : pIdx < 2 ^ 32)] at h
              simp only [hAnd31_32, hHdrPIdx192, hPIdxMod] at hFrTrap
              rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, Nat.add_zero, hFrF] at hFrTrap
              exact absurd hFrTrap (by decide)
            ·
              have hCtx20 : pageOf maddrs.ctx + lo12Of maddrs.ctx = maddrs.ctx :=
                pageOf_add_lo12Of maddrs.ctx
              wp_step
              wp_step
              obtain ⟨SecRest, hSecFocus⟩ := ctx_focus_secret maddrs.ctx cDeq
              have hSecEq : cDeq.secret = st.ctx.secret := rfl
              change SepWP _ _ _ ((maddrs.ctx ↦ₛ cDeq.toBytes) ∗ _) _ _
              rw [hSecFocus, hSecEq]
              apply step_ldr64_fast (b + 0x398#64) (b + 0x39c#64) maddrs.ctx st.ctx.secret
              · rfl
              · simp only [arm64_norm, hrun]
              · wp_close_fetch_cl
              · rfl
              · simp only [evalAddrMode, arm64_norm, hCtx20]
              · wp_sep_access_fast
              · bv_omega
              rw [← hSecEq, ← hSecFocus]
              rw [hFocusSec]
              apply step_ldr64_fast (b + 0x39c#64) (b + 0x3a0#64) maPg.base st.ctx.secret
              · rfl
              · simp only [arm64_norm, hrun]
              · wp_close_fetch_cl
              · rfl
              · simp only [evalAddrMode, arm64_norm]
                exact Prod.ext hMaBase rfl
              · wp_sep_access_fast
              · bv_omega
              rw [← hFocusSec]
              wp_step
              wp_step
              rw [hFocusPg16]
              apply step_ldr16_fast (b + 0x3a8#64) (b + 0x3ac#64)
                (pg0.metaPtr + 32#64) (pg0.packedWord.truncate 16)
              · rfl
              · simp only [arm64_norm, hrun]
              · wp_close_fetch_cl
              · rfl
              · simp only [evalAddrMode, arm64_norm]
              · wp_sep_access_fast
              · bv_omega
              rw [← hFocusPg16]
              wp_step
              wp_step
              wp_step
              wp_if_nd hScHiTrap
              · exfalso
                rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_setWidth,
                    BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hScHiTrap
                omega
              ·
                wp_step
                obtain ⟨RoRest, hRoFocus⟩ := roTables_focus_sizeClass maddrs hPgSc48
                dsimp only [NfAllFreeFrame]
                rw [hRoFocus]
                apply step_ldr16_fast (b + 0x3c0#64) (b + 0x3c4#64)
                  (maddrs.sizeClasses + BitVec.ofNat 64 (2 * pg0.sc))
                  (BitVec.ofNat 16 (sizeClass pg0.sc))
                · rfl
                · simp only [arm64_norm, hrun]
                · wp_close_fetch_cl
                · rfl
                · simp only [evalAddrMode, extendVal, arm64_norm]
                  exact Prod.ext (congrArg (maddrs.sizeClasses + ·) hPgSxtw.2.1) rfl
                · wp_sep_access_fast
                · bv_omega
                rw [← hRoFocus]
                have hScLe146 : sizeClass pg0.sc ≤ 8191 := (sizeClass_bounds hPgSc48).2.1
                have hMulEq : BitVec.ofNat 32 pIdx * BitVec.ofNat 32 (sizeClass pg0.sc) =
                    BitVec.ofNat 32 (pIdx * sizeClass pg0.sc) := by
                  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, BitVec.toNat_ofNat]
                wp_step
                wp_step
                wp_step
                wp_if_nd hTotLtTrap
                · exfalso
                  have hScZ32 : BitVec.zeroExtend 32 (BitVec.ofNat 16 (sizeClass pg0.sc)) =
                      BitVec.ofNat 32 (sizeClass pg0.sc) := by
                    apply BitVec.eq_of_toNat_eq
                    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
                    rw [Nat.mod_eq_of_lt (by omega : sizeClass pg0.sc < 2 ^ 16)]
                  simp only [arm64_norm, hAnd31_32, hHdrPIdx192] at hTotLtTrap
                  rw [BitVec.zero_add, hScZ32, hMulEq] at hTotLtTrap
                  have hSlt : (BitVec.ofNat 32 tot).slt (BitVec.ofNat 32 (pIdx * sizeClass pg0.sc)) = false := by
                    rw [BitVec.slt, decide_eq_false_iff_not,
                        hToInt32 tot (by omega), hToInt32 (pIdx * sizeClass pg0.sc) (by omega)]
                    omega
                  rw [hSlt] at hTotLtTrap
                  exact absurd hTotLtTrap Bool.false_ne_true
                ·
                  wp_step
                  wp_step
                  wp_step
                  wp_if_nd hTotGeTrap
                  · exfalso
                    have hScZ32 : BitVec.zeroExtend 32 (BitVec.ofNat 16 (sizeClass pg0.sc)) =
                        BitVec.ofNat 32 (sizeClass pg0.sc) := by
                      apply BitVec.eq_of_toNat_eq
                      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
                      rw [Nat.mod_eq_of_lt (by omega : sizeClass pg0.sc < 2 ^ 16)]
                    simp only [arm64_norm, hAnd31_32, hHdrPIdx192] at hTotGeTrap
                    have hSuccMul : (pIdx + 1) * sizeClass pg0.sc =
                        sizeClass pg0.sc + pIdx * sizeClass pg0.sc := by
                      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
                    have hAddEq : BitVec.ofNat 32 (sizeClass pg0.sc) +
                        BitVec.ofNat 32 (pIdx * sizeClass pg0.sc) =
                        BitVec.ofNat 32 ((pIdx + 1) * sizeClass pg0.sc) := by
                      rw [hSuccMul]
                      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
                    rw [BitVec.zero_add, hScZ32, hMulEq, hAddEq] at hTotGeTrap
                    have hHiBound : (pIdx + 1) * sizeClass pg0.sc < 2 ^ 31 := by omega
                    have hSleF : (BitVec.ofNat 32 ((pIdx + 1) * sizeClass pg0.sc)).sle
                        (BitVec.ofNat 32 tot) = false := by
                      rw [BitVec.sle, decide_eq_false_iff_not,
                          hToInt32 ((pIdx + 1) * sizeClass pg0.sc) hHiBound,
                          hToInt32 tot (by omega)]
                      omega
                    rw [hSleF] at hTotGeTrap
                    exact absurd hTotGeTrap Bool.false_ne_true
                  ·
                    have hAt3fc : ∀ s3fc : State,
                        s3fc.pc = b + 0x3fc#64 → s3fc.status = .Running →
                        s3fc.readReg64 (.gpr 0#5) = pg0.metaPtr →
                        s3fc.readReg64 (.gpr 1#5) = BitVec.ofNat 64 pIdx →
                        s3fc.readReg64 (.gpr 3#5) = g.mem →
                        s3fc.readReg64 (.gpr 19#5) = g.metaPtr →
                        s3fc.readReg64 (.gpr 20#5) = pageOf maddrs.ctx →
                        s3fc.sp = s0.sp - 32#64 → MallocngProcPreserved s0 s3fc →
                        s3fc.brk = s0.brk → s3fc.mem.perm = s0.mem.perm → Cs21Preserved s0 s3fc →
                        SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s3fc
                          ((maddrs.ctx ↦ₛ cDeq.toBytes) ∗
                           ((g.metaPtr ↦ₛ gZero.metaBytes) ∗ ByteMap st.masterDom keepAfterMeta bvDeq) ∗
                           (stackFrameAt (s0.sp - 32#64) (32 * (fuel' + 1)) ∗ nfStackSaved s0.sp s0 ∗
                            MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st ∗
                            ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                            MappedSet st.masterDom (OwnedMappedByte st)))
                          (NfFuelPost k (fuel' + 1) γ brkStart bud st s0) (fun _ => ⌜False⌝) := by
                      intro sF hpcF hrunF hx0F hx1F hx3F hx19F hx20F hspF hProcF hbrkF hpermF hcsF
                      rw [hFocusGMem]
                      apply step_str64_fast (b + 0x3fc#64) (b + 0x400#64) g.mem 0#64
                      · exact hpcF
                      · exact hrunF
                      · wp_close_fetch_cl
                      · rfl
                      · simp only [evalAddrMode, arm64_norm, hx3F]
                      · rfl
                      · wp_sep_access_fast
                      · bv_omega
                      intro mF hmF _
                      rw [hWriteGMem]
                      wp_step
                      let pg1 : GroupDesc := { pg0 with slots := pg0.slots.set pIdx .claimed }
                      let gs1 := replaceGroupByMeta gsDeq pg0.metaPtr pg1
                      let bv1 := writeBytesToMap bvDeq g.mem (unpack64 0#64)
                      let st1 : MallocngSt :=
                        { st with
                          ctx := cDeq
                          reservedMetas := g.metaPtr :: st.reservedMetas
                          groups := gs1
                          activeLists := actLists1
                          byteVal := bv1 }
                      have hSub := hRec st1 pg1 pIdx (by dsimp only [pg1]; omega) hKeep1 hFull1
                      refine SepWP.call_subroutine_frame (x := ()) (ret_pc := b + 0x404#64)
                        (F := (g.metaPtr ↦ₛ gZero.metaBytes) ∗ nfStackSaved s0.sp s0)
                        hSub
                        (by simp [arm64_norm])
                        (by simp [arm64_norm, hrunF])
                        (by simpa only [State.spAligned, arm64_norm, hspF] using hspAl0)
                        (by simp [arm64_norm])
                        ?_ ?_ ?_ ?_ ?_
                      · intro R' hm'
                        refine Satisfies.mono ?_ hm'
                        dsimp only [nontrivialFreeFuelPlainSpec]
                        refine Entails.trans ?_ (sepConj_mono_left (Entails.pure_right
                          ⟨by simpa [arm64_norm, hPg1MetaEq] using hx0F,
                           by simpa [arm64_norm] using hx1F,
                           hPg1Mem, hPg1Claimed⟩ (Entails.refl _)))
                        rw [coreStInflightA_eq_nfParts, pure_sepConj_of_true (by simpa [hbrkF] using hWf1)]
                        rw [← hProt1, ← hMap1]
                        dsimp only [NfStaticRest]
                        simp only [arm64_norm, hspF]
                        sep_frame
                      · intro _ _ _ hp; exact not_satisfies_false_sepConj hp
                      · intro _ _ _ _ he; exact not_satisfies_false_sepConj he
                      · intro sfR hpcR hrunR hspR hcsR
                        dsimp only [nontrivialFreeFuelPlainSpec]
                        refine SepWP.of_sepExists_left fun st2 => ?_
                        refine SepWP.with_sat fun ⟨R_sat, hmSat⟩ => ?_
                        have hmPure : sfR.mem ⊨
                            ⌜MallocngProcPreserved sF sfR ∧ sfR.brk = s0.brk ∧
                              sfR.mem.perm = mF.perm ∧ st2.reservedMetas = st1.reservedMetas ∧
                              st2.metaAreas = st1.metaAreas ∧
                              totalLiveCount st2 ≤ totalLiveCount st1 ∧
                              (dynamicRootRegions st2).length ≤ (dynamicRootRegions st1).length ∧
                              Cost.GroupsGrpMono st1.groups st2.groups⌝ ∗
                            (MallocngCoreStInflightA (k + 1) γ maddrs brkStart s0.brk bud.liveCost bud.peakCost st2 ∗
                             stackFrameAt (s0.sp - 32#64) (32 * (fuel' + 1)) ∗ MallocngRoTablesA maddrs ∗
                             NfRetSep st1 st2 (sfR.readReg64 .x0) (sfR.readReg64 .x1) ∗
                             (g.metaPtr ↦ₛ gZero.metaBytes) ∗ nfStackSaved s0.sp s0 ∗ R_sat) := by
                          refine Satisfies.mono ?_ hmSat
                          simp only [arm64_norm, hspF, hbrkF]
                          refine Entails.pure_left fun hP2 => Entails.pure_right ?_ ?_
                          · obtain ⟨⟨p1, p2, p3, p4, p5, p6, p7⟩, hb2, _, hp2, hr2, hma2, hc2, hd2, hg2⟩ := hP2
                            exact ⟨⟨by simpa [arm64_norm] using p1, by simpa [arm64_norm] using p2,
                                    by simpa [arm64_norm] using p3, by simpa [arm64_norm] using p4,
                                    by simpa [arm64_norm] using p5, by simpa [arm64_norm] using p6,
                                    by simpa [arm64_norm] using p7⟩,
                                   hb2, hp2, hr2, hma2, hc2, hd2, hg2⟩
                          · sep_frame
                        rw [satisfies_pure_sepConj] at hmPure
                        obtain ⟨⟨hProc2, hBrk2, hPerm2, hRes2, hMa2, hCnt2, hDynLen2, hGrp2⟩, hmCore2⟩ := hmPure
                        rw [coreStInflightA_eq_nfParts, sepConj_assoc, satisfies_pure_sepConj] at hmCore2
                        have hWf2 := hmCore2.1
                        have hx19R : sfR.readReg64 .x19 = gZero.metaPtr :=
                          hcsR.readReg64_x19.trans (by simpa [arm64_norm] using hx19F)
                        have hx20R : sfR.readReg64 .x20 = pageOf maddrs.ctx :=
                          hcsR.readReg64_x20.trans (by simpa [arm64_norm] using hx20F)
                        wp_step
                        apply SepWP.weaken_pre
                        rotate_left
                        · exact sepWP_nf_freeMeta_224 hb hFuel
                            (st_m := st2) (gZero := gZero)
                            (by simp [arm64_norm]) (by simp [arm64_norm, hrunR])
                            (by simpa [arm64_norm] using hx19R)
                            (by simpa [arm64_norm] using hx20R)
                            (by rw [hRes2]; exact hmRes1)
                            (by simpa [arm64_norm, hspF] using hspR) hspAl0
                            (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProcF
                                obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hProc2
                                exact ⟨g1.trans f1, g2.trans f2, g3.trans f3, g4.trans f4, g5.trans f5, g6.trans f6, g7.trans f7⟩)
                            (by simpa [arm64_norm] using hBrk2)
                            (by simpa [arm64_norm] using (hPerm2.trans (hmF.trans hpermF)))
                            (by obtain ⟨d21, d22, d23, d24, d25, d26, d27, d28, dv⟩ := hcsF
                                exact ⟨by simpa [arm64_norm] using (hcsR.readReg64_x21.trans (by simpa [arm64_norm] using d21)),
                                       by simpa [arm64_norm] using (hcsR.readReg64_x22.trans (by simpa [arm64_norm] using d22)),
                                       by simpa [arm64_norm] using (hcsR.readReg64_x23.trans (by simpa [arm64_norm] using d23)),
                                       by simpa [arm64_norm] using (hcsR.readReg64_x24.trans (by simpa [arm64_norm] using d24)),
                                       by simpa [arm64_norm] using (hcsR.readReg64_x25.trans (by simpa [arm64_norm] using d25)),
                                       by simpa [arm64_norm] using (hcsR.readReg64_x26.trans (by simpa [arm64_norm] using d26)),
                                       by simpa [arm64_norm] using (hcsR.readReg64_x27.trans (by simpa [arm64_norm] using d27)),
                                       by simpa [arm64_norm] using (hcsR.readReg64_x28.trans (by simpa [arm64_norm] using d28)),
                                       by simpa [calleeSavedVRegs] using (hcsR.vregs.trans (by simpa [calleeSavedVRegs] using dv))⟩)
                            hWf2
                            (by rw [hRes2]; exact hResErase1)
                            hMa2
                            (Nat.le_trans hCnt2 (Nat.le_of_eq hCnt1))
                            (by rw [hDyn1] at hDynLen2; exact hDynLen2)
                            ((Cost.DequeueOutcome.groupsGrpMono hDeq).trans
                              ((Cost.groupsGrpMono_replaceGroupByMeta (g1 := pg1) hPgDeq pg0.metaPtr rfl rfl).trans hGrp2))
                        · have hRetEq :
                              NfRetSep st1 st2 (sfR.readReg64 (.gpr 0#5)) (sfR.readReg64 (.gpr 1#5)) =
                              NfRetSep st st2 (sfR.readReg64 (.gpr 0#5)) (sfR.readReg64 (.gpr 1#5)) :=
                            nfRetSep_congr_left (st2 := st2)
                              (sfR.readReg64 (.gpr 0#5)) (sfR.readReg64 (.gpr 1#5)) hDyn1
                          simp only [arm64_norm, hspF, hbrkF]
                          rw [coreStInflightA_eq_nfParts, pure_sepConj_of_true hWf2, hRetEq, ← hGZeroMeta]
                          try rw [sepConj_assoc]
                          refine Entails.pure_left fun _ => ?_
                          sep_frame
                      · intro _ _ _ ho
                        dsimp only [nontrivialFreeFuelPlainSpec, Spec.onOom] at ho
                        exact False.elim (not_satisfies_false_sepConj ho)
                    rw [hFocusPgCells]
                    apply step_ldr64_fast (b + 0x3dc#64) (b + 0x3e0#64)
                      (pg0.metaPtr + 32#64) pg0.packedWord
                    · simp only [arm64_norm]
                    · simp only [arm64_norm, hrun]
                    · wp_close_fetch_cl
                    · rfl
                    · simp only [evalAddrMode, arm64_norm]
                    · wp_sep_access_fast
                    · bv_omega
                    rw [← hFocusPgCells]
                    have hPgMapMaskNeg : pg0.packedWord &&& (-4096#64) =
                        BitVec.ofNat 64 (pg0.maplen * 4096) := by
                      rw [show (-4096#64 : BitVec 64) = 0xfffffffffffff000#64 by decide]
                      exact hPgMapMask
                    wp_step
                    wp_step
                    wp_if_nd hPgMapZero
                    · exact hAt3fc _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
                        (by simp [arm64_norm]) (by simpa [arm64_norm, hMask192_64] using hPIdxZ64)
                        (by simp [arm64_norm]) (by simpa [arm64_norm] using hx19)
                        (by simp [arm64_norm]) (by simpa [arm64_norm] using hsp)
                        (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
                        (by simpa [arm64_norm] using hbrk) (by simpa [arm64_norm] using hperm)
                        (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
                            exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                                   by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                                   by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                                   by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                                   by simpa [calleeSavedVRegs] using cv⟩)
                    ·
                      have hPgMpPos : 0 < pg0.maplen := by
                        cases hM : pg0.maplen with
                        | zero =>
                          exfalso
                          simp [hM] at hPgMapZero
                        | succ _ => omega
                      obtain ⟨_, hPgLe64k, hPg256Ge1, hTotLeMp⟩ := hPgMapPosProps hPgMpPos
                      wp_step
                      wp_step
                      wp_step
                      wp_step
                      wp_step
                      wp_if_nd hLoTrap
                      · exfalso
                        have hTotSx : (BitVec.ofNat 32 tot).signExtend 64 = BitVec.ofNat 64 tot := by
                          have hMsbF : (BitVec.ofNat 32 tot).msb = false := by
                            rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt (by omega : tot < 2 ^ 32)]
                            omega
                          apply BitVec.eq_of_toNat_eq
                          rw [BitVec.toNat_signExtend, hMsbF]
                          simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                            Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
                          rw [Nat.mod_eq_of_lt (by omega : tot < 2 ^ 32)]
                        have hLsrEq : (BitVec.ofNat 64 (pg0.maplen * 4096) >>> 4) - 1#64 =
                            BitVec.ofNat 64 (pg0.maplen * 256 - 1) := by
                          apply BitVec.eq_of_toNat_eq
                          have h4096 : (BitVec.ofNat 64 (pg0.maplen * 4096)).toNat = pg0.maplen * 4096 := by
                            simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                          have hSh : (BitVec.ofNat 64 (pg0.maplen * 4096) >>> 4).toNat = pg0.maplen * 256 := by
                            rw [BitVec.toNat_ushiftRight, h4096, Nat.shiftRight_eq_div_pow]; omega
                          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1 ≤ (BitVec.ofNat 64 (pg0.maplen * 4096) >>> 4).toNat; omega), hSh]
                          simp only [BitVec.toNat_ofNat]
                          rw [Nat.mod_eq_of_lt (by omega : pg0.maplen * 256 - 1 < 2 ^ 64)]
                        rw [hLsrEq, hTotSx] at hLoTrap
                        have hUltF : (BitVec.ofNat 64 (pg0.maplen * 256 - 1)).ult (BitVec.ofNat 64 tot) = false := by
                          rw [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
                          change ¬ ((pg0.maplen * 256 - 1) % 2 ^ 64 < tot % 2 ^ 64)
                          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
                        rw [hUltF] at hLoTrap
                        exact absurd hLoTrap Bool.false_ne_true
                      · exact hAt3fc _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
                          (by simp [arm64_norm]) (by simpa [arm64_norm, hMask192_64] using hPIdxZ64)
                          (by simp [arm64_norm]) (by simpa [arm64_norm] using hx19)
                          (by simp [arm64_norm]) (by simpa [arm64_norm] using hsp)
                          (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
                          (by simpa [arm64_norm] using hbrk) (by simpa [arm64_norm] using hperm)
                          (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
                              exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                                     by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                                     by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                                     by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                                     by simpa [calleeSavedVRegs] using cv⟩)

end VerifiedLibraries.Mallocng.Proofs
