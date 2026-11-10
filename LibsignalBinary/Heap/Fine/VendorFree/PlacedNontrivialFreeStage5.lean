/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.VendorFree.PlacedNontrivialFreeStage4

/-!
# Placed `nontrivial_free` Stage 5: Root Retirement and All-Free Entry Dispatch

Root-group retirement (`sepWP_nf_retire_root`), all-free entry dispatch (`sepWP_nf_allFree_to_1d4`),
and the fuel-indexed plain contract `nontrivialFreeFuelPlainSpec` for self-recursive
`nontrivial_free`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Heap.Fine.VendorFree
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic Obj VerifiedLibraries.Mallocng

@[expose] public section

/-! ## Load, Context-Secret Focus, and Bitfield Helpers -/

theorem step_ldr32_fast {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (pc pc' : BitVec 64) {rt : Reg} {addr : AddrMode}
    (ea : BitVec 64) (v : BitVec 32)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .W32 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, none))
    (hload : SepLoad32 ea P v)
    (hpc' : pc + 4#64 = pc')
    (hnext : SepWP prog target_pc ((s.writeReg .W32 rt (v.zeroExtend 64)).setPC pc') P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldr32 hpc hrun hfetch hsp haddr hload
    (by dsimp only [applyWriteback]; exact congrArg ((s.writeReg .W32 rt (v.zeroExtend 64)).setPC ·) hpc')
    hnext

theorem ctx_focus_secret (ctx : BitVec 64) (c : CtxFields) :
    ∃ Rest : SepProp, (ctx ↦ₛ c.toBytes) = ((ctx ↦₆₄ c.secret) ∗ Rest) := by
  unfold CtxFields.toBytes
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
  exact ⟨_, rfl⟩

theorem packedWord_bit5_and_low5 (g : GroupDesc) (hLast : g.lastIdx ≤ 31) :
    ((g.packedWord.truncate 8).zeroExtend 64).getLsbD 5 = true ∧
    ((g.packedWord.truncate 8).zeroExtend 32).getLsbD 5 = true ∧
    (((g.packedWord.truncate 8).zeroExtend 64) &&& 0x1f#64 = BitVec.ofNat 64 g.lastIdx) := by
  have h5 := (packedWord_bit5_true g).1
  have h5a : ((g.packedWord.truncate 8).zeroExtend 64).getLsbD 5 = true := by
    have hEq : (g.packedWord.truncate 8).zeroExtend 64 =
        ((g.packedWord.extractLsb' 0 8).zeroExtend 32).zeroExtend 64 := by bv_robdd
    rw [hEq]; revert h5; bv_robdd
  have h5b : ((g.packedWord.truncate 8).zeroExtend 32).getLsbD 5 = true := by
    have hEq : (g.packedWord.truncate 8).zeroExtend 32 =
        (g.packedWord.extractLsb' 0 8).zeroExtend 32 := by bv_robdd
    rw [hEq]; exact h5
  have hLow : ((g.packedWord.truncate 8).zeroExtend 64) &&& 0x1f#64 = BitVec.ofNat 64 g.lastIdx := by
    unfold GroupDesc.packedWord
    have h1 : ∀ a b c : BitVec 64,
        ((((a &&& 0x1f#64) ||| (1#64 <<< 5) ||| ((b &&& 0x3f#64) <<< 6) ||| (c <<< 12)).truncate 8).zeroExtend 64) &&& 0x1f#64 =
          a &&& 0x1f#64 := by intro a b c; bv_robdd
    rw [h1]
    have hL : (BitVec.ofNat 64 g.lastIdx).ult 32#64 = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change g.lastIdx % 2 ^ 64 < 32; omega
    revert hL; bv_robdd
  exact ⟨h5a, h5b, hLow⟩

theorem sc48_sxtw_props :
    ∀ s : Fin 48,
      ((BitVec.ofNat 64 s.val).truncate 32).signExtend 64 = BitVec.ofNat 64 s.val ∧
      (((BitVec.ofNat 64 s.val).truncate 32).signExtend 64) <<< 1 = BitVec.ofNat 64 (2 * s.val) ∧
      ((BitVec.ofNat 64 s.val).truncate 32).ule 0x2f#32 = true := by
  decide

theorem fin32_sle_of_le :
    ∀ a b : Fin 32, a.val ≤ b.val → (BitVec.ofNat 32 a.val).sle (BitVec.ofNat 32 b.val) = true := by
  decide

/-! ## Root-Group Retirement -/

private theorem sepWP_nf_zero_uSeq_2e8 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b)
    {target_pc : BitVec 64} {s : State} {R : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {p endPtr : BitVec 64} (bs : List (BitVec 8))
    (hpc : s.pc = b + 0x2e8#64) (hrun : s.status = .Running)
    (hx1 : s.readReg64 (.gpr 1#5) = p)
    (hx2 : s.readReg64 (.gpr 2#5) = endPtr)
    (hNeNil : bs ≠ []) (hLenLe : bs.length ≤ 32)
    (hEnd : p + BitVec.ofNat 64 bs.length = endPtr)
    (hnext : ∀ s' : State,
      s'.pc = b + 0x2f4#64 → s'.status = .Running →
      s'.readReg64 (.gpr 0#5) = s.readReg64 (.gpr 0#5) →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.sp = s.sp → MallocngProcPreserved s s' → s'.brk = s.brk →
      s'.mem.perm = s.mem.perm → Cs21Preserved s s' →
      SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s'
        ((p ↦ₛ List.replicate bs.length 0#8) ∗ R) post oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s ((p ↦ₛ bs) ∗ R) post oom := by
  have _ := hb
  induction bs generalizing s p R with
  | nil => exact False.elim (hNeNil rfl)
  | cons b0 tl ih =>
    rw [pointsToBytes_cons]
    apply step_str8_wb_fast (b + 0x2e8#64) (b + 0x2ec#64) p (p + 1#64) (.gpr 1#5) 0#8
    · exact hpc
    · exact hrun
    · wp_close_fetch_cl
    · rfl
    · simp only [evalAddrMode, arm64_norm, hx1]
    · rfl
    · wp_sep_access_fast
    · bv_omega
    intro m1 hm1 _
    cases tl with
    | nil =>
      have hP1 : p + 1#64 = endPtr := by simpa using hEnd
      wp_step; wp_step; rw [← pointsToBytes_cons]
      exact hnext _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (by simp [arm64_norm]) hm1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [calleeSavedVRegs]⟩
    | cons b1 tl2 =>
      simp only [List.length_cons] at hLenLe hEnd
      have hNeEnd : endPtr ≠ p + 1#64 := by
        intro hEq
        have hSub : (p + BitVec.ofNat 64 (tl2.length + 1 + 1)) - p = (p + 1#64) - p :=
          congrArg (· - p) (hEnd.trans hEq)
        have hCan : ∀ x y : BitVec 64, (x + y) - x = y := by intro x y; bv_robdd
        rw [hCan, hCan] at hSub
        have hN := congrArg BitVec.toNat hSub
        simp only [BitVec.toNat_ofNat] at hN
        change (tl2.length + 1 + 1) % 2 ^ 64 = 1 at hN
        rw [Nat.mod_eq_of_lt (by omega)] at hN; omega
      wp_step; wp_step
      have hIn : (((p ↦₈ 0#8) ∗ ((p + 1#64) ↦ₛ (b1 :: tl2))) ∗ R) =
          (((p + 1#64) ↦ₛ (b1 :: tl2)) ∗ ((p ↦₈ 0#8) ∗ R)) := by ac_rfl
      rw [hIn]
      refine ih (p := p + 1#64) (R := (p ↦₈ 0#8) ∗ R) (by simp [arm64_norm, hNeEnd])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
        (by simpa only [arm64_norm] using hx2) (by simp) (by simp; omega) ?_ ?_
      · simp only [List.length_cons]
        exact (by rw [BitVec.add_assoc]; congr 1; bv_omega :
          (p + 1#64) + BitVec.ofNat 64 (tl2.length + 1) = p + BitVec.ofNat 64 (tl2.length + 1 + 1)).trans hEnd
      · intro s' hpc' hrun' hx0' hx19' hx20' hsp' hProc' hbrk' hperm' hcs'
        have hOut : (((p + 1#64) ↦ₛ List.replicate (b1 :: tl2).length 0#8) ∗ ((p ↦₈ 0#8) ∗ R)) =
            ((p ↦ₛ List.replicate (b0 :: b1 :: tl2).length 0#8) ∗ R) := by
          simp only [List.length_cons, List.replicate_succ, pointsToBytes_cons]; ac_rfl
        rw [hOut]
        exact hnext s' hpc' hrun' (hx0'.trans (by simp [arm64_norm]))
          (hx19'.trans (by simp [arm64_norm])) (hx20'.trans (by simp [arm64_norm]))
          (hsp'.trans (by simp [arm64_norm]))
          (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc'; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
          (hbrk'.trans (by simp [arm64_norm])) (hperm'.trans hm1)
          (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs'
              exact ⟨c21.trans (by simp [arm64_norm]), c22.trans (by simp [arm64_norm]),
                     c23.trans (by simp [arm64_norm]), c24.trans (by simp [arm64_norm]),
                     c25.trans (by simp [arm64_norm]), c26.trans (by simp [arm64_norm]),
                     c27.trans (by simp [arm64_norm]), c28.trans (by simp [arm64_norm]),
                     cv.trans (by simp [calleeSavedVRegs])⟩)

set_option maxHeartbeats 500000 in
theorem sepWP_nf_retire_root [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {bud : MallocngBudget}
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {active1 usage1 : List (BitVec 64)} {actLists1 : List (List (BitVec 64))}
    {gsDeq : List GroupDesc} {bvDeq : BitVec 64 → BitVec 8}
    {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x1d4#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 g.sc)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hAllFree : (g.availMask ||| g.freedMask) + (1#32 <<< idx) = (2#32 <<< g.lastIdx) - 1#32)
    (hMpPos : 0 < g.maplen)
    (hDeq : DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      ((maddrs.ctx ↦ₛ { st.ctx with active := active1, usageByClass := usage1 }.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) bvDeq ∗
       NfAllFreeFrame fuel γ st s0)
      (NfFuelPost k fuel γ brkStart bud st s0) oom := by
  have _ := hb
  have hCtx20 : pageOf maddrs.ctx + lo12Of maddrs.ctx = maddrs.ctx := pageOf_add_lo12Of maddrs.ctx
  have hCtxU : pageOf (maddrs.ctx + 848#64) + lo12Of (maddrs.ctx + 848#64) = maddrs.ctx + 848#64 :=
    pageOf_add_lo12Of (maddrs.ctx + 848#64)
  let gZero : GroupDesc := { g with prev := 0#64, next := 0#64 }
  let cDeq : CtxFields := { st.ctx with active := active1, usageByClass := usage1 }
  obtain ⟨_, _, _, _, hOwnG⟩ := meta_ownedRw_of_mem_groups hwf hg
  have hBmG := (byteMap_update40 hwf.masterDom_wf.1 bvDeq (P := OwnedRwByte st)
    (m := g.metaPtr) (bs := gZero.metaBytes) (GroupDesc.metaBytes_length _) hOwnG).1
  have hPw : gZero.packedWord = g.packedWord := rfl
  rw [hBmG, hDeq.g_zero_bytes, metaBytes_eq_cells gZero, hPw]
  apply step_ldr64_fast (b + 0x1d4#64) (b + 0x1d8#64) (g.metaPtr + 32#64) g.packedWord
  · exact hpc
  · exact hrun
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, arm64_norm, hx19]
  · wp_sep_access_fast
  · bv_omega
  rw [← hPw, ← metaBytes_eq_cells gZero, ← hDeq.g_zero_bytes, ← hBmG]
  have hMpNe0 : g.packedWord &&& -4096#64 ≠ 0#64 := by
    rw [packedWord_and_neg4096 g]
    intro hZ
    have hN := congrArg BitVec.toNat hZ
    have hTotFit := (hwf.groups_wf g hg).2.2.2.2.2.2.1
    simp only [GroupDesc.totalBytes, hMpPos, ↓reduceIte] at hTotFit
    simp only [BitVec.toNat_ofNat] at hN
    change (g.maplen * 4096) % 2 ^ 64 = 0 at hN
    rw [Nat.mod_eq_of_lt (by omega)] at hN; omega
  wp_step
  wp_step
  wp_if_nd hEqZero
  · exfalso
    have hZ : g.packedWord &&& -4096#64 = 0#64 := by simpa [arm64_norm] using hEqZero
    exact hMpNe0 hZ
  ·
    wp_step
    wp_step
    obtain ⟨SeqRest, hSeqRead, hSeqWrite⟩ :=
      ctx_focus_update_seq maddrs.ctx cDeq hDeq.lens.1 hDeq.lens.2.1
        hwf.ctx_lens.2.2.1 hwf.ctx_lens.2.2.2.1 (st.ctx.seq + 1#8)
    change SepWP _ _ _ ((maddrs.ctx ↦ₛ cDeq.toBytes) ∗ _ ∗ _) _ _
    rw [hSeqRead]
    apply step_ldr8_fast (b + 0x1e8#64) (b + 0x1ec#64) (maddrs.ctx + 912#64) st.ctx.seq
    · rfl
    · simp only [arm64_norm, hrun]
    · wp_close_fetch_cl
    · rfl
    · simp only [evalAddrMode, arm64_norm]
    · wp_sep_access_fast
    · bv_omega
    wp_step
    wp_step
    wp_if_nd _hSeq255
    · -- `seq = 255`: zero `unmapSeq` (`32` bytes), reset `seq := 1`, and jump to `+0x1fc`
      rw [← hSeqRead]
      wp_step
      wp_step
      wp_step
      obtain ⟨USliceRest, hUSliceRead, hUSliceWrite⟩ :=
        ctx_focus_update_unmapSeq_slice maddrs.ctx cDeq hDeq.lens.1 hDeq.lens.2.1
          hwf.ctx_lens.2.2.1 (List.replicate 32 0#8) (by simp)
      rw [hUSliceRead]
      have hAssocIn :
          ((((maddrs.ctx + 848#64) ↦ₛ cDeq.unmapSeq) ∗ USliceRest) ∗
           ByteMap st.masterDom (OwnedRwByte st) bvDeq ∗ NfAllFreeFrame fuel γ st s0) =
          (((maddrs.ctx + 848#64) ↦ₛ st.ctx.unmapSeq) ∗
           (USliceRest ∗ ByteMap st.masterDom (OwnedRwByte st) bvDeq ∗ NfAllFreeFrame fuel γ st s0)) := by
        dsimp only [cDeq]; ac_rfl
      rw [hAssocIn]
      refine sepWP_nf_zero_uSeq_2e8 hb st.ctx.unmapSeq
        (p := maddrs.ctx + 848#64) (endPtr := maddrs.ctx + 880#64)
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by intro hNil; have := hwf.ctx_lens.2.2.1; simp [hNil] at this)
        (by rw [hwf.ctx_lens.2.2.1]; exact Nat.le_refl 32)
        (by rw [hwf.ctx_lens.2.2.1, BitVec.add_assoc]; congr 1) ?_
      intro sZ hpcZ hrunZ hx0Z hx19Z hx20Z hspZ hProcZ hbrkZ hpermZ hcsZ
      rw [hwf.ctx_lens.2.2.1]
      have hFoldU :
          (((maddrs.ctx + 848#64) ↦ₛ List.replicate 32 0#8) ∗
           (USliceRest ∗ ByteMap st.masterDom (OwnedRwByte st) bvDeq ∗ NfAllFreeFrame fuel γ st s0)) =
          ((((maddrs.ctx + 848#64) ↦ₛ List.replicate 32 0#8) ∗ USliceRest) ∗
           ByteMap st.masterDom (OwnedRwByte st) bvDeq ∗ NfAllFreeFrame fuel γ st s0) := by
        ac_rfl
      rw [hFoldU, hUSliceWrite]
      have hx20Z' : sZ.readReg64 (.gpr 20#5) = pageOf maddrs.ctx :=
        hx20Z.trans (by simp [arm64_norm])
      let cZeroU : CtxFields := { cDeq with unmapSeq := List.replicate 32 0#8 }
      wp_step
      wp_step
      obtain ⟨SeqRest1, hSeqRead1, hSeqWrite1⟩ :=
        ctx_focus_update_seq maddrs.ctx cZeroU hDeq.lens.1 hDeq.lens.2.1
          (by simp [cZeroU]) hwf.ctx_lens.2.2.2.1 1#8
      change SepWP _ _ _ ((maddrs.ctx ↦ₛ cZeroU.toBytes) ∗ _ ∗ _) _ _
      rw [hSeqRead1]
      apply step_str8_fast (b + 0x2fc#64) (b + 0x300#64) (maddrs.ctx + 912#64) 1#8
      · rfl
      · simp only [arm64_norm, hrunZ]
      · wp_close_fetch_cl
      · rfl
      · simp only [evalAddrMode, arm64_norm]
      · rfl
      · wp_sep_access_fast
      · bv_omega
      intro m1 hm1 _
      rw [hSeqWrite1]
      wp_step
      apply SepWP.weaken_pre
      rotate_left
      · exact sepWP_nf_retire_root_from_1fc hb hFuel
          (seq1 := 1#8) (uSeqMid := List.replicate 32 0#8)
          (by simp [arm64_norm]) (by simp [arm64_norm, hrunZ])
          (by simpa [arm64_norm] using hx0Z.trans (by simpa [arm64_norm] using hx0))
          (by simpa [arm64_norm] using hx19Z.trans (by simpa [arm64_norm] using hx19))
          (by simpa [arm64_norm] using hx20Z')
          (by simpa [arm64_norm] using hspZ.trans (by simpa [arm64_norm] using hsp)) hspAl0
          (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc
              obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hProcZ
              exact ⟨g1.trans f1, g2.trans f2, g3.trans f3, g4.trans f4, g5.trans f5, g6.trans f6, g7.trans f7⟩)
          (by simpa [arm64_norm] using hbrkZ.trans (by simpa [arm64_norm] using hbrk))
          (hm1.trans (hpermZ.trans (by simpa [arm64_norm] using hperm)))
          (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
              obtain ⟨d21, d22, d23, d24, d25, d26, d27, d28, dv⟩ := hcsZ
              exact ⟨by simpa [arm64_norm] using (d21.trans (by simpa [arm64_norm] using c21)),
                     by simpa [arm64_norm] using (d22.trans (by simpa [arm64_norm] using c22)),
                     by simpa [arm64_norm] using (d23.trans (by simpa [arm64_norm] using c23)),
                     by simpa [arm64_norm] using (d24.trans (by simpa [arm64_norm] using c24)),
                     by simpa [arm64_norm] using (d25.trans (by simpa [arm64_norm] using c25)),
                     by simpa [arm64_norm] using (d26.trans (by simpa [arm64_norm] using c26)),
                     by simpa [arm64_norm] using (d27.trans (by simpa [arm64_norm] using c27)),
                     by simpa [arm64_norm] using (d28.trans (by simpa [arm64_norm] using c28)),
                     by simpa [calleeSavedVRegs] using (dv.trans (by simpa [calleeSavedVRegs] using cv))⟩)
          hwf hg hIdx hClaimed hAllFree hMpPos hDeq (by simp)
      · dsimp only [NfAllFreeFrame, cZeroU, cDeq]
        sep_frame
    · -- `seq ≠ 255`: increment `seq` and fall through to `+0x1fc`
      wp_step
      apply step_str8_fast (b + 0x1f8#64) (b + 0x1fc#64) (maddrs.ctx + 912#64) (st.ctx.seq + 1#8)
      · rfl
      · simp only [arm64_norm, hrun]
      · wp_close_fetch_cl
      · rfl
      · simp only [evalAddrMode, arm64_norm]
      · simp only [arm64_norm]
      · wp_sep_access_fast
      · bv_omega
      intro m1 hm1 _
      rw [hSeqWrite]
      apply SepWP.weaken_pre
      rotate_left
      · exact sepWP_nf_retire_root_from_1fc hb hFuel
          (seq1 := st.ctx.seq + 1#8) (uSeqMid := st.ctx.unmapSeq)
          (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
          (by simpa [arm64_norm] using hx0) (by simpa [arm64_norm] using hx19)
          (by simp [arm64_norm]) (by simpa [arm64_norm] using hsp) hspAl0
          (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
          (by simpa [arm64_norm] using hbrk) (hm1.trans (by simpa [arm64_norm] using hperm))
          (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
              exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                     by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                     by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                     by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                     by simpa [calleeSavedVRegs] using cv⟩)
          hwf hg hIdx hClaimed hAllFree hMpPos hDeq hwf.ctx_lens.2.2.1
      · dsimp only [NfAllFreeFrame, cDeq]
        sep_frame

/-! ## All-Free Entry Dispatch -/

set_option maxHeartbeats 500000 in
theorem sepWP_nf_allFree_to_1d4 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {bud : MallocngBudget}
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x68#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 g.sc)
    (hw1 : s.readReg32 (.gpr 1#5) = 1#32 <<< idx)
    (_hw3 : s.readReg32 (.gpr 3#5) = g.availMask ||| g.freedMask)
    (hw6 : s.readReg32 (.gpr 6#5) = BitVec.ofNat 32 g.lastIdx)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st)
    (hKeep : EmptyGroupKeepWf st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hCont : NfDeqCont b (s0.readReg64 .lr) st g (NfAllFreeFrame fuel γ st s0) s0 s
      (NfFuelPost k fuel γ brkStart bud st s0) oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       NfAllFreeFrame fuel γ st s0)
      (NfFuelPost k fuel γ brkStart bud st s0) oom := by
  have _ := hb
  have hLast31 : g.lastIdx ≤ 31 := (hwf.groups_wf g hg).2.1
  obtain ⟨_hBit5_64, _hBit5_32, _hLow5⟩ := packedWord_bit5_and_low5 g hLast31
  obtain ⟨_, _, _, hReadG, hOwnG⟩ := meta_ownedRw_of_mem_groups hwf hg
  have hBmG0 := (byteMap_update40 hwf.masterDom_wf.1 st.byteVal (P := OwnedRwByte st)
    (m := g.metaPtr) (bs := g.metaBytes) (GroupDesc.metaBytes_length _) hOwnG).1
  rw [hBmG0, hReadG, metaBytes_eq_cells g]
  apply step_ldr8_64_fast (b + 0x68#64) (b + 0x6c#64) (g.metaPtr + 32#64) g.packedWord
  · exact hpc
  · exact hrun
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, arm64_norm, hx19]
  · wp_sep_access_fast
  · bv_omega
  -- Bit 5 (`freeable`) of `g.packedWord` is always `1` on an active mallocng group.
  wp_step
  · rcases (hwf.groups_wf g hg).1 with hSc48 | hSc63
    ·
      have hScProps := sc_cmp47_and_active_off_fin ⟨g.sc, hSc48⟩
      have hSxtw := sc48_sxtw_props ⟨g.sc, hSc48⟩
      wp_step
      apply step_ldr64_fast (b + 0x74#64) (b + 0x78#64) (g.metaPtr + 8#64) g.next
      · rfl
      · simp only [arm64_norm, hrun]
      · wp_close_fetch_cl
      · rfl
      · simp only [evalAddrMode, arm64_norm, hx19]
      · wp_sep_access_fast
      · bv_omega
      wp_step
      wp_if_nd hGt47
      · exfalso
        have hSle := hScProps.1
        dsimp only at hSle
        revert hSle hGt47; bv_robdd
      ·
        apply step_ldr64_fast (b + 0x7c#64) (b + 0x80#64) (g.metaPtr + 32#64) g.packedWord
        · rfl
        · simp only [arm64_norm, hrun]
        · wp_close_fetch_cl
        · rfl
        · simp only [evalAddrMode, arm64_norm, hx19]
        · wp_sep_access_fast
        · bv_omega
        rw [← metaBytes_eq_cells g, ← hReadG, ← hBmG0]
        wp_step
        wp_step
        wp_step
        wp_if_nd hCntNe0
        ·
          have hLastNe0 : g.lastIdx ≠ 0 := by
            intro hZ
            simp [arm64_norm, hZ] at hCntNe0
          wp_step
          wp_step
          wp_if_nd hMapZ
          · exact sepWP_nf_at_0b8 hb (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
              hwf hg hSc48
              (by simpa [arm64_norm] using hx0) (by simp [arm64_norm])
              (by simpa [arm64_norm] using hw6) (by simp [arm64_norm])
              (by simpa [arm64_norm] using hx19)
              (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
              (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
                  exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                         by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                         by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                         by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                         by simpa [calleeSavedVRegs] using cv⟩)
              (fun a1 u1 al1 gd1 bd1 s' hD hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
                hCont a1 u1 al1 gd1 bd1 s' hD hpc' hrun' hx0' hx19'
                  (hsp'.trans (by simp [arm64_norm]))
                  (hbrk'.trans (by simp [arm64_norm]))
                  (hperm'.trans (by simp [arm64_norm])) hProc' hcs')
          · have hMpPos : 0 < g.maplen := by
              cases hMp : g.maplen with
              | zero =>
                exfalso
                have hZ0 : g.packedWord &&& (-4096#64) = 0#64 := by
                  rw [packedWord_and_neg4096 g, hMp]
                rw [hZ0] at hMapZ; simp at hMapZ
              | succ _ => omega
            exact sepWP_nf_at_0e4 hb hFuel (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
              (by simpa [arm64_norm] using hx0) (by simpa [arm64_norm] using hw1)
              (by simp [arm64_norm]) (by simpa [arm64_norm] using hw6)
              (by simp [arm64_norm]) (by simpa [arm64_norm] using hx19)
              (by simpa [arm64_norm] using hsp) hspAl0
              (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
              (by simpa [arm64_norm] using hbrk) (by simpa [arm64_norm] using hperm)
              (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
                  exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                         by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                         by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                         by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                         by simpa [calleeSavedVRegs] using cv⟩)
              hwf hKeep hg hIdx hClaimed hSc48 hMpPos (fun hZ => False.elim (hLastNe0 hZ))
              (fun a1 u1 al1 gd1 bd1 s' hD hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
                hCont a1 u1 al1 gd1 bd1 s' hD hpc' hrun' hx0' hx19'
                  (hsp'.trans (by simp [arm64_norm]))
                  (hbrk'.trans (by simp [arm64_norm]))
                  (hperm'.trans (by simp [arm64_norm])) hProc' hcs')
        ·
          wp_step
          wp_step
          wp_if_nd hMapZ
          · exact sepWP_nf_at_0b8 hb (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
              hwf hg hSc48
              (by simpa [arm64_norm] using hx0) (by simp [arm64_norm])
              (by simpa [arm64_norm] using hw6) (by simp [arm64_norm])
              (by simpa [arm64_norm] using hx19)
              (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
              (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
                  exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                         by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                         by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                         by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                         by simpa [calleeSavedVRegs] using cv⟩)
              (fun a1 u1 al1 gd1 bd1 s' hD hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
                hCont a1 u1 al1 gd1 bd1 s' hD hpc' hrun' hx0' hx19'
                  (hsp'.trans (by simp [arm64_norm]))
                  (hbrk'.trans (by simp [arm64_norm]))
                  (hperm'.trans (by simp [arm64_norm])) hProc' hcs')
          · have hMpPos : 0 < g.maplen := by
              cases hMp : g.maplen with
              | zero =>
                exfalso
                have hZ0 : g.packedWord &&& (-4096#64) = 0#64 := by
                  rw [packedWord_and_neg4096 g, hMp]
                rw [hZ0] at hMapZ; simp at hMapZ
              | succ _ => omega
            wp_step
            wp_step
            wp_step
            wp_step
            obtain ⟨RoRest, hRoFocus⟩ := roTables_focus_sizeClass maddrs hSc48
            dsimp only [NfAllFreeFrame]
            rw [hRoFocus]
            apply step_ldr16_fast (b + 0xa8#64) (b + 0xac#64)
              (maddrs.sizeClasses + BitVec.ofNat 64 (2 * g.sc))
              (BitVec.ofNat 16 (sizeClass g.sc))
            · rfl
            · simp only [arm64_norm, hrun]
            · wp_close_fetch_cl
            · rfl
            · simp only [evalAddrMode, extendVal, arm64_norm]
              rw [hx0]
              exact Prod.ext (congrArg (maddrs.sizeClasses + ·) hSxtw.2.1) rfl
            · wp_sep_access_fast
            · bv_omega
            rw [← hRoFocus]
            change SepWP _ _ _ ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
              ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ NfAllFreeFrame fuel γ st s0) _ _
            wp_step
            wp_step
            wp_step
            wp_if_nd hHsBr
            · have hStrideFit : slotStride g.sc + 16 ≤ g.maplen * 4096 := by
                have hUbf := sizeClass_ubfiz_fin ⟨g.sc, hSc48⟩
                dsimp only at hUbf
                have hPw := packedWord_and_neg4096 g
                have hTotFit := (hwf.groups_wf g hg).2.2.2.2.2.2.1
                simp only [GroupDesc.totalBytes, hMpPos, ↓reduceIte] at hTotFit
                have hStrBd : slotStride g.sc ≤ 131056 := by
                  have := (sizeClass_bounds hSc48).2.1; unfold slotStride; omega
                simp [arm64_norm] at hUbf
                rw [hPw, hUbf, BitVec.ule_iff_toNat_le] at hHsBr
                have hLHS : (BitVec.ofNat 64 (slotStride g.sc)).toNat = slotStride g.sc := by
                  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                have hMpNat : (BitVec.ofNat 64 (g.maplen * 4096)).toNat = g.maplen * 4096 := by
                  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                have hRHS : (BitVec.ofNat 64 (g.maplen * 4096) - 16#64).toNat = g.maplen * 4096 - 16 := by
                  rw [BitVec.toNat_sub_of_le]
                  · rw [hMpNat]; rfl
                  · rw [BitVec.le_def]; change 16 ≤ (BitVec.ofNat 64 (g.maplen * 4096)).toNat; omega
                omega
              exact sepWP_nf_at_0e4 hb hFuel (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
                (by simpa [arm64_norm] using hx0) (by simpa [arm64_norm] using hw1)
                (by simp [arm64_norm]) (by simpa [arm64_norm] using hw6)
                (by simp [arm64_norm]) (by simpa [arm64_norm] using hx19)
                (by simpa [arm64_norm] using hsp) hspAl0
                (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
                (by simpa [arm64_norm] using hbrk) (by simpa [arm64_norm] using hperm)
                (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
                    exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                           by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                           by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                           by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                           by simpa [calleeSavedVRegs] using cv⟩)
                hwf hKeep hg hIdx hClaimed hSc48 hMpPos (fun _ => hStrideFit)
                (fun a1 u1 al1 gd1 bd1 s' hD hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
                  hCont a1 u1 al1 gd1 bd1 s' hD hpc' hrun' hx0' hx19'
                    (hsp'.trans (by simp [arm64_norm]))
                    (hbrk'.trans (by simp [arm64_norm]))
                    (hperm'.trans (by simp [arm64_norm])) hProc' hcs')
            · exact sepWP_nf_at_0b8 hb (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
                hwf hg hSc48
                (by simpa [arm64_norm] using hx0) (by simp [arm64_norm])
                (by simpa [arm64_norm] using hw6) (by simp [arm64_norm])
                (by simpa [arm64_norm] using hx19)
                (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
                (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
                    exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                           by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                           by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                           by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                           by simpa [calleeSavedVRegs] using cv⟩)
                (fun a1 u1 al1 gd1 bd1 s' hD hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
                  hCont a1 u1 al1 gd1 bd1 s' hD hpc' hrun' hx0' hx19'
                    (hsp'.trans (by simp [arm64_norm]))
                    (hbrk'.trans (by simp [arm64_norm]))
                    (hperm'.trans (by simp [arm64_norm])) hProc' hcs')
    · -- `g.sc = 63` (`mmap`-serviced individual allocation)
      obtain ⟨_, hNx0, _, hDeq63⟩ := dequeue_sc63 hwf hg hSc63
      rw [hSc63] at hx0
      wp_step
      rw [hNx0]
      apply step_ldr64_fast (b + 0x74#64) (b + 0x78#64) (g.metaPtr + 8#64) 0#64
      · rfl
      · simp only [arm64_norm, hrun]
      · wp_close_fetch_cl
      · rfl
      · simp only [evalAddrMode, arm64_norm, hx19]
      · wp_sep_access_fast
      · bv_omega
      rw [← hNx0, ← metaBytes_eq_cells g, ← hReadG, ← hBmG0]
      wp_step
      wp_step
      wp_step
      exact hCont st.ctx.active st.ctx.usageByClass st.activeLists
        (filterOutGroup st.groups g.metaPtr) st.byteVal _ hDeq63
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by rw [hSc63]; simpa [arm64_norm] using hx0) (by simpa [arm64_norm] using hx19)
        (by simp [arm64_norm]) (by simp [arm64_norm]) rfl
        (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
        (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
            exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                   by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                   by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                   by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                   by simpa [calleeSavedVRegs] using cv⟩)

/-! ## Fuel-Indexed Plain Contract -/

def nontrivialFreeFuelPlainSpec [MallocngMultiPlacement]
    (k fuel : Nat) (γ : GhostName) (brkStart : BitVec 64) (bud : MallocngBudget)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat) : Spec Unit :=
  { pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = g.metaPtr ∧
       s0.readReg64 .x1 = BitVec.ofNat 64 idx ∧
       g ∈ st.groups ∧
       ∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .claimed⌝ ∗
      stackFrameAt s0.sp (32 * (fuel + 1)) ∗
      MallocngRoTablesA maddrs ∗
      MallocngCoreStInflightA (k + 1) γ maddrs brkStart s0.brk bud.liveCost bud.peakCost st
    post := fun (_ : Unit) s0 sf =>
      ∃∗ st' : MallocngSt,
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧
         sf.mem.perm = s0.mem.perm ∧ st'.reservedMetas = st.reservedMetas ∧
         st'.metaAreas = st.metaAreas ∧
         totalLiveCount st' ≤ totalLiveCount st ∧
         (dynamicRootRegions st').length ≤ (dynamicRootRegions st).length ∧
         Cost.GroupsGrpMono st.groups st'.groups⌝ ∗
        stackFrameAt s0.sp (32 * (fuel + 1)) ∗ MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightA k γ maddrs brkStart s0.brk bud.liveCost bud.peakCost st' ∗
        NfRetSep st st' (sf.readReg64 .x0) (sf.readReg64 .x1) }

end

end LibsignalBinary.Heap.Fine.VendorFree
