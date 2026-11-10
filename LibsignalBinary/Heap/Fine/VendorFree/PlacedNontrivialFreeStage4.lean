/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.VendorFree.PlacedNontrivialFreeStage3

/-!
# Placed `nontrivial_free` Symbolic Execution: Stage 4

Multi-block (`MallocngMultiPlacement`) symbolic execution of `nontrivial_free` (`blk05`) covering
multi-element circular active-queue removal (`sepWP_nf_dequeue_194`) and all-free active-queue
classification with kept-empty singleton exit (`sepWP_nf_at_0b8`, `sepWP_nf_at_0e4`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Heap.Fine.VendorFree
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic Obj VerifiedLibraries.Mallocng

@[expose] public section

/-! ## Multi-Element Active Queue Removal -/

set_option maxHeartbeats 600000 in
theorem sepWP_nf_dequeue_194 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b)
    {inflight : Nat} {brkStart : BitVec 64} {liveCost peakCost : Nat}
    {target_pc : BitVec 64} {st : MallocngSt} {g : GroupDesc}
    {R : SepProp} {s0 s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = b + 0x194#64) (hrun : s.status = .Running)
    (hwf : MallocngWFInflight inflight maddrs.base brkStart s0.brk liveCost peakCost st)
    (hg : g ∈ st.groups) (hSc48 : g.sc < 48)
    (hx0 : s.readReg64 (.gpr 0#5) = st.ctx.active[g.sc]'(by rw [hwf.ctx_lens.1]; exact hSc48))
    (hx4 : s.readReg64 (.gpr 4#5) = g.next)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 g.sc)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = pageOf maddrs.ctx)
    (hProc : MallocngProcPreserved s0 s) (hcs : Cs21Preserved s0 s)
    (hNxNe0 : g.next ≠ 0#64) (hNxNeSelf : g.next ≠ g.metaPtr)
    (hCont : NfDeqCont b target_pc st g R s0 s post oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ R) post oom := by
  have _ := hb
  have hCtx20 : pageOf maddrs.ctx + lo12Of maddrs.ctx = maddrs.ctx := pageOf_add_lo12Of maddrs.ctx
  have hScProps := sc_cmp47_and_active_off_fin ⟨g.sc, hSc48⟩
  have hActAddr : maddrs.ctx + ((BitVec.ofNat 64 g.sc + 10#64) <<< 3) =
      maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc) :=
    congrArg (maddrs.ctx + ·) hScProps.2.2.2.2
  have hActLt : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
  let head := st.ctx.active[g.sc]'hActLt
  obtain ⟨_, _, hOwnG, prevG, hprevG, nextG, hnextG, k, hk,
          _, hPrevPtr, _, hNextPtr, _, hOwnPrev, hOwnNext,
          hReadG_a, hReadNext_a, hReadG_b, hHeadAct, hDeq⟩ :=
    dequeue_multi hwf hg hSc48 hNxNe0 hNxNeSelf
  obtain ⟨_, _, _, hReadG0, _⟩ := meta_ownedRw_of_mem_groups hwf hg
  obtain ⟨_, _, _, hReadPrev0, _⟩ := meta_ownedRw_of_mem_groups hwf hprevG
  obtain ⟨_, hmAlN, hmFitN, _, _⟩ := meta_ownedRw_of_mem_groups hwf hnextG
  have hLast31 : g.lastIdx ≤ 31 := (hwf.groups_wf g hg).2.1
  have hDomNd := hwf.masterDom_wf.1
  let prevUpd : GroupDesc := { prevG with next := g.next }
  let nextPre : GroupDesc :=
    { nextG with next := if nextG.metaPtr == g.prev then g.next else nextG.next }
  let nextMid : GroupDesc := { nextPre with prev := g.prev }
  let gZero : GroupDesc := { g with prev := 0#64, next := 0#64 }
  let bv_a := writeBytesToMap st.byteVal prevG.metaPtr prevUpd.metaBytes
  let bv_b := writeBytesToMap bv_a nextG.metaPtr nextMid.metaBytes
  let bv_c := writeBytesToMap bv_b g.metaPtr gZero.metaBytes
  have hBmG0 := (byteMap_update40 hDomNd st.byteVal (P := OwnedRwByte st)
    (m := g.metaPtr) (bs := g.metaBytes) (GroupDesc.metaBytes_length _) hOwnG).1
  rw [hBmG0, hReadG0, metaBytes_eq_cells g]
  apply step_ldr64_fast (b + 0x194#64) (b + 0x198#64) g.metaPtr g.prev
  · exact hpc
  · exact hrun
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, arm64_norm, hx19]
  · wp_sep_access_fast
  · bv_omega
  rw [← metaBytes_eq_cells g, ← hReadG0, ← hBmG0]
  wp_step
  wp_step
  have ⟨hBmP0, hBmPW⟩ := byteMap_update40 hDomNd st.byteVal (P := OwnedRwByte st)
    (m := prevG.metaPtr) (bs := prevUpd.metaBytes) (GroupDesc.metaBytes_length _) hOwnPrev
  rw [hBmP0, hReadPrev0, metaBytes_eq_cells prevG]
  apply step_str64_fast (b + 0x1a0#64) (b + 0x1a4#64) (prevG.metaPtr + 8#64) g.next
  · rfl
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, arm64_norm, hPrevPtr]
  · simpa only [arm64_norm] using hx4
  · wp_sep_access_fast
  · bv_omega
  intro m1 hm1 _
  have hFoldA :
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       (((prevG.metaPtr ↦₆₄ prevG.prev) ∗ ((prevG.metaPtr + 8#64) ↦₆₄ g.next) ∗
         ((prevG.metaPtr + 16#64) ↦₆₄ prevG.mem) ∗ ((prevG.metaPtr + 24#64) ↦₃₂ prevG.availMask) ∗
         ((prevG.metaPtr + 28#64) ↦₃₂ prevG.freedMask) ∗ ((prevG.metaPtr + 32#64) ↦₆₄ prevG.packedWord)) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion prevG.metaPtr 40 a) st.byteVal) ∗ R) =
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) bv_a ∗ R) := by
    have hc := metaBytes_eq_cells prevUpd
    have hPw : prevUpd.packedWord = prevG.packedWord := rfl
    rw [hPw] at hc; dsimp only [prevUpd] at hc
    rw [← hc, hBmPW]
  change SepWP _ _ _ ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ _ ∗ R) _ _
  rw [hFoldA]
  have hBmGa := (byteMap_update40 hDomNd bv_a (P := OwnedRwByte st)
    (m := g.metaPtr) (bs := g.metaBytes) (GroupDesc.metaBytes_length _) hOwnG).1
  rw [hBmGa, hReadG_a, metaBytes_eq_cells g]
  apply step_ldr64_fast (b + 0x1a4#64) (b + 0x1a8#64) g.metaPtr g.prev
  · rfl
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, arm64_norm, hx19]
  · wp_sep_access_fast
  · bv_omega
  rw [← metaBytes_eq_cells g, ← hReadG_a, ← hBmGa]
  have ⟨hBmNa, hBmNW⟩ := byteMap_update40 hDomNd bv_a (P := OwnedRwByte st)
    (m := nextG.metaPtr) (bs := nextMid.metaBytes) (GroupDesc.metaBytes_length _) hOwnNext
  have hNPreCells := metaBytes_eq_cells nextPre
  have hNPreM : nextPre.metaPtr = nextG.metaPtr := rfl
  rw [hNPreM] at hNPreCells
  rw [hBmNa, hReadNext_a, hNPreCells]
  apply step_str64_fast (b + 0x1a8#64) (b + 0x1ac#64) nextG.metaPtr g.prev
  · rfl
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, arm64_norm]; exact Prod.ext (hx4.trans hNextPtr.symm) rfl
  · simp only [arm64_norm]
  · wp_sep_access_fast
  · bv_omega
  intro m2 hm2 _
  have hFoldB :
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       (((nextG.metaPtr ↦₆₄ g.prev) ∗ ((nextG.metaPtr + 8#64) ↦₆₄ nextPre.next) ∗
         ((nextG.metaPtr + 16#64) ↦₆₄ nextPre.mem) ∗ ((nextG.metaPtr + 24#64) ↦₃₂ nextPre.availMask) ∗
         ((nextG.metaPtr + 28#64) ↦₃₂ nextPre.freedMask) ∗ ((nextG.metaPtr + 32#64) ↦₆₄ nextPre.packedWord)) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion nextG.metaPtr 40 a) bv_a) ∗ R) =
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) bv_b ∗ R) := by
    have hc := metaBytes_eq_cells nextMid
    have hPw : nextMid.packedWord = nextPre.packedWord := rfl
    have hMm : nextMid.metaPtr = nextG.metaPtr := rfl
    rw [hPw, hMm] at hc; dsimp only [nextMid] at hc
    rw [← hc, hBmNW]
  change SepWP _ _ _ ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ _ ∗ R) _ _
  rw [hFoldB]
  obtain ⟨CtxRest0, hCtxRead0, hCtxWrite0⟩ :=
    ctx_focus_update_active maddrs.ctx st.ctx hwf.ctx_lens.1 hSc48 g.next
  rw [hCtxRead0]
  apply step_ldr64_fast (b + 0x1ac#64) (b + 0x1b0#64)
    (maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc)) head
  · rfl
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, extendVal, arm64_norm]; exact Prod.ext hActAddr rfl
  · wp_sep_access_fast
  · bv_omega
  wp_step
  wp_step
  wp_if_nd hEqBr
  · -- Head removal (`g.metaPtr = head`): `+0x258..+0x260 -> +0x1b8..+0x1c0 -> +0x264 -> +0x1c4`
    have ⟨hBmGb, hBmGW⟩ := byteMap_update40 hDomNd bv_b (P := OwnedRwByte st)
      (m := g.metaPtr) (bs := gZero.metaBytes) (GroupDesc.metaBytes_length _) hOwnG
    rw [hBmGb, hReadG_b, metaBytes_eq_cells g]
    apply step_ldr64_fast (b + 0x258#64) (b + 0x25c#64) (g.metaPtr + 8#64) g.next
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrun]
    · wp_close_fetch_cl
    · rfl
    · simp only [evalAddrMode, arm64_norm, hx19]
    · wp_sep_access_fast
    · bv_omega
    apply step_str64_fast (b + 0x25c#64) (b + 0x260#64)
      (maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc)) g.next
    · rfl
    · simp only [arm64_norm, hrun]
    · wp_close_fetch_cl
    · rfl
    · simp only [evalAddrMode, extendVal, arm64_norm]; exact Prod.ext hActAddr rfl
    · simp only [arm64_norm]
    · wp_sep_access_fast
    · bv_omega
    intro m3 hm3 _
    rw [hCtxWrite0]
    wp_step
    wp_stp64_p m4 hm4
    have hEqHead : g.metaPtr = head := by
      simpa only [arm64_norm, hx19, beq_iff_eq, decide_eq_true_eq] using hEqBr
    let active1 := st.ctx.active.set g.sc (if g.metaPtr == head then g.next else head)
    have hAct1Eq : st.ctx.active.set g.sc g.next = active1 := by
      dsimp only [active1]; simp [hEqHead]
    let cAct : CtxFields := { st.ctx with active := active1 }
    rw [hAct1Eq]
    have hFoldHead :
        ((maddrs.ctx ↦ₛ cAct.toBytes) ∗
         (((g.metaPtr ↦₆₄ 0#64) ∗ ((g.metaPtr + 8#64) ↦₆₄ 0#64) ∗
           ((g.metaPtr + 16#64) ↦₆₄ g.mem) ∗ ((g.metaPtr + 24#64) ↦₃₂ g.availMask) ∗
           ((g.metaPtr + 28#64) ↦₃₂ g.freedMask) ∗ ((g.metaPtr + 32#64) ↦₆₄ g.packedWord)) ∗
          ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) bv_b) ∗ R) =
        ((maddrs.ctx ↦ₛ cAct.toBytes) ∗
         ByteMap st.masterDom (OwnedRwByte st) bv_c ∗ R) := by
      have hc := metaBytes_eq_cells gZero
      have hPw : gZero.packedWord = g.packedWord := rfl
      rw [hPw] at hc; dsimp only [gZero] at hc
      rw [← hc, hBmGW]
    change SepWP _ _ _ ((maddrs.ctx ↦ₛ cAct.toBytes) ∗ _ ∗ R) _ _
    rw [hFoldHead]
    wp_step
    wp_step
    wp_if_nd hEqBr2
    · obtain ⟨hAv0N, _, hReadNc, hActBN, hOwnActB, hDomActB⟩ := hHeadAct hEqHead
      have hCLen : cAct.active.length = 48 := by simp [cAct, active1, hwf.ctx_lens.1]
      have hCGet : cAct.active[g.sc]'(hCLen ▸ hSc48) = nextMid.metaPtr := by
        dsimp only [cAct, active1, nextMid, nextPre]
        simp only [hEqHead, beq_self_eq_true, ↓reduceIte, List.getElem_set_self]
        exact hNextPtr.symm
      exact sepWP_nf_activate_group_264 hb
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simpa [arm64_norm] using hx8) (by simpa [arm64_norm] using hx20)
        (by simpa [arm64_norm] using hx19)
        (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
        (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
            exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                   by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                   by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                   by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                   by simpa [calleeSavedVRegs] using cv⟩)
        hSc48 hCLen hCGet
        (by change nextG.metaPtr ≠ 0#64; rw [hNextPtr]; exact hNxNe0)
        hAv0N hmAlN hmFitN hDomNd hOwnNext hReadNc hActBN hOwnActB hDomActB
        (fun s1 hpc1 hrun1 hx19_1 hx20_1 hsp1 hbrk1 hperm1 hProc1 hcs1 => by
          have hUseL : cAct.usageByClass.length = 48 := hwf.ctx_lens.2.1
          have hBvDeqEq :
              writeBytesToMap bv_c nextMid.metaPtr (mkActivatedGroup nextMid).metaBytes =
              (if g.metaPtr == head then
                writeBytesToMap bv_c nextG.metaPtr (mkActivatedGroup nextMid).metaBytes
               else bv_c) := by
            simp [hEqHead, nextMid, nextPre]
          rw [hBvDeqEq]
          exact sepWP_nf_usage_dec_1c4 hb
            hpc1 hrun1 hx19_1 hx20_1
            hProc1 hcs1 hSc48 hLast31 hCLen hUseL hDomNd hOwnG hDeq.g_zero_bytes
            (fun s2 hpc2 hrun2 hx0_2 hx19_2 hsp2 hbrk2 hperm2 hProc2 hcs2 =>
              hCont active1 _ _ _ _ s2 hDeq hpc2 hrun2 hx0_2 hx19_2
                (hsp2.trans (hsp1.trans (by simp [arm64_norm])))
                (hbrk2.trans (hbrk1.trans (by simp [arm64_norm])))
                (hperm2.trans (hperm1.trans (hm4.trans (hm3.trans (hm2.trans hm1)))))
                hProc2 hcs2))
    · exfalso
      dsimp only [head] at hEqBr2
      simp [arm64_norm] at hEqBr2
  · -- Non-head removal (`g.metaPtr ≠ head`): `+0x1b8..+0x1c0 -> +0x1c4`
    have hNeHead : g.metaPtr ≠ head := by
      simpa only [arm64_norm, hx19, beq_iff_eq, decide_eq_true_eq] using hEqBr
    rw [← hCtxRead0]
    have ⟨hBmGb, hBmGW⟩ := byteMap_update40 hDomNd bv_b (P := OwnedRwByte st)
      (m := g.metaPtr) (bs := gZero.metaBytes) (GroupDesc.metaBytes_length _) hOwnG
    rw [hBmGb, hReadG_b, metaBytes_eq_cells g]
    wp_stp64_p m3 hm3
    have hFoldNonHead :
        ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
         (((g.metaPtr ↦₆₄ 0#64) ∗ ((g.metaPtr + 8#64) ↦₆₄ 0#64) ∗
           ((g.metaPtr + 16#64) ↦₆₄ g.mem) ∗ ((g.metaPtr + 24#64) ↦₃₂ g.availMask) ∗
           ((g.metaPtr + 28#64) ↦₃₂ g.freedMask) ∗ ((g.metaPtr + 32#64) ↦₆₄ g.packedWord)) ∗
          ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) bv_b) ∗ R) =
        ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
         ByteMap st.masterDom (OwnedRwByte st) bv_c ∗ R) := by
      have hc := metaBytes_eq_cells gZero
      have hPw : gZero.packedWord = g.packedWord := rfl
      rw [hPw] at hc; dsimp only [gZero] at hc
      rw [← hc, hBmGW]
    change SepWP _ _ _ ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ _ ∗ R) _ _
    rw [hFoldNonHead]
    wp_step
    wp_step
    wp_if_nd hEqBr2
    · exfalso
      have hEq0 : g.metaPtr = head := by
        have hHx0 : s.readReg64 (.gpr 0#5) = head := hx0
        simpa only [arm64_norm, hx19, hHx0, beq_iff_eq, decide_eq_true_eq] using hEqBr2
      exact hNeHead hEq0
    · have hBvDeqEq :
          bv_c =
          (if g.metaPtr == head then
            writeBytesToMap bv_c nextG.metaPtr (mkActivatedGroup nextMid).metaBytes
           else bv_c) := by
        simp [beq_false_of_ne hNeHead]
      have hAct1Self :
          st.ctx.active =
          st.ctx.active.set g.sc (if g.metaPtr == head then g.next else head) := by
        simp only [beq_false_of_ne hNeHead, Bool.false_eq_true, ↓reduceIte]
        exact (List.set_getElem_self hActLt).symm
      rw [hBvDeqEq]
      exact sepWP_nf_usage_dec_1c4 hb
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simpa [arm64_norm] using hx19) (by simpa [arm64_norm] using hx20)
        (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
        (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
            exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                   by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                   by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                   by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                   by simpa [calleeSavedVRegs] using cv⟩)
        hSc48 hLast31 hwf.ctx_lens.1 hwf.ctx_lens.2.1 hDomNd hOwnG hDeq.g_zero_bytes
        (fun s2 hpc2 hrun2 hx0_2 hx19_2 hsp2 hbrk2 hperm2 hProc2 hcs2 => by
          have hCtxEq :
              (ctxSubUsage st.ctx g.sc hwf.ctx_lens.2.1 hSc48 g.cnt) =
              { st.ctx with
                active := st.ctx.active.set g.sc (if g.metaPtr == head then g.next else head)
                usageByClass := st.ctx.usageByClass.set g.sc
                  ((st.ctx.usageByClass[g.sc]'(hwf.ctx_lens.2.1 ▸ hSc48)) - BitVec.ofNat 64 g.cnt) } := by
            dsimp only [ctxSubUsage]
            rw [← hAct1Self]
          rw [hCtxEq]
          exact hCont _ _ _ _ _ s2 hDeq hpc2 hrun2 hx0_2 hx19_2
            (hsp2.trans (by simp [arm64_norm]))
            (hbrk2.trans (by simp [arm64_norm]))
            (hperm2.trans (hm3.trans (hm2.trans hm1)))
            hProc2 hcs2)

/-! ## All-Free Dispatch -/

set_option maxHeartbeats 400000 in
theorem sepWP_nf_at_0b8 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b)
    {inflight : Nat} {brkStart : BitVec 64} {liveCost peakCost : Nat}
    {target_pc : BitVec 64} {st : MallocngSt} {g : GroupDesc}
    {R : SepProp} {s0 s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = b + 0xb8#64) (hrun : s.status = .Running)
    (hwf : MallocngWFInflight inflight maddrs.base brkStart s0.brk liveCost peakCost st)
    (hg : g ∈ st.groups) (hSc48 : g.sc < 48)
    (hx0 : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 g.sc)
    (hx4 : s.readReg64 (.gpr 4#5) = g.next)
    (hw6 : s.readReg32 (.gpr 6#5) = BitVec.ofNat 32 g.lastIdx)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 g.sc)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hProc : MallocngProcPreserved s0 s) (hcs : Cs21Preserved s0 s)
    (hCont : NfDeqCont b target_pc st g R s0 s post oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ R) post oom := by
  have _ := hb
  have hLast31 : g.lastIdx ≤ 31 := (hwf.groups_wf g hg).2.1
  wp_step
  wp_if_nd hNxBr
  · -- `g.next ≠ 0#64` -> `+0x17c..+0x190`
    have hNxNe0 : g.next ≠ 0#64 := by simpa [arm64_norm] using hNxBr
    have hCtx20 : pageOf maddrs.ctx + lo12Of maddrs.ctx = maddrs.ctx := pageOf_add_lo12Of maddrs.ctx
    have hScProps := sc_cmp47_and_active_off_fin ⟨g.sc, hSc48⟩
    have hActAddr : maddrs.ctx + ((BitVec.ofNat 64 g.sc + 10#64) <<< 3) =
        maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc) :=
      congrArg (maddrs.ctx + ·) hScProps.2.2.2.2
    have hActLt : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
    let head := st.ctx.active[g.sc]'hActLt
    wp_step
    wp_step
    wp_step
    wp_step
    obtain ⟨CtxRest0, hCtxRead0, _⟩ :=
      ctx_focus_update_active maddrs.ctx st.ctx hwf.ctx_lens.1 hSc48 0#64
    rw [hCtxRead0]
    apply step_ldr64_fast (b + 0x18c#64) (b + 0x190#64)
      (maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc)) head
    · rfl
    · simp only [arm64_norm, hrun]
    · wp_close_fetch_cl
    · rfl
    · simp only [evalAddrMode, extendVal, arm64_norm]; exact Prod.ext hActAddr rfl
    · wp_sep_access_fast
    · bv_omega
    rw [← hCtxRead0]
    wp_step
    wp_if_nd hSelfBr
    · have hNxSelf : g.next = g.metaPtr := Eq.symm (by simpa [arm64_norm] using hSelfBr)
      have hHeadEq := (dequeue_singleton hwf hg hSc48 hNxSelf).1
      exact sepWP_nf_dequeue_singleton_120 hb
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simpa [arm64_norm] using hHeadEq) (by simpa [arm64_norm] using hx8)
        (by simpa [arm64_norm] using hx19) (by simp [arm64_norm])
        (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
        (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
            exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                   by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                   by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                   by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                   by simpa [calleeSavedVRegs] using cv⟩)
        hwf hg hSc48 hNxSelf
        (fun active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
          hCont active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19'
            (hsp'.trans (by simp [arm64_norm]))
            (hbrk'.trans (by simp [arm64_norm]))
            (hperm'.trans (by simp [arm64_norm]))
            hProc' hcs')
    · have hNxNeSelf : g.next ≠ g.metaPtr := Ne.symm (by simpa [arm64_norm] using hSelfBr)
      exact sepWP_nf_dequeue_194 hb
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        hwf hg hSc48
        (by simp [arm64_norm, head]) (by simpa [arm64_norm] using hx4)
        (by simpa [arm64_norm] using hx8) (by simpa [arm64_norm] using hx19)
        (by simp [arm64_norm])
        (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
        (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
            exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                   by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                   by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                   by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                   by simpa [calleeSavedVRegs] using cv⟩)
        hNxNe0 hNxNeSelf
        (fun active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
          hCont active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19'
            (hsp'.trans (by simp [arm64_norm]))
            (hbrk'.trans (by simp [arm64_norm]))
            (hperm'.trans (by simp [arm64_norm]))
            hProc' hcs')
  · -- `g.next = 0#64` -> `+0x0bc..+0x0d8`
    have hNx0 : g.next = 0#64 := by simpa [arm64_norm] using hNxBr
    obtain ⟨_, _, hDeq⟩ := dequeue_not_queued hwf hg hSc48 hNx0
    exact sepWP_nf_usage_dec_0bc hb
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simpa [arm64_norm] using hx0) (by simpa [arm64_norm] using hx8)
      (by simpa [arm64_norm] using hw6) (by simpa [arm64_norm] using hx19)
      (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
      (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
          exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                 by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                 by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                 by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                 by simpa [calleeSavedVRegs] using cv⟩)
      hSc48 hLast31 hwf.ctx_lens.1 hwf.ctx_lens.2.1
      (fun s' hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
        hCont st.ctx.active _ st.activeLists _ st.byteVal s' hDeq hpc' hrun' hx0' hx19'
          (hsp'.trans (by simp [arm64_norm]))
          (hbrk'.trans (by simp [arm64_norm]))
          (hperm'.trans (by simp [arm64_norm]))
          hProc' hcs')

abbrev NfAllFreeFrame [MallocngMultiPlacement]
    (fuel : Nat) (γ : GhostName) (st : MallocngSt) (s0 : State) : SepProp :=
  stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
  MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st ∗
  ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
  MappedSet st.masterDom (OwnedMappedByte st)

set_option maxHeartbeats 400000 in
private theorem sepWP_nf_kept_130 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {bud : MallocngBudget}
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x130#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = ((BitVec.ofNat 64 g.sc).truncate 32 - 7#32).zeroExtend 64)
    (hw1 : s.readReg32 (.gpr 1#5) = 1#32 <<< idx)
    (_hw6 : s.readReg32 (.gpr 6#5) = BitVec.ofNat 32 g.lastIdx)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 g.sc)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = pageOf maddrs.ctx)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st)
    (hKeep : EmptyGroupKeepWf st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hSc48 : g.sc < 48) (hSc7 : 7 ≤ g.sc) (hSc38 : g.sc ≤ 38)
    (hMpPos : 0 < g.maplen) (hNxSelf : g.next = g.metaPtr)
    (hStrideFit : g.lastIdx = 0 → slotStride g.sc + 16 ≤ g.maplen * 4096)
    (hCont : NfDeqCont b (s0.readReg64 .lr) st g (NfAllFreeFrame fuel γ st s0) s0 s
      (NfFuelPost k fuel γ brkStart bud st s0) oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       NfAllFreeFrame fuel γ st s0)
      (NfFuelPost k fuel γ brkStart bud st s0) oom := by
  have _ := hb
  have hCtx20 : pageOf maddrs.ctx + lo12Of maddrs.ctx = maddrs.ctx := pageOf_add_lo12Of maddrs.ctx
  have _hSignExt : ((BitVec.ofNat 64 g.sc).truncate 32 - 7#32).signExtend 64 =
      BitVec.ofNat 64 (g.sc - 7) :=
    (sc_sub7_ule31_fin ⟨g.sc, hSc48⟩).2 hSc7 hSc38
  wp_step
  wp_step
  have hKLt32 : g.sc - 7 < 32 := by omega
  obtain ⟨BncRest, hBncRead⟩ :=
    ctx_focus_bounces_byte maddrs.ctx st.ctx hwf.ctx_lens.1 hwf.ctx_lens.2.1
      hwf.ctx_lens.2.2.1 hwf.ctx_lens.2.2.2.1 hKLt32
  have hBncLt : g.sc - 7 < st.ctx.bounces.length := by rw [hwf.ctx_lens.2.2.2.1]; exact hKLt32
  let bncByte := st.ctx.bounces[g.sc - 7]'hBncLt
  rw [hBncRead]
  apply step_ldr8_fast (b + 0x138#64) (b + 0x13c#64)
    (maddrs.ctx + BitVec.ofNat 64 (880 + (g.sc - 7))) bncByte
  · rfl
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp [evalAddrMode, arm64_norm]
    rw [BitVec.add_assoc]; congr 1; bv_omega
  · wp_sep_access_fast
  · bv_omega
  rw [← hBncRead]
  wp_step
  wp_step
  wp_if_nd _hBncBr
  · exact sepWP_nf_dequeue_singleton_114 hb
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simpa [arm64_norm] using hx8) (by simpa [arm64_norm] using hx19)
      (by simpa [arm64_norm] using hx20)
      (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
      (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
          exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                 by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                 by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                 by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                 by simpa [calleeSavedVRegs] using cv⟩)
      hwf hg hSc48 hNxSelf
      (fun active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
        hCont active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19'
          (hsp'.trans (by simp [arm64_norm]))
          (hbrk'.trans (by simp [arm64_norm]))
          (hperm'.trans (by simp [arm64_norm]))
          hProc' hcs')
  · -- `+0x144: add x2, x8, #0x3a`; `+0x148: add w6, w6, #0x1`; `+0x14c: sbfiz x0, x6, #3, #32`
    wp_step
    wp_step
    wp_step
    have hUseAddr : maddrs.ctx + ((BitVec.ofNat 64 g.sc + 0x3a#64) <<< 3) =
        maddrs.ctx + BitVec.ofNat 64 (464 + 8 * g.sc) :=
      congrArg (maddrs.ctx + ·) (sc_usage_off_fin ⟨g.sc, hSc48⟩)
    obtain ⟨UseRest, hUseRead, _⟩ :=
      ctx_focus_update_usage maddrs.ctx st.ctx hwf.ctx_lens.1 hwf.ctx_lens.2.1 hSc48 0#64
    have hUseLt : g.sc < st.ctx.usageByClass.length := by rw [hwf.ctx_lens.2.1]; exact hSc48
    let useVal := st.ctx.usageByClass[g.sc]'hUseLt
    rw [hUseRead]
    apply step_ldr64_fast (b + 0x150#64) (b + 0x154#64)
      (maddrs.ctx + BitVec.ofNat 64 (464 + 8 * g.sc)) useVal
    · rfl
    · simp only [arm64_norm, hrun]
    · wp_close_fetch_cl
    · rfl
    · simp only [evalAddrMode, extendVal, arm64_norm]; exact Prod.ext hUseAddr rfl
    · wp_sep_access_fast
    · bv_omega
    rw [← hUseRead]
    wp_step
    wp_step
    wp_step
    wp_step
    wp_if_nd _hCntBr
    · exact sepWP_nf_dequeue_singleton_114 hb
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simpa [arm64_norm] using hx8) (by simpa [arm64_norm] using hx19)
        (by simpa [arm64_norm] using hx20)
        (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
        (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
            exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                   by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                   by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                   by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                   by simpa [calleeSavedVRegs] using cv⟩)
        hwf hg hSc48 hNxSelf
        (fun active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
          hCont active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19'
            (hsp'.trans (by simp [arm64_norm]))
            (hbrk'.trans (by simp [arm64_norm]))
            (hperm'.trans (by simp [arm64_norm]))
            hProc' hcs')
    · -- Kept-empty singleton exit (`+0x164..+0x178` -> `+0x474`)
      obtain ⟨hHeadEq, hActSingle, _, _, hOwnG, _⟩ := dequeue_singleton hwf hg hSc48 hNxSelf
      obtain ⟨_, hmAl, hmFit, hReadG, _⟩ := meta_ownedRw_of_mem_groups hwf hg
      have hInActive : ∀ hScLt : g.sc < st.activeLists.length, g.metaPtr ∈ st.activeLists[g.sc]'hScLt := by
        intro hScLt; rw [hActSingle]; exact List.mem_singleton.mpr rfl
      have hMpBound : g.maplen * 4096 ≤ 1048576 := hKeep g hg hMpPos hSc7 hSc38
      obtain ⟨hProt1, hMap1, hByte1, hDyn1, hCnt1, hWf1, _⟩ :=
        free_set_freedMask_keep hwf hg hIdx hClaimed hSc48 hInActive
          (Or.inr ⟨hMpPos, hSc7, hSc38, hMpBound, (fun _ => hActSingle), hStrideFit⟩)
      have hAt474 : ∀ s474 : State,
          s474.pc = b + 0x474#64 → s474.status = .Running →
          s474.readReg64 (.gpr 19#5) = g.metaPtr →
          s474.readReg32 (.gpr 1#5) = 1#32 <<< idx →
          s474.sp = s0.sp - 32#64 → MallocngProcPreserved s0 s474 →
          s474.brk = s0.brk → s474.mem.perm = s0.mem.perm → Cs21Preserved s0 s474 →
          SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s474
            ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
             ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
             NfAllFreeFrame fuel γ st s0)
            (NfFuelPost k fuel γ brkStart bud st s0) oom := by
        intro s4 hpc4 hrun4 hx19_4 hw1_4 hsp4 hProc4 hbrk4 hperm4 hcs4
        have hBmG0 := (byteMap_update40 hwf.masterDom_wf.1 st.byteVal (P := OwnedRwByte st)
          (m := g.metaPtr) (bs := (mkFreedKeepGroup g idx).metaBytes)
          (GroupDesc.metaBytes_length _) hOwnG).1
        rw [hBmG0, hReadG]
        apply SepWP.weaken_pre
        rotate_left
        · exact sepWP_nf_commit_474 hb hFuel
            (gPre := g) (gPost := mkFreedKeepGroup g idx) (self32 := 1#32 <<< idx)
            hpc4 hrun4 hx19_4 hw1_4 hmAl hmFit rfl (metaBytes_congr rfl rfl rfl rfl rfl rfl)
            hsp4 hspAl0 hProc4 hbrk4 hperm4 hcs4
            hWf1 rfl rfl (by omega) hDyn1
            (Cost.groupsGrpMono_replaceGroupByMeta hg _ rfl rfl) hByte1
        · dsimp only [NfAllFreeFrame, NfStaticRest]
          rw [hProt1, hMap1]
          sep_frame
      wp_step
      wp_if_nd _hW3Br
      · exact hAt474 _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
          (by simpa [arm64_norm] using hx19) (by simpa [arm64_norm] using hw1)
          (by simpa [arm64_norm] using hsp)
          (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
          (by simpa [arm64_norm] using hbrk) (by simpa [arm64_norm] using hperm)
          (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
              exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                     by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                     by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                     by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                     by simpa [calleeSavedVRegs] using cv⟩)
      · -- `+0x168: add x2, x8, #0xa`; `+0x16c: ldr x0, [x4, x2, lsl #3]`
        wp_step
        have hScProps := sc_cmp47_and_active_off_fin ⟨g.sc, hSc48⟩
        have hActAddr : maddrs.ctx + ((BitVec.ofNat 64 g.sc + 10#64) <<< 3) =
            maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc) :=
          congrArg (maddrs.ctx + ·) hScProps.2.2.2.2
        obtain ⟨ActRest, hActRead, _⟩ :=
          ctx_focus_update_active maddrs.ctx st.ctx hwf.ctx_lens.1 hSc48 0#64
        rw [hActRead, hHeadEq]
        apply step_ldr64_fast (b + 0x16c#64) (b + 0x170#64)
          (maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc)) g.metaPtr
        · rfl
        · simp only [arm64_norm, hrun]
        · wp_close_fetch_cl
        · rfl
        · simp only [evalAddrMode, extendVal, arm64_norm]; exact Prod.ext hActAddr rfl
        · wp_sep_access_fast
        · bv_omega
        rw [← hHeadEq, ← hActRead]
        wp_step
        wp_step
        wp_step
        exact hAt474 _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
          (by simpa [arm64_norm] using hx19) (by simpa [arm64_norm] using hw1)
          (by simpa [arm64_norm] using hsp)
          (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
          (by simpa [arm64_norm] using hbrk) (by simpa [arm64_norm] using hperm)
          (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
              exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                     by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                     by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                     by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                     by simpa [calleeSavedVRegs] using cv⟩)

set_option maxHeartbeats 400000 in
theorem sepWP_nf_at_0e4 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {bud : MallocngBudget}
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0xe4#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 g.sc)
    (hw1 : s.readReg32 (.gpr 1#5) = 1#32 <<< idx)
    (hx4 : s.readReg64 (.gpr 4#5) = g.next)
    (hw6 : s.readReg32 (.gpr 6#5) = BitVec.ofNat 32 g.lastIdx)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 g.sc)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st)
    (hKeep : EmptyGroupKeepWf st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hSc48 : g.sc < 48) (hMpPos : 0 < g.maplen)
    (hStrideFit : g.lastIdx = 0 → slotStride g.sc + 16 ≤ g.maplen * 4096)
    (hCont : NfDeqCont b (s0.readReg64 .lr) st g (NfAllFreeFrame fuel γ st s0) s0 s
      (NfFuelPost k fuel γ brkStart bud st s0) oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       NfAllFreeFrame fuel γ st s0)
      (NfFuelPost k fuel γ brkStart bud st s0) oom := by
  have _ := hb
  have hLast31 : g.lastIdx ≤ 31 := (hwf.groups_wf g hg).2.1
  wp_step
  wp_step
  wp_if_nd hSelfBr
  · -- Singleton in active list (`g.next = g.metaPtr`) -> `+0x104..+0x110`
    have hNxSelf : g.next = g.metaPtr := Eq.symm (by simpa [arm64_norm] using hSelfBr)
    wp_step
    wp_step
    wp_step
    wp_step
    wp_if_nd hLsBr
    · have ⟨hSc7, hSc38⟩ : 7 ≤ g.sc ∧ g.sc ≤ 38 := by
        try unfold BitVec.ule at hLsBr
        try unfold BitVec.ult at hLsBr
        simp [arm64_norm] at hLsBr
        omega
      exact sepWP_nf_kept_130 hb hFuel
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simp [arm64_norm]) (by simpa [arm64_norm] using hw1)
        (by simpa [arm64_norm] using hw6) (by simpa [arm64_norm] using hx8)
        (by simpa [arm64_norm] using hx19) (by simp [arm64_norm])
        (by simpa [arm64_norm] using hsp) hspAl0
        (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
        (by simpa [arm64_norm] using hbrk) (by simpa [arm64_norm] using hperm)
        (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
            exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                   by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                   by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                   by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                   by simpa [calleeSavedVRegs] using cv⟩)
        hwf hKeep hg hIdx hClaimed hSc48 hSc7 hSc38 hMpPos hNxSelf hStrideFit
        (fun active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
          hCont active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19'
            (hsp'.trans (by simp [arm64_norm]))
            (hbrk'.trans (by simp [arm64_norm]))
            (hperm'.trans (by simp [arm64_norm]))
            hProc' hcs')
    · exact sepWP_nf_dequeue_singleton_114 hb
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simpa [arm64_norm] using hx8) (by simpa [arm64_norm] using hx19)
        (by simp [arm64_norm])
        (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
        (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
            exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                   by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                   by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                   by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                   by simpa [calleeSavedVRegs] using cv⟩)
        hwf hg hSc48 hNxSelf
        (fun active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
          hCont active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19'
            (hsp'.trans (by simp [arm64_norm]))
            (hbrk'.trans (by simp [arm64_norm]))
            (hperm'.trans (by simp [arm64_norm]))
            hProc' hcs')
  · -- `g.next ≠ g.metaPtr` -> `+0x0ec: cbz x4, +0x0bc`
    have hNxNeSelf : g.next ≠ g.metaPtr := Ne.symm (by simpa [arm64_norm] using hSelfBr)
    wp_step
    wp_if_nd hNxZero
    · have hNx0 : g.next = 0#64 := by simpa [arm64_norm] using hNxZero
      obtain ⟨_, _, hDeq⟩ := dequeue_not_queued hwf hg hSc48 hNx0
      exact sepWP_nf_usage_dec_0bc hb
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simpa [arm64_norm] using hx0) (by simpa [arm64_norm] using hx8)
        (by simpa [arm64_norm] using hw6) (by simpa [arm64_norm] using hx19)
        (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
        (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
            exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                   by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                   by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                   by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                   by simpa [calleeSavedVRegs] using cv⟩)
        hSc48 hLast31 hwf.ctx_lens.1 hwf.ctx_lens.2.1
        (fun s' hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
          hCont st.ctx.active _ st.activeLists _ st.byteVal s' hDeq hpc' hrun' hx0' hx19'
            (hsp'.trans (by simp [arm64_norm]))
            (hbrk'.trans (by simp [arm64_norm]))
            (hperm'.trans (by simp [arm64_norm]))
            hProc' hcs')
    · -- `g.next ≠ 0#64` -> `+0x0f0..+0x100` -> `+0x194`
      have hNxNe0 : g.next ≠ 0#64 := by simpa [arm64_norm] using hNxZero
      have hCtx20 : pageOf maddrs.ctx + lo12Of maddrs.ctx = maddrs.ctx := pageOf_add_lo12Of maddrs.ctx
      have hScProps := sc_cmp47_and_active_off_fin ⟨g.sc, hSc48⟩
      have hActAddr : maddrs.ctx + ((BitVec.ofNat 64 g.sc + 10#64) <<< 3) =
          maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc) :=
        congrArg (maddrs.ctx + ·) hScProps.2.2.2.2
      have hActLt : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
      let head := st.ctx.active[g.sc]'hActLt
      wp_step
      wp_step
      wp_step
      obtain ⟨CtxRest0, hCtxRead0, _⟩ :=
        ctx_focus_update_active maddrs.ctx st.ctx hwf.ctx_lens.1 hSc48 0#64
      rw [hCtxRead0]
      apply step_ldr64_fast (b + 0x0fc#64) (b + 0x100#64)
        (maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc)) head
      · rfl
      · simp only [arm64_norm, hrun]
      · wp_close_fetch_cl
      · rfl
      · simp only [evalAddrMode, extendVal, arm64_norm]; exact Prod.ext hActAddr rfl
      · wp_sep_access_fast
      · bv_omega
      rw [← hCtxRead0]
      wp_step
      exact sepWP_nf_dequeue_194 hb
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        hwf hg hSc48
        (by simp [arm64_norm, head]) (by simpa [arm64_norm] using hx4)
        (by simpa [arm64_norm] using hx8) (by simpa [arm64_norm] using hx19)
        (by simp [arm64_norm])
        (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
        (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
            exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                   by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                   by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                   by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                   by simpa [calleeSavedVRegs] using cv⟩)
        hNxNe0 hNxNeSelf
        (fun active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
          hCont active1 usage1 actLists1 gsDeq bvDeq s' hDeq hpc' hrun' hx0' hx19'
            (hsp'.trans (by simp [arm64_norm]))
            (hbrk'.trans (by simp [arm64_norm]))
            (hperm'.trans (by simp [arm64_norm]))
            hProc' hcs')
end

end LibsignalBinary.Heap.Fine.VendorFree
