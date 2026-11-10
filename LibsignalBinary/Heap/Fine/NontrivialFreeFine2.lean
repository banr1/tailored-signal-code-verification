/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.NontrivialFreeFine1
public import LibsignalBinary.Heap.Fine.VendorFree.PlacedNontrivialFreeStage5

/-!
# Fine-Grained Placed `nontrivial_free` Stage 2

Strengthens the kept-empty singleton check, root-group retirement, all-free entry dispatch, and
fuel-indexed contract (`nontrivialFreeFuelFinePlainSpec`) for `nontrivial_free` (`blk05`) with
`SameLiveUserSub st' st`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic ProofLib.ProgramReflection
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open LibsignalBinary.Heap.Fine.VendorFree
open scoped LibsignalBinary.Heap.Fine.VendorFree

/-! ## Kept-Empty Singleton Check and `+0x0e4` Dispatch -/

set_option maxHeartbeats 400000 in
theorem sepWP_nf_kept_130_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {liveCost peakCost : Nat}
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
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk liveCost peakCost st)
    (hKeep : EmptyGroupKeepWf st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hSc48 : g.sc < 48) (hSc7 : 7 ≤ g.sc) (hSc38 : g.sc ≤ 38)
    (hMpPos : 0 < g.maplen) (hNxSelf : g.next = g.metaPtr)
    (hStrideFit : g.lastIdx = 0 → slotStride g.sc + 16 ≤ g.maplen * 4096)
    (hCont : NfDeqCont b (s0.readReg64 .lr) st g (NfAllFreeFrame fuel γ st s0) s0 s
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       NfAllFreeFrame fuel γ st s0)
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom := by
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
  · wp_step
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
    · obtain ⟨hHeadEq, hActSingle, _, _, hOwnG, _⟩ := dequeue_singleton hwf hg hSc48 hNxSelf
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
            (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom := by
        intro s4 hpc4 hrun4 hx19_4 hw1_4 hsp4 hProc4 hbrk4 hperm4 hcs4
        have hBmG0 := (byteMap_update40 hwf.masterDom_wf.1 st.byteVal (P := OwnedRwByte st)
          (m := g.metaPtr) (bs := (mkFreedKeepGroup g idx).metaBytes)
          (GroupDesc.metaBytes_length _) hOwnG).1
        rw [hBmG0, hReadG]
        apply SepWP.weaken_pre
        rotate_left
        · exact sepWP_nf_commit_474_fine hb hFuel
            (gPre := g) (gPost := mkFreedKeepGroup g idx) (self32 := 1#32 <<< idx)
            hpc4 hrun4 hx19_4 hw1_4 hmAl hmFit rfl (metaBytes_congr rfl rfl rfl rfl rfl rfl)
            hsp4 hspAl0 hProc4 hbrk4 hperm4 hcs4
            hWf1 rfl rfl
            (sameLiveUserSub_mkFreedKeepGroup hwf.groups_nodup.1 hg hIdx hClaimed _)
            (by omega) hDyn1 hByte1
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
      · wp_step
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
theorem sepWP_nf_at_0e4_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {liveCost peakCost : Nat}
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
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk liveCost peakCost st)
    (hKeep : EmptyGroupKeepWf st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hSc48 : g.sc < 48) (hMpPos : 0 < g.maplen)
    (hStrideFit : g.lastIdx = 0 → slotStride g.sc + 16 ≤ g.maplen * 4096)
    (hCont : NfDeqCont b (s0.readReg64 .lr) st g (NfAllFreeFrame fuel γ st s0) s0 s
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       NfAllFreeFrame fuel γ st s0)
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom := by
  have _ := hb
  have hLast31 : g.lastIdx ≤ 31 := (hwf.groups_wf g hg).2.1
  wp_step
  wp_step
  wp_if_nd hSelfBr
  · have hNxSelf : g.next = g.metaPtr := Eq.symm (by simpa [arm64_norm] using hSelfBr)
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
      exact sepWP_nf_kept_130_fine hb hFuel
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
  · have hNxNeSelf : g.next ≠ g.metaPtr := Ne.symm (by simpa [arm64_norm] using hSelfBr)
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
    · have hNxNe0 : g.next ≠ 0#64 := by simpa [arm64_norm] using hNxZero
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
theorem sepWP_nf_retire_root_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {liveCost peakCost : Nat}
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
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk liveCost peakCost st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hAllFree : (g.availMask ||| g.freedMask) + (1#32 <<< idx) = (2#32 <<< g.lastIdx) - 1#32)
    (hMpPos : 0 < g.maplen)
    (hDeq : DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      ((maddrs.ctx ↦ₛ { st.ctx with active := active1, usageByClass := usage1 }.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) bvDeq ∗
       NfAllFreeFrame fuel γ st s0)
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom := by
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
  · wp_step
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
    · rw [← hSeqRead]
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
      · exact sepWP_nf_retire_root_from_1fc_fine hb hFuel
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
    · wp_step
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
      · exact sepWP_nf_retire_root_from_1fc_fine hb hFuel
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
theorem sepWP_nf_allFree_to_1d4_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {liveCost peakCost : Nat}
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
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk liveCost peakCost st)
    (hKeep : EmptyGroupKeepWf st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hCont : NfDeqCont b (s0.readReg64 .lr) st g (NfAllFreeFrame fuel γ st s0) s0 s
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      ((maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       NfAllFreeFrame fuel γ st s0)
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom := by
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
  wp_step
  · rcases (hwf.groups_wf g hg).1 with hSc48 | hSc63
    · have hScProps := sc_cmp47_and_active_off_fin ⟨g.sc, hSc48⟩
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
      · apply step_ldr64_fast (b + 0x7c#64) (b + 0x80#64) (g.metaPtr + 32#64) g.packedWord
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
        · have hLastNe0 : g.lastIdx ≠ 0 := by
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
            exact sepWP_nf_at_0e4_fine hb hFuel (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
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
        · wp_step
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
              exact sepWP_nf_at_0e4_fine hb hFuel (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
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
    · obtain ⟨_, hNx0, _, hDeq63⟩ := dequeue_sc63 hwf hg hSc63
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

/-! ## Fuel-Indexed Plain Specification -/

noncomputable def nontrivialFreeFuelFinePlainSpec [MallocngMultiPlacement]
    (k fuel : Nat) (γ : GhostName) (brkStart : BitVec 64) (liveCost peakCost : Nat)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat) : Spec Unit :=
  { pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = g.metaPtr ∧
       s0.readReg64 .x1 = BitVec.ofNat 64 idx ∧
       g ∈ st.groups ∧
       ∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .claimed⌝ ∗
      stackFrameAt s0.sp (32 * (fuel + 1)) ∗
      MallocngRoTablesA maddrs ∗
      MallocngCoreStInflightA (k + 1) γ maddrs brkStart s0.brk liveCost peakCost st
    post := fun (_ : Unit) s0 sf =>
      ∃∗ st' : MallocngSt,
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧
         sf.mem.perm = s0.mem.perm ∧ st'.reservedMetas = st.reservedMetas ∧
         st'.metaAreas = st.metaAreas ∧
         SameLiveUserSub st' st ∧
         totalLiveCount st' ≤ totalLiveCount st ∧
         (dynamicRootRegions st').length ≤ (dynamicRootRegions st).length⌝ ∗
        stackFrameAt s0.sp (32 * (fuel + 1)) ∗ MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightA k γ maddrs brkStart s0.brk liveCost peakCost st' ∗
        NfRetSep st st' (sf.readReg64 .x0) (sf.readReg64 .x1) }

end LibsignalBinary.Heap.Fine
