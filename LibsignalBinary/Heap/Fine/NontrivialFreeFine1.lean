/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.FreeSubHelpers
public import LibsignalBinary.Heap.Fine.VendorFree.PlacedNontrivialFreeStage2

/-!
# Fine-Grained Placed `nontrivial_free` Stage 1

Strengthens the `nontrivial_free` (`blk05`) epilogue, commit, `free_meta`, non-all-free queueing,
and root-group retirement tail lemmas from `VendorFree` with `SameLiveUserSub st' st` inside
`NfFuelFinePost`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic ProofLib.ProgramReflection
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open LibsignalBinary.Heap.Fine.VendorFree
open scoped LibsignalBinary.Heap.Fine.VendorFree

/-! ## `NfFuelFinePost`, Epilogue, Commit, and `free_meta` -/

noncomputable def NfFuelFinePost [MallocngMultiPlacement]
    (k fuel : Nat) (γ : GhostName) (brkStart : BitVec 64) (liveCost peakCost : Nat)
    (st : MallocngSt) (s0 sf : State) (P_f : SepProp) : Prop :=
  (P_f ⊢ ∃∗ st' : MallocngSt,
    ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧
     sf.mem.perm = s0.mem.perm ∧ st'.reservedMetas = st.reservedMetas ∧
     st'.metaAreas = st.metaAreas ∧
     SameLiveUserSub st' st ∧
     totalLiveCount st' ≤ totalLiveCount st ∧
     (dynamicRootRegions st').length ≤ (dynamicRootRegions st).length⌝ ∗
    stackFrameAt s0.sp (32 * (fuel + 1)) ∗ MallocngRoTablesA maddrs ∗
    MallocngCoreStInflightA k γ maddrs brkStart s0.brk liveCost peakCost st' ∗
    NfRetSep st st' (sf.readReg64 .x0) (sf.readReg64 .x1)) ∧
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

theorem sepWP_nf_epilogue_490_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {liveCost peakCost : Nat}
    {st st' : MallocngSt} {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x490#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf' : MallocngWFInflight k maddrs.base brkStart s0.brk liveCost peakCost st')
    (hRes : st'.reservedMetas = st.reservedMetas)
    (hMa : st'.metaAreas = st.metaAreas)
    (hSub : SameLiveUserSub st' st)
    (hCnt : totalLiveCount st' ≤ totalLiveCount st)
    (hDynLen : (dynamicRootRegions st').length ≤ (dynamicRootRegions st).length) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st' ∗
       (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗
       ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
       ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
       MappedSet st'.masterDom (OwnedMappedByte st') ∗
       NfRetSep st st' (s.readReg64 .x0) (s.readReg64 .x1))
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom := by
  have _ := hb
  have hspAl : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact spAligned_sub32 (by simpa [State.spAligned] using hspAl0)
  have ha16 : s0.sp - 32#64 + 16#64 = s0.sp - 16#64 := by bv_arith
  have ha24 : s0.sp - 16#64 + 8#64 = s0.sp - 8#64 := by bv_arith
  have ha8  : s0.sp - 32#64 + 8#64 = s0.sp - 24#64 := by bv_arith
  have ha32 : s0.sp - 32#64 + 32#64 = s0.sp := by bv_arith
  dsimp only [nfStackSaved]
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ⟨?_, by simp [arm64_norm], ?_⟩
  · refine Entails.sepExists_right st' ?_
    refine Entails.pure_right ⟨hProc, hbrk, hProc.2.2.1, hperm, hRes, hMa, hSub, hCnt, hDynLen⟩ ?_
    rw [coreStInflightA_eq_nfParts, pure_sepConj_of_true hwf']
    simp only [arm64_norm]
    refine Entails.trans (repack_nfStack_rest s0.sp fuel hFuel s0 _) ?_
    sep_frame
  · obtain ⟨h21, h22, h23, h24, h25, h26, h27, h28, hv⟩ := hcs
    exact ⟨by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using h21, by simpa [arm64_norm] using h22,
      by simpa [arm64_norm] using h23, by simpa [arm64_norm] using h24,
      by simpa [arm64_norm] using h25, by simpa [arm64_norm] using h26,
      by simpa [arm64_norm] using h27, by simpa [arm64_norm] using h28,
      by simp [arm64_norm], by simpa [calleeSavedVRegs] using hv⟩

theorem sepWP_nf_commit_474_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {liveCost peakCost : Nat}
    {st st' : MallocngSt} {gPre gPost : GroupDesc} {self32 : BitVec 32}
    {ByteRest : SepProp} {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x474#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = gPre.metaPtr) (hw1 : s.readReg32 .x1 = self32)
    (hmAlign : gPre.metaPtr.toNat % 8 = 0) (hmFit : gPre.metaPtr.toNat + 40 ≤ 2 ^ 48)
    (hMetaPtrEq : gPost.metaPtr = gPre.metaPtr)
    (hMetaBytesEq : { gPre with freedMask := gPre.freedMask ||| self32 }.metaBytes = gPost.metaBytes)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf' : MallocngWFInflight k maddrs.base brkStart s0.brk liveCost peakCost st')
    (hRes : st'.reservedMetas = st.reservedMetas)
    (hMa : st'.metaAreas = st.metaAreas)
    (hSub : SameLiveUserSub st' st)
    (hCnt : totalLiveCount st' ≤ totalLiveCount st)
    (hDynEq : dynamicRootRegions st' = dynamicRootRegions st)
    (hByteEq : ((gPost.metaPtr ↦ₛ gPost.metaBytes) ∗ ByteRest) =
      ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st' ∗
       (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗ (gPre.metaPtr ↦ₛ gPre.metaBytes) ∗ ByteRest ∗
       ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
       MappedSet st'.masterDom (OwnedMappedByte st'))
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom := by
  have _ := hb
  have hAl28 : MemWidth.isAligned .W32 (gPre.metaPtr + 28#64) = true := by
    apply isAligned_w32_of_mod4
    have h48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    rw [BitVec.toNat_add_of_lt (by change gPre.metaPtr.toNat + 28 < 2 ^ 64; omega)]
    change (gPre.metaPtr.toNat + 28) % 4 = 0; omega
  wp_step
  have hFocus : (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st' ∗
       (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗ (gPre.metaPtr ↦ₛ gPre.metaBytes) ∗ ByteRest ∗
       ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
       MappedSet st'.masterDom (OwnedMappedByte st')) =
      (((gPre.metaPtr + 28#64) ↦₃₂ gPre.freedMask) ∗
       (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
        MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st' ∗
        (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗
        ((gPre.metaPtr ↦₆₄ gPre.prev) ∗ ((gPre.metaPtr + 8#64) ↦₆₄ gPre.next) ∗
         ((gPre.metaPtr + 16#64) ↦₆₄ gPre.mem) ∗ ((gPre.metaPtr + 24#64) ↦₃₂ gPre.availMask) ∗
         ((gPre.metaPtr + 32#64) ↦₆₄ gPre.packedWord)) ∗ ByteRest ∗
        ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
        MappedSet st'.masterDom (OwnedMappedByte st'))) := by
    rw [metaBytes_eq_cells gPre]; ac_rfl
  rw [hFocus]
  refine SepWP.seq (sepWP_nf_or32_loop_478 hb hAl28 (_ + 1) _ (Nat.lt_succ_self _)
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm])
    (by simpa [arm64_norm] using hw1) hProc
    (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
        exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
               by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
               by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
               by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
               by simpa [calleeSavedVRegs] using cv⟩)) ?_
  intro s1 P1 hpc1 hrun1 ⟨hsp1, hbrk1, hperm1, hProc1, hcs1, _hx0_1, hx1_1, hP1⟩
  have hUnfocus : (((gPre.metaPtr + 28#64) ↦₃₂ (gPre.freedMask ||| self32)) ∗
       (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
        MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st' ∗
        (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗
        ((gPre.metaPtr ↦₆₄ gPre.prev) ∗ ((gPre.metaPtr + 8#64) ↦₆₄ gPre.next) ∗
         ((gPre.metaPtr + 16#64) ↦₆₄ gPre.mem) ∗ ((gPre.metaPtr + 24#64) ↦₃₂ gPre.availMask) ∗
         ((gPre.metaPtr + 32#64) ↦₆₄ gPre.packedWord)) ∗ ByteRest ∗
        ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
        MappedSet st'.masterDom (OwnedMappedByte st'))) ⊢
      (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st' ∗
       (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗
       ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
       ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
       MappedSet st'.masterDom (OwnedMappedByte st') ∗
       NfRetSep st st' (s1.readReg64 .x0) (s1.readReg64 .x1)) := by
    have hCellsUpd := metaBytes_eq_cells { gPre with freedMask := gPre.freedMask ||| self32 }
    dsimp only [] at hCellsUpd
    rw [hMetaBytesEq] at hCellsUpd
    rw [hx1_1]; unfold NfRetSep; simp only [↓reduceIte]
    rw [sepConj_comm (MappedSet st'.masterDom (OwnedMappedByte st')) ⌜_⌝, pure_sepConj_of_true hDynEq]
    rw [← hByteEq, hMetaPtrEq, hCellsUpd]
    sep_frame
  exact SepWP.weaken_pre (Entails.trans hP1 hUnfocus)
    (sepWP_nf_epilogue_490_fine hb hFuel hpc1 hrun1
      (hsp1.trans (by simpa [arm64_norm] using hsp)) hspAl0 hProc1
      (hbrk1.trans (by simpa [arm64_norm] using hbrk))
      (hperm1.trans (by simpa [arm64_norm] using hperm)) hcs1
      hwf' hRes hMa hSub hCnt (by rw [hDynEq]; exact Nat.le_refl _))

theorem sepWP_nf_freeMeta_224_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {liveCost peakCost : Nat}
    {st st_m : MallocngSt} {gZero : GroupDesc} {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x224#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = gZero.metaPtr) (hx20 : s.readReg64 .x20 = pageOf maddrs.ctx)
    (hmRes : gZero.metaPtr ∈ st_m.reservedMetas)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf_m : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk liveCost peakCost st_m)
    (hRes_m : st_m.reservedMetas.erase gZero.metaPtr = st.reservedMetas)
    (hMa_m : st_m.metaAreas = st.metaAreas)
    (hSub_m : SameLiveUserSub st_m st)
    (hCnt_m : totalLiveCount st_m ≤ totalLiveCount st)
    (hDynLen_m : (dynamicRootRegions st_m).length ≤ (dynamicRootRegions st).length) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st_m ∗
       (maddrs.ctx ↦ₛ st_m.ctx.toBytes) ∗ (gZero.metaPtr ↦ₛ gZero.metaBytes) ∗
       ByteMap st_m.masterDom (OwnedRwByte st_m) st_m.byteVal ∗
       ProtNoneByteMap st_m.masterDom (OwnedProtNoneByte st_m) st_m.byteVal ∗
       MappedSet st_m.masterDom (OwnedMappedByte st_m) ∗
       NfRetSep st st_m (s.readReg64 .x0) (s.readReg64 .x1))
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom := by
  have _ := hb
  let m := gZero.metaPtr
  obtain ⟨w24, hMetaCells⟩ := metaBytes_eq_cells64 gZero
  obtain ⟨CtxRest, hCtxRead, hCtxWrite⟩ :=
    ctx_focus_update_freeMetaHead maddrs.ctx st_m.ctx m
  have hm24 : (m + 16#64) + 8#64 = m + 24#64 := by bv_arith
  rw [hMetaCells, hCtxRead, ← hm24]
  wp_step
  have hCtx20 : pageOf maddrs.ctx + lo12Of maddrs.ctx = maddrs.ctx := pageOf_add_lo12Of maddrs.ctx
  wp_stp64_p m1 hm1
  wp_stp64_p m2 hm2
  wp_step
  wp_str64_p m3 hm3
  wp_step
  wp_if hHead0
  · have hHd0 : st_m.ctx.freeMetaHead = 0#64 := by simpa [arm64_norm] using hHead0
    obtain ⟨hByte1, hProt1, hMap1, hWf1, hRes1, hDyn1, hCnt1⟩ :=
      free_recycle_reserved_meta_empty hwf_m hmRes hHd0
    wp_stp64_p m4 hm4
    wp_str64_p m5 hm5
    wp_step
    rw [hm24]
    refine SepWP.weaken_pre ?_ (sepWP_nf_epilogue_490_fine hb hFuel
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simpa [arm64_norm] using hsp) hspAl0
      (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
      (by simpa [arm64_norm] using hbrk)
      (hm5.trans (hm4.trans (hm3.trans (hm2.trans (hm1.trans hperm)))))
      (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
          exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                 by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                 by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                 by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                 by simpa [calleeSavedVRegs] using cv⟩)
      hWf1 (hRes1.trans hRes_m) hMa_m
      (SameLiveUserSub.trans (sameLiveUserSub_of_groups_eq hwf_m.groups_nodup.1 rfl rfl rfl) hSub_m)
      (by omega) (by rw [hDyn1]; exact hDynLen_m))
    dsimp only [m, NfStaticRest] at hCtxWrite hByte1 ⊢
    simp only [arm64_norm]
    rw [← hCtxWrite, ← hByte1, freeMeta_toBytes_cells gZero.metaPtr gZero.metaPtr gZero.metaPtr,
        hProt1, hMap1, nfRetSep_congr_dyn _ _ hDyn1]
    sep_frame
  · have hHdNe0 : st_m.ctx.freeMetaHead ≠ 0#64 := by simpa [arm64_norm] using hHead0
    let head := st_m.ctx.freeMetaHead
    obtain ⟨hdFm, _, tlFm, _, hHdPtr, hTlPtr, hSubHd, hSubTl, hReadHd0, hReadTl0,
            hReadHdAfterTl, hByte1, hProt1, hMap1, hWf1, hRes1, hDyn1, hCnt1⟩ :=
      free_recycle_reserved_meta_nonempty hwf_m hmRes hHdNe0
    let tlUpd : FreeMetaDesc := { tlFm with next := m }
    let hdMid : FreeMetaDesc := { hdFm with next := if head == hdFm.prev then m else hdFm.next }
    let hdUpd : FreeMetaDesc := { hdFm with prev := m, next := if head == hdFm.prev then m else hdFm.next }
    let bvTl := writeBytesToMap st_m.byteVal hdFm.prev tlUpd.toBytes
    wp_str64_p m4 hm4
    have hBmHd0 := (byteMap_update40 hwf_m.masterDom_wf.1 st_m.byteVal (m := head)
      (bs := hdFm.toBytes) (FreeMetaDesc.toBytes_length _) hSubHd).1
    have hHdCells0 : (head ↦ₛ hdFm.toBytes) =
        ((head ↦₆₄ hdFm.prev) ∗ ((head + 8#64) ↦₆₄ hdFm.next) ∗
         ((head + 16#64) ↦₆₄ 0#64) ∗ ((head + 24#64) ↦₆₄ 0#64) ∗ ((head + 32#64) ↦₆₄ 0#64)) := by
      have hc := freeMeta_toBytes_cells head hdFm.prev hdFm.next
      cases hdFm; dsimp only [] at hHdPtr hc ⊢; subst hHdPtr; exact hc
    rw [hBmHd0, hReadHd0, hHdCells0]
    wp_step
    rw [← hHdCells0, ← hReadHd0, ← hBmHd0]
    wp_str64_p m5 hm5
    have ⟨hBmTl0, hBmTlW⟩ := byteMap_update40 hwf_m.masterDom_wf.1 st_m.byteVal (m := hdFm.prev)
      (bs := tlUpd.toBytes) (FreeMetaDesc.toBytes_length _) hSubTl
    have hTlCells0 : (hdFm.prev ↦ₛ tlFm.toBytes) =
        ((hdFm.prev ↦₆₄ tlFm.prev) ∗ ((hdFm.prev + 8#64) ↦₆₄ tlFm.next) ∗
         ((hdFm.prev + 16#64) ↦₆₄ 0#64) ∗ ((hdFm.prev + 24#64) ↦₆₄ 0#64) ∗ ((hdFm.prev + 32#64) ↦₆₄ 0#64)) := by
      have hc := freeMeta_toBytes_cells hdFm.prev tlFm.prev tlFm.next
      cases tlFm; dsimp only [] at hTlPtr hc ⊢; subst hTlPtr; exact hc
    have hTlCells1 : ((hdFm.prev ↦₆₄ tlFm.prev) ∗ ((hdFm.prev + 8#64) ↦₆₄ m) ∗
         ((hdFm.prev + 16#64) ↦₆₄ 0#64) ∗ ((hdFm.prev + 24#64) ↦₆₄ 0#64) ∗ ((hdFm.prev + 32#64) ↦₆₄ 0#64)) =
        (hdFm.prev ↦ₛ tlUpd.toBytes) := by
      have hc := freeMeta_toBytes_cells hdFm.prev tlFm.prev m
      cases tlFm; dsimp only [tlUpd] at hTlPtr hc ⊢; subst hTlPtr; exact hc.symm
    rw [hBmTl0, hReadTl0, hTlCells0]
    wp_str64_p m6 hm6
    wp_step
    try rw [hx19]
    dsimp only [m] at hTlCells1
    rw [hTlCells1, hBmTlW]
    have ⟨hBmHd1, hBmHdW⟩ := byteMap_update40 hwf_m.masterDom_wf.1 bvTl (m := head)
      (bs := hdUpd.toBytes) (FreeMetaDesc.toBytes_length _) hSubHd
    have hHdCellsMid : (head ↦ₛ hdMid.toBytes) =
        ((head ↦₆₄ hdFm.prev) ∗ ((head + 8#64) ↦₆₄ hdMid.next) ∗
         ((head + 16#64) ↦₆₄ 0#64) ∗ ((head + 24#64) ↦₆₄ 0#64) ∗ ((head + 32#64) ↦₆₄ 0#64)) := by
      have hc := freeMeta_toBytes_cells head hdFm.prev hdMid.next
      cases hdFm; dsimp only [hdMid] at hHdPtr hc ⊢; subst hHdPtr; exact hc
    have hHdCellsUpd : ((head ↦₆₄ m) ∗ ((head + 8#64) ↦₆₄ hdMid.next) ∗
         ((head + 16#64) ↦₆₄ 0#64) ∗ ((head + 24#64) ↦₆₄ 0#64) ∗ ((head + 32#64) ↦₆₄ 0#64)) =
        (head ↦ₛ hdUpd.toBytes) := by
      have hc := freeMeta_toBytes_cells head m hdMid.next
      cases hdFm; dsimp only [hdUpd, hdMid] at hHdPtr hc ⊢; subst hHdPtr; exact hc.symm
    rw [hBmHd1, hReadHdAfterTl, hHdCellsMid]
    wp_str64_p m7 hm7
    wp_step
    rw [hm24]
    refine SepWP.weaken_pre ?_ (sepWP_nf_epilogue_490_fine hb hFuel
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simpa [arm64_norm] using hsp) hspAl0
      (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
      (by simpa [arm64_norm] using hbrk)
      (hm7.trans (hm6.trans (hm5.trans (hm4.trans (hm3.trans (hm2.trans (hm1.trans hperm)))))))
      (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
          exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                 by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                 by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                 by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                 by simpa [calleeSavedVRegs] using cv⟩)
      hWf1 (hRes1.trans hRes_m) hMa_m
      (SameLiveUserSub.trans (sameLiveUserSub_of_groups_eq hwf_m.groups_nodup.1 rfl rfl rfl) hSub_m)
      (by omega) (by rw [hDyn1]; exact hDynLen_m))
    dsimp only [m, NfStaticRest] at hHdCellsUpd ⊢
    simp only [arm64_norm]
    rw [hCtxRead, ← hByte1, freeMeta_toBytes_cells gZero.metaPtr hdFm.prev head,
        ← hBmHdW, ← hHdCellsUpd, hProt1, hMap1, nfRetSep_congr_dyn _ _ hDyn1]
    sep_frame

/-! ## Non-All-Free Slot Release and Group Queueing -/

private theorem setWidth64_eq_zero_iff32 (v : BitVec 32) :
    v.setWidth 64 = 0#64 ↔ v = 0#32 := by
  constructor
  · intro h; revert h; bv_robdd
  · rintro rfl; rfl

set_option maxHeartbeats 400000 in
theorem sepWP_nf_enqueue_nonempty_45c_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {liveCost peakCost : Nat}
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {head : BitVec 64}
    {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x45c#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hw1 : s.readReg32 .x1 = 1#32 <<< idx)
    (hx3 : s.readReg64 (.gpr 3#5) = head)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk liveCost peakCost st)
    (hFq : FullQueueKeepWf st)
    (hg : g ∈ st.groups) (hSc48 : g.sc < 48) (hActLt : g.sc < st.ctx.active.length)
    (hHeadDef : (st.ctx.active[g.sc]'hActLt) = head)
    (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hAv0 : g.availMask = 0#32) (hFr0 : g.freedMask = 0#32)
    (hNeNat : (g.availMask ||| (g.freedMask ||| 1#32 <<< idx)).toNat ≠ 2 ^ g.cnt - 1)
    (hHeadNe0 : st.ctx.active[g.sc]'hActLt ≠ 0#64)
    (hHeadNeG : st.ctx.active[g.sc]'hActLt ≠ g.metaPtr) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st ∗
       (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ((g.metaPtr ↦₆₄ g.prev) ∗ ((g.metaPtr + 8#64) ↦₆₄ g.next) ∗
        ((g.metaPtr + 16#64) ↦₆₄ g.mem) ∗ ((g.metaPtr + 24#64) ↦₃₂ g.availMask) ∗
        ((g.metaPtr + 28#64) ↦₃₂ g.freedMask) ∗ ((g.metaPtr + 32#64) ↦₆₄ g.packedWord)) ∗
       ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
       MappedSet st.masterDom (OwnedMappedByte st))
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom := by
  have _ := hb
  obtain ⟨_, hmAl, hmFit, _, hOwnG⟩ := meta_ownedRw_of_mem_groups hwf hg
  obtain ⟨_, _, hdG, hhdG, tlG, htlG, hHdPtr, _, hTlPtr, _, hHdNeG', hTlNeG',
          hReadHdAfterTl, hWf1, hRwEq, hProt1, hMap1, hDyn1, hCnt1⟩ :=
    free_queue_nonempty_active hwf hFq hg hSc48 hIdx hClaimed hAv0 hFr0 hNeNat hHeadNe0 hHeadNeG
  rw [hHeadDef] at hHdPtr hReadHdAfterTl hWf1 hRwEq hProt1 hMap1 hDyn1 hCnt1
  obtain ⟨_, _, _, hReadHd0, hOwnHd0⟩ := meta_ownedRw_of_mem_groups hwf hhdG
  obtain ⟨_, _, _, hReadTl0, hOwnTl0⟩ := meta_ownedRw_of_mem_groups hwf htlG
  let PG : BitVec 64 → Prop := fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a
  have hOwnHd : ∀ a, InRegion head 40 a → PG a ∧ a ∈ st.masterDom := by
    intro a ha
    have ha' : InRegion hdG.metaPtr 40 a := hHdPtr ▸ ha
    exact ⟨⟨(hOwnHd0 a ha').1, fun haG =>
      metaSlot_disjoint_of_ne hwf (group_mem_allMetaSlots hwf hhdG)
        (group_mem_allMetaSlots hwf hg) hHdNeG' ha' haG⟩, (hOwnHd0 a ha').2⟩
  have hOwnTl : ∀ a, InRegion hdG.prev 40 a → PG a ∧ a ∈ st.masterDom := by
    intro a ha
    have ha' : InRegion tlG.metaPtr 40 a := hTlPtr ▸ ha
    exact ⟨⟨(hOwnTl0 a ha').1, fun haG =>
      metaSlot_disjoint_of_ne hwf (group_mem_allMetaSlots hwf htlG)
        (group_mem_allMetaSlots hwf hg) hTlNeG' ha' haG⟩, (hOwnTl0 a ha').2⟩
  let tlUpd : GroupDesc := { tlG with next := g.metaPtr }
  let hdMid : GroupDesc := { hdG with next := if head == hdG.prev then g.metaPtr else hdG.next }
  let hdUpd : GroupDesc := { hdG with prev := g.metaPtr, next := if head == hdG.prev then g.metaPtr else hdG.next }
  let gPre : GroupDesc := { g with prev := hdG.prev, next := head }
  let g1 : GroupDesc := mkQueuedFullGroup g hdG.prev head idx
  let bvTl := writeBytesToMap st.byteVal tlG.metaPtr tlUpd.metaBytes
  let bvHd := writeBytesToMap bvTl head hdUpd.metaBytes
  wp_str64_p m1 hm1
  have hBmHd0 := (byteMap_update40 hwf.masterDom_wf.1 st.byteVal (P := PG) (m := head)
    (bs := hdG.metaBytes) (GroupDesc.metaBytes_length _) hOwnHd).1
  have hHdCells0 : (head ↦ₛ hdG.metaBytes) =
      ((head ↦₆₄ hdG.prev) ∗ ((head + 8#64) ↦₆₄ hdG.next) ∗
       ((head + 16#64) ↦₆₄ hdG.mem) ∗ ((head + 24#64) ↦₃₂ hdG.availMask) ∗
       ((head + 28#64) ↦₃₂ hdG.freedMask) ∗ ((head + 32#64) ↦₆₄ hdG.packedWord)) := by
    rw [← hHdPtr]; exact metaBytes_eq_cells hdG
  have hReadHd0' : readBytesFromMap st.byteVal head 40 = hdG.metaBytes := hHdPtr ▸ hReadHd0
  rw [hBmHd0, hReadHd0', hHdCells0]
  wp_step
  rw [← hHdCells0, ← hReadHd0', ← hBmHd0]
  wp_str64_p m2 hm2
  have ⟨hBmTl0, hBmTlW⟩ := byteMap_update40 hwf.masterDom_wf.1 st.byteVal (P := PG) (m := hdG.prev)
    (bs := tlUpd.metaBytes) (GroupDesc.metaBytes_length _) hOwnTl
  have hTlCells0 : (hdG.prev ↦ₛ tlG.metaBytes) =
      ((hdG.prev ↦₆₄ tlG.prev) ∗ ((hdG.prev + 8#64) ↦₆₄ tlG.next) ∗
       ((hdG.prev + 16#64) ↦₆₄ tlG.mem) ∗ ((hdG.prev + 24#64) ↦₃₂ tlG.availMask) ∗
       ((hdG.prev + 28#64) ↦₃₂ tlG.freedMask) ∗ ((hdG.prev + 32#64) ↦₆₄ tlG.packedWord)) := by
    rw [← hTlPtr]; exact metaBytes_eq_cells tlG
  have hTlCells1 :
      ((hdG.prev ↦₆₄ tlG.prev) ∗ ((hdG.prev + 8#64) ↦₆₄ g.metaPtr) ∗
       ((hdG.prev + 16#64) ↦₆₄ tlG.mem) ∗ ((hdG.prev + 24#64) ↦₃₂ tlG.availMask) ∗
       ((hdG.prev + 28#64) ↦₃₂ tlG.freedMask) ∗ ((hdG.prev + 32#64) ↦₆₄ tlG.packedWord)) =
      (hdG.prev ↦ₛ tlUpd.metaBytes) := by
    have hc := metaBytes_eq_cells tlUpd
    dsimp only [tlUpd] at hc ⊢; rw [hTlPtr] at hc; exact hc.symm
  have hReadTl0' : readBytesFromMap st.byteVal hdG.prev 40 = tlG.metaBytes := hTlPtr ▸ hReadTl0
  rw [hBmTl0, hReadTl0', hTlCells0]
  wp_str64_p m3 hm3
  wp_step
  rw [hTlCells1, hBmTlW, ← hTlPtr]
  have ⟨hBmHd1, hBmHdW⟩ := byteMap_update40 hwf.masterDom_wf.1 bvTl (P := PG) (m := head)
    (bs := hdUpd.metaBytes) (GroupDesc.metaBytes_length _) hOwnHd
  have hHdCellsMid : (head ↦ₛ hdMid.metaBytes) =
      ((head ↦₆₄ hdG.prev) ∗ ((head + 8#64) ↦₆₄ hdMid.next) ∗
       ((head + 16#64) ↦₆₄ hdG.mem) ∗ ((head + 24#64) ↦₃₂ hdG.availMask) ∗
       ((head + 28#64) ↦₃₂ hdG.freedMask) ∗ ((head + 32#64) ↦₆₄ hdG.packedWord)) := by
    have hc := metaBytes_eq_cells hdMid
    dsimp only [hdMid] at hc ⊢; rw [hHdPtr] at hc; exact hc
  have hHdCellsUpd :
      ((head ↦₆₄ g.metaPtr) ∗ ((head + 8#64) ↦₆₄ hdMid.next) ∗
       ((head + 16#64) ↦₆₄ hdG.mem) ∗ ((head + 24#64) ↦₃₂ hdG.availMask) ∗
       ((head + 28#64) ↦₃₂ hdG.freedMask) ∗ ((head + 32#64) ↦₆₄ hdG.packedWord)) =
      (head ↦ₛ hdUpd.metaBytes) := by
    have hc := metaBytes_eq_cells hdUpd
    dsimp only [hdUpd, hdMid] at hc ⊢; rw [hHdPtr] at hc; exact hc.symm
  rw [hBmHd1, hReadHdAfterTl, hHdCellsMid]
  wp_str64_p m4 hm4
  have hByte1 : ((g1.metaPtr ↦ₛ g1.metaBytes) ∗ ByteMap st.masterDom PG bvHd) =
      ByteMap st.masterDom (OwnedRwByte
        { st with
          groups := updateQueuedGroups st.groups head hdG.prev g1
          activeLists := st.activeLists.set g.sc ((st.activeLists[g.sc]'(by rw [hwf.ctx_lens.2.2.2.2.2]; exact hSc48)) ++ [g.metaPtr])
          byteVal := writeBytesToMap bvHd g.metaPtr g1.metaBytes })
        (writeBytesToMap bvHd g.metaPtr g1.metaBytes) := by
    have hAbs := (byteMap_update40 hwf.masterDom_wf.1 bvHd (P := OwnedRwByte st) (m := g.metaPtr)
      (bs := g1.metaBytes) (GroupDesc.metaBytes_length _) hOwnG).2
    dsimp only [g1, mkQueuedFullGroup, PG] at hAbs ⊢
    exact hAbs.trans (SetSep_congr (fun a _ => (hRwEq a).symm) (fun _ _ _ => rfl))
  apply SepWP.weaken_pre
  rotate_left
  · exact sepWP_nf_commit_474_fine hb hFuel
      (gPre := gPre) (gPost := g1) (self32 := 1#32 <<< idx)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simpa only [arm64_norm] using hx19) (by simpa only [arm64_norm] using hw1)
      hmAl hmFit rfl (metaBytes_congr rfl rfl rfl rfl rfl rfl)
      (by simpa only [arm64_norm] using hsp) hspAl0
      (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
      (by simpa only [arm64_norm] using hbrk) (hm4.trans (hm3.trans (hm2.trans (hm1.trans hperm))))
      (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
          exact ⟨by simpa only [arm64_norm] using c21, by simpa only [arm64_norm] using c22,
                 by simpa only [arm64_norm] using c23, by simpa only [arm64_norm] using c24,
                 by simpa only [arm64_norm] using c25, by simpa only [arm64_norm] using c26,
                 by simpa only [arm64_norm] using c27, by simpa only [arm64_norm] using c28,
                 by simpa [calleeSavedVRegs] using cv⟩)
      hWf1 rfl rfl
      (sameLiveUserSub_updateQueuedGroups hwf.groups_nodup.1 hg hIdx hClaimed head hdG.prev _ _)
      (by omega) hDyn1 hByte1
  · have hPreCells := metaBytes_eq_cells gPre
    dsimp only [gPre] at hPreCells
    dsimp only [NfStaticRest]
    simp only [arm64_norm]
    rw [hProt1, hMap1, hPreCells, hTlPtr, ← hBmHdW, ← hHdCellsUpd]
    sep_frame

set_option maxHeartbeats 400000 in
theorem sepWP_nf_nonAllFree_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {liveCost peakCost : Nat}
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x50#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = g.metaPtr)
    (hw1 : s.readReg32 .x1 = 1#32 <<< idx)
    (hw3 : s.readReg32 .x3 = g.freedMask ||| g.availMask)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 g.sc)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk liveCost peakCost st)
    (hFq : FullQueueKeepWf st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hNotAll : (g.availMask ||| g.freedMask) + (1#32 <<< idx) ≠ (2#32 <<< g.lastIdx) - 1#32) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st ∗
       (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
       MappedSet st.masterDom (OwnedMappedByte st))
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom := by
  have _ := hb
  obtain ⟨hSc48, _, hNeNat⟩ := claimed_notAllFree_props hwf hg hIdx hClaimed hNotAll
  obtain ⟨_, hmAl, hmFit, hReadG, hOwnG⟩ := meta_ownedRw_of_mem_groups hwf hg
  have hw3' : (s.readReg64 (.gpr 3#5)).truncate 32 = g.freedMask ||| g.availMask := hw3
  have hx0' : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 g.sc := hx0
  have hx19' : s.readReg64 (.gpr 19#5) = g.metaPtr := hx19
  wp_step
  wp_if_nd hW3
  · have hMaskNe0 : g.freedMask ||| g.availMask ≠ 0#32 :=
      fun h0 => hW3 (by simp [h0])
    have hInActive : ∀ hScLt : g.sc < st.activeLists.length, g.metaPtr ∈ st.activeLists[g.sc]'hScLt := by
      intro hScLt
      have hAct := hwf.active_wf g.sc (by rw [hwf.ctx_lens.1]; exact hSc48) hScLt
      exact Classical.byContradiction fun hNotIn => by
        obtain ⟨hAv0, hFr0, _⟩ := (hAct.2.2.2.1 g hg rfl).2 hNotIn
        exact hMaskNe0 (by simp [hAv0, hFr0])
    obtain ⟨hProt1, hMap1, hByte1, hDyn1, hCnt1, hWf1, _⟩ :=
      free_set_freedMask_keep hwf hg hIdx hClaimed hSc48 hInActive (Or.inl hNotAll)
    have hBmG0 := (byteMap_update40 hwf.masterDom_wf.1 st.byteVal
      (bs := (mkFreedKeepGroup g idx).metaBytes) (GroupDesc.metaBytes_length _) hOwnG).1
    rw [hBmG0, hReadG]
    apply SepWP.weaken_pre
    rotate_left
    · exact sepWP_nf_commit_474_fine hb hFuel
        (gPre := g) (gPost := mkFreedKeepGroup g idx) (self32 := 1#32 <<< idx)
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simpa [arm64_norm] using hx19) (by simpa [arm64_norm] using hw1)
        hmAl hmFit rfl (metaBytes_congr rfl rfl rfl rfl rfl rfl)
        (by simpa [arm64_norm] using hsp) hspAl0
        (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
        (by simpa [arm64_norm] using hbrk) (by simpa [arm64_norm] using hperm)
        (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
            exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                   by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                   by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                   by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                   by simpa [calleeSavedVRegs] using cv⟩)
        hWf1 rfl rfl
        (sameLiveUserSub_mkFreedKeepGroup hwf.groups_nodup.1 hg hIdx hClaimed _)
        (by omega) hDyn1 hByte1
    · dsimp only [NfStaticRest]
      rw [hProt1, hMap1]
      sep_frame
  · have ⟨hFr0, hAv0⟩ : g.freedMask = 0#32 ∧ g.availMask = 0#32 := by
      have ⟨h1, h2⟩ : BitVec.setWidth 64 g.freedMask = 0#64 ∧ BitVec.setWidth 64 g.availMask = 0#64 := by
        simpa [arm64_norm] using hW3
      exact ⟨(setWidth64_eq_zero_iff32 _).mp h1, (setWidth64_eq_zero_iff32 _).mp h2⟩
    have hScProps := sc_cmp47_and_active_off_fin ⟨g.sc, hSc48⟩
    have hLeCond : (BitVec.truncate 32 (BitVec.ofNat 64 g.sc)).sle 47#32 = true := hScProps.1
    have hScLsb31 : (BitVec.ofNat 64 g.sc).getLsbD 31 = false := hScProps.2.1
    have hScShrAnd : (BitVec.ofNat 64 g.sc >>> 0 &&& 0xffffffff#64) = BitVec.ofNat 64 g.sc := hScProps.2.2.1
    have hScAnd : (BitVec.ofNat 64 g.sc &&& 0xffffffff#64) = BitVec.ofNat 64 g.sc := hScProps.2.2.2.1
    wp_step
    wp_step
    wp_step
    wp_step
    wp_step
    wp_step
    have hActAddr : maddrs.ctx + ((BitVec.ofNat 64 g.sc + 10#64) <<< 3) =
        maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc) :=
      congrArg (maddrs.ctx + ·) hScProps.2.2.2.2
    obtain ⟨CtxRest, hCtxRead, hCtxWrite⟩ :=
      ctx_focus_update_active maddrs.ctx st.ctx hwf.ctx_lens.1 hSc48 g.metaPtr
    have hActLt : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
    generalize hHeadDef : (st.ctx.active[g.sc]'hActLt) = head at hCtxRead
    rw [hCtxRead]
    apply step_ldr64_fast (b + 0x434#64) (b + 0x438#64)
      (maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc)) head
    · rfl
    · simp only [arm64_norm, hrun]
    · wp_close_fetch_cl
    · rfl
    · simp only [evalAddrMode, extendVal, BitVec.or_zero, arm64_norm]; exact Prod.ext hActAddr rfl
    · wp_sep_access_fast
    · bv_omega
    wp_step
    wp_step
    wp_if_nd hHeadEqBr
    · have hHeadEq0 : head = g.metaPtr := by
        simpa only [arm64_norm, hx19', beq_iff_eq, decide_eq_true_eq] using hHeadEqBr
      have hHeadEq : st.ctx.active[g.sc]'hActLt = g.metaPtr := hHeadDef.trans hHeadEq0
      have hInActive : ∀ hScLt : g.sc < st.activeLists.length, g.metaPtr ∈ st.activeLists[g.sc]'hScLt := by
        intro _
        exact (activeList_head_and_singleton_props hwf hg hSc48).2.2.2.2.2.1 hHeadEq
      obtain ⟨hProt1, hMap1, hByte1, hDyn1, hCnt1, hWf1, _⟩ :=
        free_set_freedMask_keep hwf hg hIdx hClaimed hSc48 hInActive (Or.inl hNotAll)
      have hBmG0 := (byteMap_update40 hwf.masterDom_wf.1 st.byteVal
        (bs := (mkFreedKeepGroup g idx).metaBytes) (GroupDesc.metaBytes_length _) hOwnG).1
      rw [hBmG0, hReadG]
      apply SepWP.weaken_pre
      rotate_left
      · exact sepWP_nf_commit_474_fine hb hFuel
          (gPre := g) (gPost := mkFreedKeepGroup g idx) (self32 := 1#32 <<< idx)
          (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
          (by simpa only [arm64_norm] using hx19) (by simpa only [arm64_norm] using hw1)
          hmAl hmFit rfl (metaBytes_congr rfl rfl rfl rfl rfl rfl)
          (by simpa only [arm64_norm] using hsp) hspAl0
          (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
          (by simpa only [arm64_norm] using hbrk) (by simpa only [arm64_norm] using hperm)
          (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
              exact ⟨by simpa only [arm64_norm] using c21, by simpa only [arm64_norm] using c22,
                     by simpa only [arm64_norm] using c23, by simpa only [arm64_norm] using c24,
                     by simpa only [arm64_norm] using c25, by simpa only [arm64_norm] using c26,
                     by simpa only [arm64_norm] using c27, by simpa only [arm64_norm] using c28,
                     by simpa [calleeSavedVRegs] using cv⟩)
          hWf1 rfl rfl
          (sameLiveUserSub_mkFreedKeepGroup hwf.groups_nodup.1 hg hIdx hClaimed _)
          (by omega) hDyn1 hByte1
      · dsimp only [NfStaticRest]
        rw [← hCtxRead, hProt1, hMap1]
        sep_frame
    · have hHeadNeG0 : head ≠ g.metaPtr := by
        simpa only [arm64_norm, hx19', beq_iff_eq, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] using hHeadEqBr
      have hHeadNeG : st.ctx.active[g.sc]'hActLt ≠ g.metaPtr := fun h => hHeadNeG0 (hHeadDef.symm.trans h)
      have ⟨_, hPv0, hNx0⟩ :=
        (activeList_head_and_singleton_props hwf hg hSc48).2.2.2.2.2.2 hHeadNeG hFr0
      have ⟨hBmG0, _⟩ := byteMap_update40 hwf.masterDom_wf.1 st.byteVal
        (bs := (mkQueuedEmptyGroup g idx).metaBytes) (GroupDesc.metaBytes_length _) hOwnG
      rw [hBmG0, hReadG, metaBytes_eq_cells g]
      wp_step
      wp_step
      wp_step
      wp_step
      wp_step
      wp_if_nd hHead0Br
      · have hHead00 : head = 0#64 := by
          simpa only [arm64_norm, beq_iff_eq, decide_eq_true_eq] using hHead0Br
        have hHead0 : st.ctx.active[g.sc]'hActLt = 0#64 := hHeadDef.trans hHead00
        obtain ⟨_, _, hWf1, hDyn1, hCnt1, hProt1, hMap1, hByte1⟩ :=
          free_queue_empty_active hwf hg hSc48 hIdx hClaimed hNeNat hHead0
        let gPre : GroupDesc := { g with prev := g.metaPtr, next := g.metaPtr }
        wp_stp64_p m1 hm1
        apply step_str64_fast (b + 0x4a0#64) (b + 0x4a4#64)
          (maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc)) g.metaPtr
        · rfl
        · simp only [arm64_norm, hrun]
        · wp_close_fetch_cl
        · rfl
        · simp only [evalAddrMode, extendVal, BitVec.or_zero, arm64_norm]; exact Prod.ext hActAddr rfl
        · simpa only [arm64_norm] using hx19'
        · wp_sep_access_fast
        · bv_omega
        intro m2 hm2 _
        simp only [arm64_norm] at hm2
        wp_step
        apply SepWP.weaken_pre
        rotate_left
        · exact sepWP_nf_commit_474_fine hb hFuel
            (gPre := gPre) (gPost := mkQueuedEmptyGroup g idx) (self32 := 1#32 <<< idx)
            (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
            (by simpa only [arm64_norm] using hx19) (by simpa only [arm64_norm] using hw1)
            hmAl hmFit rfl (metaBytes_congr rfl rfl rfl rfl rfl rfl)
            (by simpa only [arm64_norm] using hsp) hspAl0
            (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
            (by simpa only [arm64_norm] using hbrk) (hm2.trans (hm1.trans hperm))
            (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
                exact ⟨by simpa only [arm64_norm] using c21, by simpa only [arm64_norm] using c22,
                       by simpa only [arm64_norm] using c23, by simpa only [arm64_norm] using c24,
                       by simpa only [arm64_norm] using c25, by simpa only [arm64_norm] using c26,
                       by simpa only [arm64_norm] using c27, by simpa only [arm64_norm] using c28,
                       by simpa [calleeSavedVRegs] using cv⟩)
            hWf1 rfl rfl
            (sameLiveUserSub_mkQueuedEmptyGroup hwf.groups_nodup.1 hg hIdx hClaimed _ _ _)
            (by omega) hDyn1 hByte1
        · have hPreCells := metaBytes_eq_cells gPre
          dsimp only [gPre] at hPreCells
          dsimp only [NfStaticRest]
          simp only [arm64_norm]
          rw [← hCtxWrite, hPreCells, hProt1, hMap1]
          sep_frame
      · have hHeadNe00 : head ≠ 0#64 := by
          simpa only [arm64_norm, beq_iff_eq, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] using hHead0Br
        have hHeadNe0 : st.ctx.active[g.sc]'hActLt ≠ 0#64 := fun h => hHeadNe00 (hHeadDef.symm.trans h)
        apply SepWP.weaken_pre
        rotate_left
        · exact sepWP_nf_enqueue_nonempty_45c_fine hb hFuel
            (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
            (by simpa only [arm64_norm] using hx19) (by simpa only [arm64_norm] using hw1)
            (by simp [arm64_norm])
            (by simpa only [arm64_norm] using hsp) hspAl0
            (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
            (by simpa only [arm64_norm] using hbrk) (by simpa only [arm64_norm] using hperm)
            (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
                exact ⟨by simpa only [arm64_norm] using c21, by simpa only [arm64_norm] using c22,
                       by simpa only [arm64_norm] using c23, by simpa only [arm64_norm] using c24,
                       by simpa only [arm64_norm] using c25, by simpa only [arm64_norm] using c26,
                       by simpa only [arm64_norm] using c27, by simpa only [arm64_norm] using c28,
                       by simpa [calleeSavedVRegs] using cv⟩)
            hwf hFq hg hSc48 hActLt hHeadDef hIdx hClaimed hAv0 hFr0 hNeNat hHeadNe0 hHeadNeG
        · rw [← hCtxRead]
          sep_frame

/-! ## Root-Group Retirement Tails -/

theorem sepWP_nf_retire_root_from_218_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {liveCost peakCost : Nat}
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {active1 usage1 : List (BitVec 64)} {actLists1 : List (List (BitVec 64))}
    {gsDeq : List GroupDesc} {bvDeq : BitVec 64 → BitVec 8}
    {seq1 : BitVec 8} {unmapSeq1 : List (BitVec 8)}
    {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x218#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = pageOf maddrs.ctx)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk liveCost peakCost st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hAllFree : (g.availMask ||| g.freedMask) + (1#32 <<< idx) = (2#32 <<< g.lastIdx) - 1#32)
    (hMpPos : 0 < g.maplen)
    (hDeq : DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq)
    (hUSeqLen : unmapSeq1.length = 32) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st ∗
       (maddrs.ctx ↦ₛ { st.ctx with active := active1, usageByClass := usage1, unmapSeq := unmapSeq1, seq := seq1 }.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) bvDeq ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
       MappedSet st.masterDom (OwnedMappedByte st))
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom := by
  have _ := hb
  let gZero : GroupDesc := { g with prev := 0#64, next := 0#64 }
  obtain ⟨_, _, _, _, hOwnG⟩ := meta_ownedRw_of_mem_groups hwf hg
  obtain ⟨hPos, hMemAl, hLenAl, hFit, hNe0, hToNat, hmRes, hResErase, hCnt1, hDynLen1,
          hIvCov, hWf1, hCarve, hProt1, hMap1⟩ :=
    free_retire_rootGroup hwf hg hIdx hClaimed hAllFree hMpPos hDeq seq1 unmapSeq1 hUSeqLen
  have hBmG0 := (byteMap_update40 hwf.masterDom_wf.1 bvDeq (P := OwnedRwByte st) (m := g.metaPtr)
    (bs := gZero.metaBytes) (GroupDesc.metaBytes_length _) hOwnG).1
  have hZCells := metaBytes_eq_cells gZero
  rw [show gZero.metaPtr = g.metaPtr from rfl, show gZero.prev = 0#64 from rfl,
      show gZero.next = 0#64 from rfl, show gZero.mem = g.mem from rfl,
      show gZero.availMask = g.availMask from rfl, show gZero.freedMask = g.freedMask from rfl,
      show gZero.packedWord = g.packedWord from rfl] at hZCells
  rw [hBmG0, hDeq.g_zero_bytes, hZCells]
  wp_step
  wp_step
  wp_step
  rw [← hZCells, ← hDeq.g_zero_bytes, ← hBmG0]
  apply SepWP.weaken_pre
  rotate_left
  · exact sepWP_nf_freeMeta_224_fine hb hFuel
      (gZero := gZero)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simpa only [arm64_norm] using hx19) (by simpa only [arm64_norm] using hx20)
      hmRes
      (by simpa only [arm64_norm] using hsp) hspAl0
      (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
      (by simpa only [arm64_norm] using hbrk) (by simpa only [arm64_norm] using hperm)
      (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
          exact ⟨by simpa only [arm64_norm] using c21, by simpa only [arm64_norm] using c22,
                 by simpa only [arm64_norm] using c23, by simpa only [arm64_norm] using c24,
                 by simpa only [arm64_norm] using c25, by simpa only [arm64_norm] using c26,
                 by simpa only [arm64_norm] using c27, by simpa only [arm64_norm] using c28,
                 by simpa [calleeSavedVRegs] using cv⟩)
      hWf1 hResErase rfl
      (sameLiveUserSub_of_dequeueOutcome hwf hg hIdx hClaimed hAllFree hDeq rfl rfl rfl)
      (by omega) (by omega)
  · dsimp only [NfStaticRest]
    have hMaskNeg : g.packedWord &&& -4096#64 = BitVec.ofNat 64 (g.maplen * 4096) :=
      packedWord_and_pageMask g
    simp only [arm64_norm, hMaskNeg]
    rw [show g.1 = g.metaPtr from rfl]
    unfold NfRetSep
    simp only [hNe0, ↓reduceIte, hToNat]
    have hPureGoal :
        (0 < g.maplen * 4096 ∧ 4096 ∣ g.mem.toNat ∧ 4096 ∣ g.maplen * 4096 ∧
         g.mem.toNat + g.maplen * 4096 ≤ 2 ^ 48 ∧
         (∀ a : BitVec 64, MallocngInIntervals (dynamicRootRegions st) a →
           InRegion g.mem (g.maplen * 4096) a ∨
           MallocngInIntervals (dynamicRootRegions
             { st with
               ctx := { st.ctx with active := active1, usageByClass := usage1, unmapSeq := unmapSeq1, seq := seq1 }
               reservedMetas := g.metaPtr :: st.reservedMetas
               groups := gsDeq
               activeLists := actLists1
               masterDom := st.masterDom.filter (fun a => !decide (InRegion g.mem (g.maplen * 4096) a))
               byteVal := bvDeq }) a)) = True :=
      eq_true ⟨hPos, hMemAl, hLenAl, hFit, hIvCov⟩
    rw [hPureGoal, pure_true_sepConj, hProt1, hMap1]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hCarve)))))))))))))) ?_
    sep_frame

theorem sepWP_nf_retire_root_from_1fc_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {liveCost peakCost : Nat}
    {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {active1 usage1 : List (BitVec 64)} {actLists1 : List (List (BitVec 64))}
    {gsDeq : List GroupDesc} {bvDeq : BitVec 64 → BitVec 8}
    {seq1 : BitVec 8} {uSeqMid : List (BitVec 8)}
    {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x1fc#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 g.sc)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = pageOf maddrs.ctx)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk liveCost peakCost st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hAllFree : (g.availMask ||| g.freedMask) + (1#32 <<< idx) = (2#32 <<< g.lastIdx) - 1#32)
    (hMpPos : 0 < g.maplen)
    (hDeq : DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq)
    (hUMid : uSeqMid.length = 32) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st ∗
       (maddrs.ctx ↦ₛ { st.ctx with active := active1, usageByClass := usage1, unmapSeq := uSeqMid, seq := seq1 }.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) bvDeq ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
       MappedSet st.masterDom (OwnedMappedByte st))
      (NfFuelFinePost k fuel γ brkStart liveCost peakCost st s0) oom := by
  have _ := hb
  let cMid : CtxFields := { st.ctx with active := active1, usageByClass := usage1, unmapSeq := uSeqMid, seq := seq1 }
  wp_step
  wp_step
  wp_step
  wp_if_nd hHiBr
  · exact sepWP_nf_retire_root_from_218_fine hb hFuel
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simpa only [arm64_norm] using hx19) (by simpa only [arm64_norm] using hx20)
      (by simpa only [arm64_norm] using hsp) hspAl0
      (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
      (by simpa only [arm64_norm] using hbrk) (by simpa only [arm64_norm] using hperm)
      (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
          exact ⟨by simpa only [arm64_norm] using c21, by simpa only [arm64_norm] using c22,
                 by simpa only [arm64_norm] using c23, by simpa only [arm64_norm] using c24,
                 by simpa only [arm64_norm] using c25, by simpa only [arm64_norm] using c26,
                 by simpa only [arm64_norm] using c27, by simpa only [arm64_norm] using c28,
                 by simpa [calleeSavedVRegs] using cv⟩)
      hwf hg hIdx hClaimed hAllFree hMpPos hDeq hUMid
  · let kIdx : Nat := ((BitVec.ofNat 64 g.sc).truncate 32 - 7#32).toNat
    have hKLt32 : kIdx < 32 := by
      have hNotUlt : ¬ (BitVec.ult 31#32 ((BitVec.ofNat 64 g.sc).truncate 32 - 7#32) = true) := by
        simpa only [arm64_norm] using hHiBr
      simp only [BitVec.ult, decide_eq_true_eq] at hNotUlt; change ¬ (31 < kIdx) at hNotUlt; omega
    have _hSignExt : ((BitVec.ofNat 64 g.sc).truncate 32 - 7#32).signExtend 64 = BitVec.ofNat 64 kIdx :=
      signExtend64_of_lt_pow31 (by change kIdx < 2 ^ 31; omega)
    have hCtx20 : pageOf maddrs.ctx + lo12Of maddrs.ctx = maddrs.ctx := pageOf_add_lo12Of maddrs.ctx
    wp_step
    wp_step
    obtain ⟨SeqRest, hSeqRead, _⟩ := ctx_focus_update_seq maddrs.ctx cMid hDeq.lens.1 hDeq.lens.2.1 hUMid hwf.ctx_lens.2.2.2.1 seq1
    change SepWP _ _ _ (_ ∗ _ ∗ _ ∗ _ ∗ (maddrs.ctx ↦ₛ cMid.toBytes) ∗ _ ∗ _ ∗ _) _ _
    rw [hSeqRead]
    wp_step
    rw [← hSeqRead]
    obtain ⟨UByteRest, hUByteRead, hUByteWrite⟩ :=
      ctx_focus_update_unmapSeq_byte maddrs.ctx cMid hDeq.lens.1 hDeq.lens.2.1 hUMid hKLt32 seq1
    have hKLtMid : kIdx < cMid.unmapSeq.length := by dsimp only [cMid]; rw [hUMid]; exact hKLt32
    generalize hOldByte : (cMid.unmapSeq[kIdx]'hKLtMid) = oldB at hUByteRead
    rw [hUByteRead]
    apply step_str8_fast (b + 0x214#64) (b + 0x218#64)
      (maddrs.ctx + BitVec.ofNat 64 (848 + kIdx)) seq1
    · rfl
    · simp only [arm64_norm, hrun]
    · wp_close_fetch_cl
    · rfl
    · simp [evalAddrMode, arm64_norm]
      rw [BitVec.add_assoc]; congr 1; bv_omega
    · simp [arm64_norm]; rfl
    · wp_sep_access_fast
    · bv_omega
    intro m1 hm1 _
    rw [hUByteWrite]
    exact sepWP_nf_retire_root_from_218_fine hb hFuel
      (unmapSeq1 := uSeqMid.set kIdx seq1)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simpa only [arm64_norm] using hx19) (by simpa only [arm64_norm] using hx20)
      (by simpa only [arm64_norm] using hsp) hspAl0
      (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
      (by simpa only [arm64_norm] using hbrk) (hm1.trans (by simpa only [arm64_norm] using hperm))
      (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
          exact ⟨by simpa only [arm64_norm] using c21, by simpa only [arm64_norm] using c22,
                 by simpa only [arm64_norm] using c23, by simpa only [arm64_norm] using c24,
                 by simpa only [arm64_norm] using c25, by simpa only [arm64_norm] using c26,
                 by simpa only [arm64_norm] using c27, by simpa only [arm64_norm] using c28,
                 by simpa [calleeSavedVRegs] using cv⟩)
      hwf hg hIdx hClaimed hAllFree hMpPos hDeq (by simp [hUMid])

end LibsignalBinary.Heap.Fine
