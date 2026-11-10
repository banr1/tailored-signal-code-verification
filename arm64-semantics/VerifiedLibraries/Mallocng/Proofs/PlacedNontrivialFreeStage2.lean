/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/- Symbolic execution helpers for non-all-free slot release, active-queue insertion, and
root-group retirement in placed `nontrivial_free` (`blk05`). -/
import VerifiedLibraries.Mallocng.Proofs.PlacedNontrivialFreeStage1

set_option autoImplicit false
set_option maxRecDepth 20000

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic ProofLib.ProgramReflection VerifiedLibraries.Mallocng

private theorem shift2_sub1_toNat_fin :
    ∀ l : Fin 32, ((2#32 <<< l.val) - 1#32).toNat = 2 ^ (l.val + 1) - 1 := by decide

private theorem mask_disj_of_getLsbD_false {m : BitVec 32} {idx : Nat}
    (hIdx32 : idx < 32) (hF : m.getLsbD idx = false) :
    m &&& (1#32 <<< idx) = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one,
    BitVec.getLsbD_zero]
  by_cases hEq : i = idx
  · subst hEq; simp [hF]
  · have hNe : i - idx = 0 → i < idx := by omega
    have _ := hIdx32
    by_cases hLt : i < idx
    · simp [hLt]
    · have hSubNe : i - idx ≠ 0 := by omega
      simp [hi, hLt, hSubNe]

private theorem or_add_self_eq_or {a f s : BitVec 32}
    (ha : a &&& s = 0#32) (hf : f &&& s = 0#32) :
    (a ||| f) + s = a ||| (f ||| s) ∧ (f ||| a) + s = (a ||| f) + s := by
  constructor
  · revert ha hf; bv_robdd
  · bv_robdd

theorem claimed_notAllFree_props {k : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight (k + 1) base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hNotAll : (g.availMask ||| g.freedMask) + (1#32 <<< idx) ≠ (2#32 <<< g.lastIdx) - 1#32) :
    g.sc < 48 ∧
    idx < 32 ∧
    (g.availMask ||| (g.freedMask ||| (1#32 <<< idx))).toNat ≠ 2 ^ g.cnt - 1 := by
  have hGWf := hwf.groups_wf g hg
  have hLast31 : g.lastIdx ≤ 31 := hGWf.2.1
  have hLenCnt : g.slots.length = g.cnt := hGWf.2.2.1
  have hCntDef : g.cnt = g.lastIdx + 1 := rfl
  have hIdx32 : idx < 32 := by omega
  have hSWf := hGWf.slot_wf idx hIdx
  rw [hClaimed] at hSWf
  have hAvF : g.availMask.getLsbD idx = false :=
    Bool.eq_false_iff.mpr fun h => by have := hSWf.2.1.mp h; cases this
  have hFrF : g.freedMask.getLsbD idx = false :=
    Bool.eq_false_iff.mpr fun h => by have := hSWf.2.2.1.mp h; cases this
  have hAddEq : (g.availMask ||| g.freedMask) + (1#32 <<< idx) =
      g.availMask ||| (g.freedMask ||| (1#32 <<< idx)) :=
    (or_add_self_eq_or (mask_disj_of_getLsbD_false hIdx32 hAvF)
      (mask_disj_of_getLsbD_false hIdx32 hFrF)).1
  have hRhsNat : ((2#32 <<< g.lastIdx) - 1#32).toNat = 2 ^ g.cnt - 1 := by
    rw [hCntDef]; exact shift2_sub1_toNat_fin ⟨g.lastIdx, by omega⟩
  have hNeNat : (g.availMask ||| (g.freedMask ||| (1#32 <<< idx))).toNat ≠ 2 ^ g.cnt - 1 := by
    intro hEqNat
    apply hNotAll
    rw [hAddEq]
    exact BitVec.eq_of_toNat_eq (hEqNat.trans hRhsNat.symm)
  have hSc48 : g.sc < 48 := by
    rcases hGWf.1 with h48 | h63
    · exact h48
    · exfalso
      have hLast0 : g.lastIdx = 0 := (hGWf.2.2.2.1 h63).1
      have hIdx0 : idx = 0 := by omega
      subst hIdx0
      have hOrBound : (g.availMask ||| g.freedMask).toNat < 2 := by
        have hb := hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simpa [hCntDef, hLast0] using hb
      have hBit0 : (g.availMask ||| g.freedMask).getLsbD 0 = false := by
        rw [BitVec.getLsbD_or, hAvF, hFrF]; rfl
      have hOrZero : g.availMask ||| g.freedMask = 0#32 := by
        rcases (by omega : (g.availMask ||| g.freedMask).toNat = 0 ∨
            (g.availMask ||| g.freedMask).toNat = 1) with h0 | h1
        · exact BitVec.eq_of_toNat_eq h0
        · have hEq1 : g.availMask ||| g.freedMask = 1#32 := BitVec.eq_of_toNat_eq h1
          rw [hEq1] at hBit0; cases hBit0
      apply hNotAll
      rw [hOrZero, hLast0]
      decide
  exact ⟨hSc48, hIdx32, hNeNat⟩

private theorem or_eq_zero_iff32 (a b : BitVec 32) :
    (a ||| b = 0#32) ↔ (a = 0#32 ∧ b = 0#32) := by
  constructor
  · intro h; constructor <;> (revert h; bv_robdd)
  · rintro ⟨rfl, rfl⟩; rfl

private theorem setWidth64_eq_zero_iff32 (v : BitVec 32) :
    v.setWidth 64 = 0#64 ↔ v = 0#32 := by
  constructor
  · intro h; revert h; bv_robdd
  · rintro rfl; rfl

theorem sc_cmp47_and_active_off_fin :
    ∀ s : Fin 48,
      (BitVec.truncate 32 (BitVec.ofNat 64 s.val)).sle 47#32 = true ∧
      (BitVec.ofNat 64 s.val).getLsbD 31 = false ∧
      (BitVec.ofNat 64 s.val >>> 0 &&& 0xffffffff#64) = BitVec.ofNat 64 s.val ∧
      (BitVec.ofNat 64 s.val &&& 0xffffffff#64) = BitVec.ofNat 64 s.val ∧
      (BitVec.ofNat 64 s.val + 10#64) <<< 3 = BitVec.ofNat 64 (80 + 8 * s.val) := by
  decide

theorem group_mem_allMetaSlots {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {u : GroupDesc} (hu : u ∈ st.groups) :
    u.metaPtr ∈ allMetaSlots st :=
  (hwf.free_bump_metas_wf.2.2.2.2.2 u.metaPtr).mp
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hu))))

theorem metaBytes_congr {g1 g2 : GroupDesc}
    (h1 : g1.prev = g2.prev) (h2 : g1.next = g2.next) (h3 : g1.mem = g2.mem)
    (h4 : g1.availMask = g2.availMask) (h5 : g1.freedMask = g2.freedMask)
    (h6 : g1.packedWord = g2.packedWord) :
    g1.metaBytes = g2.metaBytes := by
  unfold GroupDesc.metaBytes; rw [h1, h2, h3, h4, h5, h6]

scoped macro "wp_if_nd" h:ident : tactic =>
  `(tactic| ((apply SepWP.ite; (wp_focus_close wp_norm_lhs)) <;> intro $h:ident))

theorem step_ldr64_fast {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (pc pc' : BitVec 64) {rt : Reg} {addr : AddrMode}
    (ea : BitVec 64) (v : BitVec 64)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W64 .X64 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, none))
    (hload : SepLoad64 ea P v)
    (hpc' : pc + 4#64 = pc')
    (hnext : SepWP prog target_pc ((s.writeReg64 rt v).setPC pc') P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldr64 hpc hrun hfetch hsp haddr hload
    (by dsimp only [applyWriteback]; exact congrArg ((s.writeReg64 rt v).setPC ·) hpc')
    hnext

theorem step_str64_fast {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (pc pc' : BitVec 64) {rt : Reg} {addr : AddrMode}
    (ea : BitVec 64) (val : BitVec 64)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, none))
    (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P')
    (hpc' : pc + 4#64 = pc')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc ((s.setPC pc').setMem m') P' post oom) :
    SepWP prog target_pc s P post oom :=
  step_str64_perm_kf hpc hrun hfetch hsp haddr hval hstore
    (by dsimp only [applyWriteback]; exact congrArg (s.setPC ·) hpc')
    hnext

set_option maxHeartbeats 400000 in
theorem sepWP_nf_enqueue_nonempty_45c [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {bud : MallocngBudget}
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {head : BitVec 64}
    {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x45c#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hw1 : s.readReg32 .x1 = 1#32 <<< idx)
    (hx3 : s.readReg64 (.gpr 3#5) = head)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st)
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
      (NfFuelPost k fuel γ brkStart bud st s0) oom := by
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
  · exact sepWP_nf_commit_474 hb hFuel
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
      hWf1 rfl rfl (by omega) hDyn1
      (Cost.groupsGrpMono_updateQueuedGroups hg _ _ rfl rfl) hByte1
  · have hPreCells := metaBytes_eq_cells gPre
    dsimp only [gPre] at hPreCells
    dsimp only [NfStaticRest]
    simp only [arm64_norm]
    rw [hProt1, hMap1, hPreCells, hTlPtr, ← hBmHdW, ← hHdCellsUpd]
    sep_frame

set_option maxHeartbeats 400000 in
theorem sepWP_nf_nonAllFree [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {bud : MallocngBudget}
    {st : MallocngSt} {g : GroupDesc} {idx : Nat} {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x50#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = g.metaPtr)
    (hw1 : s.readReg32 .x1 = 1#32 <<< idx)
    (hw3 : s.readReg32 .x3 = g.freedMask ||| g.availMask)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 g.sc)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st)
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
      (NfFuelPost k fuel γ brkStart bud st s0) oom := by
  have _ := hb
  obtain ⟨hSc48, _, hNeNat⟩ := claimed_notAllFree_props hwf hg hIdx hClaimed hNotAll
  obtain ⟨_, hmAl, hmFit, hReadG, hOwnG⟩ := meta_ownedRw_of_mem_groups hwf hg
  have hw3' : (s.readReg64 (.gpr 3#5)).truncate 32 = g.freedMask ||| g.availMask := hw3
  have hx0' : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 g.sc := hx0
  have hx19' : s.readReg64 (.gpr 19#5) = g.metaPtr := hx19
  wp_step
  wp_if_nd hW3
  · -- w3 != 0: `g` is already in `st.activeLists[g.sc]`
    have hMaskNe0 : g.freedMask ||| g.availMask ≠ 0#32 :=
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
    · exact sepWP_nf_commit_474 hb hFuel
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
        hWf1 rfl rfl (by omega) hDyn1
        (Cost.groupsGrpMono_replaceGroupByMeta hg _ rfl rfl) hByte1
    · dsimp only [NfStaticRest]
      rw [hProt1, hMap1]
      sep_frame
  · -- w3 = 0: `g.availMask = 0#32` and `g.freedMask = 0#32`
    have ⟨hFr0, hAv0⟩ : g.freedMask = 0#32 ∧ g.availMask = 0#32 := by
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
    · -- head = g.metaPtr
      have hHeadEq0 : head = g.metaPtr := by
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
      · exact sepWP_nf_commit_474 hb hFuel
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
          hWf1 rfl rfl (by omega) hDyn1
          (Cost.groupsGrpMono_replaceGroupByMeta hg _ rfl rfl) hByte1
      · dsimp only [NfStaticRest]
        rw [← hCtxRead, hProt1, hMap1]
        sep_frame
    · -- head != g.metaPtr
      have hHeadNeG0 : head ≠ g.metaPtr := by
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
      · -- head = 0#64
        have hHead00 : head = 0#64 := by
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
        · exact sepWP_nf_commit_474 hb hFuel
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
            hWf1 rfl rfl (by omega) hDyn1
            (Cost.groupsGrpMono_replaceGroupByMeta hg _ rfl rfl) hByte1
        · have hPreCells := metaBytes_eq_cells gPre
          dsimp only [gPre] at hPreCells
          dsimp only [NfStaticRest]
          simp only [arm64_norm]
          rw [← hCtxWrite, hPreCells, hProt1, hMap1]
          sep_frame
      · -- head != 0#64
        have hHeadNe00 : head ≠ 0#64 := by
          simpa only [arm64_norm, beq_iff_eq, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] using hHead0Br
        have hHeadNe0 : st.ctx.active[g.sc]'hActLt ≠ 0#64 := fun h => hHeadNe00 (hHeadDef.symm.trans h)
        apply SepWP.weaken_pre
        rotate_left
        · exact sepWP_nf_enqueue_nonempty_45c hb hFuel
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

theorem roTables_focus_sizeClass (A : MallocngAddrs) {sc : Nat} (hsc : sc < 48) :
    ∃ Rest : SepProp, MallocngRoTablesA A =
      (((A.sizeClasses + BitVec.ofNat 64 (2 * sc)) ↦₁₆ᵣ BitVec.ofNat 16 (sizeClass sc)) ∗ Rest) := by
  dsimp only [MallocngRoTablesA, MallocngRoTablesAt]
  refine ⟨(A.sizeClasses ↦ᵣ sizeClassBytes.take (2 * sc)) ∗
    ((A.sizeClasses + BitVec.ofNat 64 (2 * sc + 2)) ↦ᵣ sizeClassBytes.drop (2 * sc + 2)) ∗
    (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
    (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
    (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
    (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table), ?_⟩
  rw [show mallocngSizeClassBytes = sizeClassBytes from rfl,
      pointsToBytesRO_split3 A.sizeClasses sizeClassBytes (2 * sc) 2 (by rw [sizeClassBytes_length]; omega),
      pointsToBytesRO_take2_eq_pointsTo16RO _ _ _ (by rw [sizeClassBytes_length]; omega),
      pack16_sizeClassBytes hsc]
  ac_rfl

theorem step_str8_fast {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (pc pc' : BitVec 64) (ea : BitVec 64) (val : BitVec 8)
    {rt : Reg} {addr : AddrMode}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, none))
    (hval : (s.readReg64 rt).truncate 8 = val)
    (hstore : SepStore8 ea val P P')
    (hpc' : pc + 4#64 = pc')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc ((s.setPC pc').setMem m') P' post oom) :
    SepWP prog target_pc s P post oom :=
  step_str8_perm_kf hpc hrun hfetch hsp haddr hval hstore
    (by dsimp only [applyWriteback]; exact congrArg (s.setPC ·) hpc')
    hnext

theorem step_str8_wb_fast {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (pc pc' : BitVec 64) (ea wbVal : BitVec 64) (wbReg : Reg) (val : BitVec 8)
    {rt : Reg} {addr : AddrMode}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, some (wbReg, wbVal)))
    (hval : (s.readReg64 rt).truncate 8 = val)
    (hstore : SepStore8 ea val P P')
    (hpc' : pc + 4#64 = pc')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (((s.writeReg64 wbReg wbVal).setPC pc').setMem m') P' post oom) :
    SepWP prog target_pc s P post oom :=
  step_str8_perm_kf hpc hrun hfetch hsp haddr hval hstore
    (by dsimp only [applyWriteback]; exact congrArg ((s.writeReg64 wbReg wbVal).setPC ·) hpc')
    hnext

theorem sepWP_nf_zero_bytes_2e8 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b)
    {target_pc : BitVec 64} {s : State} {R : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {p endPtr : BitVec 64} (bs : List (BitVec 8))
    (hpc : s.pc = b + 0x2e8#64) (hrun : s.status = .Running)
    (hx1 : s.readReg64 (.gpr 1#5) = p)
    (hx2 : s.readReg64 (.gpr 2#5) = endPtr)
    (hNeNil : bs ≠ [])
    (hNoWrap : p.toNat + bs.length < 2 ^ 64)
    (hEnd : p + BitVec.ofNat 64 bs.length = endPtr)
    (hnext : ∀ s' : State,
      s'.pc = b + 0x2f4#64 → s'.status = .Running →
      s'.readReg64 (.gpr 1#5) = endPtr →
      s'.readReg64 (.gpr 2#5) = endPtr →
      s'.readReg64 (.gpr 0#5) = s.readReg64 (.gpr 0#5) →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.sp = s.sp → MallocngProcPreserved s s' → s'.brk = s.brk →
      s'.mem.perm = s.mem.perm → Cs21Preserved s s' →
      SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s'
        ((p ↦ₛ List.replicate bs.length 0#8) ∗ R) post oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s
      ((p ↦ₛ bs) ∗ R) post oom := by
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
      wp_step
      wp_step
      rw [← pointsToBytes_cons]
      exact hnext _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simp [arm64_norm]) (by simpa only [arm64_norm] using hx2)
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm])
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (by simp [arm64_norm]) hm1
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [calleeSavedVRegs]⟩
    | cons b1 tl2 =>
      simp only [List.length_cons] at hNoWrap hEnd
      have hP1Nat : (p + 1#64).toNat = p.toNat + 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hNeEnd : endPtr ≠ p + 1#64 := by
        intro hEq
        have hEqNat := congrArg BitVec.toNat hEq
        have h2 : endPtr.toNat = p.toNat + (tl2.length + 1 + 1) := by
          rw [← hEnd, BitVec.toNat_add, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      wp_step
      wp_step
      have hFrameIn : (((p ↦₈ 0#8) ∗ ((p + 1#64) ↦ₛ (b1 :: tl2))) ∗ R) =
          (((p + 1#64) ↦ₛ (b1 :: tl2)) ∗ ((p ↦₈ 0#8) ∗ R)) := by ac_rfl
      rw [hFrameIn]
      apply ih (p := p + 1#64) (R := (p ↦₈ 0#8) ∗ R)
      · simp [arm64_norm, hNeEnd]
      · simp only [arm64_norm, hrun]
      · simp only [arm64_norm]
      · simpa only [arm64_norm] using hx2
      · simp
      · simp only [List.length_cons, hP1Nat]; omega
      · simp only [List.length_cons]
        have hAdd : (p + 1#64) + BitVec.ofNat 64 (tl2.length + 1) = p + BitVec.ofNat 64 (tl2.length + 1 + 1) := by
          rw [BitVec.add_assoc]; congr 1
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        exact hAdd.trans hEnd
      · intro s' hpc' hrun' hx1' hx2' hx0' hx19' hx20' hsp' hProc' hbrk' hperm' hcs'
        have hFrameOut : (((p + 1#64) ↦ₛ List.replicate (b1 :: tl2).length 0#8) ∗ ((p ↦₈ 0#8) ∗ R)) =
            ((p ↦ₛ List.replicate (b0 :: b1 :: tl2).length 0#8) ∗ R) := by
          simp only [List.length_cons, List.replicate_succ, pointsToBytes_cons]
          ac_rfl
        rw [hFrameOut]
        exact hnext s' hpc' hrun' hx1' hx2'
          (hx0'.trans (by simp [arm64_norm]))
          (hx19'.trans (by simp [arm64_norm]))
          (hx20'.trans (by simp [arm64_norm]))
          (hsp'.trans (by simp [arm64_norm]))
          (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc'
              exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
          (hbrk'.trans (by simp [arm64_norm]))
          (hperm'.trans hm1)
          (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs'
              exact ⟨c21.trans (by simp [arm64_norm]), c22.trans (by simp [arm64_norm]),
                     c23.trans (by simp [arm64_norm]), c24.trans (by simp [arm64_norm]),
                     c25.trans (by simp [arm64_norm]), c26.trans (by simp [arm64_norm]),
                     c27.trans (by simp [arm64_norm]), c28.trans (by simp [arm64_norm]),
                     cv.trans (by simp [calleeSavedVRegs])⟩)

theorem signExtend64_of_lt_pow31 {v : BitVec 32} (h : v.toNat < 2 ^ 31) :
    v.signExtend 64 = BitVec.ofNat 64 v.toNat := by
  have hUlt : v.ult 0x80000000#32 = true := by simp [BitVec.ult]; omega
  have hZ : v.zeroExtend 64 = BitVec.ofNat 64 v.toNat := by simp
  rw [← hZ]; revert hUlt; bv_robdd

private theorem sepWP_nf_retire_root_from_218 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {bud : MallocngBudget}
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
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st)
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
      (NfFuelPost k fuel γ brkStart bud st s0) oom := by
  have _ := hb
  let nBytes := g.maplen * 4096
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
  · exact sepWP_nf_freeMeta_224 hb hFuel
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
      hWf1 hResErase rfl (by omega) (by omega) (Cost.DequeueOutcome.groupsGrpMono hDeq)
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

theorem packedWord_and_neg4096 (g : GroupDesc) :
    g.packedWord &&& -4096#64 = BitVec.ofNat 64 (g.maplen * 4096) :=
  packedWord_and_pageMask g

theorem sepWP_nf_retire_root_from_1fc [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {bud : MallocngBudget}
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
    (hwf : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st)
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
      (NfFuelPost k fuel γ brkStart bud st s0) oom := by
  have _ := hb
  let cMid : CtxFields := { st.ctx with active := active1, usageByClass := usage1, unmapSeq := uSeqMid, seq := seq1 }
  wp_step
  wp_step
  wp_step
  wp_if_nd hHiBr
  · exact sepWP_nf_retire_root_from_218 hb hFuel
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
    exact sepWP_nf_retire_root_from_218 hb hFuel
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

end VerifiedLibraries.Mallocng.Proofs
