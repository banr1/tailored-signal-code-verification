/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.PlacedNontrivialFreeStage2

/-!
# Group Activation, Usage Decrement, and Singleton Dequeue for Placed `nontrivial_free` (`blk05`)

Symbolic execution lemmas for subword loads, the `activate_group` LL/SC loop, `usageByClass`
decrements, and singleton active-list dequeue paths in `blkPC_b05`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic ProofLib.ProgramReflection VerifiedLibraries.Mallocng

/-! ## Subword Load Wrappers, Cell Focus, and `Fin` Bitfield Helpers -/

theorem step_ldr8_fast {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (pc pc' : BitVec 64) {rt : Reg} {addr : AddrMode}
    (ea : BitVec 64) (v : BitVec 8)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .B8 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, none))
    (hload : SepLoad8 ea P v)
    (hpc' : pc + 4#64 = pc')
    (hnext : SepWP prog target_pc ((s.writeReg .W32 rt (v.zeroExtend 64)).setPC pc') P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldr8 hpc hrun hfetch hsp haddr hload
    (by dsimp only [applyWriteback]; exact congrArg ((s.writeReg .W32 rt (v.zeroExtend 64)).setPC ·) hpc')
    hnext

theorem step_ldr8_64_fast {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (pc pc' : BitVec 64) {rt : Reg} {addr : AddrMode}
    (ea : BitVec 64) (v : BitVec 64)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .B8 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, none))
    (hload : SepLoad64 ea P v)
    (hpc' : pc + 4#64 = pc')
    (hnext : SepWP prog target_pc ((s.writeReg .W32 rt ((v.truncate 8).zeroExtend 64)).setPC pc') P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldr8_64 hpc hrun hfetch hsp haddr hload
    (by dsimp only [applyWriteback]; exact congrArg ((s.writeReg .W32 rt ((v.truncate 8).zeroExtend 64)).setPC ·) hpc')
    hnext

theorem step_ldr16_fast {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (pc pc' : BitVec 64) {rt : Reg} {addr : AddrMode}
    (ea : BitVec 64) (v : BitVec 16)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .H16 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, none))
    (hload : SepLoad16 ea P v)
    (hpc' : pc + 4#64 = pc')
    (hnext : SepWP prog target_pc ((s.writeReg .W32 rt (v.zeroExtend 64)).setPC pc') P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldr16 hpc hrun hfetch hsp haddr hload
    (by dsimp only [applyWriteback]; exact congrArg ((s.writeReg .W32 rt (v.zeroExtend 64)).setPC ·) hpc')
    hnext

theorem pointsTo64_focus16 (a v : BitVec 64) :
    ∃ Rest16 : SepProp, (a ↦₆₄ v) = ((a ↦₁₆ v.truncate 16) ∗ Rest16) := by
  refine ⟨((a + 2#64) ↦₁₆ v.extractLsb' 16 16) ∗
    ((a + 4#64) ↦₁₆ v.extractLsb' 32 16) ∗
    ((a + 6#64) ↦₁₆ v.extractLsb' 48 16), ?_⟩
  rw [pointsTo64_split16]
  have h0 : v.extractLsb' 0 16 = v.truncate 16 := by bv_robdd
  rw [h0]

theorem byteMap_focus1 {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep]
    (val : BitVec 64 → BitVec 8) (a : BitVec 64)
    (hDom : a ∈ dom) (hKeep : keep a) :
    ∃ Rest1 : SepProp,
      ByteMap dom keep val = ((a ↦₈ val a) ∗ Rest1) := by
  refine ⟨ByteMap dom (fun x => keep x ∧ ¬ InRegion a 1 x) val, ?_⟩
  have hSubDom : ∀ x, InRegion a 1 x → x ∈ dom := by
    intro x hx
    have hEq : x = a := by unfold InRegion at hx; bv_omega
    exact hEq ▸ hDom
  have hSubKeep : ∀ x, InRegion a 1 x → keep x := by
    intro x hx
    have hEq : x = a := by unfold InRegion at hx; bv_omega
    exact hEq ▸ hKeep
  rw [ByteMap_extract_slice hNodup val a (by omega) hSubDom hSubKeep]
  have hR : readBytesFromMap val a 1 = [val a] := by
    simp [readBytesFromMap, rangeAddrs]
  rw [hR, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem sc_usage_off_fin :
    ∀ s : Fin 48,
      (BitVec.ofNat 64 s.val + 0x3a#64) <<< 3 = BitVec.ofNat 64 (464 + 8 * s.val) := by
  decide

theorem lastIdx_cnt_sub_fin :
    ∀ l : Fin 32,
      (BitVec.ofNat 32 l.val + 1#32).signExtend 64 = BitVec.ofNat 64 (l.val + 1) := by
  decide

theorem sc_sub7_ule31_fin :
    ∀ s : Fin 48,
      ((BitVec.truncate 32 (BitVec.ofNat 64 s.val) - 7#32).ule 0x1f#32 = true ↔
        (7 ≤ s.val ∧ s.val ≤ 38)) ∧
      (7 ≤ s.val → s.val ≤ 38 →
        (BitVec.truncate 32 (BitVec.ofNat 64 s.val) - 7#32).signExtend 64 =
          BitVec.ofNat 64 (s.val - 7)) := by
  decide

theorem sizeClass_ubfiz_fin :
    ∀ s : Fin 48,
      evalBitfield .W64 .UBFM 0#64 ((BitVec.ofNat 16 (sizeClass s.val)).zeroExtend 64) 60 15 =
        BitVec.ofNat 64 (slotStride s.val) := by
  decide

theorem activeByte_ubfx5_eq :
    ∀ b : BitVec 8,
      evalBitfield .W64 .UBFM 0#64 (b.zeroExtend 64) 0 4 =
        BitVec.ofNat 64 (b &&& 0x1f#8).toNat ∧
      (2#32 <<< ((BitVec.ofNat 64 (b &&& 0x1f#8).toNat).truncate 32).toNat) =
        (2#32 <<< (b &&& 0x1f#8).toNat) := by
  decide

theorem sbfiz_cnt9_fin :
    ∀ l : Fin 32,
      evalBitfield .W64 .SBFM 0#64 ((BitVec.ofNat 32 l.val + 1#32).zeroExtend 64) 61 31 +
          (BitVec.ofNat 32 l.val + 1#32).signExtend 64 =
        BitVec.ofNat 64 (9 * (l.val + 1)) ∧
      ((BitVec.ofNat 32 l.val + 1#32).sle 0x13#32 = false → 20 ≤ l.val + 1) := by
  decide

/-! ## `activate_group` LL/SC Loop -/

theorem sepWP_nf_and32_loop_2ac [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {ea : BitVec 64}
    {oldVal newVal cntMask : BitVec 32} {m4 m19 : BitVec 64}
    (hAlign : MemWidth.isAligned .W32 ea = true)
    {Rest : SepProp} {s0 : State} {oom : State → SepProp} :
    ∀ (n : Nat) (s : State),
      s.exclFails.length < n →
      s.pc = b + 0x2ac#64 →
      s.status = .Running →
      s.readReg64 (.gpr 2#5) = ea →
      s.readReg32 (.gpr 3#5) = oldVal →
      s.readReg32 (.gpr 1#5) = newVal →
      s.readReg32 (.gpr 6#5) = cntMask →
      s.readReg64 (.gpr 4#5) = m4 →
      s.readReg64 (.gpr 19#5) = m19 →
      MallocngProcPreserved s0 s →
      Cs21Preserved s0 s →
      SepWP (blkPC_b05.rebase b (fun _ => none)) (b + 0x2c0#64) s
        ((ea ↦₃₂ oldVal) ∗ Rest)
        (fun s1 P1 =>
          s1.sp = s.sp ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
          MallocngProcPreserved s0 s1 ∧ Cs21Preserved s0 s1 ∧
          s1.readReg32 (.gpr 3#5) = oldVal ∧
          s1.readReg32 (.gpr 6#5) = cntMask ∧
          s1.readReg64 (.gpr 4#5) = m4 ∧
          s1.readReg64 (.gpr 19#5) = m19 ∧
          s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
          (P1 ⊢ (ea ↦₃₂ newVal) ∗ Rest))
        oom := by
  intro n; induction n with
  | zero => intro _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    have _ := hb
    intro s hlt hpc hrun hx2 hw3 hw1 hw6 hx4 hx19 hProc hcs
    wp_steps 3
    refine step_stxr32_either_perm_next (pc := b + 0x2b8#64) (pc_next := b + 0x2bc#64)
      (ea := ea) (val := newVal)
      (by simp [arm64_norm]; rw [show BitVec.setWidth 32 (s.readReg64 (.gpr 3#5)) = oldVal by simpa [arm64_norm] using hw3])
      (by rw [BitVec.add_assoc]; rfl)
      (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
      (by simp [arm64_norm]) (by simpa [arm64_norm] using hx2) hAlign
      (by simpa [arm64_norm] using hw1)
      (fun _ m' hm' _ => ?_) (fun hfail => ?_)
    · wp_step
      refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        ⟨by simp [arm64_norm],
         by simp [arm64_norm],
         by simpa [arm64_norm, State.stepExclOracle] using hm',
         ?_, ?_,
         by simpa [arm64_norm, State.stepExclOracle] using hw3,
         by simpa [arm64_norm, State.stepExclOracle] using hw6,
         by simpa [arm64_norm, State.stepExclOracle] using hx4,
         by simpa [arm64_norm, State.stepExclOracle] using hx19,
         by simp [arm64_norm],
         Entails.refl _⟩
      · obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc
        exact ⟨by simpa [State.stepExclOracle] using f1,
               by simpa [State.stepExclOracle] using f2,
               by simpa [State.stepExclOracle] using f3,
               by simpa [State.stepExclOracle] using f4,
               by simpa [State.stepExclOracle] using f5,
               by simpa [State.stepExclOracle] using f6,
               by simpa [State.stepExclOracle] using f7⟩
      · obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
        exact ⟨by simpa [arm64_norm, State.stepExclOracle] using c21,
               by simpa [arm64_norm, State.stepExclOracle] using c22,
               by simpa [arm64_norm, State.stepExclOracle] using c23,
               by simpa [arm64_norm, State.stepExclOracle] using c24,
               by simpa [arm64_norm, State.stepExclOracle] using c25,
               by simpa [arm64_norm, State.stepExclOracle] using c26,
               by simpa [arm64_norm, State.stepExclOracle] using c27,
               by simpa [arm64_norm, State.stepExclOracle] using c28,
               by simpa [calleeSavedVRegs, State.stepExclOracle] using cv⟩
    · wp_step
      have hTailLt : s.exclFails.tail.length < n := exclFails_tail_lt_free hlt hfail
      refine SepWP.mono (ih _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        fun s1 P1 _ _ hpost =>
          ⟨by simpa [arm64_norm, State.stepExclOracle] using hpost.1,
           by simpa [arm64_norm, State.stepExclOracle] using hpost.2.1,
           by simpa [arm64_norm, State.stepExclOracle] using hpost.2.2.1,
           hpost.2.2.2.1, hpost.2.2.2.2.1,
           hpost.2.2.2.2.2.1, hpost.2.2.2.2.2.2.1,
           hpost.2.2.2.2.2.2.2.1, hpost.2.2.2.2.2.2.2.2.1,
           by simpa [arm64_norm] using hpost.2.2.2.2.2.2.2.2.2.1,
           hpost.2.2.2.2.2.2.2.2.2.2⟩
      · simpa [arm64_norm, State.stepExclOracle] using hTailLt
      · simp [arm64_norm]
      · simp [arm64_norm, hrun]
      · simpa [arm64_norm, State.stepExclOracle] using hx2
      · simpa [arm64_norm, State.stepExclOracle] using hw3
      · simpa [arm64_norm, State.stepExclOracle] using hw1
      · simpa [arm64_norm, State.stepExclOracle] using hw6
      · simpa [arm64_norm, State.stepExclOracle] using hx4
      · simpa [arm64_norm, State.stepExclOracle] using hx19
      · obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc
        exact ⟨by simpa [State.stepExclOracle] using f1,
               by simpa [State.stepExclOracle] using f2,
               by simpa [State.stepExclOracle] using f3,
               by simpa [State.stepExclOracle] using f4,
               by simpa [State.stepExclOracle] using f5,
               by simpa [State.stepExclOracle] using f6,
               by simpa [State.stepExclOracle] using f7⟩
      · obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
        exact ⟨by simpa [arm64_norm, State.stepExclOracle] using c21,
               by simpa [arm64_norm, State.stepExclOracle] using c22,
               by simpa [arm64_norm, State.stepExclOracle] using c23,
               by simpa [arm64_norm, State.stepExclOracle] using c24,
               by simpa [arm64_norm, State.stepExclOracle] using c25,
               by simpa [arm64_norm, State.stepExclOracle] using c26,
               by simpa [arm64_norm, State.stepExclOracle] using c27,
               by simpa [arm64_norm, State.stepExclOracle] using c28,
               by simpa [calleeSavedVRegs, State.stepExclOracle] using cv⟩

theorem ubfx_sc_from_u16 (w : BitVec 16) :
    evalBitfield .W64 .UBFM 0#64 (w.zeroExtend 64) 6 11 =
      ((w.zeroExtend 64) >>> 6) &&& 0x3f#64 := by
  unfold evalBitfield
  have h1 : (BitfieldOp.UBFM == BitfieldOp.UBFM) = true := rfl
  have h2 : (11 % 64 ≥ 6 % 64) := by omega
  have h3 : (11 % 64 + 1 == 64) = false := rfl
  simp only [h1, h2, h3, ↓reduceIte]
  bv_robdd

theorem activeByte_shift32_eq :
    ∀ b : BitVec 8,
      (b.toNat % 4294967296 &&& 31) % 32 = (b &&& 31#8).toNat := by
  decide

set_option maxHeartbeats 400000 in
theorem sepWP_nf_activate_group_264 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b)
    {target_pc : BitVec 64} {st : MallocngSt} {g nextMid : GroupDesc}
    {cAct : CtxFields} {bv_c : BitVec 64 → BitVec 8}
    {R : SepProp} {s0 s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = b + 0x264#64) (hrun : s.status = .Running)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 g.sc)
    (hx20 : s.readReg64 (.gpr 20#5) = pageOf maddrs.ctx)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hProc : MallocngProcPreserved s0 s) (hcs : Cs21Preserved s0 s)
    (hSc48 : g.sc < 48)
    (hCLen : cAct.active.length = 48)
    (hCGet : cAct.active[g.sc]'(hCLen ▸ hSc48) = nextMid.metaPtr)
    (hNxNe0 : nextMid.metaPtr ≠ 0#64)
    (hAv0 : nextMid.availMask = 0#32)
    (hmAlN : nextMid.metaPtr.toNat % 8 = 0)
    (hmFitN : nextMid.metaPtr.toNat + 40 ≤ 2 ^ 48)
    (hDomNd : st.masterDom.Nodup)
    (hOwnN : ∀ a, InRegion nextMid.metaPtr 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom)
    (hReadN : readBytesFromMap bv_c nextMid.metaPtr 40 = nextMid.metaBytes)
    (hActByte : bv_c (nextMid.mem + 8#64) = nextMid.activeByte)
    (hOwnActB : OwnedRwByte st (nextMid.mem + 8#64))
    (hDomActB : (nextMid.mem + 8#64) ∈ st.masterDom)
    (hnext : ∀ s' : State,
      s'.pc = b + 0x1c4#64 → s'.status = .Running →
      s'.readReg64 (.gpr 19#5) = g.metaPtr →
      s'.readReg64 (.gpr 20#5) = pageOf maddrs.ctx →
      s'.sp = s.sp → s'.brk = s.brk → s'.mem.perm = s.mem.perm →
      MallocngProcPreserved s0 s' → Cs21Preserved s0 s' →
      SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s'
        ((maddrs.ctx ↦ₛ cAct.toBytes) ∗
         ByteMap st.masterDom (OwnedRwByte st)
           (writeBytesToMap bv_c nextMid.metaPtr (mkActivatedGroup nextMid).metaBytes) ∗ R)
        post oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s
      ((maddrs.ctx ↦ₛ cAct.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) bv_c ∗ R) post oom := by
  have _ := hb
  have hCtx20 : pageOf maddrs.ctx + lo12Of maddrs.ctx = maddrs.ctx := pageOf_add_lo12Of maddrs.ctx
  have hScProps := sc_cmp47_and_active_off_fin ⟨g.sc, hSc48⟩
  have hActAddr : maddrs.ctx + ((BitVec.ofNat 64 g.sc + 10#64) <<< 3) =
      maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc) :=
    congrArg (maddrs.ctx + ·) hScProps.2.2.2.2
  wp_step
  wp_step
  obtain ⟨CtxRest, hCtxRead, _⟩ :=
    ctx_focus_update_active maddrs.ctx cAct hCLen hSc48 nextMid.metaPtr
  rw [hCtxRead, hCGet]
  apply step_ldr64_fast (b + 0x26c#64) (b + 0x270#64)
    (maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc)) nextMid.metaPtr
  · rfl
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, extendVal, arm64_norm]; exact Prod.ext hActAddr rfl
  · wp_sep_access_fast
  · bv_omega
  rw [← hCGet, ← hCtxRead]
  wp_step
  have ⟨hBmN0, hBmNW⟩ := byteMap_update40 hDomNd bv_c (P := OwnedRwByte st)
    (m := nextMid.metaPtr) (bs := (mkActivatedGroup nextMid).metaBytes)
    (GroupDesc.metaBytes_length _) hOwnN
  have hNCells := metaBytes_eq_cells nextMid
  rw [hAv0] at hNCells
  rw [hBmN0, hReadN, hNCells]
  wp_steps 5
  rw [← hNCells, ← hReadN, ← hBmN0]
  obtain ⟨Rest1, hFocus1⟩ := byteMap_focus1 hDomNd bv_c (nextMid.mem + 8#64) hDomActB hOwnActB
  rw [hFocus1, hActByte]
  wp_step
  rw [← hActByte, ← hFocus1]
  have hSh32 := activeByte_shift32_eq nextMid.activeByte
  wp_steps 5
  rw [hBmN0, hReadN, hNCells]
  wp_steps 2
  have hAl28 : MemWidth.isAligned .W32 (nextMid.metaPtr + 28#64) = true := by
    apply isAligned_w32_of_mod4
    have h48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    rw [BitVec.toNat_add_of_lt (by change nextMid.metaPtr.toNat + 28 < 2 ^ 64; omega)]
    change (nextMid.metaPtr.toNat + 28) % 4 = 0; omega
  let cntMask : BitVec 32 := (2#32 <<< nextMid.activeIdx) - 1#32
  let newFr : BitVec 32 := nextMid.freedMask &&& (-(2#32 <<< nextMid.activeIdx))
  have hFocus28 :
      ((maddrs.ctx ↦ₛ cAct.toBytes) ∗
       (((nextMid.metaPtr ↦₆₄ nextMid.prev) ∗ ((nextMid.metaPtr + 8#64) ↦₆₄ nextMid.next) ∗
         ((nextMid.metaPtr + 16#64) ↦₆₄ nextMid.mem) ∗ ((nextMid.metaPtr + 24#64) ↦₃₂ 0#32) ∗
         ((nextMid.metaPtr + 28#64) ↦₃₂ nextMid.freedMask) ∗
         ((nextMid.metaPtr + 32#64) ↦₆₄ nextMid.packedWord)) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion nextMid.metaPtr 40 a) bv_c) ∗ R) =
      (((nextMid.metaPtr + 28#64) ↦₃₂ nextMid.freedMask) ∗
       ((maddrs.ctx ↦ₛ cAct.toBytes) ∗
        ((nextMid.metaPtr ↦₆₄ nextMid.prev) ∗ ((nextMid.metaPtr + 8#64) ↦₆₄ nextMid.next) ∗
         ((nextMid.metaPtr + 16#64) ↦₆₄ nextMid.mem) ∗ ((nextMid.metaPtr + 24#64) ↦₃₂ 0#32) ∗
         ((nextMid.metaPtr + 32#64) ↦₆₄ nextMid.packedWord)) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion nextMid.metaPtr 40 a) bv_c ∗ R)) := by
    ac_rfl
  rw [hFocus28]
  refine SepWP.seq (sepWP_nf_and32_loop_2ac hb
    (ea := nextMid.metaPtr + 28#64) (oldVal := nextMid.freedMask)
    (newVal := newFr) (cntMask := cntMask) (m4 := nextMid.metaPtr) (m19 := g.metaPtr)
    hAl28 (_ + 1) _ (Nat.lt_succ_self _)
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm])
    (by simp [arm64_norm])
    (by simp [arm64_norm, BitVec.zero_sub]; rw [hSh32]; rfl)
    (by simp [arm64_norm]; rw [hSh32]; rfl)
    (by simp [arm64_norm])
    (by simpa [arm64_norm] using hx19)
    (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
    (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
        exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
               by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
               by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
               by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
               by simpa [calleeSavedVRegs] using cv⟩)) ?_
  intro s1 P1 hpc1 hrun1 ⟨hsp1, hbrk1, hperm1, hProc1, hcs1, hw3_1, hw6_1, hx4_1, hx19_1, hx20_1, hEnt1⟩
  refine SepWP.weaken_pre hEnt1 ?_
  wp_step
  wp_str32_p m2 hm2
  wp_step
  have hFoldAct :
      (((nextMid.metaPtr + 28#64) ↦₃₂ newFr) ∗
       (maddrs.ctx ↦ₛ cAct.toBytes) ∗
       ((nextMid.metaPtr ↦₆₄ nextMid.prev) ∗ ((nextMid.metaPtr + 8#64) ↦₆₄ nextMid.next) ∗
        ((nextMid.metaPtr + 16#64) ↦₆₄ nextMid.mem) ∗
        ((nextMid.metaPtr + 24#64) ↦₃₂ (BitVec.setWidth 32 (s1.readReg64 (.gpr 6#5)) &&&
          BitVec.setWidth 32 (s1.readReg64 (.gpr 3#5)))) ∗
        ((nextMid.metaPtr + 32#64) ↦₆₄ nextMid.packedWord)) ∗
       ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion nextMid.metaPtr 40 a) bv_c ∗ R) =
      ((maddrs.ctx ↦ₛ cAct.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st)
         (writeBytesToMap bv_c nextMid.metaPtr (mkActivatedGroup nextMid).metaBytes) ∗ R) := by
    have hw6' : BitVec.setWidth 32 (s1.readReg64 (.gpr 6#5)) = cntMask := by
      simpa [arm64_norm] using hw6_1
    have hw3' : BitVec.setWidth 32 (s1.readReg64 (.gpr 3#5)) = nextMid.freedMask := by
      simpa [arm64_norm] using hw3_1
    rw [hw6', hw3', ← hBmNW]
    have hCellsAct := metaBytes_eq_cells (mkActivatedGroup nextMid)
    rw [show (mkActivatedGroup nextMid).metaPtr = nextMid.metaPtr from rfl,
        show (mkActivatedGroup nextMid).prev = nextMid.prev from rfl,
        show (mkActivatedGroup nextMid).next = nextMid.next from rfl,
        show (mkActivatedGroup nextMid).mem = nextMid.mem from rfl,
        show (mkActivatedGroup nextMid).availMask = cntMask &&& nextMid.freedMask from rfl,
        show (mkActivatedGroup nextMid).freedMask = newFr from rfl,
        show (mkActivatedGroup nextMid).packedWord = nextMid.packedWord from rfl] at hCellsAct
    rw [hCellsAct]
    ac_rfl
  rw [hFoldAct]
  exact hnext _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun1])
    (by simpa [arm64_norm] using hx19_1)
    (by simpa [arm64_norm] using hx20_1.trans (by simpa [arm64_norm] using hx20))
    (by simpa [arm64_norm] using hsp1)
    (by simpa [arm64_norm] using hbrk1)
    (hm2.trans (by simpa [arm64_norm] using hperm1))
    (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc1; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
    (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs1
        exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
               by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
               by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
               by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
               by simpa [calleeSavedVRegs] using cv⟩)

/-! ## `usageByClass` Decrement Paths -/

abbrev ctxSubUsage (c : CtxFields) (sc : Nat) (hUseL : c.usageByClass.length = 48)
    (hSc48 : sc < 48) (cnt : Nat) : CtxFields :=
  let v := (c.usageByClass[sc]'(hUseL ▸ hSc48)) - BitVec.ofNat 64 cnt
  { c with usageByClass := c.usageByClass.set sc v }

theorem sepWP_nf_usage_dec_0c4 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b)
    {target_pc : BitVec 64} {g : GroupDesc} {cPre : CtxFields}
    {R : SepProp} {s0 s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = b + 0xc4#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 g.sc)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 g.sc)
    (hw6 : s.readReg32 (.gpr 6#5) = BitVec.ofNat 32 g.lastIdx)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = maddrs.ctx)
    (hProc : MallocngProcPreserved s0 s) (hcs : Cs21Preserved s0 s)
    (hSc48 : g.sc < 48) (hLast31 : g.lastIdx ≤ 31)
    (hActL : cPre.active.length = 48) (hUseL : cPre.usageByClass.length = 48)
    (hCont : ∀ s' : State,
      s'.pc = b + 0x1d4#64 → s'.status = .Running →
      s'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 g.sc →
      s'.readReg64 (.gpr 19#5) = g.metaPtr →
      s'.sp = s.sp → s'.brk = s.brk → s'.mem.perm = s.mem.perm →
      MallocngProcPreserved s0 s' → Cs21Preserved s0 s' →
      SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s'
        ((maddrs.ctx ↦ₛ (ctxSubUsage cPre g.sc hUseL hSc48 g.cnt).toBytes) ∗ R)
        post oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s
      ((maddrs.ctx ↦ₛ cPre.toBytes) ∗ R) post oom := by
  have _ := hb
  have hUseAddr : maddrs.ctx + ((BitVec.ofNat 64 g.sc + 0x3a#64) <<< 3) =
      maddrs.ctx + BitVec.ofNat 64 (464 + 8 * g.sc) :=
    congrArg (maddrs.ctx + ·) (sc_usage_off_fin ⟨g.sc, hSc48⟩)
  let oldUse := cPre.usageByClass[g.sc]'(hUseL ▸ hSc48)
  let newUse := oldUse - BitVec.ofNat 64 g.cnt
  obtain ⟨UseRest, hUseRead, hUseWrite⟩ :=
    ctx_focus_update_usage maddrs.ctx cPre hActL hUseL hSc48 newUse
  wp_step
  wp_step
  rw [hUseRead]
  apply step_ldr64_fast (b + 0xcc#64) (b + 0xd0#64)
    (maddrs.ctx + BitVec.ofNat 64 (464 + 8 * g.sc)) oldUse
  · rfl
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, extendVal, arm64_norm, hx20]; exact Prod.ext hUseAddr rfl
  · wp_sep_access_fast
  · bv_omega
  wp_step
  apply step_str64_fast (b + 0xd4#64) (b + 0xd8#64)
    (maddrs.ctx + BitVec.ofNat 64 (464 + 8 * g.sc)) newUse
  · rfl
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, extendVal, arm64_norm, hx20]; exact Prod.ext hUseAddr rfl
  · simp only [arm64_norm]
    have hw6' : BitVec.truncate 32 (s.readReg64 (.gpr 6#5)) = BitVec.ofNat 32 g.lastIdx := by
      simpa [arm64_norm] using hw6
    rw [hw6', lastIdx_cnt_sub_fin ⟨g.lastIdx, by omega⟩]
  · wp_sep_access_fast
  · bv_omega
  intro m1 hm1 _
  rw [hUseWrite]
  wp_step
  exact hCont _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simpa [arm64_norm] using hx0) (by simpa [arm64_norm] using hx19)
    (by simp [arm64_norm]) (by simp [arm64_norm]) hm1
    (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
    (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
        exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
               by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
               by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
               by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
               by simpa [calleeSavedVRegs] using cv⟩)

theorem sepWP_nf_usage_dec_0bc [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b)
    {target_pc : BitVec 64} {g : GroupDesc} {cPre : CtxFields}
    {R : SepProp} {s0 s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = b + 0xbc#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 g.sc)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 g.sc)
    (hw6 : s.readReg32 (.gpr 6#5) = BitVec.ofNat 32 g.lastIdx)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hProc : MallocngProcPreserved s0 s) (hcs : Cs21Preserved s0 s)
    (hSc48 : g.sc < 48) (hLast31 : g.lastIdx ≤ 31)
    (hActL : cPre.active.length = 48) (hUseL : cPre.usageByClass.length = 48)
    (hCont : ∀ s' : State,
      s'.pc = b + 0x1d4#64 → s'.status = .Running →
      s'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 g.sc →
      s'.readReg64 (.gpr 19#5) = g.metaPtr →
      s'.sp = s.sp → s'.brk = s.brk → s'.mem.perm = s.mem.perm →
      MallocngProcPreserved s0 s' → Cs21Preserved s0 s' →
      SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s'
        ((maddrs.ctx ↦ₛ (ctxSubUsage cPre g.sc hUseL hSc48 g.cnt).toBytes) ∗ R)
        post oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s
      ((maddrs.ctx ↦ₛ cPre.toBytes) ∗ R) post oom := by
  have _ := hb
  wp_steps 1
  exact sepWP_nf_usage_dec_0c4 hb
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simpa [arm64_norm] using hx0) (by simpa [arm64_norm] using hx8)
    (by simpa [arm64_norm] using hw6) (by simpa [arm64_norm] using hx19)
    (by simp [arm64_norm])
    (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
    (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
        exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
               by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
               by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
               by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
               by simpa [calleeSavedVRegs] using cv⟩)
    hSc48 hLast31 hActL hUseL
    (fun s' hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
      hCont s' hpc' hrun' hx0' hx19'
        (hsp'.trans (by simp [arm64_norm]))
        (hbrk'.trans (by simp [arm64_norm]))
        (hperm'.trans (by simp [arm64_norm]))
        hProc' hcs')

set_option maxHeartbeats 400000 in
theorem sepWP_nf_usage_dec_1c4 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b)
    {target_pc : BitVec 64} {st : MallocngSt} {g : GroupDesc}
    {cPre : CtxFields} {bvDeq : BitVec 64 → BitVec 8}
    {R : SepProp} {s0 s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = b + 0x1c4#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = pageOf maddrs.ctx)
    (hProc : MallocngProcPreserved s0 s) (hcs : Cs21Preserved s0 s)
    (hSc48 : g.sc < 48) (hLast31 : g.lastIdx ≤ 31)
    (hActL : cPre.active.length = 48) (hUseL : cPre.usageByClass.length = 48)
    (hDomNd : st.masterDom.Nodup)
    (hOwnG : ∀ a, InRegion g.metaPtr 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom)
    (hReadG : readBytesFromMap bvDeq g.metaPtr 40 =
      ({ g with prev := 0#64, next := 0#64 } : GroupDesc).metaBytes)
    (hCont : ∀ s' : State,
      s'.pc = b + 0x1d4#64 → s'.status = .Running →
      s'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 g.sc →
      s'.readReg64 (.gpr 19#5) = g.metaPtr →
      s'.sp = s.sp → s'.brk = s.brk → s'.mem.perm = s.mem.perm →
      MallocngProcPreserved s0 s' → Cs21Preserved s0 s' →
      SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s'
        ((maddrs.ctx ↦ₛ (ctxSubUsage cPre g.sc hUseL hSc48 g.cnt).toBytes) ∗
         ByteMap st.masterDom (OwnedRwByte st) bvDeq ∗ R)
        post oom) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s
      ((maddrs.ctx ↦ₛ cPre.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) bvDeq ∗ R) post oom := by
  have _ := hb
  have hBmG0 := (byteMap_update40 hDomNd bvDeq (P := OwnedRwByte st)
    (m := g.metaPtr) (bs := ({ g with prev := 0#64, next := 0#64 } : GroupDesc).metaBytes)
    (GroupDesc.metaBytes_length _) hOwnG).1
  have hGCells := metaBytes_eq_cells ({ g with prev := 0#64, next := 0#64 } : GroupDesc)
  have hZPw : ({ g with prev := 0#64, next := 0#64 } : GroupDesc).packedWord = g.packedWord := rfl
  rw [hZPw] at hGCells
  dsimp only [] at hGCells
  obtain ⟨Rest16, hP16⟩ := pointsTo64_focus16 (g.metaPtr + 32#64) g.packedWord
  rw [hBmG0, hReadG, hGCells, hP16]
  apply step_ldr16_fast (b + 0x1c4#64) (b + 0x1c8#64)
    (g.metaPtr + 32#64) (g.packedWord.truncate 16)
  · exact hpc
  · exact hrun
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, arm64_norm, hx19]
  · wp_sep_access_fast
  · bv_omega
  rw [← hP16]
  have hLow := packedWord_low8_low16 g hLast31 hSc48
  have hUbfxSc : evalBitfield .W64 .UBFM 0#64 ((g.packedWord.truncate 16).zeroExtend 64) 6 11 =
      BitVec.ofNat 64 g.sc := (ubfx_sc_from_u16 _).trans hLow.2
  have hScProps := sc_cmp47_and_active_off_fin ⟨g.sc, hSc48⟩
  have hLeCond := hScProps.1
  have hScLsb31 := hScProps.2.1
  have hScShrAnd := hScProps.2.2.1
  have hScAnd := hScProps.2.2.2.1
  wp_step
  wp_step
  wp_step
  apply step_ldr8_64_fast (b + 0x2cc#64) (b + 0x2d0#64)
    (g.metaPtr + 32#64) g.packedWord
  · simp only [arm64_norm]
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, arm64_norm, hx19]
  · wp_sep_access_fast
  · bv_omega
  rw [← hGCells, ← hReadG, ← hBmG0]
  wp_step
  wp_step
  wp_step
  apply blkPC_b05_pairStep_0xc0 b (fun _ => none) hb
    (by simpa [arm64_norm] using hx20) (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
  exact sepWP_nf_usage_dec_0c4 hb
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm])
    (by simp [arm64_norm])
    (by simp [arm64_norm]; exact hLow.1)
    (by simpa [arm64_norm] using hx19)
    (by simp [arm64_norm])
    (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
    (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
        exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
               by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
               by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
               by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
               by simpa [calleeSavedVRegs] using cv⟩)
    hSc48 hLast31 hActL hUseL
    (fun s' hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
      hCont s' hpc' hrun' hx0' hx19'
        (hsp'.trans (by simp [arm64_norm]))
        (hbrk'.trans (by simp [arm64_norm]))
        (hperm'.trans (by simp [arm64_norm]))
        hProc' hcs')

/-! ## Singleton Dequeue Paths -/

abbrev NfDeqCont [MallocngMultiPlacement]
    (b target_pc : BitVec 64) (st : MallocngSt) (g : GroupDesc)
    (R : SepProp) (s0 s : State) (post : State → SepProp → Prop) (oom : State → SepProp) : Prop :=
  ∀ (active1 usage1 : List (BitVec 64)) (actLists1 : List (List (BitVec 64)))
    (gsDeq : List GroupDesc) (bvDeq : BitVec 64 → BitVec 8) (s' : State),
    DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq →
    s'.pc = b + 0x1d4#64 → s'.status = .Running →
    s'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 g.sc →
    s'.readReg64 (.gpr 19#5) = g.metaPtr →
    s'.sp = s.sp → s'.brk = s.brk → s'.mem.perm = s.mem.perm →
    MallocngProcPreserved s0 s' → Cs21Preserved s0 s' →
    SepWP (blkPC_b05.rebase b (fun _ => none)) target_pc s'
      ((maddrs.ctx ↦ₛ { st.ctx with active := active1, usageByClass := usage1 }.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) bvDeq ∗ R)
      post oom

set_option maxHeartbeats 400000 in
theorem sepWP_nf_dequeue_singleton_120 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b)
    {inflight : Nat} {brkStart : BitVec 64} {liveCost peakCost : Nat}
    {target_pc : BitVec 64} {st : MallocngSt} {g : GroupDesc}
    {R : SepProp} {s0 s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = b + 0x120#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = g.metaPtr)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 g.sc)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = pageOf maddrs.ctx)
    (hProc : MallocngProcPreserved s0 s) (hcs : Cs21Preserved s0 s)
    (hwf : MallocngWFInflight inflight maddrs.base brkStart s0.brk liveCost peakCost st)
    (hg : g ∈ st.groups) (hSc48 : g.sc < 48) (hNxSelf : g.next = g.metaPtr)
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
  obtain ⟨_, _, _, _, hOwnG, hDeq⟩ := dequeue_singleton hwf hg hSc48 hNxSelf
  obtain ⟨_, hmAl, hmFit, hReadG0, _⟩ := meta_ownedRw_of_mem_groups hwf hg
  have hLast31 : g.lastIdx ≤ 31 := (hwf.groups_wf g hg).2.1
  let active1 := st.ctx.active.set g.sc 0#64
  let cAct : CtxFields := { st.ctx with active := active1 }
  let gZero : GroupDesc := { g with prev := 0#64, next := 0#64 }
  let bvDeq := writeBytesToMap st.byteVal g.metaPtr gZero.metaBytes
  obtain ⟨CtxRest0, hCtxRead0, hCtxWrite0⟩ :=
    ctx_focus_update_active maddrs.ctx st.ctx hwf.ctx_lens.1 hSc48 0#64
  have hActLt0 : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
  generalize hOldAct : (st.ctx.active[g.sc]'hActLt0) = oldAct at hCtxRead0
  wp_step
  wp_step
  rw [hCtxRead0]
  apply step_str64_fast (b + 0x128#64) (b + 0x12c#64)
    (maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc)) 0#64
  · rfl
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, extendVal, arm64_norm]; exact Prod.ext hActAddr rfl
  · rfl
  · wp_sep_access_fast
  · bv_omega
  intro m1 hm1 _
  rw [hCtxWrite0]
  wp_step
  have ⟨hBmG0, hBmGW⟩ := byteMap_update40 hwf.masterDom_wf.1 st.byteVal (P := OwnedRwByte st)
    (m := g.metaPtr) (bs := gZero.metaBytes) (GroupDesc.metaBytes_length _) hOwnG
  rw [hBmG0, hReadG0, metaBytes_eq_cells g]
  wp_stp64_p m2 hm2
  have hFoldZ :
      ((maddrs.ctx ↦ₛ cAct.toBytes) ∗
       (((g.metaPtr ↦₆₄ 0#64) ∗ ((g.metaPtr + 8#64) ↦₆₄ 0#64) ∗
         ((g.metaPtr + 16#64) ↦₆₄ g.mem) ∗ ((g.metaPtr + 24#64) ↦₃₂ g.availMask) ∗
         ((g.metaPtr + 28#64) ↦₃₂ g.freedMask) ∗ ((g.metaPtr + 32#64) ↦₆₄ g.packedWord)) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal) ∗ R) =
      ((maddrs.ctx ↦ₛ cAct.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) bvDeq ∗ R) := by
    have hZCells := metaBytes_eq_cells gZero
    have hZPw : gZero.packedWord = g.packedWord := rfl
    rw [hZPw] at hZCells
    dsimp only [gZero] at hZCells
    rw [← hZCells, hBmGW]
  change SepWP _ _ _ ((maddrs.ctx ↦ₛ cAct.toBytes) ∗ _ ∗ R) _ _
  rw [hFoldZ]
  wp_steps 4
  have hAct1Len : cAct.active.length = 48 := by simp [cAct, active1, hwf.ctx_lens.1]
  have hAct1Get : cAct.active[g.sc]'(hAct1Len ▸ hSc48) = 0#64 := by
    dsimp only [cAct, active1]; exact List.getElem_set_self _
  obtain ⟨CtxRest1, hCtxRead1, _⟩ :=
    ctx_focus_update_active maddrs.ctx cAct hAct1Len hSc48 0#64
  rw [hCtxRead1, hAct1Get]
  apply step_ldr64_fast (b + 0x26c#64) (b + 0x270#64)
    (maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc)) 0#64
  · simp [arm64_norm]
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, extendVal, arm64_norm]; exact Prod.ext hActAddr rfl
  · wp_sep_access_fast
  · bv_omega
  rw [← hAct1Get, ← hCtxRead1]
  wp_step
  have hUse1Len : cAct.usageByClass.length = 48 := hwf.ctx_lens.2.1
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
    hSc48 hLast31 hAct1Len hUse1Len hwf.masterDom_wf.1 hOwnG hDeq.g_zero_bytes
    (fun s' hpc' hrun' hx0' hx19' hsp' hbrk' hperm' hProc' hcs' =>
      hCont active1 _ _ _ bvDeq s' hDeq hpc' hrun' hx0' hx19'
        (hsp'.trans (by simp [arm64_norm]))
        (hbrk'.trans (by simp [arm64_norm]))
        (hperm'.trans (hm2.trans hm1))
        hProc' hcs')

theorem sepWP_nf_dequeue_singleton_114 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b)
    {inflight : Nat} {brkStart : BitVec 64} {liveCost peakCost : Nat}
    {target_pc : BitVec 64} {st : MallocngSt} {g : GroupDesc}
    {R : SepProp} {s0 s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = b + 0x114#64) (hrun : s.status = .Running)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 g.sc)
    (hx19 : s.readReg64 (.gpr 19#5) = g.metaPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = pageOf maddrs.ctx)
    (hProc : MallocngProcPreserved s0 s) (hcs : Cs21Preserved s0 s)
    (hwf : MallocngWFInflight inflight maddrs.base brkStart s0.brk liveCost peakCost st)
    (hg : g ∈ st.groups) (hSc48 : g.sc < 48) (hNxSelf : g.next = g.metaPtr)
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
  have hHeadEq := (dequeue_singleton hwf hg hSc48 hNxSelf).1
  obtain ⟨CtxRest0, hCtxRead0, _⟩ :=
    ctx_focus_update_active maddrs.ctx st.ctx hwf.ctx_lens.1 hSc48 0#64
  wp_step
  wp_step
  rw [hCtxRead0, hHeadEq]
  apply step_ldr64_fast (b + 0x11c#64) (b + 0x120#64)
    (maddrs.ctx + BitVec.ofNat 64 (80 + 8 * g.sc)) g.metaPtr
  · rfl
  · simp only [arm64_norm, hrun]
  · wp_close_fetch_cl
  · rfl
  · simp only [evalAddrMode, extendVal, arm64_norm]; exact Prod.ext hActAddr rfl
  · wp_sep_access_fast
  · bv_omega
  rw [← hHeadEq, ← hCtxRead0]
  exact sepWP_nf_dequeue_singleton_120 hb
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simpa [arm64_norm] using hHeadEq) (by simpa [arm64_norm] using hx8)
    (by simpa [arm64_norm] using hx19) (by simpa [arm64_norm] using hx20)
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

end VerifiedLibraries.Mallocng.Proofs
