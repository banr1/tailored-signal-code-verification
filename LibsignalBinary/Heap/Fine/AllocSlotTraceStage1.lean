/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotStage1
public import LibsignalBinary.Heap.Fine.AllocGroupTraceDefs

/-!
# Fine-Trace Stage 1 Helpers for Placed `alloc_slot`

Lifts `AllocSlotStPres`, `wp_allocSlot_activate`, and `wp_allocSlot_bump_active` (`blk08`) to
`AllocSlotStPresFine`, threading `SameGroupsSlotKind` across `activate_group` and `bump_activeIdx`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## `AllocSlotStPresFine` and Single-Group Update -/

/-- `AllocSlotStPres` strengthened with `SameGroupsSlotKind st.groups st0.groups`. -/
abbrev AllocSlotStPresFine (sc : Nat) (st0 st : MallocngSt) : Prop :=
  SameGroupsSlotKind st.groups st0.groups ∧ AllocSlotStPres sc st0 st

theorem AllocSlotStPresFine.rfl {sc : Nat} {st : MallocngSt} : AllocSlotStPresFine sc st st :=
  ⟨SameGroupsSlotKind.refl st.groups, AllocSlotStPres.rfl⟩

theorem AllocSlotStPresFine.trans {sc : Nat} {st0 st1 st2 : MallocngSt}
    (h01 : AllocSlotStPresFine sc st0 st1) (h12 : AllocSlotStPresFine sc st1 st2) :
    AllocSlotStPresFine sc st0 st2 :=
  ⟨SameGroupsSlotKind.trans h12.1 h01.1, AllocSlotStPres.trans h01.2 h12.2⟩

private theorem list_forall2_of_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} (_hlen : xs.length = ys.length)
      (_h : ∀ i (hx : i < xs.length) (hy : i < ys.length), R (xs[i]'hx) (ys[i]'hy)),
      List.Forall₂ R xs ys
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, hlen, h =>
    .cons (h 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))
      (list_forall2_of_getElem (Nat.succ.inj hlen) fun i hx hy =>
        h (i + 1) (Nat.succ_lt_succ hx) (Nat.succ_lt_succ hy))

theorem sameGroupsSlotKind_update_one {gs : List GroupDesc} (hnd : (gs.map (·.metaPtr)).Nodup)
    {g g1 : GroupDesc} (hg : g ∈ gs)
    (hGeom : GroupSameGeom g1 g) (hSlots : List.Forall₂ SlotSameKind g1.slots g.slots) :
    SameGroupsSlotKind (gs.map fun u => if u.metaPtr == g.metaPtr then g1 else u) gs :=
  SameGroupsSlotKind.of_map fun u hu => by
    by_cases hEq : u.metaPtr == g.metaPtr
    · have huEq : u = g := mem_groups_eq_of_metaPtr hnd hu hg (beq_iff_eq.mp hEq)
      subst huEq
      simp only [hEq, ↓reduceIte]
      exact ⟨hGeom, hSlots⟩
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte]
      exact ⟨GroupSameGeom.refl u, list_forall2_slotSameKind_refl u.slots⟩

/-! ## Bitvector and Alignment Helpers -/

private theorem metaPtr_add28_aligned {m : BitVec 64}
    (hMod8 : m.toNat % 8 = 0) (hBnd : m.toNat + 40 ≤ 2 ^ 48) :
    MemWidth.isAligned .W32 (m + 28#64) = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  change ((m + 28#64).toNat &&& 3) = 0
  rw [add_ofNat_toNat (by omega), show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem sizeClass_stride_all :
    ((List.range 48).all fun sc =>
      ((BitVec.ofNat 64 (2 * sc) == (BitVec.ofNat 64 sc) <<< 1) &&
       ((BitVec.setWidth 32 (BitVec.ofNat 16 (sizeClass sc)) <<< 4) ==
         BitVec.ofNat 32 (slotStride sc)))) = true := by decide +kernel

private theorem sizeClass_stride_props {sc : Nat} (hsc : sc < 48) :
    BitVec.ofNat 64 (2 * sc) = (BitVec.ofNat 64 sc) <<< 1 ∧
    (BitVec.setWidth 32 (BitVec.ofNat 16 (sizeClass sc)) <<< 4) =
      BitVec.ofNat 32 (slotStride sc) := by
  have h := List.all_eq_true.mp sizeClass_stride_all sc (List.mem_range.mpr hsc)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

private theorem and_imm32_0x1f_byte (b0 : BitVec 8) :
    BitVec.setWidth 32 (BitVec.setWidth 64 b0 &&& 0x1f0000001f#64) =
      b0.zeroExtend 32 &&& 0x1f#32 := by
  bv_robdd

private theorem bfxil_w32_0_5_byte (oldB : BitVec 8) (v : BitVec 32) :
    BitVec.zeroExtend 8
      (BitVec.zeroExtend 64 oldB &&& 0xffffffffffffffe0#64 |||
        (BitVec.setWidth 64 v >>> 0 &&& 31#64)) =
    (oldB &&& 0xe0#8) ||| (v.truncate 8 &&& 0x1f#8) := by
  bv_robdd

/-! ## `activate_group` and `bump_active` Symbolic Execution -/

theorem wp_allocSlot_activate_fine [MallocngMultiPlacement]
    (_hw0 : Blk08HasWords0 mallocngFaultSvc) (_hr0 : Blk08Range0)
    (hw348 : Blk08HasWords348 mallocngFaultSvc) (hr348 : Blk08Range348)
    {inflight sc : Nat} (hsc : sc < 48) {γ : GhostName} {brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : ∀ h1 : sc < st.ctx.active.length, st.ctx.active[sc]'h1 = g.metaPtr)
    (hAv0 : g.availMask = 0#32)
    (hActFrNe : ((2#32 <<< g.activeIdx) - 1#32) &&& g.freedMask ≠ 0#32)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_activate) (hrun : s.status = .Running)
    (hx2 : s.readReg64 .x2 = g.metaPtr) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_bounces_chk) s
      (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)
      (fun sf P_f =>
        ∃ st1 : MallocngSt, ∃ g1 ∈ st1.groups,
          sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
          PureStatePres s sf ∧
          AllocSlotStPresFine sc st st1 ∧
          g1.metaPtr = g.metaPtr ∧ g1.sc = sc ∧ g1.availMask ≠ 0#32 ∧
          (∀ h1 : sc < st1.ctx.active.length, st1.ctx.active[sc]'h1 = g1.metaPtr) ∧
          sf.readReg64 .x2 = g1.metaPtr ∧
          sf.readReg64 .x0 = BitVec.zeroExtend 64 g1.availMask ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x6 →
            sf.readReg64 r = s.readReg64 r) ∧
          P_f = (MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st1 ∗ Frame))
      (fun _ => ⌜False⌝) := by
  apply sepWP_coreSt_wf; intro hwf
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  obtain ⟨_, hMod8, hMBnd, _, _⟩ := meta_ownedRw_of_mem_groups hwf hg
  have hAlign28 := metaPtr_add28_aligned hMod8 hMBnd
  obtain ⟨RestAct, hBmAct⟩ := byteMap_focus_activeByte hwf hg
  obtain ⟨hg1Mem, hwf1, hCnt1, hEff1, hDyn1, hProt1, hMap1, hBmExt, hBmAbs⟩ :=
    tryAvail_activate_group_absorb hwf hsc hg hScEq (hHead h1) hAv0
  let cntMask : BitVec 32 := (2#32 <<< g.activeIdx) - 1#32
  let hiMask : BitVec 32 := -(2#32 <<< g.activeIdx)
  let newAvail : BitVec 32 := cntMask &&& g.freedMask
  let newFreed : BitVec 32 := g.freedMask &&& hiMask
  refine SepWP.seq (mid := mbase 8 + allocSlotOff_11c)
    (Mid := fun s1 P1 =>
      s1.sp = s.sp ∧ s1.spAligned = s.spAligned ∧ PureStatePres s s1 ∧ s1.mem = s.mem ∧
      s1.readReg64 .x0 = g.mem ∧ s1.readReg64 .x2 = g.metaPtr ∧
      s1.readReg64 .x3 = 2#64 ∧ s1.readReg64 .x5 = g.metaPtr + 28#64 ∧
      (∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x5 → s1.readReg64 r = s.readReg64 r) ∧
      P1 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)) ?_ ?_
  · conv => arg 4; rw [coreSt_eq_parts hwf, hBmExt, GroupDesc.metaBytes_pointsTo, hAv0]; simp only [sepConj_assoc]
    dsimp only [allocSlotOff_activate, allocSlotOff_11c] at hpc ⊢
    wp_sym_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], psp_rfl, rfl,
       by simp, by simpa using hx2, by simp, by simp,
       fun r r0 r3 r5 => ?_,
       by rw [coreSt_eq_parts hwf, hBmExt, GroupDesc.metaBytes_pointsTo, hAv0]; simp only [sepConj_assoc]⟩
    simp only [State.readReg64_setPC,
      State.readReg64_writeReg64_ne _ _ _ _ r5, State.readReg64_writeReg64_ne _ _ _ _ r3,
      State.readReg64_writeReg64_ne _ _ _ _ r0]
  · rintro s1 P1 hpc1 hrun1 ⟨hsp1, hal1, hpsp1, hmem1, hs1_0, hs1_2, hs1_3, hs1_5, hr1, rfl⟩
    refine SepWP.seq (mid := mbase 8 + allocSlotOff_stxr_entry)
      (Mid := fun s2 P2 =>
        s2.sp = s.sp ∧ s2.spAligned = s.spAligned ∧ PureStatePres s s2 ∧ s2.mem = s.mem ∧
        s2.readReg64 .x0 = BitVec.zeroExtend 64 cntMask ∧
        s2.readReg64 .x2 = g.metaPtr ∧
        s2.readReg64 .x3 = BitVec.zeroExtend 64 hiMask ∧
        s2.readReg64 .x5 = g.metaPtr + 28#64 ∧
        (∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x5 → s2.readReg64 r = s.readReg64 r) ∧
        P2 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)) ?_ ?_
    · have hw1_3 : BitVec.setWidth 32 (s1.readReg64 (Reg.gpr 3#5)) = 2#32 := by simp [hs1_3]
      have hIdxNat : (g.activeByte.toNat % 4294967296 &&& 31) % 32 = g.activeByte.toNat &&& 31 := by
        have hLt4G : g.activeByte.toNat < 4294967296 := Nat.lt_trans g.activeByte.isLt (by decide)
        rw [Nat.mod_eq_of_lt hLt4G]
        have hAndLt : (g.activeByte.toNat &&& 31) < 32 := by
          rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
          exact Nat.mod_lt _ (by decide)
        exact Nat.mod_eq_of_lt hAndLt
      conv => arg 4; rw [coreSt_eq_parts hwf, hBmAct]; simp only [sepConj_assoc]
      dsimp only [allocSlotOff_11c, allocSlotOff_stxr_entry] at hpc1 ⊢
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun1])
        ⟨by simpa using hsp1, by simpa [State.spAligned] using hal1, hpsp1.trans psp_rfl, hmem1,
         by simp [cntMask, GroupDesc.activeIdx, hIdxNat],
         by simpa using hs1_2,
         by simp [hiMask, GroupDesc.activeIdx, hIdxNat],
         by simpa using hs1_5,
         fun r r0 r3 r5 => ?_,
         by rw [coreSt_eq_parts hwf, hBmAct]; simp only [sepConj_assoc]⟩
      refine Eq.trans ?_ (hr1 r r0 r3 r5)
      simp only [State.readReg64_setPC,
        State.readReg64_writeReg64_ne _ _ _ _ r3, State.readReg64_writeReg64_ne _ _ _ _ r0]
    · rintro s2 P2 hpc2 hrun2 ⟨hsp2, hal2, hpsp2, hmem2, hs2_0, hs2_2, hs2_3, hs2_5, hr2, rfl⟩
      refine SepWP.seq (mid := mbase 8 + allocSlotOff_stxr_loop)
        (Mid := fun s3 P3 =>
          s3.sp = s.sp ∧ s3.spAligned = s.spAligned ∧ PureStatePres s s3 ∧ s3.mem = s.mem ∧
          s3.readReg64 .x0 = BitVec.zeroExtend 64 cntMask ∧
          s3.readReg64 .x1 = BitVec.zeroExtend 64 g.freedMask ∧
          s3.readReg64 .x2 = g.metaPtr ∧
          s3.readReg64 .x4 = BitVec.zeroExtend 64 newFreed ∧
          s3.readReg64 .x5 = g.metaPtr + 28#64 ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → s3.readReg64 r = s.readReg64 r) ∧
          P3 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)) ?_ ?_
      · have hw2_3 : BitVec.setWidth 32 (s2.readReg64 (Reg.gpr 3#5)) = hiMask := by simp [hs2_3]
        conv => arg 4; rw [coreSt_eq_parts hwf, hBmExt, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]
        dsimp only [allocSlotOff_stxr_entry, allocSlotOff_stxr_loop] at hpc2 ⊢
        wp_sym_steps
        refine SepWP.done rfl (by simp [hrun2])
          ⟨by simpa using hsp2, by simpa [State.spAligned] using hal2, hpsp2.trans psp_rfl, hmem2,
           by simpa using hs2_0, by simp, by simpa using hs2_2,
           by simp [newFreed, hiMask], by simpa using hs2_5,
           fun r r0 r1 r3 r4 r5 => ?_,
           by rw [coreSt_eq_parts hwf, hBmExt, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]⟩
        refine Eq.trans ?_ (hr2 r r0 r3 r5)
        simp only [State.readReg64_setPC,
          State.readReg64_writeReg64_ne _ _ _ _ r4, State.readReg64_writeReg64_ne _ _ _ _ r1]
      · rintro s3 P3 hpc3 hrun3 ⟨hsp3, hal3, hpsp3, hmem3, hs3_0, hs3_1, hs3_2, hs3_4, hs3_5, hr3, rfl⟩
        let RestBm := ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal
        let StxrFrame : SepProp :=
          (g.metaPtr ↦₆₄ g.prev) ∗ ((g.metaPtr + 8#64) ↦₆₄ g.next) ∗
          ((g.metaPtr + 16#64) ↦₆₄ g.mem) ∗ ((g.metaPtr + 24#64) ↦₃₂ g.availMask) ∗
          ((g.metaPtr + 32#64) ↦₆₄ g.packedWord) ∗
          RestBm ∗
          (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
          ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st) ∗
          MallocngCoreFixedA γ maddrs st ∗ Frame
        have hPreStxr : (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame) =
            (((g.metaPtr + 28#64) ↦₃₂ g.freedMask) ∗ StxrFrame) := by
          rw [coreSt_eq_parts hwf, hBmExt, GroupDesc.metaBytes_pointsTo]
          simp only [StxrFrame, RestBm, sepConj_assoc]
          ac_rfl
        rw [hPreStxr]
        refine SepWP.seq
          (wp_allocSlot_stxr_loop hw348 hr348 (s3.exclFails.length + 1) s3
            (g.metaPtr + 28#64) g.freedMask newFreed StxrFrame (Nat.lt_succ_self _)
            hpc3 hrun3 hAlign28 hs3_5 hs3_1 hs3_4) ?_
        rintro s4 P4 hpc4 hrun4 ⟨_, hsp4, hal4, hpsp4, _, hr4, rfl⟩
        have hs4_0 : s4.readReg64 .x0 = BitVec.zeroExtend 64 cntMask := (hr4 .x0 (by decide)).trans hs3_0
        have hs4_1 : s4.readReg64 .x1 = BitVec.zeroExtend 64 g.freedMask := (hr4 .x1 (by decide)).trans hs3_1
        have hs4_2 : s4.readReg64 .x2 = g.metaPtr := (hr4 .x2 (by decide)).trans hs3_2
        have hw4_0 : BitVec.setWidth 32 (s4.readReg64 (Reg.gpr 0#5)) = cntMask := by simp [hs4_0]
        have hw4_1 : BitVec.setWidth 32 (s4.readReg64 (Reg.gpr 1#5)) = g.freedMask := by simp [hs4_1]
        conv => arg 4; simp only [StxrFrame, sepConj_assoc]
        dsimp only [allocSlotOff_act_store, allocSlotOff_bounces_chk] at hpc4 ⊢
        wp_sym_steps
        let newSlots : List SlotState :=
          List.ofFn fun i : Fin g.slots.length =>
            if i.1 ≤ g.activeIdx ∧ g.slots[i.1]'i.2 = .freeInactive then .freeAvail else g.slots[i.1]'i.2
        let g1 : GroupDesc := { g with availMask := newAvail, freedMask := newFreed, slots := newSlots }
        let fG : GroupDesc → GroupDesc := fun u => if u.metaPtr == g.metaPtr then g1 else u
        let h2L : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hsc
        let st1 : MallocngSt := { st with
          ctx := { st.ctx with active := st.ctx.active.set sc g.metaPtr }
          groups := st.groups.map fG
          activeLists := st.activeLists.set sc (st.activeLists[sc]'h2L)
          byteVal := writeBytesToMap st.byteVal g.metaPtr g1.metaBytes }
        have hNewSlots : List.Forall₂ SlotSameKind newSlots g.slots :=
          list_forall2_of_getElem (by simp [newSlots]) fun i hi1 hi2 => by
            simp only [newSlots, List.getElem_ofFn]
            split
            · rename_i hCond; exact Or.inr ⟨rfl, by rw [hCond.2]; rfl⟩
            · exact Or.inl rfl
        have hSame1 : SameGroupsSlotKind st1.groups st.groups :=
          sameGroupsSlotKind_update_one hwf.groups_nodup.1 hg ⟨rfl, rfl, rfl, rfl, rfl⟩ hNewSlots
        have hCtxEq : st1.ctx = st.ctx := by
          have hSetId : st.ctx.active.set sc g.metaPtr = st.ctx.active := by
            rw [← hHead h1, List.set_getElem_self]
          cases hc : st.ctx; simp [st1, hc] at hSetId ⊢; exact hSetId
        have hBrkEq : s4.brk = s.brk := (hpsp3.trans hpsp4).2.1
        have hwf1' : MallocngWFInflight inflight maddrs.base brkStart s4.brk liveCost peakCost st1 :=
          hBrkEq.symm ▸ hwf1
        refine SepWP.done rfl (by simp [hrun4])
          ⟨st1, g1, hg1Mem, by simp [hrun4], by simpa using hsp4.trans hsp3,
           by simpa [State.spAligned] using hal4.trans hal3,
           (hpsp3.trans hpsp4).trans psp_rfl,
           ⟨hSame1, ⟨rfl, rfl, hEff1, hCnt1, rfl, hDyn1, by simp [hCtxEq], fun _ _ _ _ => by simp [hCtxEq],
            groupsGrpMono_map_ite hg g.metaPtr rfl (Nat.le_refl _)⟩⟩,
           rfl, hScEq, hActFrNe,
           fun h1' => by simp [st1, g1],
           by simpa using hs4_2,
           by simp [g1, newAvail, cntMask, BitVec.and_comm],
           fun r r0 r1 r3 r4 r5 r6 => ?_, ?_⟩
        · refine Eq.trans ?_ ((hr4 r r6).trans (hr3 r r0 r1 r3 r4 r5))
          simp only [State.readReg64_setPC, State.readReg64_setMem,
            State.readReg64_writeReg64_ne _ _ _ _ r0]
        · simp only [State.setPC, State.setMem, State.writeReg64] at hwf1' ⊢
          have hMetaFold : (((g.metaPtr + 28#64) ↦₃₂ newFreed) ∗
              (g.metaPtr ↦₆₄ g.prev) ∗ ((g.metaPtr + 8#64) ↦₆₄ g.next) ∗
              (g.metaPtr + 16#64) ↦₆₄ g.mem ∗ ((g.metaPtr + 24#64) ↦₃₂ newAvail) ∗
              ((g.metaPtr + 32#64) ↦₆₄ g.packedWord)) = (g.metaPtr ↦ₛ g1.metaBytes) := by
            rw [GroupDesc.metaBytes_pointsTo g.metaPtr g1]
            have hPkd : g1.packedWord = g.packedWord := rfl
            rw [hPkd]; dsimp only [g1]; ac_rfl
          have hFix : MallocngCoreFixedA γ maddrs st = MallocngCoreFixedA γ maddrs st1 := rfl
          have hCtxPts : (maddrs.ctx ↦ₛ st.ctx.toBytes) = (maddrs.ctx ↦ₛ st1.ctx.toBytes) := by
            rw [hCtxEq]
          dsimp only [newAvail, cntMask] at hMetaFold
          rw [coreSt_eq_parts hwf1', ← hBmAbs, ← hMetaFold, hCtxPts, hProt1, hMap1, hFix]
          dsimp only [RestBm, st1, g1, fG, newSlots, newAvail, newFreed, cntMask, hiMask]
          simp only [sepConj_assoc]; ac_rfl

theorem wp_allocSlot_bump_active_fine [MallocngMultiPlacement]
    (_hw0 : Blk08HasWords0 mallocngFaultSvc) (_hr0 : Blk08Range0)
    (hw348 : Blk08HasWords348 mallocngFaultSvc) (hr348 : Blk08Range348)
    {inflight sc : Nat} (hsc : sc < 48) {γ : GhostName} {brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : ∀ h1 : sc < st.ctx.active.length, st.ctx.active[sc]'h1 = g.metaPtr)
    (hAv0 : g.availMask = 0#32) (hLt : g.activeIdx < g.lastIdx)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_bump) (hrun : s.status = .Running)
    (hx4 : s.readReg64 .x4 = g.metaPtr) (hx5 : s.readReg64 .x5 = g.mem)
    (hw3 : s.readReg32 .x3 = BitVec.ofNat 32 g.activeIdx) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_activate) s
      (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
       MallocngRoTablesA maddrs ∗ Frame)
      (fun sf P_f =>
        ∃ st1 : MallocngSt, ∃ g1 ∈ st1.groups,
          sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
          PureStatePres s sf ∧
          AllocSlotStPresFine sc st st1 ∧
          g1.metaPtr = g.metaPtr ∧ g1.sc = sc ∧ g1.availMask = 0#32 ∧
          ((2#32 <<< g1.activeIdx) - 1#32) &&& g1.freedMask ≠ 0#32 ∧
          (∀ h1 : sc < st1.ctx.active.length, st1.ctx.active[sc]'h1 = g1.metaPtr) ∧
          sf.readReg64 .x2 = g1.metaPtr ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x6 → sf.readReg64 r = s.readReg64 r) ∧
          P_f = (MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st1 ∗
            MallocngRoTablesA maddrs ∗ Frame))
      (fun _ => ⌜False⌝) := by
  apply sepWP_coreSt_wf; intro hwf
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  have h2 : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hsc
  obtain ⟨hLast, hMapLt⟩ := group_lastIdx_maplen_bounds hwf hg
  have hScPos : 1 ≤ sc := ((hwf.active_wf sc h1 h2).2.2.2.2.2.2 g hg hScEq hLt).2
  obtain ⟨cntF, spanF, hPs, hCntLo, hCntHi⟩ :=
    pageSpanSteps_terminates hScPos hsc (by omega : g.activeIdx < 31)
  obtain ⟨RestMeta, hBmMeta⟩ := byteMap_focus_meta hwf hg
  refine SepWP.seq (mid := mbase 8 + allocSlotOff_164)
    (Mid := fun s1 P1 =>
      s1.sp = s.sp ∧ s1.spAligned = s.spAligned ∧ PureStatePres s s1 ∧ s1.mem = s.mem ∧
      s1.readReg64 .x0 = maddrs.sizeClasses ∧
      s1.readReg64 .x1 = BitVec.ofNat 64 sc ∧
      s1.readReg32 .x3 = BitVec.ofNat 32 (g.activeIdx + 2) ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → s1.readReg64 r = s.readReg64 r) ∧
      P1 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
        MallocngRoTablesA maddrs ∗ Frame)) ?_ ?_
  · have hw0_3 : BitVec.setWidth 32 (s.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 g.activeIdx := hw3
    have hPkdSc := (GroupDesc.packedWord_fields g hLast (by omega) hMapLt).2.2.2
    conv => arg 4; rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]; rw [split_m32 g.metaPtr g.packedWord]
    dsimp only [allocSlotOff_bump, allocSlotOff_164] at hpc ⊢
    wp_sym_steps
    refine Obj.MultiPlacedLib.sepWP_relaxablePair (lib := VerifiedLibraries.mallocngLib) (mpl := mmpl)
      (i := 8) (by decide) (off := 340) (rd := 0#5) (X := fun _ => none) (svc := mallocngFaultSvc)
      MallocngMultiPlacement.placeable rfl rfl (by decide) (by decide)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ?_
    simp only [resolve_size_classes, show Obj.addSignedAddr maddrs.sizeClasses 0 = maddrs.sizeClasses from rfl,
      show BitVec.ofNat 64 (340 + 8) = 348#64 from rfl]
    wp_sym_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], psp_rfl, rfl,
       by simp,
       by simp,
       by simp [State.readReg32, BitVec.truncate_eq_setWidth, hw0_3, BitVec.ofNat_add],
       fun r r0 r1 r3 => ?_,
       by rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]; rw [split_m32 g.metaPtr g.packedWord]⟩
    simp only [State.readReg64_setPC,
      State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r3,
      State.readReg64_writeReg64_ne _ _ _ _ r0]
  · rintro s1 P1 hpc1 hrun1 ⟨hsp1, hal1, hpsp1, hmem1, hs1_0, hs1_1, hs1_3, hr1, rfl⟩
    obtain ⟨RestSc, hRoSc⟩ := split_roTables_sizeClass maddrs hsc Frame
    obtain ⟨hScOff, hStrideShift⟩ := sizeClass_stride_props hsc
    refine SepWP.seq (mid := mbase 8 + allocSlotOff_ps_body)
      (Mid := fun s2 P2 =>
        s2.sp = s.sp ∧ s2.spAligned = s.spAligned ∧ PureStatePres s s2 ∧ s2.mem = s.mem ∧
        s2.readReg32 .x6 = BitVec.ofNat 32 (slotStride sc) ∧
        s2.readReg32 .x3 = BitVec.ofNat 32 (g.activeIdx + 2) ∧
        s2.readReg32 .x1 = BitVec.ofNat 32 (g.activeIdx + 2) * BitVec.ofNat 32 (slotStride sc) + 16#32 ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x6 → s2.readReg64 r = s.readReg64 r) ∧
        P2 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
          MallocngRoTablesA maddrs ∗ Frame)) ?_ ?_
    · have hw1_3 : BitVec.setWidth 32 (s1.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (g.activeIdx + 2) := hs1_3
      conv => arg 4; rw [hRoSc, hScOff]
      dsimp only [allocSlotOff_164, allocSlotOff_ps_body] at hpc1 ⊢
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun1])
        ⟨by simpa using hsp1, by simpa [State.spAligned] using hal1, hpsp1.trans psp_rfl, hmem1,
         by simpa [State.readReg32, BitVec.truncate_eq_setWidth] using hStrideShift,
         by simpa [State.readReg32] using hs1_3,
         by simp [State.readReg32, BitVec.truncate_eq_setWidth, hw1_3, hStrideShift],
         fun r r0 r1 r3 r6 => ?_,
         by rw [hRoSc, hScOff]⟩
      refine Eq.trans ?_ (hr1 r r0 r1 r3)
      simp only [State.readReg64_setPC,
        State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r0,
        State.readReg64_writeReg64_ne _ _ _ _ r6]
    · rintro s2 P2 hpc2 hrun2 ⟨hsp2, hal2, hpsp2, hmem2, hs2_6, hs2_3, hs2_1, hr2, rfl⟩
      refine SepWP.seq
        (wp_allocSlot_pageSpan_loop hPs hw348 hr348 s2 _ hpc2 hrun2 hs2_6 hs2_3 hs2_1) ?_
      rintro s3 P3 hpc3 hrun3 ⟨_, hsp3, hal3, hpsp3, hmem3, hs3_3, hr3, rfl⟩
      have hs3_4 : s3.readReg64 .x4 = g.metaPtr :=
        (hr3 .x4 (by decide) (by decide) (by decide) (by decide)).trans
          ((hr2 .x4 (by decide) (by decide) (by decide) (by decide)).trans hx4)
      have hs3_5 : s3.readReg64 .x5 = g.mem :=
        (hr3 .x5 (by decide) (by decide) (by decide) (by decide)).trans
          ((hr2 .x5 (by decide) (by decide) (by decide) (by decide)).trans hx5)
      refine SepWP.seq (mid := mbase 8 + allocSlotOff_19c)
        (Mid := fun s4 P4 =>
          s4.sp = s.sp ∧ s4.spAligned = s.spAligned ∧ PureStatePres s s4 ∧ s4.mem = s.mem ∧
          s4.readReg64 .x0 = BitVec.zeroExtend 64 (g.packedWord.extractLsb' 0 8) ∧
          s4.readReg64 .x2 = g.metaPtr ∧
          s4.readReg32 .x3 = cntF ∧
          s4.readReg64 .x5 = g.mem ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x6 → s4.readReg64 r = s.readReg64 r) ∧
          P4 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
            MallocngRoTablesA maddrs ∗ Frame)) ?_ ?_
      · conv => arg 4; rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]; rw [split_m32_byte0 g.metaPtr g.packedWord]
        dsimp only [allocSlotOff_ps_done, allocSlotOff_19c] at hpc3 ⊢
        wp_sym_steps
        refine SepWP.done rfl (by simp [hrun3])
          ⟨by simpa using hsp3.trans hsp2, by simpa [State.spAligned] using hal3.trans hal2,
           (hpsp2.trans hpsp3).trans psp_rfl, hmem3.trans hmem2,
           by simp, by simp,
           by simpa [State.readReg32] using hs3_3, by simpa using hs3_5,
           fun r r0 r1 r2 r3 r6 => ?_,
           by rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]; rw [split_m32_byte0 g.metaPtr g.packedWord]⟩
        refine Eq.trans ?_ ((hr3 r r0 r1 r2 r3).trans (hr2 r r0 r1 r3 r6))
        simp only [State.readReg64_setPC,
          State.readReg64_writeReg64_ne _ _ _ _ r2, State.readReg64_writeReg64_ne _ _ _ _ r0]
      · rintro s4 P4 hpc4 hrun4 ⟨hsp4, hal4, hpsp4, _, hs4_0, hs4_2, hs4_3, hs4_5, hr4, rfl⟩
        let wMax := BitVec.ofNat 32 (g.lastIdx + 1)
        let wSel := if wMax.sle cntF then wMax else cntF
        let wNew := wSel - 1#32
        let newActB : BitVec 8 := (g.activeByte &&& 0xe0#8) ||| (wNew.truncate 8 &&& 0x1f#8)
        obtain ⟨hClampLo, hClampHi⟩ := bump_clamp_props g.activeByte hLast hLt hCntLo hCntHi
        obtain ⟨hg1Mem, hActFrNe1, hwf1, hCnt1, hEff1, hDyn1, hProt1, hMap1, hBmExt1, hBmAbs1⟩ :=
          tryAvail_bump_activeIdx_absorb hwf hsc hg hScEq (hHead h1) hLt
            (newActByte := newActB) hClampLo hClampHi
        have hw4_3 : BitVec.setWidth 32 (s4.readReg64 (Reg.gpr 3#5)) = cntF := hs4_3
        have hByte0Last : (g.packedWord.extractLsb' 0 8).zeroExtend 32 &&& 0x1f#32 =
            BitVec.ofNat 32 g.lastIdx := (GroupDesc.packedWord_byte0 g hLast).2
        conv => arg 4; rw [coreSt_eq_parts hwf, hBmExt1, pointsToBytes_singleton]; simp only [sepConj_assoc]
        dsimp only [allocSlotOff_19c, allocSlotOff_activate] at hpc4 ⊢
        wp_sym_steps
        have hMaxAdd : BitVec.ofNat 32 g.lastIdx + 1#32 = BitVec.ofNat 32 (g.lastIdx + 1) := by
          simp [BitVec.ofNat_add]
        let g1 : GroupDesc := { g with activeByte := newActB }
        let fG : GroupDesc → GroupDesc := fun u => if u.metaPtr == g.metaPtr then g1 else u
        let st1 : MallocngSt := { st with
          groups := st.groups.map fG
          byteVal := writeBytesToMap st.byteVal (g.mem + 8#64) [newActB] }
        have hSame1 : SameGroupsSlotKind st1.groups st.groups :=
          sameGroupsSlotKind_update_one hwf.groups_nodup.1 hg
            ⟨rfl, rfl, rfl, rfl, rfl⟩ (list_forall2_slotSameKind_refl g.slots)
        have hBrkEq : s4.brk = s.brk := hpsp4.2.1
        have hwf1' : MallocngWFInflight inflight maddrs.base brkStart s4.brk liveCost peakCost st1 :=
          hBrkEq.symm ▸ hwf1
        refine SepWP.done rfl (by simp [hrun4])
          ⟨st1, g1, hg1Mem, by simp [hrun4], by simpa using hsp4,
           by simpa [State.spAligned] using hal4, hpsp4.trans psp_rfl,
           ⟨hSame1, ⟨rfl, rfl, hEff1, hCnt1, rfl, hDyn1, rfl, fun _ _ _ _ => rfl,
            groupsGrpMono_map_ite hg g.metaPtr rfl (Nat.le_refl _)⟩⟩,
           rfl, hScEq, hAv0, hActFrNe1, fun h1' => hHead h1',
           by simpa using hs4_2,
           fun r r0 r1 r2 r3 r6 => ?_, ?_⟩
        · refine Eq.trans ?_ (hr4 r r0 r1 r2 r3 r6)
          simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r0]
        · simp only [State.setPC, State.setMem, State.setPState, State.writeReg64] at hwf1' ⊢
          have hFix : MallocngCoreFixedA γ maddrs st = MallocngCoreFixedA γ maddrs st1 := rfl
          have hCtxPts : (maddrs.ctx ↦ₛ st.ctx.toBytes) = (maddrs.ctx ↦ₛ st1.ctx.toBytes) := rfl
          rw [and_imm32_0x1f_byte, hByte0Last, hMaxAdd, bfxil_w32_0_5_byte]
          rw [← pointsToBytes_singleton (g.mem + 8#64) newActB]
          rw [coreSt_eq_parts hwf1', ← hBmAbs1, hCtxPts, hProt1, hMap1, hFix]
          dsimp only [st1, g1, fG, newActB, wNew, wSel, wMax]
          simp only [sepConj_assoc]

end LibsignalBinary.Heap.Fine
