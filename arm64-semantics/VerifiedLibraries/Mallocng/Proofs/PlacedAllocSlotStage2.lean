/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotStage1

/-!
# Stage 2 Symbolic Execution Helpers for Placed `alloc_slot`

Proves `SepWP` block lemmas for the outer `alloc_slot` entry, `try_avail` fast and slow
paths, `bounces` tail, and fast bit-pop epilogue (`+0x000 .. +0x104`, `+0x134 .. +0x14c`,
`+0x1ec .. +0x280`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Stack frame bundles, symbolic offsets, and bitvector helpers -/

abbrev SlotSaved12 (sp0 r29 ret_pc r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 : BitVec 64) :
    SepProp :=
  ((sp0 - 96#64) ↦₆₄ r29) ∗ ((sp0 - 88#64) ↦₆₄ ret_pc) ∗
  ((sp0 - 80#64) ↦₆₄ r19) ∗ ((sp0 - 72#64) ↦₆₄ r20) ∗
  ((sp0 - 64#64) ↦₆₄ r21) ∗ ((sp0 - 56#64) ↦₆₄ r22) ∗
  ((sp0 - 48#64) ↦₆₄ r23) ∗ ((sp0 - 40#64) ↦₆₄ r24) ∗
  ((sp0 - 32#64) ↦₆₄ r25) ∗ ((sp0 - 24#64) ↦₆₄ r26) ∗
  ((sp0 - 16#64) ↦₆₄ r27) ∗ ((sp0 - 8#64) ↦₆₄ r28)

abbrev SlotSaved4 (sp0 r19 r20 r27 r28 : BitVec 64) : SepProp :=
  ((sp0 - 80#64) ↦₆₄ r19) ∗ ((sp0 - 72#64) ↦₆₄ r20) ∗
  ((sp0 - 16#64) ↦₆₄ r27) ∗ ((sp0 - 8#64) ↦₆₄ r28)

abbrev SlotSaved8 (sp0 r29 ret_pc r21 r22 r23 r24 r25 r26 : BitVec 64) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ r29) ∗ ((sp0 - 88#64) ↦₆₄ ret_pc) ∗
  ((sp0 - 64#64) ↦₆₄ r21) ∗ ((sp0 - 56#64) ↦₆₄ r22) ∗
  ((sp0 - 48#64) ↦₆₄ r23) ∗ ((sp0 - 40#64) ↦₆₄ r24) ∗
  ((sp0 - 32#64) ↦₆₄ r25) ∗ ((sp0 - 24#64) ↦₆₄ r26)

theorem slotSaved12_eq_8_4 (sp0 r29 ret_pc r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 : BitVec 64) :
    SlotSaved12 sp0 r29 ret_pc r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 =
      (SlotSaved4 sp0 r19 r20 r27 r28 ∗ SlotSaved8 sp0 r29 ret_pc r21 r22 r23 r24 r25 r26) := by
  simp only [SlotSaved12, SlotSaved4, SlotSaved8, sepConj_assoc]
  ac_rfl

abbrev allocSlotOff_030 : BitVec 64 := words_insn_off% blk08Words 0xb4001242#32
abbrev allocSlotOff_044 : BitVec 64 := words_insn_off% blk08Words 0xb9401c44#32 0
abbrev allocSlotOff_d0  : BitVec 64 := words_insn_off% blk08Words 0x394020a1#32 0
abbrev allocSlotOff_ec  : BitVec 64 := words_insn_off% blk08Words 0xf9400444#32
abbrev allocSlotOff_1f4 : BitVec 64 := words_insn_off% blk08Words 0x51001c21#32
abbrev allocSlotOff_200 : BitVec 64 := words_insn_off% blk08Words 0xa94153f3#32 0
abbrev allocSlotOff_22c : BitVec 64 := words_insn_off% blk08Words 0x90000001#32 0
abbrev allocSlotOff_234 : BitVec 64 := words_insn_off% blk08Words 0x1b027c00#32

theorem active_slot_addr_eq (ctx : BitVec 64) {sc : Nat} (_hsc : sc < 48) :
    ctx + ((BitVec.ofNat 64 sc + 10#64) <<< 3) = ctx + 80#64 + BitVec.ofNat 64 (8 * sc) := by
  have hsh : ((BitVec.ofNat 64 sc + 10#64) <<< 3) = (BitVec.ofNat 64 sc + 10#64) * 8#64 := by
    bv_robdd
  rw [hsh]; bv_omega

theorem spAligned_sub96 {s : State} (hsAl : s.spAligned = true) :
    ((s.sp - 96#64) &&& 15#64 == 0#64) = true := by
  simp only [State.spAligned] at hsAl; revert hsAl; bv_robdd

theorem sxtw_sc_of_lt48 {w0 : BitVec 32} {sc : Nat} (hsc : sc < 48) (hw0 : w0.toNat = sc) :
    BitVec.signExtend 64 w0 = BitVec.ofNat 64 sc := by
  have hwEq : w0 = BitVec.ofNat 32 sc := by
    apply BitVec.eq_of_toNat_eq
    rw [hw0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hwEq]
  have hlt : (BitVec.ofNat 32 sc).ult (1#32 <<< 31) = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
    change sc % (2 ^ 32) < 2 ^ 31
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hse : (BitVec.ofNat 32 sc).signExtend 64 = (BitVec.ofNat 32 sc).zeroExtend 64 := by
    revert hlt; bv_robdd
  rw [hse]; bv_omega

private theorem sbfm_sxtw_eq (v : BitVec 64) :
    (v >>> 0 &&& 0xffffffff#64 |||
      (if v.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) =
      BitVec.signExtend 64 (BitVec.setWidth 32 v) := by
  bv_robdd

theorem sbfm_sxtw_sc_of_lt48 {v : BitVec 64} {sc : Nat} (hsc : sc < 48)
    (hw0 : (BitVec.setWidth 32 v).toNat = sc) :
    (v >>> 0 &&& 0xffffffff#64 |||
      (if v.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = BitVec.ofNat 64 sc := by
  rw [sbfm_sxtw_eq]
  exact sxtw_sc_of_lt48 hsc hw0

theorem lsl2_sub1_of_byte (b : BitVec 8) :
    let idx := (b &&& 0x1f#8).toNat
    BitVec.setWidth 32 (BitVec.zeroExtend 64 b) &&& 0x1f#32 = BitVec.ofNat 32 idx ∧
    (2#32 <<< ((BitVec.setWidth 32 ((BitVec.zeroExtend 64 b >>> 0) &&& 0x1f#64)).toNat % 32)) - 1#32 =
      (2#32 <<< idx) - 1#32 := by
  dsimp only
  have hlt32 : (b &&& 0x1f#8).toNat < 32 := by
    have hUlt : (b &&& 0x1f#8).ult 32#8 = true := by bv_robdd
    simpa [BitVec.ult] using hUlt
  have h1a : BitVec.setWidth 32 (BitVec.zeroExtend 64 b) &&& 0x1f#32 =
      BitVec.zeroExtend 32 (b &&& 0x1f#8) := by bv_robdd
  have h1b : BitVec.zeroExtend 32 (b &&& 0x1f#8) = BitVec.ofNat 32 (b &&& 0x1f#8).toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have h2a : BitVec.setWidth 32 ((BitVec.zeroExtend 64 b >>> 0) &&& 0x1f#64) =
      BitVec.zeroExtend 32 (b &&& 0x1f#8) := by bv_robdd
  have h2 : (BitVec.setWidth 32 ((BitVec.zeroExtend 64 b >>> 0) &&& 0x1f#64)).toNat % 32 =
      (b &&& 0x1f#8).toNat := by
    rw [h2a, BitVec.toNat_setWidth]; omega
  exact ⟨h1a.trans h1b, by rw [h2]⟩

private theorem fastPop_uxtw_ea (db : BitVec 64) (av : BitVec 32) :
    db + BitVec.ofNat 64 ((((-av) &&& av) * 0x076be629#32) >>> 27).toNat =
      db + BitVec.zeroExtend 64
        (BitVec.setWidth 32
          (BitVec.setWidth 64
            ((0#32 - (0#32 - av &&& av) &&& (0#32 - av &&& av)) *
              124511785#32) >>>
            27)) := by
  have hIso : (0#32 - (0#32 - av &&& av) &&& (0#32 - av &&& av)) = (-av) &&& av := by bv_robdd
  have hSh : ∀ x : BitVec 32,
      BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.setWidth 64 x >>> 27)) =
        BitVec.zeroExtend 64 (x >>> 27) := fun _ => by bv_robdd
  have h2 : ∀ x : BitVec 32, BitVec.zeroExtend 64 (x >>> 27) = BitVec.ofNat 64 (x >>> 27).toNat :=
    fun _ => by apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [hIso, show (124511785#32 : BitVec 32) = 0x076be629#32 from rfl, hSh, h2]

arm64_proof_prelude
set_option diagnostics false

local macro "psp_simp" : term => `(by simp [PureStatePres, MallocngProcPreserved])

/-! ## Bounces tail (`+0x1ec .. +0x208`) -/

theorem wp_allocSlot_bounces_tail [MallocngMultiPlacement]
    (_hw348 : Blk08HasWords348 mallocngFaultSvc) (_hr348 : Blk08Range348)
    (_hw564 : Blk08HasWords564 mallocngFaultSvc) (_hr564 : Blk08Range564)
    {inflight sc : Nat} (hsc : sc < 48) {γ : GhostName}
    {sp0 r19 r20 r27 r28 brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_bounces_chk) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64) (hsAl : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = g.metaPtr)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_fast_pop) s
      (SlotSaved4 sp0 r19 r20 r27 r28 ∗
       MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)
      (fun sf P_f =>
        ∃ st1 : MallocngSt,
          sf.status = .Running ∧ sf.sp = sp0 - 96#64 ∧ sf.spAligned = true ∧
          PureStatePres s sf ∧
          AllocSlotStPres sc st st1 ∧
          st1.groups = st.groups ∧ st1.ctx.active = st.ctx.active ∧
          sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x2 = g.metaPtr ∧
          sf.readReg64 .x19 = r19 ∧ sf.readReg64 .x20 = r20 ∧
          sf.readReg64 .x27 = r27 ∧ sf.readReg64 .x28 = r28 ∧
          P_f = (SlotSaved4 sp0 r19 r20 r27 r28 ∗
            MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st1 ∗ Frame))
      (fun _ => ⌜False⌝) := by
  conv => arg 4; rw [← sepConj_assoc, sepConj_comm (SlotSaved4 _ _ _ _ _), sepConj_assoc]
  apply sepWP_coreSt_wf; intro hwf
  obtain ⟨hLast, hMapLt⟩ := group_lastIdx_maplen_bounds hwf hg
  obtain ⟨RestMeta, hBmMeta⟩ := byteMap_focus_meta hwf hg
  have hPkdSc := (GroupDesc.packedWord_fields g hLast (by omega) hMapLt).2.2.2
  refine SepWP.seq (mid := mbase 8 + allocSlotOff_1f4)
    (Mid := fun s1 P1 =>
      s1.sp = sp0 - 96#64 ∧ s1.spAligned = true ∧ PureStatePres s s1 ∧ s1.mem = s.mem ∧
      s1.readReg64 .x0 = s.readReg64 .x0 ∧
      s1.readReg64 .x1 = BitVec.ofNat 64 sc ∧
      s1.readReg64 .x2 = g.metaPtr ∧
      s1.readReg64 .x22 = Obj.pageOf maddrs.ctx ∧
      P1 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
        SlotSaved4 sp0 r19 r20 r27 r28 ∗ Frame)) ?_ ?_
  · conv => arg 4; rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]; rw [split_m32 g.metaPtr g.packedWord]; simp only [sepConj_assoc]
    dsimp only [allocSlotOff_bounces_chk, allocSlotOff_1f4] at hpc ⊢
    wp_sym_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simpa using hsp, by simpa [State.spAligned] using hsAl, psp_rfl, rfl,
       by simp, by simp [← hScEq], by simpa using hx2, by simpa using hx22, ?_⟩
    conv => rhs; rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]; rw [split_m32 g.metaPtr g.packedWord]; simp only [sepConj_assoc]
  · rintro s1 P1 hpc1 hrun1 ⟨hsp1, hal1, hpsp1, _, hs1_0, hs1_1, hs1_2, hs1_22, rfl⟩
    have hTruncSc : BitVec.setWidth 32 (BitVec.ofNat 64 sc) = BitVec.ofNat 32 sc := by bv_omega
    dsimp only [allocSlotOff_1f4, allocSlotOff_fast_pop] at hpc1 ⊢
    wp_sym_steps
    wp_if hLs
    · obtain ⟨hBncIff, hBncProps⟩ := bounces_bv_props maddrs.ctx hsc
      obtain ⟨hScLo, hScHi⟩ := hBncIff.mp hLs
      obtain ⟨hk32, hBncAddr⟩ := hBncProps hScLo hScHi
      have hkB : sc - 7 < st.ctx.bounces.length := hwf.ctx_lens.2.2.2.1 ▸ hk32
      obtain ⟨RestBnc, hCtxFoc, hCtxAbs⟩ :=
        ctx_focus_bounces maddrs.ctx st.ctx hwf.ctx_lens.1 hwf.ctx_lens.2.1
          hwf.ctx_lens.2.2.1 hwf.ctx_lens.2.2.2.1 hk32 ((st.ctx.bounces[sc - 7]'hkB) - 1#8)
      by_cases hBz : st.ctx.bounces[sc - 7]'hkB = 0#8
      · have hCtxFoc0 : (maddrs.ctx ↦ₛ st.ctx.toBytes) =
            (((maddrs.ctx + 880#64 + BitVec.ofNat 64 (sc - 7)) ↦₈ 0#8) ∗ RestBnc) := by
          simpa [hBz] using hCtxFoc
        conv => arg 4; rw [coreSt_eq_parts hwf, hCtxFoc0]; simp only [SlotSaved4, sepConj_assoc]
        wp_sym_steps
        have hBrkEq : s1.brk = s.brk := hpsp1.2.1
        have hwf' : MallocngWFInflight inflight maddrs.base brkStart s1.brk liveCost peakCost st :=
          hBrkEq.symm ▸ hwf
        refine SepWP.done rfl (by simp [hrun1])
          ⟨st, by simp [hrun1], by simpa using hsp1, by simpa [State.spAligned] using hal1,
           hpsp1.trans psp_rfl, AllocSlotStPres.rfl, rfl, rfl,
           by simpa using hs1_0, by simpa using hs1_2,
           by simp, by simp, by simp, by simp, ?_⟩
        simp only [State.setPC, State.setPState, State.writeReg64] at hwf' ⊢
        conv => rhs; rw [← sepConj_assoc, sepConj_comm (SlotSaved4 _ _ _ _ _), sepConj_assoc, coreSt_eq_parts hwf', hCtxFoc0]; simp only [SlotSaved4, sepConj_assoc]
      · have hwf1 := tryAvail_dec_bounces_wf hwf hg hk32 hBz
        conv => arg 4; rw [coreSt_eq_parts hwf, hCtxFoc]; simp only [SlotSaved4, sepConj_assoc]
        wp_sym_steps
        let st1 : MallocngSt :=
          { st with ctx := { st.ctx with bounces := st.ctx.bounces.set (sc - 7) ((st.ctx.bounces[sc - 7]'hkB) - 1#8) } }
        have hBrkEq : s1.brk = s.brk := hpsp1.2.1
        have hwf1' : MallocngWFInflight inflight maddrs.base brkStart s1.brk liveCost peakCost st1 :=
          hBrkEq.symm ▸ hwf1
        refine SepWP.done rfl (by simp [hrun1])
          ⟨st1, by simp [hrun1], by simpa using hsp1, by simpa [State.spAligned] using hal1,
           hpsp1.trans psp_rfl,
           ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, Cost.GroupsGrpMono.refl _⟩,
           rfl, rfl,
           by simpa using hs1_0, by simpa using hs1_2,
           by simp, by simp, by simp, by simp, ?_⟩
        simp only [State.setPC, State.setMem, State.setPState, State.writeReg64] at hwf1' ⊢
        have hFix : MallocngCoreFixedA γ maddrs st = MallocngCoreFixedA γ maddrs st1 := rfl
        have hBmEq : ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
            ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal := rfl
        have hProtEq : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
            ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal := rfl
        have hMapEq : MappedSet st.masterDom (OwnedMappedByte st) =
            MappedSet st1.masterDom (OwnedMappedByte st1) := rfl
        rw [sub1_w32_byte]
        conv => rhs; rw [← sepConj_assoc, sepConj_comm (SlotSaved4 _ _ _ _ _), sepConj_assoc, coreSt_eq_parts hwf1', ← hCtxAbs, ← hBmEq, ← hProtEq, ← hMapEq, ← hFix]; dsimp only [st1]; simp only [SlotSaved4, sepConj_assoc]
    · conv => arg 4; simp only [SlotSaved4, sepConj_assoc]
      wp_sym_steps
      have hBrkEq : s1.brk = s.brk := hpsp1.2.1
      refine SepWP.done rfl (by simp [hrun1])
        ⟨st, by simp [hrun1], by simpa using hsp1, by simpa [State.spAligned] using hal1,
         hpsp1.trans psp_rfl, AllocSlotStPres.rfl, rfl, rfl,
         by simpa using hs1_0, by simpa using hs1_2,
         by simp, by simp, by simp, by simp, ?_⟩
      simp only [State.setPC, State.setPState, State.writeReg64, hBrkEq]
      simp only [SlotSaved4, sepConj_assoc]
      generalize MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st = CS
      ac_rfl

/-! ## Fast bit-pop epilogue (`+0x208`) -/

theorem wp_allocSlot_fast_pop_ret [MallocngMultiPlacement]
    (_hw348 : Blk08HasWords348 mallocngFaultSvc) (_hr348 : Blk08Range348)
    (_hw564 : Blk08HasWords564 mallocngFaultSvc) (_hr564 : Blk08Range564)
    {inflight sc req : Nat} (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    {γ : GhostName} {sp0 r29 ret_pc r21 r22 r23 r24 r25 r26 brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : ∀ h1 : sc < st.ctx.active.length, st.ctx.active[sc]'h1 = g.metaPtr)
    (hAvNe : g.availMask ≠ 0#32)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_fast_pop) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64) (hsAl : s.spAligned = true)
    (hw0 : s.readReg32 .x0 = g.availMask)
    (hx2 : s.readReg64 .x2 = g.metaPtr) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) ret_pc s
      (SlotSaved8 sp0 r29 ret_pc r21 r22 r23 r24 r25 r26 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)
      (fun sf P_f =>
        ∃ st1 : MallocngSt, ∃ idx : Nat,
          sf.status = .Running ∧ sf.sp = sp0 ∧ sf.spAligned = true ∧
          PureStatePres s sf ∧
          st1.reservedMetas = st.reservedMetas ∧
          st1.liveMap = st.liveMap ∧
          totalLiveEffCost st1 = totalLiveEffCost st ∧
          totalLiveCount st1 = totalLiveCount st ∧
          st1.metaAreas.length = st.metaAreas.length ∧
          dynamicRootRegions st1 = dynamicRootRegions st ∧
          st1.ctx.active = st.ctx.active ∧ Cost.GroupsGrpMono st.groups st1.groups ∧
          sf.readReg32 .x0 = BitVec.ofNat 32 idx ∧ idx ≤ 31 ∧
          (∃ g' ∈ st1.groups, ∃ hAct : sc < st1.ctx.active.length, ∃ hIdx : idx < g'.slots.length,
            g'.sc = sc ∧
            req + 4 ≤ g'.stride ∧
            g'.metaPtr = st1.ctx.active[sc]'hAct ∧
            g'.slots[idx]'hIdx = .claimed ∧
            (g'.isMmapped = true →
              ∀ a : BitVec 64, InRegion (g'.slotStart idx) g'.stride a → st1.byteVal a = 0#8)) ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x21 = r21 ∧ sf.readReg64 .x22 = r22 ∧
          sf.readReg64 .x23 = r23 ∧ sf.readReg64 .x24 = r24 ∧
          sf.readReg64 .x25 = r25 ∧ sf.readReg64 .x26 = r26 ∧
          sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
          sf.readReg64 .x29 = r29 ∧ sf.readReg64 .lr = ret_pc ∧
          P_f = (SlotSaved8 sp0 r29 ret_pc r21 r22 r23 r24 r25 r26 ∗
            MallocngRoTablesA maddrs ∗
            MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st1 ∗ Frame))
      (fun _ => ⌜False⌝) := by
  have hPermPre :
      (SlotSaved8 sp0 r29 ret_pc r21 r22 r23 r24 r25 r26 ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame) =
      (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
        MallocngRoTablesA maddrs ∗
        SlotSaved8 sp0 r29 ret_pc r21 r22 r23 r24 r25 r26 ∗ Frame) := by
    generalize SlotSaved8 sp0 r29 ret_pc r21 r22 r23 r24 r25 r26 = S8
    generalize MallocngRoTablesA maddrs = RO
    generalize MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st = CS
    ac_rfl
  conv => arg 4; rw [hPermPre]
  apply sepWP_coreSt_wf; intro hwf
  obtain ⟨hIdx, hIdx32, hNotMmap, hMetaLenEq, hLiveCntEq, hDynEq, hwf1, hg'Mem, hBmFoc, hBmAbs, hProtEq, hMapEq⟩ :=
    claimFreeAvailInflight_absorb hwf hg hAvNe
  have hEffEq := claimFreeAvail_effCost_eq hwf hg hAvNe
  have hStride := req_add_four_le_stride_of_avail hwf hg hScEq hsc hReq hAvNe
  obtain ⟨_, hBic, _, hHashLt, _, hDbVal, _⟩ := fastPop_bv_props hAvNe
  have hDbEa := fastPop_uxtw_ea maddrs.debruijnFree g.availMask
  have hw0' : BitVec.setWidth 32 (s.readReg64 (Reg.gpr 0#5)) = g.availMask := hw0
  have hSp0Al : (sp0 &&& 15#64 == 0#64) = true := spAligned_of_sub96 hsp hsAl
  obtain ⟨RestDb, hRoDb⟩ := split_roTables_debruijnFree maddrs hHashLt
    (SlotSaved8 sp0 r29 ret_pc r21 r22 r23 r24 r25 r26 ∗ Frame)
  conv => arg 4; rw [coreSt_eq_parts hwf, hBmFoc, GroupDesc.metaBytes_pointsTo, hRoDb, hDbEa]; simp only [SlotSaved8, sepConj_assoc]
  dsimp only [allocSlotOff_fast_pop] at hpc
  wp_sym_steps
  refine Obj.MultiPlacedLib.sepWP_relaxablePair (lib := VerifiedLibraries.mallocngLib) (mpl := mmpl)
    (i := 8) (by decide) (off := 556) (rd := 1#5) (X := fun _ => none) (svc := mallocngFaultSvc)
    MallocngMultiPlacement.placeable rfl rfl (by decide) (by decide)
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ?_
  simp only [resolve_debruijn4681, show Obj.addSignedAddr maddrs.debruijnFree 0 = maddrs.debruijnFree from rfl,
    show BitVec.ofNat 64 (556 + 8) = 564#64 from rfl]
  wp_sym_steps
  let idx := ctz32DeBruijn g.availMask
  let newAvail := g.availMask - ((-g.availMask) &&& g.availMask)
  let g' := mkReplaceSlotGroup g idx newAvail .claimed
  let val' := writeBytesToMap st.byteVal g.metaPtr g'.metaBytes
  let st1 := mkReplaceSlotSt st g idx newAvail .claimed val' st.liveMap
  have hAct1 : sc < st1.ctx.active.length := by
    change sc < st.ctx.active.length; rw [hwf.ctx_lens.1]; exact hsc
  have hIdx' : idx < g'.slots.length := by simpa [g', mkReplaceSlotGroup] using hIdx
  have hClaimed : g'.slots[idx]'hIdx' = .claimed := by simp [g', mkReplaceSlotGroup]
  have hIdxW32 : BitVec.setWidth 32 (BitVec.zeroExtend 64 (BitVec.ofNat 8 idx)) = BitVec.ofNat 32 idx := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : idx < 256), Nat.mod_eq_of_lt (by omega : idx < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : idx < 2 ^ 32)]
  refine SepWP.done (by simp) (by simp [hrun])
    ⟨st1, idx, by simp [hrun], by simp, by simpa [State.spAligned, hsp] using hSp0Al,
     psp_simp, rfl, rfl, hEffEq, hLiveCntEq, hMetaLenEq, hDynEq, rfl,
     groupsGrpMono_map_ite hg g.metaPtr rfl (Nat.le_refl _),
     by simpa [State.readReg32, BitVec.truncate_eq_setWidth, hDbVal] using hIdxW32,
     by omega,
     ⟨g', hg'Mem, hAct1, hIdx', hScEq, hStride, (hHead hAct1).symm, hClaimed,
      fun hMm => by rw [hNotMmap] at hMm; cases hMm⟩,
     by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
     by simp, by simp, by simp, by simp, ?_⟩
  simp only [State.setPC, State.setMem, State.setPState, State.writeReg64]
  have hFix : ∀ bv, MallocngCoreFixedA γ maddrs
      (mkReplaceSlotSt st g (ctz32DeBruijn g.availMask) (g.availMask - (-g.availMask &&& g.availMask))
        .claimed bv st.liveMap) = MallocngCoreFixedA γ maddrs st := fun _ => rfl
  have hPermPost :
      (SlotSaved8 sp0 r29 ret_pc r21 r22 r23 r24 r25 r26 ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart s.brk liveCost peakCost st1 ∗ Frame) =
      (MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart s.brk liveCost peakCost st1 ∗
        MallocngRoTablesA maddrs ∗
        SlotSaved8 sp0 r29 ret_pc r21 r22 r23 r24 r25 r26 ∗ Frame) := by
    generalize SlotSaved8 sp0 r29 ret_pc r21 r22 r23 r24 r25 r26 = S8
    generalize MallocngRoTablesA maddrs = RO
    generalize MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart s.brk liveCost peakCost st1 = CS1
    ac_rfl
  conv => lhs; try rw [hBic]
  (conv => rhs; rw [hPermPost]; dsimp only [st1, val', g', newAvail, idx]; rw [coreSt_eq_parts hwf1, ← hBmAbs, ← hProtEq, ← hMapEq, hFix]; dsimp only [mkReplaceSlotSt, mkReplaceSlotGroup]; rw [GroupDesc.metaBytes_pointsTo, hRoDb, hDbEa]; simp only [SlotSaved8, sepConj_assoc]); rfl

/-! ## `try_avail` full-freed check and active-mask scan (`+0x0a8 .. +0x108`) -/

private theorem byteMap_focus_meta2 {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g g1 : GroupDesc} (hg : g ∈ st.groups) (hg1 : g1 ∈ st.groups)
    (hNeM : g1.metaPtr ≠ g.metaPtr) :
    ∃ Rest2 : SepProp,
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ ((g1.metaPtr ↦ₛ g1.metaBytes) ∗ Rest2)) := by
  obtain ⟨_, _, _, hMReadG, hMOwnG⟩ := meta_ownedRw_of_mem_groups hwf hg
  obtain ⟨_, _, _, hMRead1, hMOwn1⟩ := meta_ownedRw_of_mem_groups hwf hg1
  have hDisj : DisjointRegions g1.metaPtr 40 g.metaPtr 40 :=
    (allMetaSlots_info hwf ((hwf.free_bump_metas_wf.2.2.2.2.2 g1.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg1)))))).2.2.2.2
      g.metaPtr ((hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))) hNeM.symm
  let P1 := fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a
  have hMOwn1P1 : ∀ a, InRegion g1.metaPtr 40 a → P1 a ∧ a ∈ st.masterDom := fun a ha =>
    ⟨⟨(hMOwn1 a ha).1, fun hInG => DisjointRegions.not_both hDisj ha hInG⟩, (hMOwn1 a ha).2⟩
  refine ⟨ByteMap st.masterDom (fun a => P1 a ∧ ¬ InRegion g1.metaPtr 40 a) st.byteVal, ?_⟩
  rw [(slot_byteMap_update40 hwf.masterDom_wf.1 st.byteVal
    (readBytesFromMap_length st.byteVal g.metaPtr 40) hMOwnG).1, hMReadG,
    (slot_byteMap_update40 hwf.masterDom_wf.1 st.byteVal
      (readBytesFromMap_length st.byteVal g1.metaPtr 40) hMOwn1P1).1, hMRead1]

theorem wp_allocSlot_a8_to_c8 [MallocngMultiPlacement]
    (_hw0 : Blk08HasWords0 mallocngFaultSvc) (_hr0 : Blk08Range0)
    {inflight sc : Nat} (hsc : sc < 48) {γ : GhostName} {brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : ∀ h1 : sc < st.ctx.active.length, st.ctx.active[sc]'h1 = g.metaPtr)
    (hAv0 : g.availMask = 0#32) (hFrNe : g.freedMask ≠ 0#32)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_a8) (hrun : s.status = .Running)
    (hx2 : s.readReg64 .x2 = g.metaPtr)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 sc) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_c8) s
      (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)
      (fun sf P_f =>
        ∃ st1 : MallocngSt, ∃ g1 ∈ st1.groups,
          sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
          PureStatePres s sf ∧
          AllocSlotStPres sc st st1 ∧
          g1.sc = sc ∧ g1.availMask = 0#32 ∧ g1.freedMask ≠ 0#32 ∧
          (∀ h1 : sc < st1.ctx.active.length, st1.ctx.active[sc]'h1 = g1.metaPtr) ∧
          sf.readReg64 .x2 = g1.metaPtr ∧
          sf.readReg32 .x4 = g1.freedMask ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → sf.readReg64 r = s.readReg64 r) ∧
          P_f = (MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st1 ∗ Frame))
      (fun _ => ⌜False⌝) := by
  apply sepWP_coreSt_wf; intro hwf
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  have hHead1 : st.ctx.active[sc]'h1 = g.metaPtr := hHead h1
  obtain ⟨hLast, _⟩ := group_lastIdx_maplen_bounds hwf hg
  obtain ⟨RestMeta, hBmMeta⟩ := byteMap_focus_meta hwf hg
  obtain ⟨RestAct, hCtxFoc, hCtxAbs⟩ := ctx_focus_active maddrs.ctx st.ctx hwf.ctx_lens.1 hsc g.next
  have hActAddr := active_slot_addr_eq maddrs.ctx hsc
  obtain ⟨hB0Mask, hMaskEq⟩ := lsl2_sub1_of_byte (g.packedWord.extractLsb' 0 8)
  have hB0Eq : ((g.packedWord.extractLsb' 0 8) &&& 0x1f#8).toNat = g.lastIdx := by
    have hByte0Last := (GroupDesc.packedWord_byte0 g hLast).2
    have hZ : BitVec.setWidth 32 (BitVec.zeroExtend 64 (g.packedWord.extractLsb' 0 8)) =
        (g.packedWord.extractLsb' 0 8).zeroExtend 32 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      have hbLt := (g.packedWord.extractLsb' 0 8).isLt
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hZ, hByte0Last] at hB0Mask
    have ht := congrArg BitVec.toNat hB0Mask
    simp only [BitVec.toNat_ofNat] at ht
    rw [Nat.mod_eq_of_lt (by omega : g.lastIdx < 2 ^ 32),
        Nat.mod_eq_of_lt (by have := ((g.packedWord.extractLsb' 0 8) &&& 0x1f#8).isLt; omega)] at ht
    exact ht.symm
  rw [hB0Eq] at hMaskEq
  conv => arg 4; rw [coreSt_eq_parts hwf, hCtxFoc, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]; rw [split_m32_byte0 g.metaPtr g.packedWord]; simp only [sepConj_assoc]
  dsimp only [allocSlotOff_a8, allocSlotOff_c8] at hpc ⊢
  wp_sym_steps
  wp_if hFull
  · wp_sym_steps
    wp_if hTbz
    · refine SepWP.done (by simp) (by simp [hrun])
        ⟨st, g, hg, by simp [hrun], by simp, by simp [State.spAligned], psp_simp,
         AllocSlotStPres.rfl, hScEq, hAv0, hFrNe, hHead,
         by simpa using hx2, by simp [State.readReg32, hFull],
         fun r r0 r1 _ r3 r4 => by
           simp only [State.readReg64_setPC, State.readReg64_setPState,
             State.readReg64_writeReg64_ne, ne_eq, r0, r1, r3, r4, not_false_eq_true], ?_⟩
      simp only [State.setPC, State.setPState, State.writeReg64]
      conv => rhs; rw [coreSt_eq_parts hwf, hCtxFoc, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]; rw [split_m32_byte0 g.metaPtr g.packedWord]; simp only [sepConj_assoc]
    · by_cases hNxSelf : g.next = g.metaPtr
      · conv => arg 4; rw [hNxSelf]
        wp_sym_steps
        have hSetSelf : { st.ctx with active := st.ctx.active.set sc g.next } = st.ctx := by
          cases hctx : st.ctx; simp [hNxSelf, ← hHead1, hctx]
        refine SepWP.done (by simp) (by simp [hrun])
          ⟨st, g, hg, by simp [hrun], by simp, by simp [State.spAligned], psp_simp,
           AllocSlotStPres.rfl, hScEq, hAv0, hFrNe, hHead,
           by simp, by simp [State.readReg32, hFull],
           fun r r0 r1 r2 r3 r4 => by
             simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
               State.readReg64_writeReg64_ne, ne_eq, r0, r1, r2, r3, r4, not_false_eq_true], ?_⟩
        simp only [State.setPC, State.setMem, State.setPState, State.writeReg64]
        have hAbsSelf : ((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ g.metaPtr ∗ RestAct) =
            (maddrs.ctx ↦ₛ st.ctx.toBytes) := by rw [← hNxSelf, hCtxAbs, hSetSelf]
        conv => rhs; rw [coreSt_eq_parts hwf, ← hAbsSelf, hBmMeta, GroupDesc.metaBytes_pointsTo, hNxSelf]; simp only [sepConj_assoc]; rw [split_m32_byte0 g.metaPtr g.packedWord]; simp only [sepConj_assoc]
      · obtain ⟨hwfRot, g1, hg1Mem, hg1Meta, hg1Sc, hg1Av0, hg1FrNe, _⟩ :=
          tryAvail_rotate_wf hwf hsc hg hScEq hHead1 hAv0 hFrNe
        obtain ⟨Rest2, hBmMeta2⟩ := byteMap_focus_meta2 hwf hg hg1Mem (hg1Meta ▸ hNxSelf)
        have hSwapMeta : ∀ Z : SepProp,
            (g.metaPtr ↦₆₄ g.prev ∗ ((g.metaPtr + 8#64) ↦₆₄ g.next ∗
              ((g.metaPtr + 16#64) ↦₆₄ g.mem ∗ ((g.metaPtr + 24#64) ↦₃₂ g.availMask ∗
              ((g.metaPtr + 28#64) ↦₃₂ g.freedMask ∗
              ((g.metaPtr + 32#64) ↦₈ (g.packedWord.extractLsb' 0 8) ∗
              ((g.metaPtr + 33#64) ↦ₛ (unpack64 g.packedWord).tail ∗ (RestMeta ∗ Z)))))))) =
            (g.metaPtr ↦₆₄ g.prev ∗ ((g.metaPtr + 8#64) ↦₆₄ g.next ∗
              ((g.metaPtr + 16#64) ↦₆₄ g.mem ∗ ((g.metaPtr + 24#64) ↦₃₂ g.availMask ∗
              ((g.metaPtr + 28#64) ↦₃₂ g.freedMask ∗ ((g.metaPtr + 32#64) ↦₆₄ g.packedWord ∗
              (g1.metaPtr ↦₆₄ g1.prev ∗ ((g1.metaPtr + 8#64) ↦₆₄ g1.next ∗
              ((g1.metaPtr + 16#64) ↦₆₄ g1.mem ∗ ((g1.metaPtr + 24#64) ↦₃₂ g1.availMask ∗
              ((g1.metaPtr + 28#64) ↦₃₂ g1.freedMask ∗ ((g1.metaPtr + 32#64) ↦₆₄ g1.packedWord ∗
              (Rest2 ∗ Z))))))))))))) := fun Z => by
          rw [← split_m32_byte0 g.metaPtr g.packedWord]
          have h1 :
              (g.metaPtr ↦₆₄ g.prev ∗ ((g.metaPtr + 8#64) ↦₆₄ g.next ∗
                ((g.metaPtr + 16#64) ↦₆₄ g.mem ∗ ((g.metaPtr + 24#64) ↦₃₂ g.availMask ∗
                ((g.metaPtr + 28#64) ↦₃₂ g.freedMask ∗ ((g.metaPtr + 32#64) ↦₆₄ g.packedWord ∗ (RestMeta ∗ Z))))))) =
              ((g.metaPtr ↦ₛ g.metaBytes) ∗ (RestMeta ∗ Z)) := by
            rw [GroupDesc.metaBytes_pointsTo g.metaPtr g]; simp only [sepConj_assoc]
          rw [h1, ← sepConj_assoc, ← hBmMeta, hBmMeta2,
            GroupDesc.metaBytes_pointsTo g.metaPtr g, GroupDesc.metaBytes_pointsTo g1.metaPtr g1]
          simp only [sepConj_assoc]
        conv => arg 4; rw [hSwapMeta, hg1Meta]
        wp_sym_steps
        let h2 : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hsc
        let st1 : MallocngSt :=
          { st with
            ctx := { st.ctx with active := st.ctx.active.set sc g.next }
            activeLists := st.activeLists.set sc ((st.activeLists[sc]'h2).tail ++ [g.metaPtr]) }
        refine SepWP.done (by simp) (by simp [hrun])
          ⟨st1, g1, hg1Mem, by simp [hrun], by simp, by simp [State.spAligned], psp_simp,
           ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [st1],
            fun k hk hk1 _ => List.getElem_set_ne (by omega : sc ≠ k) hk1, Cost.GroupsGrpMono.refl _⟩,
           hg1Sc, hg1Av0, hg1FrNe,
           fun h1' => by simp [st1, hg1Meta],
           by simp [hg1Meta], by simp [State.readReg32],
           fun r r0 r1 r2 r3 r4 => by
             simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
               State.readReg64_writeReg64_ne, ne_eq, r0, r1, r2, r3, r4, not_false_eq_true], ?_⟩
        simp only [State.setPC, State.setMem, State.setPState, State.writeReg64] at hwfRot ⊢
        have hFix : MallocngCoreFixedA γ maddrs st = MallocngCoreFixedA γ maddrs st1 := rfl
        have hBmEq : ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
            ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal := rfl
        have hProtEq : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
            ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal := rfl
        have hMapEq : MappedSet st.masterDom (OwnedMappedByte st) =
            MappedSet st1.masterDom (OwnedMappedByte st1) := rfl
        conv => rhs; rw [coreSt_eq_parts hwfRot, ← hCtxAbs, ← hBmEq, hBmMeta2, GroupDesc.metaBytes_pointsTo g.metaPtr g, GroupDesc.metaBytes_pointsTo g1.metaPtr g1, hg1Meta, ← hProtEq, ← hMapEq, ← hFix]; simp only [sepConj_assoc]
  · refine SepWP.done (by simp) (by simp [hrun])
      ⟨st, g, hg, by simp [hrun], by simp, by simp [State.spAligned], psp_simp,
       AllocSlotStPres.rfl, hScEq, hAv0, hFrNe, hHead,
       by simpa using hx2, by simp [State.readReg32],
       fun r r0 r1 _ r3 r4 => by
         simp only [State.readReg64_setPC, State.readReg64_setPState,
           State.readReg64_writeReg64_ne, ne_eq, r0, r1, r3, r4, not_false_eq_true], ?_⟩
    simp only [State.setPC, State.setPState, State.writeReg64]
    conv => rhs; rw [coreSt_eq_parts hwf, hCtxFoc, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]; rw [split_m32_byte0 g.metaPtr g.packedWord]; simp only [sepConj_assoc]

theorem wp_allocSlot_c8_to_activate [MallocngMultiPlacement]
    (hw0 : Blk08HasWords0 mallocngFaultSvc) (hr0 : Blk08Range0)
    (hw348 : Blk08HasWords348 mallocngFaultSvc) (hr348 : Blk08Range348)
    {inflight sc : Nat} (hsc : sc < 48) {γ : GhostName} {brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : ∀ h1 : sc < st.ctx.active.length, st.ctx.active[sc]'h1 = g.metaPtr)
    (hAv0 : g.availMask = 0#32) (hFrNe : g.freedMask ≠ 0#32)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_c8) (hrun : s.status = .Running)
    (hx2 : s.readReg64 .x2 = g.metaPtr) (hw4 : s.readReg32 .x4 = g.freedMask)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 sc) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_activate) s
      (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
       MallocngRoTablesA maddrs ∗ Frame)
      (fun sf P_f =>
        ∃ st1 : MallocngSt, ∃ g1 ∈ st1.groups,
          sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
          PureStatePres s sf ∧
          AllocSlotStPres sc st st1 ∧
          g1.sc = sc ∧ g1.availMask = 0#32 ∧
          ((2#32 <<< g1.activeIdx) - 1#32) &&& g1.freedMask ≠ 0#32 ∧
          (∀ h1 : sc < st1.ctx.active.length, st1.ctx.active[sc]'h1 = g1.metaPtr) ∧
          sf.readReg64 .x2 = g1.metaPtr ∧
          sf.readReg64 .x22 = Obj.pageOf maddrs.ctx ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x6 →
            sf.readReg64 r = s.readReg64 r) ∧
          P_f = (MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st1 ∗
            MallocngRoTablesA maddrs ∗ Frame))
      (fun _ => ⌜False⌝) := by
  apply sepWP_coreSt_wf; intro hwf
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  obtain ⟨RestMeta, hBmMeta⟩ := byteMap_focus_meta hwf hg
  obtain ⟨RestActB, hBmActB⟩ := byteMap_focus_activeByte hwf hg
  refine SepWP.seq (mid := mbase 8 + allocSlotOff_d0)
    (Mid := fun s1 P1 =>
      s1.sp = s.sp ∧ s1.spAligned = s.spAligned ∧ PureStatePres s s1 ∧ s1.mem = s.mem ∧
      s1.readReg32 .x0 = 2#32 ∧ s1.readReg64 .x2 = g.metaPtr ∧
      s1.readReg32 .x4 = g.freedMask ∧ s1.readReg64 .x5 = g.mem ∧
      (∀ r, r ≠ .x0 → r ≠ .x5 → s1.readReg64 r = s.readReg64 r) ∧
      P1 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
        MallocngRoTablesA maddrs ∗ Frame)) ?_ ?_
  · conv => arg 4; rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]
    dsimp only [allocSlotOff_c8, allocSlotOff_d0] at hpc ⊢
    wp_sym_steps
    refine SepWP.done (by simp) (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], psp_simp, rfl,
       by simp [State.readReg32], by simpa using hx2,
       by simpa [State.readReg32] using hw4, by simp,
       fun r r0 r5 => by
         simp only [State.readReg64_setPC,
           State.readReg64_writeReg64_ne, ne_eq, r0, r5, not_false_eq_true], ?_⟩
    conv => rhs; rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]
  · rintro s1 P1 hpc1 hrun1 ⟨hsp1, hal1, hpsp1, hmem1, hs1_0, hs1_2, hs1_4, hs1_5, hr1, rfl⟩
    have hw1_0 : BitVec.setWidth 32 (s1.readReg64 (Reg.gpr 0#5)) = 2#32 := hs1_0
    have hw1_4 : BitVec.setWidth 32 (s1.readReg64 (Reg.gpr 4#5)) = g.freedMask := hs1_4
    obtain ⟨hActAnd, hActMask⟩ := lsl2_sub1_of_byte g.activeByte
    conv => arg 4; rw [coreSt_eq_parts hwf, hBmActB]; simp only [sepConj_assoc]
    dsimp only [allocSlotOff_d0, allocSlotOff_activate] at hpc1 ⊢
    wp_sym_steps
    wp_if hTstNe
    · have hBrkEq : s1.brk = s.brk := hpsp1.2.1
      have hwf' : MallocngWFInflight inflight maddrs.base brkStart s1.brk liveCost peakCost st :=
        hBrkEq.symm ▸ hwf
      have hs1_22 : s1.readReg64 .x22 = Obj.pageOf maddrs.ctx :=
        (hr1 .x22 (by decide) (by decide)).trans hx22
      refine SepWP.done (by simp) (by simp [hrun1])
        ⟨st, g, hg, by simp [hrun1], by simpa using hsp1, by simpa [State.spAligned] using hal1,
         hpsp1.trans psp_simp, AllocSlotStPres.rfl, hScEq, hAv0,
         by simpa [GroupDesc.activeIdx] using hTstNe, hHead,
         by simpa using hs1_2, by simpa using hs1_22,
         fun r r0 r1 _ r3 _ r5 _ => by
           refine Eq.trans ?_ (hr1 r r0 r5)
           simp only [State.readReg64_setPC, State.readReg64_setPState,
             State.readReg64_writeReg64_ne, ne_eq, r0, r1, r3, not_false_eq_true], ?_⟩
      simp only [State.setPC, State.setPState, State.writeReg64] at hwf' ⊢
      conv => rhs; rw [coreSt_eq_parts hwf', hBmActB]; simp only [sepConj_assoc]
    ·
      have hActMask0 : ((2#32 <<< g.activeIdx) - 1#32) &&& g.freedMask = 0#32 := by
        simpa [GroupDesc.activeIdx] using hTstNe
      have hgw := hwf.groups_wf g hg
      have hActLe : g.activeIdx ≤ g.lastIdx := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hActLt : g.activeIdx < g.lastIdx := Classical.byContradiction fun hGe => by
        have hEqIdx : g.activeIdx = g.lastIdx := by omega
        have hEqFr := activeMask_and_freed_of_eq_lastIdx hgw.2.1 hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hEqIdx
        rw [hEqFr] at hActMask0; exact hFrNe hActMask0
      have hs1_22 : s1.readReg64 .x22 = Obj.pageOf maddrs.ctx :=
        (hr1 .x22 (by decide) (by decide)).trans hx22
      have hs1_23 : s1.readReg64 .x23 = BitVec.ofNat 64 sc :=
        (hr1 .x23 (by decide) (by decide)).trans hx23
      obtain ⟨RestAct, hCtxFoc, hCtxAbs⟩ := ctx_focus_active maddrs.ctx st.ctx hwf.ctx_lens.1 hsc g.next
      have hActAddr := active_slot_addr_eq maddrs.ctx hsc
      have hSwapFoc : ∀ Z : SepProp,
          ((g.mem + 8#64) ↦₈ g.activeByte ∗ (RestActB ∗ Z)) =
            (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ Z) := fun Z => by
        rw [← sepConj_assoc, ← hBmActB]
      conv => arg 4; rw [hSwapFoc, hCtxFoc, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]
      wp_sym_steps
      wp_if hEqSelf
      ·
        have hBrkEq : s1.brk = s.brk := hpsp1.2.1
        have hwf' : MallocngWFInflight inflight maddrs.base brkStart s1.brk liveCost peakCost st :=
          hBrkEq.symm ▸ hwf
        have hPreEq :
            ((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ (st.ctx.active[sc]'h1) ∗
              RestAct ∗ g.metaPtr ↦₆₄ g.prev ∗ (g.metaPtr + 8#64) ↦₆₄ g.next ∗
              (g.metaPtr + 16#64) ↦₆₄ g.mem ∗ (g.metaPtr + 24#64) ↦₃₂ g.availMask ∗
              (g.metaPtr + 28#64) ↦₃₂ g.freedMask ∗ (g.metaPtr + 32#64) ↦₆₄ g.packedWord ∗
              RestMeta ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
              MappedSet st.masterDom (OwnedMappedByte st) ∗
              MallocngCoreFixedA γ maddrs st ∗ MallocngRoTablesA maddrs ∗ Frame) =
            (MallocngCoreStInflightA inflight γ maddrs brkStart s1.brk liveCost peakCost st ∗
              MallocngRoTablesA maddrs ∗ Frame) := by
          symm
          rw [coreSt_eq_parts hwf', hCtxFoc, hBmMeta, GroupDesc.metaBytes_pointsTo]
          simp only [sepConj_assoc]
        conv => arg 4; rw [hPreEq]
        refine SepWP.mono
          (wp_allocSlot_bump_active hw0 hr0 hw348 hr348 hsc hg hScEq hHead hAv0 hActLt _ Frame
            (by dsimp only [allocSlotOff_bump]; rfl) (by simp [hrun1])
            (by simpa using hEqSelf.symm) (by simpa using hs1_5)
            (by simp [State.readReg32, BitVec.truncate_eq_setWidth, GroupDesc.activeIdx])) ?_
        rintro sf P_f _ _ ⟨st1, g1, hg1, hrf, hspf, half, hpspf, hPres, _, hg1Sc, hg1Av, hg1Mask, hg1Hd, hfx2, hfr, hPf⟩
        exact ⟨st1, g1, hg1, hrf, hspf.trans hsp1, half.trans hal1, (hpsp1.trans psp_simp).trans hpspf,
          hPres, hg1Sc, hg1Av, hg1Mask,
          hg1Hd,
          hfx2,
          (hfr .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simpa using hs1_22),
          fun r r0 r1 r2 r3 r4 r5 r6 => by
            refine (hfr r r0 r1 r2 r3 r6).trans ?_
            refine Eq.trans ?_ (hr1 r r0 r5)
            simp only [State.readReg64_setPC, State.readReg64_setPState,
              State.readReg64_writeReg64_ne, ne_eq, r0, r1, r3, r4, not_false_eq_true],
          hPf⟩
      ·
        have hNxNe : g.next ≠ g.metaPtr := fun h => hEqSelf h.symm
        obtain ⟨hwfRot, g1, hg1Mem, hg1Meta, hg1Sc, hg1Av0, hg1FrNe, hg1ActEq⟩ :=
          tryAvail_rotate_wf hwf hsc hg hScEq (hHead h1) hAv0 hFrNe
        wp_sym_steps
        let h2 : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hsc
        let st1 : MallocngSt :=
          { st with
            ctx := { st.ctx with active := st.ctx.active.set sc g.next }
            activeLists := st.activeLists.set sc ((st.activeLists[sc]'h2).tail ++ [g.metaPtr]) }
        have hBrkEq : s1.brk = s.brk := hpsp1.2.1
        have hwf1' : MallocngWFInflight inflight maddrs.base brkStart s1.brk liveCost peakCost st1 :=
          hBrkEq.symm ▸ hwfRot
        have hg1Wf := hwfRot.groups_wf g1 hg1Mem
        have hg1MaskEq := activeMask_and_freed_of_eq_lastIdx hg1Wf.2.1
          hg1Wf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hg1ActEq hActLt hNxNe)
        refine SepWP.done (by simp) (by simp [hrun1])
          ⟨st1, g1, hg1Mem, by simp [hrun1], by simpa using hsp1, by simpa [State.spAligned] using hal1,
           hpsp1.trans psp_simp,
           ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [st1],
            fun k hk hk1 _ => List.getElem_set_ne (by omega : sc ≠ k) hk1, Cost.GroupsGrpMono.refl _⟩,
           hg1Sc, hg1Av0, by rw [hg1MaskEq]; exact hg1FrNe,
           fun h1' => by simp [st1, hg1Meta],
           by simp [hg1Meta], by simpa using hs1_22,
           fun r r0 r1 r2 r3 r4 r5 _ => by
             refine Eq.trans ?_ (hr1 r r0 r5)
             simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
               State.readReg64_writeReg64_ne, ne_eq, r0, r1, r2, r3, r4, not_false_eq_true], ?_⟩
        simp only [State.setPC, State.setMem, State.setPState, State.writeReg64] at hwf1' ⊢
        have hFix : MallocngCoreFixedA γ maddrs st = MallocngCoreFixedA γ maddrs st1 := rfl
        have hBmEq : ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
            ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal := rfl
        have hProtEq : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
            ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal := rfl
        have hMapEq : MappedSet st.masterDom (OwnedMappedByte st) =
            MappedSet st1.masterDom (OwnedMappedByte st1) := rfl
        conv => rhs; rw [coreSt_eq_parts hwf1', ← hCtxAbs, ← hBmEq, hBmMeta, GroupDesc.metaBytes_pointsTo, ← hProtEq, ← hMapEq, ← hFix]; simp only [sepConj_assoc]

/-! ## Entry and `try_avail` dispatch (`+0x000 .. +0x030`) -/

theorem wp_allocSlot_entry_to_030 [MallocngMultiPlacement]
    (_hw0 : Blk08HasWords0 mallocngFaultSvc) (_hr0 : Blk08Range0)
    {inflight sc req : Nat} (hsc : sc < 48) {γ : GhostName}
    {u29 u30 u21 u22 u23 u24 u25 u26 brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (s0 : State) (Frame : SepProp)
    (hpc : s0.pc = mbase 8) (hrun : s0.status = .Running) (hsAl : s0.spAligned = true)
    (hw0_sc : (s0.readReg32 .x0).toNat = sc) (hx1_req : (s0.readReg64 .x1).toNat = req) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_030) s0
      (SlotSaved8 s0.sp u29 u30 u21 u22 u23 u24 u25 u26 ∗
       MallocngCoreStInflightA inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗ Frame)
      (fun sf P_f =>
        ∃ h1 : sc < st.ctx.active.length,
          sf.status = .Running ∧ sf.sp = s0.sp - 96#64 ∧ sf.spAligned = true ∧
          PureStatePres s0 sf ∧
          sf.readReg64 .x1 = BitVec.ofNat 64 sc + 10#64 ∧
          sf.readReg64 .x2 = st.ctx.active[sc]'h1 ∧
          sf.readReg64 .x3 = maddrs.ctx ∧
          sf.readReg64 .x21 = BitVec.ofNat 64 sc ∧
          sf.readReg64 .x22 = Obj.pageOf maddrs.ctx ∧
          sf.readReg64 .x23 = BitVec.ofNat 64 sc ∧
          sf.readReg64 .x25 = BitVec.ofNat 64 req ∧
          sf.readReg64 .x19 = s0.readReg64 .x19 ∧ sf.readReg64 .x20 = s0.readReg64 .x20 ∧
          sf.readReg64 .x27 = s0.readReg64 .x27 ∧ sf.readReg64 .x28 = s0.readReg64 .x28 ∧
          sf.readReg64 .x30 = s0.readReg64 .x30 ∧
          P_f = (SlotSaved8 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
            (s0.readReg64 .x25) (s0.readReg64 .x26) ∗
            MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st ∗ Frame))
      (fun _ => ⌜False⌝) := by
  conv => arg 4; rw [← sepConj_assoc, sepConj_comm (SlotSaved8 _ _ _ _ _ _ _ _ _), sepConj_assoc]
  apply sepWP_coreSt_wf; intro hwf
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  obtain ⟨RestAct, hCtxFoc, _⟩ := ctx_focus_active maddrs.ctx st.ctx hwf.ctx_lens.1 hsc (st.ctx.active[sc]'h1)
  have hActAddr := active_slot_addr_eq maddrs.ctx hsc
  have hSxtw := sbfm_sxtw_sc_of_lt48 (v := s0.readReg64 (Reg.gpr 0#5)) hsc hw0_sc
  have hLoadAddr :
      maddrs.ctx + (((s0.readReg64 (Reg.gpr 0#5) >>> 0 &&& 0xffffffff#64 |||
        (if (s0.readReg64 (Reg.gpr 0#5)).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
          0xffffffff00000000#64) + 10#64) <<< 3) =
      maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc) := by
    rw [hSxtw]; exact hActAddr
  have hx1Bv : s0.readReg64 .x1 = BitVec.ofNat 64 req := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_req, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hx1_req ▸ (s0.readReg64 .x1).isLt)]
  conv => arg 4; rw [coreSt_eq_parts hwf, hCtxFoc]; simp only [SlotSaved8, sepConj_assoc]
  dsimp only [allocSlotOff_030]
  wp_sym_steps
  refine SepWP.done (by simp) (by simp [hrun])
    ⟨h1, by simp [hrun], by simp, by simpa [State.spAligned] using hsAl, psp_simp,
     by simp, by simp, by simp, by simp, by simp, by simp,
     by simp,
     by simp, by simp, by simp, by simp, by simp, ?_⟩
  simp only [State.setPC, State.setMem, State.writeReg64]
  conv => rhs; rw [← sepConj_assoc, sepConj_comm (SlotSaved8 _ _ _ _ _ _ _ _ _), sepConj_assoc, coreSt_eq_parts hwf, hCtxFoc]; simp only [SlotSaved8, sepConj_assoc]

theorem wp_allocSlot_030_zero_to_ag [MallocngMultiPlacement]
    (_hw0 : Blk08HasWords0 mallocngFaultSvc) (_hr0 : Blk08Range0)
    (_hw564 : Blk08HasWords564 mallocngFaultSvc) (_hr564 : Blk08Range564)
    {sp0 u19 u20 u27 u28 : BitVec 64}
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_030) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64) (hsAl : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = 0#64) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_ag) s
      (SlotSaved4 sp0 u19 u20 u27 u28 ∗ Frame)
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = sp0 - 96#64 ∧ sf.spAligned = true ∧
        PureStatePres s sf ∧
        (∀ r, sf.readReg64 r = s.readReg64 r) ∧
        P_f = (SlotSaved4 sp0 (s.readReg64 .x19) (s.readReg64 .x20)
          (s.readReg64 .x27) (s.readReg64 .x28) ∗ Frame))
      (fun _ => ⌜False⌝) := by
  conv => arg 4; simp only [SlotSaved4, sepConj_assoc]
  dsimp only [allocSlotOff_030, allocSlotOff_ag] at hpc ⊢
  wp_sym_steps
  refine SepWP.done (by simp) (by simp [hrun])
    ⟨by simp [hrun], by simpa using hsp, by simpa [State.spAligned] using hsAl, psp_simp,
     fun r => by simp, ?_⟩
  conv => rhs; simp only [SlotSaved4, sepConj_assoc]

theorem wp_allocSlot_030_fast_to_208 [MallocngMultiPlacement]
    (_hw0 : Blk08HasWords0 mallocngFaultSvc) (_hr0 : Blk08Range0)
    {inflight : Nat} {γ : GhostName} {brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hAvNe : g.availMask ≠ 0#32)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_030) (hrun : s.status = .Running)
    (hx2 : s.readReg64 .x2 = g.metaPtr) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_fast_pop) s
      (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧ sf.mem = s.mem ∧
        sf.readReg32 .x0 = g.availMask ∧ sf.readReg64 .x2 = g.metaPtr ∧
        (∀ r, r ≠ .x0 → sf.readReg64 r = s.readReg64 r) ∧
        P_f = (MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st ∗ Frame))
      (fun _ => ⌜False⌝) := by
  apply sepWP_coreSt_wf; intro hwf
  have hMetaNe0 : g.metaPtr ≠ 0#64 := by
    intro h0; have hLo := (meta_ownedRw_of_mem_groups hwf hg).1; rw [h0] at hLo; simp at hLo
  obtain ⟨RestMeta, hBmMeta⟩ := byteMap_focus_meta hwf hg
  conv => arg 4; rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]
  dsimp only [allocSlotOff_030, allocSlotOff_fast_pop] at hpc ⊢
  wp_sym_steps
  refine SepWP.done (by simp) (by simp [hrun])
    ⟨by simp [hrun], by simp, by simp [State.spAligned], psp_simp, rfl,
     by simp [State.readReg32], by simpa using hx2,
     fun r r0 => by simp only [State.readReg64_setPC, State.readReg64_writeReg64_ne, ne_eq, r0, not_false_eq_true], ?_⟩
  simp only [State.setPC, State.writeReg64]
  conv => rhs; rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]

theorem wp_allocSlot_030_to_044 [MallocngMultiPlacement]
    (_hw0 : Blk08HasWords0 mallocngFaultSvc) (_hr0 : Blk08Range0)
    {inflight : Nat} {γ : GhostName} {sp0 u19 u20 u27 u28 brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hAv0 : g.availMask = 0#32)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_030) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64) (hsAl : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = g.metaPtr) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_044) s
      (SlotSaved4 sp0 u19 u20 u27 u28 ∗
       MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = sp0 - 96#64 ∧ sf.spAligned = true ∧
        PureStatePres s sf ∧
        (∀ r, r ≠ .x0 → sf.readReg64 r = s.readReg64 r) ∧
        P_f = (SlotSaved4 sp0 (s.readReg64 .x19) (s.readReg64 .x20)
          (s.readReg64 .x27) (s.readReg64 .x28) ∗
          MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st ∗ Frame))
      (fun _ => ⌜False⌝) := by
  conv => arg 4; rw [← sepConj_assoc, sepConj_comm (SlotSaved4 _ _ _ _ _), sepConj_assoc]
  apply sepWP_coreSt_wf; intro hwf
  have hMetaNe0 : g.metaPtr ≠ 0#64 := by
    intro h0; have hLo := (meta_ownedRw_of_mem_groups hwf hg).1; rw [h0] at hLo; simp at hLo
  obtain ⟨RestMeta, hBmMeta⟩ := byteMap_focus_meta hwf hg
  conv => arg 4; rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo, hAv0]; simp only [SlotSaved4, sepConj_assoc]
  dsimp only [allocSlotOff_030, allocSlotOff_044] at hpc ⊢
  wp_sym_steps
  refine SepWP.done (by simp) (by simp [hrun])
    ⟨by simp [hrun], by simpa using hsp, by simpa [State.spAligned] using hsAl, psp_simp,
     fun r r0 => by
       simp only [State.readReg64_setPC, State.readReg64_setMem,
         State.readReg64_writeReg64_ne, ne_eq, r0, not_false_eq_true], ?_⟩
  simp only [State.setPC, State.setMem, State.writeReg64]
  conv => rhs; rw [← sepConj_assoc, sepConj_comm (SlotSaved4 _ _ _ _ _), sepConj_assoc, coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo, hAv0]; simp only [SlotSaved4, sepConj_assoc]

theorem wp_allocSlot_030_deq_singleton_to_ag [MallocngMultiPlacement]
    (hw0 : Blk08HasWords0 mallocngFaultSvc) (hr0 : Blk08Range0)
    {inflight sc : Nat} (hsc : sc < 48) {γ : GhostName}
    {sp0 u19 u20 u27 u28 brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : ∀ h1 : sc < st.ctx.active.length, st.ctx.active[sc]'h1 = g.metaPtr)
    (hAv0 : g.availMask = 0#32) (hFr0 : g.freedMask = 0#32) (hNxSelf : g.next = g.metaPtr)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_030) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64) (hsAl : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 sc + 10#64)
    (hx2 : s.readReg64 .x2 = g.metaPtr)
    (hx3 : s.readReg64 .x3 = maddrs.ctx)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 sc) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_ag) s
      (SlotSaved4 sp0 u19 u20 u27 u28 ∗
       MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)
      (fun sf P_f =>
        ∃ st1 : MallocngSt,
          sf.status = .Running ∧ sf.sp = sp0 - 96#64 ∧ sf.spAligned = true ∧
          PureStatePres s sf ∧
          AllocSlotStPres sc st st1 ∧ totalClaimedSlots st1 = totalClaimedSlots st ∧
          (∀ h1' : sc < st1.ctx.active.length, st1.ctx.active[sc]'h1' = 0#64) ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → sf.readReg64 r = s.readReg64 r) ∧
          P_f = (SlotSaved4 sp0 (s.readReg64 .x19) (s.readReg64 .x20)
            (s.readReg64 .x27) (s.readReg64 .x28) ∗
            MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st1 ∗ Frame))
      (fun _ => ⌜False⌝) := by
  refine SepWP.seq (wp_allocSlot_030_to_044 hw0 hr0 hg hAv0 s Frame hpc hrun hsp hsAl hx2) ?_
  rintro s1 P1 hpc1 hrun1 ⟨_, hsp1, hal1, hpsp1, hr1, rfl⟩
  conv => arg 4; rw [← sepConj_assoc, sepConj_comm (SlotSaved4 _ _ _ _ _), sepConj_assoc]
  apply sepWP_coreSt_wf; intro hwf
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  obtain ⟨hwf1, hCnt1, hEff1, hDyn1, hPn1, hMp1, hBmFoc, hBmAbs⟩ :=
    tryAvail_dequeue_singleton_absorb hwf hsc hg hScEq (hHead h1) hAv0 hFr0 hNxSelf
  obtain ⟨RestAct, hCtxFoc, hCtxAbs⟩ := ctx_focus_active maddrs.ctx st.ctx hwf.ctx_lens.1 hsc 0#64
  have hActAddr := active_slot_addr_eq maddrs.ctx hsc
  have hs1_1 : s1.readReg64 .x1 = BitVec.ofNat 64 sc + 10#64 := (hr1 .x1 (by decide)).trans hx1
  have hs1_2 : s1.readReg64 .x2 = g.metaPtr := (hr1 .x2 (by decide)).trans hx2
  have hs1_3 : s1.readReg64 .x3 = maddrs.ctx := (hr1 .x3 (by decide)).trans hx3
  have hs1_22 : s1.readReg64 .x22 = Obj.pageOf maddrs.ctx := (hr1 .x22 (by decide)).trans hx22
  have hs1_23 : s1.readReg64 .x23 = BitVec.ofNat 64 sc := (hr1 .x23 (by decide)).trans hx23
  conv => arg 4; rw [coreSt_eq_parts hwf, hCtxFoc, hBmFoc, GroupDesc.metaBytes_pointsTo, hFr0, hNxSelf]; simp only [sepConj_assoc]
  dsimp only [allocSlotOff_044, allocSlotOff_ag] at hpc1 ⊢
  wp_sym_steps
  let g' : GroupDesc := { g with prev := 0#64, next := 0#64 }
  let fG : GroupDesc → GroupDesc := fun u => if u.metaPtr == g.metaPtr then g' else u
  let st1 : MallocngSt :=
    { st with
      ctx := { st.ctx with active := st.ctx.active.set sc 0#64 }
      groups := st.groups.map fG
      activeLists := st.activeLists.set sc []
      byteVal := writeBytesToMap st.byteVal g.metaPtr g'.metaBytes }
  refine SepWP.done (by simp) (by simp [hrun1])
    ⟨st1, by simp [hrun1], by simpa using hsp1, by simpa [State.spAligned] using hal1,
     hpsp1.trans psp_simp,
     ⟨rfl, rfl, hEff1, hCnt1, rfl, hDyn1, by simp [st1],
      fun k hk hk1 _ => List.getElem_set_ne (by omega : sc ≠ k) hk1,
      groupsGrpMono_map_ite hg g.metaPtr rfl (Nat.le_refl _)⟩,
     by
       show (List.map _ (List.map fG st.groups)).sum = (List.map _ st.groups).sum
       rw [List.map_map]; congr 1; apply List.map_congr_left; intro u hu
       dsimp only [Function.comp, fG]; split
       · rename_i hm; rw [mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg (beq_iff_eq.mp hm)]
       · rfl,
     fun h1' => by simp [st1],
     fun r r0 r1 r2 r4 => by
       refine Eq.trans ?_ (hr1 r r0)
       simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
         State.readReg64_writeReg64_ne, ne_eq, r0, r1, r2, r4, not_false_eq_true], ?_⟩
  simp only [State.setPC, State.setMem, State.setPState, State.writeReg64] at hwf1 ⊢
  have hFix : MallocngCoreFixedA γ maddrs st = MallocngCoreFixedA γ maddrs st1 := rfl
  (conv => rhs; rw [← sepConj_assoc, sepConj_comm (SlotSaved4 _ _ _ _ _), sepConj_assoc, coreSt_eq_parts hwf1, ← hCtxAbs, ← hBmAbs, ← hPn1, ← hMp1, ← hFix]; dsimp only [g']; rw [GroupDesc.metaBytes_pointsTo, hFr0]; simp only [sepConj_assoc]); rfl

theorem wp_allocSlot_030_slow_to_a8 [MallocngMultiPlacement]
    (hw0 : Blk08HasWords0 mallocngFaultSvc) (hr0 : Blk08Range0)
    {inflight sc : Nat} (hsc : sc < 48) {γ : GhostName}
    {sp0 u19 u20 u27 u28 brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : ∀ h1 : sc < st.ctx.active.length, st.ctx.active[sc]'h1 = g.metaPtr)
    (hAv0 : g.availMask = 0#32) (hSlow : g.freedMask ≠ 0#32 ∨ g.next ≠ g.metaPtr)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_030) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64) (hsAl : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 sc + 10#64)
    (hx2 : s.readReg64 .x2 = g.metaPtr)
    (hx3 : s.readReg64 .x3 = maddrs.ctx)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 sc) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_a8) s
      (SlotSaved4 sp0 u19 u20 u27 u28 ∗
       MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)
      (fun sf P_f =>
        ∃ st1 : MallocngSt, ∃ g1 ∈ st1.groups,
          sf.status = .Running ∧ sf.sp = sp0 - 96#64 ∧ sf.spAligned = true ∧
          PureStatePres s sf ∧
          AllocSlotStPres sc st st1 ∧
          g1.sc = sc ∧ g1.availMask = 0#32 ∧ g1.freedMask ≠ 0#32 ∧
          (∀ h1' : sc < st1.ctx.active.length, st1.ctx.active[sc]'h1' = g1.metaPtr) ∧
          sf.readReg64 .x2 = g1.metaPtr ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → sf.readReg64 r = s.readReg64 r) ∧
          P_f = (SlotSaved4 sp0 (s.readReg64 .x19) (s.readReg64 .x20)
            (s.readReg64 .x27) (s.readReg64 .x28) ∗
            MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st1 ∗ Frame))
      (fun _ => ⌜False⌝) := by
  refine SepWP.seq (wp_allocSlot_030_to_044 hw0 hr0 hg hAv0 s Frame hpc hrun hsp hsAl hx2) ?_
  rintro s1 P1 hpc1 hrun1 ⟨_, hsp1, hal1, hpsp1, hr1, rfl⟩
  conv => arg 4; rw [← sepConj_assoc, sepConj_comm (SlotSaved4 _ _ _ _ _), sepConj_assoc]
  apply sepWP_coreSt_wf; intro hwf
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  have hHead1 := hHead h1
  obtain ⟨RestAct, hCtxFoc, hCtxAbs⟩ := ctx_focus_active maddrs.ctx st.ctx hwf.ctx_lens.1 hsc g.next
  have hActAddr := active_slot_addr_eq maddrs.ctx hsc
  have hs1_1 : s1.readReg64 .x1 = BitVec.ofNat 64 sc + 10#64 := (hr1 .x1 (by decide)).trans hx1
  have hs1_2 : s1.readReg64 .x2 = g.metaPtr := (hr1 .x2 (by decide)).trans hx2
  have hs1_3 : s1.readReg64 .x3 = maddrs.ctx := (hr1 .x3 (by decide)).trans hx3
  have hs1_22 : s1.readReg64 .x22 = Obj.pageOf maddrs.ctx := (hr1 .x22 (by decide)).trans hx22
  have hs1_23 : s1.readReg64 .x23 = BitVec.ofNat 64 sc := (hr1 .x23 (by decide)).trans hx23
  dsimp only [allocSlotOff_044, allocSlotOff_a8] at hpc1 ⊢
  by_cases hFr0 : g.freedMask = 0#32
  · have hNxNe : g.next ≠ g.metaPtr := hSlow.resolve_left (fun h => h hFr0)
    have hNeSelf : g.metaPtr ≠ g.next := hNxNe.symm
    obtain ⟨gNext, gPrev, msTl, _, hgNxM, hgNxNe, _, hgPvM, hgPvNe, hGNxNe0, _, _,
      hg1Mem, hg1Meta, hg1Sc, hg1Av0, hg1FrNe, hwf1, hCnt1, hEff1, hDyn1, hPn1, hMp1, hCaseEq, hCaseNe⟩ :=
      tryAvail_dequeue_multi_absorb hwf hsc hg hScEq hHead1 hAv0 hFr0 hNxNe
    let fG : GroupDesc → GroupDesc := fun u =>
      if u.metaPtr == g.metaPtr then { u with prev := 0#64, next := 0#64 }
      else { u with
        prev := if u.metaPtr == g.next then g.prev else u.prev
        next := if u.metaPtr == g.prev then g.next else u.next }
    let bv1 :=
      if g.prev = g.next then
        writeBytesToMap (writeBytesToMap st.byteVal gNext.metaPtr (fG gNext).metaBytes)
          g.metaPtr (fG g).metaBytes
      else
        writeBytesToMap
          (writeBytesToMap (writeBytesToMap st.byteVal gPrev.metaPtr (fG gPrev).metaBytes)
            gNext.metaPtr (fG gNext).metaBytes)
          g.metaPtr (fG g).metaBytes
    let st1 : MallocngSt :=
      { st with
        ctx := { st.ctx with active := st.ctx.active.set sc g.next }
        groups := st.groups.map fG
        activeLists := st.activeLists.set sc (g.next :: msTl)
        byteVal := bv1 }
    have hFgG : fG g = { g with prev := 0#64, next := 0#64 } := by dsimp only [fG]; simp
    have hNxNeM : (gNext.metaPtr == g.metaPtr) = false :=
      beq_false_of_ne (by rw [hgNxM]; exact hNxNe)
    have hEqNx : (gNext.metaPtr == g.next) = true := by simp [hgNxM]
    dsimp only [fG] at hFgG
    by_cases hPN : g.prev = g.next
    · obtain ⟨_, hBmFoc2, hBmAbs2⟩ := hCaseEq hPN
      have hEqPvNx : (gNext.metaPtr == g.prev) = true := by simp [hgNxM, hPN]
      have hFgNx : fG gNext = { gNext with prev := g.next, next := g.next } := by
        dsimp only [fG]; simp only [hNxNeM, Bool.false_eq_true, ↓reduceIte, hEqNx, hPN]
      dsimp only [fG] at hFgNx
      conv => arg 4; rw [coreSt_eq_parts hwf, hCtxFoc, hHead1, hBmFoc2, GroupDesc.metaBytes_pointsTo, GroupDesc.metaBytes_pointsTo, hgNxM, hFr0, hPN]; simp only [sepConj_assoc]
      wp_sym_steps
      refine SepWP.done (by simp) (by simp [hrun1])
        ⟨st1, fG gNext, hg1Mem, by simp [hrun1], by simpa using hsp1, by simpa [State.spAligned] using hal1,
         hpsp1.trans psp_simp,
         ⟨rfl, rfl, hEff1, hCnt1, rfl, hDyn1, by simp [st1],
          fun k hk hk1 _ => List.getElem_set_ne (by omega : sc ≠ k) hk1,
          groupsGrpMono_map fG fun u _ => by dsimp only [fG]; split <;> exact ⟨rfl, Nat.le_refl _⟩⟩,
         hg1Sc, hg1Av0, hg1FrNe,
         fun h1' => (by simp [st1] : (st1.ctx.active[sc]'h1') = g.next).trans hg1Meta.symm,
         (by simp : _ = g.next).trans hg1Meta.symm,
         fun r r0 r1 r2 r4 => by
           refine Eq.trans ?_ (hr1 r r0)
           simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
             State.readReg64_writeReg64_ne, ne_eq, r0, r1, r2, r4, not_false_eq_true], ?_⟩
      simp only [State.setPC, State.setMem, State.setPState, State.writeReg64] at hwf1 ⊢
      have hFix : MallocngCoreFixedA γ maddrs st = MallocngCoreFixedA γ maddrs st1 := rfl
      (conv => rhs; rw [← sepConj_assoc, sepConj_comm (SlotSaved4 _ _ _ _ _), sepConj_assoc, coreSt_eq_parts hwf1, ← hCtxAbs, ← hBmAbs2, ← hPn1, ← hMp1, ← hFix]; dsimp only; rw [hFgG, hFgNx]; simp only [GroupDesc.metaBytes_pointsTo, hgNxM, hFr0, sepConj_assoc]); rfl
    · obtain ⟨_, hBmFoc3, hBmAbs3⟩ := hCaseNe hPN
      have hPvNeG : g.prev ≠ g.metaPtr := fun hE => hgPvNe (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 ‹gPrev ∈ st.groups› hg (hgPvM.trans hE))
      have hPvNeM : (gPrev.metaPtr == g.metaPtr) = false := beq_false_of_ne (hgPvM ▸ hPvNeG)
      have hNxNePv' : (gNext.metaPtr == g.prev) = false := beq_false_of_ne (by rw [hgNxM]; exact Ne.symm hPN)
      have hEqPv : (gPrev.metaPtr == g.prev) = true := by simp [hgPvM]
      have hPvNeNx' : (gPrev.metaPtr == g.next) = false := beq_false_of_ne (by rw [hgPvM]; exact hPN)
      have hFgNx : fG gNext = { gNext with prev := g.prev } := by
        dsimp only [fG]; simp only [hNxNeM, Bool.false_eq_true, ↓reduceIte, hEqNx, hNxNePv']
      have hFgPv : fG gPrev = { gPrev with next := g.next } := by
        dsimp only [fG]; simp only [hPvNeM, Bool.false_eq_true, ↓reduceIte, hPvNeNx', hEqPv]
      dsimp only [fG] at hFgNx hFgPv
      conv => arg 4; rw [coreSt_eq_parts hwf, hCtxFoc, hHead1, hBmFoc3, GroupDesc.metaBytes_pointsTo, GroupDesc.metaBytes_pointsTo, GroupDesc.metaBytes_pointsTo, hgNxM, hgPvM, hFr0]; simp only [sepConj_assoc]
      wp_sym_steps
      refine SepWP.done (by simp) (by simp [hrun1])
        ⟨st1, fG gNext, hg1Mem, by simp [hrun1], by simpa using hsp1, by simpa [State.spAligned] using hal1,
         hpsp1.trans psp_simp,
         ⟨rfl, rfl, hEff1, hCnt1, rfl, hDyn1, by simp [st1],
          fun k hk hk1 _ => List.getElem_set_ne (by omega : sc ≠ k) hk1,
          groupsGrpMono_map fG fun u _ => by dsimp only [fG]; split <;> exact ⟨rfl, Nat.le_refl _⟩⟩,
         hg1Sc, hg1Av0, hg1FrNe,
         fun h1' => (by simp [st1] : (st1.ctx.active[sc]'h1') = g.next).trans hg1Meta.symm,
         (by simp : _ = g.next).trans hg1Meta.symm,
         fun r r0 r1 r2 r4 => by
           refine Eq.trans ?_ (hr1 r r0)
           simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
             State.readReg64_writeReg64_ne, ne_eq, r0, r1, r2, r4, not_false_eq_true], ?_⟩
      simp only [State.setPC, State.setMem, State.setPState, State.writeReg64] at hwf1 ⊢
      have hFix : MallocngCoreFixedA γ maddrs st = MallocngCoreFixedA γ maddrs st1 := rfl
      (conv => rhs; rw [← sepConj_assoc, sepConj_comm (SlotSaved4 _ _ _ _ _), sepConj_assoc, coreSt_eq_parts hwf1, ← hCtxAbs, ← hBmAbs3, ← hPn1, ← hMp1, ← hFix]; dsimp only; rw [hFgG, hFgNx, hFgPv]; simp only [GroupDesc.metaBytes_pointsTo, hgNxM, hgPvM, hFr0, sepConj_assoc]); rfl
  · obtain ⟨hwfRot, g1, hg1Mem, hg1Meta, hg1Sc, hg1Av0, hg1FrNe, _⟩ :=
      tryAvail_rotate_wf hwf hsc hg hScEq hHead1 hAv0 hFr0
    obtain ⟨RestMeta, hBmMeta⟩ := byteMap_focus_meta hwf hg
    conv => arg 4; rw [coreSt_eq_parts hwf, hCtxFoc, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]
    wp_sym_steps
    let h2 : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hsc
    let st1 : MallocngSt :=
      { st with
        ctx := { st.ctx with active := st.ctx.active.set sc g.next }
        activeLists := st.activeLists.set sc ((st.activeLists[sc]'h2).tail ++ [g.metaPtr]) }
    refine SepWP.done (by simp) (by simp [hrun1])
      ⟨st1, g1, hg1Mem, by simp [hrun1], by simpa using hsp1, by simpa [State.spAligned] using hal1,
       hpsp1.trans psp_simp,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [st1],
        fun k hk hk1 _ => List.getElem_set_ne (by omega : sc ≠ k) hk1, Cost.GroupsGrpMono.refl _⟩,
       hg1Sc, hg1Av0, hg1FrNe, fun h1' => by simp [st1, hg1Meta], by simp [hg1Meta],
       fun r r0 r1 r2 r4 => by
         refine Eq.trans ?_ (hr1 r r0)
         simp only [State.readReg64_setPC, State.readReg64_setMem,
           State.readReg64_writeReg64_ne, ne_eq, r0, r2, r4, not_false_eq_true], ?_⟩
    simp only [State.setPC, State.setMem, State.writeReg64] at hwfRot ⊢
    have hFix : MallocngCoreFixedA γ maddrs st = MallocngCoreFixedA γ maddrs st1 := rfl
    have hBmEq : ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
        ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal := rfl
    have hProtEq : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
        ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal := rfl
    have hMapEq : MappedSet st.masterDom (OwnedMappedByte st) =
        MappedSet st1.masterDom (OwnedMappedByte st1) := rfl
    conv => rhs; rw [← sepConj_assoc, sepConj_comm (SlotSaved4 _ _ _ _ _), sepConj_assoc, coreSt_eq_parts hwfRot, ← hCtxAbs, ← hBmEq, hBmMeta, GroupDesc.metaBytes_pointsTo, ← hProtEq, ← hMapEq, ← hFix]; simp only [sepConj_assoc]

end VerifiedLibraries.Mallocng.Proofs
