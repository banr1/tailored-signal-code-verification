/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupStage2

/-!
# Placed `alloc_group` Root `mmap` Path

Proves `SepWP` lemmas for the `alloc_group` root `mmap` path in `mallocng`, covering the
`unmap_seq` reset loop, bounce-counter updates, per-class usage checks, and page-aligned root
size and slot-count selection.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

arm64_proof_prelude

/-! ## `SepWP` Satisfaction Witness and Slice Helpers -/

theorem sepWP_with_sat {prog : Program} {exit_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : prog.CodeLoaded s.mem → (∃ R, s.mem ⊨ P ∗ R) → SepWP prog exit_pc s P post oom) :
    SepWP prog exit_pc s P post oom := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  exact SepWP.to_reaches_pc (h hL ⟨R, hm⟩) hm hL

private theorem split_rw_byte (base : BitVec 64) (bs : List (BitVec 8)) {idx : Nat}
    (hidx : idx < bs.length) :
    (base ↦ₛ bs) =
      (((base + BitVec.ofNat 64 idx) ↦₈ (bs[idx]'hidx)) ∗
       (base ↦ₛ bs.take idx) ∗
       ((base + BitVec.ofNat 64 (idx + 1)) ↦ₛ bs.drop (idx + 1))) := by
  have heq : bs = bs.take idx ++ [bs[idx]'hidx] ++ bs.drop (idx + 1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hidx,
      List.take_append_drop]
  have htl : (bs.take idx).length = idx := List.length_take_of_le (by omega)
  conv => lhs; rw [heq]
  rw [List.append_assoc, pointsToBytes_append, htl, List.singleton_append, pointsToBytes_cons,
    BitVec.add_assoc, ← BitVec.ofNat_add]
  ac_rfl

private theorem fold_rw_byte_set (base : BitVec 64) (bs : List (BitVec 8)) {idx : Nat}
    (hidx : idx < bs.length) (v : BitVec 8) :
    (((base + BitVec.ofNat 64 idx) ↦₈ v) ∗
     (base ↦ₛ bs.take idx) ∗
     ((base + BitVec.ofNat 64 (idx + 1)) ↦ₛ bs.drop (idx + 1))) =
      (base ↦ₛ bs.set idx v) := by
  have hlen : idx < (bs.set idx v).length := by simp [hidx]
  rw [split_rw_byte base (bs.set idx v) hlen]
  simp [List.getElem_set_self, List.take_set_of_le (Nat.le_refl idx),
    List.drop_set_of_lt (Nat.lt_succ_self idx)]

abbrev allocSlotOff_seq_after : BitVec 64 := words_insn_off% blk08Words 0x71007ebf#32

/-! ## `unmap_seq` Zeroing Loop, Bounces Update, and Usage Check -/

theorem wp_unmap_zero_loop [MallocngMultiPlacement]
    (_hw768 : Blk08HasWords768 mallocngFaultSvc) (_hr768 : Blk08Range768) :
    ∀ (rem : Nat) (s : State) (bs : List (BitVec 8)) (seqOld : BitVec 8) (Frame : SepProp),
      1 ≤ rem → rem ≤ 32 → bs.length = rem →
      s.pc = mbase 8 + allocSlotOff_unmap_loop → s.status = .Running →
      s.readReg64 .x1 = maddrs.ctx + BitVec.ofNat 64 (848 + (32 - rem)) →
      s.readReg64 .x3 = maddrs.ctx + 880#64 →
      s.readReg64 .x22 = Obj.pageOf maddrs.ctx →
      SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_seq_after) s
        (((maddrs.ctx + BitVec.ofNat 64 (848 + (32 - rem))) ↦ₛ bs) ∗
         ((maddrs.ctx + 912#64) ↦₈ seqOld) ∗ Frame)
        (fun sf P_f => sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
          PureStatePres s sf ∧
          (∀ r, r ≠ .x1 → r ≠ .x3 → sf.readReg64 r = s.readReg64 r) ∧
          P_f = (((maddrs.ctx + BitVec.ofNat 64 (848 + (32 - rem))) ↦ₛ List.replicate rem 0#8) ∗
                 ((maddrs.ctx + 912#64) ↦₈ 1#8) ∗ Frame))
        (fun _ => ⌜False⌝) := by
  intro rem
  induction rem with
  | zero => intro _ _ _ _ h1; omega
  | succ k ih =>
    intro s bs seqOld Frame _ hk32 hlen hpc hrun hx1 hx3 hx22
    cases bs with
    | nil => simp at hlen
    | cons b0 rest =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      cases k with
      | zero =>
        cases rest with
        | cons _ _ => simp at hlen
        | nil =>
          have h1eq : maddrs.ctx + BitVec.ofNat 64 (848 + (32 - 1)) = maddrs.ctx + 879#64 := rfl
          have h1next : maddrs.ctx + 879#64 + 1#64 = maddrs.ctx + 880#64 := by bv_robdd
          dsimp only [allocSlotOff_unmap_loop, allocSlotOff_seq_after] at hpc ⊢
          rw [h1eq] at hx1 ⊢
          conv => arg 4; simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, sepConj_assoc]
          wp_sym_steps
          refine SepWP.done rfl (by simp [hrun]) ⟨by simp [hrun], by simp, by simp [State.spAligned],
            psp_rfl, ?_, ?_⟩
          · intro r hr1 hr3
            simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
              State.readReg64_writeReg64_ne _ _ _ _ hr3, State.readReg64_writeReg64_ne _ _ _ _ hr1]
          · simp [List.replicate, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
      | succ m =>
        have hoff0 : 848 + (32 - (m + 1 + 1)) = 878 - m := by omega
        have hoff1 : 848 + (32 - (m + 1)) = 879 - m := by omega
        have hstep_addr : maddrs.ctx + BitVec.ofNat 64 (878 - m) + 1#64 =
            maddrs.ctx + BitVec.ofNat 64 (879 - m) := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
        rw [hoff0] at hx1 ⊢
        dsimp only [allocSlotOff_unmap_loop, allocSlotOff_seq_after] at hpc ⊢
        conv => arg 4; simp only [pointsToBytes_cons, hstep_addr, sepConj_assoc]
        wp_sym_steps
        wp_if hbr
        · refine SepWP.seq (mid := mbase 8 + allocSlotOff_unmap_loop)
            (Mid := fun sj Pj =>
              (sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧
                sj.readReg64 .x1 = maddrs.ctx + BitVec.ofNat 64 (879 - m) ∧
                sj.readReg64 .x3 = maddrs.ctx + 880#64 ∧ sj.readReg64 .x22 = Obj.pageOf maddrs.ctx ∧
                ∀ r, r ≠ .x1 → sj.readReg64 r = s.readReg64 r) ∧
              Pj = (((maddrs.ctx + BitVec.ofNat 64 (879 - m)) ↦ₛ rest) ∗
                ((maddrs.ctx + 912#64) ↦₈ seqOld) ∗
                ((maddrs.ctx + BitVec.ofNat 64 (878 - m)) ↦₈ 0#8) ∗ Frame)) ?_ ?_
          · refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
              by simp, by simpa using hx3, by simpa using hx22, ?_⟩,
              by ac_rfl⟩
            intro r hr1
            simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
              State.readReg64_writeReg64_ne _ _ _ _ hr1]
          · intro sj Pj hjpc hjrun ⟨⟨hsp, hal, hpsp, hj1, hj3, hj22, hjr⟩, hPj⟩
            subst hPj
            rw [← hoff1] at hj1
            conv => arg 4; rw [← hoff1]
            have hrec := ih sj rest seqOld
              (((maddrs.ctx + BitVec.ofNat 64 (878 - m)) ↦₈ 0#8) ∗ Frame)
              (by omega) (by omega) hlen hjpc hjrun hj1 hj3 hj22
            dsimp only [allocSlotOff_seq_after] at hrec
            refine SepWP.mono hrec ?_
            intro sf P_f _ _ ⟨hsfrun, hsp2, hal2, hpsp2, hregs2, hPf⟩
            refine ⟨hsfrun, hsp2.trans hsp, hal2.trans hal, hpsp.trans hpsp2,
              fun r hr1 hr3 => (hregs2 r hr1 hr3).trans (hjr r hr1), ?_⟩
            rw [hPf, hoff1]
            simp only [List.replicate_succ, pointsToBytes_cons, hstep_addr]
            ac_rfl
        · have ht := congrArg BitVec.toNat hbr
          rw [BitVec.toNat_ofNat] at ht
          change 880 = (879 - m) % (2 ^ 64) at ht
          rw [Nat.mod_eq_of_lt (by omega)] at ht; omega

private theorem split_words64 (base : BitVec 64) (ws : List (BitVec 64)) {idx : Nat}
    (hidx : idx < ws.length) :
    (base ↦₆₄* ws) =
      (((base + BitVec.ofNat 64 (8 * idx)) ↦₆₄ (ws[idx]'hidx)) ∗
       (base ↦₆₄* ws.take idx) ∗
       ((base + BitVec.ofNat 64 (8 * (idx + 1))) ↦₆₄* ws.drop (idx + 1))) := by
  have heq : ws = ws.take idx ++ [ws[idx]'hidx] ++ ws.drop (idx + 1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hidx,
      List.take_append_drop]
  have htl : (ws.take idx).length = idx := List.length_take_of_le (by omega)
  conv => lhs; rw [heq]
  rw [List.append_assoc, pointsToWords64_append, htl, List.singleton_append, pointsToWords64_cons,
    BitVec.add_assoc, ← BitVec.ofNat_add]
  have h8 : 8 * idx + 8 = 8 * (idx + 1) := by omega
  rw [h8]; ac_rfl

private theorem sub7_check :
    ((List.range 48).all fun sc =>
      let w3 := BitVec.setWidth 32 (BitVec.ofNat 64 sc) - 7#32
      (31#32).ult w3 ||
      (decide (7 ≤ sc ∧ sc ≤ 38) &&
       (BitVec.signExtend 64 w3 == BitVec.ofNat 64 (sc - 7)))) = true := by decide +kernel

private theorem sub7_ule_31 {sc : Nat} (hsc : sc < 48)
    (h : ¬ ((31#32).ult (BitVec.setWidth 32 (BitVec.ofNat 64 sc) - 7#32) = true)) :
    7 ≤ sc ∧ sc ≤ 38 ∧
    BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 sc) - 7#32) =
      BitVec.ofNat 64 (sc - 7) := by
  have ha := List.all_eq_true.mp sub7_check sc (List.mem_range.mpr hsc)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ha
  rcases ha with hlt | ⟨⟨h1, h2⟩, h3⟩
  · exact False.elim (h hlt)
  · exact ⟨h1, h2, h3⟩

private theorem sc_next_off_check :
    ((List.range 32).all fun sc =>
      let w1 := BitVec.setWidth 32 (BitVec.ofNat 64 sc) + 1#32
      (BitVec.signExtend 64 w1 <<< 3) + 0x1d0#64 ==
        464#64 + BitVec.ofNat 64 (8 * (sc + 1))) = true := by decide +kernel

private theorem sc_next_off_eq (ctxAddr : BitVec 64) {sc : Nat} (hsc31 : sc ≤ 31) :
    ctxAddr + (BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 sc) + 1#32) <<< 3) +
      0x1d0#64 = ctxAddr + 464#64 + BitVec.ofNat 64 (8 * (sc + 1)) := by
  have ha := List.all_eq_true.mp sc_next_off_check sc (List.mem_range.mpr (by omega))
  rw [beq_iff_eq] at ha
  rw [BitVec.add_assoc ctxAddr _ 0x1d0#64, ha, ← BitVec.add_assoc]

set_option maxHeartbeats 800000 in
theorem wp_root_bounces [MallocngMultiPlacement]
    (s : State) (sc : Nat)
    (unmapSeq bounces : List (BitVec 8)) (seq : BitVec 8) (Frame : SepProp)
    (_hw768 : Blk08HasWords768 mallocngFaultSvc) (_hr768 : Blk08Range768)
    (hsc : sc < 48) (hUnmL : unmapSeq.length = 32) (hBncL : bounces.length = 32)
    (hBnc : ∀ b ∈ bounces, b.toNat ≤ 150)
    (hpc : s.pc = mbase 8 + allocSlotOff_root) (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_seq_join) s
      (((maddrs.ctx + 848#64) ↦ₛ unmapSeq) ∗ ((maddrs.ctx + 880#64) ↦ₛ bounces) ∗
       ((maddrs.ctx + 912#64) ↦₈ seq) ∗ Frame)
      (fun sf P_f => ∃ bounces', bounces'.length = 32 ∧ (∀ b ∈ bounces', b.toNat ≤ 150) ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧ sf.readReg64 .x1 = BitVec.zeroExtend 64 seq ∧
        (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x5 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 →
          sf.readReg64 r = s.readReg64 r) ∧
        (38 < sc → sf.readReg64 .x5 = 0#64 ∧ sf.readReg64 .x7 = 1#64) ∧
        P_f = (((maddrs.ctx + 848#64) ↦ₛ unmapSeq) ∗ ((maddrs.ctx + 880#64) ↦ₛ bounces') ∗
               ((maddrs.ctx + 912#64) ↦₈ seq) ∗ Frame))
      (fun _ => ⌜False⌝) := by
  dsimp only [allocSlotOff_root, allocSlotOff_seq_join] at hpc ⊢
  wp_sym_steps
  wp_if hhi
  · wp_sym_steps
    refine SepWP.done rfl (by simp [hrun]) ⟨bounces, hBncL, hBnc, by simp [hrun], by simp,
      by simp [State.spAligned], psp_rfl, by simp, fun r h1 h3 h5 h7 _ _ => ?_, fun _ => ⟨by simp, by simp⟩, rfl⟩
    simp only [State.readReg64_setPC, State.readReg64_setPState,
      State.readReg64_writeReg64_ne _ _ _ _ h5, State.readReg64_writeReg64_ne _ _ _ _ h7,
      State.readReg64_writeReg64_ne _ _ _ _ h1, State.readReg64_writeReg64_ne _ _ _ _ h3]
  · obtain ⟨hsc7, hsc38, hsx⟩ := sub7_ule_31 hsc hhi
    have hidxU : sc - 7 < unmapSeq.length := by omega
    have hidxB : sc - 7 < bounces.length := by omega
    conv =>
      arg 4
      rw [split_rw_byte (maddrs.ctx + 848#64) unmapSeq hidxU,
          split_rw_byte (maddrs.ctx + 880#64) bounces hidxB]
      simp only [sepConj_assoc]
    wp_sym_steps
    wp_if hcbz
    · refine SepWP.done rfl (by simp [hrun]) ⟨bounces, hBncL, hBnc, by simp [hrun], by simp,
        by simp [State.spAligned], psp_rfl, by simp, fun r h1 h3 h5 h7 h8 h9 => ?_,
        fun h => absurd h (by omega), ?_⟩
      · simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ h7, State.readReg64_writeReg64_ne _ _ _ _ h5,
          State.readReg64_writeReg64_ne _ _ _ _ h8, State.readReg64_writeReg64_ne _ _ _ _ h9,
          State.readReg64_writeReg64_ne _ _ _ _ h3, State.readReg64_writeReg64_ne _ _ _ _ h1]
      · conv => rhs; rw [split_rw_byte (maddrs.ctx + 848#64) unmapSeq hidxU,
            split_rw_byte (maddrs.ctx + 880#64) bounces hidxB]
        simp only [sepConj_assoc]
    · wp_sym_steps
      wp_if hgt9
      · refine SepWP.done rfl (by simp [hrun]) ⟨bounces, hBncL, hBnc, by simp [hrun], by simp,
          by simp [State.spAligned], psp_rfl, by simp, fun r h1 h3 h5 h7 h8 h9 => ?_,
          fun h => absurd h (by omega), ?_⟩
        · simp only [State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ h9, State.readReg64_writeReg64_ne _ _ _ _ h7,
            State.readReg64_writeReg64_ne _ _ _ _ h5, State.readReg64_writeReg64_ne _ _ _ _ h8,
            State.readReg64_writeReg64_ne _ _ _ _ h3, State.readReg64_writeReg64_ne _ _ _ _ h1]
        · conv => rhs; rw [split_rw_byte (maddrs.ctx + 848#64) unmapSeq hidxU,
              split_rw_byte (maddrs.ctx + 880#64) bounces hidxB]
          simp only [sepConj_assoc]
      · wp_sym_steps
        let bNew : BitVec 8 :=
          if (99#64).ule (BitVec.zeroExtend 64 (bounces[sc - 7]'hidxB)) = true
          then 150#8 else (bounces[sc - 7]'hidxB) + 1#8
        refine SepWP.done rfl (by simp [hrun]) ⟨bounces.set (sc - 7) bNew, by simp [hBncL], ?_,
          by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simp,
          fun r h1 h3 h5 h7 h8 h9 => ?_, fun h => absurd h (by omega), ?_⟩
        · intro b hb
          rcases List.mem_or_eq_of_mem_set hb with hmem | rfl
          · exact hBnc b hmem
          · exact bounce_inc_le_150 _
        · simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ h8, State.readReg64_writeReg64_ne _ _ _ _ h9,
            State.readReg64_writeReg64_ne _ _ _ _ h7, State.readReg64_writeReg64_ne _ _ _ _ h5,
            State.readReg64_writeReg64_ne _ _ _ _ h3, State.readReg64_writeReg64_ne _ _ _ _ h1]
        · conv => rhs; dsimp only [bNew]; rw [split_rw_byte (maddrs.ctx + 848#64) unmapSeq hidxU,
              ← fold_rw_byte_set (maddrs.ctx + 880#64) bounces hidxB]
          simp only [sepConj_assoc]
  where
    bounce_inc_le_150_check :
        ((List.range 256).all fun n =>
          let b := BitVec.ofNat 8 n
          (if (99#64).ule (BitVec.zeroExtend 64 b) = true then 150#8 else b + 1#8).toNat ≤ 150) = true := by
      decide +kernel
    bounce_inc_le_150 (b : BitVec 8) :
        (if (99#64).ule (BitVec.zeroExtend 64 b) = true then 150#8 else b + 1#8).toNat ≤ 150 := by
      have hb : BitVec.ofNat 8 b.toNat = b := by bv_omega
      have := List.all_eq_true.mp bounce_inc_le_150_check b.toNat (List.mem_range.mpr b.isLt)
      simpa [hb] using this

private theorem cmp_sc31_slt {sc : Nat} (h32 : 32 ≤ sc) (hsc : sc < 48) :
    (31#32).slt (BitVec.setWidth 32 (BitVec.ofNat 64 sc)) = true := by
  have hw : BitVec.setWidth 32 (BitVec.ofNat 64 sc) = BitVec.ofNat 32 sc := by bv_omega
  rw [hw, BitVec.slt, decide_eq_true_eq]
  have hs1 : (31#32).toInt = 31 := rfl
  have hs2 : (BitVec.ofNat 32 sc).toInt = (sc : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sc < 2 ^ 32)]
    simp [show ¬ (2 * sc ≥ 2 ^ 32) by omega]
  rw [hs1, hs2]; omega

set_option maxHeartbeats 800000 in
theorem wp_root_seq_usage [MallocngMultiPlacement]
    (s : State) (sc : Nat)
    (usageByClass : List (BitVec 64)) (unmapSeq : List (BitVec 8)) (seq : BitVec 8)
    (Frame : SepProp)
    (hw768 : Blk08HasWords768 mallocngFaultSvc) (hr768 : Blk08Range768)
    (hsc : sc < 48) (hUseL : usageByClass.length = 48) (hUnmL : unmapSeq.length = 32)
    (hpc : s.pc = mbase 8 + allocSlotOff_seq_join) (hrun : s.status = .Running)
    (hx1 : s.readReg64 .x1 = BitVec.zeroExtend 64 seq)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_bounces_cap) s
      (((maddrs.ctx + 464#64) ↦₆₄* usageByClass) ∗ ((maddrs.ctx + 848#64) ↦ₛ unmapSeq) ∗
       ((maddrs.ctx + 912#64) ↦₈ seq) ∗ Frame)
      (fun sf P_f => ∃ unmapSeq' seq', unmapSeq'.length = 32 ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → sf.readReg64 r = s.readReg64 r) ∧
        (31 < sc → sf.readReg64 .x2 = s.readReg64 .x2) ∧
        P_f = (((maddrs.ctx + 464#64) ↦₆₄* usageByClass) ∗ ((maddrs.ctx + 848#64) ↦ₛ unmapSeq') ∗
               ((maddrs.ctx + 912#64) ↦₈ seq') ∗ Frame))
      (fun _ => ⌜False⌝) := by
  refine SepWP.seq (mid := mbase 8 + allocSlotOff_seq_after)
    (Mid := fun sj Pj => ∃ unmapSeq' seq', unmapSeq'.length = 32 ∧
      sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → sj.readReg64 r = s.readReg64 r) ∧
      Pj = (((maddrs.ctx + 464#64) ↦₆₄* usageByClass) ∗ ((maddrs.ctx + 848#64) ↦ₛ unmapSeq') ∗
            ((maddrs.ctx + 912#64) ↦₈ seq') ∗ Frame)) ?_ ?_
  · dsimp only [allocSlotOff_seq_join] at hpc
    wp_sym_steps
    wp_if heq255
    · refine SepWP.seq (mid := mbase 8 + allocSlotOff_unmap_loop)
        (Mid := fun sl Pl =>
          (sl.sp = s.sp ∧ sl.spAligned = s.spAligned ∧ PureStatePres s sl ∧
           sl.readReg64 .x1 = maddrs.ctx + 848#64 ∧ sl.readReg64 .x3 = maddrs.ctx + 880#64 ∧
           sl.readReg64 .x22 = Obj.pageOf maddrs.ctx ∧
           ∀ r, r ≠ .x1 → r ≠ .x3 → sl.readReg64 r = s.readReg64 r) ∧
          Pl = (((maddrs.ctx + 464#64) ↦₆₄* usageByClass) ∗ ((maddrs.ctx + 848#64) ↦ₛ unmapSeq) ∗
                ((maddrs.ctx + 912#64) ↦₈ seq) ∗ Frame)) ?_ ?_
      · dsimp only [allocSlotOff_unmap_loop]
        wp_sym_steps
        refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
          by simp, by simp, by simpa using hx22, fun r h1 h3 => ?_⟩, rfl⟩
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ h3, State.readReg64_writeReg64_ne _ _ _ _ h1]
      · intro sl Pl hlpc hlrun ⟨⟨hsp, hal, hpsp, hl1, hl3, hl22, hlr⟩, hPl⟩
        subst hPl
        have h848 : maddrs.ctx + BitVec.ofNat 64 (848 + (32 - 32)) = maddrs.ctx + 848#64 := rfl
        conv => arg 4; rw [show (((maddrs.ctx + 464#64) ↦₆₄* usageByClass) ∗
            ((maddrs.ctx + 848#64) ↦ₛ unmapSeq) ∗ ((maddrs.ctx + 912#64) ↦₈ seq) ∗ Frame) =
          (((maddrs.ctx + BitVec.ofNat 64 (848 + (32 - 32))) ↦ₛ unmapSeq) ∗
            ((maddrs.ctx + 912#64) ↦₈ seq) ∗ (((maddrs.ctx + 464#64) ↦₆₄* usageByClass) ∗ Frame)) by
          rw [h848]; ac_rfl]
        have hz := wp_unmap_zero_loop hw768 hr768
          32 sl unmapSeq seq (((maddrs.ctx + 464#64) ↦₆₄* usageByClass) ∗ Frame)
          (by omega) (by omega) hUnmL hlpc hlrun hl1 hl3 hl22
        refine SepWP.mono hz ?_
        intro sj Pj _ _ ⟨_, hsp2, hal2, hpsp2, hregs2, hPj⟩
        refine ⟨List.replicate 32 0#8, 1#8, by simp, hsp2.trans hsp, hal2.trans hal,
          hpsp.trans hpsp2, fun r h1 h3 => (hregs2 r h1 h3).trans (hlr r h1 h3), ?_⟩
        rw [hPj, h848]; ac_rfl
    · dsimp only [allocSlotOff_seq_after]
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun]) ⟨unmapSeq, _, hUnmL, by simp,
        by simp [State.spAligned], psp_rfl, fun r h1 h3 => ?_, rfl⟩
      simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ h1, State.readReg64_writeReg64_ne _ _ _ _ h3]
  · intro sj Pj hjpc hjrun ⟨unmapSeq', seq', hUnmL', hsp1, hal1, hpsp1, hjr, hPj⟩
    subst hPj
    have hj21 : sj.readReg64 .x21 = BitVec.ofNat 64 sc := by
      rw [hjr .x21 (by decide) (by decide), hx21]
    have hj22 : sj.readReg64 .x22 = Obj.pageOf maddrs.ctx := by
      rw [hjr .x22 (by decide) (by decide), hx22]
    dsimp only [allocSlotOff_seq_after, allocSlotOff_bounces_cap] at hjpc ⊢
    by_cases hsc31 : sc ≤ 31
    · wp_sym_steps
      wp_if hne
      · have hidx : sc + 1 < usageByClass.length := by omega
        have hoff := sc_next_off_eq maddrs.ctx hsc31
        conv => arg 4; rw [split_words64 (maddrs.ctx + 464#64) usageByClass hidx]; simp only [sepConj_assoc]
        wp_sym_steps
        refine SepWP.done rfl (by simp [hjrun]) ⟨unmapSeq', seq', hUnmL', by simp [hjrun],
          (by simp : _ = sj.sp).trans hsp1, (by simpa [State.spAligned] using hal1),
          hpsp1.trans psp_rfl, fun r h1 h2 h3 => ?_, fun h => absurd h (by omega), ?_⟩
        · rw [← hjr r h1 h3]
          simp only [State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ h2, State.readReg64_writeReg64_ne _ _ _ _ h1,
            State.readReg64_writeReg64_ne _ _ _ _ h3]
        · conv => rhs; rw [split_words64 (maddrs.ctx + 464#64) usageByClass hidx]
          simp only [sepConj_assoc]
      · refine SepWP.done rfl (by simp [hjrun]) ⟨unmapSeq', seq', hUnmL', by simp [hjrun],
          (by simp : _ = sj.sp).trans hsp1, (by simpa [State.spAligned] using hal1),
          hpsp1.trans psp_rfl, fun r h1 _ h3 => ?_, fun h => absurd h (by omega), rfl⟩
        rw [← hjr r h1 h3]
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ h1]
    · have hslt := cmp_sc31_slt (by omega) hsc
      wp_sym_steps
      wp_if hne
      · simp at hne
      · refine SepWP.done rfl (by simp [hjrun]) ⟨unmapSeq', seq', hUnmL', by simp [hjrun],
          (by simp : _ = sj.sp).trans hsp1, (by simpa [State.spAligned] using hal1),
          hpsp1.trans psp_rfl, fun r h1 _ h3 => ?_, fun _ => ?_, rfl⟩
        · rw [← hjr r h1 h3]
          simp only [State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ h1]
        · rw [← hjr .x2 (by decide) (by decide)]
          simp only [State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ (show Reg.x2 ≠ Reg.x1 by decide)]

/-! ## Root `mmap` Size and Count Selection -/

theorem align4096_bv_eq {m : Nat} (hm0 : 0 < m) (hm : m ≤ 1048576) :
    ((0#64 - BitVec.ofNat 64 m) &&& 4095#64) + BitVec.ofNat 64 m =
      BitVec.ofNat 64 (pageAlignUp m) ∧
    4096 ≤ pageAlignUp m ∧ 4096 ∣ pageAlignUp m ∧ pageAlignUp m ≤ 1048576 ∧
    (m ≤ 65536 → pageAlignUp m ≤ 65536) := by
  have hm64 : (BitVec.ofNat 64 m).toNat = m := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hsub : (0#64 - BitVec.ofNat 64 m).toNat = 2 ^ 64 - m := by
    rw [BitVec.toNat_sub, hm64]
    change (2 ^ 64 - m + 0) % (2 ^ 64) = 2 ^ 64 - m
    exact Nat.mod_eq_of_lt (by omega)
  have hand : ((0#64 - BitVec.ofNat 64 m) &&& 4095#64).toNat = (2 ^ 64 - m) % 4096 := by
    rw [BitVec.toNat_and, hsub]
    exact Nat.and_two_pow_sub_one_eq_mod _ 12
  have hlhs : (((0#64 - BitVec.ofNat 64 m) &&& 4095#64) + BitVec.ofNat 64 m).toNat =
      (2 ^ 64 - m) % 4096 + m := by
    rw [BitVec.toNat_add, hand, hm64]
    have hmod_lt : (2 ^ 64 - m) % 4096 < 4096 := Nat.mod_lt _ (by omega)
    exact Nat.mod_eq_of_lt (by omega)
  have hd1 : 4096 ∣ ((2 ^ 64 - m) % 4096 + m) := Nat.dvd_of_mod_eq_zero (by omega)
  have hd2 := pageAlignUp_dvd m
  have hle2 := pageAlignUp_le m
  have hlt2 := pageAlignUp_lt m
  obtain ⟨q1, hq1⟩ := hd1
  obtain ⟨q2, hq2⟩ := hd2
  have heq : (2 ^ 64 - m) % 4096 + m = pageAlignUp m := by omega
  refine ⟨BitVec.eq_of_toNat_eq ?_, by omega, ⟨q2, hq2⟩, by omega, fun _ => by omega⟩
  rw [hlhs, heq, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by omega : pageAlignUp m < 2 ^ 64)).symm

theorem neg_k_sub (k x c_neg : BitVec 64) (hc : c_neg + k = 0#64) :
    c_neg - x = 0#64 - (x + k) := by
  revert hc; bv_robdd

private theorem cnt_ult_33' {cnt : Nat} (hhi : cnt ≤ 32) :
    (BitVec.ofNat 64 cnt).ult 33#64 = true := by
  rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
  change cnt % (2 ^ 64) < 33
  rw [Nat.mod_eq_of_lt (by omega)]; omega

private theorem cnt32_bit30_false {cnt : Nat} (hhi : cnt ≤ 32) :
    (BitVec.ofNat 32 cnt)[30] = false := by
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
  change Nat.testBit (cnt % (2 ^ 32)) 30 = false
  rw [Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow (by omega)

private theorem lsl1_and_m32_eq {cnt : Nat} (hhi : cnt ≤ 32) :
    BitVec.setWidth 64 (BitVec.ofNat 32 cnt <<< 1) &&& 4294967295#64 = BitVec.ofNat 64 (2 * cnt) := by
  have h1 : BitVec.setWidth 64 (BitVec.ofNat 32 cnt <<< 1) = (BitVec.ofNat 64 cnt) <<< 1 := by
    have hw : BitVec.ofNat 32 cnt = BitVec.setWidth 32 (BitVec.ofNat 64 cnt) := by bv_omega
    have hlt := cnt_ult_33' hhi
    rw [hw]; revert hlt; bv_robdd
  have hsh : BitVec.ofNat 64 (2 * cnt) = (BitVec.ofNat 64 cnt) <<< 1 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    change (2 * cnt) % (2 ^ 64) = ((cnt % (2 ^ 64)) <<< 1) % (2 ^ 64)
    rw [Nat.mod_eq_of_lt (by omega : cnt < 2 ^ 64), Nat.shiftLeft_eq]
    congr 1; omega
  have hlt := cnt_ult_33' hhi
  rw [h1, hsh]; revert hlt; bv_robdd

private theorem mul_stride_cnt_eq' {cnt stride : Nat} :
    BitVec.ofNat 64 stride * BitVec.ofNat 64 cnt = BitVec.ofNat 64 (cnt * stride) := by
  rw [Nat.mul_comm]; exact (BitVec.ofNat_mul stride cnt).symm

theorem smull_stride_cnt' {cnt stride : Nat} (hcnt : cnt ≤ 32) (hstr : stride ≤ 131056) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 stride)) *
      BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 cnt)) =
    BitVec.ofNat 64 (cnt * stride) := by
  have hs : BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 stride)) =
      BitVec.ofNat 64 stride := by
    have h1 : BitVec.setWidth 32 (BitVec.ofNat 64 stride) = BitVec.ofNat 32 stride := by bv_omega
    have hlt : (BitVec.ofNat 32 stride).ult (1#32 <<< 31) = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change stride % (2 ^ 32) < 2 ^ 31
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have hse : (BitVec.ofNat 32 stride).signExtend 64 = (BitVec.ofNat 32 stride).zeroExtend 64 := by
      revert hlt; bv_robdd
    rw [h1, hse]; bv_omega
  have hc : BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 cnt)) =
      BitVec.ofNat 64 cnt := by
    have h1 : BitVec.setWidth 32 (BitVec.ofNat 64 cnt) = BitVec.ofNat 32 cnt := by bv_omega
    have hlt : (BitVec.ofNat 32 cnt).ult (1#32 <<< 31) = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change cnt % (2 ^ 32) < 2 ^ 31
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have hse : (BitVec.ofNat 32 cnt).signExtend 64 = (BitVec.ofNat 32 cnt).zeroExtend 64 := by
      revert hlt; bv_robdd
    rw [h1, hse]; bv_omega
  rw [hs, hc, Nat.mul_comm]; exact (BitVec.ofNat_mul stride cnt).symm

private theorem root_small5_check :
    ((List.range 26).all fun sc => 5 * slotStride sc + 16 ≤ 65536) = true := by decide +kernel

theorem stride_prod_plus16_le {sc cnt : Nat} (_hsc : sc < 48)
    (hprod : cnt * slotStride sc ≤ 1048575) :
    cnt * slotStride sc + 16 ≤ 1048576 := by
  have hdvd : 16 ∣ cnt * slotStride sc := by
    unfold slotStride; exact ⟨cnt * sizeClass sc, by rw [Nat.mul_left_comm]⟩
  obtain ⟨q, hq⟩ := hdvd; omega

def RootMmapParamsOk (sc cnt_f len : Nat) : Prop :=
  1 ≤ cnt_f ∧ cnt_f ≤ 32 ∧ 4096 ≤ len ∧ 4096 ∣ len ∧ len ≤ 1048576 ∧
  (sc ≤ 25 → len ≤ 65536) ∧
  (cnt_f = 1 → len - 16 ≤ slotStride sc ∨ (24 ≤ sc ∧ len = pageAlignUp (slotStride sc + 16))) ∧
  12 + cnt_f * (if cnt_f - 1 == 0 && 0 < len / 4096 then len - 16 else slotStride sc) < len

theorem rootMmapParams_of_cnt {sc cnt : Nat}
    (hm0 : 0 < cnt * slotStride sc + 16)
    (hlo : 1 ≤ cnt) (hhi : cnt ≤ 32)
    (h1M : cnt * slotStride sc + 16 ≤ 1048576)
    (h25 : sc ≤ 25 → cnt * slotStride sc + 16 ≤ 65536)
    (hc1_24 : cnt = 1 → 24 ≤ sc) :
    RootMmapParamsOk sc cnt (pageAlignUp (cnt * slotStride sc + 16)) := by
  obtain ⟨_, h4096, hdvd, hle1M, hle64⟩ := align4096_bv_eq hm0 h1M
  have hge := pageAlignUp_le (cnt * slotStride sc + 16)
  refine ⟨hlo, hhi, h4096, hdvd, hle1M, fun hs => hle64 (h25 hs), ?_, ?_⟩
  · intro hc1; subst hc1; exact Or.inr ⟨hc1_24 rfl, by simp⟩
  · by_cases hc1 : cnt = 1
    · subst hc1
      have h4 : 0 < pageAlignUp (1 * slotStride sc + 16) / 4096 := Nat.div_pos h4096 (by omega)
      simp only [Nat.sub_self, beq_self_eq_true, Bool.true_and, decide_eq_true h4, ↓reduceIte]
      omega
    · have hne0 : (cnt - 1 == 0) = false := beq_false_of_ne (by omega)
      simp [hne0]; omega

theorem root_skip_x5_ne {cnt : Nat} {x5 : BitVec 64} (hc : cnt ≤ 7) (hx5 : x5 = 0#64)
    (hne : BitVec.setWidth 32 ((if (7#32).slt (BitVec.setWidth 32 (BitVec.ofNat 64 cnt)) = true then 0#64
      else 1#64) &&& BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x5) ^^^
        4294967297#64))) = 0#32) : False := by
  subst hx5; revert hne
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      cnt = 0 ∨ cnt = 1 ∨ cnt = 2 ∨ cnt = 3 ∨ cnt = 4 ∨ cnt = 5 ∨ cnt = 6 ∨ cnt = 7 := by omega
  all_goals decide

theorem wp_root_req_round [MallocngMultiPlacement]
    (s : State) (sc req cnt_cur len_cur : Nat) (Frame : SepProp)
    (_hw768 : Blk08HasWords768 mallocngFaultSvc)
    (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    (h25_stride : sc ≤ 25 → slotStride sc + 16 ≤ 65536)
    (hCur : RootMmapParamsOk sc cnt_cur len_cur)
    (hCurLen : len_cur = pageAlignUp (cnt_cur * slotStride sc + 16))
    (hpc : s.pc = mbase 8 + allocSlotOff_req_round) (hrun : s.status = .Running)
    (hx3 : s.readReg64 .x3 = 4095#64) (hx4 : s.readReg64 .x4 = 4096#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt_cur)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 len_cur) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧
        (∀ x5, Cost.RootLenOk sc cnt_cur len (s.readReg64 .x2) x5) ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → sf.readReg64 r = s.readReg64 r) ∧
        P_f = Frame)
      (fun _ => ⌜False⌝) := by
  dsimp only [allocSlotOff_req_round, allocSlotOff_mmap_go] at hpc ⊢
  have ⟨hslo, hshi⟩ := slotStride_bounds_48 hsc
  have hreq_hi : req + 20 ≤ slotStride sc + 16 := by
    unfold nominalSlotCap slotStride at *; omega
  obtain ⟨hbv_req, h4096_req, hdvd_req, hle1M_req, hle64_req⟩ :=
    align4096_bv_eq (m := req + 20) (by omega) (by omega)
  have hge_req := pageAlignUp_le (req + 20)
  have hlt_req := pageAlignUp_lt (req + 20)
  have h4_req : 0 < pageAlignUp (req + 20) / 4096 := Nat.div_pos h4096_req (by omega)
  have hcap_req :
      12 + 1 * (if (1 : Nat) - 1 == 0 && 0 < pageAlignUp (req + 20) / 4096
        then pageAlignUp (req + 20) - 16 else slotStride sc) < pageAlignUp (req + 20) := by
    simp only [Nat.sub_self, beq_self_eq_true, Bool.true_and, decide_eq_true h4_req, ↓reduceIte]
    omega
  have hr20 : BitVec.ofNat 64 req + 20#64 = BitVec.ofNat 64 (req + 20) := (BitVec.ofNat_add req 20).symm
  have hx25_eq : ∀ (c_neg : BitVec 64), c_neg + 20#64 = 0#64 →
      ((c_neg - BitVec.ofNat 64 req) &&& 4095#64) + BitVec.ofNat 64 (req + 20) =
        BitVec.ofNat 64 (pageAlignUp (req + 20)) := fun c_neg hc => by
    rw [neg_k_sub 20#64 _ _ hc, hr20, hbv_req]
  have hx0_nat : (BitVec.ofNat 64 (slotStride sc) + 16#64).toNat = slotStride sc + 16 := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  wp_sym_steps
  wp_if hlo1
  · have hlt_str : pageAlignUp (req + 20) < slotStride sc + 16 := by
      rw [hx25_eq _ (by decide), BitVec.ult, decide_eq_true_eq, hx0_nat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hlo1
      exact hlo1
    have hOk1 : RootMmapParamsOk sc 1 (pageAlignUp (req + 20)) :=
      ⟨by omega, by omega, h4096_req, hdvd_req, hle1M_req,
       fun hs => hle64_req (by have := h25_stride hs; omega),
       fun _ => Or.inl (by omega), hcap_req⟩
    have hLen1 : ∀ x5, Cost.RootLenOk sc cnt_cur (pageAlignUp (req + 20)) (s.readReg64 .x2) x5 :=
      fun _ => Or.inl (by have := pageAlignUp_le (slotStride sc + 16); omega)
    wp_sym_steps
    refine SepWP.done rfl (by simp [hrun]) ⟨1, pageAlignUp (req + 20), hOk1, hLen1,
      by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simp, ?_, ?_, rfl⟩
    · simp; rw [neg_k_sub 20#64 _ _ (by decide), hr20, hbv_req]
    · intro r h0 h20 h25 h26
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ h20, State.readReg64_writeReg64_ne _ _ _ _ h26,
        State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h25]
  · have hge_str : slotStride sc + 16 ≤ pageAlignUp (req + 20) := by
      rw [hx25_eq _ (by decide), BitVec.ult, decide_eq_true_eq, hx0_nat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hlo1
      omega
    wp_sym_steps
    wp_if hlo2
    · have hlt16k : pageAlignUp (req + 20) < 16384 := by
        rw [hx25_eq _ (by decide)] at hlo2
        have h16k : ∀ (rhs : BitVec 64), rhs.toNat = 16384 →
            ((BitVec.ofNat 64 (pageAlignUp (req + 20))).ult rhs = true) →
            pageAlignUp (req + 20) < 16384 := fun rhs hrhs hn => by
          rw [BitVec.ult, decide_eq_true_eq, hrhs, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hn
          exact hn
        exact h16k _ (by decide) hlo2
      have hLenCur : ∀ x5, Cost.RootLenOk sc cnt_cur len_cur (s.readReg64 .x2) x5 :=
        fun _ => Or.inr ⟨hCurLen, fun _ _ h => absurd h (by omega)⟩
      refine SepWP.done rfl (by simp [hrun]) ⟨cnt_cur, len_cur, hCur, hLenCur,
        by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
        by simpa using hx20, by simpa using hx26, ?_, rfl⟩
      intro r h0 _ h25 _
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h25]
    · have hge16k : 16384 ≤ pageAlignUp (req + 20) := by
        rw [hx25_eq _ (by decide)] at hlo2
        have h16k : ∀ (rhs : BitVec 64), rhs.toNat = 16384 →
            ¬ ((BitVec.ofNat 64 (pageAlignUp (req + 20))).ult rhs = true) →
            16384 ≤ pageAlignUp (req + 20) := fun rhs hrhs hn => by
          rw [BitVec.ult, decide_eq_true_eq, hrhs, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hn
          omega
        exact h16k _ (by decide) hlo2
      have hsc24 : 24 ≤ sc := by
        apply Classical.byContradiction; intro hlt24
        have := slotStride_le_2336_of_le_24 (by omega : sc ≤ 24)
        omega
      have hAlignEq : pageAlignUp (req + 20) = pageAlignUp (slotStride sc + 16) := by
        obtain ⟨qr, hqr⟩ := hdvd_req
        obtain ⟨qs, hqs⟩ := pageAlignUp_dvd (slotStride sc + 16)
        have hle_s := pageAlignUp_le (slotStride sc + 16)
        have hlt_s := pageAlignUp_lt (slotStride sc + 16)
        omega
      have hOk2 : RootMmapParamsOk sc 1 (pageAlignUp (req + 20)) :=
        ⟨by omega, by omega, h4096_req, hdvd_req, hle1M_req,
         fun hs => hle64_req (by have := h25_stride hs; omega),
         fun _ => Or.inr ⟨hsc24, hAlignEq⟩, hcap_req⟩
      wp_sym_steps
      have hhi_cur : cnt_cur ≤ 32 := hCur.2.1
      have hw20 : BitVec.setWidth 64 (BitVec.ofNat 32 cnt_cur) = BitVec.ofNat 64 cnt_cur := by bv_omega
      have hc30 := cnt32_bit30_false hhi_cur
      have hlsl1 := lsl1_and_m32_eq hhi_cur
      by_cases hcond : (BitVec.ofNat 64 (2 * cnt_cur)).ule (s.readReg64 (Reg.gpr 2#5)) = true
      · have hLenCur : ∀ x5, Cost.RootLenOk sc cnt_cur len_cur (s.readReg64 .x2) x5 :=
          fun _ => Or.inr ⟨hCurLen, fun _ _ _ => hcond⟩
        refine SepWP.done rfl (by simp [hrun]) ⟨cnt_cur, len_cur, hCur, hLenCur,
          by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, ?_, ?_, ?_, rfl⟩
        · simp [hc30, hlsl1, hcond, hw20]
        · simp [hc30, hlsl1, hcond, hCurLen]
        · intro r h0 h20 h25 h26
          simp only [State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ h20, State.readReg64_writeReg64_ne _ _ _ _ h26,
            State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h25]
      · have hLen2 : ∀ x5, Cost.RootLenOk sc cnt_cur (pageAlignUp (req + 20)) (s.readReg64 .x2) x5 :=
          fun _ => Or.inl (Nat.le_of_eq hAlignEq)
        refine SepWP.done rfl (by simp [hrun]) ⟨1, pageAlignUp (req + 20), hOk2, hLen2,
          by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, ?_, ?_, ?_, rfl⟩
        · simp [hc30, hlsl1, hcond]
        · simp [hc30, hlsl1, hcond]; rw [neg_k_sub 20#64 _ _ (by decide), hr20, hbv_req]
        · intro r h0 h20 h25 h26
          simp only [State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ h20, State.readReg64_writeReg64_ne _ _ _ _ h26,
            State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h25]

theorem wp_root_cnt_mul [MallocngMultiPlacement]
    (s : State) (sc req c : Nat) (Frame : SepProp)
    (hw768 : Blk08HasWords768 mallocngFaultSvc)
    (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc) (hclo : 2 ≤ c) (hchi : c ≤ 5)
    (hpc : s.pc = mbase 8 + allocSlotOff_cnt_mul) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 c) (hx4 : s.readReg64 .x4 = 4096#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 c)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧
        (∀ x5, Cost.RootLenOk sc c len (s.readReg64 .x2) x5) ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 →
          sf.readReg64 r = s.readReg64 r) ∧
        P_f = Frame)
      (fun _ => ⌜False⌝) := by
  have ⟨hslo, hshi⟩ := slotStride_bounds_48 hsc
  have h5_25 : sc ≤ 25 → 5 * slotStride sc + 16 ≤ 65536 := fun hs => by
    simpa [decide_eq_true_eq] using List.all_eq_true.mp root_small5_check sc (List.mem_range.mpr (by omega))
  have hc_25 : sc ≤ 25 → c * slotStride sc + 16 ≤ 65536 := fun hs => by
    have : c * slotStride sc ≤ 5 * slotStride sc := Nat.mul_le_mul_right _ hchi
    have := h5_25 hs; omega
  have h1_25 : sc ≤ 25 → slotStride sc + 16 ≤ 65536 := fun hs => by have := h5_25 hs; omega
  have h1M : c * slotStride sc + 16 ≤ 1048576 := by
    have : c * slotStride sc ≤ 5 * 131056 := Nat.mul_le_mul hchi hshi; omega
  obtain ⟨hbv_c, _⟩ := align4096_bv_eq (m := c * slotStride sc + 16) (by omega) h1M
  have hOk_c := rootMmapParams_of_cnt (by omega) (by omega) (by omega) h1M hc_25 (by omega)
  have hadd16 : BitVec.ofNat 64 (c * slotStride sc) + 16#64 =
      BitVec.ofNat 64 (c * slotStride sc + 16) := (BitVec.ofNat_add _ 16).symm
  refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_req_round)
    (fun sj => sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧
      sj.readReg64 .x3 = 4095#64 ∧ sj.readReg64 .x4 = 4096#64 ∧
      sj.readReg64 .x20 = BitVec.ofNat 64 c ∧
      sj.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧
      sj.readReg64 .x25 = BitVec.ofNat 64 req ∧
      sj.readReg64 .x26 = BitVec.ofNat 64 (pageAlignUp (c * slotStride sc + 16)) ∧
      ∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x26 → sj.readReg64 r = s.readReg64 r) ?_ ?_
  · dsimp only [allocSlotOff_cnt_mul, allocSlotOff_req_round] at hpc ⊢
    wp_sym_steps
    refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
      by simp, by simpa using hx4, by simpa using hx20, by simpa using hx24,
      by simpa using hx25, ?_, ?_⟩, by sep_entail⟩
    · rw [mul_stride_cnt_eq']; simp; rw [neg_k_sub 16#64 _ _ (by decide), hadd16, hbv_c]
    · intro r h0 h3 h26
      simp only [State.readReg64_setPC,
        State.readReg64_writeReg64_ne _ _ _ _ h26, State.readReg64_writeReg64_ne _ _ _ _ h0,
        State.readReg64_writeReg64_ne _ _ _ _ h3]
  · intro sj hjpc hjrun ⟨hsp, hal, hpsp, hj3, hj4, hj20, hj24, hj25, hj26, hjr⟩
    have hr := wp_root_req_round sj sc req c
      (pageAlignUp (c * slotStride sc + 16)) Frame hw768 hsc hReq h1_25 hOk_c rfl
      hjpc hjrun hj3 hj4 hj20 hj24 hj25 hj26
    refine SepWP.mono hr ?_
    intro sf P_f _ _ ⟨cnt_f, len, hOk, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩
    have hx2j : sj.readReg64 .x2 = s.readReg64 .x2 := hjr _ (by decide) (by decide) (by decide)
    exact ⟨cnt_f, len, hOk, by rw [← hx2j]; exact hLen, h1, h2.trans hsp, h3.trans hal, hpsp.trans hpsp2,
      h6, h7, fun r r0 r3 r20 r25 r26 => (hregs r r0 r20 r25 r26).trans (hjr r r0 r3 r26), hPf⟩

end VerifiedLibraries.Mallocng.Proofs
