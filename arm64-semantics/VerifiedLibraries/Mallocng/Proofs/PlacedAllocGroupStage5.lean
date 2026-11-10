/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupStage4
public import VerifiedLibraries.Mallocng.Proofs.EnframeUserHelpers

/-!
# Placed `alloc_group` Nested `enframe` Path

Symbolic execution of the nested parent-slot carving (`enframe`) path in placed `alloc_slot`
(`blk08`): nested `size_to_class` call preparation (`wp_nested_call_prep`), the in-band marker
zeroing loop (`wp_nested_zero_loop`), and post-call re-entry (`wp_nested_after_self`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

arm64_proof_prelude

/-! ## Nested `size_to_class` Bit-Vector Helpers -/

private theorem nested_u_bounds {sc cnt' : Nat} (hsc : sc < 48) (hv : ValidNestedCnt sc cnt') :
    let u := cnt' * sizeClass sc
    cnt' * slotStride sc = 16 * u ∧ 2 ≤ u ∧ u ≤ 127 := by
  obtain ⟨hlo, _hhi, hspan, _⟩ := hv
  have hscB := (sizeClass_bounds hsc).1
  have hmul : cnt' * slotStride sc = 16 * (cnt' * sizeClass sc) := by
    unfold slotStride; exact Nat.mul_left_comm cnt' 16 (sizeClass sc)
  have hge2 : 2 ≤ cnt' * sizeClass sc := by
    have : 2 * 1 ≤ cnt' * sizeClass sc := Nat.mul_le_mul hlo hscB
    omega
  refine ⟨hmul, hge2, ?_⟩
  omega

private def checkNestedSizeToClassGrid : Bool :=
  (List.range 128).all fun u =>
    if 10 ≤ u then
      let x0 : BitVec 64 := BitVec.ofNat 64 (u + 1)
      let w0 : BitVec 32 := x0.setWidth 32
      let w5 : BitVec 32 := 0x076be629#32
      let w2a := (w0 >>> 2) ||| (w0 >>> 1)
      let w2b := w2a ||| (w2a >>> 2)
      let w2c := w2b ||| (w2b >>> 4)
      let w2d := w2c ||| (w2c >>> 8)
      let w2e := w2d ||| (w2d >>> 16)
      let w6 := w2e + 1#32
      let p2 := w6 &&& ~~~w2e
      let idxBv := (p2 * w5) >>> 27
      let idx := sizeToClassHashIdx u
      let b8 := debruijn32Table.getD idx 0#8
      let wBase := (BitVec.zeroExtend 32 b8 - 1#32) <<< 2
      let wMid := wBase + 1#32
      let wHi := wBase + 2#32
      let baseSc := (b8.toNat - 1) * 4
      let scMid16 := BitVec.ofNat 16 (sizeClass (baseSc + 1))
      let wSc1 := if (BitVec.zeroExtend 64 scMid16).ult x0 then wHi else wBase
      let sc1 := if u + 1 > sizeClass (baseSc + 1) then baseSc + 2 else baseSc
      let sc1_16 := BitVec.ofNat 16 (sizeClass sc1)
      let wSc2 := if (BitVec.zeroExtend 64 sc1_16).ult x0 then wSc1 + 1#32 else wSc1
      (idx < 32) &&
      (baseSc + 1 < 48) &&
      (sc1 < 48) &&
      (sizeToClassUnits u < 48) &&
      (idxBv == BitVec.ofNat 32 idx) &&
      (BitVec.zeroExtend 64 idxBv == BitVec.ofNat 64 idx) &&
      ((BitVec.signExtend 64 wMid) <<< 1 == BitVec.ofNat 64 (2 * (baseSc + 1))) &&
      ((BitVec.signExtend 64 wSc1) <<< 1 == BitVec.ofNat 64 (2 * sc1)) &&
      (wSc2 == BitVec.ofNat 32 (sizeToClassUnits u))
    else true

private theorem checkNestedSizeToClassGrid_true : checkNestedSizeToClassGrid = true := by
  decide +kernel

private theorem nested_sizeToClass_bv {u : Nat} (hu10 : 10 ≤ u) (hu127 : u ≤ 127) :
    let x0 : BitVec 64 := BitVec.ofNat 64 (u + 1)
    let w0 : BitVec 32 := x0.setWidth 32
    let w5 : BitVec 32 := 0x076be629#32
    let w2a := (w0 >>> 2) ||| (w0 >>> 1)
    let w2b := w2a ||| (w2a >>> 2)
    let w2c := w2b ||| (w2b >>> 4)
    let w2d := w2c ||| (w2c >>> 8)
    let w2e := w2d ||| (w2d >>> 16)
    let w6 := w2e + 1#32
    let p2 := w6 &&& ~~~w2e
    let idxBv := (p2 * w5) >>> 27
    let idx := sizeToClassHashIdx u
    let b8 := debruijn32Table.getD idx 0#8
    let wBase := (BitVec.zeroExtend 32 b8 - 1#32) <<< 2
    let wMid := wBase + 1#32
    let wHi := wBase + 2#32
    let baseSc := (b8.toNat - 1) * 4
    let scMid16 := BitVec.ofNat 16 (sizeClass (baseSc + 1))
    let wSc1 := if (BitVec.zeroExtend 64 scMid16).ult x0 then wHi else wBase
    let sc1 := if u + 1 > sizeClass (baseSc + 1) then baseSc + 2 else baseSc
    let sc1_16 := BitVec.ofNat 16 (sizeClass sc1)
    let wSc2 := if (BitVec.zeroExtend 64 sc1_16).ult x0 then wSc1 + 1#32 else wSc1
    idx < 32 ∧ baseSc + 1 < 48 ∧ sc1 < 48 ∧ sizeToClassUnits u < 48 ∧
    idxBv = BitVec.ofNat 32 idx ∧
    BitVec.zeroExtend 64 idxBv = BitVec.ofNat 64 idx ∧
    (BitVec.signExtend 64 wMid) <<< 1 = BitVec.ofNat 64 (2 * (baseSc + 1)) ∧
    (BitVec.signExtend 64 wSc1) <<< 1 = BitVec.ofNat 64 (2 * sc1) ∧
    wSc2 = BitVec.ofNat 32 (sizeToClassUnits u) := by
  have h := List.all_eq_true.mp checkNestedSizeToClassGrid_true u (List.mem_range.mpr (by omega))
  simp only [hu10, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2,
    h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem split_debruijn_ro (dbAddr : BitVec 64) {idx : Nat} (hidx : idx < 32) (R : SepProp) :
    ∃ Rest : SepProp, ((dbAddr ↦ᵣ debruijn32Table) ∗ R) =
      (((dbAddr + BitVec.ofNat 64 idx) ↦₈ᵣ debruijn32Table.getD idx 0#8) ∗ Rest ∗ R) := by
  have hlen : idx + 1 ≤ debruijn32Table.length := by rw [debruijn32Table_length]; omega
  refine ⟨(dbAddr ↦ᵣ debruijn32Table.take idx) ∗
    ((dbAddr + BitVec.ofNat 64 (idx + 1)) ↦ᵣ debruijn32Table.drop (idx + 1)), ?_⟩
  rw [pointsToBytesRO_split3 dbAddr debruijn32Table idx 1 hlen,
    pointsToBytesRO_take1_eq_pointsTo8RO _ _ _ hlen]
  simp only [sepConj_assoc]

/-! ## In-Band Marker Zeroing Loop -/

private theorem split_slot_byte (base : BitVec 64) (bs : List (BitVec 8)) {idx : Nat}
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

private theorem fold_slot_byte_set (base : BitVec 64) (bs : List (BitVec 8)) {idx : Nat}
    (hidx : idx < bs.length) (v : BitVec 8) :
    (((base + BitVec.ofNat 64 idx) ↦₈ v) ∗
     (base ↦ₛ bs.take idx) ∗
     ((base + BitVec.ofNat 64 (idx + 1)) ↦ₛ bs.drop (idx + 1))) =
      (base ↦ₛ bs.set idx v) := by
  have hlen : idx < (bs.set idx v).length := by simp [hidx]
  rw [split_slot_byte base (bs.set idx v) hlen]
  simp [List.getElem_set_self, List.take_set_of_le (Nat.le_refl idx),
    List.drop_set_of_lt (Nat.lt_succ_self idx)]

theorem wp_nested_zero_loop [MallocngMultiPlacement]
    (rem k cnt' stride baseOff : Nat) (s : State) (slotBase mb : BitVec 64)
    (bs : List (BitVec 8)) (Frame : SepProp)
    (hw768 : Blk08HasWords768 mallocngFaultSvc)
    (hrem_pos0 : 1 ≤ rem) (hrem : k + rem = cnt' + 1)
    (hcnt_lo : 2 ≤ cnt') (hcnt_hi : cnt' ≤ 32)
    (hstride_pos : 16 ≤ stride) (hstride_hi : stride ≤ 2032)
    (hbase_eq : slotBase + BitVec.ofNat 64 baseOff = mb + 12#64)
    (hfit : baseOff + cnt' * stride < bs.length)
    (hbs_hi : bs.length ≤ 131072)
    (hpc : s.pc = mbase 8 + allocSlotOff_zero_loop) (hrun : s.status = .Running)
    (hx1 : s.readReg64 .x1 = mb + BitVec.ofNat 64 (12 + k * stride))
    (hw2 : s.readReg32 .x2 = BitVec.ofNat 32 k)
    (hw3 : s.readReg32 .x3 = BitVec.ofNat 32 (cnt' + 1))
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt')
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 stride) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_pub_add) s
      ((slotBase ↦ₛ bs) ∗ Frame)
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg64 .x1 = BitVec.ofNat 64 (cnt' - 1) ∧
        sf.readReg64 .x2 = BitVec.ofNat 64 (cnt' - 1) ∧
        (∀ r, r ≠ .x1 → r ≠ .x2 → sf.readReg64 r = s.readReg64 r) ∧
        ∃ bs' : List (BitVec 8),
          bs'.length = bs.length ∧
          (∀ j, k ≤ j → j ≤ cnt' → bs'.getD (baseOff + j * stride) 0#8 = 0#8) ∧
          (∀ idx, (∀ j, k ≤ j → j ≤ cnt' → idx ≠ baseOff + j * stride) →
            bs'.getD idx 0#8 = bs.getD idx 0#8) ∧
          (P_f ⊢ (slotBase ↦ₛ bs') ∗ Frame))
      (fun _ => ⌜False⌝) := by
  induction rem generalizing k s bs with
  | zero => omega
  | succ rem' ih =>
    have hk_le : k ≤ cnt' := by omega
    have hmul_le : k * stride ≤ cnt' * stride := Nat.mul_le_mul_right stride hk_le
    have hoff_lt : baseOff + k * stride < bs.length := by omega
    have hSlotAddr : slotBase + BitVec.ofNat 64 (baseOff + k * stride) =
        mb + BitVec.ofNat 64 (12 + k * stride) := by
      have h1 : mb + BitVec.ofNat 64 (12 + k * stride) =
          (mb + 12#64) + BitVec.ofNat 64 (k * stride) := by bv_omega
      rw [h1, ← hbase_eq]
      bv_omega
    conv => arg 4; rw [split_slot_byte slotBase bs hoff_lt, hSlotAddr]
    simp only [sepConj_assoc]
    dsimp only [allocSlotOff_zero_loop, allocSlotOff_pub_add] at hpc ⊢
    rcases Nat.eq_or_lt_of_le (by omega : 0 ≤ rem') with hrem0 | hrem_pos
    · subst hrem0
      have hk_eq : k = cnt' := by omega
      subst hk_eq
      have hcond :
          (BitVec.setWidth 32 (s.readReg64 (Reg.gpr 2#5)) + 1#32 !=
            BitVec.setWidth 32 (s.readReg64 (Reg.gpr 3#5))) = false := by
        change ((s.readReg32 .x2 + 1#32) != s.readReg32 .x3) = false
        rw [hw2, hw3]
        have : BitVec.ofNat 32 k + 1#32 = BitVec.ofNat 32 (k + 1) := by bv_omega
        simp [this]
      wp_sym_steps
      conv => arg 4; rw [← hSlotAddr]
      have hfoldF : (((slotBase + BitVec.ofNat 64 (baseOff + k * stride)) ↦₈ 0#8) ∗
          (slotBase ↦ₛ bs.take (baseOff + k * stride)) ∗
          ((slotBase + BitVec.ofNat 64 (baseOff + k * stride + 1)) ↦ₛ
            bs.drop (baseOff + k * stride + 1)) ∗ Frame) =
          ((slotBase ↦ₛ bs.set (baseOff + k * stride) 0#8) ∗ Frame) := by
        simpa only [sepConj_assoc] using congrArg (· ∗ Frame) (fold_slot_byte_set slotBase bs hoff_lt 0#8)
      have hw20_sub :
          BitVec.setWidth 64 (BitVec.ofNat 32 k - 1#32) = BitVec.ofNat 64 (k - 1) := by
        apply BitVec.eq_of_toNat_eq
        have hsub : (BitVec.ofNat 32 k - 1#32).toNat = k - 1 := by bv_omega
        simp [hsub, Nat.mod_eq_of_lt (by omega : k - 1 < 2 ^ 64)]
      refine SepWP.done rfl (by simp [hrun])
        ⟨by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, ?_, ?_, ?_,
         bs.set (baseOff + k * stride) 0#8, List.length_set, ?_, ?_, ?_⟩
      · simpa using hw20_sub
      · simpa using hw20_sub
      · intro r hr1 hr2
        simp only [State.readReg64_setMem, State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ hr1, State.readReg64_writeReg64_ne _ _ _ _ hr2]
      · intro j hkj hjk
        have hjeq : j = k := by omega
        subst hjeq
        simp [List.getD, List.getElem?_set_self hoff_lt]
      · intro idx hne
        have hne0 : baseOff + k * stride ≠ idx := (hne k (Nat.le_refl k) (Nat.le_refl k)).symm
        simp [List.getD, List.getElem?_set_ne hne0]
      · simp only [hfoldF]
        sep_entail
    · have hk_lt : k < cnt' := by omega
      have hcond :
          (BitVec.setWidth 32 (s.readReg64 (Reg.gpr 2#5)) + 1#32 !=
            BitVec.setWidth 32 (s.readReg64 (Reg.gpr 3#5))) = true := by
        change ((s.readReg32 .x2 + 1#32) != s.readReg32 .x3) = true
        rw [hw2, hw3, bne_iff_ne]
        intro heq
        have ht := congrArg BitVec.toNat heq
        have h1 : (BitVec.ofNat 32 k + 1#32).toNat = k + 1 := by bv_omega
        have h2 : (BitVec.ofNat 32 (cnt' + 1)).toNat = cnt' + 1 := by bv_omega
        omega
      refine SepWP.seq (mid := mbase 8 + allocSlotOff_zero_loop)
        (Mid := fun s1 P1 =>
          (s1.sp = s.sp ∧ s1.spAligned = s.spAligned ∧ PureStatePres s s1 ∧
            s1.readReg64 .x1 = mb + BitVec.ofNat 64 (12 + (k + 1) * stride) ∧
            s1.readReg32 .x2 = BitVec.ofNat 32 (k + 1) ∧
            s1.readReg32 .x3 = BitVec.ofNat 32 (cnt' + 1) ∧
            s1.readReg64 .x20 = BitVec.ofNat 64 cnt' ∧
            s1.readReg64 .x24 = BitVec.ofNat 64 stride ∧
            (∀ r, r ≠ .x1 → r ≠ .x2 → s1.readReg64 r = s.readReg64 r)) ∧
          P1 = ((slotBase ↦ₛ bs.set (baseOff + k * stride) 0#8) ∗ Frame)) ?_ ?_
      · dsimp only [allocSlotOff_zero_loop]
        wp_sym_steps
        conv => arg 4; rw [← hSlotAddr]
        have hfoldF : (((slotBase + BitVec.ofNat 64 (baseOff + k * stride)) ↦₈ 0#8) ∗
            (slotBase ↦ₛ bs.take (baseOff + k * stride)) ∗
            ((slotBase + BitVec.ofNat 64 (baseOff + k * stride + 1)) ↦ₛ
              bs.drop (baseOff + k * stride + 1)) ∗ Frame) =
            ((slotBase ↦ₛ bs.set (baseOff + k * stride) 0#8) ∗ Frame) := by
          simpa only [sepConj_assoc] using congrArg (· ∗ Frame) (fold_slot_byte_set slotBase bs hoff_lt 0#8)
        refine SepWP.done rfl (by simp [hrun])
          ⟨⟨by simp, by simp [State.spAligned], psp_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · simp; have hmul1 : (k + 1) * stride = k * stride + stride := Nat.succ_mul k stride
          rw [hmul1]; bv_omega
        · simp [State.readReg32]
          change s.readReg32 .x2 + 1#32 = _
          rw [hw2]; bv_omega
        · simp [State.readReg32]; exact hw3
        · simp [hx20]
        · simp [hx24]
        · intro r hr1 hr2
          simp only [State.readReg64_setMem, State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ hr1, State.readReg64_writeReg64_ne _ _ _ _ hr2]
        · simp only [hfoldF]
      · intro s1 P1 hpc1 hrun1 ⟨⟨hsp1, hal1, hpsp1, hx1_1, hw2_1, hw3_1, hx20_1, hx24_1, hregs1⟩, hP1⟩
        subst hP1
        have hstep := ih (k + 1) s1 (bs.set (baseOff + k * stride) 0#8)
          (by omega) (by omega) (by rw [List.length_set]; exact hfit)
          (by rw [List.length_set]; exact hbs_hi)
          hpc1 hrun1 hx1_1 hw2_1 hw3_1 hx20_1 hx24_1
        dsimp only [allocSlotOff_pub_add] at hstep
        refine SepWP.mono hstep ?_
        rintro sf P_f _ _ ⟨hsf_run, hsf_sp, hsf_al, hpsp2, hsf1, hsf2, hsf_regs,
          bs', hbs'_len, hbs'_zero, hbs'_other, hPf⟩
        refine ⟨hsf_run, hsf_sp.trans hsp1, hsf_al.trans hal1, hpsp1.trans hpsp2,
          hsf1, hsf2, fun r hr1 hr2 => (hsf_regs r hr1 hr2).trans (hregs1 r hr1 hr2),
          bs', by rwa [List.length_set] at hbs'_len, ?_, ?_, hPf⟩
        · intro j hkj hjk
          rcases Nat.eq_or_lt_of_le hkj with hkj_eq | hgt
          · subst hkj_eq
            rw [hbs'_other (baseOff + k * stride)]
            · simp [List.getD, List.getElem?_set_self hoff_lt]
            · intro j' hj1 _ hEq
              have : k * stride < j' * stride :=
                (Nat.mul_lt_mul_right (by omega : 0 < stride)).mpr hj1
              omega
          · exact hbs'_zero j hgt hjk
        · intro idx hne
          rw [hbs'_other idx (fun j hj1 hj2 => hne j (by omega) hj2)]
          have hne0 : baseOff + k * stride ≠ idx := (hne k (Nat.le_refl k) hk_le).symm
          simp [List.getD, List.getElem?_set_ne hne0]

/-! ## Nested `size_to_class` Call Preparation -/

abbrev allocSlotOff_nested_sc1 : BitVec 64 := words_insn_off% blk08Words 0x7879d842#32

private theorem cinc_hi_eq (a b : BitVec 64) (w : BitVec 32) :
    BitVec.setWidth 32
      (if a.ule b = true then BitVec.setWidth 64 w
       else BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 w + 1#64))) =
    (if b.ult a = true then w + 1#32 else w) := by
  bv_robdd

private theorem lsl32_2 (v : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 v <<< 2) = v <<< 2 := by
  bv_bits

private theorem lsr32_2 (v : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 v >>> 2) = v >>> 2 := by
  bv_bits

private theorem lsr32_27 (v : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 v >>> 27) = v >>> 27 := by
  bv_bits

private theorem zext32_ofNat_lt32 {n : Nat} (h : n < 32) :
    BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
  bv_omega

theorem wp_nested_call_prep [MallocngMultiPlacement]
    (s : State) (sc cnt' : Nat) (Frame : SepProp)
    (hw768 : Blk08HasWords768 mallocngFaultSvc) (hr768 : Blk08Range768)
    (hsc : sc < 48) (hv : ValidNestedCnt sc cnt')
    (hpc : s.pc = mbase 8 + allocSlotOff_nested) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc))
    (hx26 : s.readReg64 .x26 = Obj.pageOf maddrs.sizeClasses) :
    let u := cnt' * sizeClass sc
    let pSc := sizeToClassUnits u
    let needed := cnt' * slotStride sc + 12
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8) s
      ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
       (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ Frame)
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg32 .x0 = BitVec.ofNat 32 pSc ∧
        sf.readReg64 .x1 = BitVec.ofNat 64 needed ∧
        sf.readReg32 .x25 = BitVec.ofNat 32 pSc ∧
        sf.readReg64 .lr = mbase 8 + allocSlotOff_after_self ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x6 →
          r ≠ .x25 → r ≠ .x30 → sf.readReg64 r = s.readReg64 r) ∧
        (P_f ⊢ (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
          (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ Frame))
      (fun _ => ⌜False⌝) := by
  intro u pSc needed
  have ⟨hmul, hu_lo, hu_hi⟩ := nested_u_bounds hsc hv
  have hx0_u : s.readReg64 .x0 = BitVec.ofNat 64 (16 * (cnt' * sizeClass sc)) := by rw [hx0, hmul]
  have hx25_u :
      BitVec.ofNat 64 (16 * (cnt' * sizeClass sc)) >>> 4 = BitVec.ofNat 64 (cnt' * sizeClass sc) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 16 * (cnt' * sizeClass sc) < 2 ^ 64),
        Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : cnt' * sizeClass sc < 2 ^ 64)]
    omega
  dsimp only [allocSlotOff_nested, allocSlotOff_after_self] at hpc ⊢
  by_cases hu9 : u ≤ 9
  · have hbr : (BitVec.ofNat 64 (16 * (cnt' * sizeClass sc))).ule 144#64 = true := by
      rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : 16 * (cnt' * sizeClass sc) < 2 ^ 64)]
      change 16 * (cnt' * sizeClass sc) ≤ 144; omega
    have hpSc_eq : pSc = cnt' * sizeClass sc := by simp [pSc, sizeToClassUnits, hu9, u]
    wp_sym_steps
    refine SepWP.done (by simp [mbase]) (by simp [hrun])
      ⟨by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, ?_, ?_, ?_,
       by simp [mbase], ?_, by sep_entail⟩
    · simp [State.readReg32, hpSc_eq]
    · simp [needed, hmul]; bv_omega
    · simp [State.readReg32, hpSc_eq]
    · intro r hr0 hr1 _ _ _ _ _ hr25 hr30
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ hr30,
        State.readReg64_writeReg64_ne _ _ _ _ hr0,
        State.readReg64_writeReg64_ne _ _ _ _ hr25,
        State.readReg64_writeReg64_ne _ _ _ _ hr1]
  · have hu10 : 10 ≤ cnt' * sizeClass sc := by omega
    have hbr : (BitVec.ofNat 64 (16 * (cnt' * sizeClass sc))).ule 144#64 = false := by
      rw [BitVec.ule, decide_eq_false_iff_not, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : 16 * (cnt' * sizeClass sc) < 2 ^ 64)]
      change ¬ (16 * (cnt' * sizeClass sc) ≤ 144); omega
    obtain ⟨hidx_lt, hbaseMid_lt, hsc1_lt, _hpSc_lt, _hidxBv, hidx64, hmidOff, hsc1Off, hwSc2⟩ :=
      nested_sizeToClass_bv hu10 hu_hi
    have hx0_add1 : BitVec.ofNat 64 (cnt' * sizeClass sc) + 1#64 =
        BitVec.ofNat 64 (cnt' * sizeClass sc + 1) :=
      (BitVec.ofNat_add (cnt' * sizeClass sc) 1).symm
    have hneed_add : BitVec.ofNat 64 (16 * (cnt' * sizeClass sc)) + 12#64 =
        BitVec.ofNat 64 needed := by
      simp only [needed, hmul]; exact (BitVec.ofNat_add (16 * (cnt' * sizeClass sc)) 12).symm
    let idx := sizeToClassHashIdx (cnt' * sizeClass sc)
    let b8 := debruijn32Table.getD idx 0#8
    let baseSc := (b8.toNat - 1) * 4
    let sc1 := if cnt' * sizeClass sc + 1 > sizeClass (baseSc + 1) then baseSc + 2 else baseSc
    refine SepWP.join_same (pc_join := mbase 8 + (words_insn_off% blk08Words 0x38624899#32))
      (fun s1 => s1.sp = s.sp ∧ s1.spAligned = s.spAligned ∧ PureStatePres s s1 ∧
        s1.readReg64 .x0 = BitVec.ofNat 64 (cnt' * sizeClass sc + 1) ∧
        s1.readReg64 .x1 = BitVec.ofNat 64 needed ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 idx ∧
        s1.readReg64 .x3 = maddrs.sizeClasses ∧
        s1.readReg64 .x4 = maddrs.debruijnFree ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x6 →
          r ≠ .x25 → s1.readReg64 r = s.readReg64 r)) ?_ ?_
    · wp_sym_steps
      refine SepWP.done (by simp [mbase]) (by simp [hrun])
        ⟨⟨by simp, by simp [State.spAligned], psp_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, by sep_entail⟩
      · simp [hx0_add1]
      · simp
      · refine Eq.trans ?_ hidx64
        simp [hx0_add1, lsr32_2, lsr32_27]
      · simp
      · simp
      · intro r hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr25
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ hr0, State.readReg64_writeReg64_ne _ _ _ _ hr1,
          State.readReg64_writeReg64_ne _ _ _ _ hr2, State.readReg64_writeReg64_ne _ _ _ _ hr3,
          State.readReg64_writeReg64_ne _ _ _ _ hr4, State.readReg64_writeReg64_ne _ _ _ _ hr5,
          State.readReg64_writeReg64_ne _ _ _ _ hr6, State.readReg64_writeReg64_ne _ _ _ _ hr25]
    · intro s1 hpc1 hrun1 ⟨hsp1, hal1, hpsp1, hs1_0, hs1_1, hs1_2, hs1_3, hs1_4, hs1_regs⟩
      have hidx_zext := zext32_ofNat_lt32 hidx_lt
      have hDbAddr : maddrs.debruijnFree + BitVec.ofNat 64 idx =
          maddrs.debruijnFree + BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 idx)) := by
        change _ = maddrs.debruijnFree + BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 idx))
        rw [hidx_zext]
      have hMidAddr : maddrs.sizeClasses + BitVec.ofNat 64 (2 * (baseSc + 1)) =
          maddrs.sizeClasses + BitVec.signExtend 64
            (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.zeroExtend 32 b8 - 1#32) <<< 2) + 1#32) <<< 1 := by
        rw [lsl32_2, hmidOff]
      obtain ⟨RestDb, hSplitDb⟩ := split_debruijn_ro maddrs.debruijnFree hidx_lt Frame
      obtain ⟨RestScMid, hSplitScMid⟩ := split_sizeClass_ro maddrs.sizeClasses hbaseMid_lt
        (((maddrs.debruijnFree + BitVec.ofNat 64 idx) ↦₈ᵣ b8) ∗ RestDb ∗ Frame)
      conv =>
        arg 4
        rw [hSplitDb, hSplitScMid, hDbAddr, hMidAddr]
      refine SepWP.seq (mid := mbase 8 + allocSlotOff_nested_sc1)
        (Mid := fun sm Pm =>
          (sm.sp = s.sp ∧ sm.spAligned = s.spAligned ∧ PureStatePres s sm ∧
            sm.readReg64 .x0 = BitVec.ofNat 64 (cnt' * sizeClass sc + 1) ∧
            sm.readReg64 .x1 = BitVec.ofNat 64 needed ∧
            sm.readReg64 .x2 = maddrs.sizeClasses ∧
            sm.readReg32 .x25 =
              (let wBase := (BitVec.zeroExtend 32 b8 - 1#32) <<< 2
               if (BitVec.zeroExtend 64 (BitVec.ofNat 16 (sizeClass (baseSc + 1)))).ult
                    (BitVec.ofNat 64 (cnt' * sizeClass sc + 1))
               then wBase + 2#32 else wBase) ∧
            (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x6 →
              r ≠ .x25 → sm.readReg64 r = s.readReg64 r)) ∧
          Pm = ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
            (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ Frame)) ?_ ?_
      · dsimp only [allocSlotOff_nested_sc1]
        wp_sym_steps
        conv => arg 4; rw [← hMidAddr, ← hDbAddr]
        refine SepWP.done rfl (by simp [hrun1])
          ⟨⟨by simp [hsp1], by simpa [State.spAligned] using hal1, hpsp1, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · simp [hs1_0]
        · simp [hs1_1]
        · simp
        · simp [State.readReg32]; rfl
        · intro r hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr25
          simp only [State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ hr2, State.readReg64_writeReg64_ne _ _ _ _ hr3,
            State.readReg64_writeReg64_ne _ _ _ _ hr4, State.readReg64_writeReg64_ne _ _ _ _ hr5,
            State.readReg64_writeReg64_ne _ _ _ _ hr25]
          exact hs1_regs r hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr25
        · simpa only [sepConj_assoc] using (hSplitScMid.symm.trans (by rw [← hSplitDb]))
      · intro sm Pm hpcm hrunm ⟨⟨hspm, halm, hpspm, hm0, hm1, hm2, hm25, hmregs⟩, hPm⟩
        subst hPm
        have hSc1Addr : maddrs.sizeClasses + BitVec.ofNat 64 (2 * sc1) =
            maddrs.sizeClasses + BitVec.signExtend 64 (BitVec.setWidth 32 (sm.readReg64 .x25)) <<< 1 := by
          change _ = maddrs.sizeClasses + BitVec.signExtend 64 (sm.readReg32 .x25) <<< 1
          rw [hm25, hsc1Off]
        obtain ⟨RestSc1, hSplitSc1⟩ := split_sizeClass_ro maddrs.sizeClasses hsc1_lt
          ((maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ Frame)
        conv => arg 4; rw [hSplitSc1, hSc1Addr]
        dsimp only [allocSlotOff_nested_sc1] at hpcm
        wp_sym_steps
        conv => arg 4; rw [← hSc1Addr]
        refine SepWP.done (by simp [mbase]) (by simp [hrunm])
          ⟨by simp [hrunm], hspm, by simpa [State.spAligned] using halm, hpspm,
           ?_, ?_, ?_, by simp [mbase], ?_, ?_⟩
        · change BitVec.setWidth 32
              (if (BitVec.ofNat 64 (cnt' * sizeClass sc + 1)).ule
                    (BitVec.zeroExtend 64 (BitVec.ofNat 16 (sizeClass sc1))) = true
               then BitVec.setWidth 64 (sm.readReg32 .x25)
               else BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (sm.readReg32 .x25) + 1#64))) =
              BitVec.ofNat 32 pSc
          rw [cinc_hi_eq, hm25]; exact hwSc2
        · simp [hm1]
        · change BitVec.setWidth 32
              (if (BitVec.ofNat 64 (cnt' * sizeClass sc + 1)).ule
                    (BitVec.zeroExtend 64 (BitVec.ofNat 16 (sizeClass sc1))) = true
               then BitVec.setWidth 64 (sm.readReg32 .x25)
               else BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (sm.readReg32 .x25) + 1#64))) =
              BitVec.ofNat 32 pSc
          rw [cinc_hi_eq, hm25]; exact hwSc2
        · intro r hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr25 hr30
          simp only [State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ hr30, State.readReg64_writeReg64_ne _ _ _ _ hr0,
            State.readReg64_writeReg64_ne _ _ _ _ hr25, State.readReg64_writeReg64_ne _ _ _ _ hr2]
          exact hmregs r hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr25
        · have hRew : (((maddrs.sizeClasses + BitVec.ofNat 64 (2 * sc1)) ↦₁₆ᵣ
                BitVec.ofNat 16 (sizeClass sc1)) ∗ RestSc1 ∗
              (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ Frame) =
              ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
                (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ Frame) := by
            simpa only [sepConj_assoc] using hSplitSc1.symm
          rw [hRew]; sep_entail

end VerifiedLibraries.Mallocng.Proofs
