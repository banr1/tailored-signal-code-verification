/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbLoop
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Loop Proofs for `<PolyDecoder>::into_pb`

Threads `VmPreserved` and `AllocCallPreserved` through the inner `Pt` serialization loop
(`+204..+300`) and outer-iteration finish (`+300 → +148 / +328`) on Block `377`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbLoopBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkPC_377 blkPl_377)
open CryptoVerification.RustHeap (RustAlloc arrayAt arrayAt_cons arrayAt_nil vecU8 vecU8Buf)
open CryptoVerification.LibsignalSpqrV1 (Pt)
open CryptoVerification.SpqrV1.Poly (gf16At ptAt)
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts (align_pre)
open CryptoVerification.SpqrV1.Poly.DecoderPb
  (bne_one_of_pos fp64_sub_24 fp64_sub_24_int fp64_sub_16 fp64_sub_16_int
   fp64_sub_8 fp64_sub_8_int length_pt_serialize madd_24_eq memRegion_24_cons
   memRegion_four_cons ofNat_add_one ofNat_beq_16_false ofNat_ne_16
   ofNat_succ_sub_one off_24_succ off_add_four pointsTo32_rev_orr_eq_pt_serialize
   rem_bytes_not_ule_three serializePtList
   serializePtList_cons sp_add_40_add_8 srcCur_add_2_sub_2
   srcCur_add_2_sub_2_int srcCur_add_4_add_2 vecU8_slot_intro)
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  fp64_sub_24 fp64_sub_16 fp64_sub_8
  fp64_sub_24_int fp64_sub_16_int fp64_sub_8_int
  sp_add_40_add_8 srcCur_add_2_sub_2 srcCur_add_2_sub_2_int
  ofNat_add_one madd_24_eq off_24_succ

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem sepWP_swap_vm {prog : Program} {tgt : BitVec 64} {s : State}
    {Pre : SepProp} {Ent : SepProp → Prop} {Rest : State → Prop}
    (h : SepWP prog tgt s Pre (fun sm Pm => VmPreserved s sm ∧ Ent Pm ∧ Rest sm)) :
    SepWP prog tgt s Pre (fun sm Pm => Ent Pm ∧ VmPreserved s sm ∧ Rest sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hvm, hent, hr⟩ => ⟨hent, hvm, hr⟩

private theorem align_pre_vm {prog : Program} {pc : BitVec 64} {s : State}
    {P P' : SepProp} {tp : BitVec 64} {Q : State → Prop}
    (heq : P = P')
    (h : SepWP prog pc s P' (fun sm Pm => sm.tpidrEl0 = tp ∧ (Pm ⊢ P') ∧ Q sm)) :
    SepWP prog pc s P (fun sm Pm => sm.tpidrEl0 = tp ∧ (Pm ⊢ P') ∧ Q sm) := by
  rw [heq]; exact h

/-! ## Relocatable (`[LibsignalPlacement]`) Budget/VM-Preserving Proofs for Block `377` -/

/-- Placed inner serialization loop for `Pt` elements (`+204 -> +300`), preserving `VmPreserved`
    and `AllocCallPreserved`. -/
theorem pts_inner_loop_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s0 : State) (fsp dstPtr : BitVec 64)
    (total : Nat) (hmax : 4 * total < 2 ^ 63)
    (rem : List Pt) (hne : rem ≠ [])
    (done : Nat) (htot : done + rem.length = total)
    (s : State) (srcCur lenVal : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_377).base + 204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64)
    (hx0 : s.readReg64 .x0 = dstPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (4 * done))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rem.length)
    (hx21 : s.readReg64 .x21 = srcCur + 2#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      ((blkPl_377).base + 300#64)
      s
      (arrayAt ptAt 4 srcCur rem ∗
        memRegion (dstPtr + BitVec.ofNat 64 (4 * done)) (4 * rem.length) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
        ((fsp + 56#64) ↦₆₄ lenVal) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ arrayAt ptAt 4 srcCur rem ∗
          ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ serializePtList rem) ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
          Frame) ∧
        VmPreserved s sm ∧
        AllocCallPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  induction rem generalizing s done srcCur lenVal Frame with
  | nil => exact (hne rfl).elim
  | cons pt rem' ih =>
    have htot' : done + (rem'.length + 1) = total := by
      simpa [List.length_cons] using htot
    have hrem_bound : 4 * (rem'.length + 1) < 2 ^ 63 := by omega
    have hnot_ule : BitVec.ule (BitVec.ofNat 64 (4 * total) - BitVec.ofNat 64 (4 * done)) 3#64 = false :=
      rem_bytes_not_ule_three htot' hmax
    nth_rw 1 [arrayAt_cons]
    nth_rw 1 [List.length_cons]
    rw [memRegion_four_cons dstPtr done rem'.length hrem_bound]
    dsimp only [ptAt, gf16At]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro v32
    refine seq_vm_clean (mid := (blkPl_377).base + 232#64)
      (P_mid :=
        (srcCur ↦₁₆ pt.x.value) ∗ ((srcCur + 2#64) ↦₁₆ pt.y.value) ∗
          arrayAt ptAt 4 (srcCur + 4#64) rem' ∗
          ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦₃₂ v32) ∗
          memRegion (dstPtr + BitVec.ofNat 64 (4 * (done + 1))) (4 * rem'.length) ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
          ((fsp + 56#64) ↦₆₄ lenVal) ∗
          Frame)
      (Q := fun sm =>
        AllocCallPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x0 = dstPtr ∧
        sm.readReg64 .x1 = BitVec.ofNat 64 (4 * done) ∧
        sm.readReg64 .x8 = (((pt.y.value.zeroExtend 64).setWidth 32 |||
          (pt.x.value.zeroExtend 64).setWidth 32 <<< 16).zeroExtend 64) ∧
        sm.readReg64 .x25 = BitVec.ofNat 64 (rem'.length + 1) ∧
        sm.readReg64 .x21 = srcCur + 2#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · by_vm_steps (wp_steps; wp_done)
    · intro s1 hpc1 hrun1 hvm1 ⟨hacp1, hsp1, hx29_1, hx0_1, hx1_1, hx8_1, hx25_1, hx21_1,
        hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx28_1, htrace1, hvregs1⟩
      cases rem' with
      | nil =>
        have hdone_tot : 4 * (done + 1) = 4 * total := by simp at htot'; omega
        simp only [List.length_nil, Nat.zero_add, Nat.mul_zero, memRegion_zero, sepConj_emp] at hx25_1 ⊢
        refine SepWP.mono (post := fun sm Pm =>
            VmPreserved s1 sm ∧
            (Pm ⊢ arrayAt ptAt 4 srcCur [pt] ∗
              ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ serializePtList [pt]) ∗
              ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
              ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
              Frame) ∧
            AllocCallPreserved s1 sm ∧
            sm.sp = fsp ∧
            sm.readReg64 .x29 = fsp + 64#64 ∧
            sm.readReg64 .x19 = s0.readReg64 .x19 ∧
            sm.readReg64 .x20 = s0.readReg64 .x20 ∧
            sm.readReg64 .x22 = s0.readReg64 .x22 ∧
            sm.readReg64 .x23 = s0.readReg64 .x23 ∧
            sm.readReg64 .x24 = s0.readReg64 .x24 ∧
            sm.readReg64 .x28 = s0.readReg64 .x28 ∧
            sm.trace = s0.trace ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0) ?_
          fun sm Pm _ _ ⟨hvm2, hent2, hacp2, hrest⟩ => ⟨hent2, hvm1.trans hvm2, hacp1.trans hacp2, hrest⟩
        by_vm_steps
          wp_steps
          rw [off_add_four done, hdone_tot, pointsTo32_rev_orr_eq_pt_serialize]
          have hser1 : serializePtList [pt] = pt.serialize := by
            simp [serializePtList]
          rw [hser1, arrayAt_cons]
          dsimp only [ptAt, gf16At]
          simp only [arrayAt_nil, sepConj_emp]
          wp_done
      | cons pt2 rem'' =>
        have hne' : pt2 :: rem'' ≠ [] := List.cons_ne_nil pt2 rem''
        have hpos' : 0 < (pt2 :: rem'').length := by simp
        have hlt' : (pt2 :: rem'').length + 1 < 2 ^ 64 := by simp at htot'; omega
        have hsubs_ne : (BitVec.ofNat 64 ((pt2 :: rem'').length + 1) != 1#64) = true :=
          bne_one_of_pos hpos' hlt'
        refine seq_vm_clean (mid := (blkPl_377).base + 204#64)
          (P_mid :=
            arrayAt ptAt 4 (srcCur + 4#64) (pt2 :: rem'') ∗
              memRegion (dstPtr + BitVec.ofNat 64 (4 * (done + 1))) (4 * (pt2 :: rem'').length) ∗
              ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
              ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * (done + 1))) ∗
              ((srcCur ↦₁₆ pt.x.value) ∗ ((srcCur + 2#64) ↦₁₆ pt.y.value) ∗
                ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ pt.serialize) ∗
                Frame))
          (Q := fun sm =>
            AllocCallPreserved s1 sm ∧
            sm.sp = fsp ∧
            sm.readReg64 .x29 = fsp + 64#64 ∧
            sm.readReg64 .x0 = dstPtr ∧
            sm.readReg64 .x1 = BitVec.ofNat 64 (4 * (done + 1)) ∧
            sm.readReg64 .x25 = BitVec.ofNat 64 (pt2 :: rem'').length ∧
            sm.readReg64 .x21 = (srcCur + 4#64) + 2#64 ∧
            sm.readReg64 .x19 = s0.readReg64 .x19 ∧
            sm.readReg64 .x20 = s0.readReg64 .x20 ∧
            sm.readReg64 .x22 = s0.readReg64 .x22 ∧
            sm.readReg64 .x23 = s0.readReg64 .x23 ∧
            sm.readReg64 .x24 = s0.readReg64 .x24 ∧
            sm.readReg64 .x28 = s0.readReg64 .x28 ∧
            sm.trace = s0.trace ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0)
          ?_ ?_
        · by_vm_steps
            wp_steps
            rw [off_add_four done, ofNat_succ_sub_one (pt2 :: rem'').length,
              srcCur_add_4_add_2 srcCur, pointsTo32_rev_orr_eq_pt_serialize]
            refine align_pre_vm (by sep_ac_rfl) ?_
            wp_done
        · intro s2 hpc2 hrun2 hvm2 ⟨hacp2, hsp2, hx29_2, hx0_2, hx1_2, hx25_2, hx21_2,
            hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx28_2, htrace2, hvregs2⟩
          have hih := ih hne' (done + 1) (by omega) s2 (srcCur + 4#64)
            (BitVec.ofNat 64 (4 * (done + 1)))
            ((srcCur ↦₁₆ pt.x.value) ∗ ((srcCur + 2#64) ↦₁₆ pt.y.value) ∗
              ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ pt.serialize) ∗
              Frame)
            hpc2 hrun2 hsp2 hx29_2 hx0_2 hx1_2 hx25_2 hx21_2
            hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx28_2 htrace2 hvregs2
          refine SepWP.mono hih fun sm Pm _ _ ⟨hent_ih, hvm_ih, hacp_ih, hrest_ih⟩ => ?_
          refine ⟨?_, hvm1.trans (hvm2.trans hvm_ih), hacp1.trans (hacp2.trans hacp_ih), hrest_ih⟩
          have harr : arrayAt ptAt 4 srcCur (pt :: pt2 :: rem'') =
              ((srcCur ↦₁₆ pt.x.value) ∗ ((srcCur + 2#64) ↦₁₆ pt.y.value)) ∗
                arrayAt ptAt 4 (srcCur + 4#64) (pt2 :: rem'') := by
            rw [arrayAt_cons]
            rfl
          have hser : ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ serializePtList (pt :: pt2 :: rem'')) =
              ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ pt.serialize) ∗
                ((dstPtr + BitVec.ofNat 64 (4 * (done + 1))) ↦ₛ serializePtList (pt2 :: rem'')) := by
            rw [serializePtList_cons]
            exact pointsToBytes_append_off dstPtr (4 * done) (4 * (done + 1))
              pt.serialize (serializePtList (pt2 :: rem''))
              (by simp [length_pt_serialize]; omega)
          refine Entails.trans hent_ih ?_
          rw [harr, hser]
          exact Entails.of_eq (by sep_ac_rfl)

/-- Placed finish one iteration of the `pts` outer loop (`+300 -> +104 -> +148 / +328`),
    preserving `VmPreserved` and `AllocCallPreserved`. -/
theorem pts_outer_finish_iter_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 : State) (fsp ptr_pts : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j remLen : Nat) (htot : j + (remLen + 1) = 16)
    (bs : List (BitVec 8)) (cap_c ptr_c : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_377).base + 300#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 j)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (if j + 1 = 16 then
        (blkPl_377).base + 328#64
       else
        (blkPl_377).base + 148#64)
      s
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 40#64) ↦₆₄ cap_c) ∗
        ((fsp + 48#64) ↦₆₄ ptr_c) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * j)) (24 * (remLen + 1)) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          (fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 40#64) ↦₆₄ cap_c) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8 A (ptr_pts + BitVec.ofNat 64 (24 * j)) bs ∗
          memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) ∧
        VmPreserved s sm ∧
        AllocCallPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (j + 1) ∧
        sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = 1#64 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  have hj_lt : j < 16 := by omega
  have hne16 : (BitVec.ofNat 64 j != 16#64) = true := ofNat_ne_16 hj_lt
  have hbeq16 : (BitVec.ofNat 64 j == 16#64) = false := ofNat_beq_16_false hj_lt
  rw [memRegion_24_cons ptr_pts j remLen (by omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro d0
  apply SepWP.exists_left; intro d1
  apply SepWP.exists_left; intro d2
  have hslot := vecU8_slot_intro A (ptr_pts + BitVec.ofNat 64 (24 * j)) cap_c ptr_c bs
  have hent :
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 40#64) ↦₆₄ cap_c) ∗
        ((fsp + 48#64) ↦₆₄ ptr_c) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        ((ptr_pts + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
        (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
        (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) ⊢
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 40#64) ↦₆₄ cap_c) ∗
        ((fsp + 48#64) ↦₆₄ ptr_c) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8 A (ptr_pts + BitVec.ofNat 64 (24 * j)) bs ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) := by
    have hgroup :
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 40#64) ↦₆₄ cap_c) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8Buf A cap_c ptr_c bs ∗
          ((ptr_pts + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
          (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
          (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) =
        ((((ptr_pts + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
          (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
          (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8Buf A cap_c ptr_c bs) ∗
          ((fsp ↦₆₄ 16#64) ∗
            ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
            ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
            ((fsp + 40#64) ↦₆₄ cap_c) ∗
            ((fsp + 48#64) ↦₆₄ ptr_c) ∗
            ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
            Frame)) := by sep_ac_rfl
    rw [hgroup]
    refine Entails.trans (sepConj_mono_left hslot) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  apply sepWP_swap_vm
  by_cases hdone : j + 1 = 16
  · have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = true := by simp [hdone]
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = false := by simp [hdone]
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    by_vm_steps
      wp_steps
      exact SepWP.weaken_pre hent (by wp_done)
  · have hj1_lt : j + 1 < 16 := by omega
    have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = false := ofNat_beq_16_false hj1_lt
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = true := ofNat_ne_16 hj1_lt
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    by_vm_steps
      wp_steps
      exact SepWP.weaken_pre hent (by wp_done)

end LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbLoopBudget
