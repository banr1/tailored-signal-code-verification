/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbLoopBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuter
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Outer Loop for `<PolyDecoder>::into_pb`

Threads `RustCliAllocBudget M`, `VmPreserved`, and `AllocCallPreserved` through the 16-slot outer
loop (`+148..+328`) on Block `377`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuterBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkPC_377 blkPl_377 lsρ)
open CryptoVerification.RustHeap (allocHookStack arrayAt arrayAt_nil vecU8 vecU8Buf)
open CryptoVerification.LibsignalSpqrV1 (Pt)
open CryptoVerification.SpqrV1.Alloc (
  spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Drop (vecPtOf)
open CryptoVerification.SpqrV1.Poly (ptAt)
open CryptoVerification.SpqrV1.Poly.DecoderPb (
  SepWPp.seq_clean arrayAt_24_off_cons arrayAt_24_off_singleton
  fp64_sub_16 fp64_sub_16_int fp64_sub_24 fp64_sub_24_int fp64_sub_8 fp64_sub_8_int
  length_serializePtList madd_24_eq ofNat_add_one ofNat_beq_zero_false
  sepWPp_pure_mid serializePtList serializePtList_nil shiftLeft_two_eq_mul_four
  sp_add_40_add_8 vecPtOf_expose vecPtOf_intro vecPtTail
  vecU8Buf_nil_intro vecU8Buf_of_exact_alloc
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEvent FitsEvents RustCliAllocBudget
  RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
  rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (decoderIntoPbSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbLoopBudget (
  pts_inner_loop_placed pts_outer_finish_iter_placed
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  fp64_sub_24 fp64_sub_16 fp64_sub_8
  fp64_sub_24_int fp64_sub_16_int fp64_sub_8_int
  sp_add_40_add_8
  ofNat_add_one madd_24_eq

private theorem sepWP_swap_vm {prog : Program} {tgt : BitVec 64} {s : State}
    {Pre : SepProp} {Ent : SepProp → Prop} {Rest : State → Prop}
    (h : SepWP prog tgt s Pre (fun sm Pm => VmPreserved s sm ∧ Ent Pm ∧ Rest sm)) :
    SepWP prog tgt s Pre (fun sm Pm => Ent Pm ∧ VmPreserved s sm ∧ Rest sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hvm, hent, hr⟩ => ⟨hent, hvm, hr⟩

/-! ## Relocatable (`[LibsignalPlacement]`) Budget-Threaded Outer Loop for Block `377` -/

/-- Budget-threaded placed allocate and serialize one `SortedSet<Pt>` element (`+148 -> +300`). -/
theorem pts_outer_alloc_and_copy_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    {Q Qp : State → SepProp → Prop}
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (pts : List Pt)
    (st : M.σ) (hfit : FitsEvents M lim st (decoderIntoPbSlotEvents pts))
    (v40 v48 v56 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_377).base + 148#64)
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
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (cap_c ptr_c : BitVec 64),
      sm.pc = (blkPl_377).base + 300#64 →
      sm.status = .Running →
      AllocCallPreserved s sm →
      sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 64#64 →
      sm.readReg64 .x19 = s0.readReg64 .x19 →
      sm.readReg64 .x20 = s0.readReg64 .x20 →
      sm.readReg64 .x22 = BitVec.ofNat 64 j →
      sm.readReg64 .x23 = 24#64 →
      sm.readReg64 .x24 = 1#64 →
      sm.readReg64 .x28 = s0.readReg64 .x28 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) sm
        (((fsp + 40#64) ↦₆₄ cap_c) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (serializePtList pts).length) ∗
          vecU8Buf A.repAlloc cap_c ptr_c (serializePtList pts) ∗
          vecPtOf A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
          A.pool lim (M.stepEvents (decoderIntoPbSlotEvents pts) st) sm ∗
          stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (vecPtOf A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
        ((fsp + 40#64) ↦₆₄ v40) ∗
        ((fsp + 48#64) ↦₆₄ v48) ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  have halloc_nooom : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget halloc
  simp only [rustAllocShimVmSpec, BitVec.ofNat_eq_ofNat] at hshim
  simp only [rustCliAllocNoOomSpec, ↓reduceIte, BitVec.ofNat_eq_ofNat] at halloc_nooom
  refine SepWPp.weaken_pre
    (sepConj_mono_left (vecPtOf_expose A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap_pts
  apply SepWPp.exists_elim; intro ptr_pts
  apply SepWPp.pure_elim; rintro ⟨hmax, hptr_pts⟩
  cases pts with
  | nil =>
    have hslotev : decoderIntoPbSlotEvents ([] : List Pt) = [] := rfl
    have hstep0 : M.stepEvents ([] : List _) st = st := rfl
    simp only [List.length_nil, Nat.mul_zero, serializePtList_nil, hslotev, hstep0,
      BitVec.ofNat_eq_ofNat] at hmax hnext
    conv => arg 4; simp only [List.length_nil, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
    refine SepWPp.seq_clean (mid := (blkPl_377).base + 300#64)
      (P_mid :=
        ((fsp + 40#64) ↦₆₄ 0#64) ∗
          ((fsp + 48#64) ↦₆₄ 1#64) ∗
          ((fsp + 56#64) ↦₆₄ 0#64) ∗
          vecU8Buf A.repAlloc 0#64 1#64 [] ∗
          vecPtOf A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) [] ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q_mid := fun sm =>
        VmPreserved s sm ∧
        AllocCallPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 j ∧
        sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = 1#64 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · apply sepWP_swap_vm
      by_vm_steps
        wp_steps
        have hfold_pt := vecPtOf_intro A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) cap_pts ptr_pts []
        simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hfold_pt
        have hbuf := vecU8Buf_nil_intro A.repAlloc
          (vecPtOf A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) [] ∗
            ((fsp + 40#64) ↦₆₄ 0#64) ∗
            ((fsp + 48#64) ↦₆₄ 1#64) ∗
            ((fsp + 56#64) ↦₆₄ 0#64) ∗
            A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        have hent :
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
              arrayAt ptAt 4 ptr_pts [] ∗
              vecPtTail A.repAlloc cap_pts ptr_pts 0 ∗
              ((fsp + 40#64) ↦₆₄ 0#64) ∗
              ((fsp + 48#64) ↦₆₄ 1#64) ∗
              ((fsp + 56#64) ↦₆₄ 0#64) ∗
              A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
            (((fsp + 40#64) ↦₆₄ 0#64) ∗
              ((fsp + 48#64) ↦₆₄ 1#64) ∗
              ((fsp + 56#64) ↦₆₄ 0#64) ∗
              vecU8Buf A.repAlloc 0#64 1#64 [] ∗
              vecPtOf A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) [] ∗
              A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) := by
          have h1 :
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
                (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
                (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
                arrayAt ptAt 4 ptr_pts [] ∗
                vecPtTail A.repAlloc cap_pts ptr_pts 0 ∗
                ((fsp + 40#64) ↦₆₄ 0#64) ∗
                ((fsp + 48#64) ↦₆₄ 1#64) ∗
                ((fsp + 56#64) ↦₆₄ 0#64) ∗
                A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) =
              ((((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
                (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
                (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
                arrayAt ptAt 4 ptr_pts [] ∗
                vecPtTail A.repAlloc cap_pts ptr_pts 0) ∗
                (((fsp + 40#64) ↦₆₄ 0#64) ∗
                  ((fsp + 48#64) ↦₆₄ 1#64) ∗
                  ((fsp + 56#64) ↦₆₄ 0#64) ∗
                  A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)) := by sep_ac_rfl
          rw [h1]
          refine Entails.trans (sepConj_mono_left hfold_pt) ?_
          refine Entails.trans hbuf ?_
          exact Entails.of_eq (by sep_ac_rfl)
        exact SepWP.weaken_pre hent (by wp_done)
    · intro sm hpcm hrunm ⟨hvm, hacp, hspm, hx29m, hx19m, hx20m, hx22m, hx23m, hx24m, hx28m, htrm, hvregsm⟩
      rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm]
      exact hnext sm 0#64 1#64 hpcm hrunm hacp hspm hx29m hx19m hx20m hx22m hx23m hx24m hx28m htrm hvregsm
  | cons pt pts' =>
    have hslotev : decoderIntoPbSlotEvents (pt :: pts') = rustAllocEvents (4 * (pt :: pts').length) 1 := rfl
    rw [hslotev] at hfit hnext
    have hpts_pos : 0 < (pt :: pts').length := by simp
    have hbeq0 : (BitVec.ofNat 64 (pt :: pts').length == 0#64) = false :=
      ofNat_beq_zero_false hpts_pos (by omega)
    have hlsl : (BitVec.ofNat 64 (pt :: pts').length) <<< 2 = BitVec.ofNat 64 (4 * (pt :: pts').length) :=
      shiftLeft_two_eq_mul_four hmax
    have htoNat_len : (BitVec.ofNat 64 (4 * (pt :: pts').length)).toNat = 4 * (pt :: pts').length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : RustLayoutOk (4 * (pt :: pts').length) 1 := ⟨⟨by omega, hpow2, by omega⟩, by decide⟩
    apply SepWPp.of_sepWP (mid := (blkPl_377).base + 168#64)
    wp_steps
    wp_apply
    apply SepWP.done (by assumption) (by wp_norm_lhs)
    have hpool_shim : A.pool lim st s = A.pool lim st sf := by
      have hvm_pre := (A.pool_of_vmPreserved (lim := lim) (st := st) ‹VmPreserved _ sf›).symm
      simpa [wp_norm, arm64_norm] using hvm_pre
    rw [hpool_shim]
    have hacp_s_sf : AllocCallPreserved s sf := ‹AllocCallPreserved s sf›
    have htr_sf : sf.trace = s0.trace := hacp_s_sf.2.1.trans htrace
    have hev_eq : rustAllocEvents (4 * (pt :: pts').length) 1 = [.alloc (4 * (pt :: pts').length)] := by
      have hcond : 1 ≤ 4 * (pt :: pts').length := by omega
      simp only [rustAllocEvents, hcond, Nat.one_le_ofNat, and_self, ↓reduceIte]
    have hfit_ev : FitsEvent M lim st (.alloc (4 * (pt :: pts').length)) := by
      have hfit' := hfit; rw [hev_eq] at hfit'; exact hfit'.1
    rcases hfit_ev with ⟨hwithin, henf, hram, hva⟩
    apply SepWPp.of_sepWP (mid := (blkPl_377).base + 180#64)
    wp_steps
    wp_call halloc_nooom (4 * (pt :: pts').length, 1, st)
    apply SepWP.done (by assumption) (by wp_norm_lhs)
    have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hne0
    have hacp_sf_sf1 : AllocCallPreserved sf sf_1 := by assumption
    have hacp_s_sf1 : AllocCallPreserved s sf_1 := hacp_s_sf.trans hacp_sf_sf1
    have htr_sf1 : sf_1.trace = s0.trace := hacp_sf_sf1.2.1.trans htr_sf
    let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
    let st' := M.stepEvents (rustAllocEvents (4 * (pt :: pts').length) 1) st
    refine SepWPp.seq_clean (mid := (blkPl_377).base + 204#64)
      (P_mid :=
        arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
          memRegion (ptr_c + BitVec.ofNat 64 (4 * 0)) (4 * (pt :: pts').length) ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
          ((fsp + 56#64) ↦₆₄ 0#64) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
          (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
          (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
          vecPtTail A.repAlloc cap_pts ptr_pts (pt :: pts').length ∗
          A.live ptr_c (4 * (pt :: pts').length) 1 ∗
          A.pool lim st' sf_1 ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q_mid := fun sm =>
        VmPreserved sf_1 sm ∧
        AllocCallPreserved sf_1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x0 = ptr_c ∧
        sm.readReg64 .x1 = BitVec.ofNat 64 (4 * 0) ∧
        sm.readReg64 .x25 = BitVec.ofNat 64 (pt :: pts').length ∧
        sm.readReg64 .x21 = ptr_pts + 2#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 j ∧
        sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = 1#64 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · apply sepWP_swap_vm
      by_vm_steps
        wp_steps
        have hz : ptr_c + BitVec.ofNat 64 (4 * 0) = ptr_c := by simp
        rw [hz]
        wp_done
    · intro s_in hpc_in hrun_in ⟨hvm_204, hacp_204, hsp_in, hx29_in, hx0_in, hx1_in, hx25_in, hx21_in,
        hx19_in, hx20_in, hx22_in, hx23_in, hx24_in, hx28_in, htr_in, hvregs_in⟩
      rw [← A.pool_of_vmPreserved (lim := lim) (st := st') hvm_204]
      have hloop := pts_inner_loop_placed (ext := ext) s_in fsp ptr_c
        (pt :: pts').length hmax (pt :: pts') (List.cons_ne_nil pt pts') 0 (by omega)
        s_in ptr_pts 0#64
        (((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
          (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
          (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
          vecPtTail A.repAlloc cap_pts ptr_pts (pt :: pts').length ∗
          A.live ptr_c (4 * (pt :: pts').length) 1 ∗
          A.pool lim st' s_in ∗ stackAt fsp allocHookStack ∗ Frame)
        hpc_in hrun_in hsp_in hx29_in hx0_in hx1_in hx25_in hx21_in
        rfl rfl rfl rfl rfl rfl rfl rfl
      refine SepWPp.seq_clean hloop ?_
      intro s_out hpc_out hrun_out ⟨hvm_loop, hacp_loop, hsp_out, hx29_out, hx19_out, hx20_out,
        hx22_out, hx23_out, hx24_out, hx28_out, htr_out, hvregs_out⟩
      rw [← A.pool_of_vmPreserved (lim := lim) (st := st') hvm_loop]
      rw [hx19_in] at hx19_out
      rw [hx20_in] at hx20_out
      rw [hx22_in] at hx22_out
      rw [hx23_in] at hx23_out
      rw [hx24_in] at hx24_out
      rw [hx28_in] at hx28_out
      rw [htr_in] at htr_out
      rw [hvregs_in] at hvregs_out
      have hacp_tot : AllocCallPreserved s s_out :=
        hacp_s_sf1.trans (hacp_204.trans hacp_loop)
      have hz : ptr_c + BitVec.ofNat 64 (4 * 0) = ptr_c := by simp
      have hser_len : (serializePtList (pt :: pts')).length = 4 * (pt :: pts').length :=
        length_serializePtList (pt :: pts')
      have hbuf := vecU8Buf_of_exact_alloc A.repAlloc ptr_c (serializePtList (pt :: pts'))
        (by rw [hser_len]; omega) (by rw [hser_len]; omega) hne0
      have hfold_pt := vecPtOf_intro A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) cap_pts ptr_pts (pt :: pts')
      have hent :
          (arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
            ((ptr_c + BitVec.ofNat 64 (4 * 0)) ↦ₛ serializePtList (pt :: pts')) ∗
            ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
            ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
            ((fsp + 48#64) ↦₆₄ ptr_c) ∗
            ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
            vecPtTail A.repAlloc cap_pts ptr_pts (pt :: pts').length ∗
            A.live ptr_c (4 * (pt :: pts').length) 1 ∗
            A.pool lim st' s_out ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
          (((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
            ((fsp + 48#64) ↦₆₄ ptr_c) ∗
            ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (serializePtList (pt :: pts')).length) ∗
            vecU8Buf A.repAlloc (BitVec.ofNat 64 (4 * (pt :: pts').length)) ptr_c (serializePtList (pt :: pts')) ∗
            vecPtOf A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) (pt :: pts') ∗
            A.pool lim st' s_out ∗ stackAt fsp allocHookStack ∗ Frame) := by
        rw [hz]
        rw [hser_len] at hbuf ⊢
        have hg1 :
            (arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
              (ptr_c ↦ₛ serializePtList (pt :: pts')) ∗
              ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
              ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
              ((fsp + 48#64) ↦₆₄ ptr_c) ∗
              ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
              vecPtTail A.repAlloc cap_pts ptr_pts (pt :: pts').length ∗
              A.live ptr_c (4 * (pt :: pts').length) 1 ∗
              A.pool lim st' s_out ∗ stackAt fsp allocHookStack ∗ Frame) =
            (((ptr_c ↦ₛ serializePtList (pt :: pts')) ∗
              A.repAlloc.live ptr_c (4 * (pt :: pts').length) 1) ∗
              ((((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
                (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
                (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
                arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
                vecPtTail A.repAlloc cap_pts ptr_pts (pt :: pts').length) ∗
                (((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
                  ((fsp + 48#64) ↦₆₄ ptr_c) ∗
                  ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
                  A.pool lim st' s_out ∗ stackAt fsp allocHookStack ∗ Frame))) := by
          dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl
        rw [hg1]
        refine Entails.trans (sepConj_mono hbuf (sepConj_mono_left hfold_pt)) ?_
        exact Entails.of_eq (by sep_ac_rfl)
      exact SepWPp.weaken_pre hent
        (hnext s_out (BitVec.ofNat 64 (4 * (pt :: pts').length)) ptr_c
          hpc_out hrun_out hacp_tot hsp_out hx29_out hx19_out hx20_out hx22_out hx23_out hx24_out hx28_out htr_out hvregs_out)

/-- Budget-threaded placed full `pts` outer loop (`+148 -> +328`). -/
theorem pts_outer_loop_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    {Q Qp : State → SepProp → Prop}
    (s0 : State) (fsp ptr_pts : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (rem : List (List Pt)) (hne : rem ≠ [])
    (j : Nat) (htot : j + rem.length = 16)
    (st : M.σ) (hfit : FitsEvents M lim st (rem.flatMap decoderIntoPbSlotEvents))
    (v40 v48 v56 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_377).base + 148#64)
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
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (w40 w48 w56 : BitVec 64),
      sm.pc = (blkPl_377).base + 328#64 →
      sm.status = .Running →
      AllocCallPreserved s sm →
      sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 64#64 →
      sm.readReg64 .x19 = s0.readReg64 .x19 →
      sm.readReg64 .x20 = s0.readReg64 .x20 →
      sm.readReg64 .x28 = s0.readReg64 .x28 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) sm
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ 16#64) ∗
          ((fsp + 40#64) ↦₆₄ w40) ∗
          ((fsp + 48#64) ↦₆₄ w48) ∗
          ((fsp + 56#64) ↦₆₄ w56) ∗
          arrayAt (fun pts addr => vecPtOf A.repAlloc addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) rem ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptr_pts + BitVec.ofNat 64 (24 * j)) (rem.map serializePtList) ∗
          A.pool lim (M.stepEvents (rem.flatMap decoderIntoPbSlotEvents) st) sm ∗
          stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 40#64) ↦₆₄ v40) ∗
        ((fsp + 48#64) ↦₆₄ v48) ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        arrayAt (fun pts addr => vecPtOf A.repAlloc addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) rem ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * j)) (24 * rem.length) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  induction rem generalizing j st v40 v48 v56 s Frame with
  | nil => exact (hne rfl).elim
  | cons pts rem' ih =>
    have htot' : j + (rem'.length + 1) = 16 := by
      simpa [List.length_cons] using htot
    rw [List.flatMap_cons] at hfit
    rcases (fitsEvents_append M lim _ _ _).mp hfit with ⟨hfit1, hfit2⟩
    let st1 := M.stepEvents (decoderIntoPbSlotEvents pts) st
    rw [arrayAt_24_off_cons]
    conv => arg 4; rw [List.length_cons]
    refine SepWPp.weaken_pre (P' :=
      vecPtOf A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
        ((fsp + 40#64) ↦₆₄ v40) ∗
        ((fsp + 48#64) ↦₆₄ v48) ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
          arrayAt (fun pts addr => vecPtOf A.repAlloc addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
          memRegion (ptr_pts + BitVec.ofNat 64 (24 * j)) (24 * (rem'.length + 1)) ∗
          Frame))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine pts_outer_alloc_and_copy_placed hshim halloc s0 fsp hfsp_align j pts st hfit1 v40 v48 v56 s _
      hpc hrun hsp hx29 hx19 hx20 hx22 hx23 hx24 hx28 htrace hvregs ?_
    intro sm1 cap_c ptr_c hpc1 hrun1 hacp1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1 hvregs1
    refine SepWPp.weaken_pre (P' :=
      (fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 40#64) ↦₆₄ cap_c) ∗
        ((fsp + 48#64) ↦₆₄ ptr_c) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (serializePtList pts).length) ∗
        vecU8Buf A.repAlloc cap_c ptr_c (serializePtList pts) ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * j)) (24 * (rem'.length + 1)) ∗
        (vecPtOf A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
          arrayAt (fun pts addr => vecPtOf A.repAlloc addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
          A.pool lim st1 sm1 ∗ stackAt fsp allocHookStack ∗ Frame))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    have hfin := pts_outer_finish_iter_placed (A := A.repAlloc) (ext := ext)
      s0 fsp ptr_pts hfsp_align j rem'.length htot'
      (serializePtList pts) cap_c ptr_c sm1
      (vecPtOf A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
        arrayAt (fun pts addr => vecPtOf A.repAlloc addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
        A.pool lim st1 sm1 ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1 hvregs1
    refine SepWPp.seq_clean hfin ?_
    intro sm2 hpc2 hrun2 ⟨hvm2, hacp2, hsp2, hx29_2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx28_2, htr2, hvregs2⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st1) hvm2]
    cases rem' with
    | nil =>
      have hj1 : j + 1 = 16 := by simp at htot'; omega
      simp only [hj1, ↓reduceIte] at hpc2
      have h16 : BitVec.ofNat 64 (j + 1) = 16#64 := by rw [hj1]
      have hflat : ([pts] : List (List Pt)).flatMap decoderIntoPbSlotEvents = decoderIntoPbSlotEvents pts := by
        simp
      have hacp12 : AllocCallPreserved s sm2 := hacp1.trans hacp2
      refine SepWPp.weaken_pre ?_
        (hnext sm2 cap_c ptr_c (BitVec.ofNat 64 (serializePtList pts).length)
          hpc2 hrun2 hacp12 hsp2 hx29_2 hx19_2 hx20_2 hx28_2 htr2 hvregs2)
      simp only [List.length_nil, List.map_cons, List.map_nil, arrayAt_nil, arrayAt_24_off_singleton,
        Nat.mul_zero, memRegion_zero, sepConj_emp, h16, hflat]
      exact Entails.of_eq (by dsimp only [st1]; sep_ac_rfl)
    | cons pts2 rem'' =>
      have hj1 : j + 1 ≠ 16 := by simp at htot'; omega
      simp only [hj1, ↓reduceIte] at hpc2
      refine SepWPp.weaken_pre (P' :=
        (fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 40#64) ↦₆₄ cap_c) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (serializePtList pts).length) ∗
          arrayAt (fun pts addr => vecPtOf A.repAlloc addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * (j + 1))) (pts2 :: rem'') ∗
          memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * (pts2 :: rem'').length) ∗
          A.pool lim st1 sm2 ∗ stackAt fsp allocHookStack ∗
          (vecPtOf A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
            vecU8 A.repAlloc (ptr_pts + BitVec.ofNat 64 (24 * j)) (serializePtList pts) ∗
            Frame))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine ih (List.cons_ne_nil pts2 rem'') (j + 1) (by simp at htot' ⊢; omega) st1 hfit2
        cap_c ptr_c (BitVec.ofNat 64 (serializePtList pts).length)
        sm2
        (vecPtOf A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
          vecU8 A.repAlloc (ptr_pts + BitVec.ofNat 64 (24 * j)) (serializePtList pts) ∗
          Frame)
        hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx28_2 htr2 hvregs2 ?_
      intro sm3 w40 w48 w56 hpc3 hrun3 hacp3 hsp3 hx29_3 hx19_3 hx20_3 hx28_3 htr3 hvregs3
      have hacp123 : AllocCallPreserved s sm3 := hacp1.trans (hacp2.trans hacp3)
      have hstep_cat :
          M.stepEvents ((pts2 :: rem'').flatMap decoderIntoPbSlotEvents) st1 =
            M.stepEvents ((pts :: pts2 :: rem'').flatMap decoderIntoPbSlotEvents) st :=
        (M.stepEvents_append (decoderIntoPbSlotEvents pts)
          ((pts2 :: rem'').flatMap decoderIntoPbSlotEvents) st).symm.trans
          (congrArg (fun l => M.stepEvents l st) List.flatMap_cons.symm)
      refine SepWPp.weaken_pre ?_
        (hnext sm3 w40 w48 w56 hpc3 hrun3 hacp123 hsp3 hx29_3 hx19_3 hx20_3 hx28_3 htr3 hvregs3)
      rw [hstep_cat]
      simp only [List.map_cons, arrayAt_24_off_cons]
      exact Entails.of_eq (by sep_ac_rfl)

theorem pts_outer_alloc_and_copy_placed_of_hookSat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    {Q Qp : State → SepProp → Prop}
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (pts : List Pt)
    (st : M.σ) (hfit : FitsEvents M lim st (decoderIntoPbSlotEvents pts))
    (v40 v48 v56 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_377).base + 148#64)
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
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (cap_c ptr_c : BitVec 64),
      sm.pc = (blkPl_377).base + 300#64 →
      sm.status = .Running →
      AllocCallPreserved s sm →
      sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 64#64 →
      sm.readReg64 .x19 = s0.readReg64 .x19 →
      sm.readReg64 .x20 = s0.readReg64 .x20 →
      sm.readReg64 .x22 = BitVec.ofNat 64 j →
      sm.readReg64 .x23 = 24#64 →
      sm.readReg64 .x24 = 1#64 →
      sm.readReg64 .x28 = s0.readReg64 .x28 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) sm
        (((fsp + 40#64) ↦₆₄ cap_c) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (serializePtList pts).length) ∗
          vecU8Buf A.repAlloc cap_c ptr_c (serializePtList pts) ∗
          vecPtOf A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
          A.pool lim (M.stepEvents (decoderIntoPbSlotEvents pts) st) sm ∗
          stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (vecPtOf A.repAlloc (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
        ((fsp + 40#64) ↦₆₄ v40) ∗
        ((fsp + 48#64) ↦₆₄ v48) ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp :=
  pts_outer_alloc_and_copy_placed
    (spqr_hook_ok_of_mem hshim_sat) (spqr_hook_ok_of_mem halloc_sat)
    s0 fsp hfsp_align j pts st hfit v40 v48 v56 s Frame
    hpc hrun hsp hx29 hx19 hx20 hx22 hx23 hx24 hx28 htrace hvregs hnext

theorem pts_outer_loop_placed_of_hookSat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    {Q Qp : State → SepProp → Prop}
    (s0 : State) (fsp ptr_pts : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (rem : List (List Pt)) (hne : rem ≠ [])
    (j : Nat) (htot : j + rem.length = 16)
    (st : M.σ) (hfit : FitsEvents M lim st (rem.flatMap decoderIntoPbSlotEvents))
    (v40 v48 v56 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_377).base + 148#64)
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
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (w40 w48 w56 : BitVec 64),
      sm.pc = (blkPl_377).base + 328#64 →
      sm.status = .Running →
      AllocCallPreserved s sm →
      sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 64#64 →
      sm.readReg64 .x19 = s0.readReg64 .x19 →
      sm.readReg64 .x20 = s0.readReg64 .x20 →
      sm.readReg64 .x28 = s0.readReg64 .x28 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) sm
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ 16#64) ∗
          ((fsp + 40#64) ↦₆₄ w40) ∗
          ((fsp + 48#64) ↦₆₄ w48) ∗
          ((fsp + 56#64) ↦₆₄ w56) ∗
          arrayAt (fun pts addr => vecPtOf A.repAlloc addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) rem ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptr_pts + BitVec.ofNat 64 (24 * j)) (rem.map serializePtList) ∗
          A.pool lim (M.stepEvents (rem.flatMap decoderIntoPbSlotEvents) st) sm ∗
          stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 40#64) ↦₆₄ v40) ∗
        ((fsp + 48#64) ↦₆₄ v48) ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        arrayAt (fun pts addr => vecPtOf A.repAlloc addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) rem ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * j)) (24 * rem.length) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp :=
  pts_outer_loop_placed
    (spqr_hook_ok_of_mem hshim_sat) (spqr_hook_ok_of_mem halloc_sat)
    s0 fsp ptr_pts hfsp_align rem hne j htot st hfit v40 v48 v56 s Frame
    hpc hrun hsp hx29 hx19 hx20 hx22 hx23 hx24 hx28 htrace hvregs hnext

end LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuterBudget
