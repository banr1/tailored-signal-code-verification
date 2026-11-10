/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbProof
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Top-Level Proof for `<PolyDecoder>::from_pb`

Proves `fromPbDec_placed_ok_ext`, `decoder_from_pb_placed_ok_ext`, `fromPbDec_placed_ok_x`, and
`decoder_from_pb_placed_ok_x` on Block `376` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbProofBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkPC_376 blkPl_376 lsmpl lsρ)
open CryptoVerification.RustHeap (allocHookStack arrayAt arrayAt_cons arrayAt_nil vecU8)
open CryptoVerification.LibsignalSpqrV1 (
  PolyDecoder PolynomialError ProtoPolynomialDecoder
)
open CryptoVerification.SpqrV1.Alloc (
  spqrMemcpySym spqrMemmoveSym spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Drop (dropGluePoly16Stack)
open CryptoVerification.SpqrV1.Poly (
  boolByte polyDecoderSize protoPolynomialDecoderAt protoPolynomialDecoderSize
  resultPolyDecoderFromPbAt sortedSetPtListOf
)
open CryptoVerification.SpqrV1.Poly.DecoderPb (
  FromPbDecGhost HiddenEq bv_add_lit_add_lit emptySlotAt emptySlotsAt fromPbCoreStack
  fromPbDecResult fromPbDecResult_eq_decoderFromPbResult fromPbDecResult_eq_err_of_exists_mod4
  fromPbDecResult_eq_err_of_len_ne_16 fromPbDecResult_eq_ok_of_all_mod4
  fromPb_stackAt_dropGluePoly16_split_bottom fsp_448_add_8 fsp_448_add_16 fsp_448_add_24
  fsp_448_add_32 fsp_448_add_40 fsp_448_add_48 fsp_448_add_56 fsp_448_add_64 fsp_448_add_72
  fsp_448_add_80 fsp_448_add_88 fsp_448_add_96 fsp_456_add_8 fsp_464_add_8 fsp_472_add_8
  fsp_480_add_8 fsp_488_add_8 fsp_496_add_8 fsp_504_add_8 fsp_512_add_8 fsp_520_add_8
  fsp_528_add_8 memRegion_448_split ofNat_ne_16_of_ne pbA_tail_entails_memRegion_16
  protoPolynomialDecoderAt_expose pushChunks4Total replace_sub_entails savedRegsAt
  sepWP_cells_succ sepWP_cells_zero spqrRustDeallocSym stackAt_fromPbCoreStack_split
)
open CryptoVerification.SpqrV1.States.FromPb (decoderFromPbStack)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget (
  fromPb_success_exit_876_placed_sepWP sessionMemcpyVmAcpSpec
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget (
  FromPbDecAllocEnv FromPbDecEnv FromPbDecPlacedOkExt FromPbDecPlacedOkX
  fromPbDecLoopAllocEvents
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExitPlacedBudget (
  fromPb_error_exit_712_placed_sepWP fromPb_error_exit_740_placed_sepWP
  fromPb_outer_loop_placed_wpp
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbInnerPlacedBudget (sessionMemmoveVmAcpSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (decoderFromPbSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_lit_add_lit
  fsp_448_add_8 fsp_448_add_16 fsp_448_add_24 fsp_448_add_32
  fsp_448_add_40 fsp_448_add_48 fsp_448_add_56 fsp_448_add_64
  fsp_448_add_72 fsp_448_add_80 fsp_448_add_88 fsp_448_add_96
  fsp_456_add_8 fsp_464_add_8 fsp_472_add_8 fsp_480_add_8
  fsp_488_add_8 fsp_496_add_8 fsp_504_add_8 fsp_512_add_8
  fsp_520_add_8 fsp_528_add_8
attribute [local simp] bv_add_lit_add_lit

/-! ## Stack-Parameterized Budget Specification & Sequencing Helpers -/

/-- Stack-parameterized budget specification of `<PolyDecoder>::from_pb`
    (`fromPbDecSpec M A lim = fromPbDecSpecWithStack M A lim fromPbDecStack` and
    `fromPbDecSpecX M A lim = fromPbDecSpecWithStack M A lim fromPbDecStackX` definitionally). -/
def fromPbDecSpecWithStack [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (FromPbDecGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      FitsEnv M lim st (FromPbDecAllocEnv x.pb) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.out polyDecoderSize ∗
      protoPolynomialDecoderAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FromPbDecEnv x.pb evs⌝ ∗
      resultPolyDecoderFromPbAt A.repAlloc x.out (fromPbDecResult x.pb) ∗
      memRegion x.pbA protoPolynomialDecoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk

theorem fromPbDecSpecWithStack_mono [LibsignalPlacement] {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {stk1 stk2 : Nat} (hle : stk1 ≤ stk2) (hmax : stk1 + (stk2 - stk1) ≤ 2 ^ 64)
    (h : subroutine_ok P addr (fromPbDecSpecWithStack M A lim stk1)) :
    subroutine_ok P addr (fromPbDecSpecWithStack M A lim stk2) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp stk2 =
      memRegion (s0.sp - BitVec.ofNat 64 stk2) (stk2 - stk1) ∗ stackAt s0.sp stk1 := by
    have h1 := stackAt_split_bottom s0.sp stk1 (stk2 - stk1) hmax
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk2) (stk2 - stk1) ∗ R
  have hpre' : s0.mem ⊨ (fromPbDecSpecWithStack M A lim stk1).pre x s0 ∗ R' := by
    dsimp only [fromPbDecSpecWithStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [fromPbDecSpecWithStack, R'] at hpost ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_seq_vm_clean {P : Program} {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post onPanic : State → SepProp → Prop}
    (h1 : SepWP P mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWPp P target sm P_mid post onPanic) :
    SepWPp P target s Pre post onPanic :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hvm hQ))

/-! ## `[LibsignalPlacement]` Prologue, Header Check, and Empty Slot Initialization -/

theorem fromPb_save_regs_placed_vm_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 : State) (out pbA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s0.pc = (blkPl_376).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hx1 : s0.readReg64 .x1 = pbA) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 32#64) s0
      (stackAt s0.sp fromPbCoreStack ∗ Frame)
      (fun sm Pm =>
        VmPreserved s0 sm ∧
        (Pm ⊢ savedRegsAt (s0.sp - 544#64) s0 ∗
          memRegion (s0.sp - 544#64) 448 ∗
          stackAt (s0.sp - 544#64) dropGluePoly16Stack ∗ Frame) ∧
        AllocCallPreserved s0 sm ∧
        sm.sp = s0.sp - 544#64 ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = (s0.sp - 544#64) + 448#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 544#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 544#64 hsp0_align
  have hfsp448_align : (((s0.sp - 544#64) + 448#64) &&& 15#64 == 0#64) = true := by
    revert hfsp_align; bv_bits
  rw [stackAt_fromPbCoreStack_split s0.sp,
      show (96 : Nat) = 8 * 12 by rfl,
      ProofLib.memRegion_cells ((s0.sp - 544#64) + 448#64) 12 (by decide)]
  have hpre_comm :
      (stackAt (s0.sp - 544#64) dropGluePoly16Stack ∗
        memRegion (s0.sp - 544#64) 448 ∗
        cells ((s0.sp - 544#64) + 448#64) 12) ∗ Frame =
      cells ((s0.sp - 544#64) + 448#64) 12 ∗
        (stackAt (s0.sp - 544#64) dropGluePoly16Stack ∗
          memRegion (s0.sp - 544#64) 448 ∗ Frame) := by sep_ac_rfl
  rw [hpre_comm]
  iterate 12 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [fsp_448_add_8, fsp_456_add_8, fsp_464_add_8, fsp_472_add_8,
    fsp_480_add_8, fsp_488_add_8, fsp_496_add_8, fsp_504_add_8, fsp_512_add_8,
    fsp_520_add_8, fsp_528_add_8, sepConj_assoc]
  dsimp only [Reg.x0, Reg.x1, Reg.x29, BitVec.ofNat_eq_ofNat] at hpc hx0 hx1 ⊢
  by_vm_steps (
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨by simp [wp_norm, arm64_norm], ?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    unfold savedRegsAt
    dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
      Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30, BitVec.ofNat_eq_ofNat]
    exact Entails.of_eq (by sep_ac_rfl))

theorem fromPb_header_ok_placed_vm_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out pbA : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 448#64) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 48#64) s
      (((pbA + 16#64) ↦₆₄ 16#64) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ 16#64) ∗ Frame) ∧
        AllocCallPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x20 = pbA ∧
        sm.readReg64 .x24 = 16#64 ∧
        sm.readReg64 .x29 = fsp + 448#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  dsimp only [Reg.x0, Reg.x1, Reg.x20, Reg.x24, Reg.x29, BitVec.ofNat_eq_ofNat] at hpc hx0 hx1 hx29 ⊢
  by_vm_steps (
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    exact ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
      by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩)

theorem fromPb_header_err_placed_vm_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out pbA : BitVec 64) (nPts : Nat)
    (hnPts : nPts < 2 ^ 64) (hne16 : nPts ≠ 16)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 448#64) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 712#64) s
      (((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 nPts) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 nPts) ∗ Frame) ∧
        AllocCallPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x20 = pbA ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 nPts ∧
        sm.readReg64 .x29 = fsp + 448#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  have hne : BitVec.ofNat 64 nPts ≠ 16#64 := ofNat_ne_16_of_ne hne16 hnPts
  have hbeq : (BitVec.ofNat 64 nPts == 16#64) = false := beq_eq_false_iff_ne.mpr hne
  have hbeq' : (16#64 == BitVec.ofNat 64 nPts) = false := beq_eq_false_iff_ne.mpr hne.symm
  have hbne : (BitVec.ofNat 64 nPts != 16#64) = true := bne_iff_ne.mpr hne
  have hbne' : (16#64 != BitVec.ofNat 64 nPts) = true := bne_iff_ne.mpr hne.symm
  dsimp only [Reg.x0, Reg.x1, Reg.x20, Reg.x24, Reg.x29, BitVec.ofNat_eq_ofNat] at hpc hx0 hx1 hx29 ⊢
  by_vm_steps (
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    exact ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
      by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩)

theorem fromPb_init_empty_headers_placed_vm_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out pbA ptsPtr v8 v16 v24 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 48#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx20 : s.readReg64 .x20 = pbA)
    (hx24 : s.readReg64 .x24 = 16#64)
    (hx29 : s.readReg64 .x29 = fsp + 448#64) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 204#64) s
      (memRegion (fsp + 32#64) 384 ∗
        ((fsp + 8#64) ↦₆₄ v8) ∗
        ((fsp + 16#64) ↦₆₄ v16) ∗
        ((fsp + 24#64) ↦₆₄ v24) ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ emptySlotsAt (fsp + 32#64) 16 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗
          ((fsp + 16#64) ↦₆₄ pbA) ∗
          ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
          Frame) ∧
        AllocCallPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = 24#64 ∧
        sm.readReg64 .x21 = ptsPtr ∧
        sm.readReg64 .x24 = 16#64 ∧
        sm.readReg64 .x25 = 0#64 ∧
        sm.readReg64 .x29 = fsp + 448#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  rw [ProofLib.memRegion_cells (fsp + 32#64) 48 (by decide)]
  iterate 24 (apply sepWP_cells_succ; intro)
  iterate 24 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  dsimp only [Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x24, Reg.x25, Reg.x29,
    BitVec.ofNat_eq_ofNat] at hpc hx0 hx20 hx24 hx29 ⊢
  by_vm_steps (
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨by simp [wp_norm, arm64_norm], ?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    simp only [emptySlotsAt, List.replicate_succ, List.replicate_zero, arrayAt_cons, arrayAt_nil,
      emptySlotAt, sepConj_emp, bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    exact Entails.of_eq (by sep_ac_rfl))

/-! ## Exit Packaging & Top-Level `[LibsignalPlacement]` Proofs (Block `376`) -/

theorem sepWPp_of_exit_core_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (s0 s : State) (out pbA : BitVec 64)
    (pb : ProtoPolynomialDecoder)
    (res : Except PolynomialError PolyDecoder)
    (st0 : M.σ) (evs_alloc : List AllocEvent)
    (halloc_env : FromPbDecAllocEnv pb evs_alloc)
    (hacp_pre : AllocCallPreserved s0 s)
    (P R : SepProp)
    (h : SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P
      (fun sf P' =>
        ∃ evs_free, FreeOnlyEvs evs_free ∧
          (P' ⊢ resultPolyDecoderFromPbAt A.repAlloc out res ∗
            memRegion pbA 40 ∗
            A.pool lim (M.stepEvents evs_free (M.stepEvents evs_alloc st0)) sf ∗
            stackAt s0.sp fromPbCoreStack ∗ emp) ∧
          sf.sp = s0.sp ∧ AllocCallPreserved s sf ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWPp ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (∃∗ evs : List AllocEvent,
            ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FromPbDecEnv pb evs⌝ ∗
            resultPolyDecoderFromPbAt A.repAlloc out res ∗
            memRegion pbA protoPolynomialDecoderSize ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt s0.sp fromPbCoreStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨evs_free, hfree, hPf, hspf, hacp_exit, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  rw [sepConj_emp, ← M.stepEvents_append evs_alloc evs_free st0] at hPf
  have h1 : sf.mem ⊨ (resultPolyDecoderFromPbAt A.repAlloc out res ∗
      memRegion pbA protoPolynomialDecoderSize ∗
      A.pool lim (M.stepEvents (evs_alloc ++ evs_free) st0) sf ∗
      stackAt s0.sp fromPbCoreStack) ∗ R :=
    Satisfies.mono (sepConj_mono_left hPf) hmem_f
  have henv : FromPbDecEnv pb (evs_alloc ++ evs_free) :=
    ⟨evs_alloc, evs_free, rfl, halloc_env, hfree⟩
  have hacp : AllocCallPreserved s0 sf := hacp_pre.trans hacp_exit
  refine Satisfies.mono (sepConj_mono_left ?_) h1
  refine Entails.trans
    (Entails.pure_right ⟨htrf, hacp, henv⟩ (Entails.refl _))
    (Entails.sepExists_intro (P := fun evs =>
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FromPbDecEnv pb evs⌝ ∗
      resultPolyDecoderFromPbAt A.repAlloc out res ∗
      memRegion pbA protoPolynomialDecoderSize ∗
      A.pool lim (M.stepEvents evs st0) sf ∗
      stackAt s0.sp fromPbCoreStack) (evs_alloc ++ evs_free))

theorem fromPbDec_placed_ok_core [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyVmAcpSpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveVmAcpSpec 0))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim)) :
    subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (blkPl_376).base
      (fromPbDecSpecWithStack M A lim fromPbCoreStack) := by
  have hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem hdealloc_sat
  have hmemcpy : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpyVmAcpSpec :=
    spqr_hook_ok_of_mem hmemcpy_sat
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA, pb⟩, st0⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [fromPbDecSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfits, hlr_ls⟩, hmem⟩
  have hlr_gpr30 : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := hlr_ls
  refine ⟨stackAt s0.sp fromPbCoreStack ∗
      (memRegion out polyDecoderSize ∗ protoPolynomialDecoderAt A.repAlloc pbA pb ∗ A.pool lim st0 s0),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  dsimp only [fromPbDecSpecWithStack]
  have hpro := fromPb_save_regs_placed_vm_sepWP (ext := ext) s0 out pbA hsp0_align
    (memRegion out polyDecoderSize ∗ protoPolynomialDecoderAt A.repAlloc pbA pb ∗ A.pool lim st0 s0)
    hpc0 hrun0 hx0 hx1
  refine sepWPp_seq_vm_clean hpro ?_
  intro s1 hpc1 hrun1 hvm1 ⟨hacp1, hsp1, hx0_1, hx1_1, hx29_1, hvregs1, htr1⟩
  rw [← A.pool_of_vmPreserved hvm1]
  let fsp := s0.sp - 544#64
  have hfsp : HiddenEq fsp (s0.sp - 544#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 544#64 hsp0_align
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (protoPolynomialDecoderAt_expose A.repAlloc pbA pb
        (savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
          memRegion out polyDecoderSize ∗ A.pool lim st0 s1))) ?_
  apply SepWPp.exists_elim; intro cap_pts
  apply SepWPp.exists_elim; intro ptsPtr
  apply SepWPp.pure_elim; rintro ⟨hle, hcap_bound, hlen_bound, _⟩
  by_cases hlen16 : pb.pts.length = 16
  · have hhdr := fromPb_header_ok_placed_vm_sepWP (ext := ext) s1 fsp out pbA
      ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        memRegion out polyDecoderSize ∗ A.pool lim st0 s1)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre (by rw [hlen16]; exact Entails.of_eq (by sep_ac_rfl))
      (sepWPp_seq_vm_clean hhdr ?_)
    intro s2 hpc2 hrun2 hvm2 ⟨hacp2, hsp2, hx0_2, hx20_2, hx24_2, hx29_2, hvregs2, htr2⟩
    rw [← A.pool_of_vmPreserved hvm2]
    conv => arg 4; rw [memRegion_448_split fsp, fromPb_stackAt_dropGluePoly16_split_bottom fsp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro v432
    apply SepWPp.exists_elim; intro v424
    apply SepWPp.exists_elim; intro v416
    apply SepWPp.exists_elim; intro v24
    apply SepWPp.exists_elim; intro v16
    apply SepWPp.exists_elim; intro v8
    have hinit := fromPb_init_empty_headers_placed_vm_sepWP (ext := ext)
      s2 fsp out pbA ptsPtr v8 v16 v24 hfsp_align
      (memRegion fsp 8 ∗
        ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
        memRegion out polyDecoderSize ∗ A.pool lim st0 s2)
      hpc2 hrun2 hsp2 hx0_2 hx20_2 hx24_2 hx29_2
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (sepWPp_seq_vm_clean hinit ?_)
    intro s3 hpc3 hrun3 hvm3 ⟨hacp3, hsp3, hx19_3, hx21_3, hx24_3, hx25_3, hx29_3, hvregs3, htr3⟩
    rw [← A.pool_of_vmPreserved hvm3]
    have hacp03 : AllocCallPreserved s0 s3 := (hacp1.trans hacp2).trans hacp3
    have halloc_loop : FromPbDecAllocEnv pb (fromPbDecLoopAllocEvents pb.pts) :=
      Or.inr ⟨hlen16, rfl⟩
    have hfit_loop : FitsEvents M lim st0 (fromPbDecLoopAllocEvents pb.pts) :=
      hfits _ halloc_loop
    have hpts_ne : pb.pts ≠ [] := by intro h; simp [h] at hlen16
    refine SepWPp.weaken_pre
      (by
        dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        rw [BitVec.add_zero, BitVec.add_zero, hlen16]
        exact Entails.of_eq (by sep_ac_rfl))
      (fromPb_outer_loop_placed_wpp hshim_sat halloc_sat hmemmove_sat
        s0 fsp ptsPtr hfsp_align pb.pts hpts_ne 0
        (by omega) st0 hfit_loop v416 v424 v432 s3
        (((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
          memRegion fsp 8 ∗ memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
          ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
          (if cap_pts = 0 then emp
            else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ memRegion out polyDecoderSize)
        hpc3 hrun3 hsp3 hx19_3 hx21_3 hx24_3 hx25_3 hx29_3
        (by rw [htr3, htr2, htr1]) (by rw [hvregs3, hvregs2, hvregs1])
        (fun sm w416 w424 w432 hall hpcm hrunm hacpm hspm hx21m _ _ htrm hvregsm => ?_)
        (fun sm sets_err w416 w424 w432 hex hsets_len hpcm hrunm hacpm hspm hx21m hx24m hx29m htrm hvregsm => ?_))
    · rw [fromPbDecResult_eq_ok_of_all_mod4 pb hlen16 hall]
      have hout_len : (pb.pts.map fun bs => pushChunks4Total bs { vec := [] }).length = 16 := by
        simp [hlen16]
      have hok := fromPb_success_exit_876_placed_sepWP hdealloc hmemcpy s0 fsp out pbA cap_pts ptsPtr w416 w424 w432
        hfsp hsp0_align hfsp_align pb hlen16
        (pb.pts.map fun bs => pushChunks4Total bs { vec := [] }) hout_len hle hcap_bound
        (M.stepEvents (fromPbDecLoopAllocEvents pb.pts) st0) sm emp
        hpcm hrunm hspm hx21m hvregsm htrm
      have hok' := SepWP.mono
        (post' := fun sf P' =>
          ∃ evs_free, FreeOnlyEvs evs_free ∧
            (P' ⊢ resultPolyDecoderFromPbAt A.repAlloc out
                (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete,
                       pts := pb.pts.map fun bs => pushChunks4Total bs { vec := [] } }) ∗
              memRegion pbA 40 ∗
              A.pool lim (M.stepEvents evs_free (M.stepEvents (fromPbDecLoopAllocEvents pb.pts) st0)) sf ∗
              stackAt s0.sp fromPbCoreStack ∗ emp) ∧
            sf.sp = s0.sp ∧ AllocCallPreserved sm sf ∧
            CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
        hok fun sf P' _ _ ⟨evs_f, hf, hP', hacp_f, hsp_f, hcs_f, htr_f⟩ =>
          ⟨evs_f, hf, hP', hsp_f, hacp_f, hcs_f, htr_f⟩
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_core_placed s0 sm out pbA pb _ st0
          (fromPbDecLoopAllocEvents pb.pts) halloc_loop (hacp03.trans hacpm) _ R hok')
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, polyDecoderSize]
      rw [BitVec.add_zero, BitVec.add_zero]
      exact Entails.of_eq (by sep_ac_rfl)
    · rw [fromPbDecResult_eq_err_of_exists_mod4 pb hlen16 hex]
      have hsets_len16 : sets_err.length = 16 := hsets_len.trans hlen16
      have herr := fromPb_error_exit_740_placed_sepWP hdealloc hdrop s0 fsp out pbA cap_pts ptsPtr w416 w424 w432
        hfsp hsp0_align hfsp_align sets_err hsets_len16 pb.pts hlen16 hle hcap_bound
        (M.stepEvents (fromPbDecLoopAllocEvents pb.pts) st0) sm emp
        hpcm hrunm hspm hx21m hx24m hx29m hvregsm htrm
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_core_placed s0 sm out pbA pb (.error .serializationInvalid) st0
          (fromPbDecLoopAllocEvents pb.pts) halloc_loop (hacp03.trans hacpm) _ R herr)
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, polyDecoderSize]
      rw [BitVec.add_zero, BitVec.add_zero]
      have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
      exact replace_sub_entails hpb16
        (memRegion out 400 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          sortedSetPtListOf A.repAlloc (fsp + 32#64) sets_err ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
          (if cap_pts = 0 then emp
            else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗
          A.pool lim (M.stepEvents (fromPbDecLoopAllocEvents pb.pts) st0) sm ∗
          stackAt fsp allocHookStack)
        (by sep_ac_rfl) (by sep_ac_rfl)
  · rw [fromPbDecResult_eq_err_of_len_ne_16 pb hlen16]
    have hnPts : pb.pts.length < 2 ^ 64 := by omega
    have hhdr := fromPb_header_err_placed_vm_sepWP (ext := ext) s1 fsp out pbA
      pb.pts.length hnPts hlen16
      ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        memRegion out polyDecoderSize ∗ A.pool lim st0 s1)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (sepWPp_seq_vm_clean hhdr ?_)
    intro s2 hpc2 hrun2 hvm2 ⟨hacp2, hsp2, hx0_2, hx20_2, hx24_2, _, hvregs2, htr2⟩
    rw [← A.pool_of_vmPreserved hvm2]
    have halloc_nil : FromPbDecAllocEnv pb [] := Or.inl rfl
    have herr := fromPb_error_exit_712_placed_sepWP hdealloc s0 fsp out pbA cap_pts ptsPtr
      hfsp hsp0_align hfsp_align pb.pts hle hcap_bound hlen_bound
      (M.stepEvents [] st0) s2 emp hpc2 hrun2 hsp2 hx0_2 hx20_2 hx24_2
      (by rw [hvregs2, hvregs1]) (by rw [htr2, htr1])
    refine SepWPp.weaken_pre ?_
      (sepWPp_of_exit_core_placed s0 s2 out pbA pb (.error .serializationInvalid) st0
        [] halloc_nil (hacp1.trans hacp2) _ R herr)
    dsimp only [polyDecoderSize, AllocCostModel.stepEvents]
    have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
    exact replace_sub_entails hpb16
      (memRegion out 400 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool lim st0 s2 ∗ stackAt fsp dropGluePoly16Stack)
      (by sep_ac_rfl) (by sep_ac_rfl)

theorem fromPbDec_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyVmAcpSpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveVmAcpSpec 0))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim)) :
    FromPbDecPlacedOkExt M A lim ext :=
  fromPbDecSpecWithStack_mono (by decide) (by decide)
    (fromPbDec_placed_ok_core halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat hdrop)

theorem fromPbDec_placed_ok_stack1056 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyVmAcpSpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveVmAcpSpec 0))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim)) :
    subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (blkPl_376).base
      (fromPbDecSpecWithStack M A lim decoderFromPbStack) :=
  fromPbDecSpecWithStack_mono (by decide) (by decide)
    (fromPbDec_placed_ok_core halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat hdrop)

theorem decoderFromPbSpec_of_fromPbDecSpecWithStack_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (fromPbDecSpecWithStack M A lim decoderFromPbStack)) :
    subroutine_ok P entry (decoderFromPbSpec M A lim) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  let xg : FromPbDecGhost := ⟨x.out, x.pbA, x.pb⟩
  have hpre' : s0.mem ⊨ (fromPbDecSpecWithStack M A lim decoderFromPbStack).pre (xg, st) s0 ∗ R := hpre
  refine h.mono_outcome (xg, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [decoderFromPbSpec, fromPbDecSpecWithStack, xg] at hpost ⊢
    rwa [← fromPbDecResult_eq_decoderFromPbResult x.pb]
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem decoder_from_pb_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyVmAcpSpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveVmAcpSpec 0))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim)) :
    subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (blkPl_376).base
      (decoderFromPbSpec M A lim) :=
  decoderFromPbSpec_of_fromPbDecSpecWithStack_at
    (fromPbDec_placed_ok_stack1056 halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat hdrop)

theorem fromPbDec_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyVmAcpSpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveVmAcpSpec 0))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim)) :
    FromPbDecPlacedOkX M A lim ext :=
  fromPbDecSpecWithStack_mono (by decide) (by decide)
    (fromPbDec_placed_ok_core halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat hdrop)

theorem decoder_from_pb_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyVmAcpSpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveVmAcpSpec 0))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim)) :
    FromPbDecPlacedOkX M A lim ext :=
  fromPbDec_placed_ok_x halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat hdrop

end LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbProofBudget
