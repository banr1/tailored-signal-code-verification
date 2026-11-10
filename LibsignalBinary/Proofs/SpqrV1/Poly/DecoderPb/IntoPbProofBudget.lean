/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuterBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbProof
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Top-Level Proof for `<PolyDecoder>::into_pb`

Proves `decoder_into_pb_placed_ok_ext` and `decoder_into_pb_placed_ok_x` on Block `377` under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbProofBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkPC_377 blkPl_377 lsρ lsmpl)
open CryptoVerification.RustHeap (
  allocHookStack arrayAt vecU8
)
open CryptoVerification.LibsignalSpqrV1 (CHUNK_SIZE NUM_POLYS PolyDecoder Pt SortedSetPt)
open CryptoVerification.SpqrV1.Alloc (
  spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Drop (
  DropGlueSortedSetPt16Ghost dropGluePoly16Stack
  sortedSetPtListOf_eq_vecPtListOf vecPtListOf vecPtOf
)
open CryptoVerification.SpqrV1.Poly (
  boolByte polyArrayBytes polyDecoderAt polyDecoderIsCompleteOff polyDecoderPadOff
  polyDecoderPadSize polyDecoderPtsNeededOff polyDecoderSize
  protoPolynomialDecoderAt protoPolynomialDecoderSize sortedSetPtListOf
)
open CryptoVerification.SpqrV1.Poly.DecoderPb (
  DecoderIntoPbGhost HiddenEq SepWPp.seq_clean bv384_toNat bv8_toNat
  cells20_fsp_entails cells20_fsp_eq decA_rejoin_400 decA_tail_rejoin_16
  decoderIntoPbStack decoderIntoPbStackX memRegion_40_split
  off_8_add_8 off_16_add_8 off_24_add_4 off_24_add_8 off_32_add_8 off_40_add_8
  off_48_add_8 off_56_add_8 off_64_add_8 off_72_add_8 off_80_add_8 off_88_add_8
  off_96_add_8 off_104_add_8 off_112_add_8 off_120_add_8 off_128_add_8
  off_136_add_8 off_144_add_8 pointsTo32_off24_merge64 pointsTo64_off24_split32
  pointsTo64_off32_entails_isComplete_pad pointsTo64_off32_merge_low8
  pointsTo64_off32_split_low8 protoPolynomialDecoderAt_entails sepWPp_elim_pure
  serializePtList
  setWidth_8_setWidth_32_setWidth_64 setWidth_8_setWidth_64 setWidth_32_ofNat_64
  stackAt_decoderIntoPb_split stackAt_dropGluePoly16_split_bottom sub_160_add_160
  truncate_32_ofNat_64 withSaved19_20 withSaved19_20_lr
  withSaved19_20_trace withSaved19_20_vregs withSaved19_20_x19 withSaved19_20_x20
  withSaved19_20_x28
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  FreeOnlyEvs RustCliAllocBudget RustLayoutOk VmPreserved fitsEvents_append
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (
  DecoderIntoPbAllocEnv DecoderIntoPbEnv DecoderIntoPbPlacedOkExt
  DecoderIntoPbPlacedOkX decoderIntoPbAllocEvents decoderIntoPbSlotEvents
  decoderIntoPbSpec decoderIntoPbSpecX
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuterBudget (pts_outer_loop_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  bv384_toNat bv8_toNat
  off_8_add_8 off_16_add_8 off_24_add_4 off_24_add_8 off_32_add_8 off_40_add_8
  off_48_add_8 off_56_add_8 off_64_add_8 off_72_add_8 off_80_add_8 off_88_add_8
  off_96_add_8 off_104_add_8 off_112_add_8 off_120_add_8 off_128_add_8
  off_136_add_8 off_144_add_8 sub_160_add_160
  truncate_32_ofNat_64 setWidth_32_ofNat_64
  CryptoVerification.SpqrV1.Poly.DecoderPb.truncate_8_zeroExtend_64
  setWidth_8_setWidth_64 setWidth_8_setWidth_32_setWidth_64

/-! ## Stack-Lifting Helpers -/

private theorem sepWP_swap_vm {prog : Program} {tgt : BitVec 64} {s : State}
    {Pre : SepProp} {Ent : SepProp → Prop} {Rest : State → Prop}
    (h : SepWP prog tgt s Pre (fun sm Pm => VmPreserved s sm ∧ Ent Pm ∧ Rest sm)) :
    SepWP prog tgt s Pre (fun sm Pm => Ent Pm ∧ VmPreserved s sm ∧ Rest sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hvm, hent, hr⟩ => ⟨hent, hvm, hr⟩

private theorem into_pb_epilogue_post_entails_pool (Pool : SepProp)
    (sp0 fsp out decA : BitVec 64)
    (hfsp : fsp = sp0 - 160#64)
    (ptsNeeded polys : BitVec 32)
    (v4 : BitVec 64) (isComplete : BitVec 8)
    (w0 w1 w2 w5 w6 w7 v11 : BitVec 64)
    (r29 r30 r27 r26 r25 r24 r23 r22 r21 r20 r19 : BitVec 64)
    (Frame : SepProp) :
    (fsp ↦₆₄ w0) ∗ ((fsp + 8#64) ↦₆₄ w1) ∗ ((fsp + 16#64) ↦₆₄ w2) ∗
      ((fsp + 24#64) ↦₆₄ (polys ++ ptsNeeded)) ∗
      ((fsp + 32#64) ↦₆₄ (v4.extractLsb' 8 56 ++ isComplete)) ∗
      ((fsp + 40#64) ↦₆₄ w5) ∗ ((fsp + 48#64) ↦₆₄ w6) ∗ ((fsp + 56#64) ↦₆₄ w7) ∗
      ((fsp + 64#64) ↦₆₄ r29) ∗ ((fsp + 72#64) ↦₆₄ r30) ∗ ((fsp + 80#64) ↦₆₄ r27) ∗
      ((fsp + 88#64) ↦₆₄ v11) ∗ ((fsp + 96#64) ↦₆₄ r26) ∗ ((fsp + 104#64) ↦₆₄ r25) ∗
      ((fsp + 112#64) ↦₆₄ r24) ∗ ((fsp + 120#64) ↦₆₄ r23) ∗ ((fsp + 128#64) ↦₆₄ r22) ∗
      ((fsp + 136#64) ↦₆₄ r21) ∗ ((fsp + 144#64) ↦₆₄ r20) ∗ ((fsp + 152#64) ↦₆₄ r19) ∗
      (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
      ((out + 24#64) ↦₆₄ (polys ++ ptsNeeded)) ∗
      ((out + 32#64) ↦₆₄ (v4.extractLsb' 8 56 ++ isComplete)) ∗
      memRegion decA polyArrayBytes ∗ memRegion (decA + 384#64) 16 ∗
      Pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame ⊢
    (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
      ((out + 24#64) ↦₃₂ ptsNeeded) ∗ ((out + 28#64) ↦₃₂ polys) ∗
      ((out + 32#64) ↦₈ isComplete) ∗ memRegion (out + 33#64) 7 ∗
      memRegion decA 400 ∗
      Pool ∗ stackAt sp0 decoderIntoPbStack ∗ Frame := by
  have hcells := cells20_fsp_entails fsp
    w0 w1 w2 (polys ++ ptsNeeded) (v4.extractLsb' 8 56 ++ isComplete) w5 w6 w7
    r29 r30 r27 v11 r26 r25 r24 r23 r22 r21 r20 r19
  have h24 : ((out + 24#64) ↦₆₄ (polys ++ ptsNeeded)) =
      (((out + 24#64) ↦₃₂ ptsNeeded) ∗ ((out + 28#64) ↦₃₂ polys)) :=
    (pointsTo32_off24_merge64 out ptsNeeded polys).symm
  have h32 := pointsTo64_off32_entails_isComplete_pad out v4 isComplete
  have hstk : stackAt sp0 decoderIntoPbStack = stackAt fsp dropGluePoly16Stack ∗ cells fsp 20 := by
    rw [hfsp, stackAt_decoderIntoPb_split sp0]
  dsimp only [polyArrayBytes]
  rw [hstk, ← decA_rejoin_400 decA, h24]
  refine Entails.trans (Q :=
    ((fsp ↦₆₄ w0) ∗ ((fsp + 8#64) ↦₆₄ w1) ∗ ((fsp + 16#64) ↦₆₄ w2) ∗
      ((fsp + 24#64) ↦₆₄ (polys ++ ptsNeeded)) ∗
      ((fsp + 32#64) ↦₆₄ (v4.extractLsb' 8 56 ++ isComplete)) ∗
      ((fsp + 40#64) ↦₆₄ w5) ∗ ((fsp + 48#64) ↦₆₄ w6) ∗ ((fsp + 56#64) ↦₆₄ w7) ∗
      ((fsp + 64#64) ↦₆₄ r29) ∗ ((fsp + 72#64) ↦₆₄ r30) ∗ ((fsp + 80#64) ↦₆₄ r27) ∗
      ((fsp + 88#64) ↦₆₄ v11) ∗ ((fsp + 96#64) ↦₆₄ r26) ∗ ((fsp + 104#64) ↦₆₄ r25) ∗
      ((fsp + 112#64) ↦₆₄ r24) ∗ ((fsp + 120#64) ↦₆₄ r23) ∗ ((fsp + 128#64) ↦₆₄ r22) ∗
      ((fsp + 136#64) ↦₆₄ r21) ∗ ((fsp + 144#64) ↦₆₄ r20) ∗ ((fsp + 152#64) ↦₆₄ r19)) ∗
    ((out + 32#64) ↦₆₄ (v4.extractLsb' 8 56 ++ isComplete)) ∗
    ((out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
      ((out + 24#64) ↦₃₂ ptsNeeded) ∗ ((out + 28#64) ↦₃₂ polys) ∗
      memRegion decA 384 ∗ memRegion (decA + 384#64) 16 ∗
      Pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hcells (sepConj_mono h32 (Entails.refl _))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- `decoderIntoPbSpec M A lim` entails `decoderIntoPbSpecX M A lim` by framing the unused
    bottom stack region (`decoderIntoPbStackX - decoderIntoPbStack`). -/
theorem decoderIntoPbSpecX_of_decoderIntoPbSpec {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok P addr (decoderIntoPbSpec M A lim)) :
    subroutine_ok P addr (decoderIntoPbSpecX M A lim) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hle : decoderIntoPbStack ≤ decoderIntoPbStackX := by decide
  have hsplit : stackAt s0.sp decoderIntoPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 decoderIntoPbStackX)
        (decoderIntoPbStackX - decoderIntoPbStack) ∗
        stackAt s0.sp decoderIntoPbStack := by
    have h1 := stackAt_split_bottom s0.sp decoderIntoPbStack
      (decoderIntoPbStackX - decoderIntoPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 decoderIntoPbStackX)
      (decoderIntoPbStackX - decoderIntoPbStack) ∗ R
  have hpre' : s0.mem ⊨ (decoderIntoPbSpec M A lim).pre (x, st) s0 ∗ R' := by
    dsimp only [decoderIntoPbSpecX, decoderIntoPbSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (x, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [decoderIntoPbSpecX, decoderIntoPbSpec, R',
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact (not_satisfies_false_sepConj hpan).elim
  · dsimp only [decoderIntoPbSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Relocatable (`[LibsignalPlacement]`) Budget-Threaded Proofs for Block `377` -/

/-- Budget-threaded placed epilogue of `<PolyDecoder>::into_pb` (`+328` to `s0.lr`). -/
theorem into_pb_epilogue_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim))
    (s0 : State) (fsp out decA : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 160#64))
    (ptsNeeded polys : BitVec 32) (v4 : BitVec 64) (isComplete : BitVec 8)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (vecs : List (List Pt)) (hvecs : vecs.length = NUM_POLYS)
    (st : M.σ)
    (w0 w1 w2 w5 w6 w7 v11 d0 d1 d2 d3 d4 : BitVec 64) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_377).base + 328#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64) (hx19 : s.readReg64 .x19 = decA)
    (hx20 : s.readReg64 .x20 = out)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      ((fsp ↦₆₄ w0) ∗ ((fsp + 8#64) ↦₆₄ w1) ∗ ((fsp + 16#64) ↦₆₄ w2) ∗
        ((fsp + 24#64) ↦₃₂ ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ polys) ∗
        ((fsp + 32#64) ↦₈ isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
        ((fsp + 40#64) ↦₆₄ w5) ∗ ((fsp + 48#64) ↦₆₄ w6) ∗ ((fsp + 56#64) ↦₆₄ w7) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        vecPtListOf A.repAlloc decA vecs ∗ memRegion (decA + 384#64) 16 ∗
        A.pool lim st s ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        ∃ evs_free : List AllocEvent,
          FreeOnlyEvs evs_free ∧
          (P' ⊢
            (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
            ((out + 24#64) ↦₃₂ ptsNeeded) ∗ ((out + 28#64) ↦₃₂ polys) ∗
            ((out + 32#64) ↦₈ isComplete) ∗ memRegion (out + 33#64) 7 ∗
            memRegion decA 400 ∗ A.pool lim (M.stepEvents evs_free st) sf ∗
            stackAt s0.sp decoderIntoPbStack ∗ Frame) ∧
          AllocCallPreserved s sf ∧
          sf.sp = s0.sp ∧
          sf.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5) ∧
          sf.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5) ∧
          sf.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5) ∧
          sf.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
          sf.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
          sf.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
          sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
          sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
          sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
          sf.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
          sf.readReg64 (Reg.gpr 29#5) = s0.readReg64 (Reg.gpr 29#5) ∧
          sf.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) ∧
          sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) := by
  simp only [dropGlueSortedSetPt16Spec, BitVec.ofNat_eq_ofNat] at hdrop
  conv => arg 4; rw [
    ← sepConj_assoc ((fsp + 24#64) ↦₃₂ ptsNeeded) ((fsp + 28#64) ↦₃₂ polys),
    pointsTo32_off24_merge64 fsp ptsNeeded polys,
    ← sepConj_assoc ((fsp + 32#64) ↦₈ isComplete) ((fsp + 33#64) ↦ₛ (unpack64 v4).tail),
    pointsTo64_off32_merge_low8 fsp v4 isComplete]
  wp_steps_sync_pool (lsmpl.base 264)
  simp only [State.setMem_setMem]
  wp_call hdrop (⟨decA, vecs⟩, st)
  let evs_free : List AllocEvent := (fun {evs} (_ : FreeOnlyEvs evs) => evs) ‹FreeOnlyEvs _›
  have hfree : FreeOnlyEvs evs_free := ‹FreeOnlyEvs _›
  have hacp_drop : AllocCallPreserved s sf := by
    simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
  rcases hacp_drop with ⟨_, _, _, _, _, _, _⟩
  refine SepWP.mono (post := fun sf_ret P' =>
    (P' ⊢
      (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
      ((out + 24#64) ↦₃₂ ptsNeeded) ∗ ((out + 28#64) ↦₃₂ polys) ∗
      ((out + 32#64) ↦₈ isComplete) ∗ memRegion (out + 33#64) 7 ∗
      memRegion decA 400 ∗ A.pool lim (M.stepEvents evs_free st) sf_ret ∗
      stackAt s0.sp decoderIntoPbStack ∗ Frame) ∧
    AllocCallPreserved s sf_ret ∧
    sf_ret.sp = s0.sp ∧
    sf_ret.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5) ∧
    sf_ret.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5) ∧
    sf_ret.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5) ∧
    sf_ret.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
    sf_ret.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
    sf_ret.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
    sf_ret.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
    sf_ret.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
    sf_ret.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
    sf_ret.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
    sf_ret.readReg64 (Reg.gpr 29#5) = s0.readReg64 (Reg.gpr 29#5) ∧
    sf_ret.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) ∧
    sf_ret.trace = s0.trace ∧ calleeSavedVRegs sf_ret = calleeSavedVRegs s0) ?_
    (fun _ _ _ _ hq => ⟨evs_free, hfree, hq⟩)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  have hsp_ret : fsp + 160#64 = s0.sp := by rw [hfsp.eq]; bv_omega
  conv => arg 3; rw [hsp_ret]
  conv => arg 4; simp only [hsp, hsp_ret]
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (into_pb_epilogue_post_entails_pool _ s0.sp fsp out decA hfsp.eq
      ptsNeeded polys v4 isComplete
      w0 w1 w2 w5 w6 w7 v11 (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x27)
      (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) Frame))
    (by wp_done)

/-- Budget-threaded placed prologue and header initialization of `<PolyDecoder>::into_pb`
    (`+0 -> +148`, OOM unreachable under `FitsEvents M lim st (rustAllocEvents 384 8)`). -/
theorem into_pb_prologue_and_init_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    {Q Qp : State → SepProp → Prop}
    (s0 : State) (fsp out decA : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 160#64))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (ptsNeeded : Nat) (isComplete : Bool)
    (st : M.σ) (hfit : FitsEvents M lim st (rustAllocEvents 384 8))
    (v0 v1 v2 v3 v4 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18 v19 : BitVec 64) (Frame : SepProp)
    (hpc : s0.pc = (blkPl_377).base) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out) (hx1 : s0.readReg64 .x1 = decA)
    (hnext : ∀ (sm : State) (ptr_pts : BitVec 64),
      ptr_pts ≠ 0 → sm.pc = (blkPl_377).base + 148#64 → sm.status = .Running →
      AllocCallPreserved s0 sm → sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 64#64 → sm.readReg64 .x19 = decA → sm.readReg64 .x20 = out →
      sm.readReg64 .x22 = 0#64 → sm.readReg64 .x23 = 24#64 → sm.readReg64 .x24 = 1#64 →
      sm.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) sm
        ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗ ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗ ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗ ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗ memRegion (decA + 384#64) 16 ∗
          A.live ptr_pts 384 8 ∗ memRegion ptr_pts 384 ∗
          A.pool lim (M.stepEvents (rustAllocEvents 384 8) st) sm ∗
          stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s0
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
        ((fsp + 32#64) ↦₆₄ v4) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗
        ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 96#64) ↦₆₄ v12) ∗ ((fsp + 104#64) ↦₆₄ v13) ∗
        ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗ ((fsp + 128#64) ↦₆₄ v16) ∗
        ((fsp + 136#64) ↦₆₄ v17) ∗ ((fsp + 144#64) ↦₆₄ v18) ∗ ((fsp + 152#64) ↦₆₄ v19) ∗
        ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 ptsNeeded) ∗
        ((decA + 392#64) ↦₈ boolByte isComplete) ∗
        memRegion (decA + 393#64) 7 ∗ A.pool lim st s0 ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  have hallocNoOom : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget halloc
  dsimp only [rustAllocShimVmSpec] at hshim
  dsimp only [rustCliAllocNoOomSpec, ↓reduceIte] at hallocNoOom
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hrlay384 : RustLayoutOk 384 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hfit_ev := hfit.1
  rcases hfit_ev with ⟨hwithin, henf, hram, hva⟩
  apply SepWPp.of_sepWP (mid := (blkPl_377).base + 64#64)
  wp_step
  conv => arg 3; simp only [← hfsp.eq]
  have hpool_sub : A.pool lim st s0 =
      A.pool lim st ((s0.writeReg64 .sp fsp).setPC ((blkPl_377).base + 4#64)) :=
    A.pool_of_vmPreserved (lim := lim) (st := st)
      ⟨by simp [LibsignalBinary.Heap.PoolPreserved, wp_norm, arm64_norm], rfl, fun _ => rfl,
       fun _ _ _ => rfl⟩
  conv => arg 4; rw [hpool_sub]
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have hpool_shim := (A.pool_of_vmPreserved (lim := lim) (st := st) ‹VmPreserved _ sf›).symm
  conv => arg 4; rw [hpool_shim]
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call hallocNoOom (384, 8, st)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
  have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hne0
  have hacp_shim : AllocCallPreserved s0 sf := by
    simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
  have hacp_01 : AllocCallPreserved s0 sf_1 :=
    hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
  have htr_sf1 : sf_1.trace = s0.trace := hacp_01.2.1
  have hsp_sf0 : sf.sp = fsp := ‹sf.sp = fsp›
  have hsp_sf1 : sf_1.sp = fsp := ‹sf_1.sp = sf.sp›.trans hsp_sf0
  let ptr_pts := sf_1.readReg64 (Reg.gpr 0#5)
  let st1 := M.stepEvents (rustAllocEvents 384 8) st
  conv => arg 4; simp only [hsp_sf1, hsp_sf0]
  conv => arg 4; rw [pointsTo64_off24_split32 fsp v3, pointsTo64_off32_split_low8 fsp v4]
  refine SepWPp.seq_clean (mid := (blkPl_377).base + 148#64)
    (P_mid := (fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
      ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
      ((fsp + 32#64) ↦₈ boolByte isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
      ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗ ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗ ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗ ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗ memRegion (decA + 384#64) 16 ∗
      A.live ptr_pts 384 8 ∗ memRegion ptr_pts 384 ∗
      A.pool lim st1 sf_1 ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q_mid := fun sm =>
      VmPreserved sf_1 sm ∧ AllocCallPreserved sf_1 sm ∧
      sm.sp = fsp ∧ sm.readReg64 .x29 = fsp + 64#64 ∧ sm.readReg64 .x19 = decA ∧
      sm.readReg64 .x20 = out ∧ sm.readReg64 .x22 = 0#64 ∧ sm.readReg64 .x23 = 24#64 ∧
      sm.readReg64 .x24 = 1#64 ∧ sm.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · apply sepWP_swap_vm
    by_vm_steps
      wp_steps
      have htail := decA_tail_rejoin_16 decA (BitVec.ofNat 64 ptsNeeded) (boolByte isComplete)
      refine SepWP.weaken_pre (P' :=
        (((decA + 384#64) ↦₆₄ BitVec.ofNat 64 ptsNeeded) ∗
          ((decA + 392#64) ↦₈ boolByte isComplete) ∗ memRegion (decA + 393#64) 7) ∗
        ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗ ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗ ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗ ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗ A.live ptr_pts 384 8 ∗ memRegion ptr_pts 384 ∗
          A.pool lim st1 sf_1 ∗ stackAt fsp allocHookStack ∗ Frame))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      exact SepWP.weaken_pre (Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by sep_ac_rfl)))
        (by wp_done)
  · intro sm hpcm hrunm ⟨hvm_m, hacp_m, hspm, hx29m, hx19m, hx20m, hx22m, hx23m, hx24m, hx28m, htrm, hvregsm⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st1) hvm_m]
    exact hnext sm ptr_pts hne0 hpcm hrunm (hacp_01.trans hacp_m)
      hspm hx29m hx19m hx20m hx22m hx23m hx24m hx28m htrm hvregsm

theorem decoder_into_pb_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdrop : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim)) :
    DecoderIntoPbPlacedOkExt M A lim ext := by
  unfold DecoderIntoPbPlacedOkExt
  have hshim : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec := spqr_hook_ok_of_mem hshim_sat
  have halloc : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := spqr_hook_ok_of_mem halloc_sat
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, decA, dec⟩, st⟩ R s0 hpc hrun hpre hsp0
  simp only [decoderIntoPbSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfit_env⟩, hmem⟩
  have hfit_all : FitsEvents M lim st (decoderIntoPbAllocEvents dec) :=
    hfit_env (decoderIntoPbAllocEvents dec) rfl
  have hflat_map_eq :
      (dec.pts.map SortedSetPt.vec).flatMap decoderIntoPbSlotEvents =
        dec.pts.flatMap (fun s => decoderIntoPbSlotEvents s.vec) :=
    List.flatMap_map SortedSetPt.vec decoderIntoPbSlotEvents dec.pts
  have hfit_split :
      FitsEvents M lim st (rustAllocEvents 384 8) ∧
      FitsEvents M lim (M.stepEvents (rustAllocEvents 384 8) st)
        ((dec.pts.map SortedSetPt.vec).flatMap decoderIntoPbSlotEvents) := by
    rw [hflat_map_eq]
    exact (fitsEvents_append M lim _ _ st).mp hfit_all
  rcases hfit_split with ⟨hfit384, hfit_loop⟩
  refine ⟨memRegion out protoPolynomialDecoderSize ∗ polyDecoderAt A.repAlloc decA dec ∗
      A.pool lim st s0 ∗ stackAt s0.sp decoderIntoPbStack, R,
      by simpa [sepConj_assoc] using hmem, ?_⟩
  dsimp only [decoderIntoPbSpec, polyDecoderAt, polyDecoderPtsNeededOff, polyDecoderIsCompleteOff,
    polyDecoderPadOff, polyDecoderPadSize, protoPolynomialDecoderSize, polyDecoderSize,
    BitVec.ofNat_eq_ofNat] at *
  let fsp := s0.sp - 160#64
  have hfsp : HiddenEq fsp (s0.sp - 160#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 160#64 hsp0 (by decide)
  conv => arg 4; rw [stackAt_decoderIntoPb_split s0.sp, ← hfsp.eq, stackAt_dropGluePoly16_split_bottom fsp]
  conv => arg 4; simp only [sepConj_assoc]
  refine SepWPp.weaken_pre (P' :=
      ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗ memRegion out 40 ∗ cells fsp 20 ∗
      sortedSetPtListOf A.repAlloc decA dec.pts ∗
      ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
      ((decA + 392#64) ↦₈ boolByte dec.isComplete) ∗ memRegion (decA + 393#64) 7 ∗
      A.pool lim st s0 ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack)
      (Entails.of_eq (by sep_ac_rfl)) ?_
  refine sepWPp_elim_pure fun ⟨hpts_len, _⟩ => ?_
  rw [sortedSetPtListOf_eq_vecPtListOf]
  conv => arg 4; simp only [memRegion_40_split out, cells20_fsp_eq fsp, sepConj_assoc, sepExists_sepConj_left]
  conv => arg 4; simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 => SepWPp.exists_elim fun d2 =>
    SepWPp.exists_elim fun d3 => SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun v0 =>
    SepWPp.exists_elim fun v1 => SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
    SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 => SepWPp.exists_elim fun v6 =>
    SepWPp.exists_elim fun v7 => SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 =>
    SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v11 => SepWPp.exists_elim fun v12 =>
    SepWPp.exists_elim fun v13 => SepWPp.exists_elim fun v14 => SepWPp.exists_elim fun v15 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v17 => SepWPp.exists_elim fun v18 =>
    SepWPp.exists_elim fun v19 => ?_
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (into_pb_prologue_and_init_placed hshim halloc s0 fsp out decA hfsp hfsp_align
      dec.ptsNeeded dec.isComplete st hfit384
      v0 v1 v2 v3 v4 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18 v19
      (vecPtListOf A.repAlloc decA (dec.pts.map SortedSetPt.vec) ∗ (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗
        ((out + 16#64) ↦₆₄ d2) ∗ ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        ((fsp + 40#64) ↦₆₄ v5) ∗ ((fsp + 48#64) ↦₆₄ v6) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
        ((fsp + 88#64) ↦₆₄ v11) ∗ memRegion (fsp - 4128#64) 32) ‹_› ‹_› ‹_› ‹_› ?_)
  intro s1 ptr_pts hptr_pts hpc1 hrun1 hacp01 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1 hvregs1
  let s_ref := withSaved19_20 s0 decA out
  have hrem_len : (dec.pts.map SortedSetPt.vec).length = 16 := by simp [hpts_len, NUM_POLYS, CHUNK_SIZE]
  have hrem_ne : dec.pts.map SortedSetPt.vec ≠ [] := by intro h; simp [h] at hrem_len
  generalize hQ_goal : (fun (sf : State) (P_f : SepProp) => _ ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q_goal
  generalize hQp_goal : (fun (sf : State) (P_f : SepProp) => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R)) = Qp_goal
  have hloop := pts_outer_loop_placed (Q := Q_goal) (Qp := Qp_goal) hshim halloc s_ref fsp ptr_pts hfsp_align
    (dec.pts.map SortedSetPt.vec) hrem_ne 0 (by omega)
    (M.stepEvents (rustAllocEvents 384 8) st) hfit_loop v5 v6 v7 s1
    (((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
      ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
      ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
      ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
      (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
      ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
      memRegion (decA + 384#64) 16 ∗ A.live ptr_pts 384 8 ∗ memRegion (fsp - 4128#64) 32)
    hpc1 hrun1 hsp1 hx29_1 (by simpa [s_ref] using hx19_1) (by simpa [s_ref] using hx20_1)
    hx22_1 hx23_1 hx24_1 (by simpa [s_ref] using hx28_1)
    (by simpa [s_ref] using htr1) (by simpa [s_ref] using hvregs1)
  dsimp only [s_ref] at hloop
  simp only [withSaved19_20_lr, withSaved19_20_x19, withSaved19_20_x20, withSaved19_20_x28,
    withSaved19_20_trace, withSaved19_20_vregs, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, hrem_len] at hloop
  change _ → SepWPp _ _ _ _ _ _ at hloop
  refine SepWPp.weaken_pre (by dsimp only [vecPtListOf]; exact Entails.of_eq (by sep_ac_rfl)) (hloop ?_)
  intro s2 w40 w48 w56 hpc2 hrun2 hacp12 hsp2 hx29_2 hx19_2 hx20_2 hx28_2 htr2 hvregs2
  let st_alloc := M.stepEvents ((dec.pts.map SortedSetPt.vec).flatMap decoderIntoPbSlotEvents)
    (M.stepEvents (rustAllocEvents 384 8) st)
  have hst_alloc_eq : st_alloc = M.stepEvents (decoderIntoPbAllocEvents dec) st := by
    dsimp only [st_alloc, decoderIntoPbAllocEvents]
    rw [hflat_map_eq, ← M.stepEvents_append]
  have hep := into_pb_epilogue_placed hdrop s0 fsp out decA hfsp
    (BitVec.ofNat 32 dec.ptsNeeded) 16#32 v4 (boolByte dec.isComplete)
    hfsp_align (dec.pts.map SortedSetPt.vec) (by simp [hpts_len]) st_alloc
    16#64 ptr_pts 16#64 w40 w48 w56 v11 d0 d1 d2 d3 d4 s2
    (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptr_pts
        ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗ A.live ptr_pts 384 8)
    hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 htr2 hvregs2
  have hpre2 :
      ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
        ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        arrayAt (fun pts addr => vecPtOf A.repAlloc addr pts) 24 decA (dec.pts.map SortedSetPt.vec) ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptr_pts
          ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
        A.pool lim st_alloc s2 ∗ stackAt fsp allocHookStack ∗
        (((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
          ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
          (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
          ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
          memRegion (decA + 384#64) 16 ∗ A.live ptr_pts 384 8 ∗ memRegion (fsp - 4128#64) 32)) ⊢
      ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
        ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
        ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
        ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        vecPtListOf A.repAlloc decA (dec.pts.map SortedSetPt.vec) ∗ memRegion (decA + 384#64) 16 ∗
        A.pool lim st_alloc s2 ∗ stackAt fsp dropGluePoly16Stack ∗
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptr_pts
            ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗ A.live ptr_pts 384 8)) := by
    rw [stackAt_dropGluePoly16_split_bottom fsp]; dsimp only [vecPtListOf]; exact Entails.of_eq (by sep_ac_rfl)
  subst hQ_goal; subst hQp_goal
  refine SepWPp.weaken_pre hpre2 (SepWPp.of_sepWP_ret ?_)
  refine SepWP.mono hep fun sf P_f hpcf hrunf
    ⟨evs_free, hfree, hp_ent, hacp2f, hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hx30f, htrf, hvregsf⟩ => ?_
  have hacp_all : AllocCallPreserved s0 sf := hacp01.trans (hacp12.trans hacp2f)
  have hpost_dec :
      ((out ↦₆₄ 16#64) ∗ ((out + 8#64) ↦₆₄ ptr_pts) ∗ ((out + 16#64) ↦₆₄ 16#64) ∗
        ((out + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗
        ((out + 28#64) ↦₃₂ 16#32) ∗
        ((out + 32#64) ↦₈ boolByte dec.isComplete) ∗
        memRegion (out + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptr_pts
          ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
        A.live ptr_pts 384 8) ⊢
      protoPolynomialDecoderAt A.repAlloc out dec.intoPb := by
    simpa only [RustCliAllocBudget.repAlloc] using
      protoPolynomialDecoderAt_entails A.repAlloc out ptr_pts dec hpts_len hptr_pts
  have hst_final : M.stepEvents evs_free st_alloc =
      M.stepEvents (decoderIntoPbAllocEvents dec ++ evs_free) st := by
    rw [hst_alloc_eq, ← M.stepEvents_append]
  have henv_final : DecoderIntoPbEnv dec (decoderIntoPbAllocEvents dec ++ evs_free) :=
    ⟨decoderIntoPbAllocEvents dec, evs_free, rfl, rfl, hfree⟩
  refine ⟨fun hmem_f => ?_,
    hspf, ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f.trans hx28_2, hx29f, hvregsf⟩⟩
  have h1 : P_f ∗ R ⊢
      (protoPolynomialDecoderAt A.repAlloc out dec.intoPb ∗
        memRegion decA 400 ∗
        A.pool lim (M.stepEvents (decoderIntoPbAllocEvents dec ++ evs_free) st) sf ∗
        stackAt s0.sp decoderIntoPbStack) ∗ R := by
    refine sepConj_mono_left (Entails.trans hp_ent ?_)
    rw [hst_final]
    refine Entails.trans ?_
      (Entails.trans
        (sepConj_mono_left (Q := memRegion decA 400 ∗
          A.pool lim (M.stepEvents (decoderIntoPbAllocEvents dec ++ evs_free) st) sf ∗
          stackAt s0.sp decoderIntoPbStack) hpost_dec)
        (Entails.of_eq (by sep_ac_rfl)))
    exact Entails.of_eq (by sep_ac_rfl)
  have hm1 := Satisfies.mono h1 hmem_f
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨decoderIntoPbAllocEvents dec ++ evs_free, ?_⟩
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htrf, hacp_all, henv_final⟩, by simpa only [sepConj_assoc] using hm1⟩

theorem decoder_into_pb_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdrop : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim)) :
    DecoderIntoPbPlacedOkX M A lim ext :=
  decoderIntoPbSpecX_of_decoderIntoPbSpec
    (decoder_into_pb_placed_ok_ext hshim_sat halloc_sat hdrop)

end LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbProofBudget
