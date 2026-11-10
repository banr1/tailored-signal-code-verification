/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFullPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoop
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Main Loop for `<PolyDecoder as Decoder>::decoded_message`

Threads `RustCliAllocBudget M` and `DecodedMessageLoopEnv` through the evaluation and interpolation
loop (`+548..+1404`) on Block `418`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement blkPC_418 blkPl_418 lsmpl)
open scoped CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly PolyDecoder u16ToBeBytes)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec sessionShimSpec)
open CryptoVerification.SpqrV1.Alloc
  (spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (ptSliceAt sortedSetPtListPinAt)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (PolyDecoderStrictSorted bsearchLoop bsearchLoop_bounds ptSliceAt_split_take_drop)
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.ComputeAt (computeAtPure computeAtStack)
open CryptoVerification.SpqrV1.Poly.DecodedMessage
  (bv64_and15_ofNat bv64_ofNat_mul2_comm bv64_ofNat_one_add_mul2 bv64_umaddl24_mod16
   collectedSlices decodedMessageLoopTotal decodedMessageLoopTotal_step_found
   decodedMessageLoopTotal_step_not_found interpolateScratchAt lagrangeInterpolateTotal
   necessaryPoints_pos_of_lt optPolyCacheListAt optPolyCacheListAt_focus optPolyCacheListAt_set
   optPolyCacheSlotAt polyDecoderStrictSorted_elem_length_le ptSliceRefAt
   ptSliceRefListAt ptSliceRefListAt_focus sortedSetPtListPinAt_focus sortedSetPtPinAt_eq_slice
   sortedSetPtPinRest sp96_sub104 sp96_sub112 sp96_sub120 spqrRustDeallocSym
   stackAt_computeAt_eq_prepare traceVRegs)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (lagrangeCompletePlacedSpec)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (lagrangePrepareStack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget (computeAtPlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (DecodedMessageLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFullPlacedBudget
  (lagrangeInterpolate_inlined_placed_sepWP)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopPlacedBudgetAux
  (decodedMessageLoopEnv_not_found_split decodedMessageLoopEnv_step_found
   decodedMessage_bsearchStep_placed_sepWP decodedMessage_computeAtStep_placed_sepWP
   decodedMessage_pushTwoBytes_placed_sepWP)
open LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
  (lagrangePreparePlacedSpec)

export LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopPlacedBudgetAux
  (decodedMessage_bsearchStep_placed_sepWP decodedMessage_computeAtStep_placed_sepWP
   decodedMessage_computeAtStep_placed_wpp decodedMessage_pushTwoBytes_placed_sepWP)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  sp96_sub120 sp96_sub112 sp96_sub104
  bv64_and15_ofNat bv64_umaddl24_mod16
  bv64_ofNat_mul2_comm bv64_ofNat_one_add_mul2

/-! ## Full Budget-Threaded Main Loop (`entry + 548#64` to `entry + 1404#64`) -/

/-- Full evaluation/interpolation loop (`[LibsignalPlacement]`, `SepWP`):
    executes `rem + 1` iterations from `i` to `dec.ptsNeeded`, matching
    `decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (rem + 1) polys out` and
    threading `DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (rem + 1) polys`. -/
theorem decodedMessageLoop_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (lagrangePreparePlacedSpec M A lim))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withVmPreserved lagrangeCompletePlacedSpec))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (computeAtPlacedSpec M A lim))
    (dec : PolyDecoder) (sp0 pts_base pts_vec_ptr out_ptr : BitVec 64)
    (pins : List VecPin)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hsort : PolyDecoderStrictSorted dec)
    (hneed_le : dec.ptsNeeded ≤ 16 * 65536)
    (hall_ge : ∀ k (hk : k < 16), dec.necessaryPoints k ≤ (dec.pts[k]'(by omega)).vec.length)
    (s0 : State) (F : SepProp) (post : State → SepProp → Prop) :
    ∀ (rem i : Nat) (polys : List (Option Poly)) (out : List (BitVec 8)) (st : M.σ) (s : State),
      FitsEnv M lim st (DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (rem + 1) polys) →
      i + (rem + 1) = dec.ptsNeeded →
      polys.length = 16 →
      out.length = 2 * i →
      s.pc = (blkPl_418).base + 548#64 →
      s.status = .Running →
      s.sp = sp0 - 672#64 →
      traceVRegs s = traceVRegs s0 →
      s.readReg64 .x20 = pts_base →
      s.readReg64 .x22 = BitVec.ofNat 64 i →
      s.readReg64 .x23 = BitVec.ofNat 64 (2 * i) →
      s.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded →
      s.readReg64 .x25 = 24#64 →
      s.readReg64 .x26 = sp0 - 600#64 →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ (sf : State) (evs : List AllocEvent),
        DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (rem + 1) polys evs →
        sf.pc = (blkPl_418).base + 1404#64 →
        sf.status = .Running →
        sf.sp = sp0 - 672#64 →
        traceVRegs sf = traceVRegs s0 →
        sf.readReg64 .x29 = sp0 - 96#64 →
        let (polysFinal, outFinal) :=
          decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (rem + 1) polys out
        SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
          (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polysFinal ∗
            ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
            ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
            ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
            (out_ptr ↦ₛ outFinal) ∗
            interpolateScratchAt sp0 ∗
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          post) →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
        (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polys ∗
          ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
          sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
          (out_ptr ↦ₛ out) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
          interpolateScratchAt sp0 ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F)
        post
  | rem, i, polys, out, st, s, hfit, hsum, hpolys_len, hout_len,
      hpc, hstat, hsp, htr, hx20, hx22, hx23, hx24, hx25, hx26, hx29, hnext => by
    have hi_lt : i < dec.ptsNeeded := by omega
    have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
    have hpoly_pts : i % 16 < dec.pts.length := by omega
    have hpoly_pins : i % 16 < pins.length := by omega
    have hpoly_p : i % 16 < polys.length := by omega
    have hnec_pos : 1 ≤ dec.necessaryPoints (i % 16) := necessaryPoints_pos_of_lt dec hi_lt
    have hnec_le_len : dec.necessaryPoints (i % 16) ≤ (dec.pts[i % 16]'hpoly_pts).vec.length :=
      hall_ge (i % 16) hpoly_lt
    have hle_len : (dec.pts[i % 16]'hpoly_pts).vec.length ≤ 65536 :=
      polyDecoderStrictSorted_elem_length_le hsort hpoly_pts
    have hge_len : 1 ≤ (dec.pts[i % 16]'hpoly_pts).vec.length := by omega
    have ⟨_, hb_lt0⟩ := bsearchLoop_bounds (dec.pts[i % 16]'hpoly_pts).vec
      (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length hge_len (by omega)
    have hb_lt : bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0
        (dec.pts[i % 16]'hpoly_pts).vec.length < (dec.pts[i % 16]'hpoly_pts).vec.length := by
      omega
    cases hfound :
      ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec
        (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).x.value ==
        BitVec.ofNat 16 (i / 16)
    · -- Not found (`entry + 660#64`): interpolate (if needed), then `compute_at`, then push 2 bytes
      refine SepWP.weaken_pre ?_
        (decodedMessage_bsearchStep_placed_sepWP (ext := ext) (A := A.repAlloc)
          dec sp0 pts_base pins i hpts hpins hi_lt hneed_le hge_len hle_len
          s
          (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polys ∗
            ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
            ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            (out_ptr ↦ₛ out) ∗
            memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
            interpolateScratchAt sp0 ∗
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          post hpc hstat hx20 hx22 hx23 hx24 hx25 hx26 hx29 ?_ ?_)
      · exact Entails.of_eq (by sep_ac_rfl)
      · dsimp only
        intro _ htrue
        rw [hfound] at htrue
        cases htrue
      · dsimp only
        intro _ hnot_found s1 hpc1 hrun1 hsp1 htr1 hvm1 hx0_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1
          hx29_1
        conv => arg 4; rw [← A.pool_of_vmPreserved hvm1]
        have hstep_pure := decodedMessageLoopTotal_step_not_found dec hpts hsort hpolys_len
          (rem := rem) (out := out) rfl hb_lt hnot_found
        obtain ⟨hfit_interp, hsplit_env⟩ :=
          decodedMessageLoopEnv_not_found_split dec hpts hsort hpolys_len rfl hb_lt hnot_found hfit
        let ptsSlice := (dec.pts[i % 16]'hpoly_pts).vec.take (dec.necessaryPoints (i % 16))
        let pInterp := (polys[i % 16]'hpoly_p).getD (lagrangeInterpolateTotal ptsSlice)
        let yInterp := computeAtPure pInterp (GF16.new (BitVec.ofNat 16 (i / 16)))
        have hslice_len : ptsSlice.length = dec.necessaryPoints (i % 16) :=
          List.length_take_of_le hnec_le_len
        have hk_pos : 1 ≤ ptsSlice.length := by rw [hslice_len]; exact hnec_pos
        have hk_le : ptsSlice.length ≤ 65536 := by rw [hslice_len]; omega
        have hfocus_pre :
            sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
              (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polys ∗
                ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
                ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
                ((sp0 - 608#64) ↦₆₄ 16#64) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                interpolateScratchAt sp0 ∗
                reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s1 ∗
                stackAt (sp0 - 672#64) computeAtStack ∗ F) =
            optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16)))
                (polys[i % 16]'hpoly_p) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16)))
                (pins[i % 16]'hpoly_pins).ptr ptsSlice.length ∗
              ptSliceAt (pins[i % 16]'hpoly_pins).ptr ptsSlice ∗
              interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s1 ∗
              stackAt (sp0 - 672#64) lagrangePrepareStack ∗
              (optPolyCacheListAt A.repAlloc (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A.repAlloc
                  ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr (pins.take (i % 16)) ∗
                ptSliceRefListAt dec (i % 16 + 1)
                  (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16 + 1))) (pins.drop (i % 16 + 1)) ∗
                sortedSetPtListPinAt A.repAlloc pts_base (pins.take (i % 16))
                  (dec.pts.take (i % 16)) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ (pins[i % 16]'hpoly_pins).cap) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 8#64) ↦₆₄
                  (pins[i % 16]'hpoly_pins).ptr) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 16#64) ↦₆₄
                  BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length) ∗
                ptSliceAt
                  ((pins[i % 16]'hpoly_pins).ptr + BitVec.ofNat 64 (4 * dec.necessaryPoints (i % 16)))
                  ((dec.pts[i % 16]'hpoly_pts).vec.drop (dec.necessaryPoints (i % 16))) ∗
                sortedSetPtPinRest A.repAlloc (pins[i % 16]'hpoly_pins)
                  (dec.pts[i % 16]'hpoly_pts) ∗
                sortedSetPtListPinAt A.repAlloc (pts_base + BitVec.ofNat 64 (24 * (i % 16 + 1)))
                  (pins.drop (i % 16 + 1)) (dec.pts.drop (i % 16 + 1)) ∗
                ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                memRegion ((sp0 - 672#64) - 4352#64) 48 ∗ F) := by
          rw [optPolyCacheListAt_focus A.repAlloc polys (i % 16) (sp0 - 600#64) hpoly_p,
            ptSliceRefListAt_focus dec pins (i % 16) pts_vec_ptr hpoly_pins,
            sortedSetPtListPinAt_focus A.repAlloc pins dec.pts (i % 16) pts_base
              (by rw [hpins, hpts]) hpoly_pts,
            sortedSetPtPinAt_eq_slice A.repAlloc (pins[i % 16]'hpoly_pins)
              (dec.pts[i % 16]'hpoly_pts) (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
            ptSliceAt_split_take_drop (dec.pts[i % 16]'hpoly_pts).vec
              (dec.necessaryPoints (i % 16)) (pins[i % 16]'hpoly_pins).ptr hnec_le_len,
            stackAt_computeAt_eq_prepare (sp0 - 672#64), hslice_len]
          sep_ac_rfl
        refine SepWP.weaken_pre (Entails.of_eq hfocus_pre)
          (lagrangeInterpolate_inlined_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
            hprep hcomp sp0 pts_vec_ptr (pins[i % 16]'hpoly_pins).ptr
            (BitVec.ofNat 64 dec.ptsNeeded) hsp0 (i % 16) (polys[i % 16]'hpoly_p) ptsSlice
            hpoly_lt hk_pos hk_le st hfit_interp s0 s1 _ post
            hpc1 hrun1 (by rw [hsp1, hsp]) (by rw [htr1, htr])
            hx0_1 hx24_1 hx25_1 hx26_1 hx29_1 ?_)
        intro s2 evs1 he1 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx22_2 hx24_2 hx25_2 hx26_2 hx29_2
        obtain ⟨hfit_ca, hsplit_ca⟩ := hsplit_env evs1 he1
        have hreasm_mid :
            optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16)))
                (some pInterp) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16)))
                (pins[i % 16]'hpoly_pins).ptr ptsSlice.length ∗
              ptSliceAt (pins[i % 16]'hpoly_pins).ptr ptsSlice ∗
              interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs1 st) s2 ∗
              stackAt (sp0 - 672#64) lagrangePrepareStack ∗
              (optPolyCacheListAt A.repAlloc (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A.repAlloc
                  ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr (pins.take (i % 16)) ∗
                ptSliceRefListAt dec (i % 16 + 1)
                  (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16 + 1))) (pins.drop (i % 16 + 1)) ∗
                sortedSetPtListPinAt A.repAlloc pts_base (pins.take (i % 16))
                  (dec.pts.take (i % 16)) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ (pins[i % 16]'hpoly_pins).cap) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 8#64) ↦₆₄
                  (pins[i % 16]'hpoly_pins).ptr) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 16#64) ↦₆₄
                  BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length) ∗
                ptSliceAt
                  ((pins[i % 16]'hpoly_pins).ptr + BitVec.ofNat 64 (4 * dec.necessaryPoints (i % 16)))
                  ((dec.pts[i % 16]'hpoly_pts).vec.drop (dec.necessaryPoints (i % 16))) ∗
                sortedSetPtPinRest A.repAlloc (pins[i % 16]'hpoly_pins)
                  (dec.pts[i % 16]'hpoly_pts) ∗
                sortedSetPtListPinAt A.repAlloc (pts_base + BitVec.ofNat 64 (24 * (i % 16 + 1)))
                  (pins.drop (i % 16 + 1)) (dec.pts.drop (i % 16 + 1)) ∗
                ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                memRegion ((sp0 - 672#64) - 4352#64) 48 ∗ F) =
            optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16)))
                (some pInterp) ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
              ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs1 st) s2 ∗
              stackAt (sp0 - 672#64) computeAtStack ∗
              (optPolyCacheListAt A.repAlloc (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A.repAlloc
                  ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
                ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
                ((sp0 - 608#64) ↦₆₄ 16#64) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
                sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                interpolateScratchAt sp0 ∗ F) := by
          rw [ptSliceRefListAt_focus dec pins (i % 16) pts_vec_ptr hpoly_pins,
            sortedSetPtListPinAt_focus A.repAlloc pins dec.pts (i % 16) pts_base
              (by rw [hpins, hpts]) hpoly_pts,
            sortedSetPtPinAt_eq_slice A.repAlloc (pins[i % 16]'hpoly_pins)
              (dec.pts[i % 16]'hpoly_pts) (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
            ptSliceAt_split_take_drop (dec.pts[i % 16]'hpoly_pts).vec
              (dec.necessaryPoints (i % 16)) (pins[i % 16]'hpoly_pins).ptr hnec_le_len,
            stackAt_computeAt_eq_prepare (sp0 - 672#64), hslice_len]
          sep_ac_rfl
        refine SepWP.weaken_pre (Entails.of_eq hreasm_mid)
          (decodedMessage_computeAtStep_placed_sepWP hcomp_at sp0
            ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) hsp0 i dec.ptsNeeded pInterp
            hi_lt hneed_le (M.stepEvents evs1 st) hfit_ca s0 s2 _ post
            hpc2 hrun2 hsp2 htr2 hx19_2 (by rw [hx22_2, hx22_1]) hx29_2 ?_)
        intro s3 evs2 he2 hpc3 hrun3 hsp3 htr3 hx19_3 hx21_3 hx20_3 hx22_3 hx23_3 hx24_3 hx25_3
          hx26_3 hx29_3
        obtain ⟨hfit_rest, hmk_env⟩ := hsplit_ca evs2 he2
        have hset_polys :
            optPolyCacheListAt A.repAlloc (sp0 - 600#64) (polys.take (i % 16)) ∗
              optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16)))
                (some pInterp) ∗
              optPolyCacheListAt A.repAlloc
                ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) =
            optPolyCacheListAt A.repAlloc (sp0 - 600#64) (polys.set (i % 16) (some pInterp)) :=
          (optPolyCacheListAt_set A.repAlloc polys (i % 16) (some pInterp) (sp0 - 600#64) hpoly_p).symm
        refine SepWP.weaken_pre ?_
          (decodedMessage_pushTwoBytes_placed_sepWP (ext := ext) sp0 out_ptr
            (BitVec.ofNat 64 (2 * i)) i dec.ptsNeeded out yInterp.value hi_lt hneed_le hout_len s3
            (optPolyCacheListAt A.repAlloc (sp0 - 600#64) (polys.set (i % 16) (some pInterp)) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
              sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
              interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
              A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s3 ∗
              stackAt (sp0 - 672#64) computeAtStack ∗ F)
            post hpc3 hrun3 hx19_3 hx21_3 hx22_3 hx23_3 (by rw [hx24_3, hx24_2]) hx29_3 ?_)
        · rw [← hset_polys]
          exact Entails.of_eq (by sep_ac_rfl)
        intro s4 hpc4 hrun4 hsp4 htr4 hvm4 hx20_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4
        conv => arg 4; rw [← A.pool_of_vmPreserved hvm4]
        cases rem with
        | zero =>
          have hi1_eq : i + 1 = dec.ptsNeeded := by omega
          simp only [hi1_eq, ↓reduceIte] at hpc4
          have hrem0 : dec.ptsNeeded - (i + 1) = 0 := by omega
          rw [hrem0, Nat.mul_zero, memRegion_zero]
          have hloop0 :
              decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (0 + 1) polys out =
                (polys.set (i % 16) (some pInterp), out ++ u16ToBeBytes yInterp.value) := by
            rw [hstep_pure]; rfl
          rw [hloop0] at hnext
          have hevs_tot :
              DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (0 + 1) polys
                (evs1 ++ evs2 ++ []) :=
            hmk_env [] rfl
          have hst_eq :
              M.stepEvents evs2 (M.stepEvents evs1 st) =
                M.stepEvents (evs1 ++ evs2 ++ []) st := by
            simp [← M.stepEvents_append]
          rw [hst_eq]
          refine SepWP.weaken_pre ?_
            (hnext s4 (evs1 ++ evs2 ++ []) hevs_tot hpc4 hrun4
              (by rw [hsp4, hsp3]) (by rw [htr4, htr3]) hx29_4)
          rw [hi1_eq]
          exact Entails.of_eq (by sep_ac_rfl)
        | succ rem' =>
          have hi1_ne : i + 1 ≠ dec.ptsNeeded := by omega
          simp only [hi1_ne, ↓reduceIte] at hpc4
          refine SepWP.weaken_pre ?_
            (decodedMessageLoop_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
              hprep hcomp hcomp_at dec sp0 pts_base pts_vec_ptr out_ptr pins
              hsp0 hpts hpins hsort hneed_le hall_ge s0 F post
              rem' (i + 1) (polys.set (i % 16) (some pInterp))
              (out ++ u16ToBeBytes yInterp.value)
              (M.stepEvents evs2 (M.stepEvents evs1 st)) s4 hfit_rest
              (by omega) (by simp [hpolys_len]) (by simp [hout_len, u16ToBeBytes]; omega)
              hpc4 hrun4 (by rw [hsp4, hsp3]) (by rw [htr4, htr3])
              (by rw [hx20_4, hx20_3, hx20_2, hx20_1]) hx22_4 hx23_4 hx24_4
              (by rw [hx25_4, hx25_3, hx25_2]) (by rw [hx26_4, hx26_3, hx26_2]) hx29_4
              (fun sf evs3 he3 hpc_f hrun_f hsp_f htr_f hx29_f => ?_))
          · exact Entails.of_eq (by sep_ac_rfl)
          · rw [← hstep_pure]
            have hst_eq :
                M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st)) =
                  M.stepEvents (evs1 ++ evs2 ++ evs3) st := by
              simp [← M.stepEvents_append]
            rw [hst_eq]
            exact hnext sf (evs1 ++ evs2 ++ evs3) (hmk_env evs3 he3) hpc_f hrun_f hsp_f htr_f hx29_f
    · -- Found in `dec.pts[i % 16]` at `entry + 1328#64`
      refine SepWP.weaken_pre ?_
        (decodedMessage_bsearchStep_placed_sepWP (ext := ext) (A := A.repAlloc)
          dec sp0 pts_base pins i hpts hpins hi_lt hneed_le hge_len hle_len
          s
          (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polys ∗
            ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
            ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            (out_ptr ↦ₛ out) ∗
            memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
            interpolateScratchAt sp0 ∗
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          post hpc hstat hx20 hx22 hx23 hx24 hx25 hx26 hx29 ?_ ?_)
      · exact Entails.of_eq (by sep_ac_rfl)
      · dsimp only
        intro _ hfound' s1 hpc1 hrun1 hsp1 htr1 hvm1 hx19_1 hx21_1 hx20_1 hx22_1 hx23_1 hx24_1
          hx25_1 hx26_1 hx29_1
        conv => arg 4; rw [← A.pool_of_vmPreserved hvm1]
        have hstep_pure := decodedMessageLoopTotal_step_found dec hpts hsort
          (rem := rem) (polys := polys) (out := out) rfl hb_lt hfound'
        have henv_found := decodedMessageLoopEnv_step_found dec hpts hsort
          (rem := rem) (polys := polys) rfl hb_lt hfound'
        refine SepWP.weaken_pre ?_
          (decodedMessage_pushTwoBytes_placed_sepWP (ext := ext) sp0 out_ptr
            (BitVec.ofNat 64 (2 * i)) i dec.ptsNeeded out
            ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec
              (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value
            hi_lt hneed_le hout_len s1
            (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polys ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
              sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
              interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s1 ∗
              stackAt (sp0 - 672#64) computeAtStack ∗ F)
            post hpc1 hrun1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx29_1 ?_)
        · exact Entails.of_eq (by sep_ac_rfl)
        intro s2 hpc2 hrun2 hsp2 htr2 hvm2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2
        conv => arg 4; rw [← A.pool_of_vmPreserved hvm2]
        cases rem with
        | zero =>
          have hi1_eq : i + 1 = dec.ptsNeeded := by omega
          simp only [hi1_eq, ↓reduceIte] at hpc2
          have hrem0 : dec.ptsNeeded - (i + 1) = 0 := by omega
          rw [hrem0, Nat.mul_zero, memRegion_zero]
          have hloop0 :
              decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (0 + 1) polys out =
                (polys, out ++ u16ToBeBytes
                  ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec
                    (BitVec.ofNat 16 (i / 16)) 0
                    (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value) := by
            rw [hstep_pure]; rfl
          rw [hloop0] at hnext
          have henv0 : DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (0 + 1) polys [] := by
            rw [henv_found]; rfl
          have hst_nil : st = M.stepEvents [] st := rfl
          rw [hst_nil]
          refine SepWP.weaken_pre ?_
            (hnext s2 [] henv0 hpc2 hrun2 (by rw [hsp2, hsp1, hsp])
              (by rw [htr2, htr1, htr]) hx29_2)
          rw [hi1_eq]
          exact Entails.of_eq (by sep_ac_rfl)
        | succ rem' =>
          have hi1_ne : i + 1 ≠ dec.ptsNeeded := by omega
          simp only [hi1_ne, ↓reduceIte] at hpc2
          have hfit' :
              FitsEnv M lim st
                (DecodedMessageLoopEnv dec (collectedSlices dec 0 16) (i + 1) (rem' + 1) polys) := by
            rwa [← henv_found]
          refine SepWP.weaken_pre ?_
            (decodedMessageLoop_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
              hprep hcomp hcomp_at dec sp0 pts_base pts_vec_ptr out_ptr pins
              hsp0 hpts hpins hsort hneed_le hall_ge s0 F post
              rem' (i + 1) polys
              (out ++ u16ToBeBytes
                ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec
                  (BitVec.ofNat 16 (i / 16)) 0
                  (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value)
              st s2 hfit' (by omega) hpolys_len (by simp [hout_len, u16ToBeBytes]; omega)
              hpc2 hrun2 (by rw [hsp2, hsp1, hsp]) (by rw [htr2, htr1, htr])
              (by rw [hx20_2, hx20_1]) hx22_2 hx23_2 hx24_2
              (by rw [hx25_2, hx25_1]) (by rw [hx26_2, hx26_1]) hx29_2
              (fun sf evs hevs hpc_f hrun_f hsp_f htr_f hx29_f => ?_))
          · exact Entails.of_eq (by sep_ac_rfl)
          · rw [← hstep_pure]
            have hevs' :
                DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (rem' + 1 + 1) polys evs := by
              rwa [henv_found]
            exact hnext sf evs hevs' hpc_f hrun_f hsp_f htr_f hx29_f
      · dsimp only
        intro _ hfalse
        rw [hfound] at hfalse
        cases hfalse

theorem decodedMessageLoop_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (lagrangePreparePlacedSpec M A lim))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withVmPreserved lagrangeCompletePlacedSpec))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (computeAtPlacedSpec M A lim))
    (dec : PolyDecoder) (sp0 pts_base pts_vec_ptr out_ptr : BitVec 64)
    (pins : List VecPin)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hsort : PolyDecoderStrictSorted dec)
    (hneed_le : dec.ptsNeeded ≤ 16 * 65536)
    (hall_ge : ∀ k (hk : k < 16), dec.necessaryPoints k ≤ (dec.pts[k]'(by omega)).vec.length)
    (s0 : State) (F : SepProp)
    (Q Qp : State → SepProp → Prop) (oom : State → SepProp := fun _ => ⌜False⌝)
    (rem i : Nat) (polys : List (Option Poly)) (out : List (BitVec 8)) (st : M.σ) (s : State)
    (hfit : FitsEnv M lim st
      (DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (rem + 1) polys))
    (hsum : i + (rem + 1) = dec.ptsNeeded)
    (hpolys_len : polys.length = 16)
    (hout_len : out.length = 2 * i)
    (hpc : s.pc = (blkPl_418).base + 548#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (htr : traceVRegs s = traceVRegs s0)
    (hx20 : s.readReg64 .x20 = pts_base)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (2 * i))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx26 : s.readReg64 .x26 = sp0 - 600#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (rem + 1) polys evs →
      sf.pc = (blkPl_418).base + 1404#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      let (polysFinal, outFinal) :=
        decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (rem + 1) polys out
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polysFinal ∗
          ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
          sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
          (out_ptr ↦ₛ outFinal) ∗
          interpolateScratchAt sp0 ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polys ∗
        ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
        ((sp0 - 608#64) ↦₆₄ 16#64) ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
        ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
        ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
        ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
        sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
        (out_ptr ↦ₛ out) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
        interpolateScratchAt sp0 ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
        stackAt (sp0 - 672#64) computeAtStack ∗ F)
      Q Qp oom := by
  apply SepWPp.of_sepWP (mid := (blkPl_418).base + 1404#64)
  refine SepWP.mono (oom := fun _ => ⌜False⌝) ?_ (fun _ _ _ _ hp => hp)
  refine decodedMessageLoop_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
    hprep hcomp hcomp_at dec sp0 pts_base pts_vec_ptr out_ptr pins
    hsp0 hpts hpins hsort hneed_le hall_ge s0 F _
    rem i polys out st s hfit hsum hpolys_len hout_len
    hpc hstat hsp htr hx20 hx22 hx23 hx24 hx25 hx26 hx29 ?_
  intro sf evs hevs hpc_f hrun_f hsp_f htr_f hx29_f
  exact SepWP.done hpc_f hrun_f (hnext sf evs hevs hpc_f hrun_f hsp_f htr_f hx29_f)

end LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopPlacedBudget
