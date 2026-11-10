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
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.LoopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMessageBridgePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpilogue
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.ProofBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.ProofBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget

/-!
# `<PolyDecoder as Decoder>::decoded_message` (Block `418`, Part 2): Top-Level `RustCliAllocBudget` Proof

Completes the relocatable `[LibsignalPlacement]` proof of `<PolyDecoder as Decoder>::decoded_message`
(Block `418`) under `RustCliAllocBudget M`, `BudgetLimits`, and `DecodedMessageEnv`, discharging
cross-block calls to `computeAt` (Block `371`), `lagrangePrepare` (Block `372`), and
`lagrangeComplete` (Block `373`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_418 blkPl_418 extract_withLsCodeLoaded
   ls_subroutine_ok_of_block lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalSpqrV1 (CHUNK_SIZE NUM_POLYS PolyDecoder)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack memsetName sessionMemcpyRegionSpec sessionMemsetRegionSpec sessionShimSpec
  withLsCodeRoLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (
  spqrHandleErrorSym spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (
  boolByte polyDecoderAt polyDecoderIsCompleteOff polyDecoderPadOff polyDecoderPadSize
  polyDecoderPtsNeededOff sortedSetPtListOf sortedSetPtListPinAt vecHeaderBytes
)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted)
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.Poly.ComputeAt (computeAtStack)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (
  CalleeSavedGprsPreserved DecodedMessageGhost
  calleeSavedPreserved_of_gprs_traceVRegs
  collectPointsVecsTotal collectPointsVecs_false_bounds collectedSlices
  decodedMessageLoopTotal decodedMessageLoopTotal_fst_length decodedMessageLoopTotal_snd_length
  decodedMessageStack decodedMessageTotal
  decodedMessageTotal_of_collect_false decodedMessageTotal_of_collect_true
  decodedMessageTotal_of_isComplete_true decodedMessageTotal_of_ptsNeeded_zero
  exists_lt_necessaryPoints_of_collect_true
  interpolateScratchAt
  memRegion576_split_for_decodedMessage
  memRegion_24_8_8_8_entails_48 memRegion_384_24_96_entails_504
  memRegion_8_384_24_96_entails_512
  optPolyCacheListAt optVecU8Of polyDecoderStrictSorted_elem_length_le
  ptSliceRefListAt ptSliceRefListAt_entails_memRegion256
  reassemble_polyDecoderAt savedRegsAt scratch_and_pads_entails_regions
  sortedSetPtListOf_eq_exists_pins sortedSetPtListPinAt_entails_sortedSetPtListOf
  spqrRustDeallocSym
  stackAt_computeAt_eq_allocHook stackAt_decodedMessage_eq
  stackAt_extHook_eq_allocHook stackAt_extHook_eq_computeAt
  traceVRegs
)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (lagrangeCompletePlacedSpec)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
  rustCliReallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget (computeAtPlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (
  DecodedMessageEnv DecodedMessageLoopEnv DecodedMessagePlacedOkExt decodedMessagePlacedSpec
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpiloguePlacedBudget (
  decodedMessage_epilogue_from1904_placed_sepWP
  decodedMessage_epilogue_from288_placed_sepWP
  dropOptPolyCache_from1404_placed_sepWP
  dropOptPolyCache_from1460_placed_sepWP
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.LoopPlacedBudget (
  collectPointsVecs_none_loop_placed_sepWP
  collectPointsVecs_ok_loop_placed_sepWP
)
open LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.ProofBudget (computeAt_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofPlacedBudget
  (decodedMessage_finish_from1904_placed_sepWP)
open LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.ProofBudget
  (lagrangePrepare_placed_ok_of_hookSat)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (polyDecoderDecodedMessagePlacedSpec polyDecoderDecodedMessagePlacedSpecOfEnv
   polyDecoderDecodedMessagePlacedSpecOfPrePostEnv)
open CryptoVerification.SpqrV1.States.Leaves
  (PolyDecoderDecodedMessageGhost sepWP_seq_lscl
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMessageBridgePlacedBudget
  (polyDecodedMessagePlacedOkX_of_decodedMessage
   polyDecoderDecodedMessage_placed_cro_of_decodedMessage
   polyDecoderDecodedMessage_placed_cro_of_decodedMessage_ofEnv
   polyDecoderDecodedMessage_placed_cro_of_decodedMessage_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudgetAux
  (decodedMessageLoop_cl_placed_sepWP)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudgetAux2
  (lagrangeComplete_placed_vmPreserved_ok)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget
  (PolyDecodedMessagePlacedOkX)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofPlacedBudgetAux (
  allocOut_pos_placed_sepWP allocOut_pos_placed_wpp allocOut_pos_setup_placed_sepWP
  allocOut_zero_placed_sepWP
  decodedMessageEnv_of_collect_true decodedMessageEnv_of_isComplete_true
  decodedMessageEnv_of_ptsNeeded_pos decodedMessageEnv_of_ptsNeeded_zero
  decodedMessage_allocPv_placed_sepWP decodedMessage_allocPv_setup_placed_sepWP
  decodedMessage_isComplete_true_placed_sepWP decodedMessage_prologue_placed_sepWP
  fitsAfterCollect_of_collect_false fitsAllocPv_of_isComplete_false
  freeOnlyEvs_append freeOnlyEvs_dealloc256 initOptPolyCache_placed_sepWP
)
open LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget (lagrangePreparePlacedSpec)
open scoped CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff rustAllocEvents
attribute [local wp_norm ↓, local arm64_norm ↓] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## 1. Post-`collectPointsVecs` Execution (`+352` to Return) -/

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudgetAux2
  (lagrangeComplete_placed_vmPreserved_ok)
export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudgetAux
  (decodedMessage_computeAtStep_cl_placed_sepWP decodedMessage_computeAtStep_cl_placed_wpp
   decodedMessageLoop_cl_placed_sepWP decodedMessageLoop_cl_placed_wpp)

theorem decodedMessage_afterCollect_cl_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec M A lim)))
    (hcomp_ok : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec M A lim)))
    (dec : PolyDecoder) (decA out_sret pv_ptr : BitVec 64) (pins : List VecPin)
    (hcomp_false : dec.isComplete = false) (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hsort : PolyDecoderStrictSorted dec) (hret : (collectPointsVecsTotal dec 0 16 false []).1 = false)
    (st : M.σ)
    (hfit_after : dec.ptsNeeded ≠ 0 →
      FitsEvents M lim st (rustAllocEvents (2 * dec.ptsNeeded) 1) ∧
      FitsEnv M lim (M.stepEvents (rustAllocEvents (2 * dec.ptsNeeded) 1) st)
        (DecodedMessageLoopEnv dec (collectedSlices dec 0 16) 0 dec.ptsNeeded
          (List.replicate 16 none)))
    (s0 s : State) (F : SepProp) (post : State → SepProp → Prop)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 352#64)
    (hstat : s.status = .Running) (hsp : s.sp = s0.sp - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx20 : s.readReg64 .x20 = decA) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      DecodedMessageEnv dec (rustAllocEvents 256 8 ++ evs) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.sp = s0.sp →
      traceVRegs sf = traceVRegs s0 → CalleeSavedGprsPreserved s0 sf →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (optVecU8Of A.repAlloc out_sret (decodedMessageTotal dec) ∗
          sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp decodedMessageStack ∗ F) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
        ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
        memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
        interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
        memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
        ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
        stackAt (s0.sp - 672#64) extHookStack ∗ F) post := by
  have ⟨hall_ge, hneed_le⟩ := collectPointsVecs_false_bounds dec hpts hsort hret
  refine SepWP.weaken_pre
    (show _ ⊢
      ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ memRegion (s0.sp - 600#64) 384 ∗
        (savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
          ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
          memRegion (s0.sp - 216#64) 24 ∗ interpolateScratchAt s0.sp ∗
          memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
          memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
          ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
          stackAt (s0.sp - 672#64) extHookStack ∗ F) by
      exact Entails.of_eq (by sep_ac_rfl))
    (sepWP_seq_lscl hcl (mid := (blkPl_418).base + 424#64)
      (initOptPolyCache_placed_sepWP (ext := ext) (A := A.repAlloc)
        s0.sp (BitVec.ofNat 64 dec.ptsNeeded) hsp0 s _ _
        hpc hstat hsp (fun s1 hpc1 hrun1 hsp1 htr1 hvm1 hx20_1 hx24_1 hx29_1 =>
          SepWP.transport_budgetPool hvm1 (hnext :=
            SepWP.done hpc1 hrun1 fun hcl1 => ?_))))
  by_cases hneed0 : dec.ptsNeeded = 0
  · have hx24_0 : s1.readReg64 .x24 = 0#64 := by rw [hx24_1, hneed0]
    refine SepWP.weaken_pre
      (show _ ⊢
        memRegion (s0.sp - 216#64) 24 ∗
          (((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            optPolyCacheListAt A.repAlloc (s0.sp - 600#64) (List.replicate 16 none) ∗
            savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗
            ((s0.sp - 608#64) ↦₆₄ 16#64) ∗ interpolateScratchAt s0.sp ∗
            memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
            memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
            ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s1 ∗
            stackAt (s0.sp - 672#64) extHookStack ∗ F) by
        exact Entails.of_eq (by sep_ac_rfl))
      (allocOut_zero_placed_sepWP (ext := ext) s0.sp s1 _ post hpc1 hrun1 hsp1 hx24_0
        (by rw [hx29_1, hx29])
        (fun s2 hpc2 hrun2 hsp2 htr2 hvm2 hx29_2 => ?_))
    refine SepWP.transport_budgetPool hvm2 (hnext := ?_)
    rw [stackAt_extHook_eq_allocHook (s0.sp - 672#64)]
    refine SepWP.weaken_pre
      (show _ ⊢
        optPolyCacheListAt A.repAlloc (s0.sp - 600#64) (List.replicate 16 none) ∗
          ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 216#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 208#64) ↦₆₄ 1#64) ∗ ((s0.sp - 200#64) ↦₆₄ 0#64) ∗
          memRegion out_sret vecHeaderBytes ∗ A.pool lim st s2 ∗
          stackAt (s0.sp - 672#64) allocHookStack ∗
          (memRegion ((s0.sp - 672#64) - 16384#64) 12288 ∗ savedRegsAt s0.sp s0 ∗
            ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
            ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
            interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
            memRegion (s0.sp - 120#64) 24 ∗ A.live pv_ptr 256 8 ∗
            ptSliceRefListAt dec 0 pv_ptr pins ∗
            (sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ F)) by
        exact Entails.of_eq (by sep_ac_rfl))
      (dropOptPolyCache_from1460_placed_sepWP hdealloc_sat s0.sp out_sret hsp0 st s2 _ post
        hpc2 hrun2 hsp2 hx29_2 (fun s3 evsDrop hfreeDrop hpc3 hrun3 hsp3 htr3 _hacp3 => ?_))
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (decodedMessage_finish_from1904_placed_sepWP hdealloc_sat dec pins hpins s0 out_sret pv_ptr
        (BitVec.ofNat 64 dec.ptsNeeded) (some []) hsp0 (M.stepEvents evsDrop st) s3
        (sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ F) post
        hpc3 hrun3 hsp3 (fun sf hpc_f hrun_f hsp_f htr_f _hacp_f hcs_f => ?_))
    have htot := decodedMessageTotal_of_ptsNeeded_zero hcomp_false hpts hret hneed0
    have hevs_ok : DecodedMessageEnv dec
        (rustAllocEvents 256 8 ++ (evsDrop ++ rustDeallocEvents 256 8)) :=
      decodedMessageEnv_of_ptsNeeded_zero hcomp_false hret hneed0
        (freeOnlyEvs_append hfreeDrop freeOnlyEvs_dealloc256)
    refine SepWP.weaken_pre
      (show _ ⊢
        optVecU8Of A.repAlloc out_sret (decodedMessageTotal dec) ∗
          sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          A.pool lim (M.stepEvents (evsDrop ++ rustDeallocEvents 256 8) st) sf ∗
          stackAt s0.sp decodedMessageStack ∗ F by
        rw [htot, M.stepEvents_append]
        exact Entails.of_eq (by sep_ac_rfl))
      (hnext sf (evsDrop ++ rustDeallocEvents 256 8) hevs_ok
        hpc_f hrun_f hsp_f (by rw [htr_f, htr3, htr2, htr1, htr]) hcs_f)
  · have hge1 : 1 ≤ dec.ptsNeeded := Nat.pos_of_ne_zero hneed0
    obtain ⟨hfit_out, hfit_loop⟩ := hfit_after hneed0
    rw [stackAt_extHook_eq_computeAt (s0.sp - 672#64), stackAt_computeAt_eq_allocHook (s0.sp - 672#64)]
    refine SepWP.weaken_pre
      (show _ ⊢
        memRegion (s0.sp - 216#64) 24 ∗ A.pool lim st s1 ∗ stackAt (s0.sp - 672#64) allocHookStack ∗
          (((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            optPolyCacheListAt A.repAlloc (s0.sp - 600#64) (List.replicate 16 none) ∗
            savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗
            ((s0.sp - 608#64) ↦₆₄ 16#64) ∗ interpolateScratchAt s0.sp ∗
            memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
            memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
            ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ memRegion ((s0.sp - 672#64) - 4352#64) 256 ∗
            memRegion ((s0.sp - 672#64) - 16384#64) 12032 ∗ F) by
        exact Entails.of_eq (by sep_ac_rfl))
      (sepWP_seq_lscl hcl1 (mid := (blkPl_418).base + 548#64)
        (allocOut_pos_placed_sepWP hshim_sat halloc_sat s0.sp hsp0 dec.ptsNeeded hge1 hneed_le
          st hfit_out s0 s1 _ _
          hpc1 hrun1 hsp1 (by rw [htr1, htr]) hx24_1 (by rw [hx29_1, hx29])
          (fun out_ptr s2 hout_ne0 hpc2 hrun2 hsp2 htr2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 =>
            SepWP.done hpc2 hrun2 fun hcl2 => ?_)))
    have hrem_eq : dec.ptsNeeded - 1 + 1 = dec.ptsNeeded := by omega
    have hfit_loop' :
        FitsEnv M lim (M.stepEvents (rustAllocEvents (2 * dec.ptsNeeded) 1) st)
          (DecodedMessageLoopEnv dec (collectedSlices dec 0 16) 0 (dec.ptsNeeded - 1 + 1)
            (List.replicate 16 none)) := by
      simpa only [hrem_eq] using hfit_loop
    refine SepWP.weaken_pre
      (show _ ⊢
        optPolyCacheListAt A.repAlloc (s0.sp - 600#64) (List.replicate 16 none) ∗
          ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
          ((s0.sp - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ((s0.sp - 208#64) ↦₆₄ out_ptr) ∗ ((s0.sp - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * 0)) ∗
          ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
          (out_ptr ↦ₛ ([] : List (BitVec 8))) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * 0)) (2 * (dec.ptsNeeded - 0)) ∗
          interpolateScratchAt s0.sp ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          A.pool lim (M.stepEvents (rustAllocEvents (2 * dec.ptsNeeded) 1) st) s2 ∗
          stackAt (s0.sp - 672#64) computeAtStack ∗
          (savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ memRegion (s0.sp - 672#64) 8 ∗
            memRegion (s0.sp - 120#64) 24 ∗ memRegion out_sret vecHeaderBytes ∗
            A.live pv_ptr 256 8 ∗ A.live out_ptr (2 * dec.ptsNeeded) 1 ∗
            memRegion ((s0.sp - 672#64) - 16384#64) 12032 ∗ F) by
        rw [stackAt_computeAt_eq_allocHook (s0.sp - 672#64)]
        simp only [Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        exact Entails.of_eq (by sep_ac_rfl))
      (decodedMessageLoop_cl_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
        hprep hcomp_ok hcomp_at
        dec s0.sp decA pv_ptr out_ptr pins
        hsp0 hpts hpins hsort hneed_le hall_ge s0 _ post
        (dec.ptsNeeded - 1) 0 (List.replicate 16 none) []
        (M.stepEvents (rustAllocEvents (2 * dec.ptsNeeded) 1) st) s2
        hfit_loop' (by omega) (by simp) (by simp)
        hcl2 hpc2 hrun2 hsp2 htr2 (by rw [hx20_2, hx20_1, hx20]) hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2
        (fun s3 evsLoop hloopEvs hpc3 hrun3 hsp3 htr3 hx29_3 => ?_))
    rw [hrem_eq] at hloopEvs ⊢
    dsimp only
    have hpolys_len :
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded
          (List.replicate 16 none) []).1.length = 16 :=
      decodedMessageLoopTotal_fst_length dec (collectedSlices dec 0 16) dec.ptsNeeded 0
        (List.replicate 16 none) [] (by simp)
    have hout_len :
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded
          (List.replicate 16 none) []).2.length = 2 * dec.ptsNeeded := by
      simpa using decodedMessageLoopTotal_snd_length dec (collectedSlices dec 0 16) dec.ptsNeeded 0
        (List.replicate 16 none) []
    rw [stackAt_computeAt_eq_allocHook (s0.sp - 672#64)]
    have hmem256_12032 :
        memRegion ((s0.sp - 672#64) - 4352#64) 256 ∗ memRegion ((s0.sp - 672#64) - 16384#64) 12032 =
          memRegion ((s0.sp - 672#64) - 16384#64) 12288 := by
      have hsub : (s0.sp - 672#64) - 16384#64 + 12032#64 = (s0.sp - 672#64) - 4352#64 := by bv_omega
      rw [show (12288 : Nat) = 12032 + 256 from rfl,
        memRegion_split ((s0.sp - 672#64) - 16384#64) 12032 256 (by decide), hsub, sepConj_comm]
    refine SepWP.weaken_pre
      (show _ ⊢
        optPolyCacheListAt A.repAlloc (s0.sp - 600#64)
          (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded
            (List.replicate 16 none) []).1 ∗
          ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
          ((s0.sp - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ((s0.sp - 208#64) ↦₆₄ out_ptr) ∗
          ((s0.sp - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          memRegion out_sret vecHeaderBytes ∗ A.live out_ptr (2 * dec.ptsNeeded) 1 ∗
          (out_ptr ↦ₛ (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded
            (List.replicate 16 none) []).2) ∗
          A.pool lim (M.stepEvents evsLoop (M.stepEvents (rustAllocEvents (2 * dec.ptsNeeded) 1) st)) s3 ∗
          stackAt (s0.sp - 672#64) allocHookStack ∗
          (memRegion ((s0.sp - 672#64) - 16384#64) 12288 ∗ savedRegsAt s0.sp s0 ∗
            ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
            ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
            interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
            memRegion (s0.sp - 120#64) 24 ∗ A.live pv_ptr 256 8 ∗
            ptSliceRefListAt dec 0 pv_ptr pins ∗
            (sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ F)) by
        rw [← hmem256_12032]; exact Entails.of_eq (by sep_ac_rfl))
      (dropOptPolyCache_from1404_placed_sepWP hdealloc_sat s0.sp out_sret out_ptr hsp0
        dec.ptsNeeded hge1 hneed_le
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded
          (List.replicate 16 none) []).1 hpolys_len
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded
          (List.replicate 16 none) []).2 hout_len
        hout_ne0
        (M.stepEvents evsLoop (M.stepEvents (rustAllocEvents (2 * dec.ptsNeeded) 1) st))
        s3 _ post hpc3 hrun3 hsp3 hx29_3
        (fun s4 evsDrop hfreeDrop hpc4 hrun4 hsp4 htr4 _hacp4 => ?_))
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (decodedMessage_finish_from1904_placed_sepWP hdealloc_sat dec pins hpins s0 out_sret pv_ptr
        (BitVec.ofNat 64 dec.ptsNeeded)
        (some (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded
          (List.replicate 16 none) []).2) hsp0
        (M.stepEvents evsDrop
          (M.stepEvents evsLoop (M.stepEvents (rustAllocEvents (2 * dec.ptsNeeded) 1) st)))
        s4
        (sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ F) post
        hpc4 hrun4 hsp4 (fun sf hpc_f hrun_f hsp_f htr_f _hacp_f hcs_f => ?_))
    have htot := decodedMessageTotal_of_collect_false hcomp_false hpts hret
    have hevs_ok : DecodedMessageEnv dec
        (rustAllocEvents 256 8 ++
          (rustAllocEvents (2 * dec.ptsNeeded) 1 ++
            (evsLoop ++ (evsDrop ++ rustDeallocEvents 256 8)))) :=
      decodedMessageEnv_of_ptsNeeded_pos hcomp_false hret hneed0 hloopEvs
        (freeOnlyEvs_append hfreeDrop freeOnlyEvs_dealloc256)
    refine SepWP.weaken_pre
      (show _ ⊢
        optVecU8Of A.repAlloc out_sret (decodedMessageTotal dec) ∗
          sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          A.pool lim
            (M.stepEvents
              (rustAllocEvents (2 * dec.ptsNeeded) 1 ++
                (evsLoop ++ (evsDrop ++ rustDeallocEvents 256 8))) st) sf ∗
          stackAt s0.sp decodedMessageStack ∗ F by
        rw [htot, M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
        exact Entails.of_eq (by sep_ac_rfl))
      (hnext sf
        (rustAllocEvents (2 * dec.ptsNeeded) 1 ++
          (evsLoop ++ (evsDrop ++ rustDeallocEvents 256 8)))
        hevs_ok hpc_f hrun_f hsp_f (by rw [htr_f, htr4, htr3]) hcs_f)

theorem decodedMessage_afterCollect_cl_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec M A lim)))
    (hcomp_ok : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec M A lim)))
    (dec : PolyDecoder) (decA out_sret pv_ptr : BitVec 64) (pins : List VecPin)
    (hcomp_false : dec.isComplete = false) (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hsort : PolyDecoderStrictSorted dec) (hret : (collectPointsVecsTotal dec 0 16 false []).1 = false)
    (st : M.σ)
    (hfit_after : dec.ptsNeeded ≠ 0 →
      FitsEvents M lim st (rustAllocEvents (2 * dec.ptsNeeded) 1) ∧
      FitsEnv M lim (M.stepEvents (rustAllocEvents (2 * dec.ptsNeeded) 1) st)
        (DecodedMessageLoopEnv dec (collectedSlices dec 0 16) 0 dec.ptsNeeded
          (List.replicate 16 none)))
    (s0 s : State) (F : SepProp) (Q Qp : State → SepProp → Prop)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 352#64)
    (hstat : s.status = .Running) (hsp : s.sp = s0.sp - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx20 : s.readReg64 .x20 = decA) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      DecodedMessageEnv dec (rustAllocEvents 256 8 ++ evs) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.sp = s0.sp →
      traceVRegs sf = traceVRegs s0 → CalleeSavedGprsPreserved s0 sf →
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (optVecU8Of A.repAlloc out_sret (decodedMessageTotal dec) ∗
          sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp decodedMessageStack ∗ F) Q Qp) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
        ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
        memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
        interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
        memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
        ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A.repAlloc decA pins dec.pts ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
        stackAt (s0.sp - 672#64) extHookStack ∗ F) Q Qp := by
  apply SepWPp.of_sepWP (mid := s0.readReg64 .x30)
  refine decodedMessage_afterCollect_cl_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
    hprep hcomp_ok hcomp_at dec decA out_sret pv_ptr pins hcomp_false hpts hpins hsort hret
    st hfit_after s0 s F _ hsp0 hcl hpc hstat hsp htr hx20 hx29
    (fun sf evs hevs hpc_f hrun_f hsp_f htr_f hcs_f => ?_)
  exact SepWP.done hpc_f hrun_f (hnext sf evs hevs hpc_f hrun_f hsp_f htr_f hcs_f)

/-! ## 2. Top-Level Entry Proof (`polyDecoderDecodedMessage_placed_ok`) -/

private theorem sepWP_decodedMessage_return [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {x : DecodedMessageGhost}
    {st : M.σ} {evs : List AllocEvent}
    (hevs : DecodedMessageEnv x.dec evs)
    {s0 sf : State} {R : SepProp}
    (hpc_f : sf.pc = s0.readReg64 (Reg.gpr 30#5))
    (hrun_f : sf.status = .Running)
    (hsp_f : sf.sp = s0.sp)
    (htr_f : sf.trace = s0.trace)
    (hcs_f : CalleeSavedPreserved s0 sf) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) sf
      (optVecU8Of A.repAlloc x.out (decodedMessageTotal x.dec) ∗
        polyDecoderAt A.repAlloc x.decA x.dec ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp decodedMessageStack)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ∃∗ evs' : List AllocEvent,
              ⌜DecodedMessageEnv x.dec evs' ∧ sf.trace = s0.trace⌝ ∗
              optVecU8Of A.repAlloc x.out (decodedMessageTotal x.dec) ∗
              polyDecoderAt A.repAlloc x.decA x.dec ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
              A.pool lim (M.stepEvents evs' st) sf ∗
              stackAt s0.sp decodedMessageStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  refine SepWP.done hpc_f hrun_f ⟨fun hm => ?_, hsp_f, hcs_f⟩
  rw [satisfies_sepExists]
  refine ⟨evs, ?_⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨hevs, htr_f⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩

private structure DecodedMessageClDeps [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  shim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym (withVmPreserved sessionShimSpec)
  alloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  memcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpyRegionSpec)
  prep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
    (lsmpl.base 372) (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec M A lim))
  comp_ok : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
    (lsmpl.base 373) (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec))
  comp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
    (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec M A lim))

/-- `<PolyDecoder as Decoder>::decoded_message` satisfies
    `withLsCodeLoaded lsmpl (decodedMessagePlacedSpec M A lim)` given `withLsCodeLoaded` callee
    contracts (`[LibsignalPlacement]`). -/
theorem polyDecoderDecodedMessage_cl_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec M A lim)))
    (hcomp_ok : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec M A lim))) :
    subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (blkPl_418).base (withLsCodeLoaded lsmpl (decodedMessagePlacedSpec M A lim)) := by
  have hdeps : DecodedMessageClDeps M A lim ext :=
    ⟨hshim_sat, halloc_sat, hdealloc_sat, hmemcpy_sat, hprep, hcomp_ok, hcomp_at⟩
  clear hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hprep hcomp_ok hcomp_at
  simp only [withLsCodeLoaded, decodedMessagePlacedSpec]
  wp_init g s0
  rcases g with ⟨x, st⟩
  dsimp only at *
  rcases hdeps with ⟨hshim_sat, halloc_sat, hdealloc_sat, hmemcpy_sat, hprep, hcomp_ok, hcomp_at⟩
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx8 : s0.readReg64 (Reg.gpr 8#5) = x.out := by assumption
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = x.decA := by assumption
  have hsort : PolyDecoderStrictSorted x.dec := by assumption
  have hfit : FitsEnv M lim st (DecodedMessageEnv x.dec) := by assumption
  have hsp0 : s0.sp &&& 0xf#64 = 0#64 := beq_iff_eq.mp hsp_align
  wp_conv_pre =>
    dsimp only [polyDecoderAt, NUM_POLYS, CHUNK_SIZE, boolByte, polyDecoderPadSize,
      polyDecoderPtsNeededOff, polyDecoderIsCompleteOff, polyDecoderPadOff, BitVec.ofNat_eq_ofNat]
    rw [show memRegion x.out vecHeaderBytes ∗
          (⌜x.dec.pts.length = 16 ∧ x.dec.ptsNeeded < 2 ^ 64⌝ ∗
            sortedSetPtListOf A.repAlloc x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ if x.dec.isComplete then 1#8 else 0#8) ∗
            memRegion (x.decA + 393#64) 7) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp decodedMessageStack =
        ⌜x.dec.pts.length = 16 ∧ x.dec.ptsNeeded < 2 ^ 64⌝ ∗
          (stackAt s0.sp decodedMessageStack ∗ memRegion x.out vecHeaderBytes ∗
            sortedSetPtListOf A.repAlloc x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ if x.dec.isComplete then 1#8 else 0#8) ∗
            memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim st s0) by sep_ac_rfl]
  apply SepWP.pure_elim; rintro ⟨hpts_len, hneed_lt⟩
  have hlen_bound : ∀ s ∈ x.dec.pts, s.vec.length ≤ 65536 := by
    intro s hs; rcases List.getElem_of_mem hs with ⟨i, hi, rfl⟩
    exact polyDecoderStrictSorted_elem_length_le hsort hi
  wp_conv_pre => rw [stackAt_decodedMessage_eq s0.sp]
  refine SepWP.weaken_pre
    (show _ ⊢ memRegion (s0.sp - 96#64) 96 ∗
      (memRegion (s0.sp - 672#64) 576 ∗ stackAt (s0.sp - 672#64) extHookStack ∗
        memRegion x.out vecHeaderBytes ∗ sortedSetPtListOf A.repAlloc x.decA x.dec.pts ∗
        ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
        ((x.decA + 392#64) ↦₈ if x.dec.isComplete then 1#8 else 0#8) ∗
        memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        A.pool lim st s0) by exact Entails.of_eq (by sep_ac_rfl))
    (sepWP_seq_lscl hcl0 (mid := (blkPl_418).base + 32#64)
      (decodedMessage_prologue_placed_sepWP (ext := ext) s0 _ _ hsp0 hpc hrun
        (fun s1 hpc1 hrun1 hsp1 htr1 hvm1 hx0_1 hx8_1 hx29_1 _hx30_1 =>
          SepWP.transport_budgetPool hvm1 (hnext :=
            SepWP.done hpc1 hrun1 fun hcl1 => ?_))))
  have hx0_1' : s1.readReg64 .x0 = x.decA := by
    dsimp only [Reg.x0] at hx0_1 ⊢; exact hx0_1.trans hx0
  have hx8_1' : s1.readReg64 .x8 = x.out := by
    dsimp only [Reg.x8] at hx8_1 ⊢; exact hx8_1.trans hx8
  cases hcomp : x.dec.isComplete
  ·
    have hfit_pv := fitsAllocPv_of_isComplete_false hcomp hfit
    wp_conv_pre => simp only [Bool.false_eq_true, ↓reduceIte]
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (memRegion576_split_for_decodedMessage s0.sp)))) ?_
    wp_conv_pre =>
      rw [stackAt_extHook_eq_allocHook (s0.sp - 672#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists; rename_i w_4 w_3 w_2 w_1 w
    refine SepWP.weaken_pre
      (show _ ⊢
        ((x.decA + 392#64) ↦₈ 0#8) ∗ (∃∗ w632 : BitVec 64, (s0.sp - 632#64) ↦₆₄ w632) ∗
          A.pool lim st s1 ∗ stackAt (s0.sp - 672#64) allocHookStack ∗
          (((s0.sp - 648#64) ↦₆₄ w) ∗ ((s0.sp - 624#64) ↦₆₄ w_2) ∗
            ((s0.sp - 616#64) ↦₆₄ w_3) ∗ ((s0.sp - 608#64) ↦₆₄ w_4) ∗
            savedRegsAt s0.sp s0 ∗ memRegion (s0.sp - 600#64) 384 ∗
            memRegion (s0.sp - 216#64) 24 ∗ interpolateScratchAt s0.sp ∗
            memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
            memRegion ((s0.sp - 672#64) - 16384#64) 12288 ∗
            memRegion x.out vecHeaderBytes ∗ sortedSetPtListOf A.repAlloc x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt) by
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w_1)))
        exact Entails.of_eq (by sep_ac_rfl))
      (sepWP_seq_lscl hcl1 (mid := (blkPl_418).base + 80#64)
        (decodedMessage_allocPv_placed_sepWP hshim_sat halloc_sat s0.sp x.decA x.out hsp0
          st hfit_pv s1 _ _ hpc1 hrun1 hsp1 hx0_1' hx8_1'
          (fun pv_ptr s1p _hpv_ne0 hpc1p hrun1p hsp1p htr1p hx0_1p hx20_1p hx29_1p =>
            SepWP.done hpc1p hrun1p fun hcl1p => ?_)))
    let st1 : M.σ := M.stepEvents (rustAllocEvents 256 8) st
    refine SepWP.weaken_pre
      (show _ ⊢
        ((x.decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
          (∃∗ w648 : BitVec 64, (s0.sp - 648#64) ↦₆₄ w648) ∗
          (∃∗ w624 : BitVec 64, (s0.sp - 624#64) ↦₆₄ w624) ∗
          (∃∗ w616 : BitVec 64, (s0.sp - 616#64) ↦₆₄ w616) ∗
          (∃∗ w608 : BitVec 64, (s0.sp - 608#64) ↦₆₄ w608) ∗
          (savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ x.out) ∗
            memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
            interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
            memRegion (s0.sp - 120#64) 24 ∗ stackAt (s0.sp - 672#64) extHookStack ∗
            memRegion x.out vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗ memRegion pv_ptr 256 ∗
            sortedSetPtListOf A.repAlloc x.decA x.dec.pts ∗ ((x.decA + 392#64) ↦₈ 0#8) ∗
            memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim st1 s1p) by
        rw [stackAt_extHook_eq_allocHook (s0.sp - 672#64)]
        try dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat, st1]
        refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w)))
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w_2))))
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (Entails.sepExists_intro w_3)))))
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w_4))))))
        exact Entails.of_eq (by sep_ac_rfl))
      (sepWP_seq_lscl hcl1p (mid := (blkPl_418).base + 128#64)
        (decodedMessage_allocPv_setup_placed_sepWP (ext := ext) x.dec s0.sp x.decA pv_ptr hsp0 hneed_lt s1p _ _
          hpc1p hrun1p hsp1p hx0_1p hx20_1p
          (fun s2 hpc2 hrun2 hsp2 htr2 hvm2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2 _hx30_2 =>
            SepWP.transport_budgetPool hvm2 (hnext :=
              SepWP.done hpc2 hrun2 fun hcl2 => ?_))))
    have htr2' : traceVRegs s2 = traceVRegs s0 := htr2.trans (htr1p.trans htr1)
    have hx29_2' : s2.readReg64 .x29 = s0.sp - 96#64 := hx29_2.trans (hx29_1p.trans hx29_1)
    wp_conv_pre =>
      rw [sortedSetPtListOf_eq_exists_pins A.repAlloc x.dec.pts x.decA]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists; rename_i pins
    wp_conv_pre =>
      try dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat, st1]
      rw [show A.pool lim (M.stepEvents (rustAllocEvents 256 8) st) s2 ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗
            ((s0.sp - 608#64) ↦₆₄ 0#64) ∗ savedRegsAt s0.sp s0 ∗
            ((s0.sp - 632#64) ↦₆₄ x.out) ∗ memRegion (s0.sp - 600#64) 384 ∗
            memRegion (s0.sp - 216#64) 24 ∗ interpolateScratchAt s0.sp ∗
            memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
            stackAt (s0.sp - 672#64) extHookStack ∗ memRegion x.out vecHeaderBytes ∗
            A.live pv_ptr 256 8 ∗ memRegion pv_ptr 256 ∗
            ⌜pins.length = x.dec.pts.length⌝ ∗ sortedSetPtListPinAt A.repAlloc x.decA pins x.dec.pts ∗
            ((x.decA + 392#64) ↦₈ 0#8) ∗ memRegion (x.decA + 393#64) 7 ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt =
          ⌜pins.length = x.dec.pts.length⌝ ∗
            (((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 608#64) ↦₆₄ 0#64) ∗
              sortedSetPtListPinAt A.repAlloc x.decA pins x.dec.pts ∗
              memRegion pv_ptr 256 ∗
              (savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((s0.sp - 632#64) ↦₆₄ x.out) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗
                memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
                interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
                memRegion (s0.sp - 120#64) 24 ∗ memRegion x.out vecHeaderBytes ∗
                A.live pv_ptr 256 8 ∗
                reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
                A.pool lim (M.stepEvents (rustAllocEvents 256 8) st) s2 ∗
                stackAt (s0.sp - 672#64) extHookStack ∗
                (((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                  ((x.decA + 392#64) ↦₈ 0#8) ∗
                  memRegion (x.decA + 393#64) 7))) by sep_ac_rfl]
    apply SepWP.pure_elim; intro hpins
    have hpins16 : pins.length = 16 := by rw [hpins, hpts_len]
    cases hcol : (collectPointsVecsTotal x.dec 0 16 false []).1
    ·
      have ⟨hall_ge, _⟩ := collectPointsVecs_false_bounds x.dec hpts_len hsort hcol
      have hfit_after := fitsAfterCollect_of_collect_false hcomp hcol hfit
      refine SepWP.weaken_pre
        (show _ ⊢
          ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 608#64) ↦₆₄ 0#64) ∗
            sortedSetPtListPinAt A.repAlloc x.decA pins x.dec.pts ∗
            ptSliceRefListAt x.dec 0 pv_ptr (pins.take 0) ∗
            memRegion (pv_ptr + BitVec.ofNat 64 (16 * 0)) (16 * (16 - 0)) ∗
            (savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((s0.sp - 632#64) ↦₆₄ x.out) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗
              memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
              interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
              memRegion (s0.sp - 120#64) 24 ∗ memRegion x.out vecHeaderBytes ∗
              A.live pv_ptr 256 8 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
              A.pool lim (M.stepEvents (rustAllocEvents 256 8) st) s2 ∗
              stackAt (s0.sp - 672#64) extHookStack ∗
              (((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((x.decA + 392#64) ↦₈ 0#8) ∗
                memRegion (x.decA + 393#64) 7)) by
          simp only [List.take_zero, ptSliceRefListAt, Nat.mul_zero, Nat.sub_zero,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, emp_sepConj]
          exact Entails.of_eq (by sep_ac_rfl))
        (sepWP_seq_lscl hcl2 (mid := (blkPl_418).base + 352#64)
          (collectPointsVecs_ok_loop_placed_sepWP (A := A) (ext := ext)
            x.dec x.decA pv_ptr s0.sp pins
            hpts_len hpins16 hneed_lt hlen_bound hall_ge hsp0 15 0 s2 0#64 _ _ (by decide)
            hpc2 hrun2 hsp2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2
            (fun s3 hpc3 hrun3 hsp3 htr3 hvm3 _hx0_3 hx20_3 hx29_3 _hx30_3 =>
              SepWP.transport_budgetPool hvm3 (hnext :=
                SepWP.done hpc3 hrun3 fun hcl3 => ?_))))
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (decodedMessage_afterCollect_cl_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
          hprep hcomp_ok hcomp_at
          x.dec x.decA x.out pv_ptr pins
          hcomp hpts_len hpins16 hsort hcol
          (M.stepEvents (rustAllocEvents 256 8) st) hfit_after s0 s3
          (((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ 0#8) ∗
            memRegion (x.decA + 393#64) 7) _
          hsp0 hcl3 hpc3 hrun3 hsp3 (by rw [htr3, htr2']) hx20_3 (by rw [hx29_3, hx29_2'])
          (fun sf evsAfter hevs_tot hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
      rcases calleeSavedPreserved_of_gprs_traceVRegs hcs_f htr_f with ⟨hcs_f, htr_f⟩
      refine SepWP.weaken_pre
        (show _ ⊢
          optVecU8Of A.repAlloc x.out (decodedMessageTotal x.dec) ∗
            polyDecoderAt A.repAlloc x.decA x.dec ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim (M.stepEvents (rustAllocEvents 256 8 ++ evsAfter) st) sf ∗
            stackAt s0.sp decodedMessageStack by
          rw [M.stepEvents_append]
          refine Entails.trans
            (sepConj_mono_right (sepConj_mono_left
              (sortedSetPtListPinAt_entails_sortedSetPtListOf A.repAlloc pins x.dec.pts x.decA hpins))) ?_
          refine Entails.trans (Entails.of_eq (show _ =
            (sortedSetPtListOf A.repAlloc x.decA x.dec.pts ∗
              ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((x.decA + 392#64) ↦₈ 0#8) ∗ memRegion (x.decA + 393#64) 7) ∗
            (optVecU8Of A.repAlloc x.out (decodedMessageTotal x.dec) ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
              A.pool lim (M.stepEvents evsAfter (M.stepEvents (rustAllocEvents 256 8) st)) sf ∗
              stackAt s0.sp decodedMessageStack) by sep_ac_rfl)) ?_
          rw [show (0#8 : BitVec 8) = if x.dec.isComplete then 1#8 else 0#8 by rw [hcomp]; rfl]
          refine Entails.trans
            (sepConj_mono_left (reassemble_polyDecoderAt x.decA x.dec hpts_len hneed_lt)) ?_
          exact Entails.of_eq (by sep_ac_rfl))
        (sepWP_decodedMessage_return hevs_tot hpc_f hrun_f hsp_f htr_f hcs_f)
    ·
      have hex_lt := exists_lt_necessaryPoints_of_collect_true x.dec hpts_len hcol
      refine collectPointsVecs_none_loop_placed_sepWP (A := A) (ext := ext)
        x.dec x.decA pv_ptr s0.sp pins
        hpts_len hpins16 hneed_lt hlen_bound hsp0
        15 0 0 false s2 0#64 _ _ (by decide) (by decide) (Or.inr hex_lt)
        hpc2 hrun2 hsp2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2
        (fun s3 pvLenFinal hpc3 hrun3 hsp3 htr3 hvm3 _hx29_3 _hx30_3 => ?_)
      refine SepWP.transport_budgetPool hvm3 (hnext := ?_)
      refine SepWP.weaken_pre
        (show _ ⊢
          (interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24) ∗
            (((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((s0.sp - 632#64) ↦₆₄ x.out) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
              ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ pvLenFinal) ∗
              memRegion x.out vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗ memRegion pv_ptr 256 ∗
              memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
              savedRegsAt s0.sp s0 ∗
              A.pool lim (M.stepEvents (rustAllocEvents 256 8) st) s3 ∗
              stackAt (s0.sp - 672#64) extHookStack ∗
              (sortedSetPtListPinAt A.repAlloc x.decA pins x.dec.pts ∗
                ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((x.decA + 392#64) ↦₈ 0#8) ∗
                memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt)) by
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine SepWP.weaken_pre (sepConj_mono_left (scratch_and_pads_entails_regions s0.sp)) ?_
      refine SepWP.weaken_pre
        (show _ ⊢
          (memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗ memRegion (s0.sp - 192#64) 96) ∗
            (((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((s0.sp - 632#64) ↦₆₄ x.out) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
              ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ pvLenFinal) ∗
              memRegion x.out vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗ memRegion pv_ptr 256 ∗
              memRegion (s0.sp - 672#64) 24 ∗ memRegion (s0.sp - 640#64) 8 ∗
              savedRegsAt s0.sp s0 ∗
              A.pool lim (M.stepEvents (rustAllocEvents 256 8) st) s3 ∗
              stackAt (s0.sp - 672#64) extHookStack ∗
              (sortedSetPtListPinAt A.repAlloc x.decA pins x.dec.pts ∗
                ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((x.decA + 392#64) ↦₈ 0#8) ∗
                memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt)) by
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine SepWP.weaken_pre (sepConj_mono_left (memRegion_384_24_96_entails_504 s0.sp)) ?_
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (decodedMessage_epilogue_from288_placed_sepWP hdealloc_sat s0 s0.sp x.out pv_ptr
          (BitVec.ofNat 64 x.dec.ptsNeeded) pvLenFinal hsp0
          (M.stepEvents (rustAllocEvents 256 8) st) s3
          (sortedSetPtListPinAt A.repAlloc x.decA pins x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ 0#8) ∗
            memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt) _
          hpc3 hrun3 hsp3 (fun sf hpc_f hrun_f hsp_f htr_f _hacp_f hcs_f => ?_))
      have htot := decodedMessageTotal_of_collect_true hcomp hpts_len hcol
      have htr_f_vr : traceVRegs sf = traceVRegs s0 := by rw [htr_f, htr3, htr2']
      rcases calleeSavedPreserved_of_gprs_traceVRegs hcs_f htr_f_vr with ⟨hcs_f, htr_f'⟩
      have hevs_ok := decodedMessageEnv_of_collect_true hcomp hcol
      refine SepWP.weaken_pre
        (show _ ⊢
          optVecU8Of A.repAlloc x.out (decodedMessageTotal x.dec) ∗
            polyDecoderAt A.repAlloc x.decA x.dec ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim (M.stepEvents (rustAllocEvents 256 8 ++ rustDeallocEvents 256 8) st) sf ∗
            stackAt s0.sp decodedMessageStack by
          rw [htot, M.stepEvents_append]
          refine Entails.trans
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
              (sortedSetPtListPinAt_entails_sortedSetPtListOf A.repAlloc pins x.dec.pts x.decA hpins))))) ?_
          refine Entails.trans (Entails.of_eq (show _ =
            (sortedSetPtListOf A.repAlloc x.decA x.dec.pts ∗
              ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((x.decA + 392#64) ↦₈ 0#8) ∗ memRegion (x.decA + 393#64) 7) ∗
            (optVecU8Of A.repAlloc x.out none ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
              A.pool lim (M.stepEvents (rustDeallocEvents 256 8)
                (M.stepEvents (rustAllocEvents 256 8) st)) sf ∗
              stackAt s0.sp decodedMessageStack) by sep_ac_rfl)) ?_
          rw [show (0#8 : BitVec 8) = if x.dec.isComplete then 1#8 else 0#8 by rw [hcomp]; rfl]
          refine Entails.trans
            (sepConj_mono_left (reassemble_polyDecoderAt x.decA x.dec hpts_len hneed_lt)) ?_
          exact Entails.of_eq (by sep_ac_rfl))
        (sepWP_decodedMessage_return hevs_ok hpc_f hrun_f hsp_f htr_f' hcs_f)
  ·
    wp_conv_pre => simp only [↓reduceIte]
    refine SepWP.weaken_pre
      (show _ ⊢
        savedRegsAt s0.sp s0 ∗ memRegion (s0.sp - 672#64) 576 ∗
          stackAt (s0.sp - 672#64) extHookStack ∗ memRegion x.out vecHeaderBytes ∗
          ((x.decA + 392#64) ↦₈ 1#8) ∗ A.pool lim st s1 ∗
          (sortedSetPtListOf A.repAlloc x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt) by
        exact Entails.of_eq (by sep_ac_rfl))
      (decodedMessage_isComplete_true_placed_sepWP s0 x.decA x.out hsp0 st s1 _ _
        hpc1 hrun1 hsp1 hx0_1' hx8_1'
        (fun sf hpc_f hrun_f hsp_f htr_f _hvm_f hcs_f => ?_))
    have htot := decodedMessageTotal_of_isComplete_true hcomp
    have htr_f_vr : traceVRegs sf = traceVRegs s0 := htr_f.trans htr1
    rcases calleeSavedPreserved_of_gprs_traceVRegs hcs_f htr_f_vr with ⟨hcs_f, htr_f'⟩
    have hevs_ok := decodedMessageEnv_of_isComplete_true hcomp
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWP.weaken_pre
      (show _ ⊢
        optVecU8Of A.repAlloc x.out (decodedMessageTotal x.dec) ∗
          polyDecoderAt A.repAlloc x.decA x.dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents [] st) sf ∗ stackAt s0.sp decodedMessageStack by
        rw [htot]
        dsimp only [AllocCostModel.stepEvents_nil]
        refine Entails.trans (Entails.of_eq (show _ =
          (sortedSetPtListOf A.repAlloc x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ 1#8) ∗ memRegion (x.decA + 393#64) 7) ∗
          (optVecU8Of A.repAlloc x.out none ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim st sf ∗ stackAt s0.sp decodedMessageStack) by sep_ac_rfl)) ?_
        rw [show (1#8 : BitVec 8) = if x.dec.isComplete then 1#8 else 0#8 by rw [hcomp]; rfl]
        refine Entails.trans
          (sepConj_mono_left (reassemble_polyDecoderAt x.decA x.dec hpts_len hneed_lt)) ?_
        exact Entails.of_eq (by sep_ac_rfl))
      (sepWP_decodedMessage_return (M := M) (A := A) (lim := lim) (ext := ext) (st := st) (R := R)
        hevs_ok hpc_f hrun_f hsp_f htr_f' hcs_f)

/-! ## 3. Closed Relocatable Theorems Discharging Blocks `371`, `372`, and `373` -/

private theorem subroutine_ok_withLsCodeLoaded_of_plain {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Arm64.Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => (extract_withLsCodeLoaded hp).2)
    (fun _ _ _ _ hq => hq)

private theorem hookSat_noAllocShim_of_sessionShim {hooks : String → Option (State → State)}
    {name : String} (h : HookSat hooks name (withVmPreserved sessionShimSpec)) :
    HookSat hooks name noAllocShimSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, sessionShimSpec, noAllocShimSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · right; exact hrest

theorem polyDecoderDecodedMessage_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hrealloc_sat : HookSat (Rust.withPanics ext) spqrRustReallocSym
      (rustCliReallocBudgetSpec M A lim))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName
      (withVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (blkPl_418).base (withLsCodeLoaded lsmpl (decodedMessagePlacedSpec M A lim)) :=
  polyDecoderDecodedMessage_cl_placed_ok_of_contracts
    hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
    (ls_subroutine_ok_of_block (i := 418) (j := 372)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (lagrangePrepare_placed_ok_of_hookSat M A lim ext hshim_sat halloc_sat hmemset_sat)))
    (ls_subroutine_ok_of_block (i := 418) (j := 373)
      (lagrangeComplete_placed_vmPreserved_ok ext))
    (ls_subroutine_ok_of_block (i := 418) (j := 371)
      (computeAt_placed_ok M A lim ext h_panic
        (hookSat_noAllocShim_of_sessionShim hshim_sat)
        halloc_sat hrealloc_sat hdealloc_sat))

theorem polyDecoderDecodedMessage_cro_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hrealloc_sat : HookSat (Rust.withPanics ext) spqrRustReallocSym
      (rustCliReallocBudgetSpec M A lim))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName
      (withVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (blkPl_418).base (withLsCodeRoLoaded lsmpl (decodedMessagePlacedSpec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (polyDecoderDecodedMessage_cl_placed_ok h_panic hshim_sat halloc_sat hrealloc_sat
      hdealloc_sat hmemcpy_sat hmemset_sat)

theorem polyDecoderDecodedMessage_cro_placed_ok_x_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {PreEnv PostEnv : PolyDecoderDecodedMessageGhost → List AllocEvent → Prop}
    (hPre : ∀ (x : PolyDecoderDecodedMessageGhost) (st : M.σ),
      FitsEnv M lim st (PreEnv x) → FitsEnv M lim st (DecodedMessageEnv x.dec))
    (hPost : ∀ (x : PolyDecoderDecodedMessageGhost) (evs : List AllocEvent),
      DecodedMessageEnv x.dec evs → PostEnv x evs)
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hrealloc_sat : HookSat (Rust.withPanics ext) spqrRustReallocSym
      (rustCliReallocBudgetSpec M A lim))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName
      (withVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (blkPl_418).base
      (withLsCodeRoLoaded lsmpl
        (polyDecoderDecodedMessagePlacedSpecOfPrePostEnv M A lim PreEnv PostEnv)) :=
  polyDecoderDecodedMessage_placed_cro_of_decodedMessage_ofPrePostEnv hPre hPost
    (polyDecoderDecodedMessage_cro_placed_ok h_panic hshim_sat halloc_sat hrealloc_sat
      hdealloc_sat hmemcpy_sat hmemset_sat)

theorem polyDecoderDecodedMessage_cro_placed_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Env : PolyDecoderDecodedMessageGhost → List AllocEvent → Prop}
    (hPre : ∀ (x : PolyDecoderDecodedMessageGhost) (st : M.σ),
      FitsEnv M lim st (Env x) → FitsEnv M lim st (DecodedMessageEnv x.dec))
    (hPost : ∀ (x : PolyDecoderDecodedMessageGhost) (evs : List AllocEvent),
      DecodedMessageEnv x.dec evs → Env x evs)
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hrealloc_sat : HookSat (Rust.withPanics ext) spqrRustReallocSym
      (rustCliReallocBudgetSpec M A lim))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName
      (withVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (blkPl_418).base
      (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpecOfEnv M A lim Env)) :=
  polyDecoderDecodedMessage_placed_cro_of_decodedMessage_ofEnv hPre hPost
    (polyDecoderDecodedMessage_cro_placed_ok h_panic hshim_sat halloc_sat hrealloc_sat
      hdealloc_sat hmemcpy_sat hmemset_sat)

theorem polyDecoderDecodedMessage_cro_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hrealloc_sat : HookSat (Rust.withPanics ext) spqrRustReallocSym
      (rustCliReallocBudgetSpec M A lim))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName
      (withVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (blkPl_418).base (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)) :=
  polyDecoderDecodedMessage_placed_cro_of_decodedMessage
    (polyDecoderDecodedMessage_cro_placed_ok h_panic hshim_sat halloc_sat hrealloc_sat
      hdealloc_sat hmemcpy_sat hmemset_sat)

theorem polyDecodedMessagePlacedOkX_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hrealloc_sat : HookSat (Rust.withPanics ext) spqrRustReallocSym
      (rustCliReallocBudgetSpec M A lim))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName
      (withVmPreserved sessionMemsetRegionSpec)) :
    PolyDecodedMessagePlacedOkX M A lim ext :=
  polyDecodedMessagePlacedOkX_of_decodedMessage
    (polyDecoderDecodedMessage_cro_placed_ok h_panic hshim_sat halloc_sat hrealloc_sat
      hdealloc_sat hmemcpy_sat hmemset_sat)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudget
