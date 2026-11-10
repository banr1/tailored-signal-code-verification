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
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpilogue
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Proof -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.ProofBudget -- shake: keep

/-!
# Budget-Threaded Relocatable Top-Level Proof for `<PolyDecoder as Decoder>::decoded_message`

Proves `polyDecoderDecodedMessage_placed_ok` on Block `418` under `RustCliAllocBudget M` and
`DecodedMessageEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement blkPC_418 blkPl_418 lsmpl)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalSpqrV1 (CHUNK_SIZE NUM_POLYS PolyDecoder)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack sessionMemcpyRegionSpec sessionShimSpec
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (
  spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym
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
  rustDeallocEvents
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
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopPlacedBudget (
  decodedMessageLoop_placed_sepWP
)
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

/-! ## Post-`collectPointsVecs` Execution (`+352` to Return) -/

/-- Helper (`[LibsignalPlacement]`): from `+1904` after `dropOptPolyCache_from1404_placed_sepWP` or
    `dropOptPolyCache_from1460_placed_sepWP`, collapses stack regions and `ptSliceRefListAt` and
    executes `decodedMessage_epilogue_from1904_placed_sepWP`. -/
theorem decodedMessage_finish_from1904_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (dec : PolyDecoder) (pins : List VecPin) (hpins : pins.length = 16)
    (s0 : State) (out_sret pv_ptr w648 : BitVec 64) (resOpt : Option (List (BitVec 8)))
    (hsp0 : s0.sp &&& 0xf#64 = 0#64) (st : M.σ)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 1904#64)
    (hstat : s.status = .Running) (hsp : s.sp = s0.sp - 672#64)
    (hcont : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.sp = s0.sp →
      traceVRegs sf = traceVRegs s → AllocCallPreserved s sf → CalleeSavedGprsPreserved s0 sf →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (optVecU8Of A.repAlloc out_sret resOpt ∗
          A.pool lim (M.stepEvents (rustDeallocEvents 256 8) st) sf ∗
          stackAt s0.sp decodedMessageStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (optVecU8Of A.repAlloc out_sret resOpt ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
        memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗ A.pool lim st s ∗
        stackAt (s0.sp - 672#64) allocHookStack ∗ memRegion ((s0.sp - 672#64) - 16384#64) 12288 ∗
        savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ w648) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
        ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
        interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
        A.live pv_ptr 256 8 ∗ ptSliceRefListAt dec 0 pv_ptr pins ∗ P) post := by
  have hext :
      stackAt (s0.sp - 672#64) allocHookStack ∗ memRegion ((s0.sp - 672#64) - 16384#64) 12288 =
        stackAt (s0.sp - 672#64) extHookStack :=
    (stackAt_extHook_eq_allocHook (s0.sp - 672#64)).symm
  refine SepWP.weaken_pre
    (show _ ⊢
      (interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24) ∗
      (ptSliceRefListAt dec 0 pv_ptr pins ∗ ((s0.sp - 648#64) ↦₆₄ w648) ∗
        ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
        memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
        (stackAt (s0.sp - 672#64) allocHookStack ∗ memRegion ((s0.sp - 672#64) - 16384#64) 12288) ∗
        (((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ A.live pv_ptr 256 8 ∗
          savedRegsAt s0.sp s0 ∗ A.pool lim st s ∗ (optVecU8Of A.repAlloc out_sret resOpt ∗ P))) by
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.weaken_pre (sepConj_mono_left (scratch_and_pads_entails_regions s0.sp)) ?_
  refine SepWP.weaken_pre
    (show _ ⊢
      ptSliceRefListAt dec 0 pv_ptr pins ∗
        (memRegion (s0.sp - 672#64) 24 ∗ ((s0.sp - 648#64) ↦₆₄ w648) ∗
          memRegion (s0.sp - 640#64) 8 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret)) ∗
        (((s0.sp - 608#64) ↦₆₄ 16#64) ∗
          (memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗ memRegion (s0.sp - 192#64) 96)) ∗
        (((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ A.live pv_ptr 256 8 ∗
          savedRegsAt s0.sp s0 ∗ A.pool lim st s ∗
          (stackAt (s0.sp - 672#64) allocHookStack ∗ memRegion ((s0.sp - 672#64) - 16384#64) 12288) ∗
          (optVecU8Of A.repAlloc out_sret resOpt ∗ P)) by
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  rw [hext]
  refine SepWP.weaken_pre
    (sepConj_mono (ptSliceRefListAt_entails_memRegion256 dec pv_ptr pins hpins)
      (sepConj_mono (memRegion_24_8_8_8_entails_48 s0.sp w648 out_sret)
        (sepConj_mono_left (memRegion_8_384_24_96_entails_512 s0.sp 16#64)))) ?_
  refine SepWP.weaken_pre
    (show _ ⊢
      ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗ memRegion (s0.sp - 672#64) 48 ∗ memRegion (s0.sp - 608#64) 512 ∗
        savedRegsAt s0.sp s0 ∗ A.pool lim st s ∗ stackAt (s0.sp - 672#64) extHookStack ∗
        (optVecU8Of A.repAlloc out_sret resOpt ∗ P) by exact Entails.of_eq (by sep_ac_rfl))
    (decodedMessage_epilogue_from1904_placed_sepWP hdealloc_sat s0 s0.sp pv_ptr hsp0 st s
      (optVecU8Of A.repAlloc out_sret resOpt ∗ P) post hpc hstat hsp
      (fun sf hpc_f hrun_f hsp_f htr_f hacp_f hcs_f =>
        SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hcont sf hpc_f hrun_f hsp_f htr_f hacp_f hcs_f)))

/-- Budget-threaded execution from `entry + 352#64` to function return (`s0.readReg64 .x30`) when
    `dec.isComplete = false` and `(collectPointsVecsTotal dec 0 16 false []).1 = false`
    (`[LibsignalPlacement]`, `SepWP`). -/
theorem decodedMessage_afterCollect_placed_sepWP [LibsignalPlacement]
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
      (lsmpl.base 372) (lagrangePreparePlacedSpec M A lim))
    (hcomp_ok : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withVmPreserved lagrangeCompletePlacedSpec))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (computeAtPlacedSpec M A lim))
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
    (initOptPolyCache_placed_sepWP (ext := ext) (A := A.repAlloc)
      s0.sp (BitVec.ofNat 64 dec.ptsNeeded) hsp0 s _ post
      hpc hstat hsp (fun s1 hpc1 hrun1 hsp1 htr1 hvm1 hx20_1 hx24_1 hx29_1 => ?_))
  refine SepWP.transport_budgetPool hvm1 (hnext := ?_)
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
      (allocOut_pos_placed_sepWP hshim_sat halloc_sat s0.sp hsp0 dec.ptsNeeded hge1 hneed_le
        st hfit_out s0 s1 _ post
        hpc1 hrun1 hsp1 (by rw [htr1, htr]) hx24_1 (by rw [hx29_1, hx29])
        (fun out_ptr s2 hout_ne0 hpc2 hrun2 hsp2 htr2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 => ?_))
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
      (decodedMessageLoop_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
        hprep hcomp_ok hcomp_at
        dec s0.sp decA pv_ptr out_ptr pins
        hsp0 hpts hpins hsort hneed_le hall_ge s0 _ post
        (dec.ptsNeeded - 1) 0 (List.replicate 16 none) []
        (M.stepEvents (rustAllocEvents (2 * dec.ptsNeeded) 1) st) s2
        hfit_loop' (by omega) (by simp) (by simp)
        hpc2 hrun2 hsp2 htr2 (by rw [hx20_2, hx20_1, hx20]) hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2
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

theorem decodedMessage_afterCollect_placed_wpp [LibsignalPlacement]
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
      (lsmpl.base 372) (lagrangePreparePlacedSpec M A lim))
    (hcomp_ok : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withVmPreserved lagrangeCompletePlacedSpec))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (computeAtPlacedSpec M A lim))
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
  refine decodedMessage_afterCollect_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
    hprep hcomp_ok hcomp_at dec decA out_sret pv_ptr pins hcomp_false hpts hpins hsort hret
    st hfit_after s0 s F _ hsp0 hpc hstat hsp htr hx20 hx29
    (fun sf evs hevs hpc_f hrun_f hsp_f htr_f hcs_f => ?_)
  exact SepWP.done hpc_f hrun_f (hnext sf evs hevs hpc_f hrun_f hsp_f htr_f hcs_f)

/-! ## Top-Level Entry Proof (`polyDecoderDecodedMessage_placed_ok`) -/

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

private structure DecodedMessageDeps [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  shim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym (withVmPreserved sessionShimSpec)
  alloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  memcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpyRegionSpec)
  prep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
    (lsmpl.base 372) (lagrangePreparePlacedSpec M A lim)
  comp_ok : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
    (lsmpl.base 373) (withVmPreserved lagrangeCompletePlacedSpec)
  comp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
    (lsmpl.base 371) (computeAtPlacedSpec M A lim)

theorem polyDecoderDecodedMessage_placed_ok [LibsignalPlacement]
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
      (lsmpl.base 372) (lagrangePreparePlacedSpec M A lim))
    (hcomp_ok : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withVmPreserved lagrangeCompletePlacedSpec))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (computeAtPlacedSpec M A lim)) :
    DecodedMessagePlacedOkExt M A lim ext := by
  have hdeps : DecodedMessageDeps M A lim ext :=
    ⟨hshim_sat, halloc_sat, hdealloc_sat, hmemcpy_sat, hprep, hcomp_ok, hcomp_at⟩
  clear hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hprep hcomp_ok hcomp_at
  unfold DecodedMessagePlacedOkExt
  simp only [decodedMessagePlacedSpec]
  wp_init g s0
  rcases g with ⟨x, st⟩
  dsimp only at *
  rcases hdeps with ⟨hshim_sat, halloc_sat, hdealloc_sat, hmemcpy_sat, hprep, hcomp_ok, hcomp_at⟩
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
    (decodedMessage_prologue_placed_sepWP (ext := ext) s0 _ _ hsp0 hpc hrun
      (fun s1 hpc1 hrun1 hsp1 htr1 hvm1 hx0_1 hx8_1 hx29_1 _hx30_1 => ?_))
  refine SepWP.transport_budgetPool hvm1 (hnext := ?_)
  have hx0_1' : s1.readReg64 .x0 = x.decA := by
    dsimp only [Reg.x0] at hx0_1 ⊢; exact hx0_1.trans hx0
  have hx8_1' : s1.readReg64 .x8 = x.out := by
    dsimp only [Reg.x8] at hx8_1 ⊢; exact hx8_1.trans hx8
  cases hcomp : x.dec.isComplete
  · -- `x.dec.isComplete = false`
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
      (decodedMessage_allocPv_placed_sepWP hshim_sat halloc_sat s0.sp x.decA x.out hsp0
        st hfit_pv s1 _ _ hpc1 hrun1 hsp1 hx0_1' hx8_1'
        (fun pv_ptr s1p _hpv_ne0 hpc1p hrun1p hsp1p htr1p hx0_1p hx20_1p hx29_1p => ?_))
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
      (decodedMessage_allocPv_setup_placed_sepWP (ext := ext) x.dec s0.sp x.decA pv_ptr hsp0 hneed_lt s1p _ _
        hpc1p hrun1p hsp1p hx0_1p hx20_1p
        (fun s2 hpc2 hrun2 hsp2 htr2 hvm2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2 _hx30_2 => ?_))
    refine SepWP.transport_budgetPool hvm2 (hnext := ?_)
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
    · -- `(collectPointsVecsTotal x.dec 0 16 false []).1 = false`
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
        (collectPointsVecs_ok_loop_placed_sepWP (A := A) (ext := ext)
          x.dec x.decA pv_ptr s0.sp pins
          hpts_len hpins16 hneed_lt hlen_bound hall_ge hsp0 15 0 s2 0#64 _ _ (by decide)
          hpc2 hrun2 hsp2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2
          (fun s3 hpc3 hrun3 hsp3 htr3 hvm3 _hx0_3 hx20_3 hx29_3 _hx30_3 => ?_))
      refine SepWP.transport_budgetPool hvm3 (hnext := ?_)
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (decodedMessage_afterCollect_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
          hprep hcomp_ok hcomp_at
          x.dec x.decA x.out pv_ptr pins
          hcomp hpts_len hpins16 hsort hcol
          (M.stepEvents (rustAllocEvents 256 8) st) hfit_after s0 s3
          (((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ 0#8) ∗
            memRegion (x.decA + 393#64) 7) _
          hsp0 hpc3 hrun3 hsp3 (by rw [htr3, htr2']) hx20_3 (by rw [hx29_3, hx29_2'])
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
    · -- `(collectPointsVecsTotal x.dec 0 16 false []).1 = true`
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
  · -- `x.dec.isComplete = true`
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

end LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofPlacedBudget
