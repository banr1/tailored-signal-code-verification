/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Phase
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.PhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.NextChunkCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.ProofBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.ProofBudget
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Placed Prologue and Epilogue

Relocatable `[LibsignalPlacement]` callee bundle (`AllocContractsPlaced`), prologue (`+0..+92`),
and shared epilogue (`+4484`) for Block `416` threading `RustCliAllocBudget M`, `BudgetLimits`,
`NextChunkPrologueEnv`, and `NextChunkEpilogueEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_416 blkPC_416 blkPl_416 lscall_blk
   lscall_blk_cl lsmpl lsρ withMemEq)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (memsetName sessionMemcpySpec sessionMemsetRegionSpec sessionShimSpec)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_externAt?_of_mem spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt chunkDataOff chunkIndexOff chunkSize encoderStateAt polyEncoderAt polyEncoderIdxOff
   polyEncoderPadOff polyEncoderPadSize polyEncoderPointsTag polyEncoderPolysTag polyEncoderTagOff
   polyEncoderVecsOff polyEncoderVecsSize)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sepWPp_seq_lscl sp_setMem_pre
   spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
  (lagrangeCompletePlacedSpec lagrangeComplete_placed_ok)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (PolyNextChunkGhost bv_add_lit_add_lit exists_pow_two_eq_one extractLsb_0_64_append
   extractLsb_64_64_append localFrameRest localFrameRest_fold_prologue
   memRegion_chunkSize_entails_cells nextChunkCalleeStack pack64
   pointsTo64_eq_pointsTo32_pair pointsToBytes32_eq_pointsTo64_four polyNextChunkStack
   prologue_stack_split restore_full_stack savedCells sepWP_exists_left_sep
   setWidth16_zext64_setWidth32 setWidth32_zext64 setWidth32_zext64_add_one sp_sub_16_add_8
   sp_sub_24_add_8 sp_sub_32_add_8 sp_sub_40_add_8 sp_sub_48_add_8 sp_sub_56_add_8 sp_sub_64_add_8
   sp_sub_72_add_8 sp_sub_80_add_8 sp_sub_88_add_8 sp_sub_96_add_16 sp_sub_96_add_32
   sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_add_96 sp_sub_96_sub_1104
   sp_sub_968_add_8 sp_sub_1200_add_1104 stackAt_nextChunkCallee_split_allocHook)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
   FreeOnlyEvs RustCliAllocBudget RustLayoutOk VmPreserved coarseCostModel rustAllocEvents
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
   rustCliReallocNoOomSpec rustDeallocEvents subroutine_ok_allocNoOom_of_budget
   subroutine_ok_reallocNoOom_of_budget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
  (dropGluePoly16Spec drop_glue_poly16_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget (computeAtPlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.ProofBudget (computeAt_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget (lagrangePreparePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.ProofBudget
  (lagrangePrepare_placed_ok_of_hookSat)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem fs_setMem_pre (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
private theorem sigActions_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).sigActions = s.sigActions := by cases s; rfl
private theorem tpidrEl0_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem brkStart_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).brkStart = s.brkStart := by cases s; rfl
private theorem oracle_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).oracle = s.oracle := by cases s; rfl
private theorem symtab_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).symtab = s.symtab := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] bv_add_lit_add_lit
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  fs_setMem_pre sigActions_setMem_pre tpidrEl0_setMem_pre brkStart_setMem_pre
  oracle_setMem_pre symtab_setMem_pre calleeSavedVRegs_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm]
  sp_sub_1200_add_1104 sp_sub_968_add_8
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48
  sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_add_96
  sp_sub_88_add_8 sp_sub_80_add_8 sp_sub_72_add_8 sp_sub_64_add_8 sp_sub_56_add_8
  sp_sub_48_add_8 sp_sub_40_add_8 sp_sub_32_add_8 sp_sub_24_add_8 sp_sub_16_add_8
  sp_sub_96_sub_1104 exists_pow_two_eq_one
  setWidth16_zext64_setWidth32 setWidth32_zext64 setWidth32_zext64_add_one
  extractLsb_0_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_64_64_append
  polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize
  polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  polyEncoderPointsTag polyEncoderPolysTag
  chunkDataOff chunkIndexOff chunkSize

private theorem acp_of_PureStep {s sm : State}
    (hfs : sm.fs = s.fs := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (htr : sm.trace = s.trace := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (hsig : sm.sigActions = s.sigActions := by
      first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (htp : sm.tpidrEl0 = s.tpidrEl0 := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (hbrk : sm.brkStart = s.brkStart := by
      first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (horc : sm.oracle = s.oracle := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (hsym : sm.symtab = s.symtab := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl)) :
    AllocCallPreserved s sm :=
  ⟨hfs, htr, hsig, htp, hbrk, horc, hsym⟩

private theorem acp_trans {s0 s1 s2 : State}
    (h01 : AllocCallPreserved s0 s1) (h12 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

/-! ## 1. Exact Allocator Event Envelopes for `next_chunk` Prologue & Epilogue -/

/-- Exact allocator event sequence of the `<PolyEncoder as Encoder>::next_chunk` prologue
    (`+0..+92`, Block `416`): one `32`-byte output buffer allocation at alignment `1`. -/
def nextChunkPrologueEvents : List AllocEvent :=
  rustAllocEvents 32 1

def NextChunkPrologueEnv (evs : List AllocEvent) : Prop :=
  evs = nextChunkPrologueEvents

theorem fitsEnv_nextChunkPrologue_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st NextChunkPrologueEnv ↔ FitsEvents M lim st (rustAllocEvents 32 1) := by
  constructor
  · intro h
    exact h (rustAllocEvents 32 1) rfl
  · intro h evs hevs
    rw [hevs]
    exact h

/-- Exact allocator event sequence of the `<PolyEncoder as Encoder>::next_chunk` shared epilogue
    (`+4484`, Block `416`): one `32`-byte output buffer deallocation at alignment `1`. -/
def nextChunkEpilogueEvents : List AllocEvent :=
  rustDeallocEvents 32 1

def NextChunkEpilogueEnv (evs : List AllocEvent) : Prop :=
  evs = nextChunkEpilogueEvents

theorem nextChunkEpilogueEvents_freeOnly : FreeOnlyEvs nextChunkEpilogueEvents :=
  FreeOnlyEvs.singleton 1 32

theorem fitsEnv_nextChunkEpilogue_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st NextChunkEpilogueEnv ↔ FitsEvents M lim st (rustDeallocEvents 32 1) := by
  constructor
  · intro h
    exact h (rustDeallocEvents 32 1) rfl
  · intro h evs hevs
    rw [hevs]
    exact h

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init NextChunkPrologueEnv := by
  rw [fitsEnv_nextChunkPrologue_iff]
  dsimp only [rustAllocEvents, FitsEvents, FitsEvent, FitsStep, AllocEvent.withinMaxAlloc]
  exact ⟨⟨by decide, by decide, by decide, by decide⟩, trivial⟩

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init NextChunkEpilogueEnv := by
  rw [fitsEnv_nextChunkEpilogue_iff]
  dsimp only [rustDeallocEvents, FitsEvents, FitsEvent, FitsStep, AllocEvent.withinMaxAlloc]
  exact ⟨⟨by decide, by decide, by decide, by decide⟩, trivial⟩

/-! ## 2. Budget-Threaded Relocatable Hook & Callee Bundle (`AllocContractsPlaced`) -/

/-- Budget-threaded relocatable `[LibsignalPlacement]` counterpart of `AllocContractsPlaced` for
    `NextChunk` (Block `416`) and its SPQR callees (`compute_at`, `lagrange_interpolate_prepare`,
    `lagrange_interpolate_complete`, `drop_glue::<[Poly; 16]>`). -/
structure AllocContractsPlaced [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop where
  handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked
  shim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec
  alloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  realloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)
  session_memcpy : ∀ (hookStack : Nat),
    HookSat (Rust.withPanics ext) spqrMemcpySym (sessionMemcpyBudgetSpec hookStack)
  session_memset_region :
    HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec

namespace AllocContractsPlaced

theorem handle_error_extern [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.handle_error

theorem noAllocShim [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec := by
  refine ProofLib.HookSat.mono hA.shim fun _ R s0 hpre => ⟨(), R, hpre, fun sf hpost => ?_⟩
  dsimp only [sessionShimBudgetSpec, sessionShimSpec, noAllocShimSpec,
    noAllocShimBudgetSpec] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
  rw [satisfies_pure_sepConj]
  exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩

theorem shim_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimBudgetSpec :=
  spqr_hook_ok_of_mem hA.shim

theorem noAllocShim_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec :=
  spqr_hook_ok_of_mem hA.noAllocShim

theorem alloc_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false) :=
  spqr_hook_ok_of_mem hA.alloc

theorem allocNoOom_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
  subroutine_ok_allocNoOom_of_budget hA.alloc_ok

theorem dealloc_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  spqr_hook_ok_of_mem hA.dealloc

theorem realloc_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ spqrRustReallocSym) (rustCliReallocBudgetSpec M A lim) :=
  spqr_hook_ok_of_mem hA.realloc

theorem reallocNoOom_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomSpec M A lim) :=
  subroutine_ok_reallocNoOom_of_budget hA.realloc_ok

theorem session_memcpy_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext)
    (hookStack : Nat := 4096) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (sessionMemcpyBudgetSpec hookStack) :=
  spqr_hook_ok_of_mem (hA.session_memcpy hookStack)

theorem session_memset_region_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ memsetName) sessionMemsetRegionBudgetSpec :=
  spqr_hook_ok_of_mem hA.session_memset_region

theorem computeAt_blk_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext)
    {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsmpl.base 371) (withMemEq m (computeAtPlacedSpec M A lim)) :=
  lscall_blk_cl
    (computeAt_placed_ok M A lim ext hA.handle_error hA.noAllocShim hA.alloc hA.realloc hA.dealloc)
    hcl

theorem lagrangePrepare_blk_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext)
    {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsmpl.base 372) (withMemEq m (lagrangePreparePlacedSpec M A lim)) :=
  lscall_blk
    (lagrangePrepare_placed_ok_of_hookSat M A lim ext hA.shim hA.alloc hA.session_memset_region)
    hcl

theorem lagrangeComplete_blk_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (_hA : AllocContractsPlaced M A lim ext)
    {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsmpl.base 373) (withMemEq m lagrangeCompletePlacedSpec) :=
  lscall_blk_cl (lagrangeComplete_placed_ok ext) hcl

theorem dropGluePoly16_blk_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext)
    {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsmpl.base 265) (withMemEq m (dropGluePoly16Spec M A lim)) :=
  lscall_blk (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hA.dealloc)) hcl

end AllocContractsPlaced

/-! ## 3. Shared Epilogue (Block `416`, offset `+4484`, 21 insns) -/

set_option maxHeartbeats 800000 in
theorem epilogue_placed_acp_sepWP [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (x : PolyNextChunkGhost) (R : SepProp) (s0 sf : State)
    (out_ptr : BitVec 64) (_hout_ne : out_ptr ≠ 0#64)
    (hidx_chunk : x.chunk.index = x.enc.idx.setWidth 16)
    (hidx_enc' : x.enc'.idx = x.enc.idx + 1#32)
    (hpc : sf.pc = (blkPl_416).base + 4484#64)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s0.sp - 1200#64)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (htr : sf.trace = s0.trace)
    (hx20 : sf.readReg64 .x20 = 32#64)
    (hx24 : sf.readReg64 .x24 = x.encA)
    (hx27 : (sf.readReg64 .x27).setWidth 16 = x.enc.idx.setWidth 16)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0 := by simp only [arm64_norm, wp_norm, *]) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
      ((out_ptr ↦ₛ x.chunk.data.toList) ∗
       A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       encoderStateAt A.repAlloc x.encA x.enc'.s ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
       (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ 32#64) ∗
       localFrameRest (s0.sp - 1200#64) ∗
       savedCells s0 ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool lim st sf ∗
       stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace ∧ AllocCallPreserved sf sf1⌝ ∗
             chunkAt x.outA x.chunk ∗
             polyEncoderAt A.repAlloc x.encA x.enc' ∗
             tokenInitPlacedAt ∗
             reduceTablePlacedAt ∗
             A.pool lim (M.stepEvents (rustDeallocEvents 32 1) st) sf1 ∗
             stackAt s0.sp polyNextChunkStack ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1) := by
  have hdealloc := hA.dealloc_ok
  dsimp only [rustCliDeallocBudgetSpec] at hdealloc
  clear hA
  have hlen32 : x.chunk.data.toList.length = 32 := x.chunk.data.2
  have h32_toNat : (32#64 : BitVec 64).toNat = 32 := rfl
  have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
  apply SepWP.fold (memRegion_chunkSize_entails_cells x.outA) (by sep_focus)
  apply sepWP_exists_left_sep; intro w0
  apply sepWP_exists_left_sep; intro w1
  apply sepWP_exists_left_sep; intro w2
  apply sepWP_exists_left_sep; intro w3
  apply sepWP_exists_left_sep; intro idx0
  wp_conv_pre =>
    rw [pointsToBytes32_eq_pointsTo64_four out_ptr hlen32,
        stackAt_nextChunkCallee_split_allocHook (s0.sp - 1200#64),
        ← hsp]
  unfold savedCells
  apply sepWP_seg_ls_vm
    (Q := (blkPC_416).rebase (blkPl_416).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_416 (mid := lsρ spqrRustDeallocSym)
  intro _m_strip
  wp_steps 10
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  have hbuf_mem :
      (out_ptr ↦₆₄ pack64 ((x.chunk.data.toList.take 16).take 8)) ∗
        ((out_ptr + 8#64) ↦₆₄ pack64 ((x.chunk.data.toList.take 16).drop 8)) ∗
        ((out_ptr + 16#64) ↦₆₄ pack64 ((x.chunk.data.toList.drop 16).take 8)) ∗
        ((out_ptr + 24#64) ↦₆₄ pack64 ((x.chunk.data.toList.drop 16).drop 8)) ⊢
        memRegion out_ptr 32 := by
    rw [← pointsToBytes32_eq_pointsTo64_four out_ptr hlen32]
    have h := pointsToBytes_entails_memRegion out_ptr x.chunk.data.toList
    rwa [hlen32] at h
  apply SepWP.fold hbuf_mem (by sep_focus)
  wp_call hdealloc (out_ptr, 32, 1, st)
  have hacp1 : AllocCallPreserved sf sf_1 := by assumption
  have hsp_sf1 : sf_1.sp = s0.sp - 1200#64 := by simpa [arm64_norm, wp_norm, hsp] using hsp_sf
  have hx24_sf1 : sf_1.readReg64 (Reg.gpr 24#5) = x.encA := by
    simpa [arm64_norm, wp_norm, hx24] using h_5
  wp_conv_pre => simp only [arm64_norm, wp_norm, hsp]
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  have hchunk_fold :
      (x.outA ↦₆₄ pack64 ((x.chunk.data.toList.take 16).take 8)) ∗
        ((x.outA + 8#64) ↦₆₄ pack64 ((x.chunk.data.toList.take 16).drop 8)) ∗
        ((x.outA + 16#64) ↦₆₄ pack64 ((x.chunk.data.toList.drop 16).take 8)) ∗
        ((x.outA + 24#64) ↦₆₄ pack64 ((x.chunk.data.toList.drop 16).drop 8)) ∗
        ((x.outA + 32#64) ↦₁₆ ((sf.readReg64 (Reg.gpr 27#5)).setWidth 32).setWidth 16) ⊢
        chunkAt x.outA x.chunk := by
    have htr16 : ((sf.readReg64 (Reg.gpr 27#5)).setWidth 32).setWidth 16 = x.chunk.index := by
      rw [BitVec.setWidth_setWidth_of_le (sf.readReg64 (Reg.gpr 27#5)) (by decide : 16 ≤ 32)]
      exact hx27.trans hidx_chunk.symm
    unfold chunkAt
    simp only [chunkIndexOff, htr16, pointsToBytes32_eq_pointsTo64_four x.outA hlen32]
    exact Entails.of_eq (by sep_ac_rfl)
  apply SepWP.fold hchunk_fold (by sep_focus)
  have henc_fold :
      encoderStateAt A.repAlloc x.encA x.enc'.s ∗
        ((x.encA + 392#64) ↦₃₂ (x.enc.idx + 1#32)) ∗
        memRegion (x.encA + 396#64) 4 ⊢
        polyEncoderAt A.repAlloc x.encA x.enc' := by
    unfold polyEncoderAt
    simp only [polyEncoderIdxOff, polyEncoderPadOff, polyEncoderPadSize, ← hidx_enc']
    exact Entails.of_eq (by sep_ac_rfl)
  apply SepWP.fold henc_fold (by sep_focus)
  have hstk_fold :
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        memRegion (s0.sp - 18432#64) 13136 ∗
        stackAt (s0.sp - 1200#64) allocHookStack ∗
        localFrameRest (s0.sp - 1200#64) ∗
        ((s0.sp - 1144#64) ↦₆₄ x.outA) ∗
        ((s0.sp - 968#64) ↦₆₄ 32#64) ∗
        ((s0.sp - 960#64) ↦₆₄ out_ptr) ∗
        ((s0.sp - 952#64) ↦₆₄ 32#64) ∗
        chunkAt x.outA x.chunk ∗
        polyEncoderAt A.repAlloc x.encA x.enc' ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ⊢
        (chunkAt x.outA x.chunk ∗ polyEncoderAt A.repAlloc x.encA x.enc' ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗
          stackAt s0.sp polyNextChunkStack := by
    have h0 := restore_full_stack s0 x.outA 32#64 out_ptr 32#64
      (chunkAt x.outA x.chunk ∗ polyEncoderAt A.repAlloc x.encA x.enc' ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt)
    have hsub18432 : (s0.sp - 1200#64) - 17232#64 = s0.sp - 18432#64 := by bv_omega
    unfold savedCells at h0
    simp only [arm64_norm, hsub18432] at h0
    exact Entails.trans h0 (Entails.of_eq (by sep_ac_rfl))
  apply SepWP.fold hstk_fold (by sep_focus)
  conv => arg 5; ext sf1 P_f; rw [CalleeSavedPreserved, ← hvregs]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨fun hm => ?_, by wp_norm_goal, ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨And.intro ?_ (acp_trans hacp1 acp_of_PureStep), ?_⟩
    · simp only [arm64_norm, wp_norm, hacp1.2.1, htr]
    · refine Eq.mp ?_ hm
      congr 1
      sep_ac_rfl
  · simp only [arm64_norm, wp_norm, *]

theorem epilogue_placed_sepWP [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (x : PolyNextChunkGhost) (R : SepProp) (s0 sf : State)
    (out_ptr : BitVec 64) (hout_ne : out_ptr ≠ 0#64)
    (hidx_chunk : x.chunk.index = x.enc.idx.setWidth 16)
    (hidx_enc' : x.enc'.idx = x.enc.idx + 1#32)
    (hpc : sf.pc = (blkPl_416).base + 4484#64)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s0.sp - 1200#64)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (htr : sf.trace = s0.trace)
    (hx20 : sf.readReg64 .x20 = 32#64)
    (hx24 : sf.readReg64 .x24 = x.encA)
    (hx27 : (sf.readReg64 .x27).setWidth 16 = x.enc.idx.setWidth 16)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0 := by simp only [arm64_norm, wp_norm, *]) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
      ((out_ptr ↦ₛ x.chunk.data.toList) ∗
       A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       encoderStateAt A.repAlloc x.encA x.enc'.s ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
       (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ 32#64) ∗
       localFrameRest (s0.sp - 1200#64) ∗
       savedCells s0 ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool lim st sf ∗
       stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace⌝ ∗
             chunkAt x.outA x.chunk ∗
             polyEncoderAt A.repAlloc x.encA x.enc' ∗
             tokenInitPlacedAt ∗
             reduceTablePlacedAt ∗
             A.pool lim (M.stepEvents (rustDeallocEvents 32 1) st) sf1 ∗
             stackAt s0.sp polyNextChunkStack ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1) := by
  refine SepWP.mono
    (epilogue_placed_acp_sepWP M A lim st ext hA x R s0 sf out_ptr hout_ne hidx_chunk hidx_enc'
      hpc hrun hsp hsp0 htr hx20 hx24 hx27 hvregs)
    fun sf1 P_f _ _ ⟨himp, hsp1, hcs1⟩ => ⟨fun hm => ?_, hsp1, hcs1⟩
  have hq := himp hm
  rw [satisfies_pure_sepConj] at hq ⊢
  exact ⟨hq.1.1, hq.2⟩

/-! ## 4. Budget-Threaded Prologue (`+0..+92`, Block `416`) -/

set_option maxHeartbeats 800000 in
private theorem prologue_placed_seg_sepWP [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (x : PolyNextChunkGhost) (tag : BitVec 64) (restEnc : SepProp)
    {post : State → SepProp → Prop}
    (s0 : State)
    (hpc : s0.pc = (blkPl_416).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA)
    (hfit : FitsEnv M lim st NextChunkPrologueEnv)
    (hpost : ∀ (s1 : State) (P1 : SepProp) (out_ptr : BitVec 64),
      out_ptr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 92#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 1200#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      s1.readReg64 .x9 = (tag.setWidth 32).setWidth 64 →
      s1.readReg64 .x19 = x.encA + 8#64 →
      s1.readReg64 .x24 = x.encA →
      s1.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      (P1 ⊢
        memRegion out_ptr 32 ∗
        A.live out_ptr 32 1 ∗
        memRegion x.outA chunkSize ∗
        (x.encA ↦₆₄ tag) ∗
        restEnc ∗
        ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
        memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
        (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
        (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
        (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
        (((s0.sp - 1200#64) + 248#64) ↦₆₄ 0#64) ∗
        localFrameRest (s0.sp - 1200#64) ∗
        savedCells s0 ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim (M.stepEvents (rustAllocEvents 32 1) st) s1 ∗
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 92#64) s0
      (memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ tag) ∗
       restEnc ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool lim st s0 ∗
       stackAt s0.sp polyNextChunkStack)
      post := by
  have hlayout : RustLayoutOk 32 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  have hfit_ev : FitsEvents M lim st (rustAllocEvents 32 1) :=
    (fitsEnv_nextChunkPrologue_iff).mp hfit
  rcases (by simpa [rustAllocEvents] using hfit_ev : FitsEvent M lim st (.alloc 32) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h32_toNat : (32#64 : BitVec 64).toNat = 32 := rfl
  have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  apply SepWP.fold (prologue_stack_split s0) (by sep_focus)
  apply sepWP_exists_left_sep; intro v29
  apply sepWP_exists_left_sep; intro v30
  apply sepWP_exists_left_sep; intro v28
  apply sepWP_exists_left_sep; intro v27
  apply sepWP_exists_left_sep; intro v26
  apply sepWP_exists_left_sep; intro v25
  apply sepWP_exists_left_sep; intro v24
  apply sepWP_exists_left_sep; intro v23
  apply sepWP_exists_left_sep; intro v22
  apply sepWP_exists_left_sep; intro v21
  apply sepWP_exists_left_sep; intro v20
  apply sepWP_exists_left_sep; intro v19
  apply sepWP_exists_left_sep; intro u0
  apply sepWP_exists_left_sep; intro u56
  apply sepWP_exists_left_sep; intro u232
  apply sepWP_exists_left_sep; intro u240
  apply sepWP_exists_left_sep; intro u248
  wp_conv_pre =>
    rw [CryptoVerification.SpqrV1.Poly.NextChunk.pointsTo32_eq_pointsTo16_pair
          (x.encA + polyEncoderIdxOff) x.enc.idx,
        pointsTo64_eq_pointsTo32_pair x.encA tag]
    dsimp only [polyEncoderIdxOff]
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_sf0 : sf.trace = s0.trace := by
    simpa [arm64_norm, wp_norm] using (by assumption : sf.trace = _)
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (32, 1, st)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have htr_sf1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr_sf0] using ht
  wp_steps_sync_pool ((blkPl_416).base + 92#64)
  simp only [State.setMem_setMem]
  have hfold_tag :
      (x.encA ↦₃₂ tag.setWidth 32) ∗ ((x.encA + 4#64) ↦₃₂ (tag >>> 32).setWidth 32) ⊢
        (x.encA ↦₆₄ tag) := by
    rw [← pointsTo64_eq_pointsTo32_pair x.encA tag]
    exact Entails.refl _
  apply SepWP.fold hfold_tag (by sep_focus)
  have hfold_idx :
      ((x.encA + 392#64) ↦₁₆ x.enc.idx.setWidth 16) ∗
        (((x.encA + 392#64) + 2#64) ↦₁₆ (x.enc.idx >>> 16).setWidth 16) ⊢
        ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) := by
    dsimp only [polyEncoderIdxOff]
    rw [← CryptoVerification.SpqrV1.Poly.NextChunk.pointsTo32_eq_pointsTo16_pair
          (x.encA + 392#64) x.enc.idx]
    exact Entails.refl _
  apply SepWP.fold hfold_idx (by sep_focus)
  have hfold_rest :
      ((s0.sp - 1200#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 1200#64) + 8#64) 48 ∗
        memRegion ((s0.sp - 1200#64) + 64#64) 168 ∗
        memRegion ((s0.sp - 1200#64) + 256#64) 848 ⊢
        localFrameRest (s0.sp - 1200#64) :=
    localFrameRest_fold_prologue (s0.sp - 1200#64) 0#64
  apply SepWP.fold hfold_rest (by sep_focus)
  have hfold_saved :
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
        savedCells s0 := by
    unfold savedCells
    exact Entails.refl _
  apply SepWP.fold hfold_saved (by sep_focus)
  wp_conv_pre => simp only [arm64_norm, wp_norm, *]
  have hfold_callee :
      memRegion ((s0.sp - 1200#64) - 17232#64) 13136 ∗
        stackAt (s0.sp - 1200#64) allocHookStack ⊢
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack := by
    rw [← stackAt_nextChunkCallee_split_allocHook (s0.sp - 1200#64)]
    exact Entails.refl _
  apply SepWP.fold hfold_callee (by sep_focus)
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  refine hpost _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [arm64_norm, wp_norm, Reg.x0, Reg.x8, Reg.x9, Reg.x19, Reg.x24, Reg.x27, Reg.x29,
      Reg.lr, *]
  · simp only [arm64_norm, wp_norm, *]
  · simp only [arm64_norm, wp_norm, *]
  · simp only [arm64_norm, wp_norm, htr_sf1]
  · simp only [arm64_norm, wp_norm, *]
  · simp only [arm64_norm, wp_norm, Reg.x0, Reg.x8, Reg.x9, Reg.x19, Reg.x24, Reg.x27, Reg.x29,
      Reg.lr, *]
  · simp only [arm64_norm, wp_norm, Reg.x0, Reg.x8, Reg.x9, Reg.x19, Reg.x24, Reg.x27, Reg.x29,
      Reg.lr, *]
  · simp only [arm64_norm, wp_norm, Reg.x0, Reg.x8, Reg.x9, Reg.x19, Reg.x24, Reg.x27, Reg.x29,
      Reg.lr, *]
  · simp only [arm64_norm, wp_norm, Reg.x0, Reg.x8, Reg.x9, Reg.x19, Reg.x24, Reg.x27, Reg.x29,
      Reg.lr, *]
  · simp only [arm64_norm, wp_norm, Reg.x0, Reg.x8, Reg.x9, Reg.x19, Reg.x24, Reg.x27, Reg.x29,
      Reg.lr, *]
  · simp only [arm64_norm]
    exact Entails.of_eq (by sep_ac_rfl)

theorem prologue_placed_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (x : PolyNextChunkGhost) (tag : BitVec 64) (restEnc _R : SepProp)
    {Q Q_panic : State → SepProp → Prop}
    (s0 : State)
    (hpc : s0.pc = (blkPl_416).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA)
    (hfit : FitsEnv M lim st NextChunkPrologueEnv)
    (hcont : ∀ s1 (out_ptr : BitVec 64),
      out_ptr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 92#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 1200#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      s1.readReg64 .x9 = (tag.setWidth 32).setWidth 64 →
      s1.readReg64 .x19 = x.encA + 8#64 →
      s1.readReg64 .x24 = x.encA →
      s1.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1
        (memRegion out_ptr 32 ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ tag) ∗
         restEnc ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ 0#64) ∗
         localFrameRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitPlacedAt ∗
         reduceTablePlacedAt ∗
         A.pool lim (M.stepEvents (rustAllocEvents 32 1) st) s1 ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s0
      (memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ tag) ∗
       restEnc ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool lim st s0 ∗
       stackAt s0.sp polyNextChunkStack)
      Q Q_panic :=
  SepWPp.of_sepWP
    (prologue_placed_seg_sepWP M A lim st ext hA x tag restEnc s0 hpc hrun hsp0 hx0 hx8 hfit
      fun s1 _P1 out_ptr hout hpc1 hrun1 hsp1 htr1 hvregs1 hx9 hx19 hx24 hx27 hx29 hent =>
        SepWPp.weaken_pre hent
          (hcont s1 out_ptr hout hpc1 hrun1 hsp1 htr1 hvregs1 hx9 hx19 hx24 hx27 hx29))

/-- `LibsignalCodeLoaded`-preserving wrapper around `prologue_placed_sepWPp` (`+0..+92`, Block `416`)
    for cross-block callers (`PolysLoop`, `PointsToPolys*`, `NextChunk/Proof`). -/
theorem prologue_lscl_placed_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (x : PolyNextChunkGhost) (tag : BitVec 64) (restEnc _R : SepProp)
    {Q Q_panic : State → SepProp → Prop}
    (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_416).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA)
    (hfit : FitsEnv M lim st NextChunkPrologueEnv)
    (hcont : ∀ s1 (out_ptr : BitVec 64),
      out_ptr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 92#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 1200#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.readReg64 .x9 = (tag.setWidth 32).setWidth 64 →
      s1.readReg64 .x19 = x.encA + 8#64 →
      s1.readReg64 .x24 = x.encA →
      s1.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1
        (memRegion out_ptr 32 ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ tag) ∗
         restEnc ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ 0#64) ∗
         localFrameRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitPlacedAt ∗
         reduceTablePlacedAt ∗
         A.pool lim (M.stepEvents (rustAllocEvents 32 1) st) s1 ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s0
      (memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ tag) ∗
       restEnc ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool lim st s0 ∗
       stackAt s0.sp polyNextChunkStack)
      Q Q_panic :=
  sepWPp_seq_lscl hcl0
    (prologue_placed_seg_sepWP M A lim st ext hA x tag restEnc s0 hpc hrun hsp0 hx0 hx8 hfit
      fun s1 _P1 out_ptr hout hpc1 hrun1 hsp1 htr1 hvregs1 hx9 hx19 hx24 hx27 hx29 hent hcl1 =>
        SepWPp.weaken_pre hent
          (hcont s1 out_ptr hout hpc1 hrun1 hsp1 htr1 hvregs1 hcl1 hx9 hx19 hx24 hx27 hx29))

set_option maxHeartbeats 800000 in
/-- `AllocCallPreserved`-strengthened prologue (`+0..+92`, Block `416`) when the caller additionally
    supplies `HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec`. -/
theorem prologue_placed_acp_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hshim_vm : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (x : PolyNextChunkGhost) (tag : BitVec 64) (restEnc _R : SepProp)
    {Q Q_panic : State → SepProp → Prop}
    (s0 : State)
    (hpc : s0.pc = (blkPl_416).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA)
    (hfit : FitsEnv M lim st NextChunkPrologueEnv)
    (hcont : ∀ s1 (out_ptr : BitVec 64),
      out_ptr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 92#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 1200#64 →
      s1.trace = s0.trace →
      AllocCallPreserved s0 s1 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      s1.readReg64 .x9 = (tag.setWidth 32).setWidth 64 →
      s1.readReg64 .x19 = x.encA + 8#64 →
      s1.readReg64 .x24 = x.encA →
      s1.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1
        (memRegion out_ptr 32 ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ tag) ∗
         restEnc ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ 0#64) ∗
         localFrameRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitPlacedAt ∗
         reduceTablePlacedAt ∗
         A.pool lim (M.stepEvents (rustAllocEvents 32 1) st) s1 ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s0
      (memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ tag) ∗
       restEnc ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool lim st s0 ∗
       stackAt s0.sp polyNextChunkStack)
      Q Q_panic := by
  have hlayout : RustLayoutOk 32 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  have hfit_ev : FitsEvents M lim st (rustAllocEvents 32 1) :=
    (fitsEnv_nextChunkPrologue_iff).mp hfit
  rcases (by simpa [rustAllocEvents] using hfit_ev : FitsEvent M lim st (.alloc 32) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h32_toNat : (32#64 : BitVec 64).toNat = 32 := rfl
  have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
  have hshim :
      subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec :=
    spqr_hook_ok_of_mem hshim_vm
  dsimp only [rustAllocShimVmSpec] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA hshim_vm
  apply SepWPp.of_sepWP (mid := (blkPl_416).base + 92#64)
  apply SepWP.fold (prologue_stack_split s0) (by sep_focus)
  apply sepWP_exists_left_sep; intro v29
  apply sepWP_exists_left_sep; intro v30
  apply sepWP_exists_left_sep; intro v28
  apply sepWP_exists_left_sep; intro v27
  apply sepWP_exists_left_sep; intro v26
  apply sepWP_exists_left_sep; intro v25
  apply sepWP_exists_left_sep; intro v24
  apply sepWP_exists_left_sep; intro v23
  apply sepWP_exists_left_sep; intro v22
  apply sepWP_exists_left_sep; intro v21
  apply sepWP_exists_left_sep; intro v20
  apply sepWP_exists_left_sep; intro v19
  apply sepWP_exists_left_sep; intro u0
  apply sepWP_exists_left_sep; intro u56
  apply sepWP_exists_left_sep; intro u232
  apply sepWP_exists_left_sep; intro u240
  apply sepWP_exists_left_sep; intro u248
  wp_conv_pre =>
    rw [CryptoVerification.SpqrV1.Poly.NextChunk.pointsTo32_eq_pointsTo16_pair
          (x.encA + polyEncoderIdxOff) x.enc.idx,
        pointsTo64_eq_pointsTo32_pair x.encA tag]
    dsimp only [polyEncoderIdxOff]
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have hacp1 : AllocCallPreserved s0 sf := by assumption
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (32, 1, st)
  have hacp2 : AllocCallPreserved sf sf_1 := by assumption
  have hacp3 : AllocCallPreserved s0 sf_1 := acp_trans hacp1 hacp2
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  wp_steps_sync_pool ((blkPl_416).base + 92#64)
  simp only [State.setMem_setMem]
  have hfold_tag :
      (x.encA ↦₃₂ tag.setWidth 32) ∗ ((x.encA + 4#64) ↦₃₂ (tag >>> 32).setWidth 32) ⊢
        (x.encA ↦₆₄ tag) := by
    rw [← pointsTo64_eq_pointsTo32_pair x.encA tag]
    exact Entails.refl _
  apply SepWP.fold hfold_tag (by sep_focus)
  have hfold_idx :
      ((x.encA + 392#64) ↦₁₆ x.enc.idx.setWidth 16) ∗
        (((x.encA + 392#64) + 2#64) ↦₁₆ (x.enc.idx >>> 16).setWidth 16) ⊢
        ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) := by
    dsimp only [polyEncoderIdxOff]
    rw [← CryptoVerification.SpqrV1.Poly.NextChunk.pointsTo32_eq_pointsTo16_pair
          (x.encA + 392#64) x.enc.idx]
    exact Entails.refl _
  apply SepWP.fold hfold_idx (by sep_focus)
  have hfold_rest :
      ((s0.sp - 1200#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 1200#64) + 8#64) 48 ∗
        memRegion ((s0.sp - 1200#64) + 64#64) 168 ∗
        memRegion ((s0.sp - 1200#64) + 256#64) 848 ⊢
        localFrameRest (s0.sp - 1200#64) :=
    localFrameRest_fold_prologue (s0.sp - 1200#64) 0#64
  apply SepWP.fold hfold_rest (by sep_focus)
  have hfold_saved :
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
        savedCells s0 := by
    unfold savedCells
    exact Entails.refl _
  apply SepWP.fold hfold_saved (by sep_focus)
  wp_conv_pre => simp only [arm64_norm, wp_norm, *]
  have hfold_callee :
      memRegion ((s0.sp - 1200#64) - 17232#64) 13136 ∗
        stackAt (s0.sp - 1200#64) allocHookStack ⊢
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack := by
    rw [← stackAt_nextChunkCallee_split_allocHook (s0.sp - 1200#64)]
    exact Entails.refl _
  apply SepWP.fold hfold_callee (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.weaken_pre ?_
    (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom ?_ ?_ ?_ ?_ (acp_trans hacp3 acp_of_PureStep)
      ?_ ?_ ?_ ?_ ?_ ?_)
  · simp only [arm64_norm]
    exact Entails.of_eq (by sep_ac_rfl)
  all_goals
    simp only [arm64_norm, wp_norm, Reg.x0, Reg.x8, Reg.x9, Reg.x19, Reg.x24, Reg.x27, Reg.x29,
      Reg.lr, hacp3.2.1, *]

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
