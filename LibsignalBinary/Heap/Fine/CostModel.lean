/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.CreditInst
public import LibsignalBinary.Heap.Fine.MallocImplFine
public import LibsignalBinary.Heap.Fine.MallocEntryFine
public import LibsignalBinary.Heap.Fine.CallocFine
public import LibsignalBinary.Heap.Fine.FreeFineInst
public import LibsignalBinary.Heap.Fine.AlignedPosixFine
public import LibsignalBinary.Heap.Fine.ReallocEntryFine
public import LibsignalBinary.Heap.Fine.ReallocStagesFine
public import LibsignalBinary.Heap.Fine.ReallocStage3EntryFine
public import LibsignalBinary.Heap.Fine.Footprint
public import LibsignalBinary.Heap.MallocngBridgeBudget

/-!
# Fine-Grained `MallocngCostModelSound` and Budget Pool Instantiation

Assembles the six placed `mallocng` entrypoint verifications (`malloc`, `free`, `calloc`, `realloc`,
`aligned_alloc`, `posix_memalign`) with `Init`, `Footprint`, and `CreditInst` to establish
`MallocngCostModelSound fineCostModel fineCostModelIface` and instantiate `fineRustCliAllocBudget`.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries VerifiedLibraries.Mallocng.Proofs
open VerifiedLibraries.Mallocng hiding AllocCostModel AllocEvent MallocngCostModelIface
  MallocngCostModelSound MallocngModelEnv MallocngModelPlacedEntryContracts
  MallocngModelPostEnv MallocngStepOomCond
open VerifiedLibraries.RustStd (MallocngCEntryAddrs mallocngPlacedCAddrs)
open LibsignalBinary.Heap

/-! ## Unconditional Placed Entrypoints -/

theorem placed_malloc_fine_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "malloc"
      (fineMallocSpec svc γ (mallocngAddrsOfPlacement mpl)) :=
  placed_malloc_fine_entry_ok placed_libcMallocImpl_fine_ok mpl svc hPlace hSvc γ

theorem placed_free_fine_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "free"
      (fineFreeSpec γ (mallocngAddrsOfPlacement mpl)) :=
  placed_free_fine_entry_ok mpl svc hPlace hSvc γ

theorem placed_calloc_fine_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "calloc"
      (fineCallocSpec svc γ (mallocngAddrsOfPlacement mpl)) :=
  placed_calloc_fine_entry_ok placed_defaultMalloc_fine_ok mpl svc hPlace hSvc γ

theorem placed_libcRealloc_fine_uncond_ok : LibcReallocFineStmt :=
  placed_libcRealloc_fine_ok realloc_stage2_fine_ok realloc_stage3_fine_ok

theorem placed_realloc_fine_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "realloc"
      (fineReallocSpec svc γ (mallocngAddrsOfPlacement mpl)) :=
  placed_realloc_fine_entry_of_stages realloc_stage2_fine_ok realloc_stage3_fine_ok
    mpl svc hPlace hSvc γ

theorem placed_alignedAlloc_fine_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "aligned_alloc"
      (fineAlignedAllocSpec svc γ (mallocngAddrsOfPlacement mpl)) :=
  placed_alignedAlloc_fine_entry_ok placed_libcMallocImpl_raw_fine_ok mpl svc hPlace hSvc γ

theorem placed_posixMemalign_fine_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "posix_memalign"
      (finePosixMemalignSpec svc γ (mallocngAddrsOfPlacement mpl)) :=
  placed_posixMemalign_fine_entry_ok placed_libcMallocImpl_raw_fine_ok mpl svc hPlace hSvc γ

/-! ## `MallocngCostModelSound` Instance -/

/-- All six placed C entrypoints (`malloc`, `free`, `calloc`, `realloc`, `aligned_alloc`,
    `posix_memalign`) verified against `fineCostModelIface` over `fineCostModel`. -/
theorem finePlacedEntryContracts
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) :
    MallocngModelPlacedEntryContracts fineCostModel fineCostModelIface mpl svc where
  malloc_ok γ := fineModelMalloc_of_fine (placed_malloc_fine_ok mpl svc hPlace hSvc γ)
  free_ok γ := fineModelFree_of_fine (placed_free_fine_ok mpl svc hPlace hSvc γ)
  calloc_ok γ := fineModelCalloc_of_fine (placed_calloc_fine_ok mpl svc hPlace hSvc γ)
  realloc_ok γ := fineModelRealloc_of_fine (placed_realloc_fine_ok mpl svc hPlace hSvc γ)
  alignedAlloc_ok γ :=
    fineModelAlignedAlloc_of_fine (placed_alignedAlloc_fine_ok mpl svc hPlace hSvc γ)
  posixMemalign_ok γ :=
    fineModelPosixMemalign_of_fine (placed_posixMemalign_fine_ok mpl svc hPlace hSvc γ)

/-- Soundness of `fineCostModel` and `fineCostModelIface` over `mallocngLib`. -/
theorem fineCostModelSound : MallocngCostModelSound fineCostModel fineCostModelIface where
  init := fineHeap_init
  init_resources := fineHeap_init_resources
  heap_split_runtime := fineHeap_split_runtime
  block_nonnull := fineBlock_nonnull
  block_exclusive := fineBlock_exclusive
  heap_footprint_bound := fineHeap_footprint_bound
  entries_ok mpl svc hPlace hSvc := finePlacedEntryContracts mpl svc hPlace hSvc

/-! ## Budget-Threaded Rust Pool and C Entrypoint Contracts -/

/-- Budget-threaded `RustCliAllocBudget fineCostModel` pool at concrete `MallocngAddrs`. -/
def fineRustCliAllocBudgetAt
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64) :
    RustCliAllocBudget fineCostModel :=
  mallocngRustCliAllocBudgetAt fineCostModel fineCostModelIface fineCostModelSound γ A tp brkStart

/-- Budget-threaded `RustCliAllocBudget fineCostModel` pool at a `MultiPlacement`. -/
def fineRustCliAllocBudget
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    RustCliAllocBudget fineCostModel :=
  mallocngRustCliAllocBudget fineCostModel fineCostModelIface fineCostModelSound γ mpl tp brkStart

/-- Program-level C entrypoint contracts (`malloc`, `free`, `calloc`, `realloc`, `aligned_alloc`,
    `posix_memalign`) over `fineCostModel` for any program `P` containing `mallocngLib`. -/
theorem fineProgBudgetCContracts
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64) :
    MallocngProgBudgetCContracts fineCostModel fineCostModelIface γ
      (mallocngAddrsOfPlacement mpl) tp brkStart
      P (mallocngPlacedCAddrs mpl) (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc") :=
  mallocngProgBudgetCContracts_of_placed fineCostModelSound hP γ tp brkStart

end LibsignalBinary.Heap.Fine
