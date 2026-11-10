/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.ProofPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProofPlacedBBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.TopPlacedBudgetAux

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Unconditional Budget-Threaded Placed Contracts

Combines `lagrangeComplete_vm_placed_ok` (Block `373`), `pointsToPolysLoop_polyList_placed_sepWPp`,
and `ProofPlacedBudget` to establish unconditional `[LibsignalPlacement]` budget contracts for
Block `416` over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.TopPlacedBudget

open Arm64 ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement blkPC_373 blkPl_373 lsmpl withLsCodeLoaded)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (lagrangeCompletePlacedSpec)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
  (PolyNextChunkBlockOkX PolyNextChunkCallerOkX PolyNextChunkPlacedOkExt)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProofPlacedBBudget
  (PointsToPolysLoopPlacedBudgetProp pointsToPolysLoop_polyList_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.ProofPlacedBudget
  (PointsToPolysLoopPlacedProp poly_next_chunk_block_ok_x_of_p2p
   poly_next_chunk_caller_ok_x_of_p2p poly_next_chunk_placed_ok_of_p2p
   poly_next_chunk_rodata_placed_ok_of_p2p poly_next_chunk_rodata_ro_placed_ok_of_p2p)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataPlacedBudget (PolyNextChunkRodataPlacedOkExt)

/-- Relocatable `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete` (Block `373`)
    satisfies `withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)` under
    `[LibsignalPlacement]`. -/
theorem lagrangeComplete_vm_placed_ok [LibsignalPlacement] (ext : String → Option (State → State)) :
    subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)) :=
  TopPlacedBudgetAux.lagrangeComplete_vm_placed_ok ext

/-- Discharges `PointsToPolysLoopPlacedBudgetProp M A lim ext` under `[LibsignalPlacement]`. -/
theorem pointsToPolysLoop_placed_budget_prop [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) :
    PointsToPolysLoopPlacedBudgetProp M A lim ext :=
  PointsToPolysProofPlacedBBudget.pointsToPolysLoop_placed_prop
    M A lim ext hA (lagrangeComplete_vm_placed_ok ext)

/-- Discharges `ProofPlacedBudget.PointsToPolysLoopPlacedProp M A lim ext` under
    `[LibsignalPlacement]` via `pointsToPolysLoop_polyList_placed_sepWPp` and
    `lagrangeComplete_vm_placed_ok`. -/
theorem pointsToPolysLoop_placed_prop [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) :
    PointsToPolysLoopPlacedProp M A lim ext :=
  fun s0 s hcl fsp ptsBase hfsp_align pts hlen hbounds
      u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056
      Frame R hpc hrun hsp htrace hx19 hx20 hx28 hx29 hfit hcont =>
    pointsToPolysLoop_polyList_placed_sepWPp hA (lagrangeComplete_vm_placed_ok ext)
      s0 s hcl fsp ptsBase hfsp_align pts hlen hbounds
      u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056
      Frame R hpc hrun hsp htrace hx19 hx20 hx28 hx29 hfit
      fun evs s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
          hevs _hcl_out =>
        hcont s_out evs u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
          hevs

/-- `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (Block `416`)
    satisfies `RodataPlacedBudget.PolyNextChunkRodataPlacedOkExt M A lim ext` (`withLsCodeLoaded`)
    under `[LibsignalPlacement]`. -/
theorem poly_next_chunk_rodata_placed_ok [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) :
    PolyNextChunkRodataPlacedOkExt M A lim ext :=
  poly_next_chunk_rodata_placed_ok_of_p2p M A lim ext hA
    (pointsToPolysLoop_placed_prop M A lim ext hA)

theorem poly_next_chunk_rodata_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    PolyNextChunkRodataPlacedOkExt M A lim ext :=
  poly_next_chunk_rodata_placed_ok M A lim ext hA

/-- `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (Block `416`)
    satisfies `DefsBudget.PolyNextChunkRodataPlacedOkExt M A lim ext` (`withLsCodeRoLoaded`)
    under `[LibsignalPlacement]`. -/
theorem poly_next_chunk_rodata_ro_placed_ok [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) :
    LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget.PolyNextChunkRodataPlacedOkExt
      M A lim ext :=
  poly_next_chunk_rodata_ro_placed_ok_of_p2p M A lim ext hA
    (pointsToPolysLoop_placed_prop M A lim ext hA)

theorem poly_next_chunk_rodata_ro_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget.PolyNextChunkRodataPlacedOkExt
      M A lim ext :=
  poly_next_chunk_rodata_ro_placed_ok M A lim ext hA

/-- `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (Block `416`)
    satisfies `PolyNextChunkPlacedOkExt M A lim ext` (`withLsCodeRoLoaded lsmpl
    (polyNextChunkPlacedSpec M A lim)`) under `[LibsignalPlacement]`. -/
theorem poly_next_chunk_placed_ok [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) :
    PolyNextChunkPlacedOkExt M A lim ext :=
  poly_next_chunk_placed_ok_of_p2p M A lim ext hA
    (pointsToPolysLoop_placed_prop M A lim ext hA)

theorem poly_next_chunk_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    PolyNextChunkPlacedOkExt M A lim ext :=
  poly_next_chunk_placed_ok M A lim ext hA

/-- `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (Block `416`)
    satisfies `PolyNextChunkBlockOkX M A lim ext` (`blockProgram lsmpl 416`) under
    `[LibsignalPlacement]`. -/
theorem poly_next_chunk_block_ok_x [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) :
    PolyNextChunkBlockOkX M A lim ext :=
  poly_next_chunk_block_ok_x_of_p2p M A lim ext hA
    (pointsToPolysLoop_placed_prop M A lim ext hA)

theorem poly_next_chunk_block_ok_x_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    PolyNextChunkBlockOkX M A lim ext :=
  poly_next_chunk_block_ok_x M A lim ext hA

/-- Cross-block caller specialization of `poly_next_chunk_placed_ok` onto any
    `[IsLsBlockProg callerProg i (Rust.withPanics ext)]` (`i < 619`). -/
theorem poly_next_chunk_caller_ok_x [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hA : AllocContractsPlaced M A lim ext)
    (hi : i < 619 := by decide) :
    PolyNextChunkCallerOkX callerProg M A lim :=
  poly_next_chunk_caller_ok_x_of_p2p M A lim ext hA
    (pointsToPolysLoop_placed_prop M A lim ext hA) hi

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.TopPlacedBudget
