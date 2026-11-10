/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudget

/-!
# Budget-Threaded Extended-Stack Wrapper for `<PolyDecoder as Decoder>::add_chunk`

Re-exports `addChunkSpecX_of_addChunkSpec` and `add_chunk_placed_ok_x` under `RustCliAllocBudget M`
for Block `419`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofXBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_419 blkPl_419 lsmpl)
open CryptoVerification.LibsignalTripleRatchet (sessionMemmoveSpec)
open CryptoVerification.SpqrV1.Alloc (growOneStack spqrMemmoveSym)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.LoopPlacedBudget (
  withAllocCallPreserved
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget (
  growOnePtFullSpec growOnePtSpec
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (
  withAllocVmPreserved
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (
  AddChunkPlacedOkX addChunkSpec addChunkSpecX
)

/-- `addChunkSpec M A lim` entails `addChunkSpecX M A lim` by framing the unused bottom stack region. -/
theorem addChunkSpecX_of_addChunkSpec {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok P addr (addChunkSpec M A lim)) :
    subroutine_ok P addr (addChunkSpecX M A lim) :=
  LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudget.addChunkSpecX_of_addChunkSpec h

theorem add_chunk_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withAllocCallPreserved (growOnePtFullSpec M A lim)))
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withAllocCallPreserved (growOnePtSpec M A lim))) :
    AddChunkPlacedOkX M A lim ext :=
  LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudget.add_chunk_placed_ok_x
    hmemmove_sat hgrow_full hgrow_empty

end LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofXBudget
