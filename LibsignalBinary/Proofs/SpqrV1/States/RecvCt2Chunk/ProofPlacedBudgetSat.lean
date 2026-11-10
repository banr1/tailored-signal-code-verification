/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.ProofPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare

/-!
# `HookSat` Sibling of `RecvCt2Chunk.ProofPlacedBudget` (`ProofPlacedBudgetSat`)

Replaces `[HkdfPlacedHooks F (Rust.withPanics ext)]` in the 8 top-level theorems of
`RecvCt2Chunk.ProofPlacedBudget` (`:710..819` and `:899..998`) with
`[HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.ProofPlacedBudgetSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkPC_419 blkPl_419 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (MlKem mlkemDecapsSpec)
open CryptoVerification.SpqrV1.Alloc (
  spqrHandleErrorSym spqrMemcpySym spqrPanicConstAddOverflowSym
  spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
)
open CryptoVerification.SpqrV1.Kdf (spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (
  RecvCt2ChunkGhost spqrAssertFailedU64Sym spqrLibcruxHmacSym'
  spqrMlkemDecapsSym spqrPanicBoundsCheckSym spqrRustDeallocSym' spqrSliceIndexFailSym
  spqrUnwrapFailedSym
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget rustCliAllocBudgetSpec
  rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (
  framelessMemcpyAcpSpec sessionMemcpyRegionROSpec
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (addChunkSpecX)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (
  PolyDecodedMessagePlacedOkX RecvCt2ChunkEnv
  RecvCt2ChunkPlacedOkExt RecvCt2ChunkPlacedOkExtOfEnv
  RecvCt2ChunkPlacedOkExtOfPrePostEnv RecvCt2ChunkPlacedOkX
  RecvCt2ChunkPlacedOkXOfEnv RecvCt2ChunkPlacedOkXOfPrePostEnv
  RecvCt2PlacedAlloc
  recvCt2ChunkPlacedOkExtOfEnv_of_okX recvCt2ChunkPlacedOkExtOfPrePostEnv_of_okX
  recvCt2ChunkPlacedOkExt_of_okX
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudgetSat (
  hkdfToSlice_placed_ok_of_hooks_sat
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.ProofPlacedBudget (
  recv_ct2_chunk_placed_ok_of_contracts
  recv_ct2_chunk_placed_ok_of_contracts_ofEnv
  recv_ct2_chunk_placed_ok_of_contracts_ofPrePostEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)

theorem recv_ct2_chunk_placed_ok_x_ofPrePostEnv_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hsub_pre : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → PreEnv x evs)
    (hsub_post : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → PostEnv x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkXOfPrePostEnv K F M A lim PreEnv PostEnv ext :=
  recv_ct2_chunk_placed_ok_of_contracts_ofPrePostEnv hsub_pre hsub_post hA hadd_ok hdec_ok hdecaps
    (hkdfToSlice_placed_ok_of_hooks_sat F) hhmac

theorem recv_ct2_chunk_placed_ok_x_ofEnv_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hsub : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → Env x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkXOfEnv K F M A lim Env ext :=
  recv_ct2_chunk_placed_ok_of_contracts_ofEnv hsub hA hadd_ok hdec_ok hdecaps
    (hkdfToSlice_placed_ok_of_hooks_sat F) hhmac

theorem recv_ct2_chunk_placed_ok_x_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkX K F M A lim ext :=
  recv_ct2_chunk_placed_ok_of_contracts hA hadd_ok hdec_ok hdecaps
    (hkdfToSlice_placed_ok_of_hooks_sat F) hhmac

theorem recv_ct2_chunk_placed_ok_x_of_hooks_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hallocZeroed :
      HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustCliAllocBudgetSpec M A lim true))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym' (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed_u64 : Rust.withPanics ext spqrAssertFailedU64Sym = some Rust.panicked)
    (h_slice_index_fail : Rust.withPanics ext spqrSliceIndexFailSym = some Rust.panicked)
    (h_unwrap_failed : Rust.withPanics ext spqrUnwrapFailedSym = some Rust.panicked)
    (h_panic_bounds_check : Rust.withPanics ext spqrPanicBoundsCheckSym = some Rust.panicked)
    (h_panic_add_overflow : Rust.withPanics ext spqrPanicConstAddOverflowSym = some Rust.panicked) :
    RecvCt2ChunkPlacedOkX K F M A lim ext :=
  recv_ct2_chunk_placed_ok_x_sat
    { handleError := h_handle_error
      assertFailedU64 := h_assert_failed_u64
      sliceIndexFail := h_slice_index_fail
      unwrapFailed := h_unwrap_failed
      panicBoundsCheck := h_panic_bounds_check
      panicConstAddOverflow := h_panic_add_overflow
      shim := hshim
      alloc := halloc
      allocZeroed := hallocZeroed
      dealloc := hdealloc
      realloc := hrealloc
      memcpy := hmemcpy
      memcpyRO := hRO }
    hadd_ok hdec_ok hdecaps hhmac

theorem recv_ct2_chunk_placed_ok_ext_ofPrePostEnv_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hsub_pre : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → PreEnv x evs)
    (hsub_post : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → PostEnv x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExtOfPrePostEnv K F M A lim PreEnv PostEnv ext :=
  recvCt2ChunkPlacedOkExtOfPrePostEnv_of_okX
    (recv_ct2_chunk_placed_ok_x_ofPrePostEnv_sat hsub_pre hsub_post hA hadd_ok hdec_ok hdecaps hhmac)

theorem recv_ct2_chunk_placed_ok_ext_ofEnv_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hsub : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → Env x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExtOfEnv K F M A lim Env ext :=
  recvCt2ChunkPlacedOkExtOfEnv_of_okX
    (recv_ct2_chunk_placed_ok_x_ofEnv_sat hsub hA hadd_ok hdec_ok hdecaps hhmac)

theorem recv_ct2_chunk_placed_ok_ext_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  recvCt2ChunkPlacedOkExt_of_okX
    (recv_ct2_chunk_placed_ok_x_sat hA hadd_ok hdec_ok hdecaps hhmac)

theorem recv_ct2_chunk_placed_ok_ext_of_hooks_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hallocZeroed :
      HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustCliAllocBudgetSpec M A lim true))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym' (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed_u64 : Rust.withPanics ext spqrAssertFailedU64Sym = some Rust.panicked)
    (h_slice_index_fail : Rust.withPanics ext spqrSliceIndexFailSym = some Rust.panicked)
    (h_unwrap_failed : Rust.withPanics ext spqrUnwrapFailedSym = some Rust.panicked)
    (h_panic_bounds_check : Rust.withPanics ext spqrPanicBoundsCheckSym = some Rust.panicked)
    (h_panic_add_overflow : Rust.withPanics ext spqrPanicConstAddOverflowSym = some Rust.panicked) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  recvCt2ChunkPlacedOkExt_of_okX
    (recv_ct2_chunk_placed_ok_x_of_hooks_sat hadd_ok hdec_ok hshim halloc hallocZeroed hdealloc
      hrealloc hmemcpy hRO hdecaps hhmac h_handle_error h_assert_failed_u64 h_slice_index_fail
      h_unwrap_failed h_panic_bounds_check h_panic_add_overflow)

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.ProofPlacedBudgetSat
