/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.ProofPlacedBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare

/-!
# `HookSat` Sibling of `LeavesTopPlacedBudget` (`LeavesTopPlacedBudgetSat`)

Replaces `[HkdfPlacedHooks F (Rust.withPanics ext)]` in Section 8 (`:997..1204`, the 10
Block `350` `<EkSentCt1Received>::recv_ct2_chunk` theorems) of
`LeavesTopPlacedBudget.lean` with `[HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudgetSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalSpqrV1 (MlKem mlkemDecapsSpec)
open CryptoVerification.LibsignalTripleRatchet (memsetName sessionMemmoveSpec)
open CryptoVerification.SpqrV1.Alloc (
  growOneStack spqrHandleErrorSym spqrMemcpySym spqrMemmoveSym
  spqrPanicConstAddOverflowSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
)
open CryptoVerification.SpqrV1.Kdf (spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (
  RecvCt2ChunkGhost spqrAssertFailedU64Sym spqrLibcruxHmacSym' spqrMlkemDecapsSym
  spqrPanicBoundsCheckSym spqrRustDeallocSym' spqrSliceIndexFailSym spqrUnwrapFailedSym
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
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1PlacedBudget (add_chunk_cl_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudget (
  polyDecodedMessagePlacedOkX_of_hooks
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudget (
  hookSat_sessionMemcpyRegionBudget_of_framelessAcp
  hookSat_sessionShimBudget_of_rustAllocShimVm
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (
  RecvCt2ChunkEnv RecvCt2ChunkPlacedOkExt RecvCt2ChunkPlacedOkExtOfEnv
  RecvCt2ChunkPlacedOkExtOfPrePostEnv RecvCt2ChunkPlacedOkX RecvCt2ChunkPlacedOkXOfEnv
  RecvCt2ChunkPlacedOkXOfPrePostEnv RecvCt2PlacedAlloc
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.ProofPlacedBudgetSat (
  recv_ct2_chunk_placed_ok_ext_ofEnv_sat
  recv_ct2_chunk_placed_ok_ext_ofPrePostEnv_sat
  recv_ct2_chunk_placed_ok_ext_of_hooks_sat
  recv_ct2_chunk_placed_ok_ext_sat
  recv_ct2_chunk_placed_ok_x_ofEnv_sat
  recv_ct2_chunk_placed_ok_x_ofPrePostEnv_sat
  recv_ct2_chunk_placed_ok_x_of_hooks_sat
  recv_ct2_chunk_placed_ok_x_sat
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec
)

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x_ofPrePostEnv_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hsub_pre : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent}, RecvCt2ChunkEnv x evs → PreEnv x evs)
    (hsub_post : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent}, RecvCt2ChunkEnv x evs → PostEnv x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkXOfPrePostEnv K F M A lim PreEnv PostEnv ext :=
  recv_ct2_chunk_placed_ok_x_ofPrePostEnv_sat hsub_pre hsub_post hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x_ofEnv_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hsub : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent}, RecvCt2ChunkEnv x evs → Env x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkXOfEnv K F M A lim Env ext :=
  recv_ct2_chunk_placed_ok_x_ofEnv_sat hsub hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkX K F M A lim ext :=
  recv_ct2_chunk_placed_ok_x_sat hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x_of_alloc_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkX K F M A lim ext :=
  ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x_sat hA
    (hookSat_sessionMemcpyRegionBudget_of_framelessAcp hA.memcpy) hmemmove hmemset hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x_of_hooks_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hallocZeroed : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustCliAllocBudgetSpec M A lim true))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym' (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed_u64 : Rust.withPanics ext spqrAssertFailedU64Sym = some Rust.panicked)
    (h_slice_index_fail : Rust.withPanics ext spqrSliceIndexFailSym = some Rust.panicked)
    (h_unwrap_failed : Rust.withPanics ext spqrUnwrapFailedSym = some Rust.panicked)
    (h_panic_bounds_check : Rust.withPanics ext spqrPanicBoundsCheckSym = some Rust.panicked)
    (h_panic_add_overflow : Rust.withPanics ext spqrPanicConstAddOverflowSym = some Rust.panicked) :
    RecvCt2ChunkPlacedOkX K F M A lim ext :=
  recv_ct2_chunk_placed_ok_x_of_hooks_sat
    (add_chunk_cl_placed_ok_x h_handle_error hshim halloc hrealloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks h_handle_error
      (hookSat_sessionShimBudget_of_rustAllocShimVm hshim)
      halloc hrealloc hdealloc hmemcpy hmemset)
    hshim halloc hallocZeroed hdealloc hrealloc hmemcpy_fl hRO hdecaps hhmac
    h_handle_error h_assert_failed_u64 h_slice_index_fail
    h_unwrap_failed h_panic_bounds_check h_panic_add_overflow

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_ofPrePostEnv_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hsub_pre : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent}, RecvCt2ChunkEnv x evs → PreEnv x evs)
    (hsub_post : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent}, RecvCt2ChunkEnv x evs → PostEnv x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExtOfPrePostEnv K F M A lim PreEnv PostEnv ext :=
  recv_ct2_chunk_placed_ok_ext_ofPrePostEnv_sat hsub_pre hsub_post hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_ofEnv_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hsub : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent}, RecvCt2ChunkEnv x evs → Env x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExtOfEnv K F M A lim Env ext :=
  recv_ct2_chunk_placed_ok_ext_ofEnv_sat hsub hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  recv_ct2_chunk_placed_ok_ext_sat hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_of_alloc_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_sat hA
    (hookSat_sessionMemcpyRegionBudget_of_framelessAcp hA.memcpy) hmemmove hmemset hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_of_hooks_sat [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hallocZeroed : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustCliAllocBudgetSpec M A lim true))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym' (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed_u64 : Rust.withPanics ext spqrAssertFailedU64Sym = some Rust.panicked)
    (h_slice_index_fail : Rust.withPanics ext spqrSliceIndexFailSym = some Rust.panicked)
    (h_unwrap_failed : Rust.withPanics ext spqrUnwrapFailedSym = some Rust.panicked)
    (h_panic_bounds_check : Rust.withPanics ext spqrPanicBoundsCheckSym = some Rust.panicked)
    (h_panic_add_overflow : Rust.withPanics ext spqrPanicConstAddOverflowSym = some Rust.panicked) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  recv_ct2_chunk_placed_ok_ext_of_hooks_sat
    (add_chunk_cl_placed_ok_x h_handle_error hshim halloc hrealloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks h_handle_error
      (hookSat_sessionShimBudget_of_rustAllocShimVm hshim)
      halloc hrealloc hdealloc hmemcpy hmemset)
    hshim halloc hallocZeroed hdealloc hrealloc hmemcpy_fl hRO hdecaps hhmac
    h_handle_error h_assert_failed_u64 h_slice_index_fail
    h_unwrap_failed h_panic_bounds_check h_panic_add_overflow

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudgetSat
