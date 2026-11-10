/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.DecodesPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCSBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.Encode1PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# Budget-Threaded Base Definitions and Callee Bridges for Unchunked Encoders

Defines budget-threaded `[LibsignalPlacement]` contract predicates and `withUnchunkedEncodeCSPlaced`
callee bridges for CLI Blocks `458` (`EkSentCt1Received::encode`) and `459` (`Ct1Sent::encode`)
under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.UnchunkedBasePlacedBudget

open Arm64 ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   lsMemcpySym lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (subroutine_ok_withLsCodeLoaded_unchunked subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk
   withUnchunkedEncodeCSPlaced)
open CryptoVerification.Cli.SpqrV1.Alloc.Placed (blkPl_460 lsProg_460)
open CryptoVerification.Cli.SpqrV1.Varint.Placed (blkPl_451 lsProg_451)
open CryptoVerification.Cli.SpqrV1.Auth.Placed (blkPl_454 lsProg_454)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed
  (blkPl_458 blkPl_459 lsProg_458 lsProg_459)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget
  (ct1SentEncodedLenPinnedSpec ekSentCt1ReceivedEncodedLenPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserve2SpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget (authEncodePinnedSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseStagesBudget
  (ct1SentEncodePinnedSpecS ct1SentEncodePinnedSpecXS ct1SentEncodeSpecS ct1SentEncodeSpecXS
   ekSentCt1ReceivedEncodePinnedSpecS ekSentCt1ReceivedEncodePinnedSpecXS
   ekSentCt1ReceivedEncodeSpecS ekSentCt1ReceivedEncodeSpecXS)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93PlacedBudget
  (ct1SentEncodedLen_local1_pinned_placed_ok_x
   ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlacedBudget
  (do_reserve2_placed_ok do_reserve2_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2PlacedBudget
  (encode_varint2_fit_placed_ok encode_varint2_fit_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Auth.Encode1PlacedBudget
  (auth_encode_1_pinned_placed_ok auth_encode_1_pinned_placed_ok_x)

/-! ## 1. Placed Budget Contract Predicates for Blocks `458` & `459` -/

def EkSentCt1ReceivedEncode1PinnedPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_458 H) (blkPl_458).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecS A lim))

def EkSentCt1ReceivedEncode1PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_458 H) (blkPl_458).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpecS A lim))

def EkSentCt1ReceivedEncode1PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_458 H) (blkPl_458).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecXS A lim))

def EkSentCt1ReceivedEncode1PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_458 H) (blkPl_458).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpecXS A lim))

def EkSentCt1ReceivedEncode1PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EkSentCt1ReceivedEncode1PinnedPlacedOk A lim (Rust.withPanics ext)

def EkSentCt1ReceivedEncode1PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EkSentCt1ReceivedEncode1PlacedOk A lim (Rust.withPanics ext)

def EkSentCt1ReceivedEncode1PinnedPlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EkSentCt1ReceivedEncode1PinnedPlacedOkX A lim (Rust.withPanics ext)

def EkSentCt1ReceivedEncode1PlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EkSentCt1ReceivedEncode1PlacedOkX A lim (Rust.withPanics ext)

def Ct1SentEncode1PinnedPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_459 H) (blkPl_459).base
    (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecS A lim))

def Ct1SentEncode1PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_459 H) (blkPl_459).base
    (withLsCodeLoaded lsmpl (ct1SentEncodeSpecS A lim))

def Ct1SentEncode1PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_459 H) (blkPl_459).base
    (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecXS A lim))

def Ct1SentEncode1PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_459 H) (blkPl_459).base
    (withLsCodeLoaded lsmpl (ct1SentEncodeSpecXS A lim))

def Ct1SentEncode1PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  Ct1SentEncode1PinnedPlacedOk A lim (Rust.withPanics ext)

def Ct1SentEncode1PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  Ct1SentEncode1PlacedOk A lim (Rust.withPanics ext)

def Ct1SentEncode1PinnedPlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  Ct1SentEncode1PinnedPlacedOkX A lim (Rust.withPanics ext)

def Ct1SentEncode1PlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  Ct1SentEncode1PlacedOkX A lim (Rust.withPanics ext)

/-! ## 2. Shared `withUnchunkedEncodeCSPlaced` Callee Bridges for `Cli/SpqrV1` Blocks -/

theorem unchunked_ekEncodedLen_cs_placed_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (A : RustAlloc) (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 499)
      (withUnchunkedEncodeCSPlaced s0 (ekSentCt1ReceivedEncodedLenPinnedSpec A)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (subroutine_ok_withLsCodeLoaded_unchunked
      (ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x A H)) hi

theorem unchunked_ct1EncodedLen_cs_placed_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (A : RustAlloc) (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 487)
      (withUnchunkedEncodeCSPlaced s0 (ct1SentEncodedLenPinnedSpec A)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (subroutine_ok_withLsCodeLoaded_unchunked
      (ct1SentEncodedLen_local1_pinned_placed_ok_x A H)) hi

theorem unchunked_encodeVarint2_cs_placed_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf doReserveStack A lim)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc :
      subroutine_ok (lsProg_451 H) (blkPl_451).base _) hi

theorem unchunked_encodeVarint2_cs_placed_ok_x [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf doReserveStackX A lim)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc :
      subroutine_ok (lsProg_451 H) (blkPl_451).base _) hi

theorem unchunked_authEncode1_cs_placed_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 454)
      (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf doReserveStack A lim)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (auth_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc :
      subroutine_ok (lsProg_454 H) (blkPl_454).base _) hi

theorem unchunked_authEncode1_cs_placed_ok_x [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 454)
      (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf doReserveStackX A lim)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (auth_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc :
      subroutine_ok (lsProg_454 H) (blkPl_454).base _) hi

theorem unchunked_doReserve2_cs_placed_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 460)
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf doReserveStack A lim)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (do_reserve2_placed_ok h_panic hshim halloc hrealloc :
      subroutine_ok (lsProg_460 H) (blkPl_460).base _) hi

theorem unchunked_doReserve2_cs_placed_ok_x [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 460)
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf doReserveStackX A lim)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc :
      subroutine_ok (lsProg_460 H) (blkPl_460).base _) hi

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.UnchunkedBasePlacedBudget
