/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCS
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.DecodesPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.Encode1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Placed
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# Relocatable Base Definitions and Callee Bridges for Unchunked Encoders

Defines `[LibsignalPlacement]` contract predicates and `withUnchunkedEncodeCSPlaced` callee bridges
for CLI Blocks `458` (`EkSentCt1Received::encode`) and `459` (`Ct1Sent::encode`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Prost.MessageEncode

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr hiding
  vecU8At_eq_header_sep_buf vecU8Buf ofNat_length_beq_zero_of_lt
open CryptoVerification.SpqrV1.Auth hiding
  reserveCap_one_bounds cap_toNat_eq_of_beq lt_cap_toNat_of_beq_false
open CryptoVerification.SpqrV1.Prost.MessageEncode hiding
  EkSentCt1ReceivedEncode1PinnedPlacedOkExt EkSentCt1ReceivedEncode1PlacedOkExt
  EkSentCt1ReceivedEncode1PinnedPlacedOkX EkSentCt1ReceivedEncode1PlacedOkX
  Ct1SentEncode1PinnedPlacedOkExt Ct1SentEncode1PlacedOkExt
  Ct1SentEncode1PinnedPlacedOkX Ct1SentEncode1PlacedOkX
open CryptoVerification.Cli.SpqrV1.Alloc.Placed
open CryptoVerification.Cli.SpqrV1.Varint.Placed
open CryptoVerification.Cli.SpqrV1.Auth.Placed
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.Placed
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed
open CryptoVerification.Cli.SpqrV1.Varint
  (encode_varint2_fit_placed_ok encode_varint2_fit_placed_ok_x
   do_reserve2_placed_ok do_reserve2_placed_ok_x)
open CryptoVerification.Cli.SpqrV1.Auth
  (auth_encode_1_pinned_placed_ok auth_encode_1_pinned_placed_ok_x)
open CryptoVerification.Cli.SpqrV1.ProtoRepr
  (ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x
   ct1SentEncodedLen_local1_pinned_placed_ok_x)

/-! ## 1. Placed Contract Predicates for Blocks `458` & `459` -/

def EkSentCt1ReceivedEncode1PinnedPlacedOk [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_458 H) (blkPl_458).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpec A))

def EkSentCt1ReceivedEncode1PlacedOk [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_458 H) (blkPl_458).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpec A))

def EkSentCt1ReceivedEncode1PinnedPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_458 H) (blkPl_458).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecX A))

def EkSentCt1ReceivedEncode1PlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_458 H) (blkPl_458).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpecX A))

def EkSentCt1ReceivedEncode1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  EkSentCt1ReceivedEncode1PinnedPlacedOk A (Rust.withPanics ext)

def EkSentCt1ReceivedEncode1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  EkSentCt1ReceivedEncode1PlacedOk A (Rust.withPanics ext)

def EkSentCt1ReceivedEncode1PinnedPlacedOkExtX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  EkSentCt1ReceivedEncode1PinnedPlacedOkX A (Rust.withPanics ext)

def EkSentCt1ReceivedEncode1PlacedOkExtX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  EkSentCt1ReceivedEncode1PlacedOkX A (Rust.withPanics ext)

def Ct1SentEncode1PinnedPlacedOk [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_459 H) (blkPl_459).base
    (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpec A))

def Ct1SentEncode1PlacedOk [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_459 H) (blkPl_459).base
    (withLsCodeLoaded lsmpl (ct1SentEncodeSpec A))

def Ct1SentEncode1PinnedPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_459 H) (blkPl_459).base
    (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecX A))

def Ct1SentEncode1PlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_459 H) (blkPl_459).base
    (withLsCodeLoaded lsmpl (ct1SentEncodeSpecX A))

def Ct1SentEncode1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  Ct1SentEncode1PinnedPlacedOk A (Rust.withPanics ext)

def Ct1SentEncode1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  Ct1SentEncode1PlacedOk A (Rust.withPanics ext)

def Ct1SentEncode1PinnedPlacedOkExtX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  Ct1SentEncode1PinnedPlacedOkX A (Rust.withPanics ext)

def Ct1SentEncode1PlacedOkExtX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  Ct1SentEncode1PlacedOkX A (Rust.withPanics ext)

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
    {A : RustAlloc} (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf doReserveStack A)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc) hi

theorem unchunked_encodeVarint2_cs_placed_ok_x [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {A : RustAlloc} (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf doReserveStackX A)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc) hi

theorem unchunked_authEncode1_cs_placed_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {A : RustAlloc} (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 454)
      (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf doReserveStack A)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (auth_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc) hi

theorem unchunked_authEncode1_cs_placed_ok_x [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {A : RustAlloc} (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 454)
      (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf doReserveStackX A)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (auth_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc) hi

theorem unchunked_doReserve2_cs_placed_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {A : RustAlloc} (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 460)
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf doReserveStack A)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (do_reserve2_placed_ok h_panic hshim halloc hrealloc) hi

theorem unchunked_doReserve2_cs_placed_ok_x [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {A : RustAlloc} (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 460)
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf doReserveStackX A)) :=
  subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk (callerProg := callerProg) s0 hcl0
    (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc) hi

end CryptoVerification.Cli.SpqrV1.Prost.MessageEncode
