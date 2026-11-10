/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.UnchunkedBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1Sent1Placed
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent1
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1SentPlaced
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# Relocatable Top-Level Contracts for `encode<Ct1Sent> [local#3]` (Block `459`)

Instantiates pinned/unpinned `subroutine_ok` contracts and `EncodeToVec` callee bridges for
`encode<Ct1Sent> [local#3]` on CLI Block `459` under `[LibsignalPlacement]`.
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
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Prost.MessageEncode hiding
  reserveCap_one_bounds cap_toNat_eq_of_beq lt_cap_toNat_of_beq_false
  EkSentCt1ReceivedEncode1PinnedPlacedOkExt EkSentCt1ReceivedEncode1PlacedOkExt
  EkSentCt1ReceivedEncode1PinnedPlacedOkX EkSentCt1ReceivedEncode1PlacedOkX
  Ct1SentEncode1PinnedPlacedOkExt Ct1SentEncode1PlacedOkExt
  Ct1SentEncode1PinnedPlacedOkX Ct1SentEncode1PlacedOkX
  ct1_sent_encode_1_pinned_placed_ok ct1_sent_encode_1_pinned_placed_ok_x
  ct1_sent_encode_1_pinned_placed_ok_uncond ct1_sent_encode_1_placed_ok
  ct1_sent_encode_1_pinned_placed_ok_x_uncond ct1_sent_encode_1_placed_ok_x
  etv_ct1SentEncode_placed_ok etv_ct1SentEncode_placed_ok_x
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (etvCt1SentEncodeSpecOf)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed

/-! ## 1. Top-Level `[LibsignalPlacement]` `subroutine_ok` Contracts for Block `459` -/

/-- Unconditional `[LibsignalPlacement]` pinned contract for `encode<Ct1Sent> [local#3]` (Block `459`). -/
theorem ct1_sent_encode_1_pinned_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    Ct1SentEncode1PinnedPlacedOk A H := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := ct1SentEncode1_gen_placed_ok (by decide)
    (unchunked_ct1EncodedLen_cs_placed_ok A s0 hcl0)
    (unchunked_encodeVarint2_cs_placed_ok s0 hcl0 h_panic hshim halloc hrealloc)
    (unchunked_authEncode1_cs_placed_ok s0 hcl0 h_panic hshim halloc hrealloc hmc)
    (unchunked_doReserve2_cs_placed_ok s0 hcl0 h_panic hshim halloc hrealloc)
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

/-- Unconditional `[LibsignalPlacement]` unpinned contract for `encode<Ct1Sent> [local#3]` (Block `459`). -/
theorem ct1_sent_encode_1_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    Ct1SentEncode1PlacedOk A H :=
  ct1SentEncode_unpinned_of_pinned_placed
    (ct1_sent_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

/-- Unconditional `[LibsignalPlacement]` pinned `doReserveStackX` contract for `encode<Ct1Sent> [local#3]` (Block `459`). -/
theorem ct1_sent_encode_1_pinned_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    Ct1SentEncode1PinnedPlacedOkX A H := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := ct1SentEncode1_gen_placed_ok (by decide)
    (unchunked_ct1EncodedLen_cs_placed_ok A s0 hcl0)
    (unchunked_encodeVarint2_cs_placed_ok_x s0 hcl0 h_panic hshim halloc hrealloc)
    (unchunked_authEncode1_cs_placed_ok_x s0 hcl0 h_panic hshim halloc hrealloc hmc)
    (unchunked_doReserve2_cs_placed_ok_x s0 hcl0 h_panic hshim halloc hrealloc)
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

/-- Unconditional `[LibsignalPlacement]` unpinned `doReserveStackX` contract for `encode<Ct1Sent> [local#3]` (Block `459`). -/
theorem ct1_sent_encode_1_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    Ct1SentEncode1PlacedOkX A H :=
  ct1SentEncode_unpinned_of_pinned_placed
    (ct1_sent_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

theorem ct1_sent_encode_1_pinned_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    Ct1SentEncode1PinnedPlacedOkExt A ext :=
  ct1_sent_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc

theorem ct1_sent_encode_1_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    Ct1SentEncode1PlacedOkExt A ext :=
  ct1_sent_encode_1_placed_ok h_panic hshim halloc hrealloc hmc

theorem ct1_sent_encode_1_pinned_placed_ok_ext_x [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    Ct1SentEncode1PinnedPlacedOkExtX A ext :=
  ct1_sent_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc

theorem ct1_sent_encode_1_placed_ok_ext_x [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    Ct1SentEncode1PlacedOkExtX A ext :=
  ct1_sent_encode_1_placed_ok_x h_panic hshim halloc hrealloc hmc

abbrev ct1_sent_encode_1_pinned_placed_ok_uncond := @ct1_sent_encode_1_pinned_placed_ok
abbrev ct1_sent_encode_1_pinned_placed_ok_x_uncond := @ct1_sent_encode_1_pinned_placed_ok_x
abbrev ct1SentEncode_1_pinned_placed_ok := @ct1_sent_encode_1_pinned_placed_ok
abbrev ct1SentEncode_1_placed_ok := @ct1_sent_encode_1_placed_ok
abbrev ct1SentEncode_1_pinned_placed_ok_x := @ct1_sent_encode_1_pinned_placed_ok_x
abbrev ct1SentEncode_1_placed_ok_x := @ct1_sent_encode_1_placed_ok_x

/-! ## 2. `EncodeToVec` Callee Bridges (Block `459`) -/

section EncodeToVecBridge

/-- `EncodeToVec` (`etvCt1SentEncodeSpecOf doReserveStack`) contract on Block `459`. -/
theorem etv_ct1SentEncode_1_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_459 H) (blkPl_459).base
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeSpecOf doReserveStack A)) :=
  etv_ct1SentEncode_of_lscl
    (ct1_sent_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

/-- `EncodeToVec` (`etvCt1SentEncodeSpecOf doReserveStackX`) contract on Block `459`. -/
theorem etv_ct1SentEncode_1_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_459 H) (blkPl_459).base
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeSpecOf doReserveStackX A)) :=
  etv_ct1SentEncode_of_lscl
    (ct1_sent_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

abbrev etv_ct1SentEncode_placed_ok := @etv_ct1SentEncode_1_placed_ok
abbrev etv_ct1SentEncode_placed_ok_x := @etv_ct1SentEncode_1_placed_ok_x
abbrev etv_ct1SentEncode_1_exact_placed_ok := @etv_ct1SentEncode_1_placed_ok
abbrev etv_ct1SentEncode_1_exact_placed_ok_x := @etv_ct1SentEncode_1_placed_ok_x
abbrev ct1_sent_encode_1_exact_placed_ok := @etv_ct1SentEncode_1_placed_ok
abbrev ct1_sent_encode_1_exact_placed_ok_x := @etv_ct1SentEncode_1_placed_ok_x

end EncodeToVecBridge

end CryptoVerification.Cli.SpqrV1.Prost.MessageEncode
