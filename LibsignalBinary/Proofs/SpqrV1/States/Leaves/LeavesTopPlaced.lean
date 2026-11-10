/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1Placed
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlaced
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt1ChunkPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Ct1ReceivedPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.RecvCt1AckPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProofPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlaced
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2ChunkPlaced -- shake: keep

/-!
# SPQR V1 Leaf Subroutines: Closed Relocatable Contracts

Aggregates and closes all 15 relocatable `Obj.MultiPlacedLib` leaf contracts (`335`, `336`, `337`,
`338`, `343`, `344`, `345`, `346`, `349`, `350`, `354`, `355`, `369`, `370`, `382`) under
`[LibsignalPlacement]`, discharging cross-block callees `347`, `418`, and `419`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk

private theorem hookSat_sessionShim_of_noAllocShim
    {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym noAllocShimSpec) :
    HookSat H sym sessionShimSpec :=
  HookSat.mono h fun x R _ hpre => ⟨x, R, hpre, fun _ hpost => hpost⟩

/-! ## 1. `libsignalSessionLib.blockProgram` Seam Bridge for Send Chunks (`335, 336, 344, 345, 354`) -/

theorem header_sent_send_ek_chunk_placed_blockProgram_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 336 (Rust.withPanics ext))
      (lsmpl.base 336) (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpec A F)) :=
  header_sent_send_ek_chunk_placed_ok_x hA

theorem ct1_received_send_ek_chunk_placed_blockProgram_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 345 (Rust.withPanics ext))
      (lsmpl.base 345) (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpec A F)) :=
  ct1_received_send_ek_chunk_placed_ok_x hA

theorem ct1_sampled_send_ct1_chunk_placed_blockProgram_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 335 (Rust.withPanics ext))
      (lsmpl.base 335) (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpec A F)) :=
  ct1_sampled_send_ct1_chunk_placed_ok_x hA

theorem ek_received_ct1_sampled_send_ct1_chunk_placed_blockProgram_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 344 (Rust.withPanics ext))
      (lsmpl.base 344) (withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpec A F)) :=
  ek_received_ct1_sampled_send_ct1_chunk_placed_ok_x hA

theorem ct2_sampled_send_ct2_chunk_placed_blockProgram_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 354 (Rust.withPanics ext))
      (lsmpl.base 354) (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpec A F)) :=
  ct2_sampled_send_ct2_chunk_placed_ok_x hA

/-! ## 2. Closed Contract for Block `370` (`<KeysSampled>::recv_ct1_chunk`) -/

/-- Closed relocatable contract for `<KeysSampled>::recv_ct1_chunk` (Block `370`),
discharging `PolyDecoder::add_chunk` (Block `419`). -/
theorem keys_sampled_recv_ct1_chunk_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack)) :
    KeysSampledRecvCt1ChunkPlacedOkX A F ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext h_panic hshim halloc hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 370) (j := 419)
      (add_chunk_cl_placed_ok h_panic
        (hookSat_sessionShim_of_noAllocShim hshim) halloc hrealloc hmemmove))

/-! ## 3. Closed Contract for Block `337` (`<HeaderSent>::recv_ct1_chunk`) -/

/-- Closed relocatable contract for `<HeaderSent>::recv_ct1_chunk` (Block `337`),
discharging `PolyDecoder::add_chunk` (Block `419`) and `PolyDecoder::decoded_message` (Block `418`). -/
theorem header_sent_recv_ct1_chunk_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec) :
    HeaderSentRecvCt1ChunkPlacedOkX A F ext :=
  header_sent_recv_ct1_chunk_placed_cl_ext hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 337) (j := 419)
      (add_chunk_cl_placed_ok h_panic
        (hookSat_sessionShim_of_noAllocShim hshim) halloc hrealloc hmemmove))
    (keys_ls_subroutine_ok_of_block_cro (i := 337) (j := 418)
      (polyDecoderDecodedMessage_cro_placed_ok_x h_panic
        (hookSat_sessionShim_of_noAllocShim hshim)
        halloc hrealloc hdealloc hmemcpy hmemset))

/-! ## 4. Closed Contract for Block `346` (`<Ct1Received>::recv_ct2_chunk`) -/

/-- Closed relocatable contract for `<Ct1Received>::recv_ct2_chunk` (Block `346`),
discharging `PolyDecoder::add_chunk` (Block `419`). -/
theorem ct1_received_recv_ct2_chunk_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack)) :
    Ct1ReceivedRecvCt2ChunkPlacedOkX A F ext :=
  ct1_received_recv_ct2_chunk_placed_cl_ext hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 346) (j := 419)
      (add_chunk_cl_placed_ok h_panic
        (hookSat_sessionShim_of_noAllocShim hshim) halloc hrealloc hmemmove))

/-! ## 5. Closed Contract for Block `343` (`<EkReceivedCt1Sampled>::recv_ct1_ack`) -/

/-- Closed relocatable contract for `<EkReceivedCt1Sampled>::recv_ct1_ack` (Block `343`),
discharging `<unchunked::Ct1SentEkReceived>::send_ct2` (Block `347`) and `send_ct2_encoder` (Block `382`). -/
theorem ek_received_ct1_sampled_recv_ct1_ack_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) "memcpy" framelessMemcpySpec)
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hmemcpy_ro : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym (mlkemEncaps2Spec K))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacSpec F A)) :
    EkReceivedCt1SampledRecvCt1AckPlacedOkX A F K ext :=
  ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext hdealloc
    (ls_subroutine_ok_of_block (i := 343) (j := 347)
      (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
        h_panic hshim halloc hrealloc hdealloc hmemcpy_fl hmemcpy_ro hencaps2 hhmac))
    (ls_subroutine_ok_of_block (i := 343) (j := 382)
      (send_ct2_encoder_placed_ok_x h_panic hshim halloc hrealloc hdealloc hmemcpy))

/-! ## 6. Closed Contract for Block `349` (`<Ct1Acknowledged>::recv_ek_chunk`) -/

/-- Closed relocatable contract for `<Ct1Acknowledged>::recv_ek_chunk` (Block `349`),
discharging `PolyDecoder::add_chunk` (`419`), `PolyDecoder::decoded_message` (`418`),
and `<unchunked::Ct1SentEkReceived>::send_ct2` (`347`). -/
theorem ct1_acknowledged_recv_ek_chunk_placed_closed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) "memcpy" framelessMemcpySpec)
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hmemcpy_ro : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionROSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec)
    (hval_pk : HookSat (Rust.withPanics ext) "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes" (mlkemValidatePkSpec K))
    (hencaps2 : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym (mlkemEncaps2Spec K))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacSpec F A)) :
    Ct1AcknowledgedRecvEkChunkPlacedOkX A F K ext :=
  ct1_acknowledged_recv_ek_chunk_placed_ok_x h_panic hshim halloc hrealloc hdealloc hmemcpy hval_pk
    (ls_subroutine_ok_of_block (i := 349) (j := 419)
      (add_chunk_cl_placed_ok h_panic
        (hookSat_sessionShim_of_noAllocShim hshim) halloc hrealloc hmemmove))
    (keys_ls_subroutine_ok_of_block_cro (i := 349) (j := 418)
      (polyDecoderDecodedMessage_cro_placed_ok_x h_panic
        (hookSat_sessionShim_of_noAllocShim hshim)
        halloc hrealloc hdealloc hmemcpy hmemset))
    (ls_subroutine_ok_of_block (i := 349) (j := 347)
      (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
        h_panic hshim halloc hrealloc hdealloc hmemcpy_fl hmemcpy_ro hencaps2 hhmac))

/-! ## 7. Closed Contract for Block `369` (`<NoHeaderReceived>::recv_hdr_chunk`) -/

/-- Closed relocatable contract for `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`),
discharging `PolyDecoder::add_chunk` (`419`) and `PolyDecoder::decoded_message` (`418`). -/
theorem noHeaderReceived_recv_hdr_chunk_placed_closed_okX [LibsignalPlacement]
    {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) RecvHdrChunk.spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacSpec F A))
    (h_handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed : (Rust.withPanics ext) assertFailedRecvHdrSym = some Rust.panicked)
    (h_slice_index_fail : (Rust.withPanics ext) sliceIndexFailRecvHdrSym = some Rust.panicked)
    (h_panic_bounds_check : (Rust.withPanics ext) panicBoundsCheckRecvHdrSym = some Rust.panicked) :
    NoHeaderReceivedRecvHdrChunkPlacedOkX F A ext :=
  noHeaderReceived_recv_hdr_chunk_placed_okX
    (add_chunk_cl_placed_ok_x h_handle_error
      (hookSat_sessionShim_of_noAllocShim hshim) halloc hrealloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks h_handle_error
      (hookSat_sessionShim_of_noAllocShim hshim)
      halloc hrealloc hdealloc hmemcpy hmemset)
    hshim halloc hdealloc hmemcpy_fl hRO hhmac
    h_handle_error h_assert_failed h_slice_index_fail h_panic_bounds_check

/-! ## 8. Closed Contract for Block `350` (`<EkSentCt1Received>::recv_ct2_chunk`) -/

/-- Closed relocatable contract for `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`),
discharging `PolyDecoder::add_chunk` (`419`) and `PolyDecoder::decoded_message` (`418`). -/
theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc A ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (mlkemDecapsSpec K))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacSpec F A)) :
    RecvCt2ChunkPlacedOkX K F A ext :=
  recv_ct2_chunk_placed_ok_x hA
    (add_chunk_cl_placed_ok_x hA.handleError
      (hookSat_sessionShim_of_noAllocShim hA.shim) hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShim_of_noAllocShim hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset)
    hdecaps hhmac

/-- Closed relocatable contract for `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`)
taking individual external hook and panic hypotheses directly. -/
theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x_of_hooks [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hallocZeroed : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym' (rustDeallocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (mlkemDecapsSpec K))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacSpec F A))
    (h_handle_error : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed_u64 : Rust.withPanics ext spqrAssertFailedU64Sym = some Rust.panicked)
    (h_slice_index_fail : Rust.withPanics ext spqrSliceIndexFailSym = some Rust.panicked)
    (h_unwrap_failed : Rust.withPanics ext spqrUnwrapFailedSym = some Rust.panicked)
    (h_panic_bounds_check : Rust.withPanics ext spqrPanicBoundsCheckSym = some Rust.panicked)
    (h_panic_add_overflow : Rust.withPanics ext spqrPanicConstAddOverflowSym = some Rust.panicked) :
    RecvCt2ChunkPlacedOkX K F A ext :=
  recv_ct2_chunk_placed_ok_x_of_hooks
    (add_chunk_cl_placed_ok_x h_handle_error
      (hookSat_sessionShim_of_noAllocShim hshim) halloc hrealloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks h_handle_error
      (hookSat_sessionShim_of_noAllocShim hshim)
      halloc hrealloc hdealloc hmemcpy hmemset)
    hshim halloc hallocZeroed hdealloc hrealloc hmemcpy_fl hRO
    hdecaps hhmac
    h_handle_error h_assert_failed_u64 h_slice_index_fail
    h_unwrap_failed h_panic_bounds_check h_panic_add_overflow

end CryptoVerification.SpqrV1.States.Leaves
