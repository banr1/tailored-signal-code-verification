/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DecodesPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymBasePlaced
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`): Relocatable Specifications & Contracts

Relocatable `[LibsignalPlacement]` callee contract bundle `StatesRecvPlacedContracts` and
top-level / per-variant specifications (`statesRecvPlacedSpec`, `StatesRecvPlacedOkX`) for Block `332`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev spqrDeallocSym : String := spqrRustDeallocSym

abbrev _root_.CryptoVerification.RustHeap.RustAlloc.noAllocShimSpec (_A : RustAlloc) : Spec Unit :=
  CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec

abbrev _root_.CryptoVerification.RustHeap.RustAlloc.allocSpec (A : RustAlloc) : Spec (Nat × Nat) :=
  rustAllocSpec A

abbrev _root_.CryptoVerification.RustHeap.RustAlloc.deallocSpec (A : RustAlloc) :
    Spec (BitVec 64 × Nat × Nat) :=
  rustDeallocSpec A

/-! ## Relocatable Callee Contract Bundle (`StatesRecvPlacedContracts`) -/

/-- Bundle of relocatable callee `subroutine_ok` and `HookSat` contracts used by
    `<spqr::v1::chunked::states::States>::recv` (Block `332`, `lsProg_332`). -/
structure StatesRecvPlacedContracts [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  keysSampledRecvCt1Chunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 370)
      (withLsCodeLoaded lsmpl (keysSampledRecvCt1ChunkSpec A F))
  headerSentRecvCt1Chunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 337)
      (withLsCodeRoLoaded lsmpl (headerSentRecvCt1ChunkPlacedSpec A F))
  ct1ReceivedRecvCt2Chunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 346)
      (withLsCodeLoaded lsmpl (ct1ReceivedRecvCt2ChunkSpec A F))
  ekSentCt1ReceivedRecvCt2Chunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 350)
      (withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpec K F A))
  noHeaderReceivedRecvHdrChunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 369)
      (withLsCodeRoLoaded lsmpl (noHeaderReceivedRecvHdrChunkPlacedSpec F A))
  polyAddChunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 419)
      (withLsCodeLoaded lsmpl (addChunkSpecX A))
  polyDecodedMessage_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 418)
      (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A))
  unchunkedCt1SentRecvEk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 338)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec A F K))
  unchunkedCt1SentEkReceivedSendCt2_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K))
  sendCt2Encoder_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec A))
  ekReceivedCt1SampledRecvCt1Ack_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 343)
      (withLsCodeLoaded lsmpl (ekReceivedCt1SampledRecvCt1AckPlacedSpec A F K))
  ct1AcknowledgedRecvEkChunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 349)
      (withLsCodeRoLoaded lsmpl (ct1AcknowledgedRecvEkChunkPlacedSpec A F K))
  ct2SampledRecvNextEpoch_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 355)
      (withLsCodeLoaded lsmpl (ct2SampledRecvNextEpochSpec A F))
  hdrop_pt16 :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A))
  hdrop_ct2_sampled :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 274)
      (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec A F))
  hdrop_header_sent :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 276)
      (withLsCodeLoaded lsmpl (dropChunkedHeaderSentSpec A F))
  hdrop_ek_sent_ct1_received :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 278)
      (withLsCodeLoaded lsmpl (dropChunkedEkSentCt1ReceivedSpec A F))
  hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym A.noAllocShimSpec
  halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym A.allocSpec
  hdealloc_sat : HookSat (Rust.withPanics ext) spqrDeallocSym A.deallocSpec
  hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec
  hmemcpy_ro_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec

namespace StatesRecvPlacedContracts

variable [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {K : MlKem}
  {ext : String → Option (State → State)}

theorem hsend_ct2 (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)) :=
  hC.unchunkedCt1SentEkReceivedSendCt2_ok

theorem hrecv_ek_unchunked (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 338)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec A F K)) :=
  hC.unchunkedCt1SentRecvEk_ok

theorem hkeys_sampled_recv_ct1 (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 370)
      (withLsCodeLoaded lsmpl (keysSampledRecvCt1ChunkSpec A F)) :=
  hC.keysSampledRecvCt1Chunk_ok

theorem hheader_sent_recv_ct1 (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 337)
      (withLsCodeRoLoaded lsmpl (headerSentRecvCt1ChunkPlacedSpec A F)) :=
  hC.headerSentRecvCt1Chunk_ok

theorem hrecv_ct1_chunk (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 337)
      (withLsCodeRoLoaded lsmpl (headerSentRecvCt1ChunkPlacedSpec A F)) :=
  hC.headerSentRecvCt1Chunk_ok

theorem hct1_recv_ct2 (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 346)
      (withLsCodeLoaded lsmpl (ct1ReceivedRecvCt2ChunkSpec A F)) :=
  hC.ct1ReceivedRecvCt2Chunk_ok

theorem hrecv_ct2_chunk (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 350)
      (withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpec K F A)) :=
  hC.ekSentCt1ReceivedRecvCt2Chunk_ok

theorem hrecv_hdr_chunk (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 369)
      (withLsCodeRoLoaded lsmpl (noHeaderReceivedRecvHdrChunkPlacedSpec F A)) :=
  hC.noHeaderReceivedRecvHdrChunk_ok

theorem hpoly_add_chunk (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 419)
      (withLsCodeLoaded lsmpl (addChunkSpecX A)) :=
  hC.polyAddChunk_ok

theorem hpoly_decoded_msg (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 418)
      (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)) :=
  hC.polyDecodedMessage_ok

theorem hsend_ct2_encoder (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec A)) :=
  hC.sendCt2Encoder_ok

theorem hrecv_ct1_ack (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 343)
      (withLsCodeLoaded lsmpl (ekReceivedCt1SampledRecvCt1AckPlacedSpec A F K)) :=
  hC.ekReceivedCt1SampledRecvCt1Ack_ok

theorem hct1_ack_recv_ek (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 349)
      (withLsCodeRoLoaded lsmpl (ct1AcknowledgedRecvEkChunkPlacedSpec A F K)) :=
  hC.ct1AcknowledgedRecvEkChunk_ok

theorem hrecv_next_epoch (hC : StatesRecvPlacedContracts A F K ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 355)
      (withLsCodeLoaded lsmpl (ct2SampledRecvNextEpochSpec A F)) :=
  hC.ct2SampledRecvNextEpoch_ok

theorem of_callees
    (keysSampledRecvCt1Chunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 370)
        (withLsCodeLoaded lsmpl (keysSampledRecvCt1ChunkSpec A F)))
    (headerSentRecvCt1Chunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 337)
        (withLsCodeRoLoaded lsmpl (headerSentRecvCt1ChunkPlacedSpec A F)))
    (ct1ReceivedRecvCt2Chunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 346)
        (withLsCodeLoaded lsmpl (ct1ReceivedRecvCt2ChunkSpec A F)))
    (ekSentCt1ReceivedRecvCt2Chunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 350)
        (withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpec K F A)))
    (noHeaderReceivedRecvHdrChunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 369)
        (withLsCodeRoLoaded lsmpl (noHeaderReceivedRecvHdrChunkPlacedSpec F A)))
    (polyAddChunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 419)
        (withLsCodeLoaded lsmpl (addChunkSpecX A)))
    (polyDecodedMessage_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 418)
        (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)))
    (unchunkedCt1SentRecvEk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 338)
        (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec A F K)))
    (unchunkedCt1SentEkReceivedSendCt2_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 347)
        (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)))
    (sendCt2Encoder_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 382)
        (withLsCodeLoaded lsmpl (sendCt2EncoderSpec A)))
    (ekReceivedCt1SampledRecvCt1Ack_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 343)
        (withLsCodeLoaded lsmpl (ekReceivedCt1SampledRecvCt1AckPlacedSpec A F K)))
    (ct1AcknowledgedRecvEkChunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 349)
        (withLsCodeRoLoaded lsmpl (ct1AcknowledgedRecvEkChunkPlacedSpec A F K)))
    (ct2SampledRecvNextEpoch_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 355)
        (withLsCodeLoaded lsmpl (ct2SampledRecvNextEpochSpec A F)))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym A.noAllocShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym A.allocSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrDeallocSym A.deallocSpec)
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hmemcpy_ro_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec) :
    StatesRecvPlacedContracts A F K ext where
  keysSampledRecvCt1Chunk_ok := keysSampledRecvCt1Chunk_ok
  headerSentRecvCt1Chunk_ok := headerSentRecvCt1Chunk_ok
  ct1ReceivedRecvCt2Chunk_ok := ct1ReceivedRecvCt2Chunk_ok
  ekSentCt1ReceivedRecvCt2Chunk_ok := ekSentCt1ReceivedRecvCt2Chunk_ok
  noHeaderReceivedRecvHdrChunk_ok := noHeaderReceivedRecvHdrChunk_ok
  polyAddChunk_ok := polyAddChunk_ok
  polyDecodedMessage_ok := polyDecodedMessage_ok
  unchunkedCt1SentRecvEk_ok := unchunkedCt1SentRecvEk_ok
  unchunkedCt1SentEkReceivedSendCt2_ok := unchunkedCt1SentEkReceivedSendCt2_ok
  sendCt2Encoder_ok := sendCt2Encoder_ok
  ekReceivedCt1SampledRecvCt1Ack_ok := ekReceivedCt1SampledRecvCt1Ack_ok
  ct1AcknowledgedRecvEkChunk_ok := ct1AcknowledgedRecvEkChunk_ok
  ct2SampledRecvNextEpoch_ok := ct2SampledRecvNextEpoch_ok
  hdrop_pt16 := ls_subroutine_ok_of_block (drop_glue_sorted_set_pt16_cl_placed_ok (hdealloc := hdealloc_sat))
  hdrop_ct2_sampled := ls_subroutine_ok_of_block (drop_chunked_ct2_sampled_cl_placed_ok (hdealloc := hdealloc_sat))
  hdrop_header_sent := ls_subroutine_ok_of_block (drop_chunked_header_sent_cl_placed_ok (hdealloc := hdealloc_sat))
  hdrop_ek_sent_ct1_received := ls_subroutine_ok_of_block (drop_chunked_ek_sent_ct1_received_cl_placed_ok (hdealloc := hdealloc_sat))
  hshim_sat := hshim_sat
  halloc_sat := halloc_sat
  hdealloc_sat := hdealloc_sat
  hmemcpy_sat := hmemcpy_sat
  hmemcpy_ro_sat := hmemcpy_ro_sat

end StatesRecvPlacedContracts

/-! ## Top-Level and Per-Variant Relocatable Specifications of `<States>::recv` (Block `332`) -/

/-- Relocatable specification of `<spqr::v1::chunked::states::States>::recv` (Block `332`, 4,884 insns). -/
def statesRecvPlacedSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) (K : MlKem) :
    Spec (StatesRecvGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.msgA ∧
      statesRecvPreInv x.self⌝ ∗
      memRegion x.outA v1RecvSize ∗
      chunkedStatesAt A x.selfA x.self ∗
      messageAt spqrPolyApi x.msgA x.msg ∗
      statesRecvRoPlacedAt ∗
      A.pool ∗ stackAt s.sp statesRecvStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultV1RecvAt A (F := F) x.outA (x.self.recv K x.msg) ∗
      memRegion x.selfA chunkedStatesSize ∗
      messageAt spqrPolyApi x.msgA x.msg ∗
      statesRecvRoPlacedAt ∗
      A.pool ∗ stackAt s0.sp statesRecvStackX
  onPanic := fun x s0 sf => statesRecvOnPanic K x s0 sf

/-- Per-variant relocatable specification of `<States>::recv` (Block `332`) for a fixed `(self, msg)`. -/
def statesRecvVariantPlacedSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun ⟨outA, selfA, msgA⟩ s =>
    ⌜s.readReg64 .x0 = outA ∧
      s.readReg64 .x1 = selfA ∧
      s.readReg64 .x2 = msgA ∧
      statesRecvPreInv self⌝ ∗
      memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA self ∗
      messageAt spqrPolyApi msgA msg ∗
      statesRecvRoPlacedAt ∗
      A.pool ∗ stackAt s.sp statesRecvStackX
  post := fun ⟨outA, selfA, msgA⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultV1RecvAt A (F := F) outA (self.recv K msg) ∗
      memRegion selfA chunkedStatesSize ∗
      messageAt spqrPolyApi msgA msg ∗
      statesRecvRoPlacedAt ∗
      A.pool ∗ stackAt s0.sp statesRecvStackX
  onPanic := fun ⟨outA, selfA, msgA⟩ s0 sf =>
    statesRecvOnPanic K ⟨outA, selfA, msgA, self, msg⟩ s0 sf

/-- `<States>::recv` (Block `332`) meets `withLsCodeRoLoaded lsmpl (statesRecvPlacedSpec A F K)`
    on `lsProg_332 (Rust.withPanics ext)`. -/
def StatesRecvPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 332)
    (withLsCodeRoLoaded lsmpl (statesRecvPlacedSpec A F K))

/-- `<States>::recv` (Block `332`) meets `withLsCodeRoLoaded lsmpl (statesRecvPlacedSpec A F K)`
    on `libsignalSessionLib.blockProgram lsmpl 332 (Rust.withPanics ext)`. -/
def StatesRecvPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 332 (Rust.withPanics ext)) (lsmpl.base 332)
    (withLsCodeRoLoaded lsmpl (statesRecvPlacedSpec A F K))

theorem sepWPp_of_statesRecv_exit_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (P R : SepProp)
    (h : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (self.recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗
          A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantPlacedSpec A F K self msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantPlacedSpec A F K self msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨hPf, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  dsimp only [statesRecvVariantPlacedSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨htrf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by ac_rfl))) hmem_f⟩

theorem sepWPp_of_statesRecv_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (P R : SepProp)
    (h : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (self.recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗
          A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (withLsCodeLoaded lsmpl (statesRecvVariantPlacedSpec A F K self msg)).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeLoaded lsmpl (statesRecvVariantPlacedSpec A F K self msg)).onPanic (outA, selfA, msgA) s0 sf ∗ R)) :=
  sepWPp_of_statesRecv_exit_placed s0 s outA selfA msgA self msg P R h

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  spqrDeallocSym
  StatesRecvPlacedContracts
  statesRecvPlacedSpec
  statesRecvVariantPlacedSpec
  StatesRecvPlacedOkExt
  StatesRecvPlacedOkX
  sepWPp_of_statesRecv_exit_placed
  sepWPp_of_statesRecv_exit_cl_placed
)

end CryptoVerification.SpqrV1.States.Recv
