/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesCodeSymA
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs

/-!
# Relocatable `[LibsignalPlacement]` Specifications for SPQR V1 Receiver & Encoder Leaves

Relocatable `[LibsignalPlacement]` specifications (`*PlacedSpec`) and `*PlacedOkX` contract
abbreviations for the receiver and encoder leaf transitions in `SpqrV1/States/Leaves`, re-exporting
address-independent specs directly from `Batch2Defs.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib
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
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Unchunked (unchunkedSendCt2PlacedRoAt unchunkedCt1SentEkReceivedSendCt2PlacedSpec)

/-- Relocatable specification of `<PolyDecoder as Decoder>::decoded_message` (Block `418`). -/
def polyDecoderDecodedMessagePlacedSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec PolyDecoderDecodedMessageGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.decA ∧
      PolyDecoderStrictSorted x.dec ∧
      spqrPolyApi.decoded_message x.dec = .ok x.outMsg⌝ ∗
      memRegion x.outA 24 ∗
      polyDecoderAt A x.decA x.dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp polyDecoderDecodedMessageStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      optVecU8At A x.outA x.outMsg ∗
      polyDecoderAt A x.decA x.dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp polyDecoderDecodedMessageStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable specification of `<EkReceivedCt1Sampled>::recv_ct1_ack` (Block `343`). -/
def ekReceivedCt1SampledRecvCt1AckPlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem) :
    Spec (EkReceivedCt1SampledRecvCt1AckGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      x.st.recv_ct1_ack K x.st.uc.epoch = .ok x.outSt⌝ ∗
      memRegion x.outA chunkedCt2SampledSize ∗
      chunkedEkReceivedCt1SampledAt A x.stA x.st ∗
      unchunkedSendCt2PlacedRoAt ∗
      A.pool ∗ stackAt s.sp ekReceivedCt1SampledRecvCt1AckStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedCt2SampledAt A x.outA x.outSt ∗
      memRegion x.stA chunkedEkReceivedCt1SampledSize ∗
      unchunkedSendCt2PlacedRoAt ∗
      A.pool ∗ stackAt s0.sp ekReceivedCt1SampledRecvCt1AckStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable specification of `<HeaderSent>::recv_ct1_chunk` (Block `337`). -/
def headerSentRecvCt1ChunkPlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) :
    Spec (HeaderSentRecvCt1ChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.st.receiving_ct1 ∧
      x.st.recv_ct1_chunk x.st.uc.epoch x.chunk = .ok x.outRes⌝ ∗
      memRegion x.outA chunkedHeaderSentSize ∗
      chunkedHeaderSentAt A x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp headerSentRecvCt1ChunkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      headerSentRecvChunkAt A x.outA x.outRes ∗
      memRegion x.stA chunkedHeaderSentSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp headerSentRecvCt1ChunkStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable specification of `<Ct1Acknowledged>::recv_ek_chunk` (Block `349`). -/
def ct1AcknowledgedRecvEkChunkPlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem) :
    Spec (Ct1AcknowledgedRecvEkChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.st.receiving_ek ∧
      x.st.recv_ek_chunk K x.st.uc.epoch x.chunk = StatesResult.ofError x.res⌝ ∗
      memRegion x.outA 528 ∗
      chunkedCt1AcknowledgedAt A x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      unchunkedSendCt2PlacedRoAt ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp ct1AcknowledgedRecvEkChunkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ct1AcknowledgedRecvEkChunkResAt A x.outA x.res ∗
      memRegion x.stA 528 ∗
      chunkAt x.chunkA x.chunk ∗
      unchunkedSendCt2PlacedRoAt ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Contract Abbreviations (`*PlacedOkX`) -/

def SendCt2EncoderPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_382 (Rust.withPanics ext)) (blkPl_382).base
    (withLsCodeLoaded lsmpl (sendCt2EncoderSpec A))

def UnchunkedCt1SentRecvEkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_338 (Rust.withPanics ext)) (blkPl_338).base
    (unchunkedCt1SentRecvEkSpec A F K)

def EkReceivedCt1SampledRecvCt1AckPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_343 (Rust.withPanics ext)) (blkPl_343).base
    (withLsCodeLoaded lsmpl (ekReceivedCt1SampledRecvCt1AckPlacedSpec A F K))

def Ct1ReceivedRecvCt2ChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_346 (Rust.withPanics ext)) (blkPl_346).base
    (withLsCodeLoaded lsmpl (ct1ReceivedRecvCt2ChunkSpec A F))

def HeaderSentRecvCt1ChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_337 (Rust.withPanics ext)) (blkPl_337).base
    (withLsCodeRoLoaded lsmpl (headerSentRecvCt1ChunkPlacedSpec A F))

def KeysSampledRecvCt1ChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_370 (Rust.withPanics ext)) (blkPl_370).base
    (withLsCodeLoaded lsmpl (keysSampledRecvCt1ChunkSpec A F))

def Ct1AcknowledgedRecvEkChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_349 (Rust.withPanics ext)) (blkPl_349).base
    (withLsCodeRoLoaded lsmpl (ct1AcknowledgedRecvEkChunkPlacedSpec A F K))

end CryptoVerification.SpqrV1.States.Leaves
