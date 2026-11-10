/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`): Budget-Threaded Relocatable Specifications & Contracts

Relocatable `[LibsignalPlacement]` `RustCliAllocBudget` callee contract bundles
(`StatesRecvPlacedContractsOfEnv`, `StatesRecvPlacedContracts`) and specifications for Block `332`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget

open Arm64 ProofLib
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement extract_withLsCodeLoaded libsignalSessionLib lsProg_332 lsmpl
   withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (extract_withLsCodeRoLoaded noAllocShimSpec sessionMemcpySpec withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Message MlKem States spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1 (ls_subroutine_ok_to_blockProgram)
open CryptoVerification.SpqrV1.Alloc
  (sessionMemcpyRegionROSpec spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Drop (chunkedStatesAt chunkedStatesSize)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1AcknowledgedRecvEkChunkGhost Ct1ReceivedRecvCt2ChunkGhost Ct2SampledRecvNextEpochGhost
   EkReceivedCt1SampledRecvCt1AckGhost HeaderSentRecvCt1ChunkGhost KeysSampledRecvCt1ChunkGhost
   PolyDecoderDecodedMessageGhost SendCt2EncoderGhost UnchunkedCt1SentRecvEkGhost
   UnchunkedSendCt2Ghost)
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk (NoHeaderReceivedRecvHdrChunkGhost)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (RecvCt2ChunkGhost)
open CryptoVerification.SpqrV1.States.Recv
  (StatesRecvGhost resultV1RecvAt spqrDeallocSym spqrRustDeallocSym statesRecvJumpTablePlacedAt
   statesRecvPreInv statesRecvRoPlacedAt statesRecvStackX v1RecvSize)
open CryptoVerification.SpqrV1.Top.MessageSerialize (messageAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustCliAllocBudgetSpec
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (hookSat_of_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChunkedBudget
  (dropChunkedCt1ReceivedSpec dropChunkedCt2SampledSpec dropChunkedEkReceivedCt1SampledSpec
   dropChunkedEkSentCt1ReceivedSpec dropChunkedHeaderSentSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget (dropGluePolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (addChunkSpecX)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (Ct1AcknowledgedRecvEkChunkPostEnv Ct1AcknowledgedRecvEkChunkPreEnv
   Ct1ReceivedRecvCt2ChunkPostEnv Ct1ReceivedRecvCt2ChunkPreEnv
   EkReceivedCt1SampledRecvCt1AckPostEnv EkReceivedCt1SampledRecvCt1AckPreEnv
   HeaderSentRecvCt1ChunkPostEnv HeaderSentRecvCt1ChunkPreEnv
   KeysSampledRecvCt1ChunkPostEnv KeysSampledRecvCt1ChunkPreEnv
   PolyDecoderDecodedMessagePostEnv PolyDecoderDecodedMessagePreEnv
   SendCt2EncoderPostEnv SendCt2EncoderPreEnv
   UnchunkedCt1SentRecvEkPostEnv UnchunkedCt1SentRecvEkPreEnv
   ct1AcknowledgedRecvEkChunkPlacedSpec ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv
   ct1ReceivedRecvCt2ChunkSpec ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv
   ekReceivedCt1SampledRecvCt1AckPlacedSpec ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv
   headerSentRecvCt1ChunkPlacedSpec headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv
   keysSampledRecvCt1ChunkSpec keysSampledRecvCt1ChunkSpecOfPrePostEnv
   polyDecoderDecodedMessagePlacedSpec polyDecoderDecodedMessagePlacedSpecOfPrePostEnv
   sendCt2EncoderSpec sendCt2EncoderSpecOfPrePostEnv
   unchunkedCt1SentRecvEkSpec unchunkedCt1SentRecvEkSpecOfPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (Ct2SampledRecvNextEpochEnv ct2SampledRecvNextEpochSpec ct2SampledRecvNextEpochSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
  (NoHeaderReceivedRecvHdrChunkEnv noHeaderReceivedRecvHdrChunkPlacedSpec
   noHeaderReceivedRecvHdrChunkPlacedSpecOfPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
  (drop_chunked_ct1_received_cl_on drop_chunked_ct2_sampled_cl_on
   drop_chunked_ek_received_ct1_sampled_cl_on drop_chunked_ek_sent_ct1_received_cl_on
   drop_chunked_header_sent_cl_on drop_glue_poly16_cl_on drop_glue_poly_decoder_cl_on
   drop_glue_poly_encoder_local2_cl_on drop_glue_proto_poly_encoder_cl_on
   drop_glue_sorted_set_pt16_cl_on)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget
  (RecvCt2ChunkEnv recvCt2ChunkPlacedSpec recvCt2ChunkPlacedSpecExt
   recvCt2ChunkPlacedSpecExtOfPrePostEnv recvCt2ChunkPlacedSpecOfPrePostEnv
   withLsCodeRoLoaded_recvCt2ChunkPlacedSpecExtOfPrePostEnv_of_X)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
  (UnchunkedSendCt2PostEnv UnchunkedSendCt2PreEnv
   unchunkedCt1SentEkReceivedSendCt2PlacedSpec
   unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332

/-! ## Re-Exports of `.rodata`, Symbols, and Shared Top-Level Seam Definitions -/

alias StatesRecvEnv := LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.StatesRecvEnv
alias statesRecvBudgetOnPanic :=
  LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.statesRecvBudgetOnPanic
alias statesRecvPlacedSpecOfEnv :=
  LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.statesRecvPlacedSpecOfEnv
alias statesRecvPlacedSpec :=
  LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.statesRecvPlacedSpec
alias StatesRecvPlacedOkXOfEnv :=
  LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.StatesRecvPlacedOkXOfEnv
alias StatesRecvPlacedOkX :=
  LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.StatesRecvPlacedOkX

/-! ## Budget-Threaded Relocatable Callee Contract Bundle (`StatesRecvPlacedContracts`) -/

/-- Callee `PreEnv` / `PostEnv` bundle for `<spqr::v1::chunked::states::States>::recv`
    (Block `332`). -/
structure StatesRecvCalleeEnvs (F : ShaCompress) where
  keysSampledRecvCt1Pre : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop
  keysSampledRecvCt1Post : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop
  headerSentRecvCt1Pre : HeaderSentRecvCt1ChunkGhost F → List AllocEvent → Prop
  headerSentRecvCt1Post : HeaderSentRecvCt1ChunkGhost F → List AllocEvent → Prop
  ct1ReceivedRecvCt2Pre : Ct1ReceivedRecvCt2ChunkGhost F → List AllocEvent → Prop
  ct1ReceivedRecvCt2Post : Ct1ReceivedRecvCt2ChunkGhost F → List AllocEvent → Prop
  ekSentCt1ReceivedRecvCt2Pre : RecvCt2ChunkGhost F → List AllocEvent → Prop
  ekSentCt1ReceivedRecvCt2Post : RecvCt2ChunkGhost F → List AllocEvent → Prop
  noHeaderReceivedRecvHdrPre : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop
  noHeaderReceivedRecvHdrPost : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop
  polyDecodedMessagePre : PolyDecoderDecodedMessageGhost → List AllocEvent → Prop
  polyDecodedMessagePost : PolyDecoderDecodedMessageGhost → List AllocEvent → Prop
  unchunkedRecvEkPre : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop
  unchunkedRecvEkPost : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop
  unchunkedSendCt2Pre : UnchunkedSendCt2Ghost F → List AllocEvent → Prop
  unchunkedSendCt2Post : UnchunkedSendCt2Ghost F → List AllocEvent → Prop
  sendCt2EncoderPre : SendCt2EncoderGhost → List AllocEvent → Prop
  sendCt2EncoderPost : SendCt2EncoderGhost → List AllocEvent → Prop
  ekReceivedCt1SampledRecvCt1AckPre :
    EkReceivedCt1SampledRecvCt1AckGhost F → List AllocEvent → Prop
  ekReceivedCt1SampledRecvCt1AckPost :
    EkReceivedCt1SampledRecvCt1AckGhost F → List AllocEvent → Prop
  ct1AcknowledgedRecvEkPre : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop
  ct1AcknowledgedRecvEkPost : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop

/-- Canonical exact binary callee envelopes for `<States>::recv` (Block `332`). -/
def statesRecvCalleeEnvs (F : ShaCompress) (K : MlKem) : StatesRecvCalleeEnvs F where
  keysSampledRecvCt1Pre := KeysSampledRecvCt1ChunkPreEnv
  keysSampledRecvCt1Post := KeysSampledRecvCt1ChunkPostEnv
  headerSentRecvCt1Pre := HeaderSentRecvCt1ChunkPreEnv
  headerSentRecvCt1Post := HeaderSentRecvCt1ChunkPostEnv
  ct1ReceivedRecvCt2Pre := Ct1ReceivedRecvCt2ChunkPreEnv
  ct1ReceivedRecvCt2Post := Ct1ReceivedRecvCt2ChunkPostEnv
  ekSentCt1ReceivedRecvCt2Pre := RecvCt2ChunkEnv
  ekSentCt1ReceivedRecvCt2Post := RecvCt2ChunkEnv
  noHeaderReceivedRecvHdrPre := NoHeaderReceivedRecvHdrChunkEnv
  noHeaderReceivedRecvHdrPost := NoHeaderReceivedRecvHdrChunkEnv
  polyDecodedMessagePre := PolyDecoderDecodedMessagePreEnv
  polyDecodedMessagePost := PolyDecoderDecodedMessagePostEnv
  unchunkedRecvEkPre := UnchunkedCt1SentRecvEkPreEnv
  unchunkedRecvEkPost := UnchunkedCt1SentRecvEkPostEnv
  unchunkedSendCt2Pre := UnchunkedSendCt2PreEnv
  unchunkedSendCt2Post := UnchunkedSendCt2PostEnv
  sendCt2EncoderPre := SendCt2EncoderPreEnv
  sendCt2EncoderPost := SendCt2EncoderPostEnv
  ekReceivedCt1SampledRecvCt1AckPre := EkReceivedCt1SampledRecvCt1AckPreEnv K
  ekReceivedCt1SampledRecvCt1AckPost := EkReceivedCt1SampledRecvCt1AckPostEnv K
  ct1AcknowledgedRecvEkPre := Ct1AcknowledgedRecvEkChunkPreEnv K
  ct1AcknowledgedRecvEkPost := Ct1AcknowledgedRecvEkChunkPostEnv K

/-- Envelope-parametric bundle of relocatable callee `subroutine_ok` and `HookSat` contracts used
    by `<spqr::v1::chunked::states::States>::recv` (Block `332`, `lsProg_332`). -/
structure StatesRecvPlacedContractsOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (envs : StatesRecvCalleeEnvs F)
    (ext : String → Option (State → State)) : Prop where
  keysSampledRecvCt1Chunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 370)
      (withLsCodeLoaded lsmpl
        (keysSampledRecvCt1ChunkSpecOfPrePostEnv M A lim F
          envs.keysSampledRecvCt1Pre envs.keysSampledRecvCt1Post))
  headerSentRecvCt1Chunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 337)
      (withLsCodeRoLoaded lsmpl
        (headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv M A lim F
          envs.headerSentRecvCt1Pre envs.headerSentRecvCt1Post))
  ct1ReceivedRecvCt2Chunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 346)
      (withLsCodeLoaded lsmpl
        (ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv M A lim F
          envs.ct1ReceivedRecvCt2Pre envs.ct1ReceivedRecvCt2Post))
  ekSentCt1ReceivedRecvCt2Chunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 350)
      (withLsCodeRoLoaded lsmpl
        (recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim
          envs.ekSentCt1ReceivedRecvCt2Pre envs.ekSentCt1ReceivedRecvCt2Post))
  noHeaderReceivedRecvHdrChunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 369)
      (withLsCodeRoLoaded lsmpl
        (noHeaderReceivedRecvHdrChunkPlacedSpecOfPrePostEnv M A lim F
          envs.noHeaderReceivedRecvHdrPre envs.noHeaderReceivedRecvHdrPost))
  polyAddChunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 419)
      (withLsCodeLoaded lsmpl (addChunkSpecX M A lim))
  polyDecodedMessage_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 418)
      (withLsCodeRoLoaded lsmpl
        (polyDecoderDecodedMessagePlacedSpecOfPrePostEnv M A lim
          envs.polyDecodedMessagePre envs.polyDecodedMessagePost))
  unchunkedCt1SentRecvEk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 338)
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentRecvEkSpecOfPrePostEnv M A lim F K
          envs.unchunkedRecvEkPre envs.unchunkedRecvEkPost))
  unchunkedCt1SentEkReceivedSendCt2_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 347)
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K
          envs.unchunkedSendCt2Pre envs.unchunkedSendCt2Post))
  sendCt2Encoder_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 382)
      (withLsCodeLoaded lsmpl
        (sendCt2EncoderSpecOfPrePostEnv M A lim
          envs.sendCt2EncoderPre envs.sendCt2EncoderPost))
  ekReceivedCt1SampledRecvCt1Ack_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 343)
      (withLsCodeLoaded lsmpl
        (ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv M A lim F K
          envs.ekReceivedCt1SampledRecvCt1AckPre envs.ekReceivedCt1SampledRecvCt1AckPost))
  ct1AcknowledgedRecvEkChunk_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 349)
      (withLsCodeRoLoaded lsmpl
        (ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv M A lim F K
          envs.ct1AcknowledgedRecvEkPre envs.ct1AcknowledgedRecvEkPost))
  ct2SampledRecvNextEpoch_ok :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 355)
      (withLsCodeLoaded lsmpl (ct2SampledRecvNextEpochSpec M A lim F))
  hdrop_pt16 :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim))
  hdrop_ct2_sampled :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 274)
      (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec M A lim F))
  hdrop_header_sent :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 276)
      (withLsCodeLoaded lsmpl (dropChunkedHeaderSentSpec M A lim F))
  hdrop_ek_sent_ct1_received :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 278)
      (withLsCodeLoaded lsmpl (dropChunkedEkSentCt1ReceivedSpec M A lim F))
  hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym (withVmPreserved noAllocShimSpec)
  halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  hdealloc_sat : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim)
  hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec)
  hmemcpy_ro_sat :
    HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpyRegionROSpec)

/-- Canonical budget-threaded relocatable callee contract bundle for `<States>::recv`
    (Block `332`, `lsProg_332`), specialized to the exact binary leaf envelopes
    `statesRecvCalleeEnvs F K`. -/
abbrev StatesRecvPlacedContracts [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  StatesRecvPlacedContractsOfEnv M A lim F K (statesRecvCalleeEnvs F K) ext

namespace StatesRecvPlacedContractsOfEnv

variable [LibsignalPlacement]
  {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
  {F : ShaCompress} {K : MlKem} {envs : StatesRecvCalleeEnvs F}
  {ext : String → Option (State → State)}

theorem hsend_ct2 (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 347)
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K
          envs.unchunkedSendCt2Pre envs.unchunkedSendCt2Post)) :=
  hC.unchunkedCt1SentEkReceivedSendCt2_ok

theorem hrecv_ek_unchunked (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 338)
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentRecvEkSpecOfPrePostEnv M A lim F K
          envs.unchunkedRecvEkPre envs.unchunkedRecvEkPost)) :=
  hC.unchunkedCt1SentRecvEk_ok

theorem hkeys_sampled_recv_ct1 (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 370)
      (withLsCodeLoaded lsmpl
        (keysSampledRecvCt1ChunkSpecOfPrePostEnv M A lim F
          envs.keysSampledRecvCt1Pre envs.keysSampledRecvCt1Post)) :=
  hC.keysSampledRecvCt1Chunk_ok

theorem hheader_sent_recv_ct1 (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 337)
      (withLsCodeRoLoaded lsmpl
        (headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv M A lim F
          envs.headerSentRecvCt1Pre envs.headerSentRecvCt1Post)) :=
  hC.headerSentRecvCt1Chunk_ok

theorem hrecv_ct1_chunk (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 337)
      (withLsCodeRoLoaded lsmpl
        (headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv M A lim F
          envs.headerSentRecvCt1Pre envs.headerSentRecvCt1Post)) :=
  hC.headerSentRecvCt1Chunk_ok

theorem hct1_recv_ct2 (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 346)
      (withLsCodeLoaded lsmpl
        (ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv M A lim F
          envs.ct1ReceivedRecvCt2Pre envs.ct1ReceivedRecvCt2Post)) :=
  hC.ct1ReceivedRecvCt2Chunk_ok

theorem hrecv_ct2_chunk (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 350)
      (withLsCodeRoLoaded lsmpl
        (recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim
          envs.ekSentCt1ReceivedRecvCt2Pre envs.ekSentCt1ReceivedRecvCt2Post)) :=
  hC.ekSentCt1ReceivedRecvCt2Chunk_ok

theorem hrecv_ct2_chunk_ext (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 350)
      (withLsCodeRoLoaded lsmpl
        (recvCt2ChunkPlacedSpecExtOfPrePostEnv K F M A lim
          envs.ekSentCt1ReceivedRecvCt2Pre envs.ekSentCt1ReceivedRecvCt2Post)) :=
  withLsCodeRoLoaded_recvCt2ChunkPlacedSpecExtOfPrePostEnv_of_X
    hC.ekSentCt1ReceivedRecvCt2Chunk_ok

theorem hrecv_hdr_chunk (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 369)
      (withLsCodeRoLoaded lsmpl
        (noHeaderReceivedRecvHdrChunkPlacedSpecOfPrePostEnv M A lim F
          envs.noHeaderReceivedRecvHdrPre envs.noHeaderReceivedRecvHdrPost)) :=
  hC.noHeaderReceivedRecvHdrChunk_ok

theorem hpoly_add_chunk (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 419)
      (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)) :=
  hC.polyAddChunk_ok

theorem hpoly_decoded_msg (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 418)
      (withLsCodeRoLoaded lsmpl
        (polyDecoderDecodedMessagePlacedSpecOfPrePostEnv M A lim
          envs.polyDecodedMessagePre envs.polyDecodedMessagePost)) :=
  hC.polyDecodedMessage_ok

theorem hsend_ct2_encoder (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 382)
      (withLsCodeLoaded lsmpl
        (sendCt2EncoderSpecOfPrePostEnv M A lim
          envs.sendCt2EncoderPre envs.sendCt2EncoderPost)) :=
  hC.sendCt2Encoder_ok

theorem hrecv_ct1_ack (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 343)
      (withLsCodeLoaded lsmpl
        (ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv M A lim F K
          envs.ekReceivedCt1SampledRecvCt1AckPre envs.ekReceivedCt1SampledRecvCt1AckPost)) :=
  hC.ekReceivedCt1SampledRecvCt1Ack_ok

theorem hct1_ack_recv_ek (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 349)
      (withLsCodeRoLoaded lsmpl
        (ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv M A lim F K
          envs.ct1AcknowledgedRecvEkPre envs.ct1AcknowledgedRecvEkPost)) :=
  hC.ct1AcknowledgedRecvEkChunk_ok

theorem hrecv_next_epoch (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 355)
      (withLsCodeLoaded lsmpl (ct2SampledRecvNextEpochSpec M A lim F)) :=
  hC.ct2SampledRecvNextEpoch_ok

theorem hrecv_next_epoch_freeOnly (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 355)
      (withLsCodeLoaded lsmpl
        (ct2SampledRecvNextEpochSpecOfEnv M A lim F (fun _ => Ct2SampledRecvNextEpochEnv))) := by
  refine subroutine_ok_mono hC.ct2SampledRecvNextEpoch_ok (fun (x, st) R s0 hp => ?_) (fun _ _ _ _ hq => hq)
  obtain ⟨hcl, hp0⟩ := extract_withLsCodeLoaded hp
  dsimp only [withLsCodeLoaded, ct2SampledRecvNextEpochSpecOfEnv, ct2SampledRecvNextEpochSpec] at hp0 ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp0 ⊢
  exact ⟨⟨hp0.1.1, hp0.1.2.1, hp0.1.2.2.1, hp0.1.2.2.2.1, hp0.1.2.2.2.2.2⟩, hp0.2⟩

/-- `drop_glue::<EkReceivedCt1Sampled>` (Block `275`) derived from `hC.hdealloc_sat`. -/
theorem hdrop_ek_received_ct1_sampled
    (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 275)
      (withLsCodeLoaded lsmpl (dropChunkedEkReceivedCt1SampledSpec M A lim F)) :=
  drop_chunked_ek_received_ct1_sampled_cl_on (idx := 332) hC.hdealloc_sat

/-- `drop_glue::<Ct1Received>` (Block `277`) derived from `hC.hdealloc_sat`. -/
theorem hdrop_ct1_received
    (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 277)
      (withLsCodeLoaded lsmpl (dropChunkedCt1ReceivedSpec M A lim F)) :=
  drop_chunked_ct1_received_cl_on (idx := 332) hC.hdealloc_sat

/-- `drop_glue::<[Poly; 16]>` (Block `265`) derived from `hC.hdealloc_sat`. -/
theorem hdrop_poly16
    (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)) :=
  drop_glue_poly16_cl_on (idx := 332) hC.hdealloc_sat

/-- `drop_glue::<PolyDecoder>` (Block `137`) derived from `hC.hdealloc_sat`. -/
theorem hdrop_poly_decoder
    (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 137)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
  drop_glue_poly_decoder_cl_on (idx := 332) hC.hdealloc_sat

/-- `drop_glue::<proto::PolyEncoder>` (Block `271`) derived from `hC.hdealloc_sat`. -/
theorem hdrop_proto_poly_encoder
    (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)) :=
  drop_glue_proto_poly_encoder_cl_on (idx := 332) hC.hdealloc_sat

/-- `drop_glue::<PolyEncoder> [local#2]` (Block `272`) derived from `hC.hdealloc_sat`. -/
theorem hdrop_poly_encoder_local2
    (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 272)
      (withLsCodeLoaded lsmpl (dropGluePolyEncoderSpec M A lim)) :=
  drop_glue_poly_encoder_local2_cl_on (idx := 332) hC.hdealloc_sat

theorem hshim_raw (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec :=
  hookSat_of_withVmPreserved hC.hshim_sat

theorem hmemcpy_raw (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec :=
  hookSat_of_withVmPreserved hC.hmemcpy_sat

theorem hmemcpy_ro_raw (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext) :
    HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec :=
  hookSat_of_withVmPreserved hC.hmemcpy_ro_sat

theorem of_callees
    (keysSampledRecvCt1Chunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 370)
        (withLsCodeLoaded lsmpl
          (keysSampledRecvCt1ChunkSpecOfPrePostEnv M A lim F
            envs.keysSampledRecvCt1Pre envs.keysSampledRecvCt1Post)))
    (headerSentRecvCt1Chunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 337)
        (withLsCodeRoLoaded lsmpl
          (headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv M A lim F
            envs.headerSentRecvCt1Pre envs.headerSentRecvCt1Post)))
    (ct1ReceivedRecvCt2Chunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 346)
        (withLsCodeLoaded lsmpl
          (ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv M A lim F
            envs.ct1ReceivedRecvCt2Pre envs.ct1ReceivedRecvCt2Post)))
    (ekSentCt1ReceivedRecvCt2Chunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 350)
        (withLsCodeRoLoaded lsmpl
          (recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim
            envs.ekSentCt1ReceivedRecvCt2Pre envs.ekSentCt1ReceivedRecvCt2Post)))
    (noHeaderReceivedRecvHdrChunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 369)
        (withLsCodeRoLoaded lsmpl
          (noHeaderReceivedRecvHdrChunkPlacedSpecOfPrePostEnv M A lim F
            envs.noHeaderReceivedRecvHdrPre envs.noHeaderReceivedRecvHdrPost)))
    (polyAddChunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 419)
        (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (polyDecodedMessage_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 418)
        (withLsCodeRoLoaded lsmpl
          (polyDecoderDecodedMessagePlacedSpecOfPrePostEnv M A lim
            envs.polyDecodedMessagePre envs.polyDecodedMessagePost)))
    (unchunkedCt1SentRecvEk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 338)
        (withLsCodeLoaded lsmpl
          (unchunkedCt1SentRecvEkSpecOfPrePostEnv M A lim F K
            envs.unchunkedRecvEkPre envs.unchunkedRecvEkPost)))
    (unchunkedCt1SentEkReceivedSendCt2_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 347)
        (withLsCodeLoaded lsmpl
          (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K
            envs.unchunkedSendCt2Pre envs.unchunkedSendCt2Post)))
    (sendCt2Encoder_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 382)
        (withLsCodeLoaded lsmpl
          (sendCt2EncoderSpecOfPrePostEnv M A lim
            envs.sendCt2EncoderPre envs.sendCt2EncoderPost)))
    (ekReceivedCt1SampledRecvCt1Ack_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 343)
        (withLsCodeLoaded lsmpl
          (ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv M A lim F K
            envs.ekReceivedCt1SampledRecvCt1AckPre envs.ekReceivedCt1SampledRecvCt1AckPost)))
    (ct1AcknowledgedRecvEkChunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 349)
        (withLsCodeRoLoaded lsmpl
          (ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv M A lim F K
            envs.ct1AcknowledgedRecvEkPre envs.ct1AcknowledgedRecvEkPost)))
    (ct2SampledRecvNextEpoch_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 355)
        (withLsCodeLoaded lsmpl (ct2SampledRecvNextEpochSpec M A lim F)))
    (hshim_sat :
      HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc_sat :
      HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat :
      HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat :
      HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hmemcpy_ro_sat :
      HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpyRegionROSpec)) :
    StatesRecvPlacedContractsOfEnv M A lim F K envs ext where
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
  hdrop_pt16 := drop_glue_sorted_set_pt16_cl_on (idx := 332) hdealloc_sat
  hdrop_ct2_sampled := drop_chunked_ct2_sampled_cl_on (idx := 332) hdealloc_sat
  hdrop_header_sent := drop_chunked_header_sent_cl_on (idx := 332) hdealloc_sat
  hdrop_ek_sent_ct1_received := drop_chunked_ek_sent_ct1_received_cl_on (idx := 332) hdealloc_sat
  hshim_sat := hshim_sat
  halloc_sat := halloc_sat
  hdealloc_sat := hdealloc_sat
  hmemcpy_sat := hmemcpy_sat
  hmemcpy_ro_sat := hmemcpy_ro_sat

end StatesRecvPlacedContractsOfEnv

namespace StatesRecvPlacedContracts

theorem of_callees [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (keysSampledRecvCt1Chunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 370)
        (withLsCodeLoaded lsmpl (keysSampledRecvCt1ChunkSpec M A lim F)))
    (headerSentRecvCt1Chunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 337)
        (withLsCodeRoLoaded lsmpl (headerSentRecvCt1ChunkPlacedSpec M A lim F)))
    (ct1ReceivedRecvCt2Chunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 346)
        (withLsCodeLoaded lsmpl (ct1ReceivedRecvCt2ChunkSpec M A lim F)))
    (ekSentCt1ReceivedRecvCt2Chunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 350)
        (withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpec K F M A lim)))
    (noHeaderReceivedRecvHdrChunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 369)
        (withLsCodeRoLoaded lsmpl (noHeaderReceivedRecvHdrChunkPlacedSpec M A lim F)))
    (polyAddChunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 419)
        (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (polyDecodedMessage_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 418)
        (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (unchunkedCt1SentRecvEk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 338)
        (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec M A lim F K)))
    (unchunkedCt1SentEkReceivedSendCt2_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 347)
        (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (sendCt2Encoder_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 382)
        (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (ekReceivedCt1SampledRecvCt1Ack_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 343)
        (withLsCodeLoaded lsmpl (ekReceivedCt1SampledRecvCt1AckPlacedSpec M A lim F K)))
    (ct1AcknowledgedRecvEkChunk_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 349)
        (withLsCodeRoLoaded lsmpl (ct1AcknowledgedRecvEkChunkPlacedSpec M A lim F K)))
    (ct2SampledRecvNextEpoch_ok :
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 355)
        (withLsCodeLoaded lsmpl (ct2SampledRecvNextEpochSpec M A lim F)))
    (hshim_sat :
      HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc_sat :
      HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat :
      HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat :
      HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hmemcpy_ro_sat :
      HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpyRegionROSpec)) :
    StatesRecvPlacedContracts M A lim F K ext :=
  StatesRecvPlacedContractsOfEnv.of_callees
    keysSampledRecvCt1Chunk_ok
    headerSentRecvCt1Chunk_ok
    ct1ReceivedRecvCt2Chunk_ok
    ekSentCt1ReceivedRecvCt2Chunk_ok
    noHeaderReceivedRecvHdrChunk_ok
    polyAddChunk_ok
    polyDecodedMessage_ok
    unchunkedCt1SentRecvEk_ok
    unchunkedCt1SentEkReceivedSendCt2_ok
    sendCt2Encoder_ok
    ekReceivedCt1SampledRecvCt1Ack_ok
    ct1AcknowledgedRecvEkChunk_ok
    ct2SampledRecvNextEpoch_ok
    hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hmemcpy_ro_sat

end StatesRecvPlacedContracts

/-! ## Top-Level & Per-Variant Budget-Threaded Relocatable Specifications of `<States>::recv` (Block `332`) -/

/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable budget specification of
    `<spqr::v1::chunked::states::States>::recv` (Block `332`, 4,884 insns). -/
def statesRecvPlacedSpecOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop) :
    Spec (StatesRecvGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.msgA ∧
      statesRecvPreInv x.self ∧
      FitsEnv M lim st (PreEnv x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA v1RecvSize ∗
      chunkedStatesAt A.repAlloc x.selfA x.self ∗
      messageAt spqrPolyApi x.msgA x.msg ∗
      statesRecvRoPlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp statesRecvStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      resultV1RecvAt A.repAlloc (F := F) x.outA (x.self.recv K x.msg) ∗
      memRegion x.selfA chunkedStatesSize ∗
      messageAt spqrPolyApi x.msgA x.msg ∗
      statesRecvRoPlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesRecvStackX
  onPanic := fun (x, _) s0 sf => statesRecvBudgetOnPanic K x s0 sf

theorem statesRecvPlacedSpecOfPrePostEnv_same [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (Env : StatesRecvGhost F → List AllocEvent → Prop) :
    statesRecvPlacedSpecOfPrePostEnv M A lim F K Env Env =
      statesRecvPlacedSpecOfEnv M A lim F K Env :=
  rfl

/-- Two-envelope (`PreEnv` / `PostEnv`) per-variant relocatable budget specification of
    `<States>::recv` (Block `332`) for a fixed `(self, msg)`. -/
def statesRecvVariantPlacedSpecOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop) :
    Spec ((BitVec 64 × BitVec 64 × BitVec 64) × M.σ) where
  pre := fun (⟨outA, selfA, msgA⟩, st) s =>
    ⌜s.readReg64 .x0 = outA ∧
      s.readReg64 .x1 = selfA ∧
      s.readReg64 .x2 = msgA ∧
      statesRecvPreInv self ∧
      FitsEnv M lim st (PreEnv ⟨outA, selfA, msgA, self, msg⟩) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion outA v1RecvSize ∗
      chunkedStatesAt A.repAlloc selfA self ∗
      messageAt spqrPolyApi msgA msg ∗
      statesRecvRoPlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp statesRecvStackX
  post := fun (⟨outA, selfA, msgA⟩, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv ⟨outA, selfA, msgA, self, msg⟩ evs⌝ ∗
      resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
      memRegion selfA chunkedStatesSize ∗
      messageAt spqrPolyApi msgA msg ∗
      statesRecvRoPlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesRecvStackX
  onPanic := fun (⟨outA, selfA, msgA⟩, _) s0 sf =>
    statesRecvBudgetOnPanic K ⟨outA, selfA, msgA, self, msg⟩ s0 sf

/-- Single-envelope (`Env`) per-variant relocatable budget specification of `<States>::recv`
    (Block `332`) for a fixed `(self, msg)`. -/
abbrev statesRecvVariantPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (Env : StatesRecvGhost F → List AllocEvent → Prop) :
    Spec ((BitVec 64 × BitVec 64 × BitVec 64) × M.σ) :=
  statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg Env Env

/-- Default per-variant relocatable budget specification of `<States>::recv` (Block `332`). -/
abbrev statesRecvVariantPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    Spec ((BitVec 64 × BitVec 64 × BitVec 64) × M.σ) :=
  statesRecvVariantPlacedSpecOfEnv M A lim F K self msg StatesRecvEnv

/-- Two-envelope (`PreEnv` / `PostEnv`) Block `332` contract on `lsProg_332 (Rust.withPanics ext)`. -/
def StatesRecvPlacedOkExtOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop) : Prop :=
  subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 332)
    (withLsCodeRoLoaded lsmpl
      (statesRecvPlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv))

/-- Single-envelope (`Env`) Block `332` contract on `lsProg_332 (Rust.withPanics ext)`. -/
abbrev StatesRecvPlacedOkExtOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (Env : StatesRecvGhost F → List AllocEvent → Prop) : Prop :=
  StatesRecvPlacedOkExtOfPrePostEnv M A lim F K ext Env Env

/-- Default Block `332` contract on `lsProg_332 (Rust.withPanics ext)`. -/
abbrev StatesRecvPlacedOkExt [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  StatesRecvPlacedOkExtOfEnv M A lim F K ext StatesRecvEnv

/-- Two-envelope (`PreEnv` / `PostEnv`) Block `332` contract on
    `libsignalSessionLib.blockProgram lsmpl 332 (Rust.withPanics ext)`. -/
def StatesRecvPlacedOkXOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 332 (Rust.withPanics ext))
    (lsmpl.base 332)
    (withLsCodeRoLoaded lsmpl
      (statesRecvPlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv))

theorem statesRecvPlacedOkXOfPrePostEnv_same [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (Env : StatesRecvGhost F → List AllocEvent → Prop) :
    StatesRecvPlacedOkXOfPrePostEnv M A lim F K ext Env Env =
      StatesRecvPlacedOkXOfEnv M A lim F K ext Env :=
  rfl

/-! ## Clean-Exit `SepWP` → `SepWPp` Adapters, Per-Variant Assembly, and Envelope Weakening -/

theorem sepWPp_of_statesRecv_exit_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (st : M.σ) (P R : SepProp)
    (h : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          PostEnv ⟨outA, selfA, msgA, self, msg⟩ evs ∧
          (Pf ⊢
            resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
            memRegion selfA chunkedStatesSize ∗
            messageAt spqrPolyApi msgA msg ∗
            statesRecvRoPlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesRecvStackX)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg PreEnv PostEnv).post
              ((outA, selfA, msgA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg PreEnv PostEnv).onPanic
              ((outA, selfA, msgA), st) s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨⟨evs, hevs, hPf⟩, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  dsimp only [statesRecvVariantPlacedSpecOfPrePostEnv]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htrf, hevs⟩,
    Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by sep_ac_rfl))) hmem_f⟩

theorem sepWPp_of_statesRecv_exit_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {Env : StatesRecvGhost F → List AllocEvent → Prop} {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) (st : M.σ) (P R : SepProp)
    (h : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf => (∃ evs : List AllocEvent, Env ⟨outA, selfA, msgA, self, msg⟩ evs ∧
        (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesRecvStackX)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨
        (statesRecvVariantPlacedSpecOfEnv M A lim F K self msg Env).post ((outA, selfA, msgA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨
        (statesRecvVariantPlacedSpecOfEnv M A lim F K self msg Env).onPanic ((outA, selfA, msgA), st) s0 sf ∗ R)) :=
  sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA self msg st P R h

theorem sepWPp_of_statesRecv_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)} (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) (st : M.σ) (P R : SepProp)
    (h : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf => (∃ evs : List AllocEvent, StatesRecvEnv ⟨outA, selfA, msgA, self, msg⟩ evs ∧
        (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesRecvStackX)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨
        (statesRecvVariantPlacedSpec M A lim F K self msg).post ((outA, selfA, msgA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨
        (statesRecvVariantPlacedSpec M A lim F K self msg).onPanic ((outA, selfA, msgA), st) s0 sf ∗ R)) :=
  sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA self msg st P R h

theorem sepWPp_of_statesRecv_exit_cl_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop} {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) (st : M.σ) (P R : SepProp)
    (h : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf => (∃ evs : List AllocEvent, PostEnv ⟨outA, selfA, msgA, self, msg⟩ evs ∧
        (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesRecvStackX)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨
        (withLsCodeLoaded lsmpl
          (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg PreEnv PostEnv)).post
          ((outA, selfA, msgA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨
        (withLsCodeLoaded lsmpl
          (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg PreEnv PostEnv)).onPanic
          ((outA, selfA, msgA), st) s0 sf ∗ R)) :=
  sepWPp_of_statesRecv_exit_placed_ofPrePostEnv (PreEnv := PreEnv) s0 s outA selfA msgA self msg st P R h

theorem sepWPp_of_statesRecv_exit_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {Env : StatesRecvGhost F → List AllocEvent → Prop} {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) (st : M.σ) (P R : SepProp)
    (h : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf => (∃ evs : List AllocEvent, Env ⟨outA, selfA, msgA, self, msg⟩ evs ∧
        (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesRecvStackX)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨
        (withLsCodeLoaded lsmpl (statesRecvVariantPlacedSpecOfEnv M A lim F K self msg Env)).post
          ((outA, selfA, msgA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨
        (withLsCodeLoaded lsmpl (statesRecvVariantPlacedSpecOfEnv M A lim F K self msg Env)).onPanic
          ((outA, selfA, msgA), st) s0 sf ∗ R)) :=
  sepWPp_of_statesRecv_exit_placed_ofPrePostEnv (PreEnv := Env) s0 s outA selfA msgA self msg st P R h

theorem sepWPp_of_statesRecv_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)} (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) (st : M.σ) (P R : SepProp)
    (h : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf => (∃ evs : List AllocEvent, StatesRecvEnv ⟨outA, selfA, msgA, self, msg⟩ evs ∧
        (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesRecvStackX)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨
        (withLsCodeLoaded lsmpl (statesRecvVariantPlacedSpec M A lim F K self msg)).post
          ((outA, selfA, msgA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨
        (withLsCodeLoaded lsmpl (statesRecvVariantPlacedSpec M A lim F K self msg)).onPanic
          ((outA, selfA, msgA), st) s0 sf ∗ R)) :=
  sepWPp_of_statesRecv_exit_placed_ofPrePostEnv (PreEnv := StatesRecvEnv) s0 s outA selfA msgA self msg st P R h

theorem sepWPp_of_statesRecv_exit_evs_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (st : M.σ) (evs : List AllocEvent)
    (hevs : PostEnv ⟨outA, selfA, msgA, self, msg⟩ evs)
    (P R : SepProp)
    (h : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg PreEnv PostEnv).post
              ((outA, selfA, msgA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg PreEnv PostEnv).onPanic
              ((outA, selfA, msgA), st) s0 sf ∗ R)) :=
  sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA self msg st P R
    (SepWP.mono h fun _ _ _ _ ⟨hPf, hsp, hcs, htr⟩ => ⟨⟨evs, hevs, hPf⟩, hsp, hcs, htr⟩)

theorem states_recv_placed_ok_ext_of_variants_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hvar : ∀ (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi),
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 332)
        (withLsCodeRoLoaded lsmpl
          (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg PreEnv PostEnv))) :
    StatesRecvPlacedOkExtOfPrePostEnv M A lim F K ext PreEnv PostEnv := by
  dsimp only [StatesRecvPlacedOkExtOfPrePostEnv]
  refine subroutine_ok_outcome_intro fun ⟨⟨outA, selfA, msgA, self, msg⟩, st⟩ R s0 hpc hrun hpre hsp =>
    (hvar self msg).mono_outcome ((outA, selfA, msgA), st) R s0 hpc hrun hpre hsp fun _ hout => hout

/-- Single-envelope (`Env`) specialization of `states_recv_placed_ok_ext_of_variants_ofPrePostEnv`. -/
theorem states_recv_placed_ok_ext_of_variants_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {Env : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hvar : ∀ (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi),
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 332)
        (withLsCodeRoLoaded lsmpl
          (statesRecvVariantPlacedSpecOfEnv M A lim F K self msg Env))) :
    StatesRecvPlacedOkExtOfEnv M A lim F K ext Env :=
  states_recv_placed_ok_ext_of_variants_ofPrePostEnv hvar

theorem states_recv_placed_ok_ext_of_variants [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hvar : ∀ (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi),
      subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 332)
        (withLsCodeRoLoaded lsmpl
          (statesRecvVariantPlacedSpec M A lim F K self msg))) :
    StatesRecvPlacedOkExt M A lim F K ext :=
  states_recv_placed_ok_ext_of_variants_ofPrePostEnv hvar

theorem states_recv_placed_ok_x_of_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : StatesRecvPlacedOkExtOfPrePostEnv M A lim F K ext PreEnv PostEnv) :
    StatesRecvPlacedOkXOfPrePostEnv M A lim F K ext PreEnv PostEnv :=
  ls_subroutine_ok_to_blockProgram (j := 332) h

theorem states_recv_placed_ok_x_of_ext_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {Env : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : StatesRecvPlacedOkExtOfEnv M A lim F K ext Env) :
    StatesRecvPlacedOkXOfEnv M A lim F K ext Env :=
  ls_subroutine_ok_to_blockProgram (j := 332) h

theorem states_recv_placed_ok_x_of_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (h : StatesRecvPlacedOkExt M A lim F K ext) :
    StatesRecvPlacedOkX M A lim F K ext :=
  ls_subroutine_ok_to_blockProgram (j := 332) h

/-- Monotonic envelope weakening for `withLsCodeRoLoaded lsmpl (statesRecvPlacedSpecOfPrePostEnv ...)`. -/
theorem subroutine_ok_statesRecvPlacedSpecOfPrePostEnv_weaken [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv₁ PostEnv₁ PreEnv₂ PostEnv₂ : StatesRecvGhost F → List AllocEvent → Prop}
    (hPre : ∀ x st, FitsEnv M lim st (PreEnv₂ x) → FitsEnv M lim st (PreEnv₁ x))
    (hPost : ∀ x evs, PostEnv₁ x evs → PostEnv₂ x evs)
    (hok : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (statesRecvPlacedSpecOfPrePostEnv M A lim F K PreEnv₁ PostEnv₁))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (statesRecvPlacedSpecOfPrePostEnv M A lim F K PreEnv₂ PostEnv₂)) := by
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hal
  obtain ⟨hcro, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (statesRecvPlacedSpecOfPrePostEnv M A lim F K PreEnv₁ PostEnv₁)).pre (x, st) s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfPrePostEnv] at hpre0 ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    exact ⟨⟨hpre0.1.1, hpre0.1.2.1, hpre0.1.2.2.1, hpre0.1.2.2.2.1,
      hPre x st hpre0.1.2.2.2.2.1, hpre0.1.2.2.2.2.2⟩,
      hpre0.2⟩
  refine subroutine_ok.mono_outcome hok (x, st) R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨c, hex, hpost⟩ | ⟨hoom, hpost⟩)
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfPrePostEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1, hPost x evs hpost.1.2⟩, hpost.2⟩
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨c, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

/-- Monotonic envelope weakening for `withLsCodeRoLoaded lsmpl (statesRecvVariantPlacedSpecOfPrePostEnv ...)`. -/
theorem subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {self : States spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    {PreEnv₁ PostEnv₁ PreEnv₂ PostEnv₂ : StatesRecvGhost F → List AllocEvent → Prop}
    (hPre : ∀ outA selfA msgA st,
      FitsEnv M lim st (PreEnv₂ ⟨outA, selfA, msgA, self, msg⟩) →
      FitsEnv M lim st (PreEnv₁ ⟨outA, selfA, msgA, self, msg⟩))
    (hPost : ∀ outA selfA msgA evs,
      PostEnv₁ ⟨outA, selfA, msgA, self, msg⟩ evs →
      PostEnv₂ ⟨outA, selfA, msgA, self, msg⟩ evs)
    (hok : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg PreEnv₁ PostEnv₁))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg PreEnv₂ PostEnv₂)) := by
  apply subroutine_ok_outcome_intro
  rintro ⟨⟨outA, selfA, msgA⟩, st⟩ R s0 hpc hrun hpre hal
  obtain ⟨hcro, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg PreEnv₁ PostEnv₁)).pre
        ((outA, selfA, msgA), st) s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, statesRecvVariantPlacedSpecOfPrePostEnv] at hpre0 ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    exact ⟨⟨hpre0.1.1, hpre0.1.2.1, hpre0.1.2.2.1, hpre0.1.2.2.2.1,
      hPre outA selfA msgA st hpre0.1.2.2.2.2.1, hpre0.1.2.2.2.2.2⟩, hpre0.2⟩
  refine subroutine_ok.mono_outcome hok ((outA, selfA, msgA), st) R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨c, hex, hpost⟩ | ⟨hoom, hpost⟩)
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, statesRecvVariantPlacedSpecOfPrePostEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1, hPost outA selfA msgA evs hpost.1.2⟩, hpost.2⟩
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨c, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

end LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
