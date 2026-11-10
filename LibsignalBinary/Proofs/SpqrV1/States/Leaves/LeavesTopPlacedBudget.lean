/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt1ChunkPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Ct1ReceivedPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.RecvCt1AckPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProofPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.ProofPlacedBudget

/-!
# SPQR V1 Leaf Subroutines: Closed Relocatable `RustCliAllocBudget` Contracts

Aggregates and closes all 15 relocatable `Obj.MultiPlacedLib` leaf contracts (`335`, `336`, `337`,
`338`, `343`, `344`, `345`, `346`, `349`, `350`, `354`, `355`, `369`, `370`, `382`) under
`[LibsignalPlacement]` and `RustCliAllocBudget M`, discharging cross-block callees `347`, `418`,
and `419`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkPC_347 blkPC_418 blkPC_419 blkPl_338 blkPl_347
  blkPl_418 blkPl_419 libsignalSessionLib lsProg_338 ls_subroutine_ok_of_block lsmpl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (MlKem SortedSetPt mlkemDecapsSpec mlkemEncaps2Spec
  mlkemValidatePkSpec)
open CryptoVerification.LibsignalTripleRatchet (HkdfPlacedHooks keys_ls_subroutine_ok_of_block_cro
  memsetName sessionMemcpyRegionSpec sessionMemmoveSpec withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Alloc (growOneStack spqrHandleErrorSym spqrMemcpySym spqrMemmoveSym
  spqrPanicConstAddOverflowSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym)
open CryptoVerification.SpqrV1.Kdf (spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.Poly.AddChunk (addChunkTotal)
open CryptoVerification.SpqrV1.States.Leaves (Ct1AcknowledgedRecvEkChunkGhost
  Ct1ReceivedRecvCt2ChunkGhost Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost
  Ct2SampledRecvNextEpochGhost Ct2SampledSendCt2ChunkGhost EkReceivedCt1SampledRecvCt1AckGhost
  EkReceivedCt1SampledSendCt1ChunkGhost HeaderSentRecvCt1ChunkGhost HeaderSentSendEkChunkGhost
  KeysSampledRecvCt1ChunkGhost PolyDecoderDecodedMessageGhost SendCt2EncoderGhost
  UnchunkedCt1SentRecvEkGhost UnchunkedSendCt2Ghost)
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk (NoHeaderReceivedRecvHdrChunkGhost)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (RecvCt2ChunkGhost spqrAssertFailedU64Sym
  spqrLibcruxHmacSym' spqrMlkemDecapsSym spqrPanicBoundsCheckSym spqrRustDeallocSym'
  spqrSliceIndexFailSym spqrUnwrapFailedSym)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym spqrMlkemEncaps2Sym)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FitsStep
  FreeOnlyEvs RustCliAllocBudget rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
  rustCliReallocBudgetSpec zeroBudgetLimits)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (framelessMemcpyAcpSpec
  sessionMemcpyRegionROSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (AddChunkSlotsEnv addChunkSpec
  addChunkSpecX)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (DecodedMessageEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1PlacedBudget (add_chunk_cl_placed_ok
  add_chunk_cl_placed_ok_x add_chunk_cro_placed_ok add_chunk_cro_placed_ok_x
  hookSat_memmove_withAllocVmPreserved_of_acp)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (Ct1AcknowledgedRecvEkChunkEnv Ct1AcknowledgedRecvEkChunkPlacedOkX
   Ct1AcknowledgedRecvEkChunkPlacedOkXOfEnv Ct1AcknowledgedRecvEkChunkPlacedOkXOfPrePostEnv
   Ct1AcknowledgedRecvEkChunkPostEnv Ct1AcknowledgedRecvEkChunkPreEnv Ct1ReceivedRecvCt2ChunkEnv
   Ct1ReceivedRecvCt2ChunkPlacedOkX Ct1ReceivedRecvCt2ChunkPlacedOkXOfEnv
   Ct1ReceivedRecvCt2ChunkPlacedOkXOfPrePostEnv Ct1ReceivedRecvCt2ChunkPostEnv
   Ct1ReceivedRecvCt2ChunkPreEnv EkReceivedCt1SampledRecvCt1AckEnv
   EkReceivedCt1SampledRecvCt1AckPlacedOkX EkReceivedCt1SampledRecvCt1AckPlacedOkXOfEnv
   EkReceivedCt1SampledRecvCt1AckPlacedOkXOfPrePostEnv EkReceivedCt1SampledRecvCt1AckPostEnv
   EkReceivedCt1SampledRecvCt1AckPreEnv HeaderSentRecvCt1ChunkEnv HeaderSentRecvCt1ChunkPlacedOkX
   HeaderSentRecvCt1ChunkPlacedOkXOfEnv HeaderSentRecvCt1ChunkPlacedOkXOfPrePostEnv
   HeaderSentRecvCt1ChunkPostEnv HeaderSentRecvCt1ChunkPreEnv KeysSampledRecvCt1ChunkEnv
   KeysSampledRecvCt1ChunkPlacedOkX KeysSampledRecvCt1ChunkPlacedOkXOfEnv
   KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv KeysSampledRecvCt1ChunkPostEnv
   KeysSampledRecvCt1ChunkPreEnv SendCt2EncoderPlacedOkX SendCt2EncoderPlacedOkXOfEnv
   SendCt2EncoderPlacedOkXOfPrePostEnv SendCt2EncoderPostEnv SendCt2EncoderPreEnv
   UnchunkedCt1SentRecvEkEnv UnchunkedCt1SentRecvEkPostEnv UnchunkedCt1SentRecvEkPreEnv
   polyDecoderDecodedMessagePlacedSpec polyDecoderDecodedMessagePlacedSpecOfEnv
   polyDecoderDecodedMessagePlacedSpecOfPrePostEnv sendCt2EncoderSpec sendCt2EncoderSpecOfEnv
   sendCt2EncoderSpecOfPrePostEnv unchunkedCt1SentRecvEkSpec unchunkedCt1SentRecvEkSpecOfEnv
   unchunkedCt1SentRecvEkSpecOfPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkPlacedBudget
  (ct1_acknowledged_recv_ek_chunk_placed_cl_ext ct1_acknowledged_recv_ek_chunk_placed_cl_ext_ofEnv
   ct1_acknowledged_recv_ek_chunk_placed_cl_ext_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudget
  (polyDecodedMessagePlacedOkX_of_hooks polyDecoderDecodedMessage_cro_placed_ok_x
   polyDecoderDecodedMessage_cro_placed_ok_x_ofEnv polyDecoderDecodedMessage_cro_placed_ok_x_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
  (Ct1ReceivedSendEkChunkEnv Ct1ReceivedSendEkChunkPlacedOkX Ct1ReceivedSendEkChunkPlacedOkXOfEnv
   Ct1SampledSendCt1ChunkEnv Ct1SampledSendCt1ChunkPlacedOkX Ct1SampledSendCt1ChunkPlacedOkXOfEnv
   Ct2SampledRecvNextEpochEnv Ct2SampledRecvNextEpochPlacedOkX Ct2SampledRecvNextEpochPlacedOkXOfEnv
   Ct2SampledSendCt2ChunkEnv Ct2SampledSendCt2ChunkPlacedOkX Ct2SampledSendCt2ChunkPlacedOkXOfEnv
   EkReceivedCt1SampledSendCt1ChunkEnv EkReceivedCt1SampledSendCt1ChunkPlacedOkX
   EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv HeaderSentSendEkChunkEnv
   HeaderSentSendEkChunkPlacedOkX HeaderSentSendEkChunkPlacedOkXOfEnv
   ct1ReceivedSendEkChunkPlacedSpec ct1ReceivedSendEkChunkPlacedSpecOfEnv
   ct1SampledSendCt1ChunkPlacedSpec ct1SampledSendCt1ChunkPlacedSpecOfEnv
   ct2SampledSendCt2ChunkPlacedSpec ct2SampledSendCt2ChunkPlacedSpecOfEnv
   ekReceivedCt1SampledSendCt1ChunkPlacedSpec ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv
   headerSentSendEkChunkPlacedSpec headerSentSendEkChunkPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkPlacedBudget
  (keys_sampled_recv_ct1_chunk_placed_cl_ext_of_sessionShim
   keys_sampled_recv_ct1_chunk_placed_cl_ext_of_sessionShim_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt1ChunkPlacedBudget
  (header_sent_recv_ct1_chunk_placed_cl_ext header_sent_recv_ct1_chunk_placed_cl_ext_ofEnv
   header_sent_recv_ct1_chunk_placed_cl_ext_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Ct1ReceivedPlacedBudget
  (ct1_received_recv_ct2_chunk_placed_cl_ext ct1_received_recv_ct2_chunk_placed_cl_ext_ofEnv
   ct1_received_recv_ct2_chunk_placed_cl_ext_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.RecvCt1AckPlacedBudget
  (ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext
   ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_ofEnv
   ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
  (NoHeaderReceivedRecvHdrChunkEnv NoHeaderReceivedRecvHdrChunkPlacedOkX
   NoHeaderReceivedRecvHdrChunkPlacedOkXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget
  (assertFailedRecvHdrSym panicBoundsCheckRecvHdrSym sliceIndexFailRecvHdrSym spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProofPlacedBudget
  (NoHeaderReceivedRecvHdrChunkPlacedOkXOfPrePostEnv noHeaderReceived_recv_hdr_chunk_placed_okX
   noHeaderReceived_recv_hdr_chunk_placed_okX_ofEnv noHeaderReceived_recv_hdr_chunk_placed_okX_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlacedBudget
  (ct2_sampled_recv_next_epoch_placed_ok_x ct2_sampled_recv_next_epoch_placed_ok_x_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1PlacedBudget
  (ct2_sampled_send_ct2_chunk_placed_ok_x ct2_sampled_send_ct2_chunk_placed_ok_x_ofEnv
   ek_received_ct1_sampled_send_ct1_chunk_placed_ok_x ek_received_ct1_sampled_send_ct1_chunk_placed_ok_x_ofEnv
   header_sent_send_ek_chunk_placed_ok_x header_sent_send_ek_chunk_placed_ok_x_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk2PlacedBudget
  (ct1_received_send_ek_chunk_placed_ok_x ct1_received_send_ek_chunk_placed_ok_x_ofEnv
   ct1_sampled_send_ct1_chunk_placed_ok_x ct1_sampled_send_ct1_chunk_placed_ok_x_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudget
  (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
   unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_ofEnv
   unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_ofPrePostEnv
   unchunked_ct1_sent_ek_received_send_ct2_cro_placed_ok
   unchunked_ct1_sent_ek_received_send_ct2_cro_placed_ok_ofEnv
   unchunked_ct1_sent_ek_received_send_ct2_cro_placed_ok_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
  (hookSat_sessionMemcpyBudget_of_region hookSat_sessionShimBudget_of_noAllocShim)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlacedBudget
  (sendCt2EncoderAllocPrefixEvents sendCt2EncoderEvents send_ct2_encoder_placed_ok_x
   send_ct2_encoder_placed_ok_x_ofEnv send_ct2_encoder_placed_ok_x_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkPlacedBudget
  (unchunked_ct1_sent_recv_ek_placed_cl_ok_x unchunked_ct1_sent_recv_ek_placed_cl_ok_x_of_env
   unchunked_ct1_sent_recv_ek_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget
  (PolyDecodedMessagePlacedOkX RecvCt2ChunkEnv RecvCt2ChunkPlacedOkExt
   RecvCt2ChunkPlacedOkExtOfEnv RecvCt2ChunkPlacedOkExtOfPrePostEnv RecvCt2ChunkPlacedOkX
   RecvCt2ChunkPlacedOkXOfEnv RecvCt2ChunkPlacedOkXOfPrePostEnv RecvCt2PlacedAlloc
   hookSat_framelessMemcpyAcp_of_allocMemcpyVm hookSat_noAllocShim_of_rustAllocShimVm)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.ProofPlacedBudget
  (recv_ct2_chunk_placed_ok_ext recv_ct2_chunk_placed_ok_ext_ofEnv
   recv_ct2_chunk_placed_ok_ext_ofPrePostEnv recv_ct2_chunk_placed_ok_ext_of_hooks
   recv_ct2_chunk_placed_ok_x recv_ct2_chunk_placed_ok_x_ofEnv
   recv_ct2_chunk_placed_ok_x_ofPrePostEnv recv_ct2_chunk_placed_ok_x_of_hooks)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
  (UnchunkedSendCt2Env UnchunkedSendCt2PostEnv UnchunkedSendCt2PreEnv
   unchunkedCt1SentEkReceivedSendCt2PlacedSpec unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv
   unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)

/-! ## 1. `HookSat` & Cross-Block `withLsCodeRoLoaded` Bridges -/

export CryptoVerification.LibsignalTripleRatchet (keys_ls_subroutine_ok_of_block_cro)
export LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1PlacedBudget
  (hookSat_memmove_withAllocVmPreserved_of_acp)
export LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget
  (hookSat_noAllocShim_of_rustAllocShimVm hookSat_framelessMemcpyAcp_of_allocMemcpyVm)
export LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
  (hookSat_sessionShimBudget_of_noAllocShim hookSat_sessionMemcpyBudget_of_region)

abbrev ls_subroutine_ok_cro_of_block := @keys_ls_subroutine_ok_of_block_cro

theorem hookSat_sessionShimBudget_of_rustAllocShimVm
    {H : String → Option (State → State)} {sym : String} (h : HookSat H sym rustAllocShimVmSpec) :
    HookSat H sym sessionShimBudgetSpec :=
  hookSat_sessionShimBudget_of_noAllocShim (hookSat_noAllocShim_of_rustAllocShimVm h)

theorem hookSat_withVmPreserved_noAllocShim_of_rustAllocShimVm
    {H : String → Option (State → State)} {sym : String} (h : HookSat H sym rustAllocShimVmSpec) :
    HookSat H sym (withVmPreserved CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec) := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocShimVmSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hpost.1.2, hpost.1.1.2.1, hpost.2⟩
  · exact Or.inr hrest

theorem hookSat_sessionMemcpyRegionBudget_of_framelessAcp
    {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym framelessMemcpyAcpSpec) : HookSat H sym sessionMemcpyRegionBudgetSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  have hpre' : s0.mem ⊨ framelessMemcpyAcpSpec.pre (dst, src, bs) s0 ∗ R := by
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
      framelessMemcpyAcpSpec] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  rcases hok (dst, src, bs) R s0 hrun hpre' hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [framelessMemcpyAcpSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1.2.2, ⟨hpost.1.1, hpost.1.2.1.2.1⟩, hpost.2⟩
  · exact Or.inr hrest

theorem hookSat_sessionMemcpyBudget_of_framelessAcp
    {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym framelessMemcpyAcpSpec) : HookSat H sym sessionMemcpyBudgetSpec :=
  hookSat_sessionMemcpyBudget_of_region (hookSat_sessionMemcpyRegionBudget_of_framelessAcp h)

theorem hookSat_withVmPreserved_memcpyRO_of_ro
    {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym sessionMemcpyRegionROSpec) :
    HookSat H sym (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  rcases hok (dst, src, bs) R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemcpyRegionROSpec, withVmPreserved,
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1.2.2, ⟨hpost.1.1, hpost.1.2.1.2.1⟩, hpost.2⟩
  · exact Or.inr hrest

/-! ## 2. `libsignalSessionLib.blockProgram` Seam Bridges for Send Chunks (`335, 336, 344, 345, 354`) -/

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1PlacedBudget
  (header_sent_send_ek_chunk_placed_ok_x header_sent_send_ek_chunk_placed_ok_x_ofEnv
   ek_received_ct1_sampled_send_ct1_chunk_placed_ok_x)
export LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1PlacedBudget
  (ek_received_ct1_sampled_send_ct1_chunk_placed_ok_x_ofEnv
   ct2_sampled_send_ct2_chunk_placed_ok_x ct2_sampled_send_ct2_chunk_placed_ok_x_ofEnv)
export LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk2PlacedBudget
  (ct1_received_send_ek_chunk_placed_ok_x ct1_received_send_ek_chunk_placed_ok_x_ofEnv
   ct1_sampled_send_ct1_chunk_placed_ok_x ct1_sampled_send_ct1_chunk_placed_ok_x_ofEnv)

theorem header_sent_send_ek_chunk_placed_blockProgram_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} {Env : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop}
    (hsub : ∀ x evs, HeaderSentSendEkChunkEnv x evs → Env x evs) (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 336 (Rust.withPanics ext)) (lsmpl.base 336)
      (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpecOfEnv M A lim F Env)) :=
  header_sent_send_ek_chunk_placed_ok_x_ofEnv hsub hA

theorem header_sent_send_ek_chunk_placed_blockProgram_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 336 (Rust.withPanics ext)) (lsmpl.base 336)
      (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpec M A lim F)) :=
  header_sent_send_ek_chunk_placed_ok_x hA

theorem ct1_received_send_ek_chunk_placed_blockProgram_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} {Env : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop}
    (hsub : ∀ x evs, Ct1ReceivedSendEkChunkEnv x evs → Env x evs) (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 345 (Rust.withPanics ext)) (lsmpl.base 345)
      (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpecOfEnv M A lim F Env)) :=
  ct1_received_send_ek_chunk_placed_ok_x_ofEnv hsub hA

theorem ct1_received_send_ek_chunk_placed_blockProgram_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 345 (Rust.withPanics ext)) (lsmpl.base 345)
      (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpec M A lim F)) :=
  ct1_received_send_ek_chunk_placed_ok_x hA

theorem ct1_sampled_send_ct1_chunk_placed_blockProgram_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} {Env : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    (hsub : ∀ x evs, Ct1SampledSendCt1ChunkEnv x evs → Env x evs) (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 335 (Rust.withPanics ext)) (lsmpl.base 335)
      (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F Env)) :=
  ct1_sampled_send_ct1_chunk_placed_ok_x_ofEnv hsub hA

theorem ct1_sampled_send_ct1_chunk_placed_blockProgram_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 335 (Rust.withPanics ext)) (lsmpl.base 335)
      (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpec M A lim F)) :=
  ct1_sampled_send_ct1_chunk_placed_ok_x hA

theorem ek_received_ct1_sampled_send_ct1_chunk_placed_blockProgram_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    (hsub : ∀ x evs, EkReceivedCt1SampledSendCt1ChunkEnv x evs → Env x evs)
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 344 (Rust.withPanics ext)) (lsmpl.base 344)
      (withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F Env)) :=
  ek_received_ct1_sampled_send_ct1_chunk_placed_ok_x_ofEnv hsub hA

theorem ek_received_ct1_sampled_send_ct1_chunk_placed_blockProgram_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 344 (Rust.withPanics ext)) (lsmpl.base 344)
      (withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpec M A lim F)) :=
  ek_received_ct1_sampled_send_ct1_chunk_placed_ok_x hA

theorem ct2_sampled_send_ct2_chunk_placed_blockProgram_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} {Env : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop}
    (hsub : ∀ x evs, Ct2SampledSendCt2ChunkEnv x evs → Env x evs) (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 354 (Rust.withPanics ext)) (lsmpl.base 354)
      (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpecOfEnv M A lim F Env)) :=
  ct2_sampled_send_ct2_chunk_placed_ok_x_ofEnv hsub hA

theorem ct2_sampled_send_ct2_chunk_placed_blockProgram_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 354 (Rust.withPanics ext)) (lsmpl.base 354)
      (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpec M A lim F)) :=
  ct2_sampled_send_ct2_chunk_placed_ok_x hA

/-! ## 3. Direct Leaf & Sidecar Re-Exports (`355, 382, 338, 347, 419, 418`) -/

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlacedBudget
  (ct2_sampled_recv_next_epoch_placed_ok_x ct2_sampled_recv_next_epoch_placed_ok_x_ofEnv)
export LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlacedBudget
  (send_ct2_encoder_placed_ok_x send_ct2_encoder_placed_ok_x_ofEnv
   send_ct2_encoder_placed_ok_x_ofPrePostEnv)
export LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkPlacedBudget
  (unchunked_ct1_sent_recv_ek_placed_ok_x unchunked_ct1_sent_recv_ek_placed_cl_ok_x
   unchunked_ct1_sent_recv_ek_placed_cl_ok_x_of_env)
export LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudget
  (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
   unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_ofEnv
   unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_ofPrePostEnv)
export LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudget
  (unchunked_ct1_sent_ek_received_send_ct2_cro_placed_ok
   unchunked_ct1_sent_ek_received_send_ct2_cro_placed_ok_ofEnv
   unchunked_ct1_sent_ek_received_send_ct2_cro_placed_ok_ofPrePostEnv)
export LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1PlacedBudget
  (add_chunk_cl_placed_ok add_chunk_cl_placed_ok_x add_chunk_cro_placed_ok
   add_chunk_cro_placed_ok_x)
export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudget
  (polyDecoderDecodedMessage_cro_placed_ok_x polyDecoderDecodedMessage_cro_placed_ok_x_ofEnv
   polyDecoderDecodedMessage_cro_placed_ok_x_ofPrePostEnv polyDecodedMessagePlacedOkX_of_hooks)

/-- Block `382` (`send_ct2_encoder`) two-envelope closed contract taking `rustAllocShimVmSpec`. -/
theorem send_ct2_encoder_placed_ok_x_of_rustAllocShimVm_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {PreEnv PostEnv : SendCt2EncoderGhost → List AllocEvent → Prop}
    (hPre : ∀ x, (x.ct2 ++ x.mac).length ≤ 1048576 →
      PreEnv x (sendCt2EncoderAllocPrefixEvents x.ct2 x.mac))
    (hPost : ∀ x, (x.ct2 ++ x.mac).length ≤ 1048576 →
      PostEnv x (sendCt2EncoderEvents x.ct2 x.mac))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    SendCt2EncoderPlacedOkXOfPrePostEnv M A lim PreEnv PostEnv ext :=
  send_ct2_encoder_placed_ok_x_ofPrePostEnv hPre hPost h_panic
    (hookSat_noAllocShim_of_rustAllocShimVm hshim) halloc hrealloc hdealloc hmemcpy

/-- Block `382` (`send_ct2_encoder`) single-envelope closed contract taking `rustAllocShimVmSpec`. -/
theorem send_ct2_encoder_placed_ok_x_of_rustAllocShimVm_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Env : SendCt2EncoderGhost → List AllocEvent → Prop}
    (hEnv : ∀ x, (x.ct2 ++ x.mac).length ≤ 1048576 → Env x (sendCt2EncoderEvents x.ct2 x.mac))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    SendCt2EncoderPlacedOkXOfEnv M A lim Env ext :=
  send_ct2_encoder_placed_ok_x_ofEnv hEnv h_panic
    (hookSat_noAllocShim_of_rustAllocShimVm hshim) halloc hrealloc hdealloc hmemcpy

/-- Block `382` (`send_ct2_encoder`) canonical closed contract taking `rustAllocShimVmSpec`. -/
theorem send_ct2_encoder_placed_ok_x_of_rustAllocShimVm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    SendCt2EncoderPlacedOkX M A lim ext :=
  send_ct2_encoder_placed_ok_x h_panic
    (hookSat_noAllocShim_of_rustAllocShimVm hshim) halloc hrealloc hdealloc hmemcpy

/-! ### Zero-Overhead Deallocation-Only Bridge for Block `338` (`<unchunked::Ct1Sent>::recv_ek`)

Block `338` only invokes `__rust_dealloc` and never allocates, so instantiating
`UnchunkedRecvEkPlacedBudget` at a zero-footprint proxy cost model discharges
`FitsEnv ... FreeOnlyEvs` unconditionally with zero `FitsEnv` obligations on `M` and `lim`. -/

private abbrev zeroOverheadModel (M : AllocCostModel) : AllocCostModel where
  σ := M.σ
  init := M.init
  step := M.step
  footprint := fun _ => 0
  maxDynIvs := fun _ => 0
  stepReserve := fun ev _ => ev.reqBytes
  liveBytes := M.liveBytes
  footprint_mono := fun _ _ => Nat.le_refl 0
  maxDynIvs_mono := fun _ _ => Nat.le_refl 0
  stepReserve_mono := fun _ _ _ => Nat.le_refl _
  req_le_stepReserve := fun _ _ => Nat.le_refl _
  liveBytes_free_le := M.liveBytes_free_le

private abbrev freeOnlyLim : BudgetLimits :=
  { staticCount := 0, staticBytes := 0, physCap := 0, enforced := true }

private abbrev rebindBudgetAlloc (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : RustCliAllocBudget (zeroOverheadModel M) where
  pool := fun l st s => if l.enforced then A.pool lim st s else A.pool zeroBudgetLimits st s
  live := A.live
  block_valid := A.block_valid
  pool_transport := fun l st s s' hvm => by
    cases l.enforced <;> exact A.pool_transport _ st s s' hvm
  pool_zero_transport := fun st s s' hpp => A.pool_zero_transport st s s' hpp

private theorem fitsStep_freeOnlyLim_zero : FitsStep freeOnlyLim 0 0 0 :=
  ⟨rfl, by decide, by decide⟩

private theorem fitsEvents_zeroOverhead_of_freeOnly (M : AllocCostModel) :
    ∀ (evs : List AllocEvent) (st : M.σ),
      FreeOnlyEvs evs → FitsEvents (zeroOverheadModel M) freeOnlyLim st evs
  | [], _, _ => trivial
  | ev :: evs, st, hfree => by
    obtain ⟨al, sz, rfl⟩ := hfree ev List.mem_cons_self
    exact ⟨⟨trivial, fitsStep_freeOnlyLim_zero⟩,
      fitsEvents_zeroOverhead_of_freeOnly M evs (M.step (.free al sz) st)
        (fun e he => hfree e (List.mem_cons_of_mem _ he))⟩

private theorem fitsEnv_zeroOverhead_freeOnly (M : AllocCostModel) (st : M.σ) :
    FitsEnv (zeroOverheadModel M) freeOnlyLim st FreeOnlyEvs :=
  fun evs hfree => fitsEvents_zeroOverhead_of_freeOnly M evs st hfree

/-- Two-envelope (`PreEnv` / `PostEnv`) `withLsCodeLoaded`-wrapped `[LibsignalPlacement]` budget
    contract for `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (Block `338`). -/
theorem unchunked_ct1_sent_recv_ek_placed_cl_twoEnv_ok_x_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hPost : ∀ x evs, FreeOnlyEvs evs → PostEnv x evs)
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K))) :
    subroutine_ok (lsProg_338 (Rust.withPanics ext)) (blkPl_338).base
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentRecvEkSpecOfPrePostEnv M A lim F K PreEnv PostEnv)) := by
  have hok := unchunked_ct1_sent_recv_ek_placed_ok_x
    (M := zeroOverheadModel M) (A := rebindBudgetAlloc M A lim) (lim := freeOnlyLim)
    (F := F) (K := K) hdealloc hval_pk
  refine subroutine_ok_withLsCodeLoaded_of_plain
    (subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_))
  · dsimp only [unchunkedCt1SentRecvEkSpecOfPrePostEnv] at hp
    dsimp only [LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.unchunkedCt1SentRecvEkSpec,
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.unchunkedCt1SentRecvEkSpecOfEnv,
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.UnchunkedCt1SentRecvEkEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨⟨hx0, hx1, hx2, hx3, hres, _hfit, hlr⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hres, fitsEnv_zeroOverhead_freeOnly M st, hlr⟩, hmem⟩
  · dsimp only [LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.unchunkedCt1SentRecvEkSpec,
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.unchunkedCt1SentRecvEkSpecOfEnv,
      unchunkedCt1SentRecvEkSpecOfPrePostEnv] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, hPost x evs hq.1.2⟩, hq.2⟩

/-- Canonical two-envelope (`PreEnv = (· = [])`, `PostEnv = FreeOnlyEvs`) `withLsCodeLoaded`
    contract for Block `338`, suitable for `StatesRecvPlacedContracts` and Block `349`. -/
theorem unchunked_ct1_sent_recv_ek_placed_cl_twoEnv_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K))) :
    subroutine_ok (lsProg_338 (Rust.withPanics ext)) (blkPl_338).base
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec M A lim F K)) :=
  unchunked_ct1_sent_recv_ek_placed_cl_twoEnv_ok_x_ofPrePostEnv (fun _ _ h => h) hdealloc hval_pk

/-! ## 4. Closed Contract for Block `370` (`<KeysSampled>::recv_ct1_chunk`) -/

theorem keys_sampled_recv_ct1_chunk_placed_ok_x_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {PreEnv PostEnv : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs1, AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      PreEnv x (evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length))
    (hPost : ∀ x evs1 evs_free, AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      FreeOnlyEvs evs_free → PostEnv x ((evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length) ++ evs_free))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack))) :
    KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_of_sessionShim_ofPrePostEnv hPre hPost
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 370) (j := 419)
      (add_chunk_cl_placed_ok h_panic hshim halloc hrealloc hmemmove))

theorem keys_sampled_recv_ct1_chunk_placed_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs1, AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      Env x (evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length))
    (hPost : ∀ x evs1 evs_free, AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      FreeOnlyEvs evs_free → Env x ((evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length) ++ evs_free))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack))) :
    KeysSampledRecvCt1ChunkPlacedOkXOfEnv M A lim F Env ext :=
  keys_sampled_recv_ct1_chunk_placed_ok_x_ofPrePostEnv
    hPre hPost h_panic hshim halloc hrealloc hdealloc hmemcpy hmemmove

theorem keys_sampled_recv_ct1_chunk_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack))) :
    KeysSampledRecvCt1ChunkPlacedOkX M A lim F ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_of_sessionShim
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 370) (j := 419)
      (add_chunk_cl_placed_ok h_panic hshim halloc hrealloc hmemmove))

/-! ## 5. Closed Contract for Block `337` (`<HeaderSent>::recv_ct1_chunk`) -/

theorem header_sent_recv_ct1_chunk_placed_ok_x_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {PreEnv PostEnv : HeaderSentRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs1 evs2, AddChunkSlotsEnv x.st.receiving_ct1.pts evs1 →
      DecodedMessageEnv (addChunkTotal x.st.receiving_ct1 x.chunk) evs2 → PreEnv x (evs1 ++ evs2))
    (hPost : ∀ x evs1 evs2 evs_free, AddChunkSlotsEnv x.st.receiving_ct1.pts evs1 →
      DecodedMessageEnv (addChunkTotal x.st.receiving_ct1 x.chunk) evs2 → FreeOnlyEvs evs_free →
      PostEnv x ((evs1 ++ evs2) ++ evs_free))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec) :
    HeaderSentRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext :=
  header_sent_recv_ct1_chunk_placed_cl_ext_ofPrePostEnv hPre hPost hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 337) (j := 419)
      (add_chunk_cl_placed_ok h_panic hshim halloc hrealloc hmemmove))
    (keys_ls_subroutine_ok_of_block_cro (i := 337) (j := 418)
      (polyDecoderDecodedMessage_cro_placed_ok_x h_panic
        (hookSat_sessionShimBudget_of_rustAllocShimVm hshim)
        halloc hrealloc hdealloc hmemcpy hmemset))

theorem header_sent_recv_ct1_chunk_placed_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : HeaderSentRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs1 evs2, AddChunkSlotsEnv x.st.receiving_ct1.pts evs1 →
      DecodedMessageEnv (addChunkTotal x.st.receiving_ct1 x.chunk) evs2 → Env x (evs1 ++ evs2))
    (hPost : ∀ x evs1 evs2 evs_free, AddChunkSlotsEnv x.st.receiving_ct1.pts evs1 →
      DecodedMessageEnv (addChunkTotal x.st.receiving_ct1 x.chunk) evs2 → FreeOnlyEvs evs_free →
      Env x ((evs1 ++ evs2) ++ evs_free))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec) :
    HeaderSentRecvCt1ChunkPlacedOkXOfEnv M A lim F Env ext :=
  header_sent_recv_ct1_chunk_placed_ok_x_ofPrePostEnv
    hPre hPost h_panic hshim halloc hrealloc hdealloc hmemcpy hmemmove hmemset

theorem header_sent_recv_ct1_chunk_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec) :
    HeaderSentRecvCt1ChunkPlacedOkX M A lim F ext :=
  header_sent_recv_ct1_chunk_placed_cl_ext hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 337) (j := 419)
      (add_chunk_cl_placed_ok h_panic hshim halloc hrealloc hmemmove))
    (keys_ls_subroutine_ok_of_block_cro (i := 337) (j := 418)
      (polyDecoderDecodedMessage_cro_placed_ok_x h_panic
        (hookSat_sessionShimBudget_of_rustAllocShimVm hshim)
        halloc hrealloc hdealloc hmemcpy hmemset))

/-! ## 6. Closed Contract for Block `346` (`<Ct1Received>::recv_ct2_chunk`) -/

theorem ct1_received_recv_ct2_chunk_placed_ok_x_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {PreEnv PostEnv : Ct1ReceivedRecvCt2ChunkGhost F → List AllocEvent → Prop}
    (hpre_sub : ∀ x evs, Ct1ReceivedRecvCt2ChunkPreEnv x evs → PreEnv x evs)
    (hpost_sub : ∀ x evs, Ct1ReceivedRecvCt2ChunkPostEnv x evs → PostEnv x evs)
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack))) :
    Ct1ReceivedRecvCt2ChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext :=
  ct1_received_recv_ct2_chunk_placed_cl_ext_ofPrePostEnv hpre_sub hpost_sub hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 346) (j := 419)
      (add_chunk_cl_placed_ok h_panic hshim halloc hrealloc hmemmove))

theorem ct1_received_recv_ct2_chunk_placed_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : Ct1ReceivedRecvCt2ChunkGhost F → List AllocEvent → Prop}
    (hpost_sub : ∀ x evs, Ct1ReceivedRecvCt2ChunkPostEnv x evs → Env x evs)
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack))) :
    Ct1ReceivedRecvCt2ChunkPlacedOkXOfEnv M A lim F Env ext :=
  ct1_received_recv_ct2_chunk_placed_cl_ext_ofEnv hpost_sub hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 346) (j := 419)
      (add_chunk_cl_placed_ok h_panic hshim halloc hrealloc hmemmove))

theorem ct1_received_recv_ct2_chunk_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack))) :
    Ct1ReceivedRecvCt2ChunkPlacedOkX M A lim F ext :=
  ct1_received_recv_ct2_chunk_placed_cl_ext hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 346) (j := 419)
      (add_chunk_cl_placed_ok h_panic hshim halloc hrealloc hmemmove))

/-! ## 7. Closed Contract for Block `343` (`<EkReceivedCt1Sampled>::recv_ct1_ack`) -/

theorem ek_received_ct1_sampled_recv_ct1_ack_placed_ok_x_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    {PreEnv PostEnv : EkReceivedCt1SampledRecvCt1AckGhost F → List AllocEvent → Prop}
    (hpre_sub : ∀ x evs, EkReceivedCt1SampledRecvCt1AckPreEnv K x evs → PreEnv x evs)
    (hpost_sub : ∀ x evs, EkReceivedCt1SampledRecvCt1AckPostEnv K x evs → PostEnv x evs)
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) "memcpy" framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemcpy_ro : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym
      (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    EkReceivedCt1SampledRecvCt1AckPlacedOkXOfPrePostEnv M A lim F K PreEnv PostEnv ext :=
  ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_ofPrePostEnv hpre_sub hpost_sub hdealloc
    (ls_subroutine_ok_of_block (i := 343) (j := 347)
      (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
        h_panic hshim halloc hrealloc hdealloc hmemcpy_fl hmemcpy_ro hencaps2 hhmac))
    (ls_subroutine_ok_of_block (i := 343) (j := 382)
      (send_ct2_encoder_placed_ok_x h_panic
        (hookSat_noAllocShim_of_rustAllocShimVm hshim) halloc hrealloc hdealloc hmemcpy))

theorem ek_received_ct1_sampled_recv_ct1_ack_placed_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    {Env : EkReceivedCt1SampledRecvCt1AckGhost F → List AllocEvent → Prop}
    (hpost_sub : ∀ x evs, EkReceivedCt1SampledRecvCt1AckPostEnv K x evs → Env x evs)
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) "memcpy" framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemcpy_ro : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym
      (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    EkReceivedCt1SampledRecvCt1AckPlacedOkXOfEnv M A lim F K Env ext :=
  ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_ofEnv hpost_sub hdealloc
    (ls_subroutine_ok_of_block (i := 343) (j := 347)
      (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
        h_panic hshim halloc hrealloc hdealloc hmemcpy_fl hmemcpy_ro hencaps2 hhmac))
    (ls_subroutine_ok_of_block (i := 343) (j := 382)
      (send_ct2_encoder_placed_ok_x h_panic
        (hookSat_noAllocShim_of_rustAllocShimVm hshim) halloc hrealloc hdealloc hmemcpy))

theorem ek_received_ct1_sampled_recv_ct1_ack_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) "memcpy" framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemcpy_ro : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym
      (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    EkReceivedCt1SampledRecvCt1AckPlacedOkX M A lim F K ext :=
  ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext hdealloc
    (ls_subroutine_ok_of_block (i := 343) (j := 347)
      (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
        h_panic hshim halloc hrealloc hdealloc hmemcpy_fl hmemcpy_ro hencaps2 hhmac))
    (ls_subroutine_ok_of_block (i := 343) (j := 382)
      (send_ct2_encoder_placed_ok_x h_panic
        (hookSat_noAllocShim_of_rustAllocShimVm hshim) halloc hrealloc hdealloc hmemcpy))

/-! ## 8. Closed Contract for Block `349` (`<Ct1Acknowledged>::recv_ek_chunk`) -/

theorem ct1_acknowledged_recv_ek_chunk_placed_closed_ok_x_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    {PreEnv PostEnv : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop}
    (hpre_sub : ∀ x evs, Ct1AcknowledgedRecvEkChunkPreEnv K x evs → PreEnv x evs)
    (hpost_sub : ∀ x evs, Ct1AcknowledgedRecvEkChunkPostEnv K x evs → PostEnv x evs)
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) "memcpy" framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemcpy_ro : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionROSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K)))
    (hencaps2 : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym
      (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    Ct1AcknowledgedRecvEkChunkPlacedOkXOfPrePostEnv M A lim F K PreEnv PostEnv ext :=
  ct1_acknowledged_recv_ek_chunk_placed_cl_ext_ofPrePostEnv hpre_sub hpost_sub hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 349) (j := 419)
      (add_chunk_cl_placed_ok h_panic hshim halloc hrealloc hmemmove))
    (keys_ls_subroutine_ok_of_block_cro (i := 349) (j := 418)
      (polyDecoderDecodedMessage_cro_placed_ok_x h_panic
        (hookSat_sessionShimBudget_of_rustAllocShimVm hshim)
        halloc hrealloc hdealloc hmemcpy hmemset))
    (ls_subroutine_ok_of_block (i := 349) (j := 338)
      (unchunked_ct1_sent_recv_ek_placed_cl_twoEnv_ok_x (F := F) hdealloc hval_pk))
    (ls_subroutine_ok_of_block (i := 349) (j := 347)
      (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
        h_panic hshim halloc hrealloc hdealloc hmemcpy_fl hmemcpy_ro hencaps2 hhmac))
    (ls_subroutine_ok_of_block (i := 349) (j := 382)
      (send_ct2_encoder_placed_ok_x h_panic
        (hookSat_noAllocShim_of_rustAllocShimVm hshim) halloc hrealloc hdealloc hmemcpy))

theorem ct1_acknowledged_recv_ek_chunk_placed_closed_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    {Env : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop}
    (hpost_sub : ∀ x evs, Ct1AcknowledgedRecvEkChunkPostEnv K x evs → Env x evs)
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) "memcpy" framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemcpy_ro : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionROSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K)))
    (hencaps2 : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym
      (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    Ct1AcknowledgedRecvEkChunkPlacedOkXOfEnv M A lim F K Env ext :=
  ct1_acknowledged_recv_ek_chunk_placed_cl_ext_ofEnv hpost_sub hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 349) (j := 419)
      (add_chunk_cl_placed_ok h_panic hshim halloc hrealloc hmemmove))
    (keys_ls_subroutine_ok_of_block_cro (i := 349) (j := 418)
      (polyDecoderDecodedMessage_cro_placed_ok_x h_panic
        (hookSat_sessionShimBudget_of_rustAllocShimVm hshim)
        halloc hrealloc hdealloc hmemcpy hmemset))
    (ls_subroutine_ok_of_block (i := 349) (j := 338)
      (unchunked_ct1_sent_recv_ek_placed_cl_twoEnv_ok_x (F := F) hdealloc hval_pk))
    (ls_subroutine_ok_of_block (i := 349) (j := 347)
      (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
        h_panic hshim halloc hrealloc hdealloc hmemcpy_fl hmemcpy_ro hencaps2 hhmac))
    (ls_subroutine_ok_of_block (i := 349) (j := 382)
      (send_ct2_encoder_placed_ok_x h_panic
        (hookSat_noAllocShim_of_rustAllocShimVm hshim) halloc hrealloc hdealloc hmemcpy))

theorem ct1_acknowledged_recv_ek_chunk_placed_closed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) "memcpy" framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hmemcpy_ro : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionROSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K)))
    (hencaps2 : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym
      (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    Ct1AcknowledgedRecvEkChunkPlacedOkX M A lim F K ext :=
  ct1_acknowledged_recv_ek_chunk_placed_cl_ext hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 349) (j := 419)
      (add_chunk_cl_placed_ok h_panic hshim halloc hrealloc hmemmove))
    (keys_ls_subroutine_ok_of_block_cro (i := 349) (j := 418)
      (polyDecoderDecodedMessage_cro_placed_ok_x h_panic
        (hookSat_sessionShimBudget_of_rustAllocShimVm hshim)
        halloc hrealloc hdealloc hmemcpy hmemset))
    (ls_subroutine_ok_of_block (i := 349) (j := 338)
      (unchunked_ct1_sent_recv_ek_placed_cl_twoEnv_ok_x (F := F) hdealloc hval_pk))
    (ls_subroutine_ok_of_block (i := 349) (j := 347)
      (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
        h_panic hshim halloc hrealloc hdealloc hmemcpy_fl hmemcpy_ro hencaps2 hhmac))
    (ls_subroutine_ok_of_block (i := 349) (j := 382)
      (send_ct2_encoder_placed_ok_x h_panic
        (hookSat_noAllocShim_of_rustAllocShimVm hshim) halloc hrealloc hdealloc hmemcpy))

/-! ## 9. Closed Contract for Block `369` (`<NoHeaderReceived>::recv_hdr_chunk`) -/

theorem noHeaderReceived_recv_hdr_chunk_placed_closed_okX_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hPre : ∀ x st, FitsEnv M lim st (PreEnv x) → FitsEnv M lim st (NoHeaderReceivedRecvHdrChunkEnv x))
    (hPost : ∀ x evs, NoHeaderReceivedRecvHdrChunkEnv x evs → PostEnv x evs)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed : (Rust.withPanics ext) assertFailedRecvHdrSym = some Rust.panicked)
    (h_slice_index_fail : (Rust.withPanics ext) sliceIndexFailRecvHdrSym = some Rust.panicked)
    (h_panic_bounds_check : (Rust.withPanics ext) panicBoundsCheckRecvHdrSym = some Rust.panicked) :
    NoHeaderReceivedRecvHdrChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext :=
  noHeaderReceived_recv_hdr_chunk_placed_okX_ofPrePostEnv hPre hPost
    (add_chunk_cl_placed_ok_x h_handle_error hshim halloc hrealloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks h_handle_error
      (hookSat_sessionShimBudget_of_rustAllocShimVm hshim)
      halloc hrealloc hdealloc hmemcpy hmemset)
    hshim halloc hdealloc hmemcpy_fl hRO hhmac
    h_handle_error h_assert_failed h_slice_index_fail h_panic_bounds_check

theorem noHeaderReceived_recv_hdr_chunk_placed_closed_okX_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hPre : ∀ x st, FitsEnv M lim st (Env x) → FitsEnv M lim st (NoHeaderReceivedRecvHdrChunkEnv x))
    (hPost : ∀ x evs, NoHeaderReceivedRecvHdrChunkEnv x evs → Env x evs)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed : (Rust.withPanics ext) assertFailedRecvHdrSym = some Rust.panicked)
    (h_slice_index_fail : (Rust.withPanics ext) sliceIndexFailRecvHdrSym = some Rust.panicked)
    (h_panic_bounds_check : (Rust.withPanics ext) panicBoundsCheckRecvHdrSym = some Rust.panicked) :
    NoHeaderReceivedRecvHdrChunkPlacedOkXOfEnv M A lim F Env ext :=
  noHeaderReceived_recv_hdr_chunk_placed_closed_okX_ofPrePostEnv hPre hPost
    hshim halloc hrealloc hdealloc hmemcpy_fl hmemcpy hRO hmemmove hmemset hhmac
    h_handle_error h_assert_failed h_slice_index_fail h_panic_bounds_check

theorem noHeaderReceived_recv_hdr_chunk_placed_closed_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_fl : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed : (Rust.withPanics ext) assertFailedRecvHdrSym = some Rust.panicked)
    (h_slice_index_fail : (Rust.withPanics ext) sliceIndexFailRecvHdrSym = some Rust.panicked)
    (h_panic_bounds_check : (Rust.withPanics ext) panicBoundsCheckRecvHdrSym = some Rust.panicked) :
    NoHeaderReceivedRecvHdrChunkPlacedOkX M A lim F ext :=
  noHeaderReceived_recv_hdr_chunk_placed_okX
    (add_chunk_cl_placed_ok_x h_handle_error hshim halloc hrealloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks h_handle_error
      (hookSat_sessionShimBudget_of_rustAllocShimVm hshim)
      halloc hrealloc hdealloc hmemcpy hmemset)
    hshim halloc hdealloc hmemcpy_fl hRO hhmac
    h_handle_error h_assert_failed h_slice_index_fail h_panic_bounds_check

/-! ## 10. Closed Contract for Block `350` (`<EkSentCt1Received>::recv_ct2_chunk`) -/

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x_ofPrePostEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} [HkdfPlacedHooks F (Rust.withPanics ext)]
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
  recv_ct2_chunk_placed_ok_x_ofPrePostEnv hsub_pre hsub_post hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x_ofEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hsub : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent}, RecvCt2ChunkEnv x evs → Env x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkXOfEnv K F M A lim Env ext :=
  recv_ct2_chunk_placed_ok_x_ofEnv hsub hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkX K F M A lim ext :=
  recv_ct2_chunk_placed_ok_x hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x_of_alloc [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkX K F M A lim ext :=
  ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x hA
    (hookSat_sessionMemcpyRegionBudget_of_framelessAcp hA.memcpy) hmemmove hmemset hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x_of_hooks [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooks F (Rust.withPanics ext)]
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
  recv_ct2_chunk_placed_ok_x_of_hooks
    (add_chunk_cl_placed_ok_x h_handle_error hshim halloc hrealloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks h_handle_error
      (hookSat_sessionShimBudget_of_rustAllocShimVm hshim)
      halloc hrealloc hdealloc hmemcpy hmemset)
    hshim halloc hallocZeroed hdealloc hrealloc hmemcpy_fl hRO hdecaps hhmac
    h_handle_error h_assert_failed_u64 h_slice_index_fail
    h_unwrap_failed h_panic_bounds_check h_panic_add_overflow

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_ofPrePostEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} [HkdfPlacedHooks F (Rust.withPanics ext)]
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
  recv_ct2_chunk_placed_ok_ext_ofPrePostEnv hsub_pre hsub_post hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_ofEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hsub : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent}, RecvCt2ChunkEnv x evs → Env x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExtOfEnv K F M A lim Env ext :=
  recv_ct2_chunk_placed_ok_ext_ofEnv hsub hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionBudgetSpec)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  recv_ct2_chunk_placed_ok_ext hA
    (add_chunk_cl_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks hA.handleError
      (hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim)
      hA.alloc hA.realloc hA.dealloc hmemcpy hmemset)
    hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_of_alloc [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext hA
    (hookSat_sessionMemcpyRegionBudget_of_framelessAcp hA.memcpy) hmemmove hmemset hdecaps hhmac

theorem ek_sent_ct1_received_recv_ct2_chunk_placed_ok_ext_of_hooks [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [HkdfPlacedHooks F (Rust.withPanics ext)]
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
  recv_ct2_chunk_placed_ok_ext_of_hooks
    (add_chunk_cl_placed_ok_x h_handle_error hshim halloc hrealloc hmemmove)
    (polyDecodedMessagePlacedOkX_of_hooks h_handle_error
      (hookSat_sessionShimBudget_of_rustAllocShimVm hshim)
      halloc hrealloc hdealloc hmemcpy hmemset)
    hshim halloc hallocZeroed hdealloc hrealloc hmemcpy_fl hRO hdecaps hhmac
    h_handle_error h_assert_failed_u64 h_slice_index_fail
    h_unwrap_failed h_panic_bounds_check h_panic_add_overflow

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudget
