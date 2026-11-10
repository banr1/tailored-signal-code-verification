/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProofClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateClPlacedBudget

/-!
# Budget-Threaded Placed `V1State::merge` & `spqr::decode_state` Instantiations

Proves code-loaded placed budget contracts for `V1State::merge` (Block 298) and
`spqr::decode_state` (Block 325) in both default and envelope-parametric (`OfEnv`) forms, together
with leaf-discharged corollaries parameterized only by `bytes::merge` (Block 290) and the chunked
`merge` blocks (Blocks 300..310).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement libsignalSessionLib lsmpl withLsCodeLoaded)
open CryptoVerification.Cli.SpqrV1.Top.Send (ls_subroutine_ok_of_blockProgram_cro)
open CryptoVerification.LibsignalTripleRatchet (keys_ls_subroutine_ok_of_block_cro withLsCodeRoLoaded)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots (lsRngFillSym trTrapExternsPlaced)
open CryptoVerification.SpqrV1.Prost.MessageMerge (V1StateMergeGhost)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification.SpqrV1.Top.Recv (spqrRecvPlacedProg)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget (spqrSendPlacedProg)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (bytesMerge3RawBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
  (chainParamsMerge_decodeState_of_prost cliChainParams_294_cl
   cliDeallocBudget_at_block cliDrop_267_cl cliDrop_270_cl cliDrop_271_cl
   cliDrop_281_cl cliDrop_282_cl cliDrop_283_cl cliDrop_284_cl cliDrop_285_cl cliDrop_286_cl
   cliEpochDir_299_cl cliFrom_261_cl cliGrowOne_356_cl cliLibcMemcpyBudget_at_block
   cliPushMerge_257_cl cliSessionMemcpyBudget_at_block cliSkip_263_cl cliVarint_291_cl
   decodeErrorPush_of_merge epochDirectionMerge_decodeState_of_prost skipField3Budget_of_prost)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget
  (dropProtoChunkedCt1ReceivedSpec dropProtoChunkedHeaderSentSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
  (dropOptProtoInnerStatePlacedSpec dropProtoPqRatchetStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (chunkedCt1AcknowledgedMergeSpec chunkedCt1ReceivedMergeSpec chunkedCt1SampledMergeSpec
   chunkedEkSentCt1ReceivedMergeSpec decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (chunkedCt2SampledMergeSpec chunkedEkReceivedCt1SampledMergeSpec chunkedHeaderReceivedMergeSpec
   chunkedHeaderSentMergeSpec chunkedKeysSampledMergeSpec chunkedKeysUnsampledMergeSpec
   chunkedNoHeaderReceivedMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (V1StateMergeEnv V1StateMergePostEnv v1StateMergePlacedSpec v1StateMergePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProofClPlacedBudget
  (v1State_mergeOfEnv_cl v1State_merge_cl)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (decodeStatePlacedSpecX spqrDecodeStatePlacedSpec spqrDecodeStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateClPlacedBudget
  (spqr_decode_state_cl_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget (decodeStatePlacedSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-!
## 1. Own-Block Code-Loaded Theorems (`Block 298` `V1State::merge` & `Block 325` `spqr::decode_state`)
-/

private theorem hExt_withPanics {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := fun sym hne => by
  rw [← withPanics_cliGhostExterns mmpl gh W]
  simp only [Rust.withPanics, hExt sym hne]

/-- Envelope-parameterized own-block code-loaded `V1State::merge` (`Block 298`) contract under
`[CliSpqrExt W ext]`. -/
theorem cliV1StateMergeOfEnv_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {PreEnv PostEnv : V1StateMergeGhost → List AllocEvent → Prop}
    (hpre : ∀ x evs, V1StateMergeEnv x evs → PreEnv x evs)
    (hpost : ∀ x evs, V1StateMergePostEnv x evs → PostEnv x evs)
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim PreEnv PostEnv)) :=
  v1State_mergeOfEnv_cl hpre hpost
    (cliDeallocBudget_at_block mmpl gh W hA (hExt_withPanics hExt) (i := 298))
    hFrom261 hPush257 hVarint291 hSkip263
    hDrop267 hDrop282 hDrop281
    (cliDrop_285_cl mmpl gh W hA hExt) (cliDrop_284_cl mmpl gh W hA hExt) (cliDrop_283_cl mmpl gh W hA hExt)
    (cliDrop_286_cl mmpl gh W hA hExt) (cliDrop_271_cl mmpl gh W hA hExt)
    hMerge305 hMerge304 hMerge302 hMerge303 hMerge309 hMerge308 hMerge306
    hMerge300 hMerge310 hMerge307 hMerge301

/-- Own-block code-loaded `V1State::merge` (`Block 298`) contract under `[CliSpqrExt W ext]`. -/
theorem cliV1StateMerge_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim)) :=
  v1State_merge_cl
    (cliDeallocBudget_at_block mmpl gh W hA (hExt_withPanics hExt) (i := 298))
    hFrom261 hPush257 hVarint291 hSkip263
    hDrop267 hDrop282 hDrop281
    (cliDrop_285_cl mmpl gh W hA hExt) (cliDrop_284_cl mmpl gh W hA hExt) (cliDrop_283_cl mmpl gh W hA hExt)
    (cliDrop_286_cl mmpl gh W hA hExt) (cliDrop_271_cl mmpl gh W hA hExt)
    hMerge305 hMerge304 hMerge302 hMerge303 hMerge309 hMerge308 hMerge306
    hMerge300 hMerge310 hMerge307 hMerge301

/-- Envelope-parameterized own-block code-loaded `spqr::decode_state` (`Block 325`) contract under
`[CliSpqrExt W ext]`. -/
theorem cliSpqrDecodeStateOfEnv_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    (hpre_imp : ∀ x evs, DecodeStateEnv x evs → PreEnv x evs)
    (hpost_imp : ∀ x evs, DecodeStateEnv x evs → PostEnv x evs)
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDrop270 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hChainParams294 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget.chainParamsMergeSpec A lim)))
    (hEpochDir299 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.epochDirectionMergeSpec A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim PreEnv PostEnv)) :=
  spqr_decode_state_cl_ofEnv hpre_imp hpost_imp
    (cliDeallocBudget_at_block mmpl gh W hA (hExt_withPanics hExt) (i := 325))
    (fun stk _ _ => cliLibcMemcpyBudget_at_block mmpl gh W hA (hExt_withPanics hExt) stk (i := 325))
    (fun stk _ _ => cliSessionMemcpyBudget_at_block mmpl gh W hA (hExt_withPanics hExt) stk (i := 325))
    hFrom261
    (decodeErrorPush_of_merge hPush257)
    hVarint291
    (skipField3Budget_of_prost hSkip263)
    (chainParamsMerge_decodeState_of_prost hChainParams294)
    (cliGrowOne_356_cl mmpl gh W hA hExt)
    hDrop267 hDrop270 hBytes290
    (epochDirectionMerge_decodeState_of_prost hEpochDir299)
    (cliV1StateMerge_cl mmpl gh W hA hExt hDrop267 hDrop281 hDrop282 hPush257 hFrom261 hSkip263 hVarint291
      hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
      hMerge307 hMerge308 hMerge309 hMerge310)

/-- Own-block code-loaded `spqr::decode_state` (`Block 325`) contract under `[CliSpqrExt W ext]`. -/
theorem cliSpqrDecodeState_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDrop270 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hChainParams294 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget.chainParamsMergeSpec A lim)))
    (hEpochDir299 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.epochDirectionMergeSpec A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecX canonicalV1InnerHeap A lim)) :=
  cliSpqrDecodeStateOfEnv_cl mmpl gh W hA hExt (fun _ _ h => h) (fun _ _ h => h)
    hDrop267 hDrop270 hDrop281 hDrop282
    hPush257 hFrom261 hSkip263 hBytes290 hVarint291 hChainParams294 hEpochDir299
    hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
    hMerge307 hMerge308 hMerge309 hMerge310

/-! ## 2. for `spqr::send::<Coins>` (`Block 427`) & `spqr::recv` (`Block 329`) -/

/-- Own-block `Block 325` contract specialized to `ext = cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliSpqrDecodeState_sendCoins_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDrop270 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hChainParams294 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 294)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget.chainParamsMergeSpec A lim)))
    (hEpochDir299 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.epochDirectionMergeSpec A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecX canonicalV1InnerHeap A lim)) :=
  cliSpqrDecodeState_cl mmpl gh W hA (fun _ _ => rfl)
    hDrop267 hDrop270 hDrop281 hDrop282
    hPush257 hFrom261 hSkip263 hBytes290 hVarint291 hChainParams294 hEpochDir299
    hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
    hMerge307 hMerge308 hMerge309 hMerge310

/-- on `spqrSendPlacedProg ext`: Exact `hDecodeState` hypothesis of
`ContractsPlacedBudget.spqrSendPlacedContractsTight_of_okX`, generic in `[CliSpqrExt W ext]`. -/
theorem cliSpqrSend_decodeState_ok_ext [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDrop270 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hChainParams294 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget.chainParamsMergeSpec A lim)))
    (hEpochDir299 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.epochDirectionMergeSpec A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpec canonicalV1InnerHeap A lim)) :=
  ls_subroutine_ok_of_blockProgram_cro
    (cliSpqrDecodeState_cl mmpl gh W hA hExt
      hDrop267 hDrop270 hDrop281 hDrop282
      hPush257 hFrom261 hSkip263 hBytes290 hVarint291 hChainParams294 hEpochDir299
      hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
      hMerge307 hMerge308 hMerge309 hMerge310)

/-- specialized to `cliGhostExterns gh (cliExternsPlaced mmpl W)` on
`spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem cliSpqrSend_decodeState_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDrop270 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hChainParams294 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 294)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget.chainParamsMergeSpec A lim)))
    (hEpochDir299 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.epochDirectionMergeSpec A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpec canonicalV1InnerHeap A lim)) :=
  cliSpqrSend_decodeState_ok_ext mmpl gh W hA (fun _ _ => rfl)
    hDrop267 hDrop270 hDrop281 hDrop282
    hPush257 hFrom261 hSkip263 hBytes290 hVarint291 hChainParams294 hEpochDir299
    hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
    hMerge307 hMerge308 hMerge309 hMerge310

/-- Exact `decodeState_ok` field type of `SpqrRecvPlacedContractsOfEnv` with `H_inner = canonicalV1InnerHeap`, generic in
`[CliSpqrExt W ext]`. -/
theorem cliSpqrDecodeState_recv_ok_ofEnv [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    (hpre_imp : ∀ x evs, DecodeStateEnv x evs → PreEnv x evs)
    (hpost_imp : ∀ x evs, DecodeStateEnv x evs → PostEnv x evs)
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDrop270 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hChainParams294 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget.chainParamsMergeSpec A lim)))
    (hEpochDir299 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.epochDirectionMergeSpec A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfEnv canonicalV1InnerHeap A lim PreEnv PostEnv)) :=
  keys_ls_subroutine_ok_of_block_cro (callerProg := spqrRecvPlacedProg ext)
    (i := 329) (j := 325)
    (hcallee_prog := ⟨rfl, IsLsBlockProg.externs_eq
      (prog := (blkPC_325).rebase (blkPl_325).base (fun _ => none))⟩)
    (bi := 619) (bj := 619)
    (cliSpqrDecodeStateOfEnv_cl mmpl gh W hA hExt hpre_imp hpost_imp
      hDrop267 hDrop270 hDrop281 hDrop282
      hPush257 hFrom261 hSkip263 hBytes290 hVarint291 hChainParams294 hEpochDir299
      hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
      hMerge307 hMerge308 hMerge309 hMerge310)
    (by decide) (by decide) (by decide)

/-- Exact `decodeState_ok` field type of `SpqrRecvPlacedContracts` with `H_inner = canonicalV1InnerHeap`, generic in
`[CliSpqrExt W ext]`. -/
theorem cliSpqrDecodeState_recv_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDrop270 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hChainParams294 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget.chainParamsMergeSpec A lim)))
    (hEpochDir299 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.epochDirectionMergeSpec A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.decodeStatePlacedSpecX
          canonicalV1InnerHeap A lim)) :=
  cliSpqrDecodeState_recv_ok_ofEnv mmpl gh W hA hExt (fun _ _ h => h) (fun _ _ h => h)
    hDrop267 hDrop270 hDrop281 hDrop282
    hPush257 hFrom261 hSkip263 hBytes290 hVarint291 hChainParams294 hEpochDir299
    hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
    hMerge307 hMerge308 hMerge309 hMerge310

/-- specialized to `trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))` (`Block 329` CLI hook map). -/
theorem cliSpqrDecodeState_recv_trTrap_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDrop270 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hChainParams294 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 294)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget.chainParamsMergeSpec A lim)))
    (hEpochDir299 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.epochDirectionMergeSpec A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.decodeStatePlacedSpecX
          canonicalV1InnerHeap A lim)) :=
  cliSpqrDecodeState_recv_ok mmpl gh W hA
    (fun sym hne => by
      have hbeq : (sym == lsRngFillSym) = false := beq_false_of_ne hne
      simp [trTrapExternsPlaced, ProofLib.Variant.trapAt, hbeq])
    hDrop267 hDrop270 hDrop281 hDrop282
    hPush257 hFrom261 hSkip263 hBytes290 hVarint291 hChainParams294 hEpochDir299
    hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
    hMerge307 hMerge308 hMerge309 hMerge310

/-! ## 3. Pre-Discharged Corollaries (Discharging All Drops + S4 Callees from `W, hA`) -/

/-- Pre-discharged `V1State::merge` (`Block 298`) contract requiring only the `11` chunked-state `merge` hypotheses (`Blocks 300..310`). -/
theorem cliV1StateMerge_of_chunked_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim)) :=
  cliV1StateMerge_cl mmpl gh W hA hExt
    (cliDrop_267_cl mmpl gh W hA hExt) (cliDrop_281_cl mmpl gh W hA hExt) (cliDrop_282_cl mmpl gh W hA hExt)
    (cliPushMerge_257_cl mmpl gh W hA hExt) (cliFrom_261_cl mmpl gh W hA hExt)
    (cliSkip_263_cl mmpl gh W hA hExt) (cliVarint_291_cl mmpl gh W hA hExt)
    hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
    hMerge307 hMerge308 hMerge309 hMerge310

/-- Pre-discharged `spqr::decode_state` (`Block 325`) contract requiring only `hBytes290` and the
`11` chunked-state `merge` hypotheses (`Blocks 300..310`). -/
theorem cliSpqrDecodeState_of_chunked_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecX canonicalV1InnerHeap A lim)) :=
  cliSpqrDecodeState_cl mmpl gh W hA hExt
    (cliDrop_267_cl mmpl gh W hA hExt) (cliDrop_270_cl mmpl gh W hA hExt)
    (cliDrop_281_cl mmpl gh W hA hExt) (cliDrop_282_cl mmpl gh W hA hExt)
    (cliPushMerge_257_cl mmpl gh W hA hExt) (cliFrom_261_cl mmpl gh W hA hExt)
    (cliSkip_263_cl mmpl gh W hA hExt)
    hBytes290 (cliVarint_291_cl mmpl gh W hA hExt)
    (cliChainParams_294_cl mmpl gh W hA hExt) (cliEpochDir_299_cl mmpl gh W hA hExt)
    hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
    hMerge307 hMerge308 hMerge309 hMerge310

/-- Pre-discharged `spqrSendPlacedProg ext` `decodeState_ok` contract requiring only `hBytes290`
and the `11` chunked-state `merge` hypotheses (`Blocks 300..310`). -/
theorem cliSpqrSend_decodeState_of_chunked_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpec canonicalV1InnerHeap A lim)) :=
  ls_subroutine_ok_of_blockProgram_cro
    (cliSpqrDecodeState_of_chunked_cl mmpl gh W hA hExt hBytes290
      hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
      hMerge307 hMerge308 hMerge309 hMerge310)

/-- Pre-discharged `spqrRecvPlacedProg ext` `decodeState_ok` contract requiring only `hBytes290`
and the `11` chunked-state `merge` hypotheses (`Blocks 300..310`). -/
theorem cliSpqrDecodeState_recv_of_chunked_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.decodeStatePlacedSpecX
          canonicalV1InnerHeap A lim)) :=
  cliSpqrDecodeState_recv_ok mmpl gh W hA hExt
    (cliDrop_267_cl mmpl gh W hA hExt) (cliDrop_270_cl mmpl gh W hA hExt)
    (cliDrop_281_cl mmpl gh W hA hExt) (cliDrop_282_cl mmpl gh W hA hExt)
    (cliPushMerge_257_cl mmpl gh W hA hExt) (cliFrom_261_cl mmpl gh W hA hExt)
    (cliSkip_263_cl mmpl gh W hA hExt)
    hBytes290 (cliVarint_291_cl mmpl gh W hA hExt)
    (cliChainParams_294_cl mmpl gh W hA hExt) (cliEpochDir_299_cl mmpl gh W hA hExt)
    hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
    hMerge307 hMerge308 hMerge309 hMerge310

/-- Pre-discharged `spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))`
`decodeState_ok` contract requiring only `hBytes290` and the `11` chunked-state `merge`
hypotheses (`Blocks 300..310`). -/
theorem cliSpqrDecodeState_recv_trTrap_of_chunked_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim))) :
    subroutine_ok (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.decodeStatePlacedSpecX
          canonicalV1InnerHeap A lim)) :=
  cliSpqrDecodeState_recv_of_chunked_ok mmpl gh W hA
    (fun sym hne => by
      have hbeq : (sym == lsRngFillSym) = false := beq_false_of_ne hne
      simp [trTrapExternsPlaced, ProofLib.Variant.trapAt, hbeq])
    hBytes290
    hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
    hMerge307 hMerge308 hMerge309 hMerge310

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudget
