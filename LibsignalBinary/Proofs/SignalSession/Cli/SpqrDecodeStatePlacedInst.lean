/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParams
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProofClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Drop.DropCodeSym
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.UnchunkedFromPbClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.RecvPlacedCodeSym

/-!
# Placed `V1State::merge` & `spqr::decode_state` Instantiations

Discharges extern hooks (`__rust_dealloc`, `memcpy`, `session_memcpy`), `grow_one` (Block 356),
and single-block leaf drops (Blocks 271, 283..286) under `[CliSpqrExt W ext]`, and wires
`V1State::merge` (Block 298) into `spqr::decode_state` (Block 325) for `spqr::send::<Coins>` and
`spqr::recv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
open CryptoVerification.SpqrV1.Top.DecodeState (canonicalV1InnerHeap decodeStatePlacedSpecX spqr_decode_state_cl)
open CryptoVerification.SpqrV1.Top.Recv (spqrRecvPlacedProg)
open CryptoVerification.CodeLayout

/-!
## 1. Extern `memcpy`, `grow_one` (`Block 356`), and Leaf `Drop` Wrappers (`Blocks 271, 283..286`)
-/

theorem cliLibcMemcpy_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H] (stk : Nat := 0)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ "memcpy") (libcMemcpySpec stk) :=
  spqr_hook_ok_of_mem
    (cliSpqrExt_memcpy_sat W stk (ext := H))
    (by decide) hi hunmut

theorem cliGrowOne_356_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 356 (Rust.withPanics ext))
      (lsmpl.base 356)
      (withLsCodeLoaded lsmpl (growOneStrideFullSpec E2E.HooksE.A0 112 8)) := by
  have h := cliGrowOneChainEpochFull_placed_ok W (H := Rust.withPanics ext)
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (CryptoVerification.blkPC_356).rebase (CryptoVerification.blkPl_356).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 356)] at h
  exact h

theorem cliDrop_271_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 271 (Rust.withPanics ext))
      (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoPolyEncoderSpec E2E.HooksE.A0)) :=
  CryptoVerification.SpqrV1.States.Recv.drop_glue_proto_poly_encoder_cl_blockProgram
    (cliSpqrExt_dealloc_sat W (ext := Rust.withPanics ext))

theorem cliDrop_283_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 283 (Rust.withPanics ext))
      (lsmpl.base 283)
      (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoChunkedHeaderReceivedSpec E2E.HooksE.A0)) := by
  have h := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_header_received_placed_ok
      (H := Rust.withPanics ext) (cliDealloc_at_block W))
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (CryptoVerification.blkPC_283).rebase (CryptoVerification.blkPl_283).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 283)] at h
  exact h

theorem cliDrop_284_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 284 (Rust.withPanics ext))
      (lsmpl.base 284)
      (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoChunkedNoHeaderReceivedSpec E2E.HooksE.A0)) := by
  have h := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_no_header_received_placed_ok
      (H := Rust.withPanics ext) (cliDealloc_at_block W))
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (CryptoVerification.blkPC_284).rebase (CryptoVerification.blkPl_284).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 284)] at h
  exact h

theorem cliDrop_285_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 285 (Rust.withPanics ext))
      (lsmpl.base 285)
      (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoChunkedEkSentCt1ReceivedSpec E2E.HooksE.A0)) := by
  have h := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_ek_sent_ct1_received_placed_ok
      (H := Rust.withPanics ext) (cliDealloc_at_block W))
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (CryptoVerification.blkPC_285).rebase (CryptoVerification.blkPl_285).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 285)] at h
  exact h

theorem cliDrop_286_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 286 (Rust.withPanics ext))
      (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoUnchunkedCt1SentEkReceivedSpec E2E.HooksE.A0)) :=
  LibsignalBinary.Proofs.SpqrV1.States.FromPb.drop_proto_unchunked_ct1_sent_ek_received_cl_blockProgram
    (cliSpqrExt_dealloc_sat W (ext := Rust.withPanics ext))

private theorem chainParamsMerge_decodeState_of_prost [LibsignalPlacement]
    {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    (hok : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeSpec A))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Top.DecodeState.chainParamsMergeSpec A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let x' : CryptoVerification.SpqrV1.Prost.MessageMerge.ChainParamsMergeGhost :=
    ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
  exact (hok.to_outcome x' R s0 hpc hrun hpre halign).mono_outcome fun _ hout => hout

private theorem epochDirectionMerge_decodeState_of_prost [LibsignalPlacement]
    {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    (hok : subroutine_ok prog entry
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeSpec A))) :
    subroutine_ok prog entry
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.DecodeState.epochDirectionMergeSpec A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let x' : CryptoVerification.SpqrV1.Prost.MessageMerge.EpochDirectionMergeGhost :=
    ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
  exact (hok.to_outcome x' R s0 hpc hrun hpre halign).mono_outcome fun _ hout => hout

/-!
## 2. Own-Block Code-Loaded Theorems (`Block 298` `V1State::merge` & `Block 325` `spqr::decode_state`)
-/

/-- Own-block code-loaded `V1State::merge` (`Block 298`) contract under `[CliSpqrExt W ext]`. -/
theorem cliV1StateMerge_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec E2E.HooksE.A0)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoChunkedHeaderSentSpec E2E.HooksE.A0)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoChunkedCt1ReceivedSpec E2E.HooksE.A0)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec E2E.HooksE.A0)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec E2E.HooksE.A0)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec E2E.HooksE.A0)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec E2E.HooksE.A0)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec E2E.HooksE.A0)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec E2E.HooksE.A0)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec E2E.HooksE.A0)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec E2E.HooksE.A0)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec E2E.HooksE.A0)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec E2E.HooksE.A0)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec E2E.HooksE.A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec E2E.HooksE.A0)) :=
  v1State_merge_cl
    (cliDealloc_at_block W (i := 298))
    hFrom261 hPush257 hVarint291 hSkip263
    hDrop267 hDrop282 hDrop281
    (cliDrop_285_cl W) (cliDrop_284_cl W) (cliDrop_283_cl W) (cliDrop_286_cl W) (cliDrop_271_cl W)
    hMerge305 hMerge304 hMerge302 hMerge303 hMerge309 hMerge308 hMerge306
    hMerge300 hMerge310 hMerge307 hMerge301

/-- Own-block code-loaded `spqr::decode_state` (`Block 325`) contract under `[CliSpqrExt W ext]`. -/
theorem cliSpqrDecodeState_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec E2E.HooksE.A0)))
    (hDrop270 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec E2E.HooksE.A0)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoChunkedHeaderSentSpec E2E.HooksE.A0)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoChunkedCt1ReceivedSpec E2E.HooksE.A0)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec E2E.HooksE.A0)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec E2E.HooksE.A0)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec E2E.HooksE.A0)))
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec E2E.HooksE.A0)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec E2E.HooksE.A0)))
    (hChainParams294 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec E2E.HooksE.A0)))
    (hEpochDir299 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec E2E.HooksE.A0)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec E2E.HooksE.A0)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec E2E.HooksE.A0)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec E2E.HooksE.A0)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec E2E.HooksE.A0)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec E2E.HooksE.A0)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec E2E.HooksE.A0)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec E2E.HooksE.A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
      (lsmpl.base 325)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecX canonicalV1InnerHeap E2E.HooksE.A0)) :=
  spqr_decode_state_cl
    (cliDealloc_at_block W (i := 325))
    (fun stk => cliLibcMemcpy_at_block W stk (i := 325))
    (fun stk => cliSessionMemcpy_at_block W stk (i := 325))
    hFrom261 hPush257 hVarint291 hSkip263
    (chainParamsMerge_decodeState_of_prost hChainParams294)
    (cliGrowOne_356_cl W)
    hDrop267 hDrop270 hBytes290
    (epochDirectionMerge_decodeState_of_prost hEpochDir299)
    (cliV1StateMerge_cl W hDrop267 hDrop281 hDrop282 hPush257 hFrom261 hSkip263 hVarint291
      hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
      hMerge307 hMerge308 hMerge309 hMerge310)

/-! ## 3. for `spqr::send::<Coins>` (`Block 427`) and `spqr::recv` (`Block 329`) -/

/-- Exact `hDecodeState` hypothesis type of `cliSpqrSendCoins_placed_ok`
(`SpqrSendCoinsPlacedInst.lean`, `ext = RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`). -/
theorem cliSpqrDecodeState_sendCoins_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0))
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec E2E.HooksE.A0)))
    (hDrop270 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec E2E.HooksE.A0)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoChunkedHeaderSentSpec E2E.HooksE.A0)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoChunkedCt1ReceivedSpec E2E.HooksE.A0)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec E2E.HooksE.A0)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec E2E.HooksE.A0)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec E2E.HooksE.A0)))
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 290) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec E2E.HooksE.A0)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec E2E.HooksE.A0)))
    (hChainParams294 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec E2E.HooksE.A0)))
    (hEpochDir299 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 299) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec E2E.HooksE.A0)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 300) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec E2E.HooksE.A0)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 301) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec E2E.HooksE.A0)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 302) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec E2E.HooksE.A0)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 303) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 304) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec E2E.HooksE.A0)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 305) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec E2E.HooksE.A0)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 306) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 307) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec E2E.HooksE.A0)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 308) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 309) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 310) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec E2E.HooksE.A0))) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.DecodeState.decodeStatePlacedSpecX
          canonicalV1InnerHeap E2E.HooksE.A0)) := by
  have : CliSpqrExt W (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliSpqrExt_self mmpl gh W hG hMs hMc hHmac
  exact cliSpqrDecodeState_cl W
    hDrop267 hDrop270 hDrop281 hDrop282
    hPush257 hFrom261 hSkip263 hBytes290 hVarint291 hChainParams294 hEpochDir299
    hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
    hMerge307 hMerge308 hMerge309 hMerge310

/-- Exact `decodeState_ok` field type of `SpqrRecvPlacedContracts` with `H_inner = canonicalV1InnerHeap`, generic in `[CliSpqrExt W ext]`. -/
theorem cliSpqrDecodeState_recv_ok [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec E2E.HooksE.A0)))
    (hDrop270 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec E2E.HooksE.A0)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoChunkedHeaderSentSpec E2E.HooksE.A0)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoChunkedCt1ReceivedSpec E2E.HooksE.A0)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec E2E.HooksE.A0)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec E2E.HooksE.A0)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec E2E.HooksE.A0)))
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec E2E.HooksE.A0)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec E2E.HooksE.A0)))
    (hChainParams294 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec E2E.HooksE.A0)))
    (hEpochDir299 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec E2E.HooksE.A0)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec E2E.HooksE.A0)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec E2E.HooksE.A0)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec E2E.HooksE.A0)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec E2E.HooksE.A0)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec E2E.HooksE.A0)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec E2E.HooksE.A0)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec E2E.HooksE.A0))) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 325)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecX canonicalV1InnerHeap E2E.HooksE.A0)) :=
  @keys_ls_subroutine_ok_of_block_cro _ _ (spqrRecvPlacedProg ext)
    (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
    329 325 (Rust.withPanics ext) inferInstance
    ⟨rfl, IsLsBlockProg.externs_eq
      (prog := (CryptoVerification.SpqrV1.Top.DecodeState.Placed.blkPC_325).rebase
        (CryptoVerification.SpqrV1.Top.DecodeState.Placed.blkPl_325).base (fun _ => none))⟩
    (lsmpl.base 325) (decodeStatePlacedSpecX canonicalV1InnerHeap E2E.HooksE.A0)
    (cliSpqrDecodeState_cl W
      hDrop267 hDrop270 hDrop281 hDrop282
      hPush257 hFrom261 hSkip263 hBytes290 hVarint291 hChainParams294 hEpochDir299
      hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
      hMerge307 hMerge308 hMerge309 hMerge310)
    _ _ _ _ (by decide) (by decide) (by decide)

/-- specialized to `trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))` (`Block 329` CLI hook map). -/
theorem cliSpqrDecodeState_recv_trTrap_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0))
    (hDrop267 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec E2E.HooksE.A0)))
    (hDrop270 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec E2E.HooksE.A0)))
    (hDrop281 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoChunkedHeaderSentSpec E2E.HooksE.A0)))
    (hDrop282 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoChunkedCt1ReceivedSpec E2E.HooksE.A0)))
    (hPush257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec E2E.HooksE.A0)))
    (hFrom261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec E2E.HooksE.A0)))
    (hSkip263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec E2E.HooksE.A0)))
    (hBytes290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 290) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec E2E.HooksE.A0)))
    (hVarint291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec E2E.HooksE.A0)))
    (hChainParams294 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec E2E.HooksE.A0)))
    (hEpochDir299 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 299) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec E2E.HooksE.A0)))
    (hMerge300 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 300) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec E2E.HooksE.A0)))
    (hMerge301 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 301) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec E2E.HooksE.A0)))
    (hMerge302 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 302) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec E2E.HooksE.A0)))
    (hMerge303 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 303) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge304 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 304) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec E2E.HooksE.A0)))
    (hMerge305 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 305) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec E2E.HooksE.A0)))
    (hMerge306 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 306) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge307 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 307) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec E2E.HooksE.A0)))
    (hMerge308 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 308) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge309 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 309) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec E2E.HooksE.A0)))
    (hMerge310 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))))
      (lsmpl.base 310) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec E2E.HooksE.A0))) :
    subroutine_ok (spqrRecvPlacedProg (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecX canonicalV1InnerHeap E2E.HooksE.A0)) := by
  have : CliSpqrExt W (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
    cliSpqrExt_trTrap mmpl gh W hG hMs hMc hHmac
  exact cliSpqrDecodeState_recv_ok W
    hDrop267 hDrop270 hDrop281 hDrop282
    hPush257 hFrom261 hSkip263 hBytes290 hVarint291 hChainParams294 hEpochDir299
    hMerge300 hMerge301 hMerge302 hMerge303 hMerge304 hMerge305 hMerge306
    hMerge307 hMerge308 hMerge309 hMerge310

end CryptoVerification.SignalSession.Cli
