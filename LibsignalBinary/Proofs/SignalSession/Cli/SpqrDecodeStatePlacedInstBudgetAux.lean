/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.DecodeErrorPushMergePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3ClPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget

/-!
# Auxiliary Extern, Drop, & Protobuf Callee Discharges for `decode_state`

Discharges extern hooks (`__rust_dealloc`, `memcpy`, `session_memcpy`), `grow_one` (Block 356),
protobuf drop callees (Blocks 267, 270, 271, 281..286), and protobuf utility/merge callees
(Blocks 257, 261, 263, 290, 291, 294, 299) with their allocation-envelope bridges under
`CliGhostAllocHooks M A lim gh`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement
   blkPC_261 blkPC_263 blkPC_290 blkPC_291 blkPC_356
   blkPl_261 blkPl_263 blkPl_290 blkPl_291 blkPl_356
   extract_withLsCodeLoaded libsignalMutatedBlocks libsignalSessionLib
   lsHandleErrorSym ls_blockPlacement_base ls_subroutine_ok_of_block lsmpl lsρ
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec (skipField)
open CryptoVerification.LibsignalSpqrV1 (ChainParamsPB EpochDirectionPB)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.LibsignalTripleRatchet
  (keys_ls_subroutine_ok_of_block_cro sessionMemcpySpec withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost (SkipFieldGhost)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_panic_handle_error)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChainParamsMergeGhost EpochDirectionMergeGhost
   blkPC_294 blkPC_299 blkPl_294 blkPl_299 codecWireTypeToProto)
open CryptoVerification.SpqrV1.Top.Recv (spqrRecvPlacedProg)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorPushEnv decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (skipField3BudgetSpec skipField3EventsCore)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliExternsPlaced_memcpy_budget_sat cliExternsPlaced_noAllocShim_budget_sat
   cliExternsPlaced_realloc_budget_sat cliExternsPlaced_sessionMemcpyRegion_budget_sat
   cliExternsPlaced_sessionMemcpy_budget_sat cliExternsPlaced_shim_budget_sat)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
  (growOneStrideFullSpec grow_one_chain_epoch_full_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget
  (dropProtoChunkedCt1ReceivedSpec dropProtoChunkedEkSentCt1ReceivedSpec
   dropProtoChunkedHeaderReceivedSpec dropProtoChunkedHeaderSentSpec
   dropProtoChunkedNoHeaderReceivedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlacedBudget
  (drop_proto_chunked_ct1_received_cl_blockProgram
   drop_proto_chunked_ek_sent_ct1_received_cl_blockProgram
   drop_proto_chunked_header_received_cl_blockProgram
   drop_proto_chunked_header_sent_cl_blockProgram
   drop_proto_chunked_no_header_received_cl_blockProgram
   drop_proto_unchunked_ct1_sent_ek_received_cl_blockProgram)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
  (dropOptProtoInnerStatePlacedSpec dropProtoPqRatchetStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlacedBudget
  (drop_opt_proto_inner_state_cl_blockProgram drop_opt_proto_inner_state_cl_on
   drop_proto_pq_ratchet_state_cl_blockProgram drop_proto_pq_ratchet_state_cl_on)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (dropProtoUnchunkedCt1SentEkReceivedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofClPlacedBudget (bytes_merge_3_cl_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget
  (ChainParamsErrEnv chainParamsMerge_cl_placed_ok_of_contracts
   subroutine_ok_withLsCodeLoaded_chainParamsMergeOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (DecodeErrorPushMergeEnv decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.DecodeErrorPushMergePlacedBudget
  (decode_error_push_merge_at_block_withPanics_cl decode_error_push_merge_placed_ok
   hookSat_noAllocShimBudget_of_withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudget
  (epochDirectionMerge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux
  (EpochDirectionLoopEnv EpochDirectionOkEnv subroutine_ok_withLsCodeRoLoaded_epochDirectionMergeOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux
  (drop_glue_proto_poly_encoder_cl_blockProgram ls_to_blockProgram)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2ClPlacedBudget (decodeVarint2_cl_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3ClPlacedBudget (skipField3_cl_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (SkipFieldEnv skipFieldEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (bytesMergeEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget (decode_error_from_placed_ok)

/-!
## 1. Extern Hooks (`__rust_dealloc`, `memcpy`, `session_memcpy`) & `grow_one` (`Block 356`)
-/

private theorem hookSat_of_hExt {α : Type} {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    {W : CliHooks} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {sym : String} {spec : Spec α}
    (hsat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym spec)
    (hne : sym ≠ "libsignal_session_rng_fill" := by decide) :
    HookSat H sym spec :=
  hookSat_of_eq (hExt sym hne) hsat

private theorem hExt_withPanics {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := fun sym hne => by
  rw [← withPanics_cliGhostExterns mmpl gh W]
  simp only [Rust.withPanics, hExt sym hne]

theorem cliDeallocBudget_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim) :=
  spqr_hook_ok_of_mem
    (hookSat_of_hExt hExt (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))
    (by decide) hi hunmut

theorem cliLibcMemcpyBudget_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg prog i H] (stk : Nat := 0)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ "memcpy") (withVmPreserved (libcMemcpySpec stk)) :=
  spqr_hook_ok_of_mem
    (hookSat_of_hExt hExt (cliExternsPlaced_memcpy_budget_sat mmpl gh W hA stk))
    (by decide) hi hunmut

theorem cliSessionMemcpyBudget_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg prog i H] (stk : Nat := 0)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ "memcpy") (withVmPreserved (sessionMemcpySpec stk)) :=
  spqr_hook_ok_of_mem
    (hookSat_of_hExt hExt (cliExternsPlaced_sessionMemcpy_budget_sat mmpl gh W hA stk))
    (by decide) hi hunmut

theorem cliGrowOne_356_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 356 (Rust.withPanics ext))
      (lsmpl.base 356)
      (withLsCodeLoaded lsmpl (growOneStrideFullSpec M A lim 112 8)) := by
  have h := grow_one_chain_epoch_full_placed_ok (H := Rust.withPanics ext)
    ((hExt_withPanics hExt lsHandleErrorSym (by decide)).trans
      (cliGhostExterns_panic_handle_error mmpl gh W))
    (hookSat_of_hExt (hExt_withPanics hExt)
      (hookSat_noAllocShimBudget_of_withVmPreserved
        (cliExternsPlaced_noAllocShim_budget_sat mmpl gh W hA.shim_eq)))
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_realloc_budget_sat mmpl gh W hA))
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (blkPC_356).rebase (blkPl_356).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 356)] at h
  exact h

/-! ## 2. Protobuf `Drop` Wrappers (`Blocks 267, 270, 271, 281, 282, 283, 284, 285, 286`) -/

theorem cliDrop_267_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267)
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)) :=
  drop_opt_proto_inner_state_cl_blockProgram
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))

theorem cliDrop_270_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270)
      (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)) :=
  drop_proto_pq_ratchet_state_cl_blockProgram
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))

theorem cliDrop_271_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 271 (Rust.withPanics ext))
      (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)) :=
  drop_glue_proto_poly_encoder_cl_blockProgram
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))

theorem cliDrop_281_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281)
      (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)) :=
  drop_proto_chunked_header_sent_cl_blockProgram
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))

theorem cliDrop_282_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282)
      (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)) :=
  drop_proto_chunked_ct1_received_cl_blockProgram
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))

theorem cliDrop_283_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 283 (Rust.withPanics ext))
      (lsmpl.base 283)
      (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderReceivedSpec M A lim)) :=
  drop_proto_chunked_header_received_cl_blockProgram
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))

theorem cliDrop_284_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 284 (Rust.withPanics ext))
      (lsmpl.base 284)
      (withLsCodeLoaded lsmpl (dropProtoChunkedNoHeaderReceivedSpec M A lim)) :=
  drop_proto_chunked_no_header_received_cl_blockProgram
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))

theorem cliDrop_285_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 285 (Rust.withPanics ext))
      (lsmpl.base 285)
      (withLsCodeLoaded lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)) :=
  drop_proto_chunked_ek_sent_ct1_received_cl_blockProgram
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))

theorem cliDrop_286_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 286 (Rust.withPanics ext))
      (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
  drop_proto_unchunked_ct1_sent_ek_received_cl_blockProgram
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))

/-- `dropOptProtoInnerState_ok` field of `SpqrRecvPlacedContracts` (`Block 267`) on
`spqrRecvPlacedProg ext`. -/
theorem cliSpqrRecv_dropOptProtoInnerState_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 267)
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)) :=
  drop_opt_proto_inner_state_cl_on
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))

/-- `dropPqRatchetState_ok` field of `SpqrRecvPlacedContracts` (`Block 270`) on
`spqrRecvPlacedProg ext`. -/
theorem cliSpqrRecv_dropPqRatchetState_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 270)
      (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)) :=
  drop_proto_pq_ratchet_state_cl_on
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))

/-!
## 3. Envelope & Specification Bridges + Protobuf Utility & Merge Callees (`257, 261, 263, 290, 291, 294, 299`)
-/

/-- Containment `DecodeErrorPushMergeEnv n evs → DecodeErrorPushEnv n evs` for `n < 2 ^ 32`. -/
theorem decodeErrorPushEnv_of_merge {n : Nat} {evs : List AllocEvent}
    (hn : n < 2 ^ 32) (h : DecodeErrorPushMergeEnv n evs) :
    DecodeErrorPushEnv n evs := by
  rcases h with rfl | ⟨hn0, heq⟩ | ⟨hpos, heq⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨hn0, 4, by decide, by decide, heq⟩)
  · exact Or.inr (Or.inr ⟨n, max (2 * n) 4, hpos, Nat.le_refl n, by omega, by omega, heq⟩)

/-- Weaken `decodeErrorPushMergeBudgetSpec M A lim` (`Block 257` merge envelope) to
`SpecBudget.decodeErrorPushBudgetSpec M A lim` under `withLsCodeLoaded`. -/
theorem decodeErrorPush_of_merge [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨d, e, n, st⟩ R s0 hpc hrun hp halign => ?_
  obtain ⟨hcl, hp_body⟩ := extract_withLsCodeLoaded hp
  dsimp only [decodeErrorPushBudgetSpec] at hp_body
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp_body
  have hn : n < 2 ^ 32 := hp_body.1.2.1
  have hp' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)).pre (d, e, n, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded, decodeErrorPushMergeBudgetSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hp_body.1.1, hn, hp_body.1.2.2.mono fun _ hm => decodeErrorPushEnv_of_merge hn hm⟩,
        hp_body.2⟩⟩
  exact (h.to_outcome (d, e, n, st) R s0 hpc hrun hp' halign).mono_outcome fun sf hq => by
    rcases hq with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
    · left
      refine ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, decodeErrorPushMergeBudgetSpec, decodeErrorPushBudgetSpec] at hpost ⊢
      exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_mono fun evs =>
          Entails.pure_left fun h1 =>
            Entails.pure_right (decodeErrorPushEnv_of_merge hn h1) (Entails.of_eq rfl))))))) hpost
    · dsimp only [withLsCodeLoaded, decodeErrorPushMergeBudgetSpec] at hpost
      exact (not_satisfies_false_sepConj hpost).elim
    · dsimp only [withLsCodeLoaded, decodeErrorPushMergeBudgetSpec] at hpost
      exact (not_satisfies_false_sepConj hpost).elim
    · exact (not_satisfies_false_sepConj hpost).elim

/-- Unconditional `Block 257` `<DecodeError>::push` merge-envelope contract under `[CliSpqrExt W ext]`. -/
theorem cliPushMerge_257_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  ls_to_blockProgram (decode_error_push_merge_placed_ok (H := Rust.withPanics ext)
    ((hExt_withPanics hExt lsHandleErrorSym (by decide)).trans
      (cliGhostExterns_panic_handle_error mmpl gh W))
    (hookSat_of_hExt (hExt_withPanics hExt)
      (cliExternsPlaced_noAllocShim_budget_sat mmpl gh W hA.shim_eq))
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_realloc_budget_sat mmpl gh W hA)))

/-- Unconditional `Block 257` `<DecodeError>::push` `SpecBudget` contract under `[CliSpqrExt W ext]`. -/
theorem cliPush_257_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)) :=
  decodeErrorPush_of_merge (cliPushMerge_257_cl mmpl gh W hA hExt)

/-- Unconditional `Block 261` `<DecodeError>::from` contract under `[CliSpqrExt W ext]`. -/
theorem cliFrom_261_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)) := by
  have h := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (decode_error_from_placed_ok (H := Rust.withPanics ext)
      (hookSat_of_hExt (hExt_withPanics hExt)
        (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
      (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA)))
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (blkPC_261).rebase (blkPl_261).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 261)] at h
  exact h

/-- Unconditional `Block 291` `decode_varint [local#2]` contract under `[CliSpqrExt W ext]`. -/
theorem cliVarint_291_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)) := by
  have h := decodeVarint2_cl_placed_ok (H := Rust.withPanics ext)
    (hookSat_of_hExt (hExt_withPanics hExt)
      (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (blkPC_291).rebase (blkPl_291).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 291)] at h
  exact h

/-- Extensional equality between `SkipField3Budget.SkipField3Env` and
`SignedDepsBudget.SkipField3Env`. -/
theorem skipField3Env_eq (x : SkipFieldGhost) :
    LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget.SkipField3Env x =
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SkipField3Env x := by
  funext evs
  dsimp only [LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget.SkipField3Env,
    SkipFieldEnv, skipFieldEventsCore,
    LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SkipField3Env,
    skipField3EventsCore]
  cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs <;> rfl

/-- Bridge `SkipField3Budget.skipField3Spec A lim` to `SignedDepsBudget.skipField3BudgetSpec M A lim`
under `withLsCodeLoaded`. -/
theorem skipField3Budget_of_prost [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipField3Spec A lim))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipField3BudgetSpec M A lim)) := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ R s0 hp => ?_)
    (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · dsimp only [withLsCodeLoaded, skipField3Spec, skipField3BudgetSpec] at hp ⊢
    rwa [skipField3Env_eq x]
  · dsimp only [withLsCodeLoaded, skipField3Spec, skipField3BudgetSpec] at hq ⊢
    rwa [← skipField3Env_eq x]

/-- Unconditional `Block 263` `skip_field [local#3]` (`SkipField3Budget.skipField3Spec`) contract
under `[CliSpqrExt W ext]`. -/
theorem cliSkip_263_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)) := by
  have h := skipField3_cl_placed_ok (H := Rust.withPanics ext)
    (hookSat_of_hExt (hExt_withPanics hExt)
      (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (blkPC_263).rebase (blkPl_263).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 263)] at h
  exact h

/-- Unconditional `Block 263` `skip_field [local#3]` (`SignedDepsBudget.skipField3BudgetSpec`)
contract under `[CliSpqrExt W ext]`. -/
theorem cliSkipBudget_263_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3BudgetSpec M A lim)) :=
  skipField3Budget_of_prost (cliSkip_263_cl mmpl gh W hA hExt)

/-- Unconditional `Block 290` `bytes::merge [local#3]` contract under `[CliSpqrExt W ext]`. -/
theorem cliBytes_290_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec A lim)) := by
  have h := bytes_merge_3_cl_placed_ok (H := Rust.withPanics ext)
    (hookSat_of_hExt (hExt_withPanics hExt)
      (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_realloc_budget_sat mmpl gh W hA))
    (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))
    (hookSat_of_hExt (hExt_withPanics hExt)
      (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hA))
    ((hExt_withPanics hExt lsHandleErrorSym (by decide)).trans
      (cliGhostExterns_panic_handle_error mmpl gh W))
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (blkPC_290).rebase (blkPl_290).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 290)] at h
  exact h

/-- Containment `ChainParamsErrEnv evs → DecodeStateLoopEnv 8 maxLen 0 evs`. -/
theorem chainParamsErrEnv_to_decodeState {maxLen : Nat} {evs : List AllocEvent}
    (h : ChainParamsErrEnv evs) :
    DecodeStateLoopEnv 8 maxLen 0 evs := by
  cases h with
  | fromOnly =>
    exact (DecodeStateLoopEnv.single (fuel := 0) .fromErr).mono_fuel (by decide)
  | fromPush hp =>
    exact (DecodeStateLoopEnv.step .fromErr
      (DecodeStateLoopEnv.single (fuel := 0) (.pushErr (by decide) hp))).mono_fuel (by decide)

/-- Containment `ChainParamsBudget.ChainParamsMergeEnv x evs →
DecodeState.SpecsBudget.ChainParamsMergeEnv ⟨...⟩ evs`. -/
theorem chainParamsMergeEnv_to_decodeState {x : ChainParamsMergeGhost} {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget.ChainParamsMergeEnv x evs) :
    LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.ChainParamsMergeEnv
      ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩ evs := by
  dsimp only [LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.ChainParamsMergeEnv]
  cases h with
  | ok => exact .nil
  | err he => exact (chainParamsErrEnv_to_decodeState he).mono_fuel (by omega)

/-- Containment `ChainParamsBudget.ChainParamsMergePostEnv x evs →
DecodeState.SpecsBudget.ChainParamsMergePostEnv ⟨...⟩ evs`. -/
theorem chainParamsMergePostEnv_to_decodeState {x : ChainParamsMergeGhost} {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget.ChainParamsMergePostEnv x evs) :
    LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.ChainParamsMergePostEnv
      ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩ evs := by
  dsimp only [LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget.ChainParamsMergePostEnv,
    LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.ChainParamsMergePostEnv] at h ⊢
  cases hres : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some p =>
    rw [hres] at h
    subst h
    exact .nil
  | none =>
    rw [hres] at h
    exact (chainParamsErrEnv_to_decodeState h).mono_fuel (by omega)

/-- Bridge `ChainParamsBudget.chainParamsMergeSpec A lim` to
`DecodeState.SpecsBudget.chainParamsMergeSpec A lim` under `withLsCodeLoaded`. -/
theorem chainParamsMerge_decodeState_of_prost [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (hok : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget.chainParamsMergeSpec A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.chainParamsMergeSpec A lim)) := by
  have hok' := subroutine_ok_withLsCodeLoaded_chainParamsMergeOfEnv
    (Pre₂ := fun x' evs =>
      LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.ChainParamsMergeEnv
        ⟨x'.wt, x'.msgPtr, x'.msg, x'.bufRef, x'.slot, x'.ptr, x'.bs⟩ evs)
    (Post₂ := fun x' evs =>
      LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.ChainParamsMergePostEnv
        ⟨x'.wt, x'.msgPtr, x'.msg, x'.bufRef, x'.slot, x'.ptr, x'.bs⟩ evs)
    (fun _ _ => chainParamsMergeEnv_to_decodeState)
    (fun _ _ => chainParamsMergePostEnv_to_decodeState)
    hok
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre halign => ?_
  let x' : ChainParamsMergeGhost := ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
  exact (hok'.to_outcome (x', st) R s0 hpc hrun hpre halign).mono_outcome fun _ hout => hout

/-- Unconditional `Block 294` `ChainParams::merge` (`ChainParamsBudget.chainParamsMergeSpec`)
contract under `[CliSpqrExt W ext]`. -/
theorem cliChainParams_294_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget.chainParamsMergeSpec A lim)) := by
  have hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)) := by
    have h0 := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
      (decode_error_from_placed_ok (H := Rust.withPanics ext)
        (hookSat_of_hExt (hExt_withPanics hExt)
          (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
        (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA)))
    rwa [ls_blockPlacement_base (i := 261)] at h0
  have hVarint : subroutine_ok ((blkPC_291).rebase (blkPl_291).base (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)) := by
    have h0 := decodeVarint2_cl_placed_ok (H := Rust.withPanics ext)
      (hookSat_of_hExt (hExt_withPanics hExt)
        (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
      (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    rwa [ls_blockPlacement_base (i := 291)] at h0
  have hSkip : subroutine_ok ((blkPC_263).rebase (blkPl_263).base (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)) := by
    have h0 := skipField3_cl_placed_ok (H := Rust.withPanics ext)
      (hookSat_of_hExt (hExt_withPanics hExt)
        (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
      (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    rwa [ls_blockPlacement_base (i := 263)] at h0
  have hPush : subroutine_ok ((blkPC_294).rebase (blkPl_294).base (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)) :=
    decodeErrorPush_of_merge (decode_error_push_merge_at_block_withPanics_cl
      ((hExt lsHandleErrorSym (by decide)).trans
        (cliGhostExterns_panic_handle_error mmpl gh W))
      (hookSat_of_hExt hExt (cliExternsPlaced_noAllocShim_budget_sat mmpl gh W hA.shim_eq))
      (hookSat_of_hExt hExt (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
      (hookSat_of_hExt hExt (cliExternsPlaced_realloc_budget_sat mmpl gh W hA)))
  have h := chainParamsMerge_cl_placed_ok_of_contracts
    (ls_subroutine_ok_of_block hFrom)
    hPush
    (ls_subroutine_ok_of_block hVarint)
    (ls_subroutine_ok_of_block hSkip)
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (blkPC_294).rebase (blkPl_294).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 294)] at h
  exact h

/-- Containment `EpochDirectionLoopEnv rem evs → DecodeStateLoopEnv (4 * rem + 8) maxLen 0 evs`
for `rem ≤ maxLen`. -/
theorem epochDirectionLoopEnv_to_decodeState {rem maxLen : Nat} {evs : List AllocEvent}
    (hle : rem ≤ maxLen) (h : EpochDirectionLoopEnv rem evs) :
    DecodeStateLoopEnv (4 * rem + 8) maxLen 0 evs := by
  induction h with
  | nil => exact .nil
  | errFrom =>
    exact (DecodeStateLoopEnv.single (fuel := 0) .fromErr).mono_fuel (by omega)
  | errFromPush hp =>
    exact (DecodeStateLoopEnv.step .fromErr
      (DecodeStateLoopEnv.single (fuel := 0) (.pushErr (by decide) hp))).mono_fuel (by omega)
  | @stepBytes rem wt valCap bs evs₁ evs₂ hbs hcap hbm _ ih =>
    have hbs_max : bs.length ≤ maxLen := Nat.le_trans hbs (by omega)
    have hcap_max : valCap.toNat ≤ maxLen := Nat.le_trans hcap hbs_max
    have hbm_eq : evs₁ = bytesMergeEventsCore wt valCap bs := hbm
    subst hbm_eq
    exact (DecodeStateLoopEnv.step (.bytesMerge wt valCap bs hbs_max hcap_max)
      (ih (by omega))).mono_fuel (by omega)

/-- Containment `EpochDirectionOkEnv rem consumed evs →
DecodeStateLoopEnv (4 * consumed) maxLen 0 evs` for `rem ≤ maxLen`. -/
theorem epochDirectionOkEnv_to_decodeState {rem consumed maxLen : Nat} {evs : List AllocEvent}
    (hle : rem ≤ maxLen) (h : EpochDirectionOkEnv rem consumed evs) :
    DecodeStateLoopEnv (4 * consumed) maxLen 0 evs := by
  induction h with
  | nil => exact .nil
  | @stepBytes rem consumed wt valCap bs evs₁ evs₂ hbs hcap hbm _ ih =>
    have hbs_max : bs.length ≤ maxLen := Nat.le_trans hbs (by omega)
    have hcap_max : valCap.toNat ≤ maxLen := Nat.le_trans hcap hbs_max
    have hbm_eq : evs₁ = bytesMergeEventsCore wt valCap bs := hbm
    subst hbm_eq
    exact (DecodeStateLoopEnv.step (.bytesMerge wt valCap bs hbs_max hcap_max)
      (ih (by omega))).mono_fuel (by omega)

/-- Containment `EpochDirectionBudgetAux.EpochDirectionMergeEnv x evs →
DecodeState.SpecsBudget.EpochDirectionMergeEnv ⟨...⟩ evs`. -/
theorem epochDirectionMergeEnv_to_decodeState {x : EpochDirectionMergeGhost} {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.EpochDirectionMergeEnv x evs) :
    LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.EpochDirectionMergeEnv
      ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩ evs :=
  epochDirectionLoopEnv_to_decodeState (Nat.le_refl _) h

/-- Containment `EpochDirectionBudgetAux.EpochDirectionMergePostEnv x evs →
DecodeState.SpecsBudget.EpochDirectionMergePostEnv ⟨...⟩ evs`. -/
theorem epochDirectionMergePostEnv_to_decodeState {x : EpochDirectionMergeGhost}
    {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.EpochDirectionMergePostEnv x evs) :
    LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.EpochDirectionMergePostEnv
      ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩ evs := by
  dsimp only [LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.EpochDirectionMergePostEnv,
    LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.EpochDirectionMergePostEnv] at h ⊢
  cases hres : (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
  | some p =>
    rw [hres] at h
    exact epochDirectionOkEnv_to_decodeState (Nat.le_refl _) h
  | none =>
    rw [hres] at h
    exact epochDirectionLoopEnv_to_decodeState (Nat.le_refl _) h

/-- Bridge `EpochDirectionBudgetAux.epochDirectionMergeSpec A lim` to
`DecodeState.SpecsBudget.epochDirectionMergeSpec A lim` under `withLsCodeRoLoaded`. -/
theorem epochDirectionMerge_decodeState_of_prost [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (hok : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.epochDirectionMergeSpec A lim))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.epochDirectionMergeSpec A lim)) := by
  have hok' := subroutine_ok_withLsCodeRoLoaded_epochDirectionMergeOfEnv
    (Pre₂ := fun x' evs =>
      LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.EpochDirectionMergeEnv
        ⟨x'.wt, x'.msgPtr, x'.msg, x'.bufRef, x'.slot, x'.ptr, x'.bs⟩ evs)
    (Post₂ := fun x' evs =>
      LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.EpochDirectionMergePostEnv
        ⟨x'.wt, x'.msgPtr, x'.msg, x'.bufRef, x'.slot, x'.ptr, x'.bs⟩ evs)
    (fun _ _ => epochDirectionMergeEnv_to_decodeState)
    (fun _ _ => epochDirectionMergePostEnv_to_decodeState)
    hok
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre halign => ?_
  let x' : EpochDirectionMergeGhost := ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
  exact (hok'.to_outcome (x', st) R s0 hpc hrun hpre halign).mono_outcome fun _ hout => hout

/-- Unconditional `Block 299` `EpochDirection::merge`
(`EpochDirectionBudgetAux.epochDirectionMergeSpec`) contract under `[CliSpqrExt W ext]`. -/
theorem cliEpochDir_299_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.epochDirectionMergeSpec A lim)) := by
  have hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)) := by
    have h0 := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
      (decode_error_from_placed_ok (H := Rust.withPanics ext)
        (hookSat_of_hExt (hExt_withPanics hExt)
          (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
        (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA)))
    rwa [ls_blockPlacement_base (i := 261)] at h0
  have hVarint : subroutine_ok ((blkPC_291).rebase (blkPl_291).base (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)) := by
    have h0 := decodeVarint2_cl_placed_ok (H := Rust.withPanics ext)
      (hookSat_of_hExt (hExt_withPanics hExt)
        (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
      (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    rwa [ls_blockPlacement_base (i := 291)] at h0
  have hSkip : subroutine_ok ((blkPC_263).rebase (blkPl_263).base (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)) := by
    have h0 := skipField3_cl_placed_ok (H := Rust.withPanics ext)
      (hookSat_of_hExt (hExt_withPanics hExt)
        (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
      (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    rwa [ls_blockPlacement_base (i := 263)] at h0
  have hBytes : subroutine_ok ((blkPC_290).rebase (blkPl_290).base (Rust.withPanics ext))
      (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec A lim)) := by
    have h0 := bytes_merge_3_cl_placed_ok (H := Rust.withPanics ext)
      (hookSat_of_hExt (hExt_withPanics hExt)
        (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
      (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
      (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_realloc_budget_sat mmpl gh W hA))
      (hookSat_of_hExt (hExt_withPanics hExt) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))
      (hookSat_of_hExt (hExt_withPanics hExt)
        (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hA))
      ((hExt_withPanics hExt lsHandleErrorSym (by decide)).trans
        (cliGhostExterns_panic_handle_error mmpl gh W))
    rwa [ls_blockPlacement_base (i := 290)] at h0
  have hPush : subroutine_ok ((blkPC_299).rebase (blkPl_299).base (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)) :=
    decodeErrorPush_of_merge (decode_error_push_merge_at_block_withPanics_cl
      ((hExt lsHandleErrorSym (by decide)).trans
        (cliGhostExterns_panic_handle_error mmpl gh W))
      (hookSat_of_hExt hExt (cliExternsPlaced_noAllocShim_budget_sat mmpl gh W hA.shim_eq))
      (hookSat_of_hExt hExt (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
      (hookSat_of_hExt hExt (cliExternsPlaced_realloc_budget_sat mmpl gh W hA)))
  have h := epochDirectionMerge_cl_placed_ok_of_contracts
    (ls_subroutine_ok_of_block hFrom)
    hPush
    (ls_subroutine_ok_of_block hVarint)
    (ls_subroutine_ok_of_block hSkip)
    (keys_ls_subroutine_ok_of_block_cro hBytes)
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (blkPC_299).rebase (blkPl_299).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 299)] at h
  exact h

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
