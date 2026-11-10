/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyDecoderBudget
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# Budget-Threaded Code-Loaded Drop Glue for `SpqrV1/States/Recv`

Budget-threaded `withLsCodeLoaded` `subroutine_ok` proofs (`FreeOnlyEvs`) for `drop_glue::<Ct2Sampled>`
(Block `274`), `HeaderSent` (Block `276`), and `EkSentCt1Received` (Block `278`), re-exporting leaf drop glue.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.SpqrV1.States.Recv (spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Drop (
  DropChunkedCt1ReceivedGhost DropChunkedCt2SampledGhost
  DropChunkedEkReceivedCt1SampledGhost DropChunkedEkSentCt1ReceivedGhost
  DropChunkedHeaderSentGhost DropGluePolyEncoderGhost Saved32x19Preserved
  chunkedCt1ReceivedAt chunkedCt1ReceivedSize
  chunkedCt2SampledAt chunkedCt2SampledSize
  chunkedEkReceivedCt1SampledAt chunkedEkReceivedCt1SampledSize
  chunkedEkSentCt1ReceivedAt chunkedEkSentCt1ReceivedSize
  chunkedHeaderSentAt chunkedHeaderSentSize
  chunked_104_400_join chunked_400_join chunked_880_join
  dropGluePoly16Stack dropStack32 dropStackPoly64
  fiveVec400HeadersAt fiveVec400HeadersAt_entails_memRegion_128
  fourVec104HeadersAt fourVec104HeadersAt_entails_memRegion_104
  fourVec400HeadersAt fourVec400HeadersAt_entails_memRegion_104
  polyDecoderAt_entails_vecs_tail polyEncoderAt_entails_tag_vecs_tail
  polyEncoder_local2_post_join
  stackAt_dropStack32_split stackAt_dropStack32_split_bottom
  stackAt_dropStackPoly64_split stackAt_dropStackPoly64_split_bottom
  stack_restore_32_allocHook stack_restore_64_dropStack32
  threeVec400HeadersAt threeVec400HeadersAt_entails_memRegion_80
  twoVec400HeadersAt twoVec400HeadersAt_entails_memRegion_56
  unchunkedCt1SentEkReceived400_entails_dealloc
  unchunkedCt2Sent400_entails_dealloc
  unchunkedEkSent400_entails_dealloc
  unchunkedEkSentCt1Received400_entails_dealloc
  unchunkedEkSentCt1ReceivedAt_entails_dealloc
  vecCapPtrDealloc vecGF16ListOf vecPtListOf
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChunkedBudget (
  dropChunkedCt1ReceivedSpec dropChunkedCt2SampledSpec
  dropChunkedEkReceivedCt1SampledSpec dropChunkedEkSentCt1ReceivedSpec
  dropChunkedHeaderSentSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (
  dropGluePoly16Spec drop_glue_poly16_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyDecoderBudget (
  drop_glue_poly_decoder_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget (
  dropGluePolyEncoderSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (
  dropProtoPolyEncoderSpec drop_glue_proto_poly_encoder_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (
  dropGlueSortedSetPt16Spec drop_glue_sorted_set_pt16_placed_ok
)

open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux (
  align_pre_st
  align_pre_vm
  deallocFreeOnlySpec
  drop_chunked_ct2_sampled_cl_blockProgram
  drop_chunked_ct2_sampled_cl_on
  drop_chunked_ct2_sampled_cl_placed_ok
  drop_chunked_ct2_sampled_mem_on
  drop_glue_poly16_cl_blockProgram
  drop_glue_poly16_cl_on
  drop_glue_poly16_cl_placed_ok
  drop_glue_poly16_mem_on
  drop_glue_poly_decoder_cl_blockProgram
  drop_glue_poly_decoder_cl_on
  drop_glue_poly_decoder_cl_placed_ok
  drop_glue_poly_decoder_mem_on
  drop_glue_poly_encoder_local2_cl_blockProgram
  drop_glue_poly_encoder_local2_cl_on
  drop_glue_poly_encoder_local2_cl_placed_ok
  drop_glue_poly_encoder_local2_mem_on
  drop_glue_proto_poly_encoder_cl_blockProgram
  drop_glue_proto_poly_encoder_cl_on
  drop_glue_proto_poly_encoder_cl_placed_ok
  drop_glue_proto_poly_encoder_mem_on
  drop_glue_sorted_set_pt16_cl_blockProgram
  drop_glue_sorted_set_pt16_cl_on
  drop_glue_sorted_set_pt16_cl_placed_ok
  drop_glue_sorted_set_pt16_mem_on
  ls_to_blockProgram
  savedFrame32
  sepWP_evs_dealloc
  sepWP_evs_nil
  sepWP_open_evs
  sepWP_open_evs_outer
  sepWP_vm_evs_nil
  seq_evs_step
  seq_evs_step_lscl
  seq_vm_clean
  seq_vm_clean_lscl
  subroutine_ok_deallocFreeOnly
  subroutine_ok_withLsCodeLoaded_intro
)

open CryptoVerification (IsLsBlockProg LibsignalCodeLoaded LibsignalPlacement blkPC_275 blkPC_276 blkPC_277 blkPC_278 blkPl_275 blkPl_276 blkPl_277 blkPl_278 libsignalSessionLib lsProg_137 lsProg_264 lsProg_265 lsProg_271 lsProg_272 lsProg_274 lsProg_275 lsProg_276 lsProg_277 lsProg_278 ls_blockPlacement_base ls_subroutine_ok_of_block lscall_blk_cl lsmpl lsρ withLsCodeLoaded withMemEq)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Poly (polyArrayBytes polyDecoderAt polyEncoderAt)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem drop_glue_sorted_set_pt16_cl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_264 (Rust.withPanics ext)) (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_sorted_set_pt16_cl_placed_ok h

theorem drop_glue_sorted_set_pt16_cl_blockProgram [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 264 (Rust.withPanics ext)) (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_sorted_set_pt16_cl_blockProgram h

theorem drop_glue_sorted_set_pt16_cl_on [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_sorted_set_pt16_cl_on h hidx

theorem drop_glue_sorted_set_pt16_mem_on [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 264) (withMemEq m (dropGlueSortedSetPt16Spec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_sorted_set_pt16_mem_on h hcl hidx

theorem drop_glue_poly16_cl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_265 (Rust.withPanics ext)) (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_poly16_cl_placed_ok h

theorem drop_glue_poly16_cl_blockProgram [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 265 (Rust.withPanics ext)) (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_poly16_cl_blockProgram h

theorem drop_glue_poly16_cl_on [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_poly16_cl_on h hidx

theorem drop_glue_poly16_mem_on [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 265) (withMemEq m (dropGluePoly16Spec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_poly16_mem_on h hcl hidx

theorem drop_glue_poly_decoder_cl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_137 (Rust.withPanics ext)) (lsmpl.base 137) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_poly_decoder_cl_placed_ok h

theorem drop_glue_poly_decoder_cl_blockProgram [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 137 (Rust.withPanics ext)) (lsmpl.base 137) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_poly_decoder_cl_blockProgram h

theorem drop_glue_poly_decoder_cl_on [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 137) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_poly_decoder_cl_on h hidx

theorem drop_glue_poly_decoder_mem_on [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 137) (withMemEq m (dropGlueSortedSetPt16Spec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_poly_decoder_mem_on h hcl hidx

theorem drop_glue_proto_poly_encoder_cl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_271 (Rust.withPanics ext)) (lsmpl.base 271) (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_proto_poly_encoder_cl_placed_ok h

theorem drop_glue_proto_poly_encoder_cl_blockProgram [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 271 (Rust.withPanics ext)) (lsmpl.base 271) (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_proto_poly_encoder_cl_blockProgram h

theorem drop_glue_proto_poly_encoder_cl_on [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 271) (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_proto_poly_encoder_cl_on h hidx

theorem drop_glue_proto_poly_encoder_mem_on [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 271) (withMemEq m (dropProtoPolyEncoderSpec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_proto_poly_encoder_mem_on h hcl hidx

theorem drop_glue_poly_encoder_local2_cl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_272 (Rust.withPanics ext)) (lsmpl.base 272) (withLsCodeLoaded lsmpl (dropGluePolyEncoderSpec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_poly_encoder_local2_cl_placed_ok h

theorem drop_glue_poly_encoder_local2_cl_blockProgram [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 272 (Rust.withPanics ext)) (lsmpl.base 272) (withLsCodeLoaded lsmpl (dropGluePolyEncoderSpec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_poly_encoder_local2_cl_blockProgram h

theorem drop_glue_poly_encoder_local2_cl_on [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 272) (withLsCodeLoaded lsmpl (dropGluePolyEncoderSpec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_poly_encoder_local2_cl_on h hidx

theorem drop_glue_poly_encoder_local2_mem_on [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 272) (withMemEq m (dropGluePolyEncoderSpec M A lim)) :=
  DropChunkedClPlacedBudgetAux.drop_glue_poly_encoder_local2_mem_on h hcl hidx

theorem drop_chunked_ct2_sampled_cl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_274 (Rust.withPanics ext)) (lsmpl.base 274) (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec M A lim F)) :=
  DropChunkedClPlacedBudgetAux.drop_chunked_ct2_sampled_cl_placed_ok h

theorem drop_chunked_ct2_sampled_cl_blockProgram [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 274 (Rust.withPanics ext)) (lsmpl.base 274) (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec M A lim F)) :=
  DropChunkedClPlacedBudgetAux.drop_chunked_ct2_sampled_cl_blockProgram h

theorem drop_chunked_ct2_sampled_cl_on [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 274) (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec M A lim F)) :=
  DropChunkedClPlacedBudgetAux.drop_chunked_ct2_sampled_cl_on h hidx

theorem drop_chunked_ct2_sampled_mem_on [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (h : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 274) (withMemEq m (dropChunkedCt2SampledSpec M A lim F)) :=
  DropChunkedClPlacedBudgetAux.drop_chunked_ct2_sampled_mem_on h hcl hidx

/-! ## Block `275`: `drop_glue::<chunked::send_ct::EkReceivedCt1Sampled>` -/

theorem drop_chunked_ek_received_ct1_sampled_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_275 (Rust.withPanics ext)) (lsmpl.base 275)
      (withLsCodeLoaded lsmpl (dropChunkedEkReceivedCt1SampledSpec M A lim F)) := by
  rw [← ls_blockPlacement_base (i := 275)]
  change subroutine_ok ((blkPC_275).rebase (blkPl_275).base (Rust.withPanics ext)) (blkPl_275).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_fo := subroutine_ok_deallocFreeOnly
    (spqr_hook_ok_of_mem (prog := lsProg_275 (Rust.withPanics ext)) hdealloc)
  simp only [lsProg_275, deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropChunkedEkReceivedCt1SampledSpec, chunkedEkReceivedCt1SampledSize]
  wp_init x_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hlr0 : LsRetAddr624 (s0.readReg64 .lr) := _hlr0_gpr
  rcases x_st with ⟨⟨a, st_c⟩, st⟩
  have hm : s0.mem = m := by assumption
  subst hm
  dsimp only [CryptoVerification.SpqrV1.Drop.DropChunkedEkReceivedCt1SampledGhost.a,
    CryptoVerification.SpqrV1.Drop.DropChunkedEkReceivedCt1SampledGhost.st, chunkedEkReceivedCt1SampledAt] at *
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (unchunkedCt1SentEkReceived400_entails_dealloc A.repAlloc a st_c.uc))) ?_
  wp_pull_exists; rename_i g
  apply sepWP_open_evs
  refine seq_evs_step_lscl hcl (mid := (blkPl_275).base + 116#64)
    (P_mid := fun st5 sm =>
      (polyEncoderAt A.repAlloc a st_c.sending_ct1 ∗ memRegion (a + 400#64) 128) ∗
      A.pool lim st5 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
  · refine seq_evs_step (mid := (blkPl_275).base + 36#64)
      (P_mid := fun st1 sm =>
        (polyEncoderAt A.repAlloc a st_c.sending_ct1 ∗
          (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
           vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗ vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
           vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
        A.pool lim st1 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
    · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · refine sepWP_vm_evs_nil (fun sm hvm => by
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
        by_vm_steps (
          wp_steps
          refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done)
      · apply sepWP_evs_dealloc g.v1.cap.toNat 1
        refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          (P_mid := A.pool lim st s0 ∗ A.live g.v1.ptr g.v1.cap.toNat 1 ∗ memRegion g.v1.ptr g.v1.cap.toNat ∗
            stackAt (s0.sp - 32#64) allocHookStack ∗
            ((polyEncoderAt A.repAlloc a st_c.sending_ct1 ∗
              (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
               vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗ vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
               vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗ savedFrame32 s0 w3_old))
          (Q := fun sc => Saved32x19Preserved s0 sc (s0.sp - 32#64) ∧ AllocCallPreserved s0 sc ∧
            sc.readReg64 .x0 = g.v1.ptr ∧ sc.readReg64 .x1 = g.v1.cap ∧ sc.readReg64 .x2 = 1#64 ∧
            sc.readReg64 .lr = (blkPl_275).base + 36#64 ∧ sc.readReg64 .x19 = a) ?_ ?_
        · by_vm_steps (
            wp_steps
            dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            refine align_pre_vm (by simp only [Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done)
        · intro sc hpcc hrunc hvmc ⟨hpres_c, hacp_c, hx0_c, hx1_c, hx2_c, hlr_c, hx19_c⟩
          rcases hpres_c with ⟨hx20_c, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hsp_c, htrace_c, hvregs_c⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_c
          rw [← A.pool_of_vmPreserved hvmc, ← hsp_c, ← hlr_c]
          have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
            change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
            simp (config := { decide := true }) only [arm64_norm, wp_norm]
          have _hlr_sc_lr : LsRetAddr624 (sc.readReg64 .lr) := _hlr_sc
          wp_call hdealloc_fo (g.v1.ptr, g.v1.cap.toNat, 1, st)
          rw [hsp_c, hlr_c]
          have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done
    · intro st1 s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_1
      refine seq_evs_step (mid := (blkPl_275).base + 56#64)
        (P_mid := fun st2 sm =>
          (polyEncoderAt A.repAlloc a st_c.sending_ct1 ∗
            (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
             vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗ vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
          A.pool lim st2 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
        (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
      · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · apply sepWP_evs_dealloc g.v2.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_1]
          have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · intro st2 s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_2
        refine seq_evs_step (mid := (blkPl_275).base + 76#64)
          (P_mid := fun st3 sm =>
            (polyEncoderAt A.repAlloc a st_c.sending_ct1 ∗
              (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
               vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
            A.pool lim st3 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
          (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
        · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc3 : (g.v3.cap == 0#64) = true <;>
            simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
          · apply sepWP_evs_dealloc g.v3.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_2]
            have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · intro st3 s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_3
          refine seq_evs_step (mid := (blkPl_275).base + 96#64)
            (P_mid := fun st4 sm =>
              (polyEncoderAt A.repAlloc a st_c.sending_ct1 ∗
                (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
              A.pool lim st4 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
            (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
          · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hc4 : (g.v4.cap == 0#64) = true <;>
              simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
              wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
            · apply sepWP_evs_dealloc g.v4.cap.toNat 1
              wp_steps; wp_apply; rw [hsp_3]
              have hacp' : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
          · intro st4 s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hacp_4, hx19_4⟩
            have ⟨_, _, _, _, _, _, _⟩ := hacp_4
            dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hc5 : (g.v5.cap == 0#64) = true <;>
              simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
              wp_steps
              have hhdr := fiveVec400HeadersAt_entails_memRegion_128 a g; dsimp only [fiveVec400HeadersAt] at hhdr
              refine SepWP.focus_weaken hhdr (by sep_focus) ?_
              refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
            · apply sepWP_evs_dealloc g.v5.cap.toNat 1
              wp_steps; wp_apply; rw [hsp_4]
              have hacp' : AllocCallPreserved s0 sf := hacp_4.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              have hhdr := fiveVec400HeadersAt_entails_memRegion_128 a g; dsimp only [fiveVec400HeadersAt] at hhdr
              refine SepWP.focus_weaken hhdr (by sep_focus) ?_
              refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st5 s5 hpc5 hrun5 hcl5 ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hacp_5, hx19_5⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_5
    refine SepWP.weaken_pre
      (sepConj_mono_left (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A.repAlloc a st_c.sending_ct1))) ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro tag
    rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
    wp_focus_pure; intro hvecs_len
    refine seq_vm_clean_lscl hcl5 (mid := lsmpl.base 265)
      (P_mid := vecGF16ListOf A.repAlloc (a + 8#64) vecs ∗ A.pool lim st5 s5 ∗
        stackAt s0.sp dropGluePoly16Stack ∗ ((a ↦₆₄ tag) ∗ memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 128))
      (Q := fun sc => sc.sp = s0.sp ∧ sc.trace = s0.trace ∧
        sc.readReg64 .x0 = a + 8#64 ∧ sc.readReg64 .lr = s0.readReg64 .lr ∧
        AllocCallPreserved s0 sc ∧ CalleeSavedPreserved s0 sc) ?_ ?_
    · by_vm_steps (
        dsimp only [savedFrame32]; wp_steps
        refine SepWP.focus_weaken (stack_restore_32_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old) (by sep_focus) ?_
        refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
    · intro sc hpcc hrunc hclc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hacp_c, hcs_c⟩
      have hpoly16_raw := drop_glue_poly16_mem_on
        (callerProg := lsProg_275 (Rust.withPanics ext)) hdealloc hclc
      dsimp only [lsProg_275, withMemEq, dropGluePoly16Spec] at hpoly16_raw
      have ⟨_, _, _, _, _, _, _⟩ := hacp_c
      have hlr_sc : LsRetAddr624 (sc.readReg64 .lr) := hlr_c ▸ hlr0
      have _hlr_sc_gpr : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := hlr_sc
      rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
      wp_call hpoly16_raw (⟨a + 8#64, vecs⟩, st5)
      rw [hsp_c]
      have hacp_cf : AllocCallPreserved sc sf := by assumption
      have hevs_w : FreeOnlyEvs w := by assumption
      have hacp_f : AllocCallPreserved s0 sf := hacp_c.trans hacp_cf
      have ⟨_, _, _, _, _, _, _⟩ := hacp_f
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ = ((a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗
            memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 128) ∗
            A.pool lim (M.stepEvents w st5) sf ∗ stackAt s0.sp dropGluePoly16Stack by sep_ac_rfl))
          (sepConj_mono_left (chunked_400_join a tag 128 528 rfl (by decide)))) ?_
      refine SepWP.mono (post := fun sf' Pf =>
          (Pf ⊢ memRegion a 528 ∗ A.pool lim (M.stepEvents w st5) sf' ∗ stackAt s0.sp dropGluePoly16Stack) ∧
          (sf'.sp = s0.sp ∧ sf'.trace = s0.trace ∧ AllocCallPreserved s0 sf' ∧ CalleeSavedPreserved s0 sf'))
        (by wp_done) (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)

theorem drop_chunked_ek_received_ct1_sampled_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 275 (Rust.withPanics ext)) (lsmpl.base 275)
      (withLsCodeLoaded lsmpl (dropChunkedEkReceivedCt1SampledSpec M A lim F)) :=
  ls_to_blockProgram (drop_chunked_ek_received_ct1_sampled_cl_placed_ok hdealloc)

theorem drop_chunked_ek_received_ct1_sampled_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 275)
      (withLsCodeLoaded lsmpl (dropChunkedEkReceivedCt1SampledSpec M A lim F)) :=
  ls_subroutine_ok_of_block (drop_chunked_ek_received_ct1_sampled_cl_placed_ok hdealloc) hidx

theorem drop_chunked_ek_received_ct1_sampled_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 275)
      (withMemEq m (dropChunkedEkReceivedCt1SampledSpec M A lim F)) :=
  lscall_blk_cl (drop_chunked_ek_received_ct1_sampled_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `277`: `drop_glue::<chunked::send_ek::Ct1Received>` -/

theorem drop_chunked_ct1_received_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_277 (Rust.withPanics ext)) (lsmpl.base 277)
      (withLsCodeLoaded lsmpl (dropChunkedCt1ReceivedSpec M A lim F)) := by
  rw [← ls_blockPlacement_base (i := 277)]
  change subroutine_ok ((blkPC_277).rebase (blkPl_277).base (Rust.withPanics ext)) (blkPl_277).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_fo := subroutine_ok_deallocFreeOnly
    (spqr_hook_ok_of_mem (prog := lsProg_277 (Rust.withPanics ext)) hdealloc)
  simp only [lsProg_277, deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropChunkedCt1ReceivedSpec, chunkedCt1ReceivedSize]
  wp_init x_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hlr0 : LsRetAddr624 (s0.readReg64 .lr) := _hlr0_gpr
  rcases x_st with ⟨⟨a, st_c⟩, st⟩
  have hm : s0.mem = m := by assumption
  subst hm
  dsimp only [CryptoVerification.SpqrV1.Drop.DropChunkedCt1ReceivedGhost.a, CryptoVerification.SpqrV1.Drop.DropChunkedCt1ReceivedGhost.st, chunkedCt1ReceivedAt] at *
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (unchunkedEkSentCt1Received400_entails_dealloc A.repAlloc a st_c.uc))) ?_
  wp_pull_exists; rename_i g
  apply sepWP_open_evs
  refine seq_evs_step_lscl hcl (mid := (blkPl_277).base + 96#64)
    (P_mid := fun st4 sm =>
      (polyEncoderAt A.repAlloc a st_c.sending_ek ∗ memRegion (a + 400#64) 104) ∗
      A.pool lim st4 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
  · refine seq_evs_step (mid := (blkPl_277).base + 36#64)
      (P_mid := fun st1 sm =>
        (polyEncoderAt A.repAlloc a st_c.sending_ek ∗
          (fourVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
           vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗ vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr)) ∗
        A.pool lim st1 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
    · dsimp only [fourVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · refine sepWP_vm_evs_nil (fun sm hvm => by
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
        by_vm_steps (
          wp_steps
          refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done)
      · apply sepWP_evs_dealloc g.v1.cap.toNat 1
        refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          (P_mid := A.pool lim st s0 ∗ A.live g.v1.ptr g.v1.cap.toNat 1 ∗ memRegion g.v1.ptr g.v1.cap.toNat ∗
            stackAt (s0.sp - 32#64) allocHookStack ∗
            ((polyEncoderAt A.repAlloc a st_c.sending_ek ∗
              (fourVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
               vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗ vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr)) ∗ savedFrame32 s0 w3_old))
          (Q := fun sc => Saved32x19Preserved s0 sc (s0.sp - 32#64) ∧ AllocCallPreserved s0 sc ∧
            sc.readReg64 .x0 = g.v1.ptr ∧ sc.readReg64 .x1 = g.v1.cap ∧ sc.readReg64 .x2 = 1#64 ∧
            sc.readReg64 .lr = (blkPl_277).base + 36#64 ∧ sc.readReg64 .x19 = a) ?_ ?_
        · by_vm_steps (
            wp_steps
            dsimp only [fourVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            refine align_pre_vm (by simp only [Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done)
        · intro sc hpcc hrunc hvmc ⟨hpres_c, hacp_c, hx0_c, hx1_c, hx2_c, hlr_c, hx19_c⟩
          rcases hpres_c with ⟨hx20_c, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hsp_c, htrace_c, hvregs_c⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_c
          rw [← A.pool_of_vmPreserved hvmc, ← hsp_c, ← hlr_c]
          have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
            change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
            simp (config := { decide := true }) only [arm64_norm, wp_norm]
          have _hlr_sc_lr : LsRetAddr624 (sc.readReg64 .lr) := _hlr_sc
          wp_call hdealloc_fo (g.v1.ptr, g.v1.cap.toNat, 1, st)
          rw [hsp_c, hlr_c]
          have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          dsimp only [fourVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done
    · intro st1 s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_1
      refine seq_evs_step (mid := (blkPl_277).base + 56#64)
        (P_mid := fun st2 sm =>
          (polyEncoderAt A.repAlloc a st_c.sending_ek ∗
            (fourVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
             vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr)) ∗
          A.pool lim st2 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
        (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
      · dsimp only [fourVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · apply sepWP_evs_dealloc g.v2.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_1]
          have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · intro st2 s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_2
        refine seq_evs_step (mid := (blkPl_277).base + 76#64)
          (P_mid := fun st3 sm =>
            (polyEncoderAt A.repAlloc a st_c.sending_ek ∗
              (fourVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr)) ∗
            A.pool lim st3 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
          (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
        · dsimp only [fourVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc3 : (g.v3.cap == 0#64) = true <;>
            simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
          · apply sepWP_evs_dealloc g.v3.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_2]
            have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · intro st3 s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_3
          dsimp only [fourVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            wp_steps
            have hhdr := fourVec400HeadersAt_entails_memRegion_104 a g; dsimp only [fourVec400HeadersAt] at hhdr
            refine SepWP.focus_weaken hhdr (by sep_focus) ?_
            refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
          · apply sepWP_evs_dealloc g.v4.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_3]
            have hacp' : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            have hhdr := fourVec400HeadersAt_entails_memRegion_104 a g; dsimp only [fourVec400HeadersAt] at hhdr
            refine SepWP.focus_weaken hhdr (by sep_focus) ?_
            refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st4 s4 hpc4 hrun4 hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hacp_4, hx19_4⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_4
    refine SepWP.weaken_pre
      (sepConj_mono_left (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A.repAlloc a st_c.sending_ek))) ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro tag
    rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
    wp_focus_pure; intro hvecs_len
    refine seq_vm_clean_lscl hcl4 (mid := lsmpl.base 265)
      (P_mid := vecGF16ListOf A.repAlloc (a + 8#64) vecs ∗ A.pool lim st4 s4 ∗
        stackAt s0.sp dropGluePoly16Stack ∗ ((a ↦₆₄ tag) ∗ memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 104))
      (Q := fun sc => sc.sp = s0.sp ∧ sc.trace = s0.trace ∧
        sc.readReg64 .x0 = a + 8#64 ∧ sc.readReg64 .lr = s0.readReg64 .lr ∧
        AllocCallPreserved s0 sc ∧ CalleeSavedPreserved s0 sc) ?_ ?_
    · by_vm_steps (
        dsimp only [savedFrame32]; wp_steps
        refine SepWP.focus_weaken (stack_restore_32_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old) (by sep_focus) ?_
        refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
    · intro sc hpcc hrunc hclc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hacp_c, hcs_c⟩
      have hpoly16_raw := drop_glue_poly16_mem_on
        (callerProg := lsProg_277 (Rust.withPanics ext)) hdealloc hclc
      dsimp only [lsProg_277, withMemEq, dropGluePoly16Spec] at hpoly16_raw
      have ⟨_, _, _, _, _, _, _⟩ := hacp_c
      have hlr_sc : LsRetAddr624 (sc.readReg64 .lr) := hlr_c ▸ hlr0
      have _hlr_sc_gpr : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := hlr_sc
      rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
      wp_call hpoly16_raw (⟨a + 8#64, vecs⟩, st4)
      rw [hsp_c]
      have hacp_cf : AllocCallPreserved sc sf := by assumption
      have hevs_w : FreeOnlyEvs w := by assumption
      have hacp_f : AllocCallPreserved s0 sf := hacp_c.trans hacp_cf
      have ⟨_, _, _, _, _, _, _⟩ := hacp_f
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ = ((a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗
            memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 104) ∗
            A.pool lim (M.stepEvents w st4) sf ∗ stackAt s0.sp dropGluePoly16Stack by sep_ac_rfl))
          (sepConj_mono_left (chunked_400_join a tag 104 504 rfl (by decide)))) ?_
      refine SepWP.mono (post := fun sf' Pf =>
          (Pf ⊢ memRegion a 504 ∗ A.pool lim (M.stepEvents w st4) sf' ∗ stackAt s0.sp dropGluePoly16Stack) ∧
          (sf'.sp = s0.sp ∧ sf'.trace = s0.trace ∧ AllocCallPreserved s0 sf' ∧ CalleeSavedPreserved s0 sf'))
        (by wp_done) (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)

theorem drop_chunked_ct1_received_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 277 (Rust.withPanics ext)) (lsmpl.base 277)
      (withLsCodeLoaded lsmpl (dropChunkedCt1ReceivedSpec M A lim F)) :=
  ls_to_blockProgram (drop_chunked_ct1_received_cl_placed_ok hdealloc)

theorem drop_chunked_ct1_received_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 277)
      (withLsCodeLoaded lsmpl (dropChunkedCt1ReceivedSpec M A lim F)) :=
  ls_subroutine_ok_of_block (drop_chunked_ct1_received_cl_placed_ok hdealloc) hidx

theorem drop_chunked_ct1_received_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 277)
      (withMemEq m (dropChunkedCt1ReceivedSpec M A lim F)) :=
  lscall_blk_cl (drop_chunked_ct1_received_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `278`: `drop_glue::<chunked::send_ek::EkSentCt1Received>` -/

theorem drop_chunked_ek_sent_ct1_received_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_278 (Rust.withPanics ext)) (lsmpl.base 278)
      (withLsCodeLoaded lsmpl (dropChunkedEkSentCt1ReceivedSpec M A lim F)) := by
  rw [← ls_blockPlacement_base (i := 278)]
  change subroutine_ok ((blkPC_278).rebase (blkPl_278).base (Rust.withPanics ext)) (blkPl_278).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_fo := subroutine_ok_deallocFreeOnly
    (spqr_hook_ok_of_mem (prog := lsProg_278 (Rust.withPanics ext)) hdealloc)
  simp only [lsProg_278, deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropChunkedEkSentCt1ReceivedSpec, chunkedEkSentCt1ReceivedSize]
  wp_init x_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hlr0 : LsRetAddr624 (s0.readReg64 .lr) := _hlr0_gpr
  rcases x_st with ⟨⟨a, st_c⟩, st⟩
  have hm : s0.mem = m := by assumption
  subst hm
  dsimp only [CryptoVerification.SpqrV1.Drop.DropChunkedEkSentCt1ReceivedGhost.a,
    CryptoVerification.SpqrV1.Drop.DropChunkedEkSentCt1ReceivedGhost.st, chunkedEkSentCt1ReceivedAt] at *
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_left (unchunkedEkSentCt1ReceivedAt_entails_dealloc A.repAlloc a st_c.uc)) ?_
  wp_pull_exists; rename_i g
  apply sepWP_open_evs
  refine seq_evs_step_lscl hcl (mid := (blkPl_278).base + 96#64)
    (P_mid := fun st4 sm =>
      (memRegion a 104 ∗ polyDecoderAt A.repAlloc (a + 104#64) st_c.receiving_ct2) ∗
      A.pool lim st4 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
  · refine seq_evs_step (mid := (blkPl_278).base + 36#64)
      (P_mid := fun st1 sm =>
        ((fourVec104HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
           vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗ vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr) ∗
          polyDecoderAt A.repAlloc (a + 104#64) st_c.receiving_ct2) ∗
        A.pool lim st1 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
    · dsimp only [fourVec104HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · refine sepWP_vm_evs_nil (fun sm hvm => by
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
        by_vm_steps (
          wp_steps
          refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done)
      · apply sepWP_evs_dealloc g.v1.cap.toNat 1
        refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          (P_mid := A.pool lim st s0 ∗ A.live g.v1.ptr g.v1.cap.toNat 1 ∗ memRegion g.v1.ptr g.v1.cap.toNat ∗
            stackAt (s0.sp - 32#64) allocHookStack ∗
            (((fourVec104HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
               vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗ vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr) ∗
              polyDecoderAt A.repAlloc (a + 104#64) st_c.receiving_ct2) ∗ savedFrame32 s0 w3_old))
          (Q := fun sc => Saved32x19Preserved s0 sc (s0.sp - 32#64) ∧ AllocCallPreserved s0 sc ∧
            sc.readReg64 .x0 = g.v1.ptr ∧ sc.readReg64 .x1 = g.v1.cap ∧ sc.readReg64 .x2 = 1#64 ∧
            sc.readReg64 .lr = (blkPl_278).base + 36#64 ∧ sc.readReg64 .x19 = a) ?_ ?_
        · by_vm_steps (
            wp_steps
            dsimp only [fourVec104HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            refine align_pre_vm (by simp only [Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done)
        · intro sc hpcc hrunc hvmc ⟨hpres_c, hacp_c, hx0_c, hx1_c, hx2_c, hlr_c, hx19_c⟩
          rcases hpres_c with ⟨hx20_c, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hsp_c, htrace_c, hvregs_c⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_c
          rw [← A.pool_of_vmPreserved hvmc, ← hsp_c, ← hlr_c]
          have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
            change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
            simp (config := { decide := true }) only [arm64_norm, wp_norm]
          have _hlr_sc_lr : LsRetAddr624 (sc.readReg64 .lr) := _hlr_sc
          wp_call hdealloc_fo (g.v1.ptr, g.v1.cap.toNat, 1, st)
          rw [hsp_c, hlr_c]
          have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          dsimp only [fourVec104HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done
    · intro st1 s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_1
      refine seq_evs_step (mid := (blkPl_278).base + 56#64)
        (P_mid := fun st2 sm =>
          ((fourVec104HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
             vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr) ∗
            polyDecoderAt A.repAlloc (a + 104#64) st_c.receiving_ct2) ∗
          A.pool lim st2 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
        (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
      · dsimp only [fourVec104HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · apply sepWP_evs_dealloc g.v2.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_1]
          have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · intro st2 s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_2
        refine seq_evs_step (mid := (blkPl_278).base + 76#64)
          (P_mid := fun st3 sm =>
            ((fourVec104HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr) ∗
              polyDecoderAt A.repAlloc (a + 104#64) st_c.receiving_ct2) ∗
            A.pool lim st3 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
          (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
        · dsimp only [fourVec104HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc3 : (g.v3.cap == 0#64) = true <;>
            simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
          · apply sepWP_evs_dealloc g.v3.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_2]
            have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · intro st3 s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_3
          dsimp only [fourVec104HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            wp_steps
            have hhdr := fourVec104HeadersAt_entails_memRegion_104 a g; dsimp only [fourVec104HeadersAt] at hhdr
            refine SepWP.focus_weaken hhdr (by sep_focus) ?_
            refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
          · apply sepWP_evs_dealloc g.v4.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_3]
            have hacp' : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            have hhdr := fourVec104HeadersAt_entails_memRegion_104 a g; dsimp only [fourVec104HeadersAt] at hhdr
            refine SepWP.focus_weaken hhdr (by sep_focus) ?_
            refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st4 s4 hpc4 hrun4 hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hacp_4, hx19_4⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_4
    refine SepWP.weaken_pre
      (sepConj_mono_left (sepConj_mono_right (polyDecoderAt_entails_vecs_tail A.repAlloc (a + 104#64) st_c.receiving_ct2))) ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
    have h488 : (a + 104#64) + 384#64 = a + 488#64 := by bv_omega
    rw [h488]; wp_focus_pure; intro hvecs_len
    refine seq_vm_clean_lscl hcl4 (mid := lsmpl.base 264)
      (P_mid := vecPtListOf A.repAlloc (a + 104#64) vecs ∗ A.pool lim st4 s4 ∗
        stackAt s0.sp dropGluePoly16Stack ∗ (memRegion a 104 ∗ memRegion (a + 488#64) 16))
      (Q := fun sc => sc.sp = s0.sp ∧ sc.trace = s0.trace ∧
        sc.readReg64 .x0 = a + 104#64 ∧ sc.readReg64 .lr = s0.readReg64 .lr ∧
        AllocCallPreserved s0 sc ∧ CalleeSavedPreserved s0 sc) ?_ ?_
    · by_vm_steps (
        dsimp only [savedFrame32]; wp_steps
        refine SepWP.focus_weaken (stack_restore_32_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old) (by sep_focus) ?_
        refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
    · intro sc hpcc hrunc hclc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hacp_c, hcs_c⟩
      have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
        (callerProg := lsProg_278 (Rust.withPanics ext)) hdealloc hclc
      dsimp only [lsProg_278, withMemEq, dropGlueSortedSetPt16Spec] at hpt16_raw
      have ⟨_, _, _, _, _, _, _⟩ := hacp_c
      have hlr_sc : LsRetAddr624 (sc.readReg64 .lr) := hlr_c ▸ hlr0
      have _hlr_sc_gpr : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := hlr_sc
      rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
      wp_call hpt16_raw (⟨a + 104#64, vecs⟩, st4)
      rw [hsp_c]
      have hacp_cf : AllocCallPreserved sc sf := by assumption
      have hevs_w : FreeOnlyEvs w := by assumption
      have hacp_f : AllocCallPreserved s0 sf := hacp_c.trans hacp_cf
      have ⟨_, _, _, _, _, _, _⟩ := hacp_f
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ = (memRegion a 104 ∗ memRegion (a + 104#64) polyArrayBytes ∗
            memRegion (a + 488#64) 16) ∗
            A.pool lim (M.stepEvents w st4) sf ∗ stackAt s0.sp dropGluePoly16Stack by sep_ac_rfl))
          (sepConj_mono_left (chunked_104_400_join a))) ?_
      refine SepWP.mono (post := fun sf' Pf =>
          (Pf ⊢ memRegion a 504 ∗ A.pool lim (M.stepEvents w st4) sf' ∗ stackAt s0.sp dropGluePoly16Stack) ∧
          (sf'.sp = s0.sp ∧ sf'.trace = s0.trace ∧ AllocCallPreserved s0 sf' ∧ CalleeSavedPreserved s0 sf'))
        (by wp_done) (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)

theorem drop_chunked_ek_sent_ct1_received_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 278 (Rust.withPanics ext)) (lsmpl.base 278)
      (withLsCodeLoaded lsmpl (dropChunkedEkSentCt1ReceivedSpec M A lim F)) :=
  ls_to_blockProgram (drop_chunked_ek_sent_ct1_received_cl_placed_ok hdealloc)

theorem drop_chunked_ek_sent_ct1_received_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 278)
      (withLsCodeLoaded lsmpl (dropChunkedEkSentCt1ReceivedSpec M A lim F)) :=
  ls_subroutine_ok_of_block (drop_chunked_ek_sent_ct1_received_cl_placed_ok hdealloc) hidx

theorem drop_chunked_ek_sent_ct1_received_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 278)
      (withMemEq m (dropChunkedEkSentCt1ReceivedSpec M A lim F)) :=
  lscall_blk_cl (drop_chunked_ek_sent_ct1_received_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `276`: `drop_glue::<chunked::send_ek::HeaderSent>` -/

theorem drop_chunked_header_sent_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_276 (Rust.withPanics ext)) (lsmpl.base 276)
      (withLsCodeLoaded lsmpl (dropChunkedHeaderSentSpec M A lim F)) := by
  rw [← ls_blockPlacement_base (i := 276)]
  change subroutine_ok ((blkPC_276).rebase (blkPl_276).base (Rust.withPanics ext)) (blkPl_276).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_fo := subroutine_ok_deallocFreeOnly
    (spqr_hook_ok_of_mem (prog := lsProg_276 (Rust.withPanics ext)) hdealloc)
  simp only [lsProg_276, deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropChunkedHeaderSentSpec, chunkedHeaderSentSize]
  wp_init x_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hlr0 : LsRetAddr624 (s0.readReg64 .lr) := _hlr0_gpr
  rcases x_st with ⟨⟨a, st_c⟩, st⟩
  have hm : s0.mem = m := by assumption
  subst hm
  dsimp only [CryptoVerification.SpqrV1.Drop.DropChunkedHeaderSentGhost.a, CryptoVerification.SpqrV1.Drop.DropChunkedHeaderSentGhost.st, chunkedHeaderSentAt] at *
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  have hsub_4160 : (s0.sp - 32#64) - 4128#64 = s0.sp - 4160#64 := by bv_omega
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]
  nth_rw 1 [stackAt_dropStack32_split_bottom (s0.sp - 32#64)]
  rw [hsub_4160]; cells_unfold; wp_pull_exists; rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (unchunkedEkSent400_entails_dealloc A.repAlloc a st_c.uc))) ?_
  wp_pull_exists; rename_i g
  apply sepWP_open_evs
  refine seq_evs_step_lscl hcl (mid := (blkPl_276).base + 76#64)
    (P_mid := fun st3 sm =>
      (polyEncoderAt A.repAlloc a st_c.sending_ek ∗ memRegion (a + 400#64) 80 ∗
        polyDecoderAt A.repAlloc (a + 480#64) st_c.receiving_ct1) ∗
      A.pool lim st3 sm ∗ stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗ savedFrame32 s0 w3_old)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
  · refine seq_evs_step (mid := (blkPl_276).base + 36#64)
      (P_mid := fun st1 sm =>
        (polyEncoderAt A.repAlloc a st_c.sending_ek ∗
          (threeVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
           vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
          polyDecoderAt A.repAlloc (a + 480#64) st_c.receiving_ct1) ∗ A.pool lim st1 sm ∗
        (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗ savedFrame32 s0 w3_old)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
    · dsimp only [threeVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · refine sepWP_vm_evs_nil (fun sm hvm => by
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
        by_vm_steps (
          wp_steps
          refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done)
      · apply sepWP_evs_dealloc g.v1.cap.toNat 1
        refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          (P_mid := A.pool lim st s0 ∗ A.live g.v1.ptr g.v1.cap.toNat 1 ∗ memRegion g.v1.ptr g.v1.cap.toNat ∗
            stackAt (s0.sp - 32#64) allocHookStack ∗
            ((polyEncoderAt A.repAlloc a st_c.sending_ek ∗
              (threeVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
               vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
              polyDecoderAt A.repAlloc (a + 480#64) st_c.receiving_ct1) ∗
             memRegion (s0.sp - 4160#64) 32 ∗ savedFrame32 s0 w3_old))
          (Q := fun sc => Saved32x19Preserved s0 sc (s0.sp - 32#64) ∧ AllocCallPreserved s0 sc ∧
            sc.readReg64 .x0 = g.v1.ptr ∧ sc.readReg64 .x1 = g.v1.cap ∧ sc.readReg64 .x2 = 1#64 ∧
            sc.readReg64 .lr = (blkPl_276).base + 36#64 ∧ sc.readReg64 .x19 = a) ?_ ?_
        · by_vm_steps (
            wp_steps
            dsimp only [threeVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            refine align_pre_vm (by simp only [Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done)
        · intro sc hpcc hrunc hvmc ⟨hpres_c, hacp_c, hx0_c, hx1_c, hx2_c, hlr_c, hx19_c⟩
          rcases hpres_c with ⟨hx20_c, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hsp_c, htrace_c, hvregs_c⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_c
          rw [← A.pool_of_vmPreserved hvmc, ← hsp_c, ← hlr_c]
          have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
            change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
            simp (config := { decide := true }) only [arm64_norm, wp_norm]
          have _hlr_sc_lr : LsRetAddr624 (sc.readReg64 .lr) := _hlr_sc
          wp_call hdealloc_fo (g.v1.ptr, g.v1.cap.toNat, 1, st)
          rw [hsp_c, hlr_c]
          have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          dsimp only [threeVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done
    · intro st1 s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_1
      refine seq_evs_step (mid := (blkPl_276).base + 56#64)
        (P_mid := fun st2 sm =>
          (polyEncoderAt A.repAlloc a st_c.sending_ek ∗
            (threeVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
            polyDecoderAt A.repAlloc (a + 480#64) st_c.receiving_ct1) ∗ A.pool lim st2 sm ∗
          (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗ savedFrame32 s0 w3_old)
        (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
      · dsimp only [threeVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · apply sepWP_evs_dealloc g.v2.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_1]
          have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · intro st2 s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_2
        have hstack_join : memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack ⊢
            stackAt (s0.sp - 32#64) dropGluePoly16Stack := by
          rw [← hsub_4160]; exact Entails.of_eq (stackAt_dropStack32_split_bottom (s0.sp - 32#64)).symm
        dsimp only [threeVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps
          have hhdr := threeVec400HeadersAt_entails_memRegion_80 a g; dsimp only [threeVec400HeadersAt] at hhdr
          refine SepWP.focus_weaken hhdr (by sep_focus) ?_
          refine SepWP.focus_weaken hstack_join (by sep_focus) ?_
          refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · apply sepWP_evs_dealloc g.v3.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_2]
          have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          have hhdr := threeVec400HeadersAt_entails_memRegion_80 a g; dsimp only [threeVec400HeadersAt] at hhdr
          refine SepWP.focus_weaken hhdr (by sep_focus) ?_
          refine SepWP.focus_weaken hstack_join (by sep_focus) ?_
          refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st3 s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_3
    refine seq_evs_step_lscl hcl3 (mid := (blkPl_276).base + 84#64)
      (P_mid := fun st4 sm =>
        (memRegion a 480 ∗ polyDecoderAt A.repAlloc (a + 480#64) st_c.receiving_ct1) ∗
        A.pool lim st4 sm ∗ stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗ savedFrame32 s0 w3_old)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
    · refine SepWP.weaken_pre
        (sepConj_mono_left (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A.repAlloc a st_c.sending_ek))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro tag
      rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
      wp_focus_pure; intro hvecs_len
      refine seq_vm_clean_lscl hcl3 (mid := lsmpl.base 265)
        (P_mid := vecGF16ListOf A.repAlloc (a + 8#64) vecs ∗ A.pool lim st3 s3 ∗
          stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗
          (((a ↦₆₄ tag) ∗ memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 80) ∗
            polyDecoderAt A.repAlloc (a + 480#64) st_c.receiving_ct1 ∗ savedFrame32 s0 w3_old))
        (Q := fun sc => Saved32x19Preserved s0 sc (s0.sp - 32#64) ∧ AllocCallPreserved s0 sc ∧
          sc.readReg64 .x0 = a + 8#64 ∧ sc.readReg64 .lr = (blkPl_276).base + 84#64 ∧
          sc.readReg64 .x19 = a) ?_ ?_
      · by_vm_steps (wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
      · intro sc hpcc hrunc hclc hvmc ⟨hpres_c, hacp_c, hx0_c, hlr_c, hx19_c⟩
        have hpoly16_raw := drop_glue_poly16_mem_on
          (callerProg := lsProg_276 (Rust.withPanics ext)) hdealloc hclc
        dsimp only [lsProg_276, withMemEq, dropGluePoly16Spec] at hpoly16_raw
        rcases hpres_c with ⟨hx20_c, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hsp_c, htrace_c, hvregs_c⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_c
        rw [← A.pool_of_vmPreserved hvmc, ← hsp_c, ← hlr_c]
        have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
          change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
          simp (config := { decide := true }) only [arm64_norm, wp_norm]
        have _hlr_sc_lr : LsRetAddr624 (sc.readReg64 .lr) := _hlr_sc
        wp_call hpoly16_raw (⟨a + 8#64, vecs⟩, st3)
        rw [hsp_c, hlr_c]
        have hacp_cf : AllocCallPreserved sc sf := by assumption
        have hevs_w : FreeOnlyEvs w := by assumption
        have hacp_f : AllocCallPreserved s0 sf := hacp_c.trans hacp_cf
        have ⟨_, _, _, _, _, _, _⟩ := hacp_f
        refine SepWP.weaken_pre
          (Entails.trans
            (Entails.of_eq (show _ = (((a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗
              memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 80) ∗
              polyDecoderAt A.repAlloc (a + 480#64) st_c.receiving_ct1) ∗
              A.pool lim (M.stepEvents w st3) sf ∗ stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗
              savedFrame32 s0 w3_old by sep_ac_rfl))
            (sepConj_mono_left (sepConj_mono_left (chunked_400_join a tag 80 480 rfl (by decide))))) ?_
        refine SepWP.mono (post := fun sf' Pf =>
            (Pf ⊢ (memRegion a 480 ∗ polyDecoderAt A.repAlloc (a + 480#64) st_c.receiving_ct1) ∗
              A.pool lim (M.stepEvents w st3) sf' ∗ stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗
              savedFrame32 s0 w3_old) ∧
            (Saved32x19Preserved s0 sf' (s0.sp - 32#64) ∧ AllocCallPreserved s0 sf' ∧ sf'.readReg64 .x19 = a))
          (by wp_done) (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)
    · intro st4 s4 hpc4 hrun4 hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hacp_4, hx19_4⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_4
      refine SepWP.weaken_pre
        (sepConj_mono_left (sepConj_mono_right (polyDecoderAt_entails_vecs_tail A.repAlloc (a + 480#64) st_c.receiving_ct1))) ?_
      rw [sepExists_sepConj_right, sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
      have h864 : (a + 480#64) + 384#64 = a + 864#64 := by bv_omega
      rw [h864]; wp_focus_pure; intro hvecs_len
      refine seq_vm_clean_lscl hcl4 (mid := lsmpl.base 264)
        (P_mid := vecPtListOf A.repAlloc (a + 480#64) vecs ∗ A.pool lim st4 s4 ∗
          stackAt s0.sp dropGluePoly16Stack ∗ (memRegion a 480 ∗ memRegion (a + 864#64) 16 ∗ memRegion (s0.sp - 4160#64) 32))
        (Q := fun sc => sc.sp = s0.sp ∧ sc.trace = s0.trace ∧
          sc.readReg64 .x0 = a + 480#64 ∧ sc.readReg64 .lr = s0.readReg64 .lr ∧
          AllocCallPreserved s0 sc ∧ CalleeSavedPreserved s0 sc) ?_ ?_
      · by_vm_steps (
          dsimp only [savedFrame32]; wp_steps
          refine SepWP.focus_weaken
            (Entails.trans
              (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old)
              (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)))
            (by sep_focus) ?_
          refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
      · intro sc hpcc hrunc hclc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hacp_c, hcs_c⟩
        have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
          (callerProg := lsProg_276 (Rust.withPanics ext)) hdealloc hclc
        dsimp only [lsProg_276, withMemEq, dropGlueSortedSetPt16Spec] at hpt16_raw
        have ⟨_, _, _, _, _, _, _⟩ := hacp_c
        have hlr_sc : LsRetAddr624 (sc.readReg64 .lr) := hlr_c ▸ hlr0
        have _hlr_sc_gpr : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := hlr_sc
        rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
        wp_call hpt16_raw (⟨a + 480#64, vecs⟩, st4)
        rw [hsp_c]
        have hacp_cf : AllocCallPreserved sc sf := by assumption
        have hevs_w : FreeOnlyEvs w := by assumption
        have hacp_f : AllocCallPreserved s0 sf := hacp_c.trans hacp_cf
        have ⟨_, _, _, _, _, _, _⟩ := hacp_f
        have hstack64_join : memRegion (s0.sp - 4160#64) 32 ∗ stackAt s0.sp dropGluePoly16Stack ⊢
            stackAt s0.sp dropStackPoly64 :=
          Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm
        refine SepWP.weaken_pre
          (Entails.trans
            (Entails.of_eq (show _ = (memRegion a 480 ∗ memRegion (a + 480#64) polyArrayBytes ∗
              memRegion (a + 864#64) 16) ∗ A.pool lim (M.stepEvents w st4) sf ∗
              (memRegion (s0.sp - 4160#64) 32 ∗ stackAt s0.sp dropGluePoly16Stack) by sep_ac_rfl))
            (sepConj_mono (chunked_880_join a) (sepConj_mono_right hstack64_join))) ?_
        refine SepWP.mono (post := fun sf' Pf =>
            (Pf ⊢ memRegion a 880 ∗ A.pool lim (M.stepEvents w st4) sf' ∗ stackAt s0.sp dropStackPoly64) ∧
            (sf'.sp = s0.sp ∧ sf'.trace = s0.trace ∧ AllocCallPreserved s0 sf' ∧ CalleeSavedPreserved s0 sf'))
          (by wp_done) (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)

theorem drop_chunked_header_sent_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 276 (Rust.withPanics ext)) (lsmpl.base 276)
      (withLsCodeLoaded lsmpl (dropChunkedHeaderSentSpec M A lim F)) :=
  ls_to_blockProgram (drop_chunked_header_sent_cl_placed_ok hdealloc)

theorem drop_chunked_header_sent_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 276)
      (withLsCodeLoaded lsmpl (dropChunkedHeaderSentSpec M A lim F)) :=
  ls_subroutine_ok_of_block (drop_chunked_header_sent_cl_placed_ok hdealloc) hidx

theorem drop_chunked_header_sent_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 276)
      (withMemEq m (dropChunkedHeaderSentSpec M A lim F)) :=
  lscall_blk_cl (drop_chunked_header_sent_cl_placed_ok hdealloc) hcl hidx

end LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
