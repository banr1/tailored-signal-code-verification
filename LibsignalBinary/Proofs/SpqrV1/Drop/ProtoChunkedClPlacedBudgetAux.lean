/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2Budget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# Budget-Threaded Code-Loaded Drop Glue for Leaf PB Blocks and `Ct1Received` (`282..286, 288`)

Proves `withLsCodeLoaded lsmpl` subroutine contracts under `RustCliAllocBudget M` (`FreeOnlyEvs`)
for leaf Blocks `283..286` and `288` and composite Block `282` (`chunked::Ct1Received`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkPC_282 blkPl_282 extract_withLsCodeLoaded libsignalSessionLib
  lsProg_282 lsProg_283 lsProg_284 lsProg_285 lsProg_286
  ls_blockPlacement_base ls_subroutine_ok_of_block lscall_blk_cl
  lsmpl lsρ sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain
  withLsCodeLoaded withMemEq
)
open CryptoVerification.LibsignalSpqrV1 (pbToProtoPolyEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop.Blk337_338 (lsProg_288)
open CryptoVerification.SpqrV1.Drop (
  DropProtoChunkedCt1ReceivedGhost DropProtoChunkedEkSentCt1ReceivedGhost
  DropProtoChunkedHeaderReceivedGhost DropProtoChunkedNoHeaderReceivedGhost
  DropProtoEpochSliceGhost DropProtoUnchunkedCt1SentEkReceivedGhost
  Saved32x20Preserved auth48HeadersAt auth48HeadersAt_entails_memRegion_48
  cap_add_one_beq_zero_false dropStack48
  none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
  optProtoAuthenticatorAt_48_none optProtoAuthenticatorAt_48_none_entails_memRegion_48
  optProtoAuthenticatorAt_some optProtoPolyEncoder_none_entails_memRegion_56
  optProtoPolynomialEncoderAt_none' optProtoPolynomialEncoderAt_some'
  optProtoUnchunked2Vec_none_entails_memRegion_104
  optProtoUnchunkedEkSentCt1ReceivedAt_none optProtoUnchunkedEkSentCt1ReceivedAt_some
  protoAuthenticatorAt_entails_dealloc protoChunkedCt1ReceivedAt
  protoChunkedCt1ReceivedSize protoPolynomialEncoderAt_expose_cap
  protoPolynomialEncoderAt_unexpose_cap protoUnchunked2VecHeadersAt
  protoUnchunked2VecHeadersAt_entails_memRegion_104'
  protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc
  stackAt_allocHook16_split_bottom stackAt_dropStack48_split32
  stack_restore_48_from_32 twoVecHeadersAt twoVecHeadersAt_48_eq vecCapPtrDealloc
)
open CryptoVerification.SpqrV1.Poly (
  optProtoPolynomialEncoderAt protoPolynomialEncoderAt protoPolynomialEncoderSize
)
open CryptoVerification.SpqrV1.States.Recv (spqrRustDeallocSym)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (
  dropProtoEpochSliceSpec drop_proto_epoch_slice_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget (
  dropProtoChunkedCt1ReceivedSpec dropProtoChunkedEkSentCt1ReceivedSpec
  dropProtoChunkedHeaderReceivedSpec dropProtoChunkedNoHeaderReceivedSpec
  drop_proto_chunked_no_header_received_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2Budget (
  drop_proto_chunked_ek_sent_ct1_received_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2BudgetAux (
  align_pre_st align_pre_vm deallocFreeOnlySpec
  drop_proto_chunked_header_received_placed_ok
  sepWP_close_drop sepWP_evs_dealloc sepWP_evs_nil sepWP_vm_evs_nil
  seq_clean_evs seq_vm_clean subroutine_ok_deallocFreeOnly
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (
  dropProtoUnchunkedCt1SentEkReceivedSpec
  drop_proto_unchunked_ct1_sent_ek_received_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget (
  drop_glue_proto_poly_encoder_mem_on
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux (
  ls_to_blockProgram seq_vm_clean_lscl subroutine_ok_withLsCodeLoaded_intro
)

namespace LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## `withLsCodeLoaded` Event-Sequencing Helper -/

theorem seq_clean_evs_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ hcl' =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hcl' hQ))

/-! ## Leaf Single-Block Wrappers (`283, 284, 285, 286, 288`) -/

theorem drop_proto_chunked_header_received_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_283 (Rust.withPanics ext)) (lsmpl.base 283)
      (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderReceivedSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 283)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_proto_chunked_header_received_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_proto_chunked_header_received_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 283 (Rust.withPanics ext)) (lsmpl.base 283)
      (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderReceivedSpec M A lim)) :=
  ls_to_blockProgram (drop_proto_chunked_header_received_cl_placed_ok hdealloc)

theorem drop_proto_chunked_header_received_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 283)
      (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderReceivedSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_proto_chunked_header_received_cl_placed_ok hdealloc) hidx

theorem drop_proto_chunked_header_received_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 283)
      (withMemEq m (dropProtoChunkedHeaderReceivedSpec M A lim)) :=
  lscall_blk_cl (drop_proto_chunked_header_received_cl_placed_ok hdealloc) hcl hidx

theorem drop_proto_chunked_no_header_received_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_284 (Rust.withPanics ext)) (lsmpl.base 284)
      (withLsCodeLoaded lsmpl (dropProtoChunkedNoHeaderReceivedSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 284)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_proto_chunked_no_header_received_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_proto_chunked_no_header_received_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 284 (Rust.withPanics ext)) (lsmpl.base 284)
      (withLsCodeLoaded lsmpl (dropProtoChunkedNoHeaderReceivedSpec M A lim)) :=
  ls_to_blockProgram (drop_proto_chunked_no_header_received_cl_placed_ok hdealloc)

theorem drop_proto_chunked_no_header_received_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 284)
      (withLsCodeLoaded lsmpl (dropProtoChunkedNoHeaderReceivedSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_proto_chunked_no_header_received_cl_placed_ok hdealloc) hidx

theorem drop_proto_chunked_no_header_received_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 284)
      (withMemEq m (dropProtoChunkedNoHeaderReceivedSpec M A lim)) :=
  lscall_blk_cl (drop_proto_chunked_no_header_received_cl_placed_ok hdealloc) hcl hidx

theorem drop_proto_chunked_ek_sent_ct1_received_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_285 (Rust.withPanics ext)) (lsmpl.base 285)
      (withLsCodeLoaded lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 285)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_proto_chunked_ek_sent_ct1_received_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_proto_chunked_ek_sent_ct1_received_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 285 (Rust.withPanics ext)) (lsmpl.base 285)
      (withLsCodeLoaded lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)) :=
  ls_to_blockProgram (drop_proto_chunked_ek_sent_ct1_received_cl_placed_ok hdealloc)

theorem drop_proto_chunked_ek_sent_ct1_received_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 285)
      (withLsCodeLoaded lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_proto_chunked_ek_sent_ct1_received_cl_placed_ok hdealloc) hidx

theorem drop_proto_chunked_ek_sent_ct1_received_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 285)
      (withMemEq m (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)) :=
  lscall_blk_cl (drop_proto_chunked_ek_sent_ct1_received_cl_placed_ok hdealloc) hcl hidx

theorem drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_286 (Rust.withPanics ext)) (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 286)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_proto_unchunked_ct1_sent_ek_received_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_proto_unchunked_ct1_sent_ek_received_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 286 (Rust.withPanics ext)) (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
  ls_to_blockProgram (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hdealloc)

theorem drop_proto_unchunked_ct1_sent_ek_received_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hdealloc) hidx

theorem drop_proto_unchunked_ct1_sent_ek_received_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 286)
      (withMemEq m (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
  lscall_blk_cl (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hdealloc) hcl hidx

theorem drop_proto_epoch_slice_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_288 (Rust.withPanics ext)) (lsmpl.base 288)
      (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 288)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_proto_epoch_slice_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_proto_epoch_slice_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 288 (Rust.withPanics ext)) (lsmpl.base 288)
      (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)) :=
  ls_to_blockProgram (drop_proto_epoch_slice_cl_placed_ok hdealloc)

theorem drop_proto_epoch_slice_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 288)
      (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_proto_epoch_slice_cl_placed_ok hdealloc) hidx

theorem drop_proto_epoch_slice_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 288)
      (withMemEq m (dropProtoEpochSliceSpec M A lim)) :=
  lscall_blk_cl (drop_proto_epoch_slice_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `282`: `drop_glue::<proto::pq_ratchet::v1_state::chunked::Ct1Received>` -/

theorem drop_proto_chunked_ct1_received_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_282 (Rust.withPanics ext)) (lsmpl.base 282)
      (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 282)]
  change subroutine_ok ((blkPC_282).rebase (blkPl_282).base (Rust.withPanics ext)) (blkPl_282).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_282).rebase (blkPl_282).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (prog := lsProg_282 (Rust.withPanics ext)) hdealloc
  simp only [spqrRustDeallocSym] at hdealloc_raw
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  clear hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropProtoChunkedCt1ReceivedSpec, protoChunkedCt1ReceivedSize] at *
  wp_init x_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  rcases x_st with ⟨⟨a, st_pb⟩, st⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  dsimp only [DropProtoChunkedCt1ReceivedGhost.a, DropProtoChunkedCt1ReceivedGhost.st,
    protoChunkedCt1ReceivedAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  have hsub_4144 : (s0.sp - 32#64) - 4112#64 = s0.sp - 4144#64 := by bv_omega
  nth_rw 1 [stackAt_dropStack48_split32 s0.sp]
  nth_rw 1 [stackAt_allocHook16_split_bottom (s0.sp - 32#64)]
  rw [hsub_4144]
  cells_unfold
  wp_pull_exists
  rename_i fp_old lr_old x20_old x19_old
  refine seq_clean_evs_lscl hcl (mid := (blkPl_282).base + 116#64)
    (P_evs := fun evs sm =>
      (memRegion a 104 ∗
        optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x19 = a)
    ?_ ?_
  · cases huc : st_pb.uc with
    | none =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_none]
      refine sepWP_vm_evs_nil (fun sm hvm => by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
      by_vm_steps (
        wp_steps
        refine SepWP.focus_weaken
          (optProtoUnchunked2Vec_none_entails_memRegion_104 a)
          (by sep_focus) ?_
        refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
        wp_done)
    | some u =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_some]
      refine SepWP.weaken_pre
        (sepConj_mono_left (protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc A.repAlloc a u)) ?_
      wp_pull_exists; rename_i g
      wp_focus_pure; intro hcap1_lt
      have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
      refine seq_clean_evs (mid := (blkPl_282).base + 76#64)
        (P_evs := fun evs sm =>
          ((protoUnchunked2VecHeadersAt a g ∗
            memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
            vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
            vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
            optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
        ?_ ?_
      · cases hauth : u.auth with
        | none =>
          rw [optProtoAuthenticatorAt_48_none]
          dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt]
          refine sepWP_vm_evs_nil (fun sm hvm => by
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
          by_vm_steps (
            wp_steps
            refine SepWP.focus_weaken
              (optProtoAuthenticatorAt_48_none_entails_memRegion_48 A.repAlloc a)
              (by sep_focus) ?_
            refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done)
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken
            (protoAuthenticatorAt_entails_dealloc A.repAlloc (a + 48#64) auth)
            (by sep_focus) ?_
          wp_pull_exists; rename_i ga
          rw [twoVecHeadersAt_48_eq]
          wp_focus_pure; intro hga_lt
          have hne_nonea := cap_add_one_beq_zero_false hga_lt
          refine seq_clean_evs (mid := (blkPl_282).base + 56#64)
            (P_evs := fun evs sm =>
              ((protoUnchunked2VecHeadersAt a g ∗
                (auth48HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                memRegion (a + 96#64) 8 ∗
                vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
                optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
              A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
            ?_ ?_
          · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt,
              vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
              simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · refine sepWP_vm_evs_nil (fun sm hvm => by
                simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
              by_vm_steps (
                wp_steps
                refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
                wp_done)
            · apply sepWP_evs_dealloc ga.v1.cap.toNat 1
              refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
                (P_mid :=
                  A.pool lim st s0 ∗ A.live ga.v1.ptr ga.v1.cap.toNat 1 ∗ memRegion ga.v1.ptr ga.v1.cap.toNat ∗
                  stackAt (s0.sp - 32#64) allocHookStack ∗
                  (((protoUnchunked2VecHeadersAt a g ∗
                     (auth48HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                     memRegion (a + 96#64) 8 ∗
                     vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                     vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
                    optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
                   memRegion (s0.sp - 4144#64) 16 ∗
                   (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
                (Q := fun sc => Saved32x20Preserved s0 sc (s0.sp - 32#64) ∧ AllocCallPreserved s0 sc ∧
                  sc.readReg64 .x0 = ga.v1.ptr ∧ sc.readReg64 .x1 = ga.v1.cap ∧ sc.readReg64 .x2 = 1#64 ∧
                  sc.readReg64 .lr = (blkPl_282).base + 56#64 ∧
                  sc.readReg64 .x19 = a ∧ sc.readReg64 .x20 = g.v1.cap)
                ?_ ?_
              · by_vm_steps (
                  wp_steps
                  dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt,
                    vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
                  refine align_pre_vm (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
                  wp_done)
              · intro sc hpcc hrunc hvmc ⟨hpres_c, hacp_c, hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c⟩
                rcases hpres_c with ⟨hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hsp_c, htrace_c, hvregs_c⟩
                have ⟨_, _, _, _, _, _, _⟩ := hacp_c
                rw [← A.pool_of_vmPreserved hvmc, ← hsp_c, ← hlr_c]
                have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
                  change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
                  simp (config := { decide := true }) only [arm64_norm, wp_norm]
                wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, st)
                rw [hsp_c, hlr_c]
                have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
                rcases hacp' with ⟨_, _, _, _, _, _, _⟩
                dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt,
                  vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
                refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
                wp_done
          · intro evsa1 sa1 hevsa1 hpca1 hruna1 ⟨⟨hx21_a1, hx22_a1, hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hacp_a1, hx19_a1, hx20_a1⟩
            have ⟨_, _, _, _, _, _, _⟩ := hacp_a1
            let sta1 := M.stepEvents evsa1 st
            dsimp only [auth48HeadersAt, vecCapPtrDealloc,
              LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
              simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · refine SepWP.mono (post := fun sm Pm =>
                  (Pm ⊢
                    ((protoUnchunked2VecHeadersAt a g ∗
                      memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
                      vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                      vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
                      optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
                    A.pool lim sta1 sm ∗
                    (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
                    (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                     ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                  Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
                  sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
                ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                  ⟨evsa1, hevsa1,
                    Entails.trans hp (Entails.of_eq (by
                      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, sta1]
                      sep_ac_rfl)),
                    hq⟩)
              dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
              wp_steps
              refine SepWP.focus_weaken (auth48HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              wp_done
            · refine SepWP.mono (post := fun sm Pm =>
                  (Pm ⊢
                    ((protoUnchunked2VecHeadersAt a g ∗
                      memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
                      vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                      vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
                      optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
                    A.pool lim (M.stepEvents (rustDeallocEvents ga.v2.cap.toNat 1) sta1) sm ∗
                    (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
                    (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                     ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                  Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
                  sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
                ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                  ⟨evsa1 ++ rustDeallocEvents ga.v2.cap.toNat 1,
                    hevsa1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 ga.v2.cap.toNat),
                    Entails.trans hp (Entails.of_eq (by
                      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
                      simp only [sta1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
                      sep_ac_rfl)),
                    hq⟩)
              dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
              wp_steps
              wp_apply
              rw [hsp_a1]
              have hacp' : AllocCallPreserved s0 sf := hacp_a1.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              refine SepWP.focus_weaken (auth48HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              wp_done
      · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx20_1⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_1
        let st1 := M.stepEvents evs1 st
        refine seq_clean_evs (mid := (blkPl_282).base + 96#64)
          (P_evs := fun evs sm =>
            ((protoUnchunked2VecHeadersAt a g ∗
              memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
              vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
              optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
            A.pool lim (M.stepEvents evs st1) sm ∗
            (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc,
            LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc1 : (g.v1.cap == 0#64) = true <;>
            simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            wp_steps; wp_done
          · apply sepWP_evs_dealloc g.v1.cap.toNat 1
            wp_steps
            wp_apply
            rw [hsp_1]
            have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done
        · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_2
          let st2 := M.stepEvents evs2 st1
          dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc,
            LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc2 : (g.v2.cap == 0#64) = true <;>
            simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · refine SepWP.mono (post := fun sm Pm =>
                (Pm ⊢
                  (memRegion a 104 ∗
                    optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
                  A.pool lim st2 sm ∗
                  (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
                  (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = a)
              ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                ⟨evs1 ++ evs2, hevs1.append hevs2,
                  Entails.trans hp (Entails.of_eq (by
                    simp only [st1, st2, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
                    sep_ac_rfl)),
                  hq⟩)
            wp_steps
            refine SepWP.focus_weaken
              (protoUnchunked2VecHeadersAt_entails_memRegion_104' a g)
              (by sep_focus) ?_
            wp_done
          · refine SepWP.mono (post := fun sm Pm =>
                (Pm ⊢
                  (memRegion a 104 ∗
                    optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
                  A.pool lim (M.stepEvents (rustDeallocEvents g.v2.cap.toNat 1) st2) sm ∗
                  (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
                  (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = a)
              ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                ⟨evs1 ++ evs2 ++ rustDeallocEvents g.v2.cap.toNat 1,
                  (hevs1.append hevs2).append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 g.v2.cap.toNat),
                  Entails.trans hp (Entails.of_eq (by
                    simp only [st1, st2, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
                    sep_ac_rfl)),
                  hq⟩)
            wp_steps
            wp_apply
            rw [hsp_2]
            have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine SepWP.focus_weaken
              (protoUnchunked2VecHeadersAt_entails_memRegion_104' a g)
              (by sep_focus) ?_
            refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done
  · intro evs3 s3 hevs3 hpc3 hrun3 hcl3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_3
    let st3 := M.stepEvents evs3 st
    cases hek : st_pb.sendingEk with
    | none =>
      simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
      have h112 : (a + 104#64) + 8#64 = a + 112#64 := BitVec.add_assoc a 104#64 8#64
      rw [h112]
      refine sepWP_close_drop
        (fun sf => memRegion a 160 ∗ A.pool lim st3 sf ∗ stackAt s0.sp dropStack48)
        ?_
        (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · wp_steps
        have hjoin : memRegion a 104 ∗ ((a + 104#64) ↦₆₄ noneCap) ∗ memRegion (a + 112#64) 48 ⊢
            memRegion a 160 := by
          rw [← h112,
              ProofLib.memRegion_split' (b := a) (n := 104) (k := 56) (b' := a + 104#64) rfl rfl (by decide)]
          exact sepConj_mono_right (optProtoPolyEncoder_none_entails_memRegion_56 (a + 104#64))
        refine SepWP.focus_weaken hjoin (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_from_32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by sep_focus) ?_
        wp_done
      · rw [satisfies_sepExists]
        refine ⟨evs3, ?_⟩
        rw [satisfies_pure_sepConj]
        refine ⟨⟨htr_f, hacp_f, hevs3⟩, ?_⟩
        exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
    | some enc =>
      simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
      refine SepWP.focus_weaken
        (protoPolynomialEncoderAt_expose_cap A.repAlloc (a + 104#64) (pbToProtoPolyEncoder enc))
        (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr
      wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      refine seq_vm_clean_lscl hcl3 (mid := lsmpl.base 271)
        (P_mid :=
          protoPolynomialEncoderAt A.repAlloc (a + 104#64) (pbToProtoPolyEncoder enc) ∗
          A.pool lim st3 s3 ∗ stackAt s0.sp dropStack48 ∗
          memRegion a 104)
        (Q := fun sc => sc.sp = s0.sp ∧ sc.trace = s0.trace ∧
          sc.readReg64 .x0 = a + 104#64 ∧ sc.readReg64 .lr = s0.readReg64 .lr ∧
          AllocCallPreserved s0 sc ∧ CalleeSavedPreserved s0 sc)
        ?_ ?_
      · by_vm_steps (
          wp_steps
          refine SepWP.focus_weaken
            (protoPolynomialEncoderAt_unexpose_cap A.repAlloc (a + 104#64) cap ptr (pbToProtoPolyEncoder enc))
            (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_from_32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x20) (s0.readReg64 .x19))
            (by sep_focus) ?_
          refine align_pre_vm (by sep_ac_rfl) ?_
          wp_done)
      · intro sc hpcc hrunc hclc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hacp_c, hcs_c⟩
        have hpoly_enc_raw := drop_glue_proto_poly_encoder_mem_on
          (callerProg := lsProg_282 (Rust.withPanics ext)) hdealloc hclc
        dsimp only [lsProg_282, withMemEq, dropProtoPolyEncoderSpec] at hpoly_enc_raw
        have ⟨_, _, _, _, _, _, _⟩ := hacp_c
        rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
        have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
          change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]; assumption
        wp_call hpoly_enc_raw (⟨a + 104#64, pbToProtoPolyEncoder enc⟩, st3)
        rw [hsp_c]
        have hacp_cf : AllocCallPreserved sc sf := by assumption
        have hevs_w : FreeOnlyEvs w := by assumption
        have hacp_f : AllocCallPreserved s0 sf := hacp_c.trans hacp_cf
        have ⟨_, _, _, _, _, _, _⟩ := hacp_f
        have hjoin : memRegion a 104 ∗ memRegion (a + 104#64) protoPolynomialEncoderSize ⊢
            memRegion a 160 := by
          rw [show (160 : Nat) = 104 + protoPolynomialEncoderSize from rfl,
              ProofLib.memRegion_split a 104 protoPolynomialEncoderSize (by decide)]
          exact Entails.refl _
        refine SepWP.focus_weaken hjoin (by sep_focus) ?_
        refine sepWP_close_drop
          (fun sf' => memRegion a 160 ∗ A.pool lim (M.stepEvents w st3) sf' ∗ stackAt s0.sp dropStack48)
          (by wp_done)
          (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        rw [satisfies_sepExists]
        refine ⟨evs3 ++ w, ?_⟩
        rw [satisfies_pure_sepConj]
        refine ⟨⟨htr_f, hacp_f', hevs3.append hevs_w⟩, ?_⟩
        have heq_st : M.stepEvents (evs3 ++ w) st = M.stepEvents w st3 := by
          simp only [st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        rw [heq_st]
        exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

theorem drop_proto_chunked_ct1_received_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext)) (lsmpl.base 282)
      (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)) :=
  ls_to_blockProgram (drop_proto_chunked_ct1_received_cl_placed_ok hdealloc)

theorem drop_proto_chunked_ct1_received_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 282)
      (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_proto_chunked_ct1_received_cl_placed_ok hdealloc) hidx

theorem drop_proto_chunked_ct1_received_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 282)
      (withMemEq m (dropProtoChunkedCt1ReceivedSpec M A lim)) :=
  lscall_blk_cl (drop_proto_chunked_ct1_received_cl_placed_ok hdealloc) hcl hidx

end LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlacedBudgetAux
