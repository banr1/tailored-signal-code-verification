/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare

/-!
# `HookSat` Sibling of `States.Recv.TopPlacedBudget` (`TopPlacedBudgetSat`)

Replaces `[HkdfPlacedHooks F (Rust.withPanics ext)]` in
`statesRecvPlacedContracts_of_ro_leaves` (`:198`) and `states_recv_placed_ok_x_closed` (`:274`)
of `States.Recv.TopPlacedBudget.lean` with `[HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudgetSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement ls_subroutine_ok_of_block)
open CryptoVerification.LibsignalSpqrV1 (
  MlKem mlkemDecapsSpec mlkemEncaps2Spec mlkemValidatePkSpec
)
open CryptoVerification.LibsignalTripleRatchet (
  keys_ls_subroutine_ok_of_block_cro memsetName sessionMemmoveSpec
)
open CryptoVerification.SpqrV1.Alloc (growOneStack spqrMemmoveSym)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (spqrMlkemDecapsSym)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym spqrMlkemEncaps2Sym)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1PlacedBudget (add_chunk_cl_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudget (
  polyDecoderDecodedMessage_cro_placed_ok_x
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudget (
  ct1_acknowledged_recv_ek_chunk_placed_closed_ok_x
  ct1_received_recv_ct2_chunk_placed_ok_x
  ek_received_ct1_sampled_recv_ct1_ack_placed_ok_x
  header_sent_recv_ct1_chunk_placed_ok_x
  hookSat_sessionMemcpyBudget_of_framelessAcp
  hookSat_sessionMemcpyRegionBudget_of_framelessAcp
  hookSat_sessionShimBudget_of_rustAllocShimVm
  hookSat_withVmPreserved_memcpyRO_of_ro
  hookSat_withVmPreserved_noAllocShim_of_rustAllocShimVm
  keys_sampled_recv_ct1_chunk_placed_ok_x
  noHeaderReceived_recv_hdr_chunk_placed_closed_okX
  send_ct2_encoder_placed_ok_x_of_rustAllocShimVm
  unchunked_ct1_sent_recv_ek_placed_cl_twoEnv_ok_x
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudgetSat (
  ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x_sat
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlacedBudget (
  ct2_sampled_recv_next_epoch_placed_ok_x
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudget (
  unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget (
  StatesRecvExactEnv states_recv_placed_ok_x
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (RecvCt2PlacedAlloc)
open LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget (StatesRecvPlacedOkXOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

theorem statesRecvPlacedContracts_of_ro_leaves_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hval_pk_sat : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K)))
    (hencaps2_sat : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym
      (withVmPreserved (mlkemEncaps2Spec K)))
    (hdecaps_sat : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac_sat : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec F M A lim)) :
    DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext :=
  let hmemcpy_reg_sat :=
    hookSat_sessionMemcpyRegionBudget_of_framelessAcp hA.memcpy
  let hshim_sess :=
    hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim
  DefsPlacedBudget.StatesRecvPlacedContracts.of_callees
    (ls_subroutine_ok_of_block (i := 332) (j := 370)
      (keys_sampled_recv_ct1_chunk_placed_ok_x
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc hmemcpy_reg_sat hmemmove_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 337)
      (header_sent_recv_ct1_chunk_placed_ok_x
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc
        hmemcpy_reg_sat hmemmove_sat hmemset_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 346)
      (ct1_received_recv_ct2_chunk_placed_ok_x
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc hmemcpy_reg_sat hmemmove_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 350)
      (ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x_sat
        hA hmemcpy_reg_sat hmemmove_sat hmemset_sat hdecaps_sat hhmac_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 369)
      (noHeaderReceived_recv_hdr_chunk_placed_closed_okX
        hA.shim hA.alloc hA.realloc hA.dealloc hA.memcpy hmemcpy_reg_sat hA.memcpyRO
        hmemmove_sat hmemset_sat hhmac_sat
        hA.handleError hA.assertFailedU64 hA.sliceIndexFail hA.panicBoundsCheck))
    (ls_subroutine_ok_of_block (i := 332) (j := 419)
      (add_chunk_cl_placed_ok_x
        hA.handleError hA.shim hA.alloc hA.realloc hmemmove_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 418)
      (polyDecoderDecodedMessage_cro_placed_ok_x
        hA.handleError hshim_sess hA.alloc hA.realloc hA.dealloc hmemcpy_reg_sat hmemset_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 338)
      (unchunked_ct1_sent_recv_ek_placed_cl_twoEnv_ok_x
        (F := F) hA.dealloc hval_pk_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 347)
      (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc
        hA.memcpy hA.memcpyRO hencaps2_sat hhmac_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 382)
      (send_ct2_encoder_placed_ok_x_of_rustAllocShimVm
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc hmemcpy_reg_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 343)
      (ek_received_ct1_sampled_recv_ct1_ack_placed_ok_x
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc
        hA.memcpy hmemcpy_reg_sat hA.memcpyRO hencaps2_sat hhmac_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 349)
      (ct1_acknowledged_recv_ek_chunk_placed_closed_ok_x
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc
        hA.memcpy hmemcpy_reg_sat hA.memcpyRO hmemmove_sat hmemset_sat
        hval_pk_sat hencaps2_sat hhmac_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 355)
      (ct2_sampled_recv_next_epoch_placed_ok_x hA.dealloc))
    (hookSat_withVmPreserved_noAllocShim_of_rustAllocShimVm hA.shim)
    hA.alloc
    hA.dealloc
    (hookSat_sessionMemcpyBudget_of_framelessAcp hA.memcpy)
    (hookSat_withVmPreserved_memcpyRO_of_ro hA.memcpyRO)

theorem states_recv_placed_ok_x_closed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hval_pk_sat : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K)))
    (hencaps2_sat : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym
      (withVmPreserved (mlkemEncaps2Spec K)))
    (hdecaps_sat : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac_sat : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec F M A lim)) :
    StatesRecvPlacedOkXOfEnv M A lim F K ext (StatesRecvExactEnv K) :=
  states_recv_placed_ok_x A lim F K ext
    (statesRecvPlacedContracts_of_ro_leaves_sat
      hA hmemmove_sat hmemset_sat hval_pk_sat hencaps2_sat hdecaps_sat hhmac_sat)

end LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudgetSat
