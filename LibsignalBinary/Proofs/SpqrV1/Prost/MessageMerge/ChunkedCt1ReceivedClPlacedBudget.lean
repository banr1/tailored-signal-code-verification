/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedClPlaced

/-!
# Budget-Threaded Code-Loaded `[LibsignalPlacement]` `Chunked.Ct1Received::merge` Re-Exports (Block `303`)

Re-exports the budget-threaded `[LibsignalPlacement]` `withLsCodeRoLoaded lsmpl` error-exit,
field-step, key-decode, loop, and top-level Block `303` contracts from
`ChunkedCt1ReceivedBudgetAux`, `ChunkedCt1ReceivedBudgetAux2`, and `ChunkedCt1ReceivedBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedClPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux
  (ct1Received_ret_err_exit_placed
   ct1Received_from_err_exit_cl_placed
   ct1Received_push_err_exit_cl_placed
   ct1Received_skip_step_cl_placed
   ct1Received_decode_key_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux2
  (ct1Received_tag1_init_step_budget_placed
   ct1Received_tag1_step_cl_placed
   ct1Received_tag2_init_step_budget_placed
   ct1Received_tag2_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudget
  (ct1Received_loop_le_exit_cl_placed
   ct1Received_loop_ok_cl_placed
   chunkedCt1Received_merge_cl_placed_ok_of_contracts
   chunkedCt1Received_merge_placed_ok_of_contracts
   chunkedCt1ReceivedMerge_cl_placed_ok_of_contracts
   chunkedCt1ReceivedMerge_placed_ok_of_contracts
   chunked_ct1_received_merge_cl_placed_ok_of_contracts
   chunked_ct1_received_merge_placed_ok_of_contracts)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedClPlacedBudget
