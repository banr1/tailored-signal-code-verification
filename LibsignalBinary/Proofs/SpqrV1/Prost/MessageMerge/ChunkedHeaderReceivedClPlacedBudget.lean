/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedBudgetSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedUcClPlacedBudget

/-!
# Code-Loaded Placed Budget Wrapper for `Chunked.HeaderReceived::merge` (Block `306`)

Re-exports the `withLsCodeRoLoaded lsmpl` budget-threaded inner and outer step, loop, and top-level
contracts for `Chunked.HeaderReceived::merge` on Block `306`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedClPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedUcClPlacedBudget
  (chunkedHeaderReceived_from_err_exit_cl_placed
   chunkedHeaderReceived_push_ret_exit_cl_placed
   chunkedHeaderReceived_uc_push_exit_cl_placed
   chunkedHeaderReceived_uc_from_push_exit_cl_placed
   chunkedHeaderReceived_uc_field_push_exit_cl_placed
   chunkedHeaderReceived_uc_skip_step_cl_placed
   chunkedHeaderReceived_uc_tag1_varint_step_cl_placed
   chunkedHeaderReceived_uc_tag1_wt_err_step_cl_placed
   chunkedHeaderReceived_uc_tag2_step_cl_placed
   chunkedHeaderReceived_uc_tag3_step_cl_placed
   chunkedHeaderReceived_uc_loop_le_exit_cl_placed
   chunkedHeaderReceived_uc_decode_key_step_cl_placed
   chunkedHeaderReceived_uc_loop_ok_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedBudgetAux
  (chunkedHeaderReceived_decode_key_step_cl_placed
   chunkedHeaderReceived_loop_le_exit_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedBudgetSteps
  (chunkedHeaderReceived_skip_step_cl_placed
   chunkedHeaderReceived_tag1_step_cl_placed
   chunkedHeaderReceived_tag2_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedBudget
  (chunkedHeaderReceived_loop_ok_cl_placed
   chunked_header_received_merge_cl_placed_ok_of_contracts)

alias chunkedHeaderReceived_merge_cl_placed_ok_of_contracts :=
  chunked_header_received_merge_cl_placed_ok_of_contracts

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedClPlacedBudget
