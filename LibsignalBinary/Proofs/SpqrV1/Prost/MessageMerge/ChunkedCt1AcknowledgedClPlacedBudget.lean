/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedBudgetSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedClPlaced

/-!
# Budget-Threaded Code-Loaded `[LibsignalPlacement]` `Chunked.Ct1Acknowledged::merge` Re-Exports (Block `307`)

Re-exports the budget-threaded `[LibsignalPlacement]` `withLsCodeRoLoaded lsmpl` error-exit,
step, loop, and top-level Block `307` contracts from `ChunkedCt1AcknowledgedBudgetAux`,
`ChunkedCt1AcknowledgedBudgetSteps`, and `ChunkedCt1AcknowledgedBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedClPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedBudgetAux
  (ct1Acknowledged_from_err_exit_cl_placed
   ct1Acknowledged_push_err_exit_cl_placed
   ct1Acknowledged_loop_le_exit_cl_placed
   ct1Acknowledged_decode_key_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedBudgetSteps
  (ct1Acknowledged_skip_step_cl_placed
   ct1Acknowledged_tag1_step_cl_placed
   ct1Acknowledged_tag2_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedBudget
  (ct1Acknowledged_loop_ok_cl_placed
   chunked_ct1_acknowledged_merge_cl_placed_ok_of_contracts)

alias chunkedCt1Acknowledged_merge_cl_placed_ok_of_contracts :=
  chunked_ct1_acknowledged_merge_cl_placed_ok_of_contracts

alias chunked_ct1_acknowledged_merge_placed_ok_of_contracts :=
  chunked_ct1_acknowledged_merge_cl_placed_ok_of_contracts

alias chunkedCt1Acknowledged_merge_placed_ok_of_contracts :=
  chunked_ct1_acknowledged_merge_cl_placed_ok_of_contracts

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedClPlacedBudget
