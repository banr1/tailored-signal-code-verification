/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedBudgetSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedClPlaced

/-!
# Code-Loaded Placed Budget Wrapper for `Chunked.NoHeaderReceived::merge` (Block `308`)

Re-exports the `withLsCodeRoLoaded lsmpl` budget-threaded step, loop, and top-level contracts for
`Chunked.NoHeaderReceived::merge` on Block `308`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedClPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedBudgetAux
  (chunkedNoHeaderReceived_loop_le_exit_cl_placed
   chunkedNoHeaderReceived_decode_key_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedBudgetSteps
  (chunkedNoHeaderReceived_skip_step_cl_placed
   chunkedNoHeaderReceived_tag1_step_cl_placed
   chunkedNoHeaderReceived_tag2_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedBudget
  (chunkedNoHeaderReceived_loop_ok_cl_placed
   chunked_no_header_received_merge_cl_placed_ok_of_contracts)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedClPlacedBudget
