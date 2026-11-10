/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedBudgetSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedClPlaced

/-!
# Code-Loaded Placed Budget Wrapper for `Chunked.EkSentCt1Received::merge` (Block `309`)

Re-exports the `withLsCodeRoLoaded lsmpl` budget-threaded exit, step, loop, and top-level contracts
for `Chunked.EkSentCt1Received::merge` on Block `309`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedClPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedBudgetAux
  (ekSentCt1Received_from_err_exit_cl_placed
   ekSentCt1Received_push_err_exit_cl_placed
   ekSentCt1Received_loop_le_exit_cl_placed
   ekSentCt1Received_decode_key_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedBudgetSteps
  (ekSentCt1Received_skip_step_cl_placed
   ekSentCt1Received_tag1_step_cl_placed
   ekSentCt1Received_tag2_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedBudget
  (ekSentCt1Received_loop_ok_cl_placed
   chunked_ek_sent_ct1_received_merge_cl_placed_ok_of_contracts)

alias chunkedEkSentCt1Received_merge_cl_placed_ok_of_contracts :=
  chunked_ek_sent_ct1_received_merge_cl_placed_ok_of_contracts

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedClPlacedBudget
