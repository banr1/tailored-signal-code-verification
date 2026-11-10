/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledBudgetSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledUcClPlacedBudget

/-!
# Code-Loaded Placed Budget Wrapper for `Chunked.EkReceivedCt1Sampled::merge` (Block `310`)

Re-exports the `withLsCodeRoLoaded lsmpl` budget-threaded inner and outer step, loop, and top-level
contracts for `Chunked.EkReceivedCt1Sampled::merge` on Block `310`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledClPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledUcClPlacedBudget
  (chunkedEkReceivedCt1Sampled_uc_decode_key_step_cl_placed
   chunkedEkReceivedCt1Sampled_uc_loop_ok_cl_placed
   chunkedEkReceivedCt1Sampled_push_ret_exit_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledBudgetAux
  (chunkedEkReceivedCt1Sampled_loop_le_exit_cl_placed
   chunkedEkReceivedCt1Sampled_decode_key_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledBudgetSteps
  (chunkedEkReceivedCt1Sampled_skip_step_cl_placed
   chunkedEkReceivedCt1Sampled_tag2_step_cl_placed
   chunkedEkReceivedCt1Sampled_tag1_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledBudget
  (chunkedEkReceivedCt1Sampled_loop_ok_cl_placed
   chunked_ek_received_ct1_sampled_merge_cl_placed_ok_of_contracts)

alias chunkedEkReceivedCt1Sampled_merge_cl_placed_ok_of_contracts :=
  chunked_ek_received_ct1_sampled_merge_cl_placed_ok_of_contracts

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledClPlacedBudget
