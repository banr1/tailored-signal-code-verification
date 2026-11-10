/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetInit
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetSteps

/-!
# Budget-Threaded Code-Loaded `[LibsignalPlacement]` `Chunked.Ct1Sampled::merge` Re-Exports (Block `300`)

Re-exports the budget-threaded `[LibsignalPlacement]` `withLsCodeRoLoaded lsmpl` exit,
field-initialization, loop-step, loop, and top-level Block `300` contracts from
`ChunkedCt1SampledBudgetAux`, `ChunkedCt1SampledBudgetInit`, `ChunkedCt1SampledBudgetSteps`, and
`ChunkedCt1SampledBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledClPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetAux
  (ct1Sampled_err0_ret_exit_placed
   ct1Sampled_from_err_exit_cl_placed
   ct1Sampled_push_err_exit_cl_placed
   ct1Sampled_loop_le_exit_cl_placed
   ct1Sampled_decode_key_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetInit
  (ct1Sampled_tag1_init_step_placed
   ct1Sampled_tag2_init_step_placed
   ct1Sampled_tag3_init_step_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetSteps
  (ct1Sampled_skip_step_cl_placed
   ct1Sampled_tag1_step_cl_placed
   ct1Sampled_tag2_step_cl_placed
   ct1Sampled_tag3_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudget
  (ct1Sampled_loop_ok_cl_placed
   chunked_ct1_sampled_merge_cl_placed_ok_of_contracts)

alias chunkedCt1Sampled_merge_cl_placed_ok_of_contracts :=
  chunked_ct1_sampled_merge_cl_placed_ok_of_contracts

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledClPlacedBudget
