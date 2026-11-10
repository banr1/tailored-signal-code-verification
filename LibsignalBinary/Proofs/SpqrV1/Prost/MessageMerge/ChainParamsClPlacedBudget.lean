/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget

/-!
# Budget-Threaded Code-Loaded `[LibsignalPlacement]` `ChainParams::merge` Re-Exports (Block `294`)

Re-exports the budget-threaded code-loaded `[LibsignalPlacement]` Block `294` step, loop, and
subroutine contracts (`chainParamsMerge_cl_placed_ok_of_contracts` and
`chainParamsMerge_cro_placed_ok_of_contracts`) from `ChainParamsBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsClPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget
  (chainParams_err0_ret_exit_placed chainParams_from_err_exit_cl_placed
   chainParams_push_err_exit_cl_placed chainParams_skip_step_cl_placed
   chainParams_tag1_push_exit_cl_placed)
export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget
  (chainParams_tag1_wt_err_step_cl_placed chainParams_tag1_varint_step_cl_placed
   chainParams_tag2_push_exit_cl_placed chainParams_tag2_wt_err_step_cl_placed
   chainParams_tag2_varint_step_cl_placed)
export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget
  (chainParams_loop_le_exit_cl_placed chainParams_decode_key_step_cl_placed
   chainParams_loop_ok_cl_placed chainParamsMerge_cl_placed_ok_of_contracts
   chainParamsMerge_cro_placed_ok_of_contracts)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsClPlacedBudget
