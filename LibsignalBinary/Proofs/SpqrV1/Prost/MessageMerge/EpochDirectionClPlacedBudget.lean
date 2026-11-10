/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetSteps

/-!
# Code-Loaded Placed Budget Wrapper for `EpochDirection::merge` (Block `299`)

Re-exports the code-loaded (`withLsCodeRoLoaded lsmpl` / `withLsCodeLoaded lsmpl`) budget-threaded
exit, per-field step, loop, and top-level theorems for `EpochDirection::merge` on Block `299`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionClPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux
  (EpochDirectionLoopEnv
   EpochDirectionOkEnv
   EpochDirectionMergeEnv
   EpochDirectionMergePostEnv
   epochDirectionMergeSpecOfEnv)
export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux
  (epochDirectionMergeSpec
   epochDirectionLoopPre
   epochDirectionErrFrame
   epochDirection_err0_ret_exit_placed
   epochDirection_from_err_exit_cl_placed)
export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux
  (epochDirection_push_err_exit_cl_placed
   epochDirection_skip_step_cl_placed
   epochDirection_tag1_push_exit_cl_placed
   epochDirection_tag1_wt_err_step_cl_placed
   epochDirection_tag1_varint_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetSteps
  (subroutine_ok_withLsCodeRoLoaded_of_bare
   epochDirection_tag2_step_cl_placed
   epochDirection_tag3_step_cl_placed
   epochDirection_loop_le_exit_cl_placed
   epochDirection_decode_key_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudget
  (epochDirection_loop_ok_cl_placed
   epochDirectionMerge_cro_placed_ok_of_contracts
   epochDirectionMerge_cl_placed_ok_of_contracts
   epochDirectionMerge_placed_ok_of_contracts
   epochDirectionMergeOfEnv_cro_placed_ok_of_contracts)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionClPlacedBudget
