/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudget

/-!
# Budget-Threaded Code-Loaded Proof Re-Exports for `Authenticator::merge` (Block `295`)

Re-exports the `RustCliAllocBudget`-threaded, code-loaded `[LibsignalPlacement]` step lemmas,
loop invariant, and subroutine contracts for `Authenticator::merge` (Block `295`) against
`withLsCodeRoLoaded lsmpl (authMergeSpec A lim)`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Auth.MergeClPlacedBudget

/-! ## Exit and Field Step Lemmas -/

abbrev auth_err0_ret_exit_placed := @MergePlacedBudgetAux.auth_err0_ret_exit_placed
abbrev auth_from_err_exit_cl_placed := @MergePlacedBudgetAux.auth_from_err_exit_cl_placed
abbrev auth_push_err_exit_cl_placed := @MergePlacedBudgetAux.auth_push_err_exit_cl_placed
abbrev auth_skip_step_cl_placed := @MergePlacedBudgetAux.auth_skip_step_cl_placed
abbrev auth_tag1_step_cl_placed := @MergePlacedBudgetAux.auth_tag1_step_cl_placed
abbrev auth_tag2_step_cl_placed := @MergePlacedBudgetAux.auth_tag2_step_cl_placed

/-! ## Loop Induction and Top-Level Contracts -/

abbrev auth_loop_le_exit_cl_placed := @MergePlacedBudget.auth_loop_le_exit_cl_placed
abbrev auth_decode_key_step_cl_placed := @MergePlacedBudget.auth_decode_key_step_cl_placed
abbrev auth_loop_ok_cl_placed := @MergePlacedBudget.auth_loop_ok_cl_placed
abbrev auth_merge_cl_placed_ok_of_cro_contracts_env :=
  @MergePlacedBudget.auth_merge_cl_placed_ok_of_cro_contracts_env
abbrev auth_merge_cl_placed_ok_of_cro_contracts :=
  @MergePlacedBudget.auth_merge_cl_placed_ok_of_cro_contracts
abbrev auth_merge_cl_placed_ok_of_contracts_env :=
  @MergePlacedBudget.auth_merge_cl_placed_ok_of_contracts_env
abbrev auth_merge_cl_placed_ok_of_contracts :=
  @MergePlacedBudget.auth_merge_cl_placed_ok_of_contracts

end LibsignalBinary.Proofs.SpqrV1.Auth.MergeClPlacedBudget
