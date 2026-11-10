/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget

/-!
# Budget-Threaded Relocatable Specifications & Prologue/Epilogue Re-Exports

Re-exports the `[LibsignalPlacement]` budget-threaded specifications, hook bundles, Block `333`
prologue/epilogue/`None`-variant theorems, and exit `SepWP -> SepWPp` adapters from `DefsBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget

alias DecoderFromPbPlacedOkExt := DefsBudget.DecoderFromPbPlacedOkExt
alias statesFromPbPlacedSpecOfEnv := DefsBudget.statesFromPbPlacedSpecOfEnv
alias statesFromPbPlacedSpec := DefsBudget.statesFromPbPlacedSpec
alias statesFromPbVariantPlacedSpecOfEnv := DefsBudget.statesFromPbVariantPlacedSpecOfEnv
alias statesFromPbVariantPlacedSpec := DefsBudget.statesFromPbVariantPlacedSpec
alias statesFromPbPlacedSpecXOfEnv := DefsBudget.statesFromPbPlacedSpecXOfEnv
alias statesFromPbPlacedSpecX := DefsBudget.statesFromPbPlacedSpecX
alias statesFromPbPlacedRoFreeSpecXOfEnv := DefsBudget.statesFromPbPlacedRoFreeSpecXOfEnv
alias statesFromPbPlacedRoFreeSpecX := DefsBudget.statesFromPbPlacedRoFreeSpecX
alias StatesFromPbPlacedOk := DefsBudget.StatesFromPbPlacedOk
alias StatesFromPbPlacedOkExt := DefsBudget.StatesFromPbPlacedOkExt
alias StatesFromPbPlacedOkX := DefsBudget.StatesFromPbPlacedOkX
alias spqrRustDeallocSym := DefsBudget.spqrRustDeallocSym
alias FromPbAllocHooksPlacedBudget := DefsBudget.FromPbAllocHooksPlacedBudget

alias withLsCodeLoaded_decoderFromPbSpec_of_fromPbDecSpec :=
  DefsBudget.withLsCodeLoaded_decoderFromPbSpec_of_fromPbDecSpec
alias statesFromPbPlacedSpecXOfEnv_of_statesFromPbPlacedSpecOfEnv :=
  DefsBudget.statesFromPbPlacedSpecXOfEnv_of_statesFromPbPlacedSpecOfEnv
alias statesFromPbPlacedSpecX_of_statesFromPbPlacedSpec :=
  DefsBudget.statesFromPbPlacedSpecX_of_statesFromPbPlacedSpec
alias states_from_pb_prologue_placed := DefsBudget.states_from_pb_prologue_placed
alias states_from_pb_epilogue_64_placed := DefsBudget.states_from_pb_epilogue_64_placed
alias states_from_pb_none_step_placed := DefsBudget.states_from_pb_none_step_placed
alias sepWPp_of_states_exit_placed := DefsBudget.sepWPp_of_states_exit_placed
alias sepWPp_of_states_exit_cl_placed := DefsBudget.sepWPp_of_states_exit_cl_placed
alias states_from_pb_none_placed_ok_of_env := DefsBudget.states_from_pb_none_placed_ok_of_env
alias states_from_pb_none_placed_ok_raw := DefsBudget.states_from_pb_none_placed_ok_raw
alias states_from_pb_none_placed_ok_ext := DefsBudget.states_from_pb_none_placed_ok_ext

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
