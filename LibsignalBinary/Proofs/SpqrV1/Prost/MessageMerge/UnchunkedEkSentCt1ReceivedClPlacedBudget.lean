/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedBudgetAux

/-!
# Code-Loaded Placed Budget Wrapper for `Unchunked.EkSentCt1Received::merge` (Block `311`)

Re-exports the `withLsCodeRoLoaded lsmpl` budget-threaded step, loop, and top-level contracts for
`Unchunked.EkSentCt1Received::merge` on Block `311`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedClPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedBudgetAux
  (ekSent_tag4_step_cl_placed ekSent_tag4_step_placed ekSent_loop_le_exit_cl_placed)
export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedBudgetAux
  (ekSent_loop_le_exit_placed ekSent_decode_key_step_cl_placed ekSent_decode_key_step_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedBudget
  (ekSent_loop_ok_cl_placed
   ekSent_loop_ok_placed
   unchunkedEkSentCt1ReceivedMerge_own_cl_placed_ok_of_contracts)
export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedBudget
  (unchunkedEkSentCt1ReceivedMerge_own_placed_ok_of_contracts
   unchunkedEkSentCt1ReceivedMerge_cl_placed_ok_of_contracts
   unchunkedEkSentCt1ReceivedMerge_placed_ok_of_contracts)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedClPlacedBudget
