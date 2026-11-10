/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudgetAux

/-!
# Budget-Threaded Code-Loaded Step Re-Exports for `unchunked::EkSentCt1Received::merge` (Block `311`)

Re-exports the `RustCliAllocBudget`-threaded `[LibsignalPlacement]` code-loaded exit, `skip_field`,
and per-field step lemmas for Block `311` from `UnchunkedEkSentCt1ReceivedStepBudgetAux` and
`UnchunkedEkSentCt1ReceivedStepBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepClPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudgetAux
  (subroutine_ok_withLsCodeRoLoaded_of_bare ekSentSavedRegs
   stackAt_unchunkedMerge_epilogue ekSentLoopPre ekSentErrFrame)
export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudgetAux
  (ekSent_ret_err_exit_placed ekSent_err0_ret_exit_placed
   ekSent_from_err_exit_cl_placed ekSent_from_err_exit_placed)
export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudgetAux
  (ekSent_push_err_exit_cl_placed ekSent_push_err_exit_placed
   ekSent_skip_step_cl_placed ekSent_skip_step_placed)
export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudgetAux
  (ekSent_tag1_push_exit_cl_placed ekSent_tag1_push_exit_placed
   ekSent_tag1_wt_err_step_cl_placed ekSent_tag1_wt_err_step_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudget
  (ekSent_tag1_varint_step_cl_placed ekSent_tag1_varint_step_placed
   ekSent_tag2_call_step_cl_placed ekSent_tag2_call_step_placed)
export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudget
  (ekSent_tag2_step_cl_placed ekSent_tag2_step_placed
   ekSent_tag3_step_cl_placed ekSent_tag3_step_placed)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepClPlacedBudget
