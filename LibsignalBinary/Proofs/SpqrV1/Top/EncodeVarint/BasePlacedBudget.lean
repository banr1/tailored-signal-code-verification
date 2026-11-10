/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlacedBudget

/-!
# Budget-Threaded Relocatable Base Step Lemmas for `spqr::encode_varint` (`Block 326`)

Re-exports the relocatable `[LibsignalPlacement]` step lemmas, prologue/tail/exit blocks,
continuation-byte stages 1..2, and `SpqrVecPushBudgetInv` algebra from `BaseBudgetAux` and
`BaseBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BasePlacedBudget

abbrev growOneU8ByteStep_of_lt :=
  @BaseBudgetAux.growOneU8ByteStep_of_lt

abbrev growOneU8ByteStep_of_eq :=
  @BaseBudgetAux.growOneU8ByteStep_of_eq

abbrev fitsEnv_growOneU8_of_fitsEvents :=
  @BaseBudgetAux.fitsEnv_growOneU8_of_fitsEvents

abbrev SpqrVecPushBudgetInv :=
  @BaseBudgetAux.SpqrVecPushBudgetInv

abbrev grow_frame_budget_reassoc :=
  @BaseBudgetAux.grow_frame_budget_reassoc

abbrev step_growOneU8_placed_call :=
  @BaseBudgetAux.step_growOneU8_placed_call

abbrev step_spqrEncVarint_placed_prologue :=
  @BaseBudgetAux.step_spqrEncVarint_placed_prologue

abbrev step_spqrEncVarint_placed_tail :=
  @BaseBudgetAux.step_spqrEncVarint_placed_tail

abbrev step_spqrEncVarint_placed_exit0 :=
  @BaseBudget.step_spqrEncVarint_placed_exit0

abbrev step_spqrEncVarint_placed_exit1 :=
  @BaseBudget.step_spqrEncVarint_placed_exit1

abbrev step_spqrEncVarint_placed_exit2 :=
  @BaseBudget.step_spqrEncVarint_placed_exit2

abbrev step_spqrEncVarint_placed_exit3 :=
  @BaseBudget.step_spqrEncVarint_placed_exit3

abbrev step_spqrEncVarint_placed_exit_328 :=
  @BaseBudget.step_spqrEncVarint_placed_exit_328

abbrev step_spqrEncVarint_placed_exit_396 :=
  @BaseBudget.step_spqrEncVarint_placed_exit_396

abbrev step_spqrEncVarint_placed_exit9 :=
  @BaseBudget.step_spqrEncVarint_placed_exit9

abbrev step_spqrEncVarint_placed_s1 :=
  @BaseBudget.step_spqrEncVarint_placed_s1

abbrev step_spqrEncVarint_placed_s2 :=
  @BaseBudget.step_spqrEncVarint_placed_s2

end LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BasePlacedBudget
