/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DefsBudget
public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon

/-!
# Budget-Threaded `E2E.Bin.SpecsCommon` Contracts

Budget-threaded (`RustCliAllocBudget M`) `recordDeserializeOpenSpec` over `RecordDeserializeEnv bs`
and its 1 GiB non-vacuity witness.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Bin.SpecsCommonBudget

open Arm64 ProofLib
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open CryptoGames.LibsignalSessionApi (Session)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (nonVacLimits)
open LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DefsBudget (
  RecordDeserializeEnv recordDeserializeEnv_fitsEnv_of_len_le
)

/-- Budget-threaded `SessionRecord::deserialize` on a canonical encoded `SessionRecord`, bounded
by `RecordDeserializeEnv bs` with `onOom = ⌜False⌝` and `onPanic = ⌜False⌝`. -/
def recordDeserializeOpenSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8) × BitVec 64 × Session (List (BitVec 8))) × M.σ) where
  pre := fun (x, st) s =>
    let (_, bs, _, _) := x
    ⌜FitsEnv M lim st (RecordDeserializeEnv bs)⌝ ∗
      (CryptoVerification.E2E.Bin.recordDeserializeOpenSpec (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    let (_, bs, _, _) := x
    ∃∗ evs : List AllocEvent,
      ⌜RecordDeserializeEnv bs evs⌝ ∗
      (CryptoVerification.E2E.Bin.recordDeserializeOpenSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Non-vacuity witness for `recordDeserializeOpenSpec` under `nonVacLimits`. -/
theorem recordDeserializeOpenSpec_fitsEnv_witness :
    FitsEnv fineCostModel nonVacLimits fineCostModel.init
      (RecordDeserializeEnv (List.replicate 128 0#8)) :=
  recordDeserializeEnv_fitsEnv_of_len_le (List.replicate 128 0#8)
    (by rw [List.length_replicate]; decide)

end LibsignalBinary.Proofs.E2E.Bin.SpecsCommonBudget
