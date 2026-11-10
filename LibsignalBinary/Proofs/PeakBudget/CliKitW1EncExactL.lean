/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit

/-!
# Implication-Guard Lift for `W1` (`encrypt` `@109`) Exact Slot

**Checked by Lean.**

Proves `w1x_liftCredit_Stmt`, `w1x_liftGroup_Stmt`, and `w1x_lift_Stmt` via
`PhaseCreditSpec.of_imp` and `PhaseGroupSpec.of_imp`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactL

open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit
  (w1x_liftCredit_Stmt w1x_liftGroup_Stmt w1x_lift_Stmt)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)

theorem w1xl_liftCredit : w1x_liftCredit_Stmt :=
  fun hG h => PhaseCreditSpec.of_imp (fun _ h' => h' hG) h

theorem w1xl_liftGroup : w1x_liftGroup_Stmt :=
  fun hG h => PhaseGroupSpec.of_imp h (fun _ h' => h' hG)

theorem w1xl_lift : w1x_lift_Stmt :=
  ⟨w1xl_liftCredit, w1xl_liftGroup⟩

end LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactL
