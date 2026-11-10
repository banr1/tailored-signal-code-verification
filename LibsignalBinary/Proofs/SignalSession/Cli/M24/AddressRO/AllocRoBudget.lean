/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocBudget

/-!
# Budgeted Read-Only `argv` Postcondition for `signal_session::address`

Defines `AddrGoalPostRO` over `M24.CalleesRO.addressSpecRO` for read-only (`↦ᵣ`) input slices.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.AllocRoBudget

open Arm64 ProofLib
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession.Cli.MainHops (AddressCall)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (addressSpecRO)

abbrev AddrGoalPostRO {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (resStack : Nat) (x : AddressCall) (st : M.σ) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    (P_f ⊢ (addressSpecRO A lim uuidTryParse resStack).post (x, st) s0 sf)

end LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.AllocRoBudget
