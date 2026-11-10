/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Alloc

/-!
# Budget-Threaded Frame and Postcondition Helpers for `signal_session::address`

Defines `AddrFrameCommon` and `AddrGoalPost` over `CalleesBudget.addressSpec` for the
`RustCliAllocBudget` proofs of `signal_session::address`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocBudget

open Arm64 ProofLib
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession.Cli.MainHops (AddressCall)
open CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers (subStackSize addrSavedRegs)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (addressSpec)

abbrev AddrFrameCommon {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (resStack : Nat) (st : M.σ) (s0 s : State) : SepProp :=
  A.pool lim st s ∗
  memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
  stackAt (s0.sp - 96#64) subStackSize ∗
  memRegion (s0.sp - 96#64) 32 ∗
  addrSavedRegs s0.sp s0

abbrev AddrGoalPost {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (resStack : Nat) (x : AddressCall) (st : M.σ) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    (P_f ⊢ (addressSpec A lim uuidTryParse resStack).post (x, st) s0 sf)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocBudget
