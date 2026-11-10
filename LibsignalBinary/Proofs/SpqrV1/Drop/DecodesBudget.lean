/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Proofs.SpqrV1.Drop.Decodes

/-!
# Budget-Threaded `__rust_dealloc` Contract Alias for SPQR V1 Drop Glue

Defines the `RustCliAllocBudget`-threaded `DeallocOkExt` contract alias on `dropProgAtExt`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Drop.DecodesBudget

open Arm64 ProofLib
open CryptoVerification.SpqrV1.Drop (dropProgAtExt)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpecBase)

/-- Budget-threaded `subroutine_ok` contract for `__rustc::__rust_dealloc` on `dropProgAtExt b ext`. -/
abbrev DeallocOkExt (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (dropProgAtExt b ext)
    ((dropProgAtExt b ext).fnAddr "__rustc::__rust_dealloc")
    (rustCliDeallocBudgetSpecBase M A lim)

end LibsignalBinary.Proofs.SpqrV1.Drop.DecodesBudget
