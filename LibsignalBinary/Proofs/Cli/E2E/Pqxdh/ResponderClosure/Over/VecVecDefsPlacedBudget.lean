/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsPlaced
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX

/-!
# Budget-Threaded Placed `<Vec<Vec<u8>> as Clone>::clone` Contract Statement on 1 Element

Defines `VecVecClone1PlacedOkStmt` at `lsmpl.base 117` and its caller-block transfer
`vecVecClone1_placed_ok_cl` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsPlacedBudget

open Arm64 ProofLib
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl withLsCodeLoaded withLsCl
)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.E2E.Record.Placed (blkPC_117 blkPl_117)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget (
  vecVecClone1SpecX
)

/-- Budget-threaded `[LibsignalPlacement]` subroutine contract for `<Vec<Vec<u8>> as Clone>::clone`
on `len = 1` at `lsmpl.base 117`. -/
def VecVecClone1PlacedOkStmt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_117).rebase (blkPl_117).base H) (lsmpl.base 117)
    (withLsCodeLoaded lsmpl (vecVecClone1SpecX M A lim))

theorem vecVecClone1_placed_ok_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hK1 : VecVecClone1PlacedOkStmt M A lim H) :
    subroutine_ok callerProg (blkPl_117).base (withLsCl lsmpl (vecVecClone1SpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (j := 117) hK1

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsPlacedBudget
