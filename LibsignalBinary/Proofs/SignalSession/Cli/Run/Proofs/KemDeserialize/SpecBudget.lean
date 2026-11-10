/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.Spec

/-!
# Budget-Threaded `kem::Key<Public>::deserialize` Specification

Allocation-budget (`RustCliAllocBudget M`) specification for `kem::Key<Public>::deserialize`,
pairing `kemDeserResAt A.repAlloc` with deterministic allocation events `kemDeserializeEvents`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEvents rustAllocEvents)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession.Cli.RunProofs
  (kemPkLen kemPkDeserialize kemDeserResAt KemDeserializeGhost)

/-- Deterministic `AllocEvent` list emitted by `kem::Key<Public>::deserialize` on `bs`:
    `rustAllocEvents kemPkLen 1` (`1568` bytes, align `1`) on `.ok _`, and `[]` on error. -/
def kemDeserializeEvents (bs : List (BitVec 8)) : List AllocEvent :=
  match kemPkDeserialize bs with
  | .ok _ => rustAllocEvents kemPkLen 1
  | _ => []

/-- Budget-form counterpart of `cliKemDeserializeSpec` (`onPanic := ⌜False⌝`, `onOom := ⌜False⌝`
under `FitsEvents M lim st (kemDeserializeEvents x.bs)`). -/
def cliKemDeserializeSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) : Spec (KemDeserializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.r ∧ s.readReg64 .x1 = x.p ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.bs.length ∧ x.bs.length < 2 ^ 63 ∧
      FitsEvents M lim st (kemDeserializeEvents x.bs)⌝ ∗
      memRegion x.r 24 ∗ bytesAt x.ro x.p x.bs ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      kemDeserResAt A.repAlloc x.r (kemPkDeserialize x.bs) ∗ bytesAt x.ro x.p x.bs ∗
      A.pool lim (M.stepEvents (kemDeserializeEvents x.bs) st) sf ∗ stackAt s0.sp stk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
