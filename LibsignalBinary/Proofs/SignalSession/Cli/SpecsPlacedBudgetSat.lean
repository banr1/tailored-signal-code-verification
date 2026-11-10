/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget -- proof-setup: allow-public-import

/-!
# `HookSat`-Ready Relocatable `MainIoPlacedSat` Bundle (`SpecsPlacedBudgetSat`)

- **Role**: `Role::Proof` (outside the TCB). Untrusted groundwork for #1255 (HOOKS-PREP).
- **Overview**:
  Honest-write-spec twin of `SpecsPlacedBudget.MainIoPlaced` on Block `617` (`lsProg_617 H`):
  `readStdin` and `readFile` stay unchanged; `writeFile` and `writeStdout` use the honest contracts
  `writeFileSpecPlacedSat` and `writeStdoutSpecPlacedSat` (`IoHonestSpecs.lean`), accompanied by the
  stack-floor bounds `writeFileStackFloor ≤ hookStack` and `writeStdoutStackFloor ≤ hookStack` so
  consumers generic in `hookStack` (`M5`, `M6`) can project them without a concrete `decide`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudgetSat

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.SignalSession
  (lsReadFileSym lsReadStdinSym lsWriteFileSym lsWriteStdoutSym)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops (IoModel)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
  (writeFileSpecPlacedSat writeFileStackFloor writeStdoutSpecPlacedSat writeStdoutStackFloor)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileLitSpecPlaced readStdinSpecPlaced)

/-- Honest-write-spec twin of `SpecsPlacedBudget.MainIoPlaced` on Block `617` (`lsProg_617 H`). -/
structure MainIoPlacedSat [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat) : Prop where
  readStdin : subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
    (withLsRoCl lsmpl (readStdinSpecPlaced io A lim hookStack))
  readFile : subroutine_ok (lsProg_617 H) (lsρ lsReadFileSym)
    (withLsRoCl lsmpl (readFileLitSpecPlaced io A lim hookStack))
  writeFile : subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
    (withLsRoCl lsmpl (writeFileSpecPlacedSat io A lim hookStack))
  writeStdout : subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
    (withLsRoCl lsmpl (writeStdoutSpecPlacedSat A lim hookStack))
  hWriteFileStack : writeFileStackFloor ≤ hookStack
  hWriteStdoutStack : writeStdoutStackFloor ≤ hookStack

end LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudgetSat
