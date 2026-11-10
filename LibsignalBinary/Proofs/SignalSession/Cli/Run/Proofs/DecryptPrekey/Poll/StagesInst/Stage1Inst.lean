/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.Closure
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1OkTrap
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrap

/-!
# Poll Stage P1 Instantiation

Instantiates `StageP1OkTrapExtStmt`, `StageP1UntrustedTrapExtStmt`, `StageP1OkXExtStmt`, and
`StageP1UntrustedXExtStmt`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

/-- Instantiates `StageP1OkTrapExtStmt` via `Kits.stageP1_ok_kit_ext`. -/
theorem stageP1Ok_inst : StageP1OkTrapExtStmt :=
  Kits.stageP1_ok_kit_ext

/-- Instantiates `StageP1UntrustedTrapExtStmt` via `Kits.stageP1_untrusted_ok_kit_ext`. -/
theorem stageP1Untrusted_inst : StageP1UntrustedTrapExtStmt :=
  Kits.stageP1_untrusted_ok_kit_ext

/-- Instantiates `StageP1OkXExtStmt` via `Kits.stageP1_ok_x_ext` (`AllocContractsX`). -/
theorem stageP1Ok_x_inst : StageP1OkXExtStmt :=
  Kits.stageP1_ok_x_ext

/-- Instantiates `StageP1UntrustedXExtStmt` via `Kits.stageP1_untrusted_ok_x_ext`
(`AllocContractsX`). -/
theorem stageP1Untrusted_x_inst : StageP1UntrustedXExtStmt :=
  Kits.stageP1_untrusted_ok_x_ext

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
