/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit

/-!
# Guarded-Tight `W1` (`encrypt` `@109`) Guard Discharge

**Checked by Lean.**

Discharges `w1x_guard_Stmt W`: under `CliPqxdhInputs ⟨W.C, W.Q⟩ g.i`,
`parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV)`, and
`W1BinarySendDom (.send peerV) g.i w1R`, `PeerSpqrStateTight640 W.C.F W.Q.K w1R.x.F w1R.x.peer.val`
holds via `peerSpqrStateTight640_of_cliPqInputs_send`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactG

open CryptoVerification.SignalSession (CliHooks)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit (w1x_guard_Stmt)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (peerSpqrStateTight640_of_cliPqInputs_send)

theorem w1x_guard (W : CliHooks) : w1x_guard_Stmt W := by
  intro g peerV w1R hi hp hdom
  obtain ⟨hpv, hxpeer, _, _, hxF⟩ := hdom peerV rfl
  rw [hxF, hxpeer, hpv]
  exact peerSpqrStateTight640_of_cliPqInputs_send hi hp

end LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactG
