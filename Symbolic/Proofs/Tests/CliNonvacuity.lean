/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Defs
public import Symbolic.Proofs.Tests.CliNonvacuity.Witness
public import Symbolic.Proofs.Tests.CliNonvacuity.Handshake
public import Symbolic.Proofs.Tests.CliNonvacuity.Session

/-!
# CLI-Level Non-Vacuity Barrel Proofs

Aggregates `cliSpecPq_satisfiable_proof` and the five `CliTraceReachableProof` witnesses from
`Defs`, `Witness`, `Handshake`, and `Session` into `cli_nonvacuity_examples_reachable_proof`
for `Symbolic.Tests.CliNonvacuity`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity

open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.SignalSession (Address CliRun CliHooks CliSpecPqxdh)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (ProtocolSetup)
open DY.Libsignal.Composed.Refinement.Cli (CoinsFresh)
open Symbolic.Tests.Nonvacuity
  (keySetupTrace honestHandshakeWithoutOpkTrace honestHandshakeWithOpkTrace
   honestSessionTrace exposedSessionTrace)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs
  (CliTraceReachableProof not_coinsFresh_two_inits_same_coins_proof)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (cliReachable_keySetupTrace)
open Symbolic.Proofs.Tests.CliNonvacuity.Handshake
  (cliReachable_honestHandshakeWithoutOpkTrace cliReachable_honestHandshakeWithOpkTrace)
open Symbolic.Proofs.Tests.CliNonvacuity.Session
  (cliReachable_honestSessionTrace cliReachable_exposedSessionTrace)

theorem cliSpecPq_satisfiable_proof (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    ∃ run : CliRun, CliSpecPqxdh run X ⟨W.C, W.Q⟩ :=
  Defs.cliSpecPq_satisfiable_proof X W

theorem cli_nonvacuity_examples_reachable_proof :
    CliTraceReachableProof keySetupTrace ∧
    CliTraceReachableProof honestHandshakeWithoutOpkTrace ∧
    CliTraceReachableProof honestHandshakeWithOpkTrace ∧
    CliTraceReachableProof honestSessionTrace ∧
    CliTraceReachableProof exposedSessionTrace :=
  ⟨cliReachable_keySetupTrace,
   cliReachable_honestHandshakeWithoutOpkTrace,
   cliReachable_honestHandshakeWithOpkTrace,
   cliReachable_honestSessionTrace,
   cliReachable_exposedSessionTrace⟩

theorem not_coinsFresh_two_inits_same_coins_proof (r : ProtocolSetup) (party₁ party₂ : String)
    (peer₁ peer₂ : Address) (bundle₁ bundle₂ : String) (in₁ in₂ coins out₁ out₂ : HwBytes) :
    ¬ CoinsFresh r
      [.run { party := party₁, cmd := .init peer₁ bundle₁, input := in₁, coins := coins,
              exit := some (0, out₁) },
       .run { party := party₂, cmd := .init peer₂ bundle₂, input := in₂, coins := coins,
              exit := some (0, out₂) }] :=
  Defs.not_coinsFresh_two_inits_same_coins_proof
    r party₁ party₂ peer₁ peer₂ bundle₁ bundle₂ in₁ in₂ coins out₁ out₂

end Symbolic.Proofs.Tests.CliNonvacuity
