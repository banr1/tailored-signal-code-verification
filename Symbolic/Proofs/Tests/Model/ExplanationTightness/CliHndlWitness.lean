/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.Model
public import Symbolic.Proofs.Tests.Model.ExplanationTightness.CliHndlWitness.Explains

/-!
# CLI-Realizable Harvest-Now-Decrypt-Later Witness

Exhibits a guarded CLI trace from provisioned directories under `PqModelRel` containing a
post-handshake `breakDH` and `invertDH` event whose symbolic `Explains` witness completes a
handshake (`AliceDone`), subsequently logs `BrokenDH`, and satisfies `HNDLPremise`. This shows that
`HNDLQuery` in `AllSecurityQueriesHoldOnHwTrace` is non-vacuous once quantum break and inversion
events are allowed.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.CliHndlWitness

open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.E2E (PEParams)
open DY DY.Comparse
open DY.Libsignal DY.Libsignal.PQXDH
open DY.Libsignal.HwEvents (EnvEvent CliEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli

/-- There exist an extern interpretation, model parameters, well-formed setup records, and a
guarded CLI trace with an `invertDH` event whose `Explains` witness completes a handshake
(`AliceDone` at `i`), logs `BrokenDH`, and satisfies `HNDLPremise` for that session. -/
theorem cli_hndl_witness :
    ∃ (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup) (evs : List CliEvent)
      (S : OpaqueSymbolSemantics) (g : Ghost) (ss : List Step) (vis : List VisEntry),
      ExternContractsHoldCli interp ∧ ModelAgree interp P ∧ ProtocolSetupWF r ∧
      CliTraces (PqModelRel interp P) interp r (CliTurn.init (initDirs interp r)) evs ∧
      InvertsGuarded interp r evs ∧
      (∃ pk sk, CliEvent.env (EnvEvent.invertDH pk sk) ∈ evs) ∧
      Explains interp r S g ss vis evs ∧
      (runTrace r ss).EventLogged PQXDHEvent.BrokenDH ∧
      ∃ a b ikA ikB spk pqpk opk ek ct keys i,
        (runTrace r ss).EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i ∧
        HNDLPremise a b ikA ikB spk pqpk i (runTrace r ss) := by
  exact Explains.cli_hndl_witness_aux

end Symbolic.Proofs.Tests.Model.ExplanationTightness.CliHndlWitness
