/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Machine-Free Identity Key Shape Projections

Projects `IkShape` from `ExternCryptoLawsHold` and `ExternContractsHoldCli` without machine state.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.TRREF.Pure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli)

theorem rcv_ikShape_of_cryptoEquations {interpretation : ExternInterpretation}
    (heq : ExternCryptoLawsHold interpretation) (r : ProtocolSetup) :
    Symbolic.Swarm.CREF.TR.IkShape interpretation r :=
  ⟨heq.x25519_public_key_length (clamp (secretBytes r 0)),
   heq.x25519_public_key_length (clamp (secretBytes r 2))⟩

theorem rcv_ikShape_of_externCli {interpretation : ExternInterpretation}
    (hcli : ExternContractsHoldCli interpretation) (r : ProtocolSetup) :
    Symbolic.Swarm.CREF.TR.IkShape interpretation r :=
  rcv_ikShape_of_cryptoEquations hcli.1 r

end Symbolic.Proofs.Swarm.TRREF.Pure
