/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
public import Symbolic.Specifications.Refinement.Statement
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Identity Public-Key Length from External Crypto Contracts

Proves `IkShape interpretation r₀` from `ExternCryptoLawsHold.x25519_public_key_length` and
`ExternContractsHoldCli`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)

theorem pubBytes_length (interpretation : ExternInterpretation)
    (heq : ExternCryptoLawsHold interpretation) (b : HwBytes) :
    (pubBytes interpretation b).length = 32 :=
  heq.x25519_public_key_length (clamp b)

theorem ikShape_of_cryptoEquations {interpretation : ExternInterpretation}
    (heq : ExternCryptoLawsHold interpretation) (r₀ : ProtocolSetup) :
    IkShape interpretation r₀ :=
  ⟨pubBytes_length interpretation heq (secretBytes r₀ 0),
   pubBytes_length interpretation heq (secretBytes r₀ 2)⟩

/-- Derives `IkShape interpretation r₀` from `ExternContractsHoldCli`. -/
theorem ikShape_of_extern {interpretation : ExternInterpretation} (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation) (r₀ : ProtocolSetup) :
    IkShape interpretation r₀ :=
  ikShape_of_cryptoEquations hext.1 r₀

end Symbolic.Swarm.CREF.CliPure.TR

namespace Symbolic.Swarm.CREF.CliPure

export TR (pubBytes_length ikShape_of_cryptoEquations ikShape_of_extern)

end Symbolic.Swarm.CREF.CliPure
