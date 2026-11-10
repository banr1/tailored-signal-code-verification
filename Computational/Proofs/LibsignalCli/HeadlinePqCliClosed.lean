/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.HeadlinePqCliMixEq
public import Computational.Proofs.LibsignalCli.StatementPqSecure
import Computational.Proofs.LibsignalCli.CliPqAdapterSmStep
import Computational.Proofs.LibsignalCli.CliPqKeyIndStep
import Computational.Proofs.LibsignalCli.CliPqStartStep
import Computational.Proofs.LibsignalCli.HeadlinePqCli
import Computational.Proofs.SignalPqxdh.Delta.Statements

/-!
# Closed CLI security on PQXDH directories with SPQR

Assembles the step-level adapter bridges and `headlineδ_proof.keyInd` to prove
`LibsignalCliPqSecure S ℓ` with no external premises.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

/-- `CliPqAdapterBoundProp S ℓ` from the `KeyInd`, `startDR`, and SM step bridges. -/
theorem cliPqAdapterBoundProp_holds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    CliPqAdapterBoundProp (Pt := Pt) S ℓ :=
  cliPqAdapterBoundProp_of_step_bridges (Pt := Pt) S ℓ
    (cliKeyIndStepBridgeProp_holds (Pt := Pt) S ℓ)
    (cliStartStepBridgeProp_holds (Pt := Pt) S ℓ)
    (cliSmStepBridgeProp_holds (Pt := Pt) S ℓ)

/-- Closed proof of `LibsignalCliPqSecure S ℓ`. -/
theorem libsignalCliPqSecure_holds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    LibsignalCliPqSecure (Pt := Pt) S ℓ :=
  libsignalCliPqSecure_of_bridges (Pt := Pt) S ℓ
    (cliPqAdapterBoundProp_holds (Pt := Pt) S ℓ)
    (_root_.SignalPqxdh.Security.headlineδ_proof.keyInd S)

end CryptoVerification.E2E
