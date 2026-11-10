/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqStatement
public import Computational.Proofs.E2E.PqxdhSessionModelProofDefs
import Computational.Proofs.E2E.Pqxdh.FirstMessageRoundtrip
import Computational.Proofs.LibsignalCli.PqFirstMessageRoundtrip

/-!
# First-Message Roundtrip Witnesses for PQXDH-Mode Models

Checks honest-path non-vacuity of the PQXDH-mode models by re-exporting first-message roundtrip
theorems for the CLI directory models (`pqInitModel`, `pqSendModel`, `pqRecvPrekeyModel`) and for
the pure wire and handshake models (`PqxdhSessionModel`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoVerification.E2E

/-- Under the primitive laws of `PqCliFirstMessageRoundtrip`, Alice's `init` on Bob's honest bundle
and first `send` produce a pre-key message in `CliRecvPrekeyCorrect`'s domain, and Bob's `recv`
recovers the plaintext whenever his store accepts the Kyber pre-key. -/
theorem pqCliFirstMessageRoundtrip (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    PqCliFirstMessageRoundtrip X W :=
  pqCliFirstMessageRoundtrip_proof X W

end CryptoVerification.SignalSession

namespace CryptoVerification.E2E

theorem pqxdhFirstMessageRoundtrip (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    PqxdhFirstMessageRoundtrip X W :=
  pqxdhFirstMessageRoundtrip_proof X W

end CryptoVerification.E2E
