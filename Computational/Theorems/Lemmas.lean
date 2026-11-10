/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.Composition.StatementModel
import Computational.Proofs.LibsignalCli.HeadlineModel
import Computational.Proofs.LibsignalCli.HeadlineSession
import Computational.Proofs.SignalPqxdh.Delta.Statements

/-!
# Lemmas 1–3: PQXDH, Single Session, and Multi-Session Composition

**Trusted: the statement.** Each theorem below states a proposition from
`Computational/Specifications/` and is proved by a corresponding `*_proof` theorem in
`Computational/Proofs/`. See `Computational/docs/TRUSTED_BASE.md` for the trusted definitions and
kernel axioms of each theorem, and `Computational/Theorems/Main.lean` (`CliElfLib`) for Lemma 4
and the Main Theorem on the compiled `signal-session` binary.

| Lemma | Theorem | Statement | Proof |
|---|---|---|---|
| 1 (PQXDH) | `SignalPqxdh.Security.headlineδ` | `PqxdhCorrectAndSecureδ` (`Computational/Specifications/Pqxdh/Security/HeadlineDelta.lean`) | `Computational/Proofs/SignalPqxdh/Delta/Statements.lean` |
| 2 (single session) | `CryptoVerification.E2E.session_secure` | `SessionSecure` (`Computational/Specifications/Session/StatementSession.lean`) | `Computational/Proofs/LibsignalCli/HeadlineSession.lean` |
| 3 (composition) | `CryptoVerification.E2E.model_secure_costed` | `ModelSecure` (`Computational/Specifications/Composition/StatementModel.lean`) | `Computational/Proofs/LibsignalCli/HeadlineModel.lean` |
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

/-- **Lemma 1 (PQXDH)** (`PqxdhCorrectAndSecureδ`,
`Computational/Specifications/Pqxdh/Security/HeadlineDelta.lean`). For all setups `S` and
well-formed primitives `P` (`WellFormedPrimitivesδ P`): honest Alice and Bob derive matching session
keys (`PqxdhCorrect P`); the one-key handshake with `HkdfRO` satisfies `PqxdhKeyIndSecureδ S`,
bounding `KeyInd1KeyRoAdvantage` by `pqxdhKeyIndAdvantageBoundActiveδ` (`pqxdhKeyIndBoundActive`
plus `kemDecapsFailureTerm`) via costed reductions to `GapSigEufCma`, `KemShCr`, and
`GapDhWithSign`; and the one-key first-message authentication game satisfies `PqxdhAuth1KeySecureδ S`
(`Computational/Specifications/Pqxdh/Security/Auth/Headline.lean`, DEV-C5), bounding
`Auth1KeyAdvantage` by `pqxdhAuthAdvantageBoundδ` via costed reductions to `GapSigEufCma`, `KemShCr`,
`GapDhWithSign`, `PrfChainKey`, `PrfMsgKeys`, `AeadIndCpa`, and `PrfHmac`. -/
theorem headlineδ : PqxdhCorrectAndSecureδ :=
  headlineδ_proof

end SignalPqxdh.Security

namespace CryptoVerification.E2E

/-- **Lemma 2 (single session)** (`SessionSecure`,
`Computational/Specifications/Session/StatementSession.lean`). There exists a family `D` of
cost-bounded session reductions such that, for all primitives satisfying the session hypotheses
(P1–P10), a 32-bit counter bound, and a point-fiber bound `δ`, every mixture `oa` of session
contexts and `q`-query adversaries has single-session `SM.gameR` bias against
`sessionSchemeFixedSpk` at most `sessionAdvantageBound` evaluated on `D`. -/
theorem session_secure {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) : SessionSecure (Pt := Pt) ℓ :=
  session_secure_proof ℓ

/-- **Lemma 3 (composition)** (`ModelSecure`,
`Computational/Specifications/Composition/StatementModel.lean`). For the one-key real-HKDF handshake
`ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P`, there exists a budget-indexed family of
cost-bounded `ReductionDsl` reductions (uniform in `P`) such that, for every `P` satisfying
`SignalPqxdh.WellFormedPrimitivesδ P`, any bounded adversary's advantage in `G(Σ_model^ki)` is at
most twice the `KeyInd` advantage against `ki` plus, per promoted session, the supremum over `flip`
of the single-session `SM.gameR` bias mixed over stage 1 of the prefix reduction. -/
theorem model_secure_costed {Pt : Type}
    (S : SignalPqxdh.Setup) (ℓ : ℕ) : ModelSecure (Pt := Pt) S ℓ :=
  model_secure_costed_proof S ℓ

end CryptoVerification.E2E
