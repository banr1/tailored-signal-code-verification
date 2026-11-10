/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyStatements
public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyFinal

/-!
# One-Key PQXDH Headline Security under Imperfect KEM Correctness

**Checked by Lean.** Combines δ-correctness (`wellFormedδ_pqxdhCorrect`), one-key key
indistinguishability (`pqxdh_key_indδ`), and one-key first-message authentication
(`pqxdh_auth1KeySecureδ`, DEV-C5) to prove `PqxdhCorrectAndSecureδ`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh

/-- One-key first-message authentication at setup `S` under a δ-correct KEM. -/
theorem pqxdh_auth1Keyδ (S : Setup) : PqxdhAuth1KeySecureδ S :=
  _root_.Proofs.SignalPqxdh.Security.PqxdhDelta.pqxdh_auth1KeySecureδ S

/-- Combined correctness, key indistinguishability, and authentication for one-key PQXDH under a
    δ-correct KEM. -/
theorem headlineδ_proof : PqxdhCorrectAndSecureδ :=
  headlineδ_of_securityδ pqxdh_key_indδ pqxdh_auth1Keyδ

end SignalPqxdh.Security
