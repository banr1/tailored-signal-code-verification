/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.Assumptions
public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthGames
public import LibsignalBinary.Specifications.SignalPqxdh.Model
public import Computational.Specifications.Pqxdh.Game
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt

/-!
# Decidability instances for multi-user AEAD query predicates

**Checked by Lean.** Proof-side `DecidablePred` instances accompanying
`Computational/Specifications/Assumptions/Assumptions.lean` and
`Computational/Proofs/SignalPqxdh/TwoKeyAndAuthStatements.lean`.
-/

@[expose] public section

set_option autoImplicit false
namespace SignalPqxdh
open OracleComp OracleSpec ENNReal

instance : DecidablePred isMuEncQuery := fun q => by
  rcases q with _ | q
  · simp only [isMuEncQuery]; infer_instance
  · cases q <;> simp only [isMuEncQuery] <;> infer_instance

instance : DecidablePred isMuForgeQuery := fun q => by
  rcases q with _ | q
  · simp only [isMuForgeQuery]; infer_instance
  · cases q <;> simp only [isMuForgeQuery] <;> infer_instance

end SignalPqxdh
