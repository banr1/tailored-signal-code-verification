/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto

/-!
# Out-of-Order Message-Key Bound for SPQR States

Defines `SpqrOooBounded`, asserting that every chain-parameter block in a decodable
`PqRatchetState` caps out-of-order message keys at `2000`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Grow

open CryptoVerification.LibsignalSpqrV1

/-- Every chain-parameter block in a decodable SPQR state caps `maxOooKeysOrDefault` at `2000`
(`DEV-TR-OOO`). -/
def SpqrOooBounded (bs : List (BitVec 8)) : Prop :=
  ∀ st, PqRatchetState.decode bs = .ok st →
    (∀ c ∈ st.chain, ∀ p ∈ c.params, p.maxOooKeysOrDefault.toNat ≤ 2000) ∧
    (∀ v ∈ st.versionNegotiation, ∀ p ∈ v.chainParams, p.maxOooKeysOrDefault.toNat ≤ 2000)

end Symbolic.Swarm.CREF.Grow

namespace Symbolic.Swarm.CREF
export Grow (SpqrOooBounded)
end Symbolic.Swarm.CREF
