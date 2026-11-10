/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.KeyInd1KeyRo
public import Computational.Proofs.SpecLemmas.SignalPqxdh.Assumptions

/-!
# Definitional Guards for `pqxdhKeyIndImpl1KeyRo`

**Checked by Lean.** Pins the query dispatch of `pqxdhKeyIndImpl1KeyRo`: `.initPrin` coincides
definitionally with `pqxdhKeyIndImpl1KeyReal`, every other query delegates to
`pqxdhKeyIndImpl true`, and `.roQuery` evaluates `HkdfRO P` on `st.roCache` where
`pqxdhKeyIndImpl1KeyReal` evaluates `evalHkdfOrRo false P`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

theorem pqxdhKeyIndImpl1KeyRo_initPrin (S : Setup) (P : Primitives) (u : Fin S.N_id) :
    pqxdhKeyIndImpl1KeyRo S P (.initPrin u) = pqxdhKeyIndImpl1KeyReal S P (.initPrin u) :=
  rfl

theorem pqxdhKeyIndImpl1KeyRo_of_ne_initPrin (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hq : ∀ u : Fin S.N_id, q ≠ .initPrin u) :
    pqxdhKeyIndImpl1KeyRo S P q = pqxdhKeyIndImpl true S P q := by
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | _ => rfl

theorem pqxdhKeyIndImpl1KeyRo_roQuery (S : Setup) (P : Primitives) (secrets : Bytes) :
    pqxdhKeyIndImpl1KeyRo S P (.roQuery secrets) = (do
      let st ← get
      let (dk, roCache') ← liftM (HkdfRO P st.roCache secrets)
      set { st with roCache := roCache' }
      return .drKeyResp dk) :=
  rfl

theorem pqxdhKeyIndImpl1KeyReal_roQuery (S : Setup) (P : Primitives) (secrets : Bytes) :
    pqxdhKeyIndImpl1KeyReal S P (.roQuery secrets) = (do
      let st ← get
      let (dk, roCache') ← liftM (evalHkdfOrRo false P st.roCache secrets)
      set { st with roCache := roCache' }
      return .drKeyResp dk) :=
  rfl

end SignalPqxdh
