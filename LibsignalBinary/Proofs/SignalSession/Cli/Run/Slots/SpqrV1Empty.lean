/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model

/-!
# SPQR V1 Model on Empty Serialized State

Proves `SendEmptyOk` and `RecvEmptyOk` for `toSpqrModel` and `spqrV1 F K`: on an empty serialized
state `[]`, `spqr::send` and `spqr::recv` decode `inner = None` and return an empty state with no
key, empty message, and zero consumed randomness bytes, allowing `spqrV1` to serve both PQXDH and
empty-PQ Signal-Message sessions.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalSpqrV1

open CryptoVerification.LibsignalTripleRatchet

/-- `toSpqrModel D hkdf` satisfies `SpqrModel.SendEmptyOk`. -/
theorem toSpqrModel_emptyOk (D : SpqrApiDeps) (hkdf : HkdfFn) : (toSpqrModel D hkdf).SendEmptyOk := by
  exact ⟨fun _ => rfl, fun rest => Nat.sub_self rest.length, fun _ => Bool.false_ne_true⟩

/-- `toSpqrModel D hkdf` satisfies `SpqrModel.RecvEmptyOk`. -/
theorem toSpqrModel_recvEmptyOk (D : SpqrApiDeps) (hkdf : HkdfFn) :
    (toSpqrModel D hkdf).RecvEmptyOk := by
  exact ⟨toSpqrModel_recv_empty D hkdf, not_toSpqrModel_recvPanics_empty D hkdf⟩

/-- `spqrV1 F K` satisfies `SpqrModel.SendEmptyOk`. -/
theorem spqrV1_emptyOk (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem) :
    (spqrV1 F K).SendEmptyOk := by
  exact spqrV1_eq F K ▸ toSpqrModel_emptyOk (spqrDeps F K) (spqrHkdfWith F)

/-- `spqrV1 F K` satisfies `SpqrModel.RecvEmptyOk`. -/
theorem spqrV1_recvEmptyOk (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem) :
    (spqrV1 F K).RecvEmptyOk := by
  exact spqrV1_eq F K ▸ toSpqrModel_recvEmptyOk (spqrDeps F K) (spqrHkdfWith F)

end CryptoVerification.LibsignalSpqrV1
