/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession

/-!
# Canonical 33-Byte Public-Key Serialization Lemmas
-/

@[expose] public section

namespace CryptoGames.LibsignalSession

theorem PublicKey.serialize_length (k : PublicKey) : k.serialize.length = 33 := by
  simp [PublicKey.serialize]

theorem pk_deserialize_len33 {bs : List (BitVec 8)} {k : PublicKey}
    (hd : PublicKey.deserialize bs = .ok k) (hl : bs.length = 33) :
    bs = k.serialize := by
  unfold PublicKey.deserialize at hd
  rcases bs with _ | ⟨t, rest⟩
  · contradiction
  · dsimp only at hd
    split at hd <;> try contradiction
    rename_i h_djb
    split at hd <;> try contradiction
    rename_i h_len
    cases hd
    have ht : t = djbType := Classical.not_not.mp h_djb
    subst ht
    simp only [List.length_cons] at hl
    simp only [PublicKey.serialize, List.cons.injEq, true_and, List.Vector.toList_mk]
    exact (List.take_of_length_le (by omega)).symm

end CryptoGames.LibsignalSession
