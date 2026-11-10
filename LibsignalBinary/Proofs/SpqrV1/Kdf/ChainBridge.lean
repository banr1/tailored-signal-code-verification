/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain

/-!
# Bridge Between `hkdfToSlice` / `hkdfToVec` and `spqrHkdfWith`

Shows that for all output lengths `L ≤ 8160` (`255 * 32`), `hkdfToSlice` and `hkdfToVec` succeed
and return `spqrHkdfWith F salt ikm info L`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Kdf

open CryptoGames.HMAC (ShaState)
open CryptoVerification.LibsignalSpqrV1

@[simp]
theorem hkdfToSliceUnchecked_eq_spqrHkdfWith
    (F : ShaState → Bytes → ShaState) (salt ikm info : Bytes) (L : Nat) :
    hkdfToSliceUnchecked F salt ikm info L = spqrHkdfWith F salt ikm info L :=
  rfl

@[simp]
theorem hkdfToVecUnchecked_eq_spqrHkdfWith
    (F : ShaState → Bytes → ShaState) (salt ikm info : Bytes) (L : Nat) :
    hkdfToVecUnchecked F salt ikm info L = spqrHkdfWith F salt ikm info L :=
  rfl

theorem hkdfToSlice_eq_spqrHkdfWith
    (F : ShaState → Bytes → ShaState) (salt ikm info : Bytes) (L : Nat) (hL : L ≤ 8160) :
    hkdfToSlice F salt ikm info L = .ok (spqrHkdfWith F salt ikm info L) :=
  hkdfToSlice_of_le F salt ikm info hL

theorem hkdfToVec_eq_spqrHkdfWith
    (F : ShaState → Bytes → ShaState) (salt ikm info : Bytes) (L : Nat) (hL : L ≤ 8160) :
    hkdfToVec F salt ikm info L = .ok (spqrHkdfWith F salt ikm info L) :=
  hkdfToVec_of_le F salt ikm info hL

end CryptoVerification.SpqrV1.Kdf
