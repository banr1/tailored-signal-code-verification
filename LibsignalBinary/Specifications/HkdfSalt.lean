/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.Vector.Defs

/-!
# HKDF Salt Type

**Trusted: definitions used by the statement.** Leaf definition of `CryptoGames.HKDF.Salt`, an
optional 32-byte HKDF salt (`none` = no salt) shared between `CryptoGames/AEAD/HKDFDefs.lean` and
`LibsignalSpqr.lean` without pulling `CryptoGames` / VCVio into the symbolic statement closure.
-/

@[expose] public section

namespace CryptoGames
namespace HKDF

/-- A 32-byte HKDF salt (`spqr` message key); `none` = no salt. -/
abbrev Salt := Option (List.Vector (BitVec 8) 32)

end HKDF
end CryptoGames
