/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem

/-!
# SPQR V1: ML-KEM first-step totality (`Encaps1Total`)

**Checked by Lean.** No headline of `Computational/Theorems/` uses `Encaps1Total` (the composed
SPQR V1 statements assume `E2E.Encaps1Total` in
`Computational/Specifications/Session/StatementComposed.lean`; see
`Computational/docs/TRUSTED_BASE.md`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1

/-- `K.encaps1` succeeds on every 64-byte public-key header `hdr` and 32-byte randomness `rand`. -/
def Encaps1Total (K : MlKem) : Prop :=
  ∀ (hdr : Bytes) (rand : List.Vector (BitVec 8) 32), hdr.length = 64 → (K.encaps1 hdr rand).isSome

end CryptoVerification.SpqrV1Sync.SendTotal
