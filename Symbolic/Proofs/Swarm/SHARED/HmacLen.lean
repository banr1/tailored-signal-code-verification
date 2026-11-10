/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.SHARED.HookAuthPure

/-!
# External HMAC Tag-Length Projection

Projects `ExternCryptoLawsHold.hmac_tag_length` to `hmacFnOf i` (`hmacLen_of_ceh`) and unfolds
`PQXDH.Refinement.libcruxHmacSymbol`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.SHARED.HmacLen

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open Symbolic.Swarm.SHARED.HookAuth (hmacFnOf)

@[simp]
theorem pq_libcruxHmacSymbol_eq :
    DY.Libsignal.PQXDH.Refinement.libcruxHmacSymbol = "libcrux_hmac::hmac" := rfl

/-- Projects `ExternCryptoLawsHold.hmac_tag_length` to `hmacFnOf i`. -/
theorem hmacLen_of_ceh {i : ExternInterpretation} (h : ExternCryptoLawsHold i) :
    ∀ k d t, hmacFnOf i k d = some t → t.length = 32 :=
  fun k d t ht => h.hmac_tag_length k d t ht

end Symbolic.Swarm.SHARED.HmacLen
