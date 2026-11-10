/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# PQXDH wire-coverage re-exports

Re-exports the `Composed` wire-coverage lemmas from `TripleRatchet.WireCovered` into
`DY.Libsignal.PQXDH.Refinement`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.PQXDH.Refinement
export DY.Libsignal.Composed.Refinement (
  withSentinel withSentinel_ne_canonical encode_withFields knownValue?_tag
  trItemEncode_of_itemWF flatMap_trItemEncode trWireBytes_withSentinel
  trWireBytes_covered_uniform
  trWireBytes_canonical gamma_litOf   gamma_trWireMsg
)
end DY.Libsignal.PQXDH.Refinement
