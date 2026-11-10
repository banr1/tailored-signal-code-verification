/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyDefs

/-!
# One-Key PQXDH δ Key Indistinguishability: `G0 -> G3` Hop

**Checked by Lean.** Proves `KI1KeyHopG0G3Stmt` (DEV-CLI16, DEV-PQ21) from `keyInd1Key_hop_G0_G3_le`,
which assumes `CryptoWellFormedPrimitivesδ` without perfect KEM correctness.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh
open Proofs.SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

theorem ki1KeyHopG0G3 (S : Setup) : KI1KeyHopG0G3Stmt S :=
  fun P hP b A => keyInd1Key_hop_G0_G3_le S P hP b A

end Proofs.SignalPqxdh.Security.PqxdhDelta
