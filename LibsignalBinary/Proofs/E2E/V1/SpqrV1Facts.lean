/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.V1.BinDefs
import LibsignalBinary.Proofs.E2E.V1.SpqrV1FactsPure

/-!
# SPQR V1 send-message length bound (`SendMsgBoundOn`)

Instantiates `SendMsgBoundOn (spqrV1 F K) Pq` (`sendMsgBoundOn_spqrV1`) from the pure length bound
`spqrV1Send_msg_len_le` in `SpqrV1FactsPure.lean`.
-/

@[expose] public section

namespace CryptoVerification.E2E.V1

set_option autoImplicit false

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1

/-- Every `spqrV1` send message has length `≤ 2 ^ 30`, establishing `SendMsgBoundOn (spqrV1 F K) Pq`. -/
theorem sendMsgBoundOn_spqrV1 (F : ShaCompress) (K : MlKem) (Pq : List (BitVec 8) → Prop) :
    SendMsgBoundOn (spqrV1 F K) Pq := by
  intro st rest st' salt pm _ h
  have := spqrV1Send_msg_len_le F K st rest st' salt pm h
  omega

end CryptoVerification.E2E.V1
