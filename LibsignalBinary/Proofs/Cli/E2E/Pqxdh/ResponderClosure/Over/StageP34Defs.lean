/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.HeapDefs

/-!
# Stage P3 and Stage P4 1-Element `previous_sessions` Heap Re-Exports

Re-exports the `Over.HeapDefs` predicates (`prevElem`, `HdrP`, `prevVecAt`, `recCurAt`,
`sessionRecordPrevAt`) under `OverP34` for Stage P3 and Stage P4.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr

theorem sessionRecordAt_eq_prevP34At (A : RustAlloc) (r : BitVec 64) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) :
    sessionRecordAt A r g rec = sessionRecordPrevAt A r g [] rec := by
  unfold sessionRecordAt sessionRecordPrevAt recCurAt
  cases g.cur <;> cases rec.currentSession <;> rfl

theorem sessionRecordPrevP34At_some (A : RustAlloc) (r cap q : BitVec 64) (G : SessionGhost)
    (ps : List (List (BitVec 8))) (s : Session (List (BitVec 8))) :
    sessionRecordPrevAt A r ⟨cap, q, some G⟩ ps ⟨some s⟩ =
      prevVecAt A r cap q ps ∗ sessionStateReprAt A (r + 0x18#64) G s :=
  rfl

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP34
end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP34
