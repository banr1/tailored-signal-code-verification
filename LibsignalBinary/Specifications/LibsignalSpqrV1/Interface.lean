/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# SPQR V1: receive-model interface (`SpqrRecvModel`)

**Checked by Lean.** No theorem of `Computational/Theorems/` uses `SpqrRecvModel` (see
`Computational/docs/TRUSTED_BASE.md`).

Defines `SpqrRecvModel`, the receive half of an SPQR model retaining the binary's exact key type
`Option (List (BitVec 8))` (`some []` is reachable under DEV-SPQR2, which `SpqrModel`'s 32-byte
`Salt` cannot represent). Kept in this leaf module so `Top.lean` and `Model.lean` can depend on it
without an import cycle.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

/-- The recv half of an SPQR model with the binary's exact key type `spqr::MessageKey =
Option<Vec<u8>>` (`some []` is reachable, DEV-SPQR2). `recv state msg` = `.ok (state', key)` or
`.error sd` with `sd` true exactly for `Error::StateDecode`; `recvPanics state msg` holds when
the call panics. -/
structure SpqrRecvModel where
  recv : List (BitVec 8) → List (BitVec 8) → Except Bool (List (BitVec 8) × Option (List (BitVec 8)))
  recvPanics : List (BitVec 8) → List (BitVec 8) → Prop

end CryptoVerification.LibsignalSpqrV1
