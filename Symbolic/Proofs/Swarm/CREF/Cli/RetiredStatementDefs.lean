/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation

/-!
# Auxiliary Hardware-Event and Pre-Key Predicates

Auxiliary result-buffer and single-session record predicates used by the move-based CLI
refinement proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.HwEvents

/-- Decoded `[len_state: u64 LE][len_msg: u64 LE][state][msg]` result buffer of session entry
points. -/
structure StateAndMessage where
  state : HwBytes
  message : HwBytes

end DY.Libsignal.HwEvents

namespace DY.Libsignal.Composed.Refinement

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)

/-- Every parsed pre-key wire message carries Alice's identity key (`DEV-PQS-IDENTITY`). -/
def HonestIdentity (interpretation : ExternInterpretation) (r : ProtocolSetup) (b : HwBytes) : Prop :=
  ∀ p, parsePreKeyWire b = some p →
    p.identityKey.take 33 = ecKey (pubBytes interpretation (secretBytes r 0))

/-- Event-block index of `opk_removed` in `session_recv_prekey`. -/
abbrev opkRemovedIdx : Nat := 42

/-- Event-block index of `kyber_used` in `session_recv_prekey`. -/
abbrev kyberUsedIdx : Nat := 0

/-- Serialized session record with `previous = []` (`DEV-C-PREV`). -/
def SingleSession (rec : HwBytes) : Prop :=
  ∃ rr, rec = recordBytes rr ∧ rr.previous = []

end DY.Libsignal.Composed.Refinement
