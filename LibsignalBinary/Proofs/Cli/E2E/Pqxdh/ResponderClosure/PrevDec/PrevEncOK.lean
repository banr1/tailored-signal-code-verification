/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3Defs

/-!
# Well-Formedness Predicates for Archived `previous_sessions` Encodings

Defines `OverPrevEncOKAt` and `OverPrevEncOK`, characterizing archived `previous_sessions` byte
slices `enc = encSession sess` for canonical version-4 sessions without pending pre-keys.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open CryptoGames.LibsignalSessionApi (Session)

/-- The archived bytes `enc` are the encoding of the session `sess`: `sess` is in
`DeserializeScopeP_Q NonEmptyV1Q`, has `session_version = 4`, and has neither a pending pre-key nor
a pending Kyber pre-key. -/
def OverPrevEncOKAt (enc : List (BitVec 8)) (sess : Session (List (BitVec 8))) : Prop :=
  enc = CryptoVerification.E2E.Record.encSession sess ∧
    Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q
      ⟨some sess⟩ ∧
    sess.state.sessionVersion = 4#32 ∧
    sess.pendingPreKey = none ∧ sess.pendingKyberPreKey = none

/-- Existential form of `OverPrevEncOKAt`: `enc` encodes a canonical version-4 session with no pending pre-keys. -/
def OverPrevEncOK (enc : List (BitVec 8)) : Prop :=
  ∃ sess : Session (List (BitVec 8)),
    enc = CryptoVerification.E2E.Record.encSession sess ∧
    Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q
      ⟨some sess⟩ ∧
    sess.state.sessionVersion = 4#32 ∧
    sess.pendingPreKey = none ∧ sess.pendingKyberPreKey = none

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
