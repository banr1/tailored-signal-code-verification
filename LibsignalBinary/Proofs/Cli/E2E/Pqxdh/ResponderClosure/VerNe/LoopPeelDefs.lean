/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs

/-!
# Decoded `SessionStructure` Inline Peel Definitions

Defines the 344-byte inline `SessionStructure` decomposition `overPrevMovesSS` (exposing the
`local_identity_public` header `(w0, w1, w2)` and `session_version = 4#32` at `+0x148`), the drop
reassembly predicate `overPrevDropFromMovesExt`, and `OverPrevPeelStmtExt`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (prostSSGQAt ssgqOf)

/-- The 344 inline bytes of a v4 `SessionStructure` at `p`, split at the offsets inspected by
`+0x2620 → +0x1fd4`:
- `p + 0x00 .. +0x18`: `local_identity_public` `Vec<u8>` header `(w0, w1, w2)` (`w0.toNat < 2 ^ 63`,
  so `w0 + 1 ≠ 0` and `w0 + 2 ≠ 0`);
- `p + 0x18 .. +0x148`: 304 bytes `r1`;
- `p + 0x148`: `session_version = 4#32`;
- `p + 0x14c .. +0x158`: 12 bytes `r2`. -/
def overPrevMovesSS (p w0 w1 w2 : BitVec 64) (r1 r2 : List (BitVec 8)) : SepProp :=
  (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 0x10#64) ↦₆₄ w2) ∗
  ((p + 0x18#64) ↦ₛ r1) ∗ ((p + 0x148#64) ↦₃₂ 4#32) ∗ ((p + 0x14c#64) ↦ₛ r2)

/-- Reassemble `overPrevMovesSS p w0 w1 w2 r1 r2 ∗ H` back into a `sessionStateAt A p G st`
(`st.sessionVersion = 4#32`) ready for `drop_session_structure3`. -/
def overPrevDropFromMovesExt (A : RustAlloc) (p w0 w1 w2 : BitVec 64)
    (r1 r2 : List (BitVec 8)) (H : SepProp) : Prop :=
  overPrevMovesSS p w0 w1 w2 r1 r2 ∗ H ⊢
    ∃∗ G : SessionGhost, ∃∗ st : SessionState (List (BitVec 8)),
      ⌜st.sessionVersion = 4#32⌝ ∗ sessionStateAt A p G st

abbrev overPrevDropFromMoves (p w0 w1 w2 : BitVec 64) (r1 r2 : List (BitVec 8)) (H : SepProp) : Prop :=
  overPrevDropFromMovesExt A0 p w0 w1 w2 r1 r2 H

/-- For any `A : RustAlloc` and canonical v4 session `sess` with no pending pre-keys,
`prostSSGQAt A p (ssgqOf sess)` decomposes into `overPrevMovesSS p w0 w1 w2 r1 r2 ∗ H` together
with `overPrevDropFromMovesExt A p w0 w1 w2 r1 r2 H`. -/
def OverPrevPeelStmtExt (A : RustAlloc) : Prop :=
  ∀ (sess : Session (List (BitVec 8))),
    DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩ →
    sess.state.sessionVersion = 4#32 →
    sess.pendingKyberPreKey = none →
    ∀ (p : BitVec 64),
      prostSSGQAt A p (ssgqOf sess) ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ∃∗ r1 : List (BitVec 8), ∃∗ r2 : List (BitVec 8), ∃∗ H : SepProp,
          ⌜w0.toNat < 2 ^ 63 ∧ r1.length = 304 ∧ r2.length = 12 ∧
            overPrevDropFromMovesExt A p w0 w1 w2 r1 r2 H⌝ ∗
          overPrevMovesSS p w0 w1 w2 r1 r2 ∗ H

abbrev OverPrevPeelStmt : Prop := OverPrevPeelStmtExt A0

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
