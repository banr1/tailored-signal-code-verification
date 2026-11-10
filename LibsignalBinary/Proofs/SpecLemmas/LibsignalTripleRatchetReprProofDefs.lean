/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.AsmConstants
public import Init.Data.String.Defs

/-!
# Proof-Side `SessionGhost` Frame Relations

Defines `SessionGhost.AgreeExceptPq` and `SessionGhost.AfterOutgoingRatchetApply` for
`OutgoingTripleRatchet::{from_session_state, apply_to_session_state}` frame updates.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchetRepr
open Arm64 CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- `G'` is `G` except possibly the pq pin (`OTR::from_session_state` takes the pq state and, on
its version / identity errors, frees it). -/
def SessionGhost.AgreeExceptPq (G G' : SessionGhost) : Prop :=
  G' = { G with pq := G'.pq }

/-- The ghost after `OTR::apply_to_session_state`: only the sender chain's chain-key pin and the pq
pin change. -/
def SessionGhost.AfterOutgoingRatchetApply (G G' : SessionGhost) : Prop :=
  ∃ sg sg', G.sender = some sg ∧ G'.sender = some sg' ∧ sg' = { sg with ck := sg'.ck } ∧
    G' = { G with sender := some sg', pq := G'.pq }

end CryptoVerification.LibsignalTripleRatchetRepr
