/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PqValid

/-!
# CLI Session-Record Scopes (`scopeKit` and `scopeIn`)

Defines the two `SessionRecord` scopes used across the CLI `run` proof:
- `scopeKit` (`DeserializeScopeP_Q NonEmptyV1Q`): records with SPQR state `< 2^32` bytes, used by
  `cliSessionStoreSpec`, `sessDeserializeSpec`, and `EncodeInjOn`.
- `scopeIn` (`DeserializeScopeP_Q PqInV1`): records with a valid SPQR state `< 2^31` bytes at the
  start of a run (`filesOk₀`), closed into `scopeKit` with encoded length `< 2^32` under one
  encrypt or decrypt step.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Slots

open CryptoGames CryptoGames.LibsignalSessionApi

/-- Store-kit record scope (`DeserializeScopeP_Q NonEmptyV1Q`, SPQR state `< 2^32` bytes). -/
abbrev scopeKit : SessionRecord (List (BitVec 8)) → Prop :=
  Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q

/-- Run-entry record scope (`DeserializeScopeP_Q PqInV1`, valid SPQR state `< 2^31` bytes). -/
abbrev scopeIn : SessionRecord (List (BitVec 8)) → Prop :=
  Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q PqValid.PqInV1

theorem scopeKit_of_scopeIn {r : SessionRecord (List (BitVec 8))} (h : scopeIn r) : scopeKit r := by
  exact ⟨⟨h.1.1, fun s hs => Nat.lt_trans (h.1.2.1 s hs).2 (by omega), h.1.2.2⟩, h.2⟩

end CryptoVerification.SignalSession.Cli.Slots
