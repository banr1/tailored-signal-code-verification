/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Defs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Entries
public import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.ReprBridge

/-!
# Scope predicates and store-kit bridges for SPQR V1

Defines the SPQR V1 counterparts (`InScopeV1`, `InvV1`, `InMemRecOkV1`, `HonestEnv.paramsS`,
`loadSessionSpecS_pqBound`) of the SPQR-off scope predicates by relaxing `RecordPqEmpty` to
`RecordPqStateLengthBelow2Pow32` (`pqRatchetState.length < 2 ^ 32`), and proves inclusion of the
SPQR-off scopes.
-/

@[expose] public section

namespace CryptoVerification.E2E.V1

set_option autoImplicit false

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.InMem.SessionStoreImpl

/-! ## Record scope `InScopeV1` -/

/-- V1 record scope: `Record.InScope` with `RecordPqStateLengthBelow2Pow32` in place of `RecordPqEmpty`. -/
def InScopeV1 (r : SessionRecord (List (BitVec 8))) : Prop :=
  Record.RecordInScope r ∧ LibsignalSpqrV1.RecordPqStateLengthBelow2Pow32 r ∧ Record.RecordRepr r

theorem recordPqBound_of_recordPqEmpty {r : SessionRecord (List (BitVec 8))} (h : Record.RecordPqEmpty r) :
    LibsignalSpqrV1.RecordPqStateLengthBelow2Pow32 r := by
  exact fun s hs => by simp [h s hs]

theorem inScopeV1_of_inScope {r : SessionRecord (List (BitVec 8))} (h : Record.InScope r) : InScopeV1 r := by
  exact ⟨h.1, recordPqBound_of_recordPqEmpty h.2.1, h.2.2⟩

/-! ## `HonestEnv.paramsS` and reachable-state invariant `InvV1` -/

/-- `HonestEnv.params` parameterized by an arbitrary SPQR model `S` in place of `Record.spqrOffB`. -/
def _root_.CryptoVerification.E2E.Record.HonestEnv.paramsS (E : Record.HonestEnv) {PQC : Type}
    (S : Spqr (List (BitVec 8)) PQC) : Params (List (BitVec 8)) PQC :=
  ⟨E.C, protoSignalCodec, S, E.idOf .A, E.idOf .B,
    serializeAddrVals (serviceIdParse uuidTryParse) (E.addr .A) (E.addr .B),
    serializeAddrVals (serviceIdParse uuidTryParse) (E.addr .B) (E.addr .A)⟩

theorem params_eq_paramsS (E : Record.HonestEnv) : E.params = E.paramsS Record.spqrOffB := by
  rfl

theorem ownId_eq_paramsS (E : Record.HonestEnv) {PQC : Type} (S : Spqr (List (BitVec 8)) PQC) (p : Party) :
    Record.ownId E p = (match p with | .A => (E.paramsS S).idA | .B => (E.paramsS S).idB) := by
  cases p <;> rfl

/-- Reachable-session invariant for V1 (`Record.Inv` with `InScopeV1` in place of `Record.InScope`). -/
def InvV1 (E : Record.HonestEnv) (g : GhostState (List (BitVec 8))) : Prop :=
  InScopeV1 (E.recOf g) ∧ g.session.localIdentity = Record.ownId E g.party ∧
    g.session.remoteIdentity = some (Record.ownId E g.party.other)

theorem invV1_of_inv {E : Record.HonestEnv} {g : GhostState (List (BitVec 8))} (h : Record.Inv E g) :
    InvV1 E g := by
  exact ⟨inScopeV1_of_inScope h.1, h.2⟩

/-! ## In-memory store scope `InMemRecOkV1` -/

/-- Store-side record invariant for an SPQR V1 `InMemSessionStore` (`RecordPqStateLengthBelow2Pow32` in place of `RecordPqEmpty`). -/
def InMemRecOkV1 (r : SessionRecord (List (BitVec 8))) : Prop :=
  Record.RecordInScope r ∧ LibsignalSpqrV1.RecordPqStateLengthBelow2Pow32 r ∧ r.currentSession.isSome

theorem inMemRecOkV1_of_inMemRecOk {r : SessionRecord (List (BitVec 8))} (h : InMemRecOk r) :
    InMemRecOkV1 r := by
  exact ⟨h.1, recordPqBound_of_recordPqEmpty h.2.1, h.2.2⟩

theorem InMemRecOkV1.inScope_isSome {r : SessionRecord (List (BitVec 8))} (h : InMemRecOkV1 r) :
    LibsignalPublicApi.RecordInScope r ∧ r.currentSession.isSome := by
  exact ⟨h.1, h.2.2⟩

/-! ## Store-kit specialization -/

/-- Identifies `loadSessionSpecPqStateLengthBound` with `loadSessionSpecS` at `RecordInScope ∧ RecordPqStateLengthBelow2Pow32`. -/
theorem loadSessionSpecS_pqBound (A : RustAlloc)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    loadSessionSpecS (fun r => LibsignalPublicApi.RecordInScope r ∧ LibsignalSpqrV1.RecordPqStateLengthBelow2Pow32 r)
      A encRecord = LibsignalSpqrV1.loadSessionSpecPqStateLengthBound A encRecord := by
  rfl

end CryptoVerification.E2E.V1
