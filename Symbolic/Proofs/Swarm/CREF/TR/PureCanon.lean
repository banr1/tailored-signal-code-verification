/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.CliPureBytes
public import Symbolic.Proofs.Swarm.CREF.Grow.Defs
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import Symbolic.Specifications.Refinement.ModelTraces

/-!
# Ghost-Free Session Record Canonicity Predicates

Defines ghost-free and machine-free counterparts of `RecordRepr`, `BinCanonSession`,
`slots_InScopeP_Q`, `slots_DeserializeScopeP_Q`, `slots_RecordCanonical_Q`, `WireRecCanon`,
`TRRecordCanon`, and `RecPending` over the canonical protobuf encoder `encSession` / `encodeRecord`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR.Pure

open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (ProtocolSetup)
open Symbolic.Swarm.CREF (SpqrOooBounded)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32)

theorem publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  unfold PublicKey.serialize
  simp [pk.bytes.toList_length]

theorem identityKey_serialize_length (ik : IdentityKey) : ik.serialize.length = 33 :=
  publicKey_serialize_length ik.publicKey

/-- Pure session-record layout side conditions (`RecordRepr` without binary environment imports). -/
def PureRecordRepr (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ s, r.currentSession = some s →
    (∀ c ∈ s.state.receiverChains, c.messageKeys.length ≤ maxMessageKeys) ∧
      (∀ sc, s.state.senderChain = some sc →
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes) ∧
      s.Wf ∧ s.aliceBaseKey.length < 2 ^ 32

/-- Pure ghost-free session canonicity invariant (`Session`-only content of `BinCanonSession`). -/
def PureBinCanonSession (s : Session (List (BitVec 8))) : Prop :=
  s.Wf ∧
  s.state.receiverChains.length ≤ maxReceiverChains ∧
  (∀ rc ∈ s.state.receiverChains, rc.messageKeys.length ≤ maxMessageKeys ∧
    ∀ mkg ∈ rc.messageKeys, mkg.seed.length = 32) ∧
  s.aliceBaseKey.length < 2 ^ 32 ∧
  (match s.pendingKyberPreKey with | none => True | some pkp => pkp.ciphertext.length < 2 ^ 32) ∧
  s.state.pqRatchetState.length < 2 ^ 32 ∧
  (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 62

abbrev slots_SessionScopeP (s : Session (List (BitVec 8))) : Prop :=
  s.state.receiverChains.length ≤ CryptoGames.LibsignalSession.maxReceiverChains ∧
    (∀ p, s.pendingPreKey = some p → p.timestamp = 0) ∧
    (∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length = 1569) ∧
    (s.aliceBaseKey = [] ∨ s.aliceBaseKey.length = 33)

abbrev slots_RecordInScopeP (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ s, r.currentSession = some s →
    SeedsLen32 s.state ∧
      s.state.receiverChains.length < 2 ^ 32 ∧
      ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length < 2 ^ 32

abbrev slots_NonEmptyV1Q : List (BitVec 8) → Prop :=
  fun st => st.length < 2 ^ 32

abbrev slots_RecordScopeP (Q : List (BitVec 8) → Prop)
    (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ s, r.currentSession = some s → Q s.state.pqRatchetState

abbrev slots_InScopeP_Q (Q : List (BitVec 8) → Prop)
    (r : SessionRecord (List (BitVec 8))) : Prop :=
  slots_RecordInScopeP r ∧
  slots_RecordScopeP Q r ∧
  PureRecordRepr r

abbrev slots_DeserializeScopeP_Q (Q : List (BitVec 8) → Prop)
    (r : SessionRecord (List (BitVec 8))) : Prop :=
  slots_InScopeP_Q Q r ∧
  ∃ s, r.currentSession = some s ∧ slots_SessionScopeP s

/-- Ghost-free canonical session record predicate (`RecordCanonical_Q` over `PureBinCanonSession`). -/
abbrev slots_RecordCanonical_Q (Q : List (BitVec 8) → Prop)
    (stateBytes : List (BitVec 8)) (s : Session (List (BitVec 8))) : Prop :=
  stateBytes = CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩ ∧
  slots_DeserializeScopeP_Q Q ⟨some s⟩ ∧
  PureBinCanonSession s

/-- Ghost-free post-wire canonical record predicate. -/
def WireRecCanon (bs : List (BitVec 8)) : Prop :=
  ∃ sess : Session (List (BitVec 8)),
    slots_RecordCanonical_Q slots_NonEmptyV1Q bs sess ∧
    slots_RecordInScopeP ⟨some sess⟩ ∧
    slots_RecordScopeP slots_NonEmptyV1Q ⟨some sess⟩ ∧
    sess.state.remoteIdentity.isSome ∧
    bs.length < 2 ^ 62 ∧
    sess.pendingPreKey = none

/-- Ghost-free Triple Ratchet canonical stored record predicate. -/
def TRRecordCanon (_r₀ : ProtocolSetup) (_p : Participant) (bs : HwBytes) : Prop :=
  ∃ sess : Session (List (BitVec 8)),
    slots_RecordCanonical_Q slots_NonEmptyV1Q bs sess ∧
    slots_RecordInScopeP ⟨some sess⟩ ∧
    slots_RecordScopeP slots_NonEmptyV1Q ⟨some sess⟩ ∧
    sess.state.remoteIdentity.isSome ∧
    bs.length < 2 ^ 62 ∧
    sess.pendingPreKey = none ∧
    bs.length < 2 ^ 32 - 2 ^ 20 ∧
    SpqrOooBounded sess.state.pqRatchetState

/-- Ghost-free pending-prekey canonical record predicate. -/
def RecPending (b : HwBytes) : Prop :=
  ∃ sess : Session (List (BitVec 8)),
    slots_RecordCanonical_Q slots_NonEmptyV1Q b sess ∧
    sess.pendingPreKey.isSome = true

end Symbolic.Swarm.CREF.TR.Pure

namespace Symbolic.Swarm.CREF.TR

abbrev PureRecordRepr := Pure.PureRecordRepr

abbrev PureBinCanonSession := Pure.PureBinCanonSession

abbrev PureTRRecordCanon := Pure.TRRecordCanon

abbrev PureRecPending := Pure.RecPending

end Symbolic.Swarm.CREF.TR
