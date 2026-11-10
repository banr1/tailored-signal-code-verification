/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
public import LibsignalBinary.Proofs.E2E.RecordX.BridgeCommon
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon

/-!
# Widened record scope `DeserializeScopeX` and reachability

**Checked by Lean.** Widens `DeserializeGeneral.SessionScope` to `SessionScopeX` and
`DeserializeScopeX` (allowing `aliceBaseKey` and a zero-ID pending Kyber ciphertext of length
`< 2 ^ 16`), characterizes `SessionScope` as the empty-extras special case, and proves that every
reachable state under `FixedIdRecordExtras` lies in `DeserializeScopeX`.
-/

@[expose] public section

namespace CryptoVerification.E2E.RecordX

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E CryptoVerification.E2E.Record

/-- The current session of `toRecord (extrasOf E) g`. -/
def sessionOfX (E : Party → RecordExtras) (g : GhostState Bytes) : Session Bytes :=
  { state := g.session
    pendingPreKey := if g.session.pendingPreKey then some (E g.party).pending else none
    pendingKyberPreKey := if g.session.pendingPreKey then (E g.party).kyber else none
    localRegistrationId := (E g.party).localRegistrationId
    remoteRegistrationId := (E g.party).remoteRegistrationId
    aliceBaseKey := (E g.party).aliceBaseKey }

theorem toRecord_extrasOf_eq (E : Party → RecordExtras) (g : GhostState Bytes) :
    toRecord (extrasOf E) g = { currentSession := some (sessionOfX E g) } := rfl

theorem sessionOfX_wf (E : Party → RecordExtras) (g : GhostState Bytes) :
    (sessionOfX E g).Wf := by
  unfold sessionOfX Session.Wf
  cases g.session.pendingPreKey <;> rfl

/-- Widened session scope allowing `aliceBaseKey` and a zero-ID pending Kyber ciphertext of length `< 2 ^ 16`. -/
def SessionScopeX (s : Session Bytes) : Prop :=
  s.state.receiverChains.length ≤ maxReceiverChains ∧
    s.localRegistrationId = 0 ∧ s.remoteRegistrationId = 0 ∧
    (∀ p, s.pendingPreKey = some p → p.preKeyId = none ∧ p.signedPreKeyId = 0 ∧ p.timestamp = 0) ∧
    (∀ k, s.pendingKyberPreKey = some k → k.preKeyId = 0 ∧ k.ciphertext.length < 2 ^ 16) ∧
    s.aliceBaseKey.length < 2 ^ 16

/-- `DeserializeGeneral.SessionScope` is `SessionScopeX` with no Kyber pre-key and an empty `alice_base_key`. -/
theorem sessionScope_iff (s : Session Bytes) :
    DeserializeGeneral.SessionScope s ↔
      SessionScopeX s ∧ s.pendingKyberPreKey = none ∧ s.aliceBaseKey = [] := by
  unfold DeserializeGeneral.SessionScope SessionScopeX
  constructor
  · rintro ⟨h1, hk, hl, hr, ha, hp⟩
    refine ⟨⟨h1, hl, hr, hp, ?_, ?_⟩, hk, ha⟩
    · intro k hk'; rw [hk] at hk'; cases hk'
    · rw [ha]; decide
  · rintro ⟨⟨h1, hl, hr, hp, _, _⟩, hk, ha⟩
    exact ⟨h1, hk, hl, hr, ha, hp⟩

/-- Widened record scope combining `InScope` with `SessionScopeX` on the current session. -/
def DeserializeScopeX (r : SessionRecord Bytes) : Prop :=
  InScope r ∧ ∃ s, r.currentSession = some s ∧ SessionScopeX s

theorem deserializeScope_iff (r : SessionRecord Bytes) :
    DeserializeGeneral.DeserializeScope r ↔
      DeserializeScopeX r ∧ ∀ s, r.currentSession = some s →
        s.pendingKyberPreKey = none ∧ s.aliceBaseKey = [] := by
  unfold DeserializeGeneral.DeserializeScope DeserializeScopeX
  constructor
  · rintro ⟨hin, s, hs, hsc⟩
    obtain ⟨hx, hk, ha⟩ := (sessionScope_iff s).1 hsc
    refine ⟨⟨hin, s, hs, hx⟩, ?_⟩
    intro s' hs'
    rw [hs] at hs'; cases hs'
    exact ⟨hk, ha⟩
  · rintro ⟨⟨hin, s, hs, hx⟩, h⟩
    exact ⟨hin, s, hs, (sessionScope_iff s).2 ⟨hx, h s hs⟩⟩

/-! ## Reachability of `DeserializeScopeX` -/

section Reach
variable (Z : EParams) (E : Party → RecordExtras) (hE : ∀ P, FixedIdRecordExtras (E P))
include hE

theorem reach_sessionScopeX {g : GhostState Bytes} (hg : Reach Z.params g) :
    SessionScopeX (sessionOfX E g) := by
  obtain ⟨hr, hl, hpid, hspk, hts, hk, ha⟩ := hE g.party
  refine ⟨Reach.reach_receiverChains_le Z hg, hl, hr, ?_, ?_, ha⟩
  · intro p hp
    unfold sessionOfX at hp
    dsimp only at hp
    split at hp
    · injection hp with hp'
      subst hp'
      exact ⟨hpid, hspk, hts⟩
    · cases hp
  · intro k hk'
    unfold sessionOfX at hk'
    dsimp only at hk'
    split at hk'
    · exact hk k hk'
    · cases hk'

theorem reach_inScopeX {g : GhostState Bytes} (hg : Reach Z.params g) :
    InScope (toRecord (extrasOf E) g) := by
  rw [toRecord_extrasOf_eq]
  obtain ⟨_, _, _, _, _, hk, ha⟩ := hE g.party
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    injection hs with hs'
    subst hs'
    refine ⟨Reach.reach_remoteIdentity_ne_local Z hg, Reach.reach_seedsLen32 Z hg,
      Reach.reach_receiverChains_lt Z hg, ?_⟩
    intro k hk'
    unfold sessionOfX at hk'
    dsimp only at hk'
    split at hk'
    · exact Nat.lt_trans (hk k hk').2 (by decide)
    · cases hk'
  · intro s hs
    injection hs with hs'
    subst hs'
    exact Reach.reach_pqRatchetState_eq_nil Z hg
  · intro s hs
    injection hs with hs'
    subst hs'
    exact ⟨Reach.reach_messageKeys_le Z hg, Reach.reach_senderKey_clamped Z hg,
      sessionOfX_wf E g, Nat.lt_trans ha (by decide)⟩

/-- Every reachable record under `FixedIdRecordExtras` lies in `DeserializeScopeX`. -/
theorem reach_deserializeScopeX {g : GhostState Bytes} (hg : Reach Z.params g) :
    DeserializeScopeX (toRecord (extrasOf E) g) :=
  ⟨reach_inScopeX Z E hE hg, sessionOfX E g, rfl, reach_sessionScopeX Z E hE hg⟩

end Reach

end CryptoVerification.E2E.RecordX
