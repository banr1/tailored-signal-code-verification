/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.RecordX.Scope
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon
import LibsignalBinary.Proofs.E2E.RecordX.Length

/-!
# PQXDH decoder scope `DeserializeScopeP` and reachability

**Checked by Lean.** Defines the PQXDH record decoder scopes `SessionScopeP`, `DeserializeScopeP`,
and `DeserializeScopeBounded` (arbitrary `u32` registration and pre-key IDs, `timestamp = 0`,
1569-byte ML-KEM-1024 ciphertext, empty or 33-byte `aliceBaseKey`, and arbitrary identity pairs),
and proves that reachable states under `ExtrasPqxdh` satisfy `DeserializeScopeP`.
-/

@[expose] public section

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSession

/-- PQXDH extras invariant: `pending.timestamp = 0`, 1569-byte Kyber ciphertext (if present), and empty or 33-byte `aliceBaseKey`. -/
def ExtrasPqxdh (x : RecordExtras) : Prop :=
  x.pending.timestamp = 0 ∧
    (∀ k, x.kyber = some k → k.ciphertext.length = 1569) ∧
    (x.aliceBaseKey = [] ∨ x.aliceBaseKey.length = 33)

end CryptoVerification.E2E

namespace CryptoVerification.E2E.RecordX

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32)

/-- PQXDH decoder session scope: bounded `receiverChains`, `timestamp = 0`, 1569-byte Kyber ciphertext, and empty or 33-byte `aliceBaseKey`. -/
def SessionScopeP (s : Session Bytes) : Prop :=
  s.state.receiverChains.length ≤ maxReceiverChains ∧
    (∀ p, s.pendingPreKey = some p → p.timestamp = 0) ∧
    (∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length = 1569) ∧
    (s.aliceBaseKey = [] ∨ s.aliceBaseKey.length = 33)

/-- `RecordInScope` without the `remoteIdentity ≠ some localIdentity` side condition. -/
def RecordInScopeP (r : SessionRecord Bytes) : Prop :=
  ∀ s, r.currentSession = some s →
    SeedsLen32 s.state ∧
      s.state.receiverChains.length < 2 ^ 32 ∧
      ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length < 2 ^ 32

/-- `InScope` without `s.state.remoteIdentity ≠ some s.state.localIdentity`. -/
def InScopeP (r : SessionRecord Bytes) : Prop :=
  RecordInScopeP r ∧ RecordPqEmpty r ∧ RecordRepr r

/-- PQXDH decoder record scope combining `InScopeP` with `SessionScopeP` on the current session. -/
def DeserializeScopeP (r : SessionRecord Bytes) : Prop :=
  InScopeP r ∧ ∃ s, r.currentSession = some s ∧ SessionScopeP s

theorem recordInScopeP_of_recordInScope {r : SessionRecord Bytes} (h : RecordInScope r) :
    RecordInScopeP r :=
  fun s hs => (h s hs).2

theorem inScopeP_of_inScope {r : SessionRecord Bytes} (h : InScope r) : InScopeP r :=
  ⟨recordInScopeP_of_recordInScope h.1, h.2⟩

/-- Selects `partyIdentityKey .A` or `partyIdentityKey .B` distinct from `rem`. -/
def freshLocalId (rem : Option IdentityKey) : IdentityKey :=
  if rem = some (partyIdentityKey .A) then partyIdentityKey .B else partyIdentityKey .A

theorem remoteIdentity_ne_freshLocalId (rem : Option IdentityKey) :
    rem ≠ some (freshLocalId rem) := by
  unfold freshLocalId
  split_ifs with h
  · rw [h]; decide
  · exact h

theorem sessionScopeP_of_sessionScope {s : Session Bytes} (h : DeserializeGeneral.SessionScope s) :
    SessionScopeP s := by
  obtain ⟨h1, hk, _, _, ha, hp⟩ := h
  refine ⟨h1, ?_, ?_, Or.inl ha⟩
  · intro p hp'
    exact (hp p hp').2.2
  · intro k hk'; rw [hk] at hk'; cases hk'

theorem deserializeScopeP_of_deserializeScope {r : SessionRecord Bytes} (h : DeserializeGeneral.DeserializeScope r) : DeserializeScopeP r := by
  obtain ⟨hin, s, hs, hsc⟩ := h
  exact ⟨inScopeP_of_inScope hin, s, hs, sessionScopeP_of_sessionScope hsc⟩

theorem extrasPqxdh_abk_lt {x : RecordExtras} (h : ExtrasPqxdh x) :
    x.aliceBaseKey.length < 2 ^ 16 := by
  obtain ⟨_, _, ha⟩ := h
  rcases ha with ha | ha
  · rw [ha]; decide
  · rw [ha]; decide

theorem extrasPqxdh_kyber_lt {x : RecordExtras} (h : ExtrasPqxdh x) :
    ∀ k, x.kyber = some k → k.ciphertext.length < 2 ^ 16 := by
  obtain ⟨_, hk, _⟩ := h
  intro k hk'
  rw [hk k hk']; decide


/-- Bounded-extras session scope unifying `SessionScopeX`, `SessionScopeP`, and `DeserializeGeneral.SessionScope`:
at most `maxReceiverChains` receiver chains, `timestamp = 0` on any pending pre-key,
`aliceBaseKey.length < 2 ^ 16`, and `ciphertext.length < 2 ^ 16` on any pending Kyber pre-key. -/
def SessionScopeBounded (s : Session Bytes) : Prop :=
  s.state.receiverChains.length ≤ maxReceiverChains ∧
    (∀ p, s.pendingPreKey = some p → p.timestamp = 0) ∧
    (∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length < 2 ^ 16) ∧
    s.aliceBaseKey.length < 2 ^ 16

/-- Bounded-extras record scope unifying `DeserializeScopeX`, `DeserializeScopeP`, and `DeserializeGeneral.DeserializeScope`. -/
def DeserializeScopeBounded (r : SessionRecord Bytes) : Prop :=
  InScopeP r ∧ ∃ s, r.currentSession = some s ∧ SessionScopeBounded s

theorem sessionScopeBounded_of_sessionScopeX {s : Session Bytes} (h : SessionScopeX s) :
    SessionScopeBounded s := by
  obtain ⟨hc, _, _, hp, hk, ha⟩ := h
  exact ⟨hc, fun p hp' => (hp p hp').2.2, fun k hk' => (hk k hk').2, ha⟩

theorem deserializeScopeBounded_of_deserializeScopeX {r : SessionRecord Bytes} (h : DeserializeScopeX r) :
    DeserializeScopeBounded r := by
  obtain ⟨hin, s, hs, hsc⟩ := h
  exact ⟨inScopeP_of_inScope hin, s, hs, sessionScopeBounded_of_sessionScopeX hsc⟩

theorem sessionScopeBounded_of_sessionScopeP {s : Session Bytes} (h : SessionScopeP s) :
    SessionScopeBounded s := by
  obtain ⟨hc, hp, hk, ha⟩ := h
  refine ⟨hc, hp, fun k hk' => ?_, ?_⟩
  · rw [hk k hk']; decide
  · rcases ha with ha | ha <;> rw [ha] <;> decide

theorem deserializeScopeBounded_of_deserializeScopeP {r : SessionRecord Bytes} (h : DeserializeScopeP r) :
    DeserializeScopeBounded r := by
  obtain ⟨hin, s, hs, hsc⟩ := h
  exact ⟨hin, s, hs, sessionScopeBounded_of_sessionScopeP hsc⟩

theorem deserializeScopeBounded_of_deserializeScope {r : SessionRecord Bytes} (h : DeserializeGeneral.DeserializeScope r) :
    DeserializeScopeBounded r :=
  deserializeScopeBounded_of_deserializeScopeP (deserializeScopeP_of_deserializeScope h)

/-! ## Reachability of `DeserializeScopeP` -/

section Reach
variable (Z : EParams) (E : Party → RecordExtras) (hE : ∀ P, ExtrasPqxdh (E P))
include hE

theorem reach_sessionScopeP {g : GhostState Bytes} (hg : Reach Z.params g) :
    SessionScopeP (sessionOfX E g) := by
  obtain ⟨hts, hk, ha⟩ := hE g.party
  refine ⟨Reach.reach_receiverChains_le Z hg, ?_, ?_, ha⟩
  · intro p hp
    unfold sessionOfX at hp
    dsimp only at hp
    split at hp
    · injection hp with hp'
      subst hp'
      exact hts
    · cases hp
  · intro k hk'
    unfold sessionOfX at hk'
    dsimp only at hk'
    split at hk'
    · exact hk k hk'
    · cases hk'

theorem reach_inScopeP {g : GhostState Bytes} (hg : Reach Z.params g) :
    InScopeP (toRecord (extrasOf E) g) := by
  rw [toRecord_extrasOf_eq]
  have hk := extrasPqxdh_kyber_lt (hE g.party)
  have ha := extrasPqxdh_abk_lt (hE g.party)
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    injection hs with hs'
    subst hs'
    refine ⟨Reach.reach_seedsLen32 Z hg, Reach.reach_receiverChains_lt Z hg, ?_⟩
    intro k hk'
    unfold sessionOfX at hk'
    dsimp only at hk'
    split at hk'
    · exact Nat.lt_trans (hk k hk') (by decide)
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

/-- Every reachable record under `ExtrasPqxdh` lies in `DeserializeScopeP`. -/
theorem reach_deserializeScopeP {g : GhostState Bytes} (hg : Reach Z.params g) :
    DeserializeScopeP (toRecord (extrasOf E) g) :=
  ⟨reach_inScopeP Z E hE hg, sessionOfX E g, rfl, reach_sessionScopeP Z E hE hg⟩

/-- Every reachable record under `ExtrasPqxdh` encodes to fewer than `2 ^ 32` bytes. -/
theorem reach_encodeRecordX_length_lt_of_pqxdh {g : GhostState Bytes} (hg : Reach Z.params g) :
    (encodeRecordUnderExtras E g).length < 2 ^ 32 :=
  reach_encodeRecordX_length_lt Z E (fun P => extrasPqxdh_abk_lt (hE P))
    (fun P => extrasPqxdh_kyber_lt (hE P)) hg

end Reach

end CryptoVerification.E2E.RecordX
