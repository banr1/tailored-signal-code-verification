/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Receiver-Counter Freshness and Skipped-Key Index Invariants

Defines `TRRecvCountersFresh`, `TRSkippedRIdxFun`, `TRSkippedRIdxChainRel`, and `TRRecvFreshAll`
for Triple Ratchet snapshots, together with trace-extension transfer lemmas.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Symbolic.Swarm.CREF.TR

cref_open
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain)
open DY.Libsignal.TripleRatchet (TRState TREvent isCurrentSnapshot)

/-- Receiver-counter freshness of snapshot `st` of `p` on `tr`. -/
def TRRecvCountersFresh (tr : ExecTrace) (p : Participant) (st : TRState) : Prop :=
  (∀ c ∈ st.recv,
    (∀ seed pqSalt n pIdx i,
      tr.EventLoggedAt (TREvent.MessageKey (st.sessionInfo p) .receiver seed pqSalt n c.rIdx pIdx) i →
      n < c.index) ∧
    (∀ pk n seed srcIdx i,
      tr.EventLoggedAt (TREvent.SkippedKeyStored (st.sessionInfo p) pk n seed c.rIdx srcIdx) i →
      n < c.index)) ∧
  (∀ seed pqSalt n r pIdx i,
    tr.EventLoggedAt (TREvent.MessageKey (st.sessionInfo p) .receiver seed pqSalt n r pIdx) i →
    r ≤ st.rIdx) ∧
  (∀ pk n seed r srcIdx i,
    tr.EventLoggedAt (TREvent.SkippedKeyStored (st.sessionInfo p) pk n seed r srcIdx) i →
    r ≤ st.rIdx) ∧
  (∀ c ∈ st.recv, c.rIdx ≤ st.rIdx) ∧
  (st.recv.map RecvChain.rIdx).Nodup

/-- Any two `SkippedKeyStored sinfo` events on `tr` with the same `rIdx` carry equal `pk`. -/
def TRSkippedRIdxFun (tr : ExecTrace) (sinfo : SessionInfo) : Prop :=
  ∀ pk₁ n₁ seed₁ srcIdx₁ i₁ pk₂ n₂ seed₂ srcIdx₂ i₂ rIdx,
    tr.EventLoggedAt (TREvent.SkippedKeyStored sinfo pk₁ n₁ seed₁ rIdx srcIdx₁) i₁ →
    tr.EventLoggedAt (TREvent.SkippedKeyStored sinfo pk₂ n₂ seed₂ rIdx srcIdx₂) i₂ →
    pk₁ = pk₂

/-- Functionality of `SkippedKeyStored` by `rIdx` and ratchet-key agreement with `st.recv`. -/
def TRSkippedRIdxChainRel (tr : ExecTrace) (p : Participant) (st : TRState) : Prop :=
  TRSkippedRIdxFun tr (st.sessionInfo p) ∧
  ∀ c ∈ st.recv, ∀ pk n seed srcIdx i,
    tr.EventLoggedAt (TREvent.SkippedKeyStored (st.sessionInfo p) pk n seed c.rIdx srcIdx) i →
    pk = c.ratchetKey

/-- Receiver-counter freshness and skipped-key index invariants across all current snapshots of
`r₀.alice` and `r₀.bob` on `runTraceMoves r₀ ms`. -/
def TRRecvFreshAll (r₀ : ProtocolSetup) (ms : List Move) : Prop :=
  ∀ q stateIdx st,
    (q = r₀.alice ∨ q = r₀.bob) →
    ((PersistentLocalState.getLocalState q stateIdx : Traceful TRState).run (runTraceMoves r₀ ms)).1 = some st →
    isCurrentSnapshot (runTraceMoves r₀ ms) stateIdx = true →
    TRRecvCountersFresh (runTraceMoves r₀ ms) q st ∧ TRSkippedRIdxChainRel (runTraceMoves r₀ ms) q st

/-- `TRRecvCountersFresh` transfers along receiver-event implication for its own session. -/
theorem trRecvCountersFresh_of_imp {tr tr' : ExecTrace} {p : Participant} {st : TRState}
    (hmk : ∀ seed pqSalt n r pIdx i,
      tr'.EventLoggedAt (TREvent.MessageKey (st.sessionInfo p) .receiver seed pqSalt n r pIdx) i →
      tr.EventLoggedAt (TREvent.MessageKey (st.sessionInfo p) .receiver seed pqSalt n r pIdx) i)
    (hsk : ∀ pk n seed r src i,
      tr'.EventLoggedAt (TREvent.SkippedKeyStored (st.sessionInfo p) pk n seed r src) i →
      tr.EventLoggedAt (TREvent.SkippedKeyStored (st.sessionInfo p) pk n seed r src) i)
    (h : TRRecvCountersFresh tr p st) :
    TRRecvCountersFresh tr' p st := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun c hc => ⟨fun seed pqSalt n pIdx i hl =>
      (h1 c hc).1 seed pqSalt n pIdx i (hmk _ _ _ _ _ _ hl),
    fun pk n seed srcIdx i hl => (h1 c hc).2 pk n seed srcIdx i (hsk _ _ _ _ _ _ hl)⟩,
    fun seed pqSalt n r pIdx i hl =>
      h2 seed pqSalt n r pIdx i (hmk _ _ _ _ _ _ hl),
    fun pk n seed r srcIdx i hl => h3 pk n seed r srcIdx i (hsk _ _ _ _ _ _ hl), h4, h5⟩

/-- Frame invariance of `TRSkippedRIdxChainRel` when no new `SkippedKeyStored` events for
`st.sessionInfo p` are added on `tr'`. -/
theorem trSkippedRIdxChainRel_of_imp {tr tr' : ExecTrace} {p : Participant} {st : TRState}
    (himp : ∀ pk n seed rIdx srcIdx i,
      tr'.EventLoggedAt (TREvent.SkippedKeyStored (st.sessionInfo p) pk n seed rIdx srcIdx) i →
      tr.EventLoggedAt (TREvent.SkippedKeyStored (st.sessionInfo p) pk n seed rIdx srcIdx) i)
    (hRel : TRSkippedRIdxChainRel tr p st) :
    TRSkippedRIdxChainRel tr' p st := by
  refine ⟨?_, ?_⟩
  · intro pk₁ n₁ seed₁ srcIdx₁ i₁ pk₂ n₂ seed₂ srcIdx₂ i₂ rIdx h₁ h₂
    exact hRel.1 pk₁ n₁ seed₁ srcIdx₁ i₁ pk₂ n₂ seed₂ srcIdx₂ i₂ rIdx
      (himp pk₁ n₁ seed₁ rIdx srcIdx₁ i₁ h₁)
      (himp pk₂ n₂ seed₂ rIdx srcIdx₂ i₂ h₂)
  · intro c hc pk n seed srcIdx i hlog
    exact hRel.2 c hc pk n seed srcIdx i (himp pk n seed c.rIdx srcIdx i hlog)

end Symbolic.Swarm.CREF.TR
