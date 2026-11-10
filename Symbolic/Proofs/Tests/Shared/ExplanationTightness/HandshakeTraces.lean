/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.Composed.HonestSession
import Init.Data.String.Defs
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

@[expose] public section

set_option autoImplicit false

/-!
# Shared Handshake Session-State Exposure Witness Traces

Constructs three reachable, compromise-free witness traces extending the honest handshake trace
`t8`: `trExpSpqrA` (exposing Alice's initial SPQR state `stA0.spqr` to reveal `keys1.pqr`),
`trExpSpqrB` (exposing Bob's stored SPQR state `stB1.spqr` to reveal `keys1.pqr`), and `trExpCkrA`
(exposing Alice's initial receiving chain key on `stA0` to reveal `keys1.ck`).
-/

namespace Symbolic.Proofs.Tests.Shared.ExplanationTightness.HandshakeTraces

open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (cA0 dhsA ikA ikB keys1
  o1 pqm0 pqskB spkB stA0 stB0' stB1 t1 t1_length t2 t2_length t3 t3_length
  t4 t4_length t5 t5_handshakeSessionA_at t5_stA0_at t6 t7 t8 t8_aliceDone_at t8_bobDone_at
  t8_handshakeSessionB_at t8_length t8_noCompromise t8_reach t8_stB1_at)
open Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas (attacker_knows_spqrInit_args
  attacker_knows_spqrRecv_args)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (EvC EvP NetE Runs Runs.exposeCkr Runs.exposeSpqr
  Runs.genPQPrekey Runs.genSignedPrekey Runs.registerIdentity StP StT aliceSt aliceTr aliceTrOpt
  encTr exposeCkrTr exposeKey_reachable exposeSpqrTr exposeSpqr_reachable genPQPrekeyTr
  genSignedPrekeyTr reach_of_runs registerIdentityTr rnd)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.Comparse DY.DiffieHellman DY.PQKem
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open TripleRatchet (RecvChain SessionInfo KeyDir KeyComponent TRState TREvent spqrA2B spqrB2A
  findRecvChain)
open PQXDH (PQXDHEvent HandshakeKeys IsHandshakeBlock HandshakeKeysAt SessionStateExposed
  AliceHandshakeWasCompromised BobHandshakeWasCompromised NoCompromise FSPremise HNDLPremise SIPremise)

/-! ## Generic event-absence helpers on concrete traces -/

private theorem snoc_le (tr : ExecTrace) (entry : ExecTrace.Entry) : tr ≤ Trace.snoc tr entry :=
  Trace.le.extend tr tr entry (Trace.le_refl tr)

/-- Collects all events of type `E` logged on `tr` (newest first). -/
def eventsOn (E : Type) [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)] :
    ExecTrace → List E
  | .nil => []
  | .snoc tr entry =>
    match (TraceEntryHas.proj entry : Option (ProtocolEvent.ExecEntryT E)) with
    | some ⟨ev⟩ => ev :: eventsOn E tr
    | none => eventsOn E tr

theorem mem_eventsOn_of_loggedAt {E : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)] {ev : E} {i : Nat} :
    ∀ {tr : ExecTrace}, tr.EventLoggedAt ev i → ev ∈ eventsOn E tr
  | .nil, h =>
    absurd (Symbolic.DYBridge.DY.Trace.length_eq_1 ▸
      Trace.EventLoggedAt_implies_i_le_length ev i _ h) (Nat.not_lt_zero i)
  | .snoc tr entry, h => by
    have hlt : i < (Trace.snoc tr entry).length :=
      Trace.EventLoggedAt_implies_i_le_length ev i _ h
    have hlen : (Trace.snoc tr entry).length = tr.length + 1 :=
      Symbolic.DYBridge.DY.Trace.length_eq_2 tr entry
    rcases (show i < tr.length ∨ i = tr.length by omega) with hi | rfl
    · have hmem := mem_eventsOn_of_loggedAt
        (Trace.EventLoggedAt_le' ev i tr (Trace.snoc tr entry) hi (snoc_le tr entry) h)
      dsimp only [eventsOn]
      split
      · exact List.mem_cons_of_mem _ hmem
      · exact hmem
    · simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h
      simp only [Trace.at?, hlt, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2] at h
      dsimp only [eventsOn]; rw [h]; exact List.Mem.head _

theorem no_ev {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    {tr : ExecTrace} {p : E → Bool} (h : (eventsOn E tr).filter p = [])
    {ev : E} (hlog : tr.EventLogged ev) (hp : p ev = true) : False :=
  let ⟨_, hi⟩ := hlog
  List.not_mem_nil (h ▸ List.mem_filter.mpr ⟨mem_eventsOn_of_loggedAt hi, hp⟩)

/-- Collects all events of type `E` logged on `tr` at indices `≥ bound` (newest first). -/
def eventsFrom (E : Type) [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    (bound : Nat) : ExecTrace → List E
  | .nil => []
  | .snoc tr entry =>
    if bound ≤ tr.length then
      match (TraceEntryHas.proj entry : Option (ProtocolEvent.ExecEntryT E)) with
      | some ⟨ev⟩ => ev :: eventsFrom E bound tr
      | none => eventsFrom E bound tr
    else []

theorem mem_eventsFrom_of_loggedAt {E : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)] {bound : Nat} {ev : E} {i : Nat}
    (hbi : bound ≤ i) : ∀ {tr : ExecTrace}, tr.EventLoggedAt ev i → ev ∈ eventsFrom E bound tr
  | .nil, h =>
    absurd (Symbolic.DYBridge.DY.Trace.length_eq_1 ▸
      Trace.EventLoggedAt_implies_i_le_length ev i _ h) (Nat.not_lt_zero i)
  | .snoc tr entry, h => by
    have hlt : i < (Trace.snoc tr entry).length :=
      Trace.EventLoggedAt_implies_i_le_length ev i _ h
    have hlen : (Trace.snoc tr entry).length = tr.length + 1 :=
      Symbolic.DYBridge.DY.Trace.length_eq_2 tr entry
    have hb_le : bound ≤ tr.length := by omega
    rcases (show i < tr.length ∨ i = tr.length by omega) with hi | rfl
    · have hmem := mem_eventsFrom_of_loggedAt hbi
        (Trace.EventLoggedAt_le' ev i tr (Trace.snoc tr entry) hi (snoc_le tr entry) h)
      simp only [eventsFrom, hb_le, ↓reduceIte]
      split
      · exact List.mem_cons_of_mem _ hmem
      · exact hmem
    · simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h
      simp only [Trace.at?, hlt, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2] at h
      simp only [eventsFrom, hb_le, ↓reduceIte, h]
      exact List.Mem.head _

theorem no_ev_from {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    {tr : ExecTrace} {bound : Nat} {p : E → Bool}
    (h : (eventsFrom E bound tr).filter p = []) {ev : E} {j : Nat}
    (hbj : bound ≤ j) (hj : tr.EventLoggedAt ev j) (hp : p ev = true) : False :=
  List.not_mem_nil (h ▸ List.mem_filter.mpr ⟨mem_eventsFrom_of_loggedAt hbj hj, hp⟩)

theorem hs_mem {tr : ExecTrace} {l : List (SessionInfo × Nat)}
    (hl : (eventsOn ComposedEvent tr).filterMap (fun | ComposedEvent.HandshakeSession s j => some (s, j)) = l)
    {s : SessionInfo} {j : Nat} (h : tr.EventLogged (ComposedEvent.HandshakeSession s j)) :
    (s, j) ∈ l :=
  let ⟨_, hi⟩ := h
  hl ▸ List.mem_filterMap.mpr ⟨_, mem_eventsOn_of_loggedAt hi, rfl⟩

private theorem ak_net_sent {tr : ExecTrace} {m : Bytes} {i : Nat} (h : tr.MessageSentAt m i) :
    m.AttackerKnows tr :=
  Trace.MessageSentAt_implies_AttackerKnows _ _ _ h

set_option synthInstance.maxHeartbeats 100000 in
theorem ak_spqrInit_authKey {tr : ExecTrace} {authKey params : Bytes}
    (h : (Spqr.spqrInit authKey params).AttackerKnows tr) :
    authKey.AttackerKnows tr :=
  (attacker_knows_spqrInit_args authKey params tr h).1

/-! ## Compromise-Absence Corollaries -/

theorem not_thm7Excuse_of_noCompromise {tr : ExecTrace} (hno : NoCompromise tr)
    {b : Participant} {ikB spk pqpk : Bytes} {i : Nat} :
    ¬ AliceHandshakeWasCompromised b ikB spk pqpk i tr := by
  rintro (⟨j, hj, _⟩ | ⟨j, hj, _⟩)
  · exact hno.1 b ikB ⟨j, hj⟩
  · exact hno.2.2.2.2.1 ⟨j, hj⟩

theorem not_thm9Excuse_of_noCompromise {tr : ExecTrace} (hno : NoCompromise tr)
    {b a : Participant} {ikB ikA spk pqpk : Bytes} {opk : Option Bytes} {i : Nat} :
    ¬ BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr := by
  rintro ((⟨j, hj, _⟩ | ⟨j, hj, _⟩ | ⟨j, hj, _⟩) | ⟨hI, _⟩ | ⟨hD, _⟩)
  · exact hno.1 a ikA ⟨j, hj⟩
  · exact hno.2.1 b spk ⟨j, hj⟩
  · exact hno.2.2.2.2.1 ⟨j, hj⟩
  · exact hno.1 b ikB hI
  · exact hno.2.2.2.2.1 hD

theorem fsPremise_of_noCompromise {tr : ExecTrace} (hno : NoCompromise tr)
    (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat) :
    FSPremise a b ikA ikB spk pqpk i tr :=
  ⟨fun j hj => (hno.1 a ikA ⟨j, hj⟩).elim,
   fun j hj => (hno.1 b ikB ⟨j, hj⟩).elim,
   hno.2.1 b spk, hno.2.2.1 b pqpk, hno.2.2.2.2.1, hno.2.2.2.2.2⟩

theorem hndlPremise_of_noCompromise {tr : ExecTrace} (hno : NoCompromise tr)
    (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat) :
    HNDLPremise a b ikA ikB spk pqpk i tr :=
  ⟨fun j hj => (hno.2.2.2.2.1 ⟨j, hj⟩).elim,
   hno.2.2.2.2.2, hno.1 a ikA, hno.1 b ikB, hno.2.1 b spk, hno.2.2.1 b pqpk⟩

theorem siPremise_of_noCompromise {tr : ExecTrace} (hno : NoCompromise tr)
    (a b : Participant) (ikA ikB spk pqpk : Bytes) (opk : Option Bytes) :
    SIPremise a b ikA ikB spk pqpk opk tr :=
  ⟨hno.1 a ikA, hno.1 b ikB, hno.2.2.2.2.1, hno.2.2.2.2.2,
   fun s hs => (hno.2.1 b s hs).elim,
   fun q hq => (hno.2.2.1 b q hq).elim,
   fun o ho => (hno.2.2.2.1 b o ho).elim⟩

/-! ## Witness Traces -/

/-- `t8` followed by `exposeSpqr "alice" 30` on `stA0` (`ExposedSpqr` at 54, network at 55). -/
def trExpSpqrA : ExecTrace := exposeSpqrTr t8 "alice" stA0

/-- `t8` followed by `exposeSpqr "bob" 53` on `stB1` (`ExposedSpqr` at 54, network at 55). -/
def trExpSpqrB : ExecTrace := exposeSpqrTr t8 "bob" stB1

/-- `t8` followed by `exposeKey "alice" 30 (.ckr (dhPk spkB))` on `stA0` (`ExposedCKr` at 54,
network at 55). -/
def trExpCkrA : ExecTrace := exposeCkrTr t8 "alice" stA0 cA0

abbrev trPqr : ExecTrace := trExpSpqrA
abbrev trPqrB : ExecTrace := trExpSpqrB
abbrev trCkr : ExecTrace := trExpCkrA

private theorem append_len_local {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem le_append_local {E : Type} [ExecTraceTypes.Has E] {ta tb : ExecTrace}
    (h : ta ≤ tb) (e : E) : ta ≤ tb.append e :=
  Trace.le_trans _ _ _ h (Trace.append_le tb e)

private theorem at?_mono_local {E : Type} [ExecTraceTypes.Has E] {ta tb : ExecTrace}
    {i : Nat} {x : E} (hle : ta ≤ tb) (h : ta.at? i = some x) : tb.at? i = some x := by
  have := Trace.at?_le (EntryT := E) ta tb i hle
  rwa [h] at this

private theorem at?_append_at_local {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    {i : Nat} (hi : tr.length = i) : (tr.append e).at? i = some e := by
  subst hi; exact Trace.at?_append tr e

private theorem at?_append_self_proj_local {E1 E2 : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2] (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hlt : tr.length < (tr.snoc (TraceEntryHas.inj e)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.lt_succ_self]
  simp only [Trace.at?, hlt, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2]

private theorem at?_append_of_lt_local {E1 E2 : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = tr.at? i := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hi' : i < (tr.snoc (TraceEntryHas.inj e)).length := by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  have hne : i ≠ tr.length := by omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2, hne]

private theorem eventLoggedAt_mono_local {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {ta tb : ExecTrace} {ev : Ev} {i : Nat} (hle : ta ≤ tb) (h : ta.EventLoggedAt ev i) :
    tb.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono_local hle h

private theorem runs_cast_local {α : Type} {x : Traceful α} {tr ta tb : ExecTrace} {a1 a2 : α}
    (h : Runs x tr a1 ta) (ha : a1 = a2) (ht : ta = tb) : Runs x tr a2 tb := by
  subst ha; subst ht; exact h

private theorem encTr_le_local (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) : tr ≤ encTr tr me stH st pq := by
  dsimp only [encTr]
  exact le_append_local (le_append_local (le_append_local (le_append_local (le_append_local
    (le_append_local (Trace.append_le _ _) _) _) _) _) _) _

private theorem t5_le_t8_local : t5 ≤ t8 := by
  have h57 : t5 ≤ t7 := Trace.le_trans _ _ _ (encTr_le_local _ _ _ _ _) (encTr_le_local _ _ _ _ _)
  have h78 : t7 ≤ t8 := by
    dsimp only [t8]
    exact le_append_local (le_append_local (le_append_local (le_append_local (le_append_local
      (le_append_local (le_append_local (le_append_local (Trace.append_le _ _) _) _) _) _) _) _) _) _
  exact Trace.le_trans _ _ _ h57 h78

theorem trExpSpqrA_length : trExpSpqrA.length = 56 := by
  simp only [trExpSpqrA, exposeSpqrTr, append_len_local, t8_length]
theorem trExpSpqrB_length : trExpSpqrB.length = 56 := by
  simp only [trExpSpqrB, exposeSpqrTr, append_len_local, t8_length]
theorem trExpCkrA_length : trExpCkrA.length = 56 := by
  simp only [trExpCkrA, exposeCkrTr, append_len_local, t8_length]

theorem trExpSpqrA_runs : Runs (TripleRatchet.exposeSpqr "alice" 30) t8 55 trExpSpqrA :=
  runs_cast_local
    (Runs.exposeSpqr (tr := t8) (stH := 30) (st := stA0)
      (at?_mono_local t5_le_t8_local t5_stA0_at))
    (by rw [t8_length]) rfl

theorem trExpSpqrB_runs : Runs (TripleRatchet.exposeSpqr "bob" 53) t8 55 trExpSpqrB :=
  runs_cast_local
    (Runs.exposeSpqr (tr := t8) (stH := 53) (st := stB1) t8_stB1_at)
    (by rw [t8_length]) rfl

theorem find_cA0_stA0 : findRecvChain stA0.recv (dhPk spkB) = some cA0 := by
  simp [findRecvChain, stA0, aliceSt, cA0]; rfl

theorem trExpCkrA_runs :
    Runs (TripleRatchet.exposeKey "alice" 30 (.ckr (dhPk spkB))) t8 55 trExpCkrA :=
  runs_cast_local
    (Runs.exposeCkr (tr := t8) (stH := 30) (st := stA0) (c := cA0)
      (at?_mono_local t5_le_t8_local t5_stA0_at) find_cA0_stA0)
    (by rw [t8_length]) rfl

theorem trExpSpqrA_reach : trExpSpqrA.Reachable reachability :=
  reach_of_runs trExpSpqrA_runs (exposeSpqr_reachable t8_reach)

theorem trExpSpqrB_reach : trExpSpqrB.Reachable reachability :=
  reach_of_runs trExpSpqrB_runs (exposeSpqr_reachable t8_reach)

theorem trExpCkrA_reach : trExpCkrA.Reachable reachability :=
  reach_of_runs trExpCkrA_runs (exposeKey_reachable t8_reach)

abbrev trExpSpqrA_reachable := trExpSpqrA_reach
abbrev trExpSpqrB_reachable := trExpSpqrB_reach
abbrev trExpCkrA_reachable := trExpCkrA_reach

/-! ### Attacker knowledge on the witness traces -/

theorem trExpSpqrA_spqr_sent_at : trExpSpqrA.MessageSentAt stA0.spqr 55 := by
  rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1]
  dsimp only [trExpSpqrA, exposeSpqrTr]
  exact at?_append_at_local _ _ (by simp only [append_len_local, t8_length])

theorem trExpSpqrB_spqr_sent_at : trExpSpqrB.MessageSentAt stB1.spqr 55 := by
  rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1]
  dsimp only [trExpSpqrB, exposeSpqrTr]
  exact at?_append_at_local _ _ (by simp only [append_len_local, t8_length])

theorem trExpCkrA_ck_sent_at : trExpCkrA.MessageSentAt keys1.ck 55 := by
  rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1]
  dsimp only [trExpCkrA, exposeCkrTr, cA0]
  exact at?_append_at_local _ _ (by simp only [append_len_local, t8_length])

theorem trExpSpqrA_knows_pqr : keys1.pqr.AttackerKnows trExpSpqrA :=
  ak_spqrInit_authKey (params := spqrA2B) (ak_net_sent trExpSpqrA_spqr_sent_at)

theorem trExpSpqrB_knows_pqr : keys1.pqr.AttackerKnows trExpSpqrB :=
  ak_spqrInit_authKey (params := spqrB2A)
    (attacker_knows_spqrRecv_args (Spqr.spqrInit keys1.pqr spqrB2A) pqm0 trExpSpqrB
      (ak_net_sent trExpSpqrB_spqr_sent_at)).1

theorem trExpCkrA_knows_ck : keys1.ck.AttackerKnows trExpCkrA :=
  ak_net_sent trExpCkrA_ck_sent_at

/-! ### Logged events and `NoCompromise` on the witness traces -/

private theorem t8_le_expSpqrA : t8 ≤ trExpSpqrA := le_append_local (Trace.append_le _ _) _
private theorem t8_le_expSpqrB : t8 ≤ trExpSpqrB := le_append_local (Trace.append_le _ _) _
private theorem t8_le_expCkrA : t8 ≤ trExpCkrA := le_append_local (Trace.append_le _ _) _

theorem trExpSpqrA_aliceDone_at :
    trExpSpqrA.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 27 :=
  eventLoggedAt_mono_local t8_le_expSpqrA t8_aliceDone_at

theorem trExpSpqrA_bobDone_at :
    trExpSpqrA.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 47 :=
  eventLoggedAt_mono_local t8_le_expSpqrA t8_bobDone_at

theorem trExpSpqrA_handshakeSessionA_at :
    trExpSpqrA.EventLoggedAt (ComposedEvent.HandshakeSession (stA0.sessionInfo "alice") 27) 29 :=
  eventLoggedAt_mono_local (Trace.le_trans _ _ _ t5_le_t8_local t8_le_expSpqrA)
    t5_handshakeSessionA_at

theorem trExpSpqrA_handshakeSessionB_at :
    trExpSpqrA.EventLoggedAt (ComposedEvent.HandshakeSession (stB0'.sessionInfo "bob") 47) 50 :=
  eventLoggedAt_mono_local t8_le_expSpqrA t8_handshakeSessionB_at

theorem trExpSpqrA_exposedSpqr_at :
    trExpSpqrA.EventLoggedAt (TREvent.ExposedSpqr (stA0.sessionInfo "alice") stA0.spqr 1) 54 := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  dsimp only [trExpSpqrA, exposeSpqrTr]
  exact at?_mono_local (Trace.append_le _ _) (at?_append_at_local _ _ t8_length)

theorem trExpSpqrB_aliceDone_at :
    trExpSpqrB.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 27 :=
  eventLoggedAt_mono_local t8_le_expSpqrB t8_aliceDone_at

theorem trExpSpqrB_bobDone_at :
    trExpSpqrB.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 47 :=
  eventLoggedAt_mono_local t8_le_expSpqrB t8_bobDone_at

theorem trExpSpqrB_handshakeSessionA_at :
    trExpSpqrB.EventLoggedAt (ComposedEvent.HandshakeSession (stA0.sessionInfo "alice") 27) 29 :=
  eventLoggedAt_mono_local (Trace.le_trans _ _ _ t5_le_t8_local t8_le_expSpqrB)
    t5_handshakeSessionA_at

theorem trExpSpqrB_handshakeSessionB_at :
    trExpSpqrB.EventLoggedAt (ComposedEvent.HandshakeSession (stB0'.sessionInfo "bob") 47) 50 :=
  eventLoggedAt_mono_local t8_le_expSpqrB t8_handshakeSessionB_at

theorem trExpSpqrB_exposedSpqr_at :
    trExpSpqrB.EventLoggedAt (TREvent.ExposedSpqr (stB0'.sessionInfo "bob") stB1.spqr 2) 54 := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  dsimp only [trExpSpqrB, exposeSpqrTr]
  exact at?_mono_local (Trace.append_le _ _) (at?_append_at_local _ _ t8_length)

theorem trExpCkrA_aliceDone_at :
    trExpCkrA.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 27 :=
  eventLoggedAt_mono_local t8_le_expCkrA t8_aliceDone_at

theorem trExpCkrA_bobDone_at :
    trExpCkrA.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 47 :=
  eventLoggedAt_mono_local t8_le_expCkrA t8_bobDone_at

theorem trExpCkrA_handshakeSessionA_at :
    trExpCkrA.EventLoggedAt (ComposedEvent.HandshakeSession (stA0.sessionInfo "alice") 27) 29 :=
  eventLoggedAt_mono_local (Trace.le_trans _ _ _ t5_le_t8_local t8_le_expCkrA)
    t5_handshakeSessionA_at

theorem trExpCkrA_handshakeSessionB_at :
    trExpCkrA.EventLoggedAt (ComposedEvent.HandshakeSession (stB0'.sessionInfo "bob") 47) 50 :=
  eventLoggedAt_mono_local t8_le_expCkrA t8_handshakeSessionB_at

theorem trExpCkrA_exposedCKr_at :
    trExpCkrA.EventLoggedAt (TREvent.ExposedCKr (stA0.sessionInfo "alice") keys1.ck 0 1) 54 := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  dsimp only [trExpCkrA, exposeCkrTr, cA0]
  exact at?_mono_local (Trace.append_le _ _) (at?_append_at_local _ _ t8_length)

private theorem not_pqxdh_append_non {X : Type} [ExecTraceTypes.Has X] {tr : ExecTrace} {x : X}
    {ev : PQXDHEvent}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none)
    (h : ¬ tr.EventLogged ev) : ¬ (tr.append x).EventLogged ev := by
  rintro ⟨i, hi⟩
  have hlt : i < (tr.append x).length := Trace.EventLoggedAt_implies_i_le_length ev i _ hi
  have hlen : (tr.append x).length = tr.length + 1 := append_len_local tr x
  rcases (show i < tr.length ∨ i = tr.length by omega) with hi_lt | rfl
  · exact h ⟨i, Trace.EventLoggedAt_le' ev i tr (tr.append x) hi_lt (Trace.append_le tr x) hi⟩
  · rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, at?_append_self_proj_local, hnone] at hi
    cases hi

private theorem noCompromise_append_non {X : Type} [ExecTraceTypes.Has X] {tr : ExecTrace} {x : X}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none)
    (h : NoCompromise tr) : NoCompromise (tr.append x) :=
  ⟨fun p k => not_pqxdh_append_non hnone (h.1 p k),
   fun b k => not_pqxdh_append_non hnone (h.2.1 b k),
   fun b k => not_pqxdh_append_non hnone (h.2.2.1 b k),
   fun b k => not_pqxdh_append_non hnone (h.2.2.2.1 b k),
   not_pqxdh_append_non hnone h.2.2.2.2.1,
   not_pqxdh_append_non hnone h.2.2.2.2.2⟩

theorem trExpSpqrA_noCompromise : NoCompromise trExpSpqrA :=
  noCompromise_append_non rfl (noCompromise_append_non rfl t8_noCompromise)
theorem trExpSpqrB_noCompromise : NoCompromise trExpSpqrB :=
  noCompromise_append_non rfl (noCompromise_append_non rfl t8_noCompromise)
theorem trExpCkrA_noCompromise : NoCompromise trExpCkrA :=
  noCompromise_append_non rfl (noCompromise_append_non rfl t8_noCompromise)

/-! ### Positive `SessionStateExposed` witnesses -/

theorem trExpSpqrA_sse_pqr : SessionStateExposed trExpSpqrA keys1 keys1.pqr :=
  ⟨stA0.sessionInfo "alice", 27, ⟨29, trExpSpqrA_handshakeSessionA_at⟩,
    ⟨"alice", "bob", dhPk ikA, dhPk ikB, dhPk spkB, kemPk pqskB, none,
      Or.inl ⟨o1.ek, o1.ct, trExpSpqrA_aliceDone_at⟩⟩,
    Or.inl ⟨rfl, stA0.spqr, 1, 54, trExpSpqrA_exposedSpqr_at⟩⟩

theorem trExpSpqrB_sse_pqr : SessionStateExposed trExpSpqrB keys1 keys1.pqr :=
  ⟨stB0'.sessionInfo "bob", 47, ⟨50, trExpSpqrB_handshakeSessionB_at⟩,
    ⟨"alice", "bob", dhPk ikA, dhPk ikB, dhPk spkB, kemPk pqskB, none,
      Or.inr ⟨o1.ek, o1.ct, trExpSpqrB_bobDone_at⟩⟩,
    Or.inl ⟨rfl, stB1.spqr, 2, 54, trExpSpqrB_exposedSpqr_at⟩⟩

theorem trExpCkrA_sse_ck : SessionStateExposed trExpCkrA keys1 keys1.ck :=
  ⟨stA0.sessionInfo "alice", 27, ⟨29, trExpCkrA_handshakeSessionA_at⟩,
    ⟨"alice", "bob", dhPk ikA, dhPk ikB, dhPk spkB, kemPk pqskB, none,
      Or.inl ⟨o1.ek, o1.ct, trExpCkrA_aliceDone_at⟩⟩,
    Or.inr (Or.inl ⟨rfl, 0, 1, 54, trExpCkrA_exposedCKr_at⟩)⟩

/-! ### Exact `HandshakeSession` inventories on the witness traces -/

private theorem someEventB_nil_local (p : PQXDHEvent → Bool) :
    (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) Trace.nil p = false := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]; rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; rfl

private theorem someEventB_append_non_local {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace)
    (x : E) (p : PQXDHEvent → Bool)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none)
    (h : (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) tr p = false) :
    (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) (tr.append x) p = false := by
  simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
  rw [append_len_local, List.range_succ, List.any_append, List.any_cons, List.any_nil,
    Bool.or_false, Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · rw [List.any_eq_false] at h ⊢
    intro i hi
    rw [at?_append_of_lt_local tr x (List.mem_range.mp hi)]
    exact h i hi
  · rw [at?_append_self_proj_local, hnone]

private theorem someEventB_append_false_local (tr : ExecTrace) (ev : PQXDHEvent)
    (p : PQXDHEvent → Bool) (hp : p ev = false)
    (h : (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) tr p = false) :
    (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) (tr.append (EvP ev)) p = false := by
  simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
  rw [append_len_local, List.range_succ, List.any_append, List.any_cons, List.any_nil,
    Bool.or_false, Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · rw [List.any_eq_false] at h ⊢
    intro i hi
    rw [at?_append_of_lt_local tr (EvP ev) (List.mem_range.mp hi)]
    exact h i hi
  · rw [Trace.at?_append]; exact hp

private theorem t1_eq_local : t1 = registerIdentityTr Trace.nil "alice" :=
  (Runs.registerIdentity (by unfold PQXDH.isRegisteredB; rw [someEventB_nil_local]; rfl)).2

private theorem t2_eq_local : t2 = registerIdentityTr t1 "bob" := by
  refine (Runs.registerIdentity ?_).2
  unfold PQXDH.isRegisteredB; rw [t1_eq_local]; dsimp only [registerIdentityTr]
  rw [someEventB_append_non_local _ _ _ rfl (someEventB_append_non_local _ _ _ rfl
    (someEventB_append_non_local _ _ _ rfl (someEventB_append_false_local _ _ _ rfl
      (someEventB_append_non_local _ _ _ rfl (someEventB_nil_local _)))))]
  rfl

private theorem t3_eq_local : t3 = genSignedPrekeyTr t2 "bob" ikB := by
  have hb : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [t2_eq_local]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_append_at_local _ _ (by simp only [append_len_local, t1_length])
  exact (Runs.genSignedPrekey hb).2

private theorem t4_eq_local : t4 = genPQPrekeyTr t3 "bob" ikB := by
  have hb2 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [t2_eq_local]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_append_at_local _ _ (by simp only [append_len_local, t1_length])
  have h23 : t2 ≤ t3 := by
    rw [t3_eq_local]
    exact le_append_local (le_append_local (le_append_local (le_append_local
      (le_append_local (Trace.append_le t2 _) _) _) _) _) _
  exact (Runs.genPQPrekey (at?_mono_local h23 hb2)).2

private theorem eventsOn_append_non {E X : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)] [ExecTraceTypes.Has X]
    (tr : ExecTrace) (x : X)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT E)) = none) :
    eventsOn E (tr.append x) = eventsOn E tr := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  dsimp only [eventsOn]
  rw [hnone]

private theorem eventsOn_append_evc (tr : ExecTrace) (ev : ComposedEvent) :
    eventsOn ComposedEvent (tr.append (EvC ev)) = ev :: eventsOn ComposedEvent tr := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]; rfl

private theorem eventsOn_encTr_composed (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (pq : Bytes) :
    eventsOn ComposedEvent (encTr tr me stH st pq) = eventsOn ComposedEvent tr := by
  dsimp only [encTr]
  rw [eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl,
    eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl,
    eventsOn_append_non _ _ rfl]

private theorem eventsOn_t8_composed :
    eventsOn ComposedEvent t8 =
      [ComposedEvent.HandshakeSession (stB0'.sessionInfo "bob") 47,
       ComposedEvent.HandshakeSession (stA0.sessionInfo "alice") 27] := by
  dsimp only [t8, t7, t6]
  rw [eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl,
    eventsOn_append_evc, eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl,
    eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl,
    eventsOn_encTr_composed, eventsOn_encTr_composed]
  dsimp only [t5, aliceTr, aliceTrOpt]
  have hd : rnd (t4.length + 2) 32 = dhsA := by rw [t4_length]
  have h5 : t4.length + 5 = 27 := by rw [t4_length]
  rw [eventsOn_append_non _ _ rfl, eventsOn_append_evc, hd, h5]
  change ComposedEvent.HandshakeSession (stB0'.sessionInfo "bob") 47 ::
    ComposedEvent.HandshakeSession (stA0.sessionInfo "alice") 27 ::
    eventsOn ComposedEvent (((((((t4.append _).append _).append _).append _).append _).append _).append _) = _
  rw [eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl,
    eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl,
    eventsOn_append_non _ _ rfl]
  rw [t4_eq_local]; dsimp only [genPQPrekeyTr]
  rw [eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl,
    eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl]
  rw [t3_eq_local]; dsimp only [genSignedPrekeyTr]
  rw [eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl,
    eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl]
  rw [t2_eq_local]; dsimp only [registerIdentityTr]
  rw [eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl,
    eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl]
  rw [t1_eq_local]; dsimp only [registerIdentityTr]
  rw [eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl,
    eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl]
  rfl

theorem trExpSpqrA_sessions :
    (eventsOn ComposedEvent trExpSpqrA).filterMap (fun | ComposedEvent.HandshakeSession s j => some (s, j)) =
      [(stB0'.sessionInfo "bob", 47), (stA0.sessionInfo "alice", 27)] := by
  dsimp only [trExpSpqrA, exposeSpqrTr]
  rw [eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_t8_composed]
  rfl

theorem trExpSpqrB_sessions :
    (eventsOn ComposedEvent trExpSpqrB).filterMap (fun | ComposedEvent.HandshakeSession s j => some (s, j)) =
      [(stB0'.sessionInfo "bob", 47), (stA0.sessionInfo "alice", 27)] := by
  dsimp only [trExpSpqrB, exposeSpqrTr]
  rw [eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_t8_composed]
  rfl

theorem trExpCkrA_sessions :
    (eventsOn ComposedEvent trExpCkrA).filterMap (fun | ComposedEvent.HandshakeSession s j => some (s, j)) =
      [(stB0'.sessionInfo "bob", 47), (stA0.sessionInfo "alice", 27)] := by
  dsimp only [trExpCkrA, exposeCkrTr]
  rw [eventsOn_append_non _ _ rfl, eventsOn_append_non _ _ rfl, eventsOn_t8_composed]
  rfl

end Symbolic.Proofs.Tests.Shared.ExplanationTightness.HandshakeTraces

