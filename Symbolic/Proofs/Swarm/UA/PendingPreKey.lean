/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyTR
public import Symbolic.Proofs.Swarm.CREF.Initiate.InitOk35Pure
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Actions.Network
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
public import Symbolic.Proofs.Swarm.UA.Defs
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.UA.Base

/-!
# Pending Pre-Key Monotonicity and Transport

Establishes `HandshakeSessionValid` on reachable composed traces, proves monotonicity of
`pendingPreKey`, transports `AlicePendingKeysOn` and `AliceRecordPendingInSession` across
non-initiating steps, and establishes `AlicePendingKeysOn` immediately after `Step.aliceStart`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.PendingPreKey

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Trace Traceful ExecTraceTypes)
open _root_.DY.Concat (concat)
open _root_.DY.DiffieHellman (dhPk)
open _root_.DY.PQKem (kemPk)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.PQXDH (PQXDHEvent PQXDHState BundleHandles BobKeyHandles
  PreKeyMsgHandles AliceHandshakeOut)
open _root_.DY.Libsignal.TripleRatchet (TRState TREvent SessionInfo isCurrentSnapshot)
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open _root_.DY.Libsignal.Composed (ComposedEvent reachability )
open _root_.DY.Libsignal.Composed.Refinement (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost Step VisEntry
  BundlePreKeyIds randTerm sessionHasDecrypted pendingPreKey runSteps runTrace StepsWF ModelRunWF
  stepBundleIds activeBundleIds MatchesEventsClassical MatchesEventsClassicalAt RunMatches EnvMatchesClassical
  preKeyRepresentationsOn parsePreKeyWire ecKey kyberKey gamma)
open _root_.DY.Libsignal.Composed.Refinement.Cli (ReadCollisionCliClassical)
open CryptoGames.LibsignalSessionApi (Session PendingPreKey PendingKyberPreKey)
open Symbolic.Swarm.CREF (NewBobSinfo BkNew BkTraceful RoleSnapshots RoleStE
  bks_getEventAt_of_le bks_lt_length_of_at? bks_lt_length_of_getEventAt
  bks_getLocalState_of_stored bks_stored_of_getLocalState
  isCurrentSnapshot_of_le_of_lt isCurrentSnapshot_false_of_later
  newBobSinfo_refl newBobSinfo_trans newBobSinfo_of_bkNew
  bkNew_refl bkNew_append_non_st bkNew_append_st_ne
  bkNew_messageEncrypt bkNew_messageEncryptAbort bkNew_messageDecrypt bkNew_messageDecryptSkipped
  iniAliceStartState iniAliceStartTr)
open Symbolic.Swarm.CREF.TR.Pure (slots_RecordCanonical_Q slots_NonEmptyV1Q)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry PQXDHEntry NetE RndE CEvE CEntry Preserves
  at?_le_some composed_reachable_induction bind_aliceHandshake_at bind_bobHandshake_at
  aliceOut NetMsgAt mkRand_inj)
open Symbolic.Swarm.COMPOSED.CompTermAlgebra (concat_inj dhPk_inj)
open Symbolic.Proofs.Swarm.UA.Defs (AlicePendingKeysOn AliceNotPendingOn AliceRecordPendingInSession)

attribute [local instance 2000]
  _root_.DY.Libsignal.Composed.instBytesFunctor_symbolic _root_.DY.Libsignal.Composed.instBytesLength_symbolic
  _root_.DY.Libsignal.Composed.instAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instExecTraceTypes_symbolic
  _root_.DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instHasExecBytes
  _root_.DY.Libsignal.Composed.instHasExecEntryT _root_.DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  _root_.DY.Libsignal.Composed.instHasExecTrace _root_.DY.Libsignal.Composed.instHasSubF
  _root_.DY.Libsignal.Composed.instHasSubFAttackerKnowledge _root_.DY.Libsignal.Composed.instHasSubFLength
  _root_.DY.Libsignal.Composed.HasExecBytes.toPQXDHExecBytes _root_.DY.Libsignal.Composed.toTripleRatchet
  _root_.DY.Libsignal.Composed.toPQXDHSpqr

/-! ## `HandshakeSessionValid` on Reachable Traces -/

/-- Reachable-trace invariant relating `HandshakeSession` events, initiator `TRState` snapshots,
and receiver `MessageKey` events. -/
structure HandshakeSessionValid (tr : ExecTrace) : Prop where
  hs : ∀ i s d, tr.getEventAt ComposedEvent i = some (.HandshakeSession s d) →
    d < i ∧
    (s.initiator = true → ∃ t rk, t < i ∧ s.sid = concat (dhPk (randTerm t 32)) rk) ∧
    (∀ a b ikA ikB spk pqpk opk ek ct keys,
      tr.getEventAt PQXDHEvent d = some (.AliceDone a b ikA ikB spk pqpk opk ek ct keys) →
      s.initiator = true ∧ s.me = a)
  stSid : ∀ i p st, (tr.at? i : Option TRStEntry) = some ⟨⟨p, st⟩⟩ →
    st.initiator = true → ∃ t rk, t < i ∧ st.sid = concat (dhPk (randTerm t 32)) rk
  mkRecv : ∀ m s seed salt n rIdx par,
    tr.getEventAt TREvent m = some (.MessageKey s .receiver seed salt n rIdx par) →
    (s.initiator = true → ∃ t rk, t < m ∧ s.sid = concat (dhPk (randTerm t 32)) rk) ∧
    (∃ st_m, (tr.at? (m + 1) : Option TRStEntry) = some ⟨⟨s.me, st_m⟩⟩ ∧ st_m.initiator = s.initiator)

theorem handshakeSessionValid_nil : HandshakeSessionValid Trace.nil := by
  refine ⟨fun i _ _ h => ?_, fun i _ _ h => ?_, fun m _ _ _ _ _ _ h => ?_⟩
  · unfold Trace.getEventAt Trace.at? at h; simp [Trace.length] at h
  · simp [Trace.at?, Trace.length] at h
  · unfold Trace.getEventAt Trace.at? at h; simp [Trace.length] at h

private theorem hsv_append_non_cEv {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} (e : E)
    (hnoneC : (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CEntry) = none)
    (hnoneSt : (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option TRStEntry) = none)
    (hnoneTR : (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) = none)
    (h : HandshakeSessionValid tr) : HandshakeSessionValid (tr.append e) := by
  have hle := Trace.append_le tr e
  refine ⟨fun i s d hev => ?_, fun i p st hat hinit => ?_, fun m s seed salt n rIdx par hev => ?_⟩
  · by_cases hi : i < tr.length
    · rw [bks_getEventAt_of_le ComposedEvent hle hi] at hev
      obtain ⟨hd, hsid, had⟩ := h.hs i s d hev
      refine ⟨hd, hsid, fun a b ikA ikB spk pqpk opk ek ct keys hpev => had a b ikA ikB spk pqpk opk ek ct keys ?_⟩
      rwa [bks_getEventAt_of_le PQXDHEvent hle (Nat.lt_trans hd hi)] at hpev
    · have hi_lt := bks_lt_length_of_getEventAt ComposedEvent hev
      have heq : i = tr.length := by simp only [Trace.append, Trace.length] at hi_lt; omega
      subst heq; unfold Trace.getEventAt at hev
      have hat : ((tr.append e).at? tr.length : Option CEntry) =
          (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option CEntry) := by
        simp [Trace.at?, Trace.append, Trace.at, Trace.length]
      rw [hat, hnoneC] at hev; cases hev
  · by_cases hi : i < tr.length
    · have hi' : i < (tr.append e).length := Nat.lt_of_lt_of_le hi (Trace.length_le _ _ hle)
      have hat₀ : (tr.at? i : Option TRStEntry) = some ⟨⟨p, st⟩⟩ := by
        simp only [Trace.at?, hi, hi', ↓reduceDIte] at hat ⊢
        rwa [Trace.at_le tr (tr.append e) i hi hle]
      exact h.stSid i p st hat₀ hinit
    · have hi_lt := bks_lt_length_of_at? hat
      have heq : i = tr.length := by simp only [Trace.append, Trace.length] at hi_lt; omega
      subst heq
      have hat' : ((tr.append e).at? tr.length : Option TRStEntry) =
          (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) := by
        simp [Trace.at?, Trace.append, Trace.at, Trace.length]
      rw [hat', hnoneSt] at hat; cases hat
  · by_cases hm : m < tr.length
    · rw [bks_getEventAt_of_le TREvent hle hm] at hev
      obtain ⟨hsid, st_m, hat_m, hinit_m⟩ := h.mkRecv m s seed salt n rIdx par hev
      exact ⟨hsid, st_m, at?_le_some hle hat_m, hinit_m⟩
    · have hm_lt := bks_lt_length_of_getEventAt TREvent hev
      have heq : m = tr.length := by simp only [Trace.append, Trace.length] at hm_lt; omega
      subst heq; unfold Trace.getEventAt at hev
      have hat : ((tr.append e).at? tr.length : Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) =
          (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj e : ExecTrace.Entry) :
            Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) := by
        simp [Trace.at?, Trace.append, Trace.at, Trace.length]
      rw [hat, hnoneTR] at hev; cases hev

private theorem hsv_append_tr_nonRecvMK {tr : ExecTrace} (ev : TREvent)
    (hnot : ∀ s seed salt n rIdx par,
      ev ≠ .MessageKey s .receiver seed salt n rIdx par)
    (h : HandshakeSessionValid tr) :
    HandshakeSessionValid (tr.append (⟨ev⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent)) := by
  set e : _root_.DY.ProtocolEvent.ExecEntryT TREvent := ⟨ev⟩
  have hle := Trace.append_le tr e
  refine ⟨fun i s d hev => ?_, fun i p st hat hinit => ?_, fun m s seed salt n rIdx par hev => ?_⟩
  · by_cases hi : i < tr.length
    · rw [bks_getEventAt_of_le ComposedEvent hle hi] at hev
      obtain ⟨hd, hsid, had⟩ := h.hs i s d hev
      refine ⟨hd, hsid, fun a b ikA ikB spk pqpk opk ek ct keys hpev => had a b ikA ikB spk pqpk opk ek ct keys ?_⟩
      rwa [bks_getEventAt_of_le PQXDHEvent hle (Nat.lt_trans hd hi)] at hpev
    · have hi_lt := bks_lt_length_of_getEventAt ComposedEvent hev
      have heq : i = tr.length := by simp only [Trace.append, Trace.length] at hi_lt; omega
      subst heq; unfold Trace.getEventAt at hev
      have hat : ((tr.append e).at? tr.length : Option CEntry) = none := by
        simp [Trace.at?, Trace.append, Trace.at, Trace.length]; rfl
      rw [hat] at hev; cases hev
  · by_cases hi : i < tr.length
    · have hi' : i < (tr.append e).length := Nat.lt_of_lt_of_le hi (Trace.length_le _ _ hle)
      have hat₀ : (tr.at? i : Option TRStEntry) = some ⟨⟨p, st⟩⟩ := by
        simp only [Trace.at?, hi, hi', ↓reduceDIte] at hat ⊢
        rwa [Trace.at_le tr (tr.append e) i hi hle]
      exact h.stSid i p st hat₀ hinit
    · have hi_lt := bks_lt_length_of_at? hat
      have heq : i = tr.length := by simp only [Trace.append, Trace.length] at hi_lt; omega
      subst heq
      have hat' : ((tr.append e).at? tr.length : Option TRStEntry) = none := by
        simp [Trace.at?, Trace.append, Trace.at, Trace.length]; rfl
      rw [hat'] at hat; cases hat
  · by_cases hm : m < tr.length
    · rw [bks_getEventAt_of_le TREvent hle hm] at hev
      obtain ⟨hsid, st_m, hat_m, hinit_m⟩ := h.mkRecv m s seed salt n rIdx par hev
      exact ⟨hsid, st_m, at?_le_some hle hat_m, hinit_m⟩
    · have hm_lt := bks_lt_length_of_getEventAt TREvent hev
      have heq : m = tr.length := by simp only [Trace.append, Trace.length] at hm_lt; omega
      subst heq; unfold Trace.getEventAt at hev
      rw [Trace.at?_append tr e] at hev
      injection hev with hev_eq
      exact False.elim (hnot s seed salt n rIdx par hev_eq)

private theorem hsv_append_storeTR {tr : ExecTrace} (p : Participant) (st : TRState)
    (hsid : st.initiator = true → ∃ t rk, t < tr.length ∧ st.sid = concat (dhPk (randTerm t 32)) rk)
    (h : HandshakeSessionValid tr) :
    HandshakeSessionValid (tr.append (⟨⟨p, st⟩⟩ : TRStEntry)) := by
  set e : TRStEntry := ⟨⟨p, st⟩⟩
  have hle := Trace.append_le tr e
  refine ⟨fun i s d hev => ?_, fun i q st' hat hinit => ?_, fun m s seed salt n rIdx par hev => ?_⟩
  · by_cases hi : i < tr.length
    · rw [bks_getEventAt_of_le ComposedEvent hle hi] at hev
      obtain ⟨hd, hs_sid, had⟩ := h.hs i s d hev
      refine ⟨hd, hs_sid, fun a b ikA ikB spk pqpk opk ek ct keys hpev => had a b ikA ikB spk pqpk opk ek ct keys ?_⟩
      rwa [bks_getEventAt_of_le PQXDHEvent hle (Nat.lt_trans hd hi)] at hpev
    · have hi_lt := bks_lt_length_of_getEventAt ComposedEvent hev
      have heq : i = tr.length := by simp only [Trace.append, Trace.length] at hi_lt; omega
      subst heq; unfold Trace.getEventAt at hev
      have hat : ((tr.append e).at? tr.length : Option CEntry) = none := by
        simp [Trace.at?, Trace.append, Trace.at, Trace.length]; rfl
      rw [hat] at hev; cases hev
  · by_cases hi : i < tr.length
    · have hi' : i < (tr.append e).length := Nat.lt_of_lt_of_le hi (Trace.length_le _ _ hle)
      have hat₀ : (tr.at? i : Option TRStEntry) = some ⟨⟨q, st'⟩⟩ := by
        simp only [Trace.at?, hi, hi', ↓reduceDIte] at hat ⊢
        rwa [Trace.at_le tr (tr.append e) i hi hle]
      exact h.stSid i q st' hat₀ hinit
    · have hi_lt := bks_lt_length_of_at? hat
      have heq : i = tr.length := by simp only [Trace.append, Trace.length] at hi_lt; omega
      subst heq
      rw [Trace.at?_append tr e] at hat
      injection hat with h1; injection h1 with h2
      have hst_eq : st' = st := congrArg _root_.DY.PersistentLocalState.LocalState.state h2.symm
      subst hst_eq; exact hsid hinit
  · by_cases hm : m < tr.length
    · rw [bks_getEventAt_of_le TREvent hle hm] at hev
      obtain ⟨hs_sid, st_m, hat_m, hinit_m⟩ := h.mkRecv m s seed salt n rIdx par hev
      exact ⟨hs_sid, st_m, at?_le_some hle hat_m, hinit_m⟩
    · have hm_lt := bks_lt_length_of_getEventAt TREvent hev
      have heq : m = tr.length := by simp only [Trace.append, Trace.length] at hm_lt; omega
      subst heq; unfold Trace.getEventAt at hev
      have hat : ((tr.append e).at? tr.length : Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) = none := by
        simp [Trace.at?, Trace.append, Trace.at, Trace.length]; rfl
      rw [hat] at hev; cases hev

private theorem hsv_append_handshake {tr : ExecTrace} {s : SessionInfo} {d : Nat}
    (hd : d < tr.length)
    (hinit : s.initiator = true → ∃ t rk, t < tr.length ∧ s.sid = concat (dhPk (randTerm t 32)) rk)
    (had : ∀ a b ikA ikB spk pqpk opk ek ct keys,
      tr.getEventAt PQXDHEvent d = some (.AliceDone a b ikA ikB spk pqpk opk ek ct keys) →
      s.initiator = true ∧ s.me = a)
    (h : HandshakeSessionValid tr) :
    HandshakeSessionValid (tr.append (CEvE (.HandshakeSession s d))) := by
  set e := CEvE (.HandshakeSession s d)
  have hle := Trace.append_le tr e
  refine ⟨fun i s' d' hev => ?_, fun i p st hat hi_init => ?_, fun m s' seed salt n rIdx par hev => ?_⟩
  · by_cases hi : i < tr.length
    · rw [bks_getEventAt_of_le ComposedEvent hle hi] at hev
      obtain ⟨hd', hs_sid, had'⟩ := h.hs i s' d' hev
      refine ⟨hd', hs_sid, fun a b ikA ikB spk pqpk opk ek ct keys hpev => had' a b ikA ikB spk pqpk opk ek ct keys ?_⟩
      rwa [bks_getEventAt_of_le PQXDHEvent hle (Nat.lt_trans hd' hi)] at hpev
    · have hi_lt := bks_lt_length_of_getEventAt ComposedEvent hev
      have heq : i = tr.length := by simp only [Trace.append, Trace.length] at hi_lt; omega
      subst heq; unfold Trace.getEventAt at hev
      rw [Trace.at?_append tr e] at hev
      injection hev with heq_ev; cases heq_ev
      refine ⟨hd, hinit, fun a b ikA ikB spk pqpk opk ek ct keys hpev => had a b ikA ikB spk pqpk opk ek ct keys ?_⟩
      rwa [bks_getEventAt_of_le PQXDHEvent hle hd] at hpev
  · by_cases hi : i < tr.length
    · have hi' : i < (tr.append e).length := Nat.lt_of_lt_of_le hi (Trace.length_le _ _ hle)
      have hat₀ : (tr.at? i : Option TRStEntry) = some ⟨⟨p, st⟩⟩ := by
        simp only [Trace.at?, hi, hi', ↓reduceDIte] at hat ⊢
        rwa [Trace.at_le tr (tr.append e) i hi hle]
      exact h.stSid i p st hat₀ hi_init
    · have hi_lt := bks_lt_length_of_at? hat
      have heq : i = tr.length := by simp only [Trace.append, Trace.length] at hi_lt; omega
      subst heq
      have hat' : ((tr.append e).at? tr.length : Option TRStEntry) = none := by
        simp [Trace.at?, Trace.append, Trace.at, Trace.length]; rfl
      rw [hat'] at hat; cases hat
  · by_cases hm : m < tr.length
    · rw [bks_getEventAt_of_le TREvent hle hm] at hev
      obtain ⟨hs_sid, st_m, hat_m, hinit_m⟩ := h.mkRecv m s' seed salt n rIdx par hev
      exact ⟨hs_sid, st_m, at?_le_some hle hat_m, hinit_m⟩
    · have hm_lt := bks_lt_length_of_getEventAt TREvent hev
      have heq : m = tr.length := by simp only [Trace.append, Trace.length] at hm_lt; omega
      subst heq; unfold Trace.getEventAt at hev
      have hat : ((tr.append e).at? tr.length : Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) = none := by
        simp [Trace.at?, Trace.append, Trace.at, Trace.length]; rfl
      rw [hat] at hev; cases hev

private theorem preserves_hsv_genRand (n : Nat) :
    Preserves HandshakeSessionValid (_root_.DY.Random.genRand n) :=
  fun _ h => hsv_append_non_cEv (RndE n) rfl rfl rfl h
private theorem preserves_hsv_sendMessage (m : _root_.DY.Bytes) :
    Preserves HandshakeSessionValid (_root_.DY.Network.sendMessage m) :=
  fun _ h => hsv_append_non_cEv (NetE m) rfl rfl rfl h
private theorem preserves_hsv_logPQ (ev : PQXDHEvent) :
    Preserves HandshakeSessionValid (_root_.DY.ProtocolEvent.logEvent ev) :=
  fun _ h => hsv_append_non_cEv (⟨ev⟩ : PQXDHEntry) rfl rfl rfl h
private theorem preserves_hsv_logTR_nonRecvMK (ev : TREvent)
    (hnot : ∀ s seed salt n rIdx par,
      ev ≠ .MessageKey s .receiver seed salt n rIdx par := by intros; intro h; cases h) :
    Preserves HandshakeSessionValid (_root_.DY.ProtocolEvent.logEvent ev) :=
  fun _ h => hsv_append_tr_nonRecvMK ev hnot h
private theorem preserves_hsv_storePQ (p : Participant) (st : PQXDHState) :
    Preserves HandshakeSessionValid (_root_.DY.PersistentLocalState.storeLocalState p st) :=
  fun _ h => hsv_append_non_cEv
    (⟨⟨p, st⟩⟩ : _root_.DY.PersistentGlobalState.State.ExecEntryT (_root_.DY.PersistentLocalState.LocalState PQXDHState))
    rfl rfl rfl h

private theorem preserves_hsv_getKey (p : Participant) (idx : Nat)
    (k : _root_.DY.Libsignal.PQXDH.KeyKind) :
    Preserves HandshakeSessionValid (_root_.DY.Libsignal.PQXDH.getKey p idx k) := by
  unfold _root_.DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p idx) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem preserves_hsv_logSkippedKeys (s : SessionInfo) (pk : _root_.DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : _root_.DY.Bytes) (n : UInt32),
      Preserves HandshakeSessionValid (_root_.DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k)
  | 0, _, _ => Preserves.pure _
  | k + 1, ck, n => by
    rw [_root_.DY.Libsignal.TripleRatchet.logSkippedKeys]
    exact Preserves.bind (preserves_hsv_logTR_nonRecvMK _) fun _ =>
      preserves_hsv_logSkippedKeys s pk rIdx src k _ _

private theorem preserves_len_and {α : Type} (bound : Nat) {m : Traceful α}
    (hm : Preserves HandshakeSessionValid m) :
    Preserves (fun tr => bound ≤ tr.length ∧ HandshakeSessionValid tr) m :=
  fun tr ⟨hb, h⟩ => ⟨Nat.le_trans hb (Trace.length_le _ _ (m.run tr).2.property), hm tr h⟩

private theorem preserves_hsv_logMessageKeyAndStore_sender (bound : Nat) (me : Participant) (s : SessionInfo)
    (seed salt : _root_.DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState)
    (hsid : st.initiator = true → ∃ t rk, t < bound ∧ st.sid = concat (dhPk (randTerm t 32)) rk) :
    Preserves (fun tr => bound ≤ tr.length ∧ HandshakeSessionValid tr)
      (_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s .sender seed salt n rIdx par st) := by
  unfold _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine Preserves.bind (preserves_len_and bound (preserves_hsv_logTR_nonRecvMK _)) fun _ tr ⟨hb, h⟩ => ?_
  refine ⟨Nat.le_trans hb (Trace.length_le _ _ (Trace.append_le tr (⟨⟨me, st⟩⟩ : TRStEntry))),
    hsv_append_storeTR me st (fun hi => ?_) h⟩
  obtain ⟨t, rk, htb, hseq⟩ := hsid hi
  exact ⟨t, rk, Nat.lt_of_lt_of_le htb hb, hseq⟩

private theorem preserves_hsv_logMessageKeyAndStore_receiver (bound : Nat) (me : Participant) (s : SessionInfo)
    (seed salt : _root_.DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState)
    (hs_me : s.me = me) (hst_init : st.initiator = s.initiator) (hst_sid : st.sid = s.sid)
    (hsid : s.initiator = true → ∃ t rk, t < bound ∧ s.sid = concat (dhPk (randTerm t 32)) rk) :
    Preserves (fun tr => bound ≤ tr.length ∧ HandshakeSessionValid tr)
      (_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s .receiver seed salt n rIdx par st) := by
  intro tr ⟨hb, h⟩
  set e1 : _root_.DY.ProtocolEvent.ExecEntryT TREvent :=
    ⟨.MessageKey s .receiver seed salt n rIdx par⟩
  set tr1 := tr.append e1
  set e2 : TRStEntry := ⟨⟨me, st⟩⟩
  set tr2 := tr1.append e2
  have hrun : ((_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s .receiver seed salt n rIdx par st).run tr).2.val = tr2 := by
    unfold _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
      _root_.DY.ProtocolEvent.logEvent _root_.DY.PersistentLocalState.storeLocalState
      _root_.DY.PersistentGlobalState.storeGlobalState _root_.DY.appendEntry
    rfl
  rw [hrun]
  have hle1 := Trace.append_le tr e1
  have hle2 := Trace.append_le tr1 e2
  have hle12 := Trace.le_trans _ _ _ hle1 hle2
  have hlen1 : tr1.length = tr.length + 1 := by simp [tr1, Trace.append, Trace.length]
  have hlen2 : tr2.length = tr.length + 2 := by simp [tr2, tr1, Trace.append, Trace.length]
  refine ⟨by omega, fun i s' d hev => ?_, fun i p st' hat hi_init => ?_,
    fun m s' seed' salt' n' rIdx' par' hev => ?_⟩
  · by_cases hi : i < tr.length
    · rw [bks_getEventAt_of_le ComposedEvent hle12 hi] at hev
      obtain ⟨hd, hs_sid, had⟩ := h.hs i s' d hev
      refine ⟨hd, hs_sid, fun a b ikA ikB spk pqpk opk ek ct keys hpev => had a b ikA ikB spk pqpk opk ek ct keys ?_⟩
      rwa [bks_getEventAt_of_le PQXDHEvent hle12 (Nat.lt_trans hd hi)] at hpev
    · have hi_lt := bks_lt_length_of_getEventAt ComposedEvent hev
      by_cases hi1 : i = tr.length
      · subst hi1; unfold Trace.getEventAt at hev
        rw [show (tr2.at? tr.length : Option CEntry) = (tr1.at? tr.length : Option CEntry) from by
          simp only [Trace.at?, hlen1, hlen2, show tr.length < tr.length + 1 by omega,
            show tr.length < tr.length + 2 by omega, ↓reduceDIte]
          rw [← Trace.at_le tr1 tr2 tr.length (by omega) hle2]] at hev
        have hat1 : (tr1.at? tr.length : Option CEntry) = none := by
          simp [tr1, e1, Trace.at?, Trace.append, Trace.at, Trace.length]; rfl
        rw [hat1] at hev; cases hev
      · have hi2 : i = tr1.length := by omega
        subst hi2; unfold Trace.getEventAt at hev
        have hat2 : (tr2.at? tr1.length : Option CEntry) = none := by
          simp [tr2, e2, Trace.at?, Trace.append, Trace.at, Trace.length]; rfl
        rw [hat2] at hev; cases hev
  · by_cases hi : i < tr.length
    · have hi' : i < tr2.length := by omega
      have hat₀ : (tr.at? i : Option TRStEntry) = some ⟨⟨p, st'⟩⟩ := by
        simp only [Trace.at?, hi, hi', ↓reduceDIte] at hat ⊢
        rwa [Trace.at_le tr tr2 i hi hle12]
      exact h.stSid i p st' hat₀ hi_init
    · have hi_lt := bks_lt_length_of_at? hat
      by_cases hi1 : i = tr.length
      · subst hi1
        have hat12 : (tr2.at? tr.length : Option TRStEntry) = (tr1.at? tr.length : Option TRStEntry) := by
          simp only [Trace.at?, hlen1, hlen2, show tr.length < tr.length + 1 by omega,
            show tr.length < tr.length + 2 by omega, ↓reduceDIte]
          rw [← Trace.at_le tr1 tr2 tr.length (by omega) hle2]
        rw [hat12] at hat
        have hat1 : (tr1.at? tr.length : Option TRStEntry) = none := by
          simp [tr1, e1, Trace.at?, Trace.append, Trace.at, Trace.length]; rfl
        rw [hat1] at hat; cases hat
      · have hi2 : i = tr1.length := by omega
        subst hi2
        rw [Trace.at?_append tr1 e2] at hat
        injection hat with h1; injection h1 with h2
        have hst_eq : st' = st := congrArg _root_.DY.PersistentLocalState.LocalState.state h2.symm
        subst hst_eq
        obtain ⟨t, rk, htb, hseq⟩ := hsid (hst_init.symm.trans hi_init)
        exact ⟨t, rk, by omega, hst_sid.trans hseq⟩
  · by_cases hm : m < tr.length
    · rw [bks_getEventAt_of_le TREvent hle12 hm] at hev
      obtain ⟨hs_sid, st_m, hat_m, hinit_m⟩ := h.mkRecv m s' seed' salt' n' rIdx' par' hev
      exact ⟨hs_sid, st_m, at?_le_some hle12 hat_m, hinit_m⟩
    · have hm_lt := bks_lt_length_of_getEventAt TREvent hev
      by_cases hm1 : m = tr.length
      · subst hm1
        rw [bks_getEventAt_of_le TREvent hle2 (by omega)] at hev
        unfold Trace.getEventAt at hev
        rw [Trace.at?_append tr e1] at hev
        injection hev with hev_eq
        cases hev_eq
        refine ⟨fun hi_s => ?_, st, ?_, hst_init⟩
        · obtain ⟨t, rk, htb, hseq⟩ := hsid hi_s
          exact ⟨t, rk, Nat.lt_of_lt_of_le htb hb, hseq⟩
        · rw [hs_me, ← hlen1]
          exact Trace.at?_append tr1 e2
      · have hm2 : m = tr1.length := by omega
        subst hm2; unfold Trace.getEventAt at hev
        have hat2 : (tr2.at? tr1.length : Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) = none := by
          simp [tr2, e2, Trace.at?, Trace.append, Trace.at, Trace.length]; rfl
        rw [hat2] at hev; cases hev

private theorem preserves_hsv_dhRatchetStep (st : TRState) (pk : _root_.DY.Bytes) :
    Preserves HandshakeSessionValid (_root_.DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact Preserves.bind (Preserves.guardP _) fun _ =>
    Preserves.bind (preserves_hsv_genRand 32) fun _ => Preserves.pure _

private theorem ensureReceiverChain_initiator_and_hsv (st : TRState) (pk : _root_.DY.Bytes) (tr : ExecTrace)
    (h : HandshakeSessionValid tr) :
    HandshakeSessionValid ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st pk).run tr).2.val ∧
      ∀ st' c rat, ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st pk).run tr).1 = some (st', c, rat) →
        st'.initiator = st.initiator ∧ st'.sid = st.sid := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  rcases _root_.DY.Libsignal.TripleRatchet.recvChainFor st.toDRState pk with _ | ⟨c, _ | _⟩
  · exact ⟨h, fun _ _ _ hb => by cases hb⟩
  · refine ⟨h, fun st' _ _ hb => ?_⟩
    injection hb with ht; injection ht with hst _
    exact ⟨congrArg (fun s : TRState => s.initiator) hst.symm, congrArg (fun s : TRState => s.sid) hst.symm⟩
  · refine ⟨(Preserves.bind (preserves_hsv_dhRatchetStep st pk) fun _ => Preserves.pure _) tr h,
      fun st' _ _ hb => ?_⟩
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst] at hb
    rcases hdhr : ((_root_.DY.Libsignal.TripleRatchet.dhRatchetStep st pk).run tr).1 with _ | ⟨st1, c1⟩
    · rw [hdhr] at hb; cases hb
    · rw [hdhr] at hb; dsimp only [Traceful.run_pure] at hb
      injection hb with ht; injection ht with hst1 _; subst hst1
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard] at hdhr
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst] at hdhr
      rcases hg : ((«guard» (!_root_.DY.X25519.x25519LowOrder pk) : Traceful Unit).run tr).1 with _ | _
      · rw [hg] at hdhr; cases hdhr
      · rw [hg] at hdhr; dsimp only at hdhr
        rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst] at hdhr
        dsimp only [_root_.DY.Random.genRand, Traceful.run_pure] at hdhr
        injection hdhr with hp; injection hp with hst1 _; rw [← hst1]; exact ⟨rfl, rfl⟩

private theorem bind_ensureReceiverChain_hsv {α : Type} (st0 : TRState) (pk : _root_.DY.Bytes)
    (h0 : st0.initiator = false)
    {f : TRState × _root_.DY.Libsignal.TripleRatchet.RecvChain × Bool → Traceful α}
    (hf : ∀ x, x.1.initiator = false → Preserves HandshakeSessionValid (f x)) :
    Preserves HandshakeSessionValid (_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st0 pk >>= f) := by
  intro tr hInv
  have herc := ensureReceiverChain_initiator_and_hsv st0 pk tr hInv
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  rcases hrc : ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st0 pk).run tr).1 with _ | ⟨st, c, rat⟩
  · exact herc.1
  · exact hf (st, c, rat) ((herc.2 st c rat hrc).1.trans h0) _ herc.1

private theorem bind_getLocalState_tr_hsv {α : Type} (me : Participant) (stH : Nat)
    {f : TRState → Traceful α}
    (hf : ∀ st, (st.initiator = true → ∃ t rk, t < stH ∧ st.sid = concat (dhPk (randTerm t 32)) rk) →
      Preserves (fun tr => stH ≤ tr.length ∧ HandshakeSessionValid tr) (f st)) :
    Preserves HandshakeSessionValid (_root_.DY.PersistentLocalState.getLocalState me stH >>= f) := by
  intro tr hInv
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  rcases hget : ((_root_.DY.PersistentLocalState.getLocalState (StateT := TRState) me stH).run tr).1 with _ | st
  · rw [Symbolic.Swarm.CREF.XplSteps.xfix_getLocalState me stH tr]; exact hInv
  · rw [Symbolic.Swarm.CREF.XplSteps.xfix_getLocalState me stH tr]
    have hat : (tr.at? stH : Option TRStEntry) = some ⟨⟨me, st⟩⟩ := bks_stored_of_getLocalState hget
    have hlt : stH < tr.length := bks_lt_length_of_at? hat
    exact (hf st (hInv.stSid stH me st hat) tr ⟨Nat.le_of_lt hlt, hInv⟩).2

private theorem preserves_hsv_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) :
    Preserves HandshakeSessionValid (_root_.DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh) := by
  intro tr hInv; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hInv (hsv_append_non_cEv (RndE 32) rfl rfl rfl hInv) ?_
  intro ikA ikB _ spk _ pqpk _ opk _ _ _ _ _ _ _ _ _ _ _ _
  set o := aliceOut tr ikA ikB spk pqpk opk
  change HandshakeSessionValid (iniAliceStartTr tr a b o); unfold iniAliceStartTr; dsimp only
  set t5 := ((((tr.append (RndE 32)).append (RndE 32)).append (RndE 32)).append (NetE o.ek)).append (NetE o.ct)
  have ht5 : HandshakeSessionValid t5 :=
    hsv_append_non_cEv (NetE o.ct) rfl rfl rfl (hsv_append_non_cEv (NetE o.ek) rfl rfl rfl
      (hsv_append_non_cEv (RndE 32) rfl rfl rfl (hsv_append_non_cEv (RndE 32) rfl rfl rfl
        (hsv_append_non_cEv (RndE 32) rfl rfl rfl hInv))))
  set t6 := (t5.append (⟨.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys⟩ : PQXDHEntry)).append
    (⟨.InitSession a b (dhPk (randTerm (tr.length + 2) 32)) o.spk⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent)
  have ht6 : HandshakeSessionValid t6 :=
    hsv_append_tr_nonRecvMK _ (by intros; intro h; cases h)
      (hsv_append_non_cEv (⟨.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys⟩ : PQXDHEntry) rfl rfl rfl ht5)
  have had_t6 : ∀ a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys',
      t6.getEventAt PQXDHEvent (tr.length + 5) = some (.AliceDone a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys') →
      ((iniAliceStartState tr b o).sessionInfo a).initiator = true ∧ ((iniAliceStartState tr b o).sessionInfo a).me = a' := by
    intro a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys' hpev
    have hlen5 : t5.length = tr.length + 5 := by simp [t5, Trace.append, Trace.length]
    rw [bks_getEventAt_of_le PQXDHEvent (Trace.append_le _ _) (by simp [Trace.append, Trace.length, hlen5])] at hpev
    unfold Trace.getEventAt at hpev
    rw [← hlen5, Trace.at?_append] at hpev
    injection hpev with heq; cases heq
    exact ⟨rfl, rfl⟩
  refine hsv_append_storeTR a (iniAliceStartState tr b o)
    (fun _ => ⟨tr.length + 2, o.keys.rk,
      by simp [t6, t5, Trace.append, Trace.length], rfl⟩)
    (hsv_append_handshake (by simp [t6, t5, Trace.append, Trace.length])
      (fun _ => ⟨tr.length + 2, o.keys.rk,
        by simp [t6, t5, Trace.append, Trace.length], rfl⟩)
      had_t6 ht6)

private theorem preserves_hsv_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves HandshakeSessionValid
      (_root_.DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr hInv; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.bobStart_eq_inline]
  refine bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hInv ?_
  intro ikBSk spkSk pqsk opkSk ikA _ ek ct _ keys _ _ _ _ _ _ _ _ _
  refine (Preserves.bind (Preserves.receiveSignalMsg mh.msg) fun msg => ?_) tr hInv
  try dsimp only
  refine bind_ensureReceiverChain_hsv _ msg.ratchetKey ?_ fun ⟨st, c, ratcheted⟩ hinit_false => ?_
  · rfl
  dsimp only at hinit_false ⊢; split
  · next seed c' _ =>
    split
    · next spqr' key _ =>
      refine Preserves.bind (preserves_hsv_sendMessage key) fun _ =>
        Preserves.bind (Preserves.receiveMessage pqIdx) fun pqSalt =>
        Preserves.bind (Preserves.verifyMacAndDecrypt st msg pqSalt seed) fun ptTerm => ?_
      try dsimp only
      have hpost_opk : ∀ (opk_opt : Option _root_.DY.Bytes) (t₂ : ExecTrace), HandshakeSessionValid t₂ →
          HandshakeSessionValid ((do
            let doneIdx ← _root_.DY.Libsignal.TripleRatchet.traceLength
            _root_.DY.ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (dhPk ikBSk) ikA (dhPk spkSk)
              (kemPk pqsk) opk_opt ek ct keys)
            if ratcheted then do
              _root_.DY.ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (dhPk st.dhs))
              _root_.DY.ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
            _root_.DY.ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
            let skipped := msg.counter.toNat - c.index.toNat
            let childIdx := (← _root_.DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
            _root_.DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx
              c.chainKey c.index skipped
            _root_.DY.ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter ptTerm)
            _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver
              seed pqSalt msg.counter c.rIdx childIdx
              { st with recv := _root_.DY.Libsignal.TripleRatchet.setRecvChain st.recv c', spqr := spqr' }).run t₂).2.val := by
        intro opk_opt t₂ ht₂
        rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
        have htl : ((_root_.DY.Libsignal.TripleRatchet.traceLength).run t₂) = (some t₂.length, ⟨t₂, Trace.le_refl t₂⟩) := rfl
        rw [htl]; dsimp only
        rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
        set t₃ := t₂.append (⟨PQXDHEvent.BobDone b a (dhPk ikBSk) ikA (dhPk spkSk) (kemPk pqsk)
          opk_opt ek ct keys⟩ : PQXDHEntry)
        have ht₃ : HandshakeSessionValid t₃ := hsv_append_non_cEv _ rfl rfl rfl ht₂
        have had_t₃ : ∀ a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys',
            t₃.getEventAt PQXDHEvent t₂.length = some (.AliceDone a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys') →
            (st.sessionInfo b).initiator = true ∧ (st.sessionInfo b).me = a' := by
          intro _ _ _ _ _ _ _ _ _ _ hpev
          unfold Trace.getEventAt at hpev
          rw [Trace.at?_append t₂ _] at hpev
          cases hpev
        try dsimp only
        cases ratcheted
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
          have h4 : HandshakeSessionValid (t₃.append (CEvE (.HandshakeSession (st.sessionInfo b) t₂.length))) :=
            hsv_append_handshake (by change t₂.length < t₂.length + 1; omega)
              (fun hi => by simp [_root_.DY.Libsignal.TripleRatchet.DRState.sessionInfo, hinit_false] at hi)
              had_t₃ ht₃
          exact ((Preserves.bind (preserves_len_and 0 Preserves.traceLength) fun _ =>
            Preserves.bind (preserves_len_and 0 (preserves_hsv_logSkippedKeys _ _ _ _ _ _ _)) fun _ =>
            Preserves.bind (preserves_len_and 0 (preserves_hsv_logTR_nonRecvMK _)) fun _ =>
            preserves_hsv_logMessageKeyAndStore_receiver 0 b _ _ _ _ _ _ _
              rfl rfl rfl
              (fun hi => by simp [_root_.DY.Libsignal.TripleRatchet.DRState.sessionInfo, hinit_false] at hi))
            _ ⟨Nat.zero_le _, h4⟩).2
        · simp only [↓reduceIte]
          rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
          set t₄ := (t₃.append (⟨TREvent.DHRatchet b st.peer msg.ratchetKey (dhPk st.dhs)⟩ :
            _root_.DY.ProtocolEvent.ExecEntryT TREvent)).append
            (⟨TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent)
          have ht₄ : HandshakeSessionValid t₄ :=
            hsv_append_tr_nonRecvMK _ (by intros; intro h; cases h)
              (hsv_append_tr_nonRecvMK _ (by intros; intro h; cases h) ht₃)
          have had_t₄ : ∀ a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys',
              t₄.getEventAt PQXDHEvent t₂.length = some (.AliceDone a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys') →
              (st.sessionInfo b).initiator = true ∧ (st.sessionInfo b).me = a' := by
            intro a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys' hpev
            have hle34 : t₃ ≤ t₄ := Trace.le_trans _ _ _ (Trace.append_le _ _) (Trace.append_le _ _)
            rw [bks_getEventAt_of_le PQXDHEvent hle34 (by change t₂.length < t₂.length + 1; omega)] at hpev
            exact had_t₃ a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys' hpev
          rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
          have h5 : HandshakeSessionValid (t₄.append (CEvE (.HandshakeSession (st.sessionInfo b) t₂.length))) :=
            hsv_append_handshake (by change t₂.length < t₂.length + 1 + 1 + 1; omega)
              (fun hi => by simp [_root_.DY.Libsignal.TripleRatchet.DRState.sessionInfo, hinit_false] at hi)
              had_t₄ ht₄
          exact ((Preserves.bind (preserves_len_and 0 Preserves.traceLength) fun _ =>
            Preserves.bind (preserves_len_and 0 (preserves_hsv_logSkippedKeys _ _ _ _ _ _ _)) fun _ =>
            Preserves.bind (preserves_len_and 0 (preserves_hsv_logTR_nonRecvMK _)) fun _ =>
            preserves_hsv_logMessageKeyAndStore_receiver 0 b _ _ _ _ _ _ _
              rfl rfl rfl
              (fun hi => by simp [_root_.DY.Libsignal.TripleRatchet.DRState.sessionInfo, hinit_false] at hi))
            _ ⟨Nat.zero_le _, h5⟩).2
      cases opkSk.map dhPk with
      | none => try dsimp only; exact hpost_opk none
      | some opk =>
        try dsimp only
        exact Preserves.bind (Preserves.requireTracePredicate _) (fun _ =>
          Preserves.bind (preserves_hsv_logPQ _) fun _ => hpost_opk (some opk))
    · exact Preserves.failure
  · exact Preserves.failure

private theorem preserves_hsv_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat) :
    Preserves HandshakeSessionValid (_root_.DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx) := by
  unfold _root_.DY.Libsignal.TripleRatchet.messageEncrypt
  refine bind_getLocalState_tr_hsv me stH fun st hsid => ?_
  exact Preserves.bind (preserves_len_and stH (Preserves.guardP _)) fun _ =>
    Preserves.bind (preserves_len_and stH (preserves_hsv_genRand 32)) fun _ =>
    Preserves.bind (preserves_len_and stH (preserves_hsv_genRand coinsLen)) fun _ =>
    Preserves.bind (preserves_len_and stH (preserves_hsv_sendMessage _)) fun _ =>
    Preserves.bind (preserves_len_and stH (Preserves.receiveMessage pqIdx)) fun _ =>
    Preserves.bind (preserves_len_and stH (preserves_hsv_logTR_nonRecvMK _)) fun _ =>
    Preserves.bind (preserves_hsv_logMessageKeyAndStore_sender stH me _ _ _ _ _ _ _ hsid) fun _ =>
    preserves_len_and stH (preserves_hsv_sendMessage _)

private theorem preserves_hsv_messageEncryptAbort (me : Participant) (stH : Nat) :
    Preserves HandshakeSessionValid (_root_.DY.Libsignal.TripleRatchet.messageEncryptAbort me stH) := by
  unfold _root_.DY.Libsignal.TripleRatchet.messageEncryptAbort
  exact Preserves.bind (Preserves.getLocalState_tr me stH) fun _ =>
    Preserves.bind (preserves_hsv_genRand 32) fun _ => Preserves.failure

private theorem preserves_hsv_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves HandshakeSessionValid
      (_root_.DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine bind_getLocalState_tr_hsv me stH fun st hsid => ?_
  refine Preserves.bind (preserves_len_and stH (Preserves.receiveSignalMsg msgH)) fun msg t ⟨hb, ht⟩ => ?_
  have herc := ensureReceiverChain_initiator_and_hsv st msg.ratchetKey t ht
  have hb_erc : stH ≤ ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st msg.ratchetKey).run t).2.val.length :=
    Nat.le_trans hb (Trace.length_le _ _ ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st msg.ratchetKey).run t).2.property)
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  rcases hrc : ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st msg.ratchetKey).run t).1 with _ | ⟨st', c, rat⟩
  · exact ⟨hb_erc, herc.1⟩
  · obtain ⟨hinit_eq, hsid_eq⟩ := herc.2 st' c rat hrc
    have hsid' : (st'.sessionInfo me).initiator = true →
        ∃ t₀ rk, t₀ < stH ∧ (st'.sessionInfo me).sid = concat (dhPk (randTerm t₀ 32)) rk := by
      intro hi
      obtain ⟨t₀, rk, ht₀, hs₀⟩ := hsid (hinit_eq.symm.trans hi)
      exact ⟨t₀, rk, ht₀, hsid_eq.trans hs₀⟩
    refine (?G : Preserves (fun tr => stH ≤ tr.length ∧ HandshakeSessionValid tr) _)
      ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st msg.ratchetKey).run t).2.val ⟨hb_erc, herc.1⟩
    dsimp only; split
    · split
      · refine Preserves.bind (preserves_len_and stH (preserves_hsv_sendMessage _)) fun _ =>
          Preserves.bind (preserves_len_and stH (Preserves.receiveMessage _)) fun _ =>
          Preserves.bind (preserves_len_and stH (Preserves.verifyMacAndDecrypt _ _ _ _)) fun _ => ?_
        split
        · exact Preserves.bind (preserves_len_and stH (preserves_hsv_logTR_nonRecvMK _)) fun _ =>
            Preserves.bind (preserves_len_and stH (preserves_hsv_logTR_nonRecvMK _)) fun _ =>
            Preserves.bind (preserves_len_and stH (preserves_hsv_logSkippedKeys _ _ _ _ _ _ _)) fun _ =>
            Preserves.bind (preserves_len_and stH (preserves_hsv_logTR_nonRecvMK _)) fun _ =>
            preserves_hsv_logMessageKeyAndStore_receiver stH me _ _ _ _ _ _ _ rfl rfl rfl hsid'
        · exact Preserves.bind (preserves_len_and stH (preserves_hsv_logSkippedKeys _ _ _ _ _ _ _)) fun _ =>
            Preserves.bind (preserves_len_and stH (preserves_hsv_logTR_nonRecvMK _)) fun _ =>
            preserves_hsv_logMessageKeyAndStore_receiver stH me _ _ _ _ _ _ _ rfl rfl rfl hsid'
      · exact fun _ h => h
    · exact fun _ h => h

private theorem bind_guard_preserves {P : ExecTrace → Prop} {α : Type}
    (p : Prop) [Decidable p] {k : PUnit → Traceful α}
    (hk : p → Preserves P (k ())) :
    Preserves P (_root_.guard p >>= k) := by
  by_cases hp : p
  · simp only [_root_.guard, hp, ↓reduceIte]; exact hk hp
  · simp only [_root_.guard, hp, ↓reduceIte]; exact fun _ h => h

private theorem preserves_hsv_messageDecryptSkipped (me : Participant) (stH msgH evH pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    Preserves HandshakeSessionValid
      (_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine bind_getLocalState_tr_hsv me stH fun st hsid => ?_
  refine Preserves.bind (preserves_len_and stH (Preserves.receiveSignalMsg msgH)) fun _ =>
    Preserves.bind (preserves_len_and stH (Preserves.getEntry evH)) fun _ => ?_
  split
  · refine bind_guard_preserves _ fun hg => ?_
    rcases hg with ⟨rfl, _, _⟩
    refine Preserves.bind (preserves_len_and stH (Preserves.guardTrace _)) fun _ => ?_
    split
    · exact Preserves.bind (preserves_len_and stH (preserves_hsv_sendMessage _)) fun _ =>
        Preserves.bind (preserves_len_and stH (Preserves.receiveMessage _)) fun _ =>
        Preserves.bind (preserves_len_and stH (Preserves.verifyMacAndDecrypt _ _ _ _)) fun _ =>
        Preserves.bind (preserves_len_and stH (preserves_hsv_logTR_nonRecvMK _)) fun _ =>
        Preserves.bind (preserves_len_and stH (preserves_hsv_logTR_nonRecvMK _)) fun _ =>
        preserves_hsv_logMessageKeyAndStore_receiver stH me _ _ _ _ _ _ _ rfl rfl rfl hsid
    · exact fun _ h => h
  · exact fun _ h => h

/-- `HandshakeSessionValid` holds on every reachable composed trace. -/
theorem handshakeSessionValid_reachable {tr : ExecTrace} (hReach : tr.Reachable reachability) :
    HandshakeSessionValid tr := by
  refine composed_reachable_induction handshakeSessionValid_nil
    (fun msg _ _ h => hsv_append_non_cEv (NetE msg) rfl rfl rfl h)
    (fun p => ?_) (fun p skIdx => ?_) (fun b idx => ?_) (fun b idx => ?_) (fun b => ?_)
    preserves_hsv_aliceStart preserves_hsv_bobStart
    preserves_hsv_messageEncrypt preserves_hsv_messageEncryptAbort
    preserves_hsv_messageDecrypt preserves_hsv_messageDecryptSkipped
    (fun me stH k => ?_) (fun me stH => ?_) (fun evH => ?_)
    (fun p idx => ?_) (fun b idx => ?_) (fun b idx => ?_) (fun b idx => ?_)
    ?_ ?_ (fun pkIdx => ?_) (fun pkIdx => ?_) hReach
  · unfold _root_.DY.Libsignal.PQXDH.registerIdentity
    exact Preserves.bind (Preserves.requireTracePredicate _) fun _ => Preserves.bind (preserves_hsv_genRand 32) fun _ =>
      Preserves.bind (preserves_hsv_logPQ _) fun _ => Preserves.bind (preserves_hsv_sendMessage _) fun _ =>
      Preserves.bind (preserves_hsv_sendMessage _) fun _ => preserves_hsv_storePQ p _
  · unfold _root_.DY.Libsignal.PQXDH.registerCorruptIdentity
    exact Preserves.bind (Preserves.requireTracePredicate _) fun _ => Preserves.bind (Preserves.receiveMessage skIdx) fun _ =>
      Preserves.bind (preserves_hsv_logPQ _) fun _ => preserves_hsv_logPQ _
  · unfold _root_.DY.Libsignal.PQXDH.genSignedPrekey
    exact Preserves.bind (preserves_hsv_getKey b idx .identity) fun _ => Preserves.bind (preserves_hsv_genRand 32) fun _ =>
      Preserves.bind (preserves_hsv_genRand 64) fun _ => Preserves.bind (preserves_hsv_logPQ _) fun _ =>
      Preserves.bind (preserves_hsv_storePQ b _) fun _ => Preserves.bind (preserves_hsv_sendMessage _) fun _ =>
      Preserves.bind (preserves_hsv_sendMessage _) fun _ => Preserves.pure _
  · unfold _root_.DY.Libsignal.PQXDH.genPQPrekey
    exact Preserves.bind (preserves_hsv_getKey b idx .identity) fun _ => Preserves.bind (preserves_hsv_genRand 64) fun _ =>
      Preserves.bind (preserves_hsv_genRand 64) fun _ => Preserves.bind (preserves_hsv_logPQ _) fun _ =>
      Preserves.bind (preserves_hsv_storePQ b _) fun _ => Preserves.bind (preserves_hsv_sendMessage _) fun _ =>
      Preserves.bind (preserves_hsv_sendMessage _) fun _ => Preserves.pure _
  · unfold _root_.DY.Libsignal.PQXDH.genOneTimePrekey
    exact Preserves.bind (preserves_hsv_genRand 32) fun _ => Preserves.bind (preserves_hsv_logPQ _) fun _ =>
      Preserves.bind (preserves_hsv_storePQ b _) fun _ => Preserves.bind (preserves_hsv_sendMessage _) fun _ =>
      Preserves.pure _
  · unfold _root_.DY.Libsignal.TripleRatchet.exposeKey
    refine Preserves.bind (Preserves.getLocalState_tr me stH) fun _ => ?_
    cases k with
    | rk | dhs | cks => exact Preserves.bind (preserves_hsv_logTR_nonRecvMK _) fun _ => preserves_hsv_sendMessage _
    | ckr pk =>
      dsimp only; split
      · exact Preserves.bind (preserves_hsv_logTR_nonRecvMK _) fun _ => preserves_hsv_sendMessage _
      · exact Preserves.failure
  · unfold _root_.DY.Libsignal.TripleRatchet.exposeSpqr
    exact Preserves.bind (Preserves.getLocalState_tr me stH) fun _ =>
      Preserves.bind (preserves_hsv_logTR_nonRecvMK _) fun _ => preserves_hsv_sendMessage _
  · unfold _root_.DY.Libsignal.TripleRatchet.exposeSkipped
    refine Preserves.bind (Preserves.getEntry evH) fun _ => ?_
    split
    · exact Preserves.bind (Preserves.guardTrace _) fun _ =>
        Preserves.bind (preserves_hsv_logTR_nonRecvMK _) fun _ => preserves_hsv_sendMessage _
    · exact Preserves.failure
  · unfold _root_.DY.Libsignal.PQXDH.compromiseIK
    exact Preserves.bind (preserves_hsv_getKey p idx .identity) fun _ =>
      Preserves.bind (preserves_hsv_logPQ _) fun _ => preserves_hsv_sendMessage _
  · unfold _root_.DY.Libsignal.PQXDH.compromiseSPK
    exact Preserves.bind (preserves_hsv_getKey b idx .signedPrekey) fun _ =>
      Preserves.bind (preserves_hsv_logPQ _) fun _ => preserves_hsv_sendMessage _
  · unfold _root_.DY.Libsignal.PQXDH.compromisePQSPK
    exact Preserves.bind (preserves_hsv_getKey b idx .pqPrekey) fun _ =>
      Preserves.bind (preserves_hsv_logPQ _) fun _ => preserves_hsv_sendMessage _
  · unfold _root_.DY.Libsignal.PQXDH.compromiseOPK
    exact Preserves.bind (preserves_hsv_getKey b idx .oneTimePrekey) fun _ =>
      Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
      Preserves.bind (preserves_hsv_logPQ _) fun _ => preserves_hsv_sendMessage _
  · unfold _root_.DY.Libsignal.PQXDH.breakDH; exact preserves_hsv_logPQ _
  · unfold _root_.DY.Libsignal.PQXDH.breakKEM; exact preserves_hsv_logPQ _
  · unfold _root_.DY.Libsignal.PQXDH.invertDH
    refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => Preserves.bind (Preserves.receiveMessage pkIdx) fun _ => ?_
    split <;> [exact preserves_hsv_sendMessage _; exact Preserves.failure]
  · unfold _root_.DY.Libsignal.PQXDH.invertKEM
    exact Preserves.bind (Preserves.requireTracePredicate _) fun _ => Preserves.bind (Preserves.receiveMessage pkIdx) fun _ =>
      Preserves.bind (Preserves.monadLiftErr _) fun _ => preserves_hsv_sendMessage _

theorem stepsWF_reachable : ∀ (ss : List Step) {tr : ExecTrace},
    tr.Reachable reachability → StepsWF ss tr → (runSteps ss tr).Reachable reachability
  | [], _, hReach, _ => hReach
  | s :: ss, _, hReach, ⟨hpre, _, hwf⟩ =>
    stepsWF_reachable ss (Trace.Reachable.Step s.toInput hpre hReach) hwf

theorem stepsWF_le : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => Trace.le_refl tr
  | s :: ss, tr =>
    Trace.le_trans _ _ _ ((reachability.step s.toInput).2.run tr).2.property (stepsWF_le ss (s.next tr))

theorem modelRunWF_reachable {r : ProtocolSetup} {ss : List Step} (h : ModelRunWF r ss) :
    (runTrace r ss).Reachable reachability :=
  stepsWF_reachable ss h.2.1 h.2.2.1

/-! ## `ppkOf` and `pendingPreKey` Monotonicity -/

/-- Session-descriptor form of `pendingPreKey`. -/
def ppkOf (tr : ExecTrace) (s : SessionInfo) : Option (_root_.DY.Bytes × _root_.DY.Bytes) :=
  (List.range tr.length).findSome? fun i =>
    match tr.getEventAt ComposedEvent i with
    | some (.HandshakeSession s' d) =>
      if s' = s then
        match tr.getEventAt PQXDHEvent d with
        | some (.AliceDone _ _ _ _ _ _ _ ek ct _) => some (ek, ct)
        | _ => none
      else none
    | none => none

/-- No `ComposedEvent.HandshakeSession s _` with `s.me = alice` is logged at indices `≥ n₀`. -/
def NoNewHsFrom (alice : Participant) (n₀ : Nat) (tr : ExecTrace) : Prop :=
  n₀ ≤ tr.length ∧
  ∀ m, n₀ ≤ m → m < tr.length → ∀ s d,
    tr.getEventAt ComposedEvent m = some (.HandshakeSession s d) → s.me ≠ alice

/-- No `TREvent.MessageKey s .receiver ..` with `s.me = alice` is logged at indices `≥ n₀`. -/
def NoNewRecvMKFrom (alice : Participant) (n₀ : Nat) (tr : ExecTrace) : Prop :=
  n₀ ≤ tr.length ∧
  ∀ m, n₀ ≤ m → m < tr.length → ∀ s seed salt n rIdx par,
    tr.getEventAt TREvent m = some (.MessageKey s .receiver seed salt n rIdx par) →
    s.me ≠ alice

private theorem findSome?_filterMap {α β γ : Type _} (g : α → Option β) (f : β → Option γ) :
    ∀ l : List α, (l.filterMap g).findSome? f = l.findSome? fun x => (g x).bind f
  | [] => rfl
  | x :: xs => by
    cases gx : g x with
    | none => simp [List.filterMap_cons_none gx, gx, findSome?_filterMap g f xs]
    | some y =>
      simp only [List.filterMap_cons_some gx, List.findSome?_cons, gx, Option.bind_some]
      cases f y <;> simp [findSome?_filterMap g f xs]

theorem pendingPreKey_eq_ppkOf {tr : ExecTrace} {i : Nat} {p : Participant} {st : TRState}
    (h : (tr.at? i : Option TRStEntry) = some ⟨⟨p, st⟩⟩) :
    pendingPreKey tr i =
      if sessionHasDecrypted tr (st.sessionInfo p) i then none else ppkOf tr (st.sessionInfo p) := by
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents ppkOf
  rw [h, Option.map_some]
  dsimp only
  split_ifs with hdec
  · rfl
  · rw [findSome?_filterMap]
    refine congrArg (fun fn => (List.range tr.length).findSome? fn) (funext fun j => ?_)
    cases tr.getEventAt ComposedEvent j with
    | none => rfl
    | some ev =>
      cases ev with
      | HandshakeSession s' d =>
        by_cases hs : s' = st.sessionInfo p
        · simp only [hs, ↓reduceIte]
          rcases tr.getEventAt PQXDHEvent d with _ | pqev
          · rfl
          · cases pqev <;> rfl
        · simp only [hs, ↓reduceIte]; rfl

theorem ppkOf_eq_none_of_initiator_false {tr : ExecTrace} (hv : HandshakeSessionValid tr)
    {s : SessionInfo} (hinit : s.initiator = false) :
    ppkOf tr s = none := by
  unfold ppkOf
  rw [List.findSome?_eq_none_iff]
  intro i _
  rcases hev : tr.getEventAt ComposedEvent i with _ | ⟨s', d⟩
  · rfl
  · dsimp only
    by_cases hs : s' = s
    · subst hs; simp only [↓reduceIte]
      rcases hpq : tr.getEventAt PQXDHEvent d with _ | ev_pq
      · rfl
      · cases ev_pq with
        | AliceDone a b ikA ikB spk pqpk opk ek ct keys =>
          have htrue := ((hv.hs i s' d hev).2.2 a b ikA ikB spk pqpk opk ek ct keys hpq).1
          rw [hinit] at htrue; cases htrue
        | _ => rfl
    · simp [hs]

theorem pendingPreKey_eq_none_of_initiator_false {tr : ExecTrace} (hv : HandshakeSessionValid tr)
    {i : Nat} {p : Participant} {st : TRState}
    (hat : (tr.at? i : Option TRStEntry) = some ⟨⟨p, st⟩⟩)
    (hinit : st.initiator = false) :
    pendingPreKey tr i = none := by
  rw [pendingPreKey_eq_ppkOf hat,
    ppkOf_eq_none_of_initiator_false hv (show (st.sessionInfo p).initiator = false from hinit),
    ite_self]

private theorem findSome?_congr_mem {α β : Type} {xs : List α} {f g : α → Option β}
    (hfg : ∀ x ∈ xs, f x = g x) : xs.findSome? f = xs.findSome? g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.findSome?_cons, hfg x List.mem_cons_self]
    cases g x with
    | none => exact ih fun y hy => hfg y (List.mem_cons_of_mem x hy)
    | some v => rfl

private theorem any_congr_mem {α : Type} {xs : List α} {f g : α → Bool}
    (hfg : ∀ x ∈ xs, f x = g x) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons, hfg x List.mem_cons_self,
      ih fun y hy => hfg y (List.mem_cons_of_mem x hy)]

theorem sessionHasDecrypted_of_le {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {s : SessionInfo} {i : Nat} (hi : i ≤ tr.length) :
    sessionHasDecrypted tr' s i = sessionHasDecrypted tr s i := by
  unfold sessionHasDecrypted
  refine any_congr_mem fun j hj => ?_
  have hj_lt : j < tr.length := Nat.lt_of_lt_of_le (List.mem_range.mp hj) hi
  rw [bks_getEventAt_of_le TREvent hle hj_lt]

theorem sessionHasDecrypted_mono_true {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {s : SessionInfo} {i j : Nat} (hi : i ≤ tr.length) (hij : i ≤ j)
    (hdec : sessionHasDecrypted tr s i = true) :
    sessionHasDecrypted tr' s j = true := by
  unfold sessionHasDecrypted at hdec ⊢
  rw [List.any_eq_true] at hdec ⊢
  obtain ⟨m, hm_range, hm⟩ := hdec
  have hm_lt_i : m < i := List.mem_range.mp hm_range
  refine ⟨m, List.mem_range.mpr (Nat.lt_of_lt_of_le hm_lt_i hij), ?_⟩
  rwa [bks_getEventAt_of_le TREvent hle (Nat.lt_of_lt_of_le hm_lt_i hi)]

theorem sessionHasDecrypted_eq_false_of_current_and_noRecv {tr tr' : ExecTrace}
    (hv : HandshakeSessionValid tr) (hle : tr ≤ tr')
    {p : Participant} {k₀ k : Nat} {st₀ : TRState}
    (hat₀ : (tr.at? k₀ : Option TRStEntry) = some ⟨⟨p, st₀⟩⟩)
    (hcur₀ : isCurrentSnapshot tr k₀ = true)
    (hdec₀ : sessionHasDecrypted tr (st₀.sessionInfo p) k₀ = false)
    (hk : k ≤ tr'.length)
    (hnoRecv : NoNewRecvMKFrom p tr.length tr') :
    sessionHasDecrypted tr' (st₀.sessionInfo p) k = false := by
  unfold sessionHasDecrypted
  rw [List.any_eq_false]
  intro m hm_range
  have hm_lt_k : m < k := List.mem_range.mp hm_range
  have hm_lt_tr' : m < tr'.length := Nat.lt_of_lt_of_le hm_lt_k hk
  by_cases hm_tr : m < tr.length
  · rw [bks_getEventAt_of_le TREvent hle hm_tr]
    by_cases hm_k₀ : m < k₀
    · unfold sessionHasDecrypted at hdec₀
      rw [List.any_eq_false] at hdec₀
      exact hdec₀ m (List.mem_range.mpr hm_k₀)
    · rcases hev : tr.getEventAt TREvent m with _ | ev_tr
      · simp
      · cases ev_tr with
        | MessageKey s' dir seed salt n rIdx par =>
          cases dir with
          | sender => simp
          | receiver =>
            dsimp only
            rw [Bool.not_eq_true, decide_eq_false_iff_not]
            intro hs_eq
            subst hs_eq
            obtain ⟨_, st_m, hat_m, hinit_m⟩ := hv.mkRecv m _ seed salt n rIdx par hev
            have hfalse := isCurrentSnapshot_false_of_later hat₀ hat_m (by omega) hinit_m
            rw [hfalse] at hcur₀; cases hcur₀
        | _ => simp
  · rcases hev : tr'.getEventAt TREvent m with _ | ev_tr
    · simp
    · cases ev_tr with
      | MessageKey s' dir seed salt n rIdx par =>
        cases dir with
        | sender => simp
        | receiver =>
          dsimp only
          rw [Bool.not_eq_true, decide_eq_false_iff_not]
          intro hs_eq
          have hne := hnoRecv.2 m (Nat.le_of_not_lt hm_tr) hm_lt_tr' s' seed salt n rIdx par hev
          exact hne (congrArg SessionInfo.me hs_eq)
      | _ => simp

theorem ppkOf_mono {tr tr' : ExecTrace} (hv : HandshakeSessionValid tr) (hle : tr ≤ tr')
    {s : SessionInfo} {val : _root_.DY.Bytes × _root_.DY.Bytes} (h : ppkOf tr s = some val) :
    ppkOf tr' s = some val := by
  unfold ppkOf at h ⊢
  have hlen : tr.length ≤ tr'.length := Trace.length_le tr tr' hle
  have hrange : List.range tr'.length = List.range tr.length ++ List.range' tr.length (tr'.length - tr.length) := by
    have heq : tr'.length = tr.length + (tr'.length - tr.length) := by omega
    conv => lhs; rw [heq]
    rw [List.range_eq_range', List.range_eq_range', ← List.range'_append_1]
    simp only [Nat.zero_add]
  rw [hrange, List.findSome?_append]
  rw [show (List.range tr.length).findSome? _ = some val from by
    rw [← h]
    refine findSome?_congr_mem fun i hi => ?_
    have hilt : i < tr.length := List.mem_range.mp hi
    rw [bks_getEventAt_of_le ComposedEvent hle hilt]
    rcases hev : tr.getEventAt ComposedEvent i with _ | ⟨s', d⟩
    · rfl
    · dsimp only
      have hd_lt : d < tr.length := Nat.lt_trans (hv.hs i s' d hev).1 hilt
      rw [bks_getEventAt_of_le PQXDHEvent hle hd_lt]]
  rfl

theorem ppkOf_eq_of_noHs {tr tr' : ExecTrace} (hv : HandshakeSessionValid tr) (hle : tr ≤ tr')
    {p : Participant} (hnoHs : NoNewHsFrom p tr.length tr')
    {s : SessionInfo} (hs_me : s.me = p) :
    ppkOf tr' s = ppkOf tr s := by
  conv => lhs; unfold ppkOf
  have hlen : tr.length ≤ tr'.length := Trace.length_le tr tr' hle
  have hrange : List.range tr'.length = List.range tr.length ++ List.range' tr.length (tr'.length - tr.length) := by
    have heq : tr'.length = tr.length + (tr'.length - tr.length) := by omega
    conv => lhs; rw [heq]
    rw [List.range_eq_range', List.range_eq_range', ← List.range'_append_1]
    simp only [Nat.zero_add]
  rw [hrange, List.findSome?_append]
  rw [show (List.range tr.length).findSome? _ = ppkOf tr s from by
    unfold ppkOf
    refine findSome?_congr_mem fun i hi => ?_
    have hilt : i < tr.length := List.mem_range.mp hi
    rw [bks_getEventAt_of_le ComposedEvent hle hilt]
    rcases hev : tr.getEventAt ComposedEvent i with _ | ⟨s', d⟩
    · rfl
    · dsimp only
      have hd_lt : d < tr.length := Nat.lt_trans (hv.hs i s' d hev).1 hilt
      rw [bks_getEventAt_of_le PQXDHEvent hle hd_lt]]
  rw [show (List.range' tr.length (tr'.length - tr.length)).findSome? _ = none from by
    rw [List.findSome?_eq_none_iff]
    intro m hm
    rw [List.mem_range'_1] at hm
    have hm_lt' : m < tr'.length := by omega
    rcases hev : tr'.getEventAt ComposedEvent m with _ | ⟨s', d⟩
    · rfl
    · dsimp only
      by_cases hs : s' = s
      · exfalso
        exact hnoHs.2 m hm.1 hm_lt' s' d hev ((congrArg SessionInfo.me hs).trans hs_me)
      · simp [hs]]
  exact Option.or_none

theorem pendingPreKey_mono {tr tr' : ExecTrace} (hv : HandshakeSessionValid tr) (hle : tr ≤ tr')
    {i : Nat} {val : _root_.DY.Bytes × _root_.DY.Bytes} (h : pendingPreKey tr i = some val) :
    pendingPreKey tr' i = some val := by
  rcases hat : (tr.at? i : Option TRStEntry) with _ | ⟨⟨p, st⟩⟩
  · unfold pendingPreKey DY.ExecTrace.getLocalStateAt at h; rw [hat] at h; cases h
  · have hi_lt : i < tr.length := bks_lt_length_of_at? hat
    rw [pendingPreKey_eq_ppkOf hat] at h
    rw [pendingPreKey_eq_ppkOf (at?_le_some hle hat),
      sessionHasDecrypted_of_le hle (Nat.le_of_lt hi_lt)]
    cases hdec : sessionHasDecrypted tr (st.sessionInfo p) i
    · rw [hdec] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ppkOf_mono hv hle h
    · rw [hdec] at h; cases h

theorem pendingPreKey_eq_of_sinfo {tr tr' : ExecTrace} (hv : HandshakeSessionValid tr)
    (hle : tr ≤ tr') {i j : Nat} {p : Participant} {st st' : TRState}
    {val : _root_.DY.Bytes × _root_.DY.Bytes}
    (hi : (tr.at? i : Option TRStEntry) = some ⟨⟨p, st⟩⟩)
    (hcur : isCurrentSnapshot tr i = true)
    (hj : (tr'.at? j : Option TRStEntry) = some ⟨⟨p, st'⟩⟩)
    (hs : st.sessionInfo p = st'.sessionInfo p)
    (hnoRecv : NoNewRecvMKFrom p tr.length tr')
    (h : pendingPreKey tr i = some val) :
    pendingPreKey tr' j = some val := by
  have hj_lt : j < tr'.length := bks_lt_length_of_at? hj
  rw [pendingPreKey_eq_ppkOf hi] at h
  cases hdec : sessionHasDecrypted tr (st.sessionInfo p) i
  · rw [hdec] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
    have hdec' := sessionHasDecrypted_eq_false_of_current_and_noRecv hv hle hi hcur hdec
      (Nat.le_of_lt hj_lt) hnoRecv
    rw [pendingPreKey_eq_ppkOf hj, ← hs, hdec']
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ppkOf_mono hv hle h
  · rw [hdec] at h; cases h

/-! ## `AlicePendingKeysOn` and `AliceRecordPendingInSession` Transport -/

theorem alicePendingKeysOn_ext {interp' : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {alice : Participant} {tr tr' : ExecTrace} {bk kct : HwBytes}
    (hv : HandshakeSessionValid tr) (hle : tr ≤ tr')
    (hnew : NewBobSinfo alice tr tr')
    (hnoRecv : NoNewRecvMKFrom alice tr.length tr')
    (h : AlicePendingKeysOn interp' S g alice tr bk kct) :
    AlicePendingKeysOn interp' S g alice tr' bk kct := by
  intro k st hst hcur
  have hat := bks_stored_of_getLocalState hst
  by_cases hk : k < tr.length
  · have hat₀ : (tr.at? k : Option TRStEntry) = some ⟨⟨alice, st⟩⟩ := by
      have hi' : k < tr'.length := Nat.lt_of_lt_of_le hk (Trace.length_le tr tr' hle)
      have hle_at : (tr'.at? k : Option TRStEntry) = (tr.at? k : Option TRStEntry) := by
        simp only [Trace.at?, hk, hi', ↓reduceDIte]
        rw [← Trace.at_le tr tr' k hk hle]
      rwa [← hle_at]
    obtain ⟨ek, ct, hppk, hbk, hkct⟩ := h k st (bks_getLocalState_of_stored hat₀)
      (isCurrentSnapshot_of_le_of_lt hle hk hcur)
    exact ⟨ek, ct, pendingPreKey_mono hv hle hppk, hbk, hkct⟩
  · obtain ⟨k₀, st₀, hat₀, hcur₀, hs⟩ := hnew k st (Nat.le_of_not_lt hk) hat
    obtain ⟨ek, ct, hppk, hbk, hkct⟩ := h k₀ st₀ (bks_getLocalState_of_stored hat₀) hcur₀
    exact ⟨ek, ct, pendingPreKey_eq_of_sinfo hv hle hat₀ hcur₀ hat hs hnoRecv hppk, hbk, hkct⟩

theorem aliceNotPendingOn_ext {alice : Participant} {tr tr' : ExecTrace}
    (hv : HandshakeSessionValid tr) (hle : tr ≤ tr')
    (hnew : NewBobSinfo alice tr tr')
    (hnoHs : NoNewHsFrom alice tr.length tr')
    (h : AliceNotPendingOn alice tr) :
    AliceNotPendingOn alice tr' := by
  intro k st hst hcur
  have hat := bks_stored_of_getLocalState hst
  by_cases hk : k < tr.length
  · have hat₀ : (tr.at? k : Option TRStEntry) = some ⟨⟨alice, st⟩⟩ := by
      have hi' : k < tr'.length := Nat.lt_of_lt_of_le hk (Trace.length_le tr tr' hle)
      have hle_at : (tr'.at? k : Option TRStEntry) = (tr.at? k : Option TRStEntry) := by
        simp only [Trace.at?, hk, hi', ↓reduceDIte]
        rw [← Trace.at_le tr tr' k hk hle]
      rwa [← hle_at]
    have hnone₀ := h k st (bks_getLocalState_of_stored hat₀)
      (isCurrentSnapshot_of_le_of_lt hle hk hcur)
    rw [pendingPreKey_eq_ppkOf hat₀] at hnone₀
    rw [pendingPreKey_eq_ppkOf hat, sessionHasDecrypted_of_le hle (Nat.le_of_lt hk),
      ppkOf_eq_of_noHs hv hle hnoHs rfl]
    exact hnone₀
  · obtain ⟨k₀, st₀, hat₀, hcur₀, hs⟩ := hnew k st (Nat.le_of_not_lt hk) hat
    have hnone₀ := h k₀ st₀ (bks_getLocalState_of_stored hat₀) hcur₀
    have hk₀_lt : k₀ < tr.length := bks_lt_length_of_at? hat₀
    rw [pendingPreKey_eq_ppkOf hat₀] at hnone₀
    rw [pendingPreKey_eq_ppkOf hat, ← hs]
    cases hdec₀ : sessionHasDecrypted tr (st₀.sessionInfo alice) k₀
    · rw [hdec₀] at hnone₀; simp only [Bool.false_eq_true, ↓reduceIte] at hnone₀
      rw [ppkOf_eq_of_noHs hv hle hnoHs rfl, hnone₀, ite_self]
    · have hdec' := sessionHasDecrypted_mono_true hle (Nat.le_of_lt hk₀_lt)
        (Nat.le_trans (Nat.le_of_lt hk₀_lt) (Nat.le_of_not_lt hk)) hdec₀
      rw [hdec']; rfl

private theorem bkt_pqSt {alice : Participant} {tr : ExecTrace} (p : Participant) (st : PQXDHState) :
    BkTraceful alice tr (fun _ => True) (_root_.DY.PersistentLocalState.storeLocalState p st) :=
  fun _ _ ht => ⟨bkNew_append_non_st
    (⟨⟨p, st⟩⟩ : _root_.DY.PersistentGlobalState.State.ExecEntryT (_root_.DY.PersistentLocalState.LocalState PQXDHState))
    rfl ht, fun _ _ => trivial⟩
private theorem bkt_rnd {alice : Participant} {tr : ExecTrace} (n : Nat) :
    BkTraceful alice tr (fun _ => True) (_root_.DY.Random.genRand n) :=
  BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_genRand n)
private theorem bkt_net {alice : Participant} {tr : ExecTrace} (m : _root_.DY.Bytes) :
    BkTraceful alice tr (fun _ => True) (_root_.DY.Network.sendMessage m) :=
  BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage m)
private theorem bkt_getKey {alice : Participant} {tr : ExecTrace} (p : Participant) (idx : Nat)
    (k : _root_.DY.Libsignal.PQXDH.KeyKind) :
    BkTraceful alice tr (fun _ => True) (_root_.DY.Libsignal.PQXDH.getKey p idx k) :=
  BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_getKey p idx k))
private theorem bkt_recv {alice : Participant} {tr : ExecTrace} (idx : Nat) :
    BkTraceful alice tr (fun _ => True) (_root_.DY.Network.receiveMessage idx) :=
  BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage idx))
private theorem bkt_guardOn {alice : Participant} {tr : ExecTrace} (p : ExecTrace → Bool) :
    BkTraceful alice tr (fun _ => True) (_root_.DY.Libsignal.TripleRatchet.guardTrace p) :=
  BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_guardOnTrace p))

theorem bkNew_step {alice : Participant} {tr : ExecTrace} {s : Step}
    (hnoA : ∀ b idIdx regB bh, s ≠ .aliceStart alice b idIdx regB bh)
    (hnoB : ∀ a kh regA mh pqIdx spqrIdx, s ≠ .bobStart alice a kh regA mh pqIdx spqrIdx) :
    BkNew alice tr (s.next tr) := by
  cases s with
  | network msg => exact bkNew_append_non_st (NetE msg) rfl (bkNew_refl alice tr)
  | registerIdentity p =>
    change BkNew alice tr ((_root_.DY.Libsignal.PQXDH.registerIdentity p).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.registerIdentity
    exact BkTraceful.run_start (BkTraceful.bind_true (bkt_guardOn _) fun _ => BkTraceful.bind_true (bkt_rnd 32) fun _ =>
      BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ => BkTraceful.bind_true (bkt_net _) fun _ =>
      BkTraceful.bind_true (bkt_net _) fun _ => bkt_pqSt p _)
  | registerCorruptIdentity p skIdx =>
    change BkNew alice tr ((_root_.DY.Libsignal.PQXDH.registerCorruptIdentity p skIdx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.registerCorruptIdentity
    exact BkTraceful.run_start (BkTraceful.bind_true (bkt_guardOn _) fun _ =>
      BkTraceful.bind_true (bkt_recv skIdx) fun _ => BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ =>
      BkTraceful.logEvent_pq _)
  | genSignedPrekey b idIdx =>
    change BkNew alice tr ((_root_.DY.Libsignal.PQXDH.genSignedPrekey b idIdx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.genSignedPrekey
    exact BkTraceful.run_start (BkTraceful.bind_true (bkt_getKey b idIdx .identity) fun _ =>
      BkTraceful.bind_true (bkt_rnd 32) fun _ => BkTraceful.bind_true (bkt_rnd 64) fun _ =>
      BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ => BkTraceful.bind_true (bkt_pqSt b _) fun _ =>
      BkTraceful.bind_true (bkt_net _) fun _ => BkTraceful.bind_true (bkt_net _) fun _ => BkTraceful.pure trivial)
  | genPQPrekey b idIdx =>
    change BkNew alice tr ((_root_.DY.Libsignal.PQXDH.genPQPrekey b idIdx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.genPQPrekey
    exact BkTraceful.run_start (BkTraceful.bind_true (bkt_getKey b idIdx .identity) fun _ =>
      BkTraceful.bind_true (bkt_rnd 64) fun _ => BkTraceful.bind_true (bkt_rnd 64) fun _ =>
      BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ => BkTraceful.bind_true (bkt_pqSt b _) fun _ =>
      BkTraceful.bind_true (bkt_net _) fun _ => BkTraceful.bind_true (bkt_net _) fun _ => BkTraceful.pure trivial)
  | genOneTimePrekey b =>
    change BkNew alice tr ((_root_.DY.Libsignal.PQXDH.genOneTimePrekey b).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.genOneTimePrekey
    exact BkTraceful.run_start (BkTraceful.bind_true (bkt_rnd 32) fun _ =>
      BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ => BkTraceful.bind_true (bkt_pqSt b _) fun _ =>
      BkTraceful.bind_true (bkt_net _) fun _ => BkTraceful.pure trivial)
  | aliceStart a b idIdx regB bh =>
    exact BkTraceful.run_start (BkTraceful.aliceStart (fun heq => hnoA b idIdx regB bh (by subst heq; rfl)) b idIdx regB bh)
  | bobStart b a kh regA mh pqIdx spqrIdx =>
    have hb : b ≠ alice := fun heq => hnoB a kh regA mh pqIdx spqrIdx (by subst heq; rfl)
    change BkNew alice tr ((_root_.DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqrIdx).run tr).2.val
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.bobStart_eq_inline]
    refine BkTraceful.run_start (Q := fun _ => True)
      (BkTraceful.bind_true (BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_bobHandshake b a kh regA mh.ek mh.ct)) fun o =>
        BkTraceful.bind_true (BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_receiveSignalMsg mh.msg)) fun msg =>
        BkTraceful.bind (BkTraceful.ensureReceiverChain _ msg.ratchetKey) fun ⟨st, c, rat⟩ _ => ?_)
    dsimp only; split
    · next seed c' _ =>
      split
      · next spqr' key _ =>
        refine BkTraceful.bind_true (bkt_net key) fun _ => BkTraceful.bind_true (bkt_recv pqIdx) fun pqSalt =>
          BkTraceful.bind_true (BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_verifyMacAndDecrypt st msg pqSalt seed)) fun m => ?_
        (cases o.opk <;> try dsimp only)
        swap
        refine BkTraceful.bind_true (bkt_guardOn _) fun _ =>
          BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ => ?_
        all_goals
          refine BkTraceful.bind_true
            (BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix Symbolic.Swarm.CREF.XplSteps.xfix_traceLength)) fun doneIdx =>
            BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ => ?_
          try dsimp only
          cases rat
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact BkTraceful.bind_true (BkTraceful.logEvent_c _) fun _ =>
              BkTraceful.bind_true (BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix Symbolic.Swarm.CREF.XplSteps.xfix_traceLength)) fun _ =>
              BkTraceful.bind_true (BkTraceful.logSkippedKeys _ _ _ _ _ _ _) fun _ =>
              BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
              BkTraceful.logMessageKeyAndStore b (fun hbe => absurd hbe hb)
          · simp only [↓reduceIte]
            exact BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
              BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
              BkTraceful.bind_true (BkTraceful.logEvent_c _) fun _ =>
              BkTraceful.bind_true (BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix Symbolic.Swarm.CREF.XplSteps.xfix_traceLength)) fun _ =>
              BkTraceful.bind_true (BkTraceful.logSkippedKeys _ _ _ _ _ _ _) fun _ =>
              BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
              BkTraceful.logMessageKeyAndStore b (fun hbe => absurd hbe hb)
      · exact BkTraceful.failure
    · exact BkTraceful.failure
  | messageEncrypt me stateIdx coinsLen pqIdx => exact bkNew_messageEncrypt me stateIdx coinsLen pqIdx
  | messageEncryptAbort me stateIdx => exact bkNew_messageEncryptAbort me stateIdx
  | messageDecrypt me stateIdx msgIdx pqIdx spqrIdx => exact bkNew_messageDecrypt me stateIdx msgIdx pqIdx spqrIdx
  | messageDecryptSkipped me stateIdx msgIdx k pqIdx spqrIdx => exact bkNew_messageDecryptSkipped me stateIdx msgIdx k pqIdx spqrIdx
  | exposeKey me stateIdx comp =>
    change BkNew alice tr ((_root_.DY.Libsignal.TripleRatchet.exposeKey me stateIdx comp).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.exposeKey
    refine BkTraceful.run_start (Q := fun _ => True)
      (BkTraceful.bind_true (BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix
        (Symbolic.Swarm.CREF.XplSteps.xfix_getLocalState me stateIdx))) fun _ => ?_)
    cases comp with
    | rk | dhs | cks => exact BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ => bkt_net _
    | ckr _ => dsimp only; split <;> [exact BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ => bkt_net _; exact BkTraceful.failure]
  | exposeSpqr me stateIdx =>
    change BkNew alice tr ((_root_.DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.exposeSpqr
    exact BkTraceful.run_start (BkTraceful.bind_true (BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix
      (Symbolic.Swarm.CREF.XplSteps.xfix_getLocalState me stateIdx))) fun _ =>
      BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ => bkt_net _)
  | exposeSkipped skIdx =>
    change BkNew alice tr ((_root_.DY.Libsignal.TripleRatchet.exposeSkipped skIdx).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.exposeSkipped
    refine BkTraceful.run_start (Q := fun _ => True)
      (BkTraceful.bind_true (BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix
        (Symbolic.Swarm.CREF.XplSteps.xfix_getEntry skIdx))) fun _ => ?_)
    split
    · exact BkTraceful.bind_true (BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix
        (Symbolic.Swarm.CREF.XplSteps.xfix_guardTrace _))) fun _ =>
        BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ => bkt_net _
    · exact BkTraceful.failure
  | compromiseIK p idx =>
    change BkNew alice tr ((_root_.DY.Libsignal.PQXDH.compromiseIK p idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.compromiseIK
    exact BkTraceful.run_start (BkTraceful.bind_true (bkt_getKey p idx .identity) fun _ =>
      BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ => bkt_net _)
  | compromiseSPK b idx =>
    change BkNew alice tr ((_root_.DY.Libsignal.PQXDH.compromiseSPK b idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.compromiseSPK
    exact BkTraceful.run_start (BkTraceful.bind_true (bkt_getKey b idx .signedPrekey) fun _ =>
      BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ => bkt_net _)
  | compromisePQSPK b idx =>
    change BkNew alice tr ((_root_.DY.Libsignal.PQXDH.compromisePQSPK b idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.compromisePQSPK
    exact BkTraceful.run_start (BkTraceful.bind_true (bkt_getKey b idx .pqPrekey) fun _ =>
      BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ => bkt_net _)
  | compromiseOPK b idx =>
    change BkNew alice tr ((_root_.DY.Libsignal.PQXDH.compromiseOPK b idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.compromiseOPK
    exact BkTraceful.run_start (BkTraceful.bind_true (bkt_getKey b idx .oneTimePrekey) fun _ =>
      BkTraceful.bind_true (bkt_guardOn _) fun _ =>
      BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ => bkt_net _)
  | breakDH =>
    change BkNew alice tr ((_root_.DY.Libsignal.PQXDH.breakDH).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.breakDH; exact BkTraceful.run_start (BkTraceful.logEvent_pq _)
  | breakKEM =>
    change BkNew alice tr ((_root_.DY.Libsignal.PQXDH.breakKEM).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.breakKEM; exact BkTraceful.run_start (BkTraceful.logEvent_pq _)
  | invertDH pkIdx =>
    change BkNew alice tr ((_root_.DY.Libsignal.PQXDH.invertDH pkIdx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.invertDH
    refine BkTraceful.run_start (Q := fun _ => True)
      (BkTraceful.bind_true (bkt_guardOn _) fun _ => BkTraceful.bind_true (bkt_recv pkIdx) fun _ => ?_)
    split <;> [exact bkt_net _; exact BkTraceful.failure]
  | invertKEM pkIdx =>
    change BkNew alice tr ((_root_.DY.Libsignal.PQXDH.invertKEM pkIdx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.invertKEM
    exact BkTraceful.run_start (BkTraceful.bind_true (bkt_guardOn _) fun _ =>
      BkTraceful.bind_true (bkt_recv pkIdx) fun _ =>
      BkTraceful.bind_true (BkTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (fun t =>
        Preserves.monadLiftErr _ (Inv := fun t' => t' = t) t rfl))) fun _ => bkt_net _)

/-- `s` is neither `aliceStart alice ..` nor `bobStart alice ..`. -/
def StepNoStartFor (alice : Participant) (s : Step) : Prop :=
  (∀ b idIdx regB bh, s ≠ .aliceStart alice b idIdx regB bh) ∧
  (∀ a kh regA mh pqIdx spqrIdx, s ≠ .bobStart alice a kh regA mh pqIdx spqrIdx)

/-- `s` is neither an `alice` session start nor an `alice` message decrypt. -/
def StepNoAliceInitOrRecv (alice : Participant) (s : Step) : Prop :=
  StepNoStartFor alice s ∧
  (∀ stateIdx msgIdx pqIdx spqrIdx, s ≠ .messageDecrypt alice stateIdx msgIdx pqIdx spqrIdx) ∧
  (∀ stateIdx msgIdx k pqIdx spqrIdx, s ≠ .messageDecryptSkipped alice stateIdx msgIdx k pqIdx spqrIdx)

theorem stepNoStartFor_of_invisible {alice : Participant} {s : Step} (h : s.cls = .invisible) :
    StepNoStartFor alice s := by
  refine ⟨fun _ _ _ _ heq => ?_, fun _ _ _ _ _ _ heq => ?_⟩ <;> (subst heq; cases h)

theorem stepNoStartFor_of_leak {alice : Participant} {s : Step} (h : s.IsLeak) :
    StepNoStartFor alice s := by
  refine ⟨fun _ _ _ _ heq => ?_, fun _ _ _ _ _ _ heq => ?_⟩ <;> (subst heq; cases h)

theorem stepNoAliceInitOrRecv_of_invisible {alice : Participant} {s : Step} (h : s.cls = .invisible) :
    StepNoAliceInitOrRecv alice s := by
  refine ⟨stepNoStartFor_of_invisible h, fun _ _ _ _ heq => ?_, fun _ _ _ _ _ heq => ?_⟩ <;>
    (subst heq; cases h)

theorem stepNoAliceInitOrRecv_of_leak {alice : Participant} {s : Step} (h : s.IsLeak) :
    StepNoAliceInitOrRecv alice s := by
  refine ⟨stepNoStartFor_of_leak h, fun _ _ _ _ heq => ?_, fun _ _ _ _ _ heq => ?_⟩ <;>
    (subst heq; cases h)

private theorem noNewHs_append_non_cEv {E : Type} [ExecTraceTypes.Has E]
    {alice : Participant} {n₀ : Nat} {tr : ExecTrace} (e : E)
    (hnone : (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CEntry) = none)
    (h : NoNewHsFrom alice n₀ tr) : NoNewHsFrom alice n₀ (tr.append e) := by
  have hle := Trace.append_le tr e
  refine ⟨Nat.le_trans h.1 (Trace.length_le _ _ hle), fun m hm_ge hm_lt s d hev => ?_⟩
  by_cases hm : m < tr.length
  · rw [bks_getEventAt_of_le ComposedEvent hle hm] at hev
    exact h.2 m hm_ge hm s d hev
  · have heq : m = tr.length := by simp only [Trace.append, Trace.length] at hm_lt; omega
    subst heq; unfold Trace.getEventAt at hev
    have hat : ((tr.append e).at? tr.length : Option CEntry) =
        (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option CEntry) := by
      simp [Trace.at?, Trace.append, Trace.at, Trace.length]
    rw [hat, hnone] at hev; cases hev

private theorem noNewHs_append_hs {alice : Participant} {n₀ : Nat} {tr : ExecTrace}
    {s : SessionInfo} {d : Nat} (hne : s.me ≠ alice)
    (h : NoNewHsFrom alice n₀ tr) :
    NoNewHsFrom alice n₀ (tr.append (CEvE (.HandshakeSession s d))) := by
  set e := CEvE (.HandshakeSession s d)
  have hle := Trace.append_le tr e
  refine ⟨Nat.le_trans h.1 (Trace.length_le _ _ hle), fun m hm_ge hm_lt s' d' hev => ?_⟩
  by_cases hm : m < tr.length
  · rw [bks_getEventAt_of_le ComposedEvent hle hm] at hev
    exact h.2 m hm_ge hm s' d' hev
  · have heq : m = tr.length := by simp only [Trace.append, Trace.length] at hm_lt; omega
    subst heq; unfold Trace.getEventAt at hev
    rw [Trace.at?_append tr e] at hev
    injection hev with heq_ev; cases heq_ev; exact hne

private theorem noNewRecvMK_append_non_tr {E : Type} [ExecTraceTypes.Has E]
    {alice : Participant} {n₀ : Nat} {tr : ExecTrace} (e : E)
    (hnone : (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) = none)
    (h : NoNewRecvMKFrom alice n₀ tr) : NoNewRecvMKFrom alice n₀ (tr.append e) := by
  have hle := Trace.append_le tr e
  refine ⟨Nat.le_trans h.1 (Trace.length_le _ _ hle),
    fun m hm_ge hm_lt s seed salt n rIdx par hev => ?_⟩
  by_cases hm : m < tr.length
  · rw [bks_getEventAt_of_le TREvent hle hm] at hev
    exact h.2 m hm_ge hm s seed salt n rIdx par hev
  · have heq : m = tr.length := by simp only [Trace.append, Trace.length] at hm_lt; omega
    subst heq; unfold Trace.getEventAt at hev
    have hat : ((tr.append e).at? tr.length : Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) =
        (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) := by
      simp [Trace.at?, Trace.append, Trace.at, Trace.length]
    rw [hat, hnone] at hev; cases hev

private theorem noNewRecvMK_append_tr {alice : Participant} {n₀ : Nat} {tr : ExecTrace}
    (ev : TREvent)
    (hnot : ∀ s seed salt n rIdx par,
      ev = .MessageKey s .receiver seed salt n rIdx par → s.me ≠ alice)
    (h : NoNewRecvMKFrom alice n₀ tr) :
    NoNewRecvMKFrom alice n₀ (tr.append (⟨ev⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent)) := by
  set e : _root_.DY.ProtocolEvent.ExecEntryT TREvent := ⟨ev⟩
  have hle := Trace.append_le tr e
  refine ⟨Nat.le_trans h.1 (Trace.length_le _ _ hle),
    fun m hm_ge hm_lt s seed salt n rIdx par hev => ?_⟩
  by_cases hm : m < tr.length
  · rw [bks_getEventAt_of_le TREvent hle hm] at hev
    exact h.2 m hm_ge hm s seed salt n rIdx par hev
  · have heq : m = tr.length := by simp only [Trace.append, Trace.length] at hm_lt; omega
    subst heq; unfold Trace.getEventAt at hev
    rw [Trace.at?_append tr e] at hev
    injection hev with hev_eq
    exact hnot s seed salt n rIdx par hev_eq

private theorem pres_noHs_getKey {alice : Participant} {n₀ : Nat} (p : Participant) (idx : Nat)
    (k : _root_.DY.Libsignal.PQXDH.KeyKind) :
    Preserves (NoNewHsFrom alice n₀) (_root_.DY.Libsignal.PQXDH.getKey p idx k) := by
  unfold _root_.DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p idx) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem pres_noHs_logSkipped {alice : Participant} {n₀ : Nat}
    (s : SessionInfo) (pk : _root_.DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : _root_.DY.Bytes) (n : UInt32),
      Preserves (NoNewHsFrom alice n₀) (_root_.DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k)
  | 0, _, _ => Preserves.pure _
  | k + 1, ck, n => by
    rw [_root_.DY.Libsignal.TripleRatchet.logSkippedKeys]
    exact Preserves.bind (fun _ h => noNewHs_append_non_cEv (⟨_⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent) rfl h)
      fun _ => pres_noHs_logSkipped s pk rIdx src k _ _

private theorem pres_noHs_logMKStore {alice : Participant} {n₀ : Nat}
    (me : Participant) (s : SessionInfo) (dir : _root_.DY.Libsignal.TripleRatchet.KeyDir)
    (seed salt : _root_.DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState) :
    Preserves (NoNewHsFrom alice n₀)
      (_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed salt n rIdx par st) := by
  unfold _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact Preserves.bind (fun _ h => noNewHs_append_non_cEv (⟨_⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent) rfl h)
    fun _ _ h => noNewHs_append_non_cEv (⟨⟨me, st⟩⟩ : TRStEntry) rfl h

private theorem pres_noHs_ensureRC {alice : Participant} {n₀ : Nat}
    (st : TRState) (pk : _root_.DY.Bytes) :
    Preserves (NoNewHsFrom alice n₀) (_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  rcases _root_.DY.Libsignal.TripleRatchet.recvChainFor st.toDRState pk with _ | ⟨c, _ | _⟩
  · exact Preserves.failure
  · exact Preserves.pure _
  · simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
    exact Preserves.bind (Preserves.bind (Preserves.guardP _) fun _ =>
      Preserves.bind (fun _ h => noNewHs_append_non_cEv (RndE 32) rfl h) fun _ => Preserves.pure _)
      fun _ => Preserves.pure _

theorem noNewHs_step {alice : Participant} {n₀ : Nat} {tr : ExecTrace} {s : Step}
    (hno : StepNoStartFor alice s) (hInv : NoNewHsFrom alice n₀ tr) :
    NoNewHsFrom alice n₀ (s.next tr) := by
  have rnd (n : Nat) : Preserves (NoNewHsFrom alice n₀) (_root_.DY.Random.genRand n) :=
    fun _ h => noNewHs_append_non_cEv (RndE n) rfl h
  have net (m : _root_.DY.Bytes) : Preserves (NoNewHsFrom alice n₀) (_root_.DY.Network.sendMessage m) :=
    fun _ h => noNewHs_append_non_cEv (NetE m) rfl h
  have lpq (ev : PQXDHEvent) : Preserves (NoNewHsFrom alice n₀) (_root_.DY.ProtocolEvent.logEvent ev) :=
    fun _ h => noNewHs_append_non_cEv (⟨ev⟩ : PQXDHEntry) rfl h
  have ltr (ev : TREvent) : Preserves (NoNewHsFrom alice n₀) (_root_.DY.ProtocolEvent.logEvent ev) :=
    fun _ h => noNewHs_append_non_cEv (⟨ev⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent) rfl h
  have spq (p : Participant) (st : PQXDHState) :
      Preserves (NoNewHsFrom alice n₀) (_root_.DY.PersistentLocalState.storeLocalState p st) :=
    fun _ h => noNewHs_append_non_cEv
      (⟨⟨p, st⟩⟩ : _root_.DY.PersistentGlobalState.State.ExecEntryT (_root_.DY.PersistentLocalState.LocalState PQXDHState)) rfl h
  cases s with
  | network msg => exact noNewHs_append_non_cEv (NetE msg) rfl hInv
  | registerIdentity p =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.registerIdentity p).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.registerIdentity
    exact (Preserves.bind (Preserves.requireTracePredicate _) fun _ => Preserves.bind (rnd 32) fun _ =>
      Preserves.bind (lpq _) fun _ => Preserves.bind (net _) fun _ => Preserves.bind (net _) fun _ => spq p _) tr hInv
  | registerCorruptIdentity p skIdx =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.registerCorruptIdentity p skIdx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.registerCorruptIdentity
    exact (Preserves.bind (Preserves.requireTracePredicate _) fun _ => Preserves.bind (Preserves.receiveMessage skIdx) fun _ =>
      Preserves.bind (lpq _) fun _ => lpq _) tr hInv
  | genSignedPrekey b idx =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.genSignedPrekey b idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.genSignedPrekey
    exact (Preserves.bind (pres_noHs_getKey b idx .identity) fun _ => Preserves.bind (rnd 32) fun _ =>
      Preserves.bind (rnd 64) fun _ => Preserves.bind (lpq _) fun _ => Preserves.bind (spq b _) fun _ =>
      Preserves.bind (net _) fun _ => Preserves.bind (net _) fun _ => Preserves.pure _) tr hInv
  | genPQPrekey b idx =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.genPQPrekey b idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.genPQPrekey
    exact (Preserves.bind (pres_noHs_getKey b idx .identity) fun _ => Preserves.bind (rnd 64) fun _ =>
      Preserves.bind (rnd 64) fun _ => Preserves.bind (lpq _) fun _ => Preserves.bind (spq b _) fun _ =>
      Preserves.bind (net _) fun _ => Preserves.bind (net _) fun _ => Preserves.pure _) tr hInv
  | genOneTimePrekey b =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.genOneTimePrekey b).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.genOneTimePrekey
    exact (Preserves.bind (rnd 32) fun _ => Preserves.bind (lpq _) fun _ => Preserves.bind (spq b _) fun _ =>
      Preserves.bind (net _) fun _ => Preserves.pure _) tr hInv
  | aliceStart a b idIdx regB bh =>
    have ha : a ≠ alice := fun heq => hno.1 b idIdx regB bh (by subst heq; rfl)
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.Composed.aliceStart a b idIdx regB bh).run tr).2.val
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.aliceStart_eq_inline]
    refine bind_aliceHandshake_at a b idIdx regB bh tr hInv (noNewHs_append_non_cEv (RndE 32) rfl hInv) ?_
    intro ikA ikB _ spk _ pqpk _ opk _ _ _ _ _ _ _ _ _ _ _ _
    set o := aliceOut tr ikA ikB spk pqpk opk
    change NoNewHsFrom alice n₀ (iniAliceStartTr tr a b o); unfold iniAliceStartTr; dsimp only
    exact noNewHs_append_non_cEv (⟨⟨a, iniAliceStartState tr b o⟩⟩ : TRStEntry) rfl
      (noNewHs_append_hs ha
      (noNewHs_append_non_cEv (⟨.InitSession a b (dhPk (randTerm (tr.length + 2) 32)) o.spk⟩ :
        _root_.DY.ProtocolEvent.ExecEntryT TREvent) rfl
      (noNewHs_append_non_cEv (⟨.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys⟩ : PQXDHEntry) rfl
      (noNewHs_append_non_cEv (NetE o.ct) rfl (noNewHs_append_non_cEv (NetE o.ek) rfl
      (noNewHs_append_non_cEv (RndE 32) rfl (noNewHs_append_non_cEv (RndE 32) rfl
      (noNewHs_append_non_cEv (RndE 32) rfl hInv))))))))
  | bobStart b a kh regA mh pqIdx spqrIdx =>
    have hb : b ≠ alice := fun heq => hno.2 a kh regA mh pqIdx spqrIdx (by subst heq; rfl)
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqrIdx).run tr).2.val
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.bobStart_eq_inline]
    refine bind_bobHandshake_at b a kh regA mh.ek mh.ct tr hInv ?_
    intro ikBSk spkSk pqsk opkSk ikA _ ek ct _ keys _ _ _ _ _ _ _ _ _
    refine (Preserves.bind (Preserves.receiveSignalMsg mh.msg) fun msg =>
      Preserves.bind (pres_noHs_ensureRC _ msg.ratchetKey) fun ⟨st, c, ratcheted⟩ => ?_) tr hInv
    dsimp only; split
    · next seed c' _ =>
      split
      · next spqr' key _ =>
        refine Preserves.bind (net key) fun _ => Preserves.bind (Preserves.receiveMessage pqIdx) fun pqSalt =>
          Preserves.bind (Preserves.verifyMacAndDecrypt st msg pqSalt seed) fun ptTerm => ?_
        (cases opkSk.map dhPk <;> try dsimp only)
        swap
        refine Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
          Preserves.bind (lpq _) fun _ => ?_
        all_goals
          refine Preserves.bind Preserves.traceLength fun doneIdx =>
            Preserves.bind (lpq _) fun _ => ?_
          try dsimp only
          cases ratcheted
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact Preserves.bind (fun _ h => noNewHs_append_hs hb h) fun _ =>
              Preserves.bind Preserves.traceLength fun _ =>
              Preserves.bind (pres_noHs_logSkipped _ _ _ _ _ _ _) fun _ =>
              Preserves.bind (ltr _) fun _ => pres_noHs_logMKStore b _ _ _ _ _ _ _ _
          · simp only [↓reduceIte]
            exact Preserves.bind (ltr _) fun _ =>
              Preserves.bind (ltr _) fun _ =>
              Preserves.bind (fun _ h => noNewHs_append_hs hb h) fun _ =>
              Preserves.bind Preserves.traceLength fun _ =>
              Preserves.bind (pres_noHs_logSkipped _ _ _ _ _ _ _) fun _ =>
              Preserves.bind (ltr _) fun _ => pres_noHs_logMKStore b _ _ _ _ _ _ _ _
      · exact Preserves.failure
    · exact Preserves.failure
  | messageEncrypt me stH coinsLen pqIdx =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.messageEncrypt
    exact (Preserves.bind (Preserves.getLocalState_tr me stH) fun _ => Preserves.bind (Preserves.guardP _) fun _ =>
      Preserves.bind (rnd 32) fun _ => Preserves.bind (rnd coinsLen) fun _ => Preserves.bind (net _) fun _ =>
      Preserves.bind (Preserves.receiveMessage pqIdx) fun _ => Preserves.bind (ltr _) fun _ =>
      Preserves.bind (pres_noHs_logMKStore me _ _ _ _ _ _ _ _) fun _ => net _) tr hInv
  | messageEncryptAbort me stH =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.messageEncryptAbort me stH).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.messageEncryptAbort
    exact (Preserves.bind (Preserves.getLocalState_tr me stH) fun _ =>
      Preserves.bind (rnd 32) fun _ => Preserves.failure) tr hInv
  | messageDecrypt me stH msgH pqIdx spqrIdx =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrIdx).run tr).2.val
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
    refine (Preserves.bind (Preserves.getLocalState_tr me stH) fun st =>
      Preserves.bind (Preserves.receiveSignalMsg msgH) fun msg =>
      Preserves.bind (pres_noHs_ensureRC st msg.ratchetKey) fun _ => ?_) tr hInv
    dsimp only; split
    · split
      · refine Preserves.bind (net _) fun _ => Preserves.bind (Preserves.receiveMessage _) fun _ =>
          Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
        split
        · exact Preserves.bind (ltr _) fun _ => Preserves.bind (ltr _) fun _ =>
            Preserves.bind (pres_noHs_logSkipped _ _ _ _ _ _ _) fun _ =>
            Preserves.bind (ltr _) fun _ => pres_noHs_logMKStore me _ _ _ _ _ _ _ _
        · exact Preserves.bind (pres_noHs_logSkipped _ _ _ _ _ _ _) fun _ =>
            Preserves.bind (ltr _) fun _ => pres_noHs_logMKStore me _ _ _ _ _ _ _ _
      · exact Preserves.failure
    · exact Preserves.failure
  | messageDecryptSkipped me stH msgH evH pqIdx spqrIdx =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrIdx).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
    refine (Preserves.bind (Preserves.getLocalState_tr me stH) fun _ =>
      Preserves.bind (Preserves.receiveSignalMsg msgH) fun _ =>
      Preserves.bind (Preserves.getEntry evH) fun _ => ?_) tr hInv
    split
    · refine Preserves.bind (Preserves.guardP _) fun _ => Preserves.bind (Preserves.guardTrace _) fun _ => ?_
      split
      · exact Preserves.bind (net _) fun _ => Preserves.bind (Preserves.receiveMessage _) fun _ =>
          Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun _ =>
          Preserves.bind (ltr _) fun _ => Preserves.bind (ltr _) fun _ =>
          pres_noHs_logMKStore me _ _ _ _ _ _ _ _
      · exact Preserves.failure
    · exact Preserves.failure
  | exposeKey me stH comp =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.exposeKey me stH comp).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.exposeKey
    refine (Preserves.bind (Preserves.getLocalState_tr me stH) fun _ => ?_) tr hInv
    cases comp with
    | rk | dhs | cks => exact Preserves.bind (ltr _) fun _ => net _
    | ckr _ => dsimp only; split <;> [exact Preserves.bind (ltr _) fun _ => net _; exact Preserves.failure]
  | exposeSpqr me stH =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.exposeSpqr me stH).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.exposeSpqr
    exact (Preserves.bind (Preserves.getLocalState_tr me stH) fun _ =>
      Preserves.bind (ltr _) fun _ => net _) tr hInv
  | exposeSkipped evH =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.exposeSkipped evH).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.exposeSkipped
    refine (Preserves.bind (Preserves.getEntry evH) fun _ => ?_) tr hInv
    split <;> [exact Preserves.bind (Preserves.guardTrace _) fun _ => Preserves.bind (ltr _) fun _ => net _;
      exact Preserves.failure]
  | compromiseIK p idx =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.compromiseIK p idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.compromiseIK
    exact (Preserves.bind (pres_noHs_getKey p idx .identity) fun _ => Preserves.bind (lpq _) fun _ => net _) tr hInv
  | compromiseSPK b idx =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.compromiseSPK b idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.compromiseSPK
    exact (Preserves.bind (pres_noHs_getKey b idx .signedPrekey) fun _ => Preserves.bind (lpq _) fun _ => net _) tr hInv
  | compromisePQSPK b idx =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.compromisePQSPK b idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.compromisePQSPK
    exact (Preserves.bind (pres_noHs_getKey b idx .pqPrekey) fun _ => Preserves.bind (lpq _) fun _ => net _) tr hInv
  | compromiseOPK b idx =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.compromiseOPK b idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.compromiseOPK
    exact (Preserves.bind (pres_noHs_getKey b idx .oneTimePrekey) fun _ =>
      Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
      Preserves.bind (lpq _) fun _ => net _) tr hInv
  | breakDH =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.breakDH).run tr).2.val
    exact lpq _ tr hInv
  | breakKEM =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.breakKEM).run tr).2.val
    exact lpq _ tr hInv
  | invertDH pkIdx =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.invertDH pkIdx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.invertDH
    refine (Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
      Preserves.bind (Preserves.receiveMessage pkIdx) fun _ => ?_) tr hInv
    split <;> [exact net _; exact Preserves.failure]
  | invertKEM pkIdx =>
    change NoNewHsFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.invertKEM pkIdx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.invertKEM
    exact (Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
      Preserves.bind (Preserves.receiveMessage pkIdx) fun _ =>
      Preserves.bind (Preserves.monadLiftErr _) fun _ => net _) tr hInv

private theorem pres_noRecv_getKey {alice : Participant} {n₀ : Nat} (p : Participant) (idx : Nat)
    (k : _root_.DY.Libsignal.PQXDH.KeyKind) :
    Preserves (NoNewRecvMKFrom alice n₀) (_root_.DY.Libsignal.PQXDH.getKey p idx k) := by
  unfold _root_.DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p idx) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem pres_noRecv_logSkipped {alice : Participant} {n₀ : Nat}
    (s : SessionInfo) (pk : _root_.DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : _root_.DY.Bytes) (n : UInt32),
      Preserves (NoNewRecvMKFrom alice n₀) (_root_.DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k)
  | 0, _, _ => Preserves.pure _
  | k + 1, ck, n => by
    rw [_root_.DY.Libsignal.TripleRatchet.logSkippedKeys]
    exact Preserves.bind (fun _ h => noNewRecvMK_append_tr _ (by intro _ _ _ _ _ _ hc; cases hc) h)
      fun _ => pres_noRecv_logSkipped s pk rIdx src k _ _

private theorem pres_noRecv_logMKStore {alice : Participant} {n₀ : Nat}
    (me : Participant) (s : SessionInfo) (dir : _root_.DY.Libsignal.TripleRatchet.KeyDir)
    (seed salt : _root_.DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState)
    (hdir : dir = .receiver → s.me ≠ alice) :
    Preserves (NoNewRecvMKFrom alice n₀)
      (_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed salt n rIdx par st) := by
  unfold _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine Preserves.bind (fun _ h => noNewRecvMK_append_tr _ ?_ h)
    fun _ _ h => noNewRecvMK_append_non_tr (⟨⟨me, st⟩⟩ : TRStEntry) rfl h
  intro s' _ _ _ _ _ heq
  injection heq with hs hd; subst hs hd
  exact hdir rfl

private theorem pres_noRecv_ensureRC {alice : Participant} {n₀ : Nat}
    (st : TRState) (pk : _root_.DY.Bytes) :
    Preserves (NoNewRecvMKFrom alice n₀) (_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  rcases _root_.DY.Libsignal.TripleRatchet.recvChainFor st.toDRState pk with _ | ⟨c, _ | _⟩
  · exact Preserves.failure
  · exact Preserves.pure _
  · simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
    exact Preserves.bind (Preserves.bind (Preserves.guardP _) fun _ =>
      Preserves.bind (fun _ h => noNewRecvMK_append_non_tr (RndE 32) rfl h) fun _ => Preserves.pure _)
      fun _ => Preserves.pure _

private theorem pres_noRecv_logTR_non {alice : Participant} {n₀ : Nat} (ev : TREvent)
    (hn : ∀ s seed salt n rIdx par,
      ev ≠ .MessageKey s .receiver seed salt n rIdx par := by intros; intro h; cases h) :
    Preserves (NoNewRecvMKFrom alice n₀) (_root_.DY.ProtocolEvent.logEvent ev) :=
  fun _ h => noNewRecvMK_append_tr ev (fun s seed salt n rIdx par heq =>
    (hn s seed salt n rIdx par heq).elim) h

theorem noNewRecvMK_step {alice : Participant} {n₀ : Nat} {tr : ExecTrace} {s : Step}
    (hno : StepNoAliceInitOrRecv alice s) (hInv : NoNewRecvMKFrom alice n₀ tr) :
    NoNewRecvMKFrom alice n₀ (s.next tr) := by
  have rnd (n : Nat) : Preserves (NoNewRecvMKFrom alice n₀) (_root_.DY.Random.genRand n) :=
    fun _ h => noNewRecvMK_append_non_tr (RndE n) rfl h
  have net (m : _root_.DY.Bytes) : Preserves (NoNewRecvMKFrom alice n₀) (_root_.DY.Network.sendMessage m) :=
    fun _ h => noNewRecvMK_append_non_tr (NetE m) rfl h
  have lpq (ev : PQXDHEvent) : Preserves (NoNewRecvMKFrom alice n₀) (_root_.DY.ProtocolEvent.logEvent ev) :=
    fun _ h => noNewRecvMK_append_non_tr (⟨ev⟩ : PQXDHEntry) rfl h
  have spq (p : Participant) (st : PQXDHState) :
      Preserves (NoNewRecvMKFrom alice n₀) (_root_.DY.PersistentLocalState.storeLocalState p st) :=
    fun _ h => noNewRecvMK_append_non_tr
      (⟨⟨p, st⟩⟩ : _root_.DY.PersistentGlobalState.State.ExecEntryT (_root_.DY.PersistentLocalState.LocalState PQXDHState)) rfl h
  cases s with
  | network msg => exact noNewRecvMK_append_non_tr (NetE msg) rfl hInv
  | registerIdentity p =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.registerIdentity p).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.registerIdentity
    exact (Preserves.bind (Preserves.requireTracePredicate _) fun _ => Preserves.bind (rnd 32) fun _ =>
      Preserves.bind (lpq _) fun _ => Preserves.bind (net _) fun _ => Preserves.bind (net _) fun _ => spq p _) tr hInv
  | registerCorruptIdentity p skIdx =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.registerCorruptIdentity p skIdx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.registerCorruptIdentity
    exact (Preserves.bind (Preserves.requireTracePredicate _) fun _ => Preserves.bind (Preserves.receiveMessage skIdx) fun _ =>
      Preserves.bind (lpq _) fun _ => lpq _) tr hInv
  | genSignedPrekey b idx =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.genSignedPrekey b idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.genSignedPrekey
    exact (Preserves.bind (pres_noRecv_getKey b idx .identity) fun _ => Preserves.bind (rnd 32) fun _ =>
      Preserves.bind (rnd 64) fun _ => Preserves.bind (lpq _) fun _ => Preserves.bind (spq b _) fun _ =>
      Preserves.bind (net _) fun _ => Preserves.bind (net _) fun _ => Preserves.pure _) tr hInv
  | genPQPrekey b idx =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.genPQPrekey b idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.genPQPrekey
    exact (Preserves.bind (pres_noRecv_getKey b idx .identity) fun _ => Preserves.bind (rnd 64) fun _ =>
      Preserves.bind (rnd 64) fun _ => Preserves.bind (lpq _) fun _ => Preserves.bind (spq b _) fun _ =>
      Preserves.bind (net _) fun _ => Preserves.bind (net _) fun _ => Preserves.pure _) tr hInv
  | genOneTimePrekey b =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.genOneTimePrekey b).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.genOneTimePrekey
    exact (Preserves.bind (rnd 32) fun _ => Preserves.bind (lpq _) fun _ => Preserves.bind (spq b _) fun _ =>
      Preserves.bind (net _) fun _ => Preserves.pure _) tr hInv
  | aliceStart a b idIdx regB bh =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.Composed.aliceStart a b idIdx regB bh).run tr).2.val
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.aliceStart_eq_inline]
    refine bind_aliceHandshake_at a b idIdx regB bh tr hInv (noNewRecvMK_append_non_tr (RndE 32) rfl hInv) ?_
    intro ikA ikB _ spk _ pqpk _ opk _ _ _ _ _ _ _ _ _ _ _ _
    set o := aliceOut tr ikA ikB spk pqpk opk
    change NoNewRecvMKFrom alice n₀ (iniAliceStartTr tr a b o); unfold iniAliceStartTr; dsimp only
    exact noNewRecvMK_append_non_tr (⟨⟨a, iniAliceStartState tr b o⟩⟩ : TRStEntry) rfl
      (noNewRecvMK_append_non_tr (CEvE (.HandshakeSession _ _)) rfl
      (noNewRecvMK_append_tr (.InitSession a b (dhPk (randTerm (tr.length + 2) 32)) o.spk) (by intro _ _ _ _ _ _ hc; cases hc)
      (noNewRecvMK_append_non_tr (⟨.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys⟩ : PQXDHEntry) rfl
      (noNewRecvMK_append_non_tr (NetE o.ct) rfl (noNewRecvMK_append_non_tr (NetE o.ek) rfl
      (noNewRecvMK_append_non_tr (RndE 32) rfl (noNewRecvMK_append_non_tr (RndE 32) rfl
      (noNewRecvMK_append_non_tr (RndE 32) rfl hInv))))))))
  | bobStart b a kh regA mh pqIdx spqrIdx =>
    have hb : b ≠ alice := fun heq => hno.1.2 a kh regA mh pqIdx spqrIdx (by subst heq; rfl)
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqrIdx).run tr).2.val
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.bobStart_eq_inline]
    refine bind_bobHandshake_at b a kh regA mh.ek mh.ct tr hInv ?_
    intro ikBSk spkSk pqsk opkSk ikA _ ek ct _ keys _ _ _ _ _ _ _ _ _
    refine (Preserves.bind (Preserves.receiveSignalMsg mh.msg) fun msg =>
      Preserves.bind (pres_noRecv_ensureRC _ msg.ratchetKey) fun ⟨st, c, ratcheted⟩ => ?_) tr hInv
    dsimp only; split
    · next seed c' _ =>
      split
      · next spqr' key _ =>
        refine Preserves.bind (net key) fun _ => Preserves.bind (Preserves.receiveMessage pqIdx) fun pqSalt =>
          Preserves.bind (Preserves.verifyMacAndDecrypt st msg pqSalt seed) fun ptTerm => ?_
        (cases opkSk.map dhPk <;> try dsimp only)
        swap
        refine Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
          Preserves.bind (lpq _) fun _ => ?_
        all_goals
          refine Preserves.bind Preserves.traceLength fun doneIdx =>
            Preserves.bind (lpq _) fun _ => ?_
          try dsimp only
          cases ratcheted
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact Preserves.bind (fun _ h => noNewRecvMK_append_non_tr (CEvE _) rfl h) fun _ =>
              Preserves.bind Preserves.traceLength fun _ =>
              Preserves.bind (pres_noRecv_logSkipped _ _ _ _ _ _ _) fun _ =>
              Preserves.bind (pres_noRecv_logTR_non _) fun _ =>
              pres_noRecv_logMKStore b _ _ _ _ _ _ _ _ (fun _ => hb)
          · simp only [↓reduceIte]
            exact Preserves.bind (pres_noRecv_logTR_non _) fun _ =>
              Preserves.bind (pres_noRecv_logTR_non _) fun _ =>
              Preserves.bind (fun _ h => noNewRecvMK_append_non_tr (CEvE _) rfl h) fun _ =>
              Preserves.bind Preserves.traceLength fun _ =>
              Preserves.bind (pres_noRecv_logSkipped _ _ _ _ _ _ _) fun _ =>
              Preserves.bind (pres_noRecv_logTR_non _) fun _ =>
              pres_noRecv_logMKStore b _ _ _ _ _ _ _ _ (fun _ => hb)
      · exact Preserves.failure
    · exact Preserves.failure
  | messageEncrypt me stH coinsLen pqIdx =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.messageEncrypt
    exact (Preserves.bind (Preserves.getLocalState_tr me stH) fun _ => Preserves.bind (Preserves.guardP _) fun _ =>
      Preserves.bind (rnd 32) fun _ => Preserves.bind (rnd coinsLen) fun _ => Preserves.bind (net _) fun _ =>
      Preserves.bind (Preserves.receiveMessage pqIdx) fun _ =>
      Preserves.bind (pres_noRecv_logTR_non _) fun _ =>
      Preserves.bind (pres_noRecv_logMKStore me _ _ _ _ _ _ _ _ (by intro hd; cases hd)) fun _ => net _) tr hInv
  | messageEncryptAbort me stH =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.messageEncryptAbort me stH).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.messageEncryptAbort
    exact (Preserves.bind (Preserves.getLocalState_tr me stH) fun _ =>
      Preserves.bind (rnd 32) fun _ => Preserves.failure) tr hInv
  | messageDecrypt me stH msgH pqIdx spqrIdx =>
    have hme : me ≠ alice := fun heq => hno.2.1 stH msgH pqIdx spqrIdx (by subst heq; rfl)
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrIdx).run tr).2.val
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
    refine (Preserves.bind (Preserves.getLocalState_tr me stH) fun st =>
      Preserves.bind (Preserves.receiveSignalMsg msgH) fun msg =>
      Preserves.bind (pres_noRecv_ensureRC st msg.ratchetKey) fun _ => ?_) tr hInv
    dsimp only; split
    · split
      · refine Preserves.bind (net _) fun _ => Preserves.bind (Preserves.receiveMessage _) fun _ =>
          Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
        split
        · exact Preserves.bind (pres_noRecv_logTR_non _) fun _ =>
            Preserves.bind (pres_noRecv_logTR_non _) fun _ =>
            Preserves.bind (pres_noRecv_logSkipped _ _ _ _ _ _ _) fun _ =>
            Preserves.bind (pres_noRecv_logTR_non _) fun _ =>
            pres_noRecv_logMKStore me _ _ _ _ _ _ _ _ (fun _ => hme)
        · exact Preserves.bind (pres_noRecv_logSkipped _ _ _ _ _ _ _) fun _ =>
            Preserves.bind (pres_noRecv_logTR_non _) fun _ =>
            pres_noRecv_logMKStore me _ _ _ _ _ _ _ _ (fun _ => hme)
      · exact Preserves.failure
    · exact Preserves.failure
  | messageDecryptSkipped me stH msgH evH pqIdx spqrIdx =>
    have hme : me ≠ alice := fun heq => hno.2.2 stH msgH evH pqIdx spqrIdx (by subst heq; rfl)
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrIdx).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
    refine (Preserves.bind (Preserves.getLocalState_tr me stH) fun _ =>
      Preserves.bind (Preserves.receiveSignalMsg msgH) fun _ =>
      Preserves.bind (Preserves.getEntry evH) fun _ => ?_) tr hInv
    split
    · refine bind_guard_preserves _ fun hg => ?_
      rcases hg with ⟨rfl, _, _⟩
      refine Preserves.bind (Preserves.guardTrace _) fun _ => ?_
      split
      · exact Preserves.bind (net _) fun _ => Preserves.bind (Preserves.receiveMessage _) fun _ =>
          Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun _ =>
          Preserves.bind (pres_noRecv_logTR_non _) fun _ =>
          Preserves.bind (pres_noRecv_logTR_non _) fun _ =>
          pres_noRecv_logMKStore me _ _ _ _ _ _ _ _ (fun _ => hme)
      · exact Preserves.failure
    · exact Preserves.failure
  | exposeKey me stH comp =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.exposeKey me stH comp).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.exposeKey
    refine (Preserves.bind (Preserves.getLocalState_tr me stH) fun _ => ?_) tr hInv
    cases comp with
    | rk | dhs | cks =>
      exact Preserves.bind (pres_noRecv_logTR_non _) fun _ => net _
    | ckr _ =>
      dsimp only; split
      · exact Preserves.bind (pres_noRecv_logTR_non _) fun _ => net _
      · exact Preserves.failure
  | exposeSpqr me stH =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.exposeSpqr me stH).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.exposeSpqr
    exact (Preserves.bind (Preserves.getLocalState_tr me stH) fun _ =>
      Preserves.bind (pres_noRecv_logTR_non _) fun _ => net _) tr hInv
  | exposeSkipped evH =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.TripleRatchet.exposeSkipped evH).run tr).2.val
    unfold _root_.DY.Libsignal.TripleRatchet.exposeSkipped
    refine (Preserves.bind (Preserves.getEntry evH) fun _ => ?_) tr hInv
    split
    · exact Preserves.bind (Preserves.guardTrace _) fun _ =>
        Preserves.bind (pres_noRecv_logTR_non _) fun _ => net _
    · exact Preserves.failure
  | compromiseIK p idx =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.compromiseIK p idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.compromiseIK
    exact (Preserves.bind (pres_noRecv_getKey p idx .identity) fun _ => Preserves.bind (lpq _) fun _ => net _) tr hInv
  | compromiseSPK b idx =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.compromiseSPK b idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.compromiseSPK
    exact (Preserves.bind (pres_noRecv_getKey b idx .signedPrekey) fun _ => Preserves.bind (lpq _) fun _ => net _) tr hInv
  | compromisePQSPK b idx =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.compromisePQSPK b idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.compromisePQSPK
    exact (Preserves.bind (pres_noRecv_getKey b idx .pqPrekey) fun _ => Preserves.bind (lpq _) fun _ => net _) tr hInv
  | compromiseOPK b idx =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.compromiseOPK b idx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.compromiseOPK
    exact (Preserves.bind (pres_noRecv_getKey b idx .oneTimePrekey) fun _ =>
      Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
      Preserves.bind (lpq _) fun _ => net _) tr hInv
  | breakDH =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.breakDH).run tr).2.val
    exact lpq _ tr hInv
  | breakKEM =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.breakKEM).run tr).2.val
    exact lpq _ tr hInv
  | invertDH pkIdx =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.invertDH pkIdx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.invertDH
    refine (Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
      Preserves.bind (Preserves.receiveMessage pkIdx) fun _ => ?_) tr hInv
    split <;> [exact net _; exact Preserves.failure]
  | invertKEM pkIdx =>
    change NoNewRecvMKFrom alice n₀ ((_root_.DY.Libsignal.PQXDH.invertKEM pkIdx).run tr).2.val
    unfold _root_.DY.Libsignal.PQXDH.invertKEM
    exact (Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
      Preserves.bind (Preserves.receiveMessage pkIdx) fun _ =>
      Preserves.bind (Preserves.monadLiftErr _) fun _ => net _) tr hInv

theorem noNewHs_runSteps {alice : Participant} {n₀ : Nat} :
    ∀ (ss : List Step) {tr : ExecTrace},
      NoNewHsFrom alice n₀ tr →
      (∀ s ∈ ss, StepNoStartFor alice s) →
      NoNewHsFrom alice n₀ (runSteps ss tr)
  | [], _, h, _ => h
  | s :: ss, _, h, hno =>
    noNewHs_runSteps ss (noNewHs_step (hno s List.mem_cons_self) h)
      (fun s' hs' => hno s' (List.mem_cons_of_mem s hs'))

theorem noNewRecvMK_runSteps {alice : Participant} {n₀ : Nat} :
    ∀ (ss : List Step) {tr : ExecTrace},
      NoNewRecvMKFrom alice n₀ tr →
      (∀ s ∈ ss, StepNoAliceInitOrRecv alice s) →
      NoNewRecvMKFrom alice n₀ (runSteps ss tr)
  | [], _, h, _ => h
  | s :: ss, _, h, hno =>
    noNewRecvMK_runSteps ss (noNewRecvMK_step (hno s List.mem_cons_self) h)
      (fun s' hs' => hno s' (List.mem_cons_of_mem s hs'))

theorem newBobSinfo_step_ua {alice : Participant} {tr : ExecTrace} {s : Step}
    (hReach : tr.Reachable reachability) (hpre : s.PreCond tr) (hno : StepNoStartFor alice s) :
    NewBobSinfo alice tr (s.next tr) := by
  have hReach' : (s.next tr).Reachable reachability := Trace.Reachable.Step s.toInput hpre hReach
  exact newBobSinfo_of_bkNew ((reachability.step s.toInput).2.run tr).2.property
    (Symbolic.Swarm.CREF.TR.messageKeyCurrentInv_reachable hReach')
    (bkNew_step hno.1 hno.2)

theorem newBobSinfo_runSteps_ua {alice : Participant} :
    ∀ (ss : List Step) {tr : ExecTrace},
      tr.Reachable reachability →
      StepsWF ss tr →
      (∀ s ∈ ss, StepNoStartFor alice s) →
      NewBobSinfo alice tr (runSteps ss tr)
  | [], tr, _, _, _ => newBobSinfo_refl alice tr
  | s :: ss, tr, hReach, ⟨hpre, _, hwf⟩, hno => by
    have h₁ := newBobSinfo_step_ua hReach hpre (hno s List.mem_cons_self)
    have h₂ := newBobSinfo_runSteps_ua ss (Trace.Reachable.Step s.toInput hpre hReach) hwf
      (fun s' hs' => hno s' (List.mem_cons_of_mem s hs'))
    exact newBobSinfo_trans ((reachability.step s.toInput).2.run tr).2.property
      (stepsWF_le ss (s.next tr)) h₁ h₂

private theorem isSome_bind {α β : Type} {m : Traceful α} {f : α → Traceful β} {tr : ExecTrace}
    (h : ((m >>= f).run tr).1.isSome = true) :
    ∃ a, (m.run tr).1 = some a ∧ ((f a).run (m.run tr).2.val).1.isSome = true := by
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst] at h
  rcases hm : (m.run tr).1 with _ | a
  · rw [hm] at h; cases h
  · rw [hm] at h; exact ⟨a, rfl, h⟩

/-- A `MatchesEventsClassicalAt` suffix whose run events are never `init` and whose Alice `recv` runs have a
whisper-tagged input contains no `aliceStart r.alice ..` or `bobStart r.alice ..`. -/
theorem matchesEvents_noStart_alice {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (hwf : ProtocolSetupWF r) :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry},
      MatchesEventsClassicalAt interp' r S g initIds tr ss evs vis →
      (∀ ev, .run ev ∈ evs →
        (∀ p d, ev.cmd ≠ .init p d) ∧
        (ev.party = r.alice → ∀ p, ev.cmd = .recv p → ev.input.head? = some wireWhisperTag)) →
      ∀ s ∈ ss, StepNoStartFor r.alice s
  | _, _, _, _, _, .nil hinv, _, s, hs => stepNoStartFor_of_invisible (hinv s hs)
  | _, _, _, _, _, .run0 hpre _ hrest, hevs, s, hs => by
    rcases List.mem_append.mp hs with hsp | hsr
    · exact stepNoStartFor_of_invisible (hpre s hsp)
    · exact matchesEvents_noStart_alice hwf hrest
        (fun ev hev => hevs ev (List.mem_cons_of_mem _ hev)) s hsr
  | _, _, _, _, _, @MatchesEventsClassicalAt.env _ _ _ _ _ _ pre s₀ ss' ev_env evs' _ _ hpre hem hrest, hevs, s, hs => by
    rcases List.mem_append.mp hs with hsp | hsr
    · exact stepNoStartFor_of_invisible (hpre s hsp)
    · rcases List.mem_cons.mp hsr with rfl | hst
      · cases ev_env with
        | leak _ _ => exact stepNoStartFor_of_leak hem.2.1
        | _ => exact hem.elim
      · exact matchesEvents_noStart_alice hwf hrest
          (fun ev hev => hevs ev (List.mem_cons_of_mem _ hev)) s hst
  | _, _, _, _, _, @MatchesEventsClassicalAt.run1 _ _ _ _ _ tr pre s₀ ss' ev evs' v vs hpre hrm hrest, hevs, s, hs => by
    rcases List.mem_append.mp hs with hsp | hsr
    · exact stepNoStartFor_of_invisible (hpre s hsp)
    · rcases List.mem_cons.mp hsr with rfl | hst
      · obtain ⟨hno_init, hwhisper⟩ := hevs ev List.mem_cons_self
        obtain ⟨_, hparty, hfits, _, hok, _, hvis, inp, drs, outs, hvis_eq, hbme, _, _, _, _⟩ := hrm
        refine ⟨fun b idIdx regB bh heq => ?_, fun a kh regA mh pqIdx spqrIdx heq => ?_⟩
        · subst heq
          cases hcmd : ev.cmd with
          | init p d => exact hno_init p d hcmd
          | send _ | recv _ => rw [hcmd] at hfits; cases hfits
        · subst heq
          simp only [Step.party?, Option.some.injEq] at hparty
          cases hcmd : ev.cmd with
          | init p d => exact hno_init p d hcmd
          | send _ => rw [hcmd] at hfits; cases hfits
          | recv p =>
            have hhead := hwhisper hparty.symm p hcmd
            rw [hvis] at hvis_eq
            unfold _root_.DY.Libsignal.Composed.Refinement.stepView at hvis_eq
            rw [hok] at hvis_eq
            simp only [↓reduceIte, _root_.DY.Libsignal.Composed.Refinement.bobVis,
              List.cons_append, List.cons.injEq] at hvis_eq
            rw [← hvis_eq.1] at hbme
            have hp_some : ∃ q, parsePreKeyWire ev.input = some q := by
              have hprm := hbme.2
              dsimp only [_root_.DY.Libsignal.Composed.Refinement.PreKeyRecvOpkMatches] at hprm
              split at hprm
              · obtain ⟨⟨q, hq, _⟩, _⟩ := hprm; exact ⟨q, hq⟩
              · obtain ⟨⟨q, hq, _⟩, _⟩ := hprm; exact ⟨q, hq⟩
              · exact hprm.elim
            obtain ⟨q, hq⟩ := hp_some
            unfold parsePreKeyWire at hq
            rcases hinp : ev.input with _ | ⟨hd, tl⟩
            · simp [hinp] at hhead
            · simp only [hinp, List.head?_cons, Option.some.injEq] at hhead
              subst hhead; rw [hinp] at hq
              have hne : wireWhisperTag ≠ _root_.DY.Libsignal.PQXDH.Refinement.wirePrekeyTag := by decide
              simp [hne] at hq
      · exact matchesEvents_noStart_alice hwf hrest
          (fun ev' hev' => hevs ev' (List.mem_cons_of_mem _ hev')) s hst

/-- A `MatchesEventsClassicalAt` suffix with no `init` run and no exit-`0` Alice `recv` run contains
neither an Alice session start nor an Alice message decrypt. -/
theorem matchesEvents_noAliceInitOrRecv {interp' : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry},
      MatchesEventsClassicalAt interp' r S g initIds tr ss evs vis →
      (∀ ev, .run ev ∈ evs →
        (∀ p d, ev.cmd ≠ .init p d) ∧
        (ev.party = r.alice → ∀ p out, ev.cmd = .recv p → ev.exit ≠ some (0, out))) →
      ∀ s ∈ ss, StepNoAliceInitOrRecv r.alice s
  | _, _, _, _, _, .nil hinv, _, s, hs => stepNoAliceInitOrRecv_of_invisible (hinv s hs)
  | _, _, _, _, _, .run0 hpre _ hrest, hevs, s, hs => by
    rcases List.mem_append.mp hs with hsp | hsr
    · exact stepNoAliceInitOrRecv_of_invisible (hpre s hsp)
    · exact matchesEvents_noAliceInitOrRecv hrest
        (fun ev hev => hevs ev (List.mem_cons_of_mem _ hev)) s hsr
  | _, _, _, _, _, @MatchesEventsClassicalAt.env _ _ _ _ _ _ pre s₀ ss' ev_env _ _ _ hpre hem hrest, hevs, s, hs => by
    rcases List.mem_append.mp hs with hsp | hsr
    · exact stepNoAliceInitOrRecv_of_invisible (hpre s hsp)
    · rcases List.mem_cons.mp hsr with rfl | hst
      · cases ev_env with
        | leak _ _ => exact stepNoAliceInitOrRecv_of_leak hem.2.1
        | _ => exact hem.elim
      · exact matchesEvents_noAliceInitOrRecv hrest
          (fun ev hev => hevs ev (List.mem_cons_of_mem _ hev)) s hst
  | _, _, _, _, _, @MatchesEventsClassicalAt.run1 _ _ _ _ _ _ pre s₀ ss' ev _ _ _ hpre hrm hrest, hevs, s, hs => by
    rcases List.mem_append.mp hs with hsp | hsr
    · exact stepNoAliceInitOrRecv_of_invisible (hpre s hsp)
    · rcases List.mem_cons.mp hsr with rfl | hst
      · obtain ⟨hno_init, hno_recv⟩ := hevs ev List.mem_cons_self
        obtain ⟨_, hparty, hfits, _, _, ⟨out, hexit⟩, _⟩ := hrm
        refine ⟨⟨fun b idIdx regB bh heq => ?_, fun a kh regA mh pqIdx spqrIdx heq => ?_⟩,
          fun stateIdx msgIdx pqIdx spqrIdx heq => ?_,
          fun stateIdx msgIdx k pqIdx spqrIdx heq => ?_⟩
        · subst heq
          cases hcmd : ev.cmd with
          | init p d => exact hno_init p d hcmd
          | send _ | recv _ => rw [hcmd] at hfits; cases hfits
        · subst heq
          simp only [Step.party?, Option.some.injEq] at hparty
          cases hcmd : ev.cmd with
          | init p d => exact hno_init p d hcmd
          | send _ => rw [hcmd] at hfits; cases hfits
          | recv p => exact hno_recv hparty.symm p out hcmd hexit
        · subst heq
          simp only [Step.party?, Option.some.injEq] at hparty
          cases hcmd : ev.cmd with
          | init p d => exact hno_init p d hcmd
          | send _ => rw [hcmd] at hfits; cases hfits
          | recv p => exact hno_recv hparty.symm p out hcmd hexit
        · subst heq
          simp only [Step.party?, Option.some.injEq] at hparty
          cases hcmd : ev.cmd with
          | init p d => exact hno_init p d hcmd
          | send _ => rw [hcmd] at hfits; cases hfits
          | recv p => exact hno_recv hparty.symm p out hcmd hexit
      · exact matchesEvents_noAliceInitOrRecv hrest
          (fun ev' hev' => hevs ev' (List.mem_cons_of_mem _ hev')) s hst

theorem matchesEventsAt_split {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (more : List CliEvent) :
    ∀ (evs : List CliEvent) {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {vis : List VisEntry},
      MatchesEventsClassicalAt interp r S g initIds tr ss (evs ++ more) vis →
      ∃ ss₁ ss₂ vis₁ vis₂, ss = ss₁ ++ ss₂ ∧ vis = vis₁ ++ vis₂ ∧
        MatchesEventsClassicalAt interp r S g initIds tr ss₁ evs vis₁ ∧
        MatchesEventsClassicalAt interp r S g (evs.foldl stepBundleIds initIds) (runSteps ss₁ tr) ss₂ more vis₂
  | [], _, _, _, _, h => ⟨[], _, [], _, rfl, rfl, .nil (by simp), h⟩
  | e :: evs, initIds, tr, ss, vis, h => by
    rw [List.cons_append] at h
    generalize hE : e :: (evs ++ more) = E at h
    cases h with
    | nil _ => cases hE
    | @run1 _ _ pre s ss' ev _ v vs hpre hrm hrest =>
      injection hE with he hevs; subst he hevs
      obtain ⟨a, b, c, d, rfl, rfl, hm₁, hm₂⟩ := matchesEventsAt_split more evs hrest
      refine ⟨pre ++ s :: a, b, v ++ c, d, by simp, by simp, .run1 hpre hrm hm₁, ?_⟩
      simpa [Symbolic.Proofs.Swarm.UA.Base.runSteps_append, runSteps,
        Symbolic.Proofs.Swarm.UA.Base.stepBundleIds_run_of_runMatches hrm] using hm₂
    | @run0 _ _ pre ss' ev _ vs hpre hrej hrest =>
      injection hE with he hevs; subst he hevs
      obtain ⟨a, b, c, d, rfl, rfl, hm₁, hm₂⟩ := matchesEventsAt_split more evs hrest
      refine ⟨pre ++ a, b, c, d, by simp, rfl, .run0 hpre hrej hm₁, ?_⟩
      simpa [Symbolic.Proofs.Swarm.UA.Base.runSteps_append,
        Symbolic.Proofs.Swarm.UA.Base.stepBundleIds_run_of_runRejected hrej] using hm₂
    | @env _ _ pre s ss' ev _ v vs hpre hem hrest =>
      injection hE with he hevs; subst he hevs
      obtain ⟨a, b, c, d, rfl, rfl, hm₁, hm₂⟩ := matchesEventsAt_split more evs hrest
      refine ⟨pre ++ s :: a, b, v ++ c, d, by simp, by simp, .env hpre hem hm₁, ?_⟩
      simpa [Symbolic.Proofs.Swarm.UA.Base.runSteps_append, runSteps, stepBundleIds] using hm₂

theorem matchesEvents_split {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (more : List CliEvent) (evs : List CliEvent)
    {tr : ExecTrace} {ss : List Step} {vis : List VisEntry}
    (h : MatchesEventsClassical interp r S g tr ss (evs ++ more) vis) :
    ∃ ss₁ ss₂ vis₁ vis₂, ss = ss₁ ++ ss₂ ∧ vis = vis₁ ++ vis₂ ∧
      MatchesEventsClassical interp r S g tr ss₁ evs vis₁ ∧
      MatchesEventsClassicalAt interp r S g (activeBundleIds evs) (runSteps ss₁ tr) ss₂ more vis₂ :=
  matchesEventsAt_split more evs h

/-- `AlicePendingKeysOn` transports across any `MatchesEventsClassicalAt` suffix with no `init` run
and no exit-`0` Alice `recv` run. -/
theorem alicePendingKeysOn_of_matchesEvents {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {ss₁ ss₂ : List Step} {evs₂ : List CliEvent} {vis₂ : List VisEntry}
    {bk kct : HwBytes}
    (_hwf : ProtocolSetupWF r)
    (hrun : ModelRunWF r (ss₁ ++ ss₂))
    (hm : MatchesEventsClassicalAt interp' r S g initIds (runTrace r ss₁) ss₂ evs₂ vis₂)
    (hevs : ∀ ev, .run ev ∈ evs₂ →
      (∀ p d, ev.cmd ≠ .init p d) ∧
      (ev.party = r.alice → ∀ p out, ev.cmd = .recv p → ev.exit ≠ some (0, out)))
    (hap : AlicePendingKeysOn interp' S g r.alice (runTrace r ss₁) bk kct) :
    AlicePendingKeysOn interp' S g r.alice (runTrace r (ss₁ ++ ss₂)) bk kct := by
  have hReach₁ : (runTrace r ss₁).Reachable reachability :=
    modelRunWF_reachable (Symbolic.Proofs.Swarm.UA.Base.modelRunWF_of_append hrun)
  have hwf₂ : StepsWF ss₂ (runTrace r ss₁) := by
    let rec go (a b : List Step) (tr : ExecTrace) (h : StepsWF (a ++ b) tr) : StepsWF b (runSteps a tr) :=
      match a with
      | [] => h
      | x :: xs => go xs b (x.next tr) h.2.2
    exact go ss₁ ss₂ (_root_.DY.Libsignal.Composed.Refinement.setupTrace r) hrun.2.2.1
  have hno := matchesEvents_noAliceInitOrRecv hm hevs
  rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
  exact alicePendingKeysOn_ext (handshakeSessionValid_reachable hReach₁)
    (stepsWF_le ss₂ (runTrace r ss₁))
    (newBobSinfo_runSteps_ua ss₂ hReach₁ hwf₂ (fun s hs => (hno s hs).1))
    (noNewRecvMK_runSteps ss₂ ⟨Nat.le_refl _, fun _ h1 h2 => absurd h1 (Nat.not_le_of_gt h2)⟩ hno)
    hap

theorem aliceNotPendingOn_of_matchesEvents {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {ss₁ ss₂ : List Step} {evs₂ : List CliEvent} {vis₂ : List VisEntry}
    (hwf : ProtocolSetupWF r)
    (hrun : ModelRunWF r (ss₁ ++ ss₂))
    (hm : MatchesEventsClassicalAt interp' r S g initIds (runTrace r ss₁) ss₂ evs₂ vis₂)
    (hevs : ∀ ev, .run ev ∈ evs₂ →
      (∀ p d, ev.cmd ≠ .init p d) ∧
      (ev.party = r.alice → ∀ p, ev.cmd = .recv p → ev.input.head? = some wireWhisperTag))
    (hnp : AliceNotPendingOn r.alice (runTrace r ss₁)) :
    AliceNotPendingOn r.alice (runTrace r (ss₁ ++ ss₂)) := by
  have hReach₁ : (runTrace r ss₁).Reachable reachability :=
    modelRunWF_reachable (Symbolic.Proofs.Swarm.UA.Base.modelRunWF_of_append hrun)
  have hwf₂ : StepsWF ss₂ (runTrace r ss₁) := by
    let rec go (a b : List Step) (tr : ExecTrace) (h : StepsWF (a ++ b) tr) : StepsWF b (runSteps a tr) :=
      match a with
      | [] => h
      | x :: xs => go xs b (x.next tr) h.2.2
    exact go ss₁ ss₂ (_root_.DY.Libsignal.Composed.Refinement.setupTrace r) hrun.2.2.1
  have hno := matchesEvents_noStart_alice hwf hm hevs
  rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
  exact aliceNotPendingOn_ext (handshakeSessionValid_reachable hReach₁)
    (stepsWF_le ss₂ (runTrace r ss₁))
    (newBobSinfo_runSteps_ua ss₂ hReach₁ hwf₂ hno)
    (noNewHs_runSteps ss₂ ⟨Nat.le_refl _, fun _ h1 h2 => absurd h1 (Nat.not_le_of_gt h2)⟩ hno)
    hnp

theorem alicePendingKeysOn_of_explains_append {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs₁ evs₂ : List CliEvent} {bk kct : HwBytes}
    (hwf : ProtocolSetupWF r)
    (hex : _root_.DY.Libsignal.Composed.Refinement.ExplainsClassical interp' r S g ss vis (evs₁ ++ evs₂))
    (hnrc : ¬ ReadCollisionCliClassical interp' r S g ss (evs₁ ++ evs₂))
    (hevs : ∀ ev, .run ev ∈ evs₂ →
      (∀ p d, ev.cmd ≠ .init p d) ∧
      (ev.party = r.alice → ∀ p out, ev.cmd = .recv p → ev.exit ≠ some (0, out)))
    (hpre : ∀ ss₁ vis₁,
      _root_.DY.Libsignal.Composed.Refinement.ExplainsClassical interp' r S g ss₁ vis₁ evs₁ →
      ¬ ReadCollisionCliClassical interp' r S g ss₁ evs₁ →
      AlicePendingKeysOn interp' S g r.alice (runTrace r ss₁) bk kct) :
    AlicePendingKeysOn interp' S g r.alice (runTrace r ss) bk kct := by
  obtain ⟨hc, hg, hrun, hm⟩ := hex
  obtain ⟨ss₁, ss₂, vis₁, vis₂, rfl, rfl, hm₁, hm₂⟩ := matchesEvents_split evs₂ evs₁ hm
  exact alicePendingKeysOn_of_matchesEvents hwf hrun hm₂ hevs
    (hpre ss₁ vis₁ ⟨hc, Symbolic.Proofs.Swarm.UA.Base.ghostWF_of_append hg,
      Symbolic.Proofs.Swarm.UA.Base.modelRunWF_of_append hrun, hm₁⟩
      (fun hrc => hnrc (Symbolic.Proofs.Swarm.UA.Base.readCollisionCli_append ss₂ evs₂ hrc)))

theorem aliceNotPendingOn_of_explains_append {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs₁ evs₂ : List CliEvent}
    (hwf : ProtocolSetupWF r)
    (hex : _root_.DY.Libsignal.Composed.Refinement.ExplainsClassical interp' r S g ss vis (evs₁ ++ evs₂))
    (hnrc : ¬ ReadCollisionCliClassical interp' r S g ss (evs₁ ++ evs₂))
    (hevs : ∀ ev, .run ev ∈ evs₂ →
      (∀ p d, ev.cmd ≠ .init p d) ∧
      (ev.party = r.alice → ∀ p, ev.cmd = .recv p → ev.input.head? = some wireWhisperTag))
    (hpre : ∀ ss₁ vis₁,
      _root_.DY.Libsignal.Composed.Refinement.ExplainsClassical interp' r S g ss₁ vis₁ evs₁ →
      ¬ ReadCollisionCliClassical interp' r S g ss₁ evs₁ →
      AliceNotPendingOn r.alice (runTrace r ss₁)) :
    AliceNotPendingOn r.alice (runTrace r ss) := by
  obtain ⟨hc, hg, hrun, hm⟩ := hex
  obtain ⟨ss₁, ss₂, vis₁, vis₂, rfl, rfl, hm₁, hm₂⟩ := matchesEvents_split evs₂ evs₁ hm
  exact aliceNotPendingOn_of_matchesEvents hwf hrun hm₂ hevs
    (hpre ss₁ vis₁ ⟨hc, Symbolic.Proofs.Swarm.UA.Base.ghostWF_of_append hg,
      Symbolic.Proofs.Swarm.UA.Base.modelRunWF_of_append hrun, hm₁⟩
      (fun hrc => hnrc (Symbolic.Proofs.Swarm.UA.Base.readCollisionCli_append ss₂ evs₂ hrc)))

theorem aliceRecordPendingInSession_of_explains_append {interp' : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ evs₂ : List CliEvent} {records₁ records₂ : Participant → Option HwBytes}
    (hwf : ProtocolSetupWF r)
    (hex : _root_.DY.Libsignal.Composed.Refinement.ExplainsClassical interp' r S g ss vis (evs₁ ++ evs₂))
    (hnrc : ¬ ReadCollisionCliClassical interp' r S g ss (evs₁ ++ evs₂))
    (hevs : ∀ ev, .run ev ∈ evs₂ →
      (∀ p d, ev.cmd ≠ .init p d) ∧
      (ev.party = r.alice → ∀ p out, ev.cmd = .recv p → ev.exit ≠ some (0, out)))
    (hrec_eq : records₂ r.alice = records₁ r.alice)
    (hpre : ∀ ss₁ vis₁,
      _root_.DY.Libsignal.Composed.Refinement.ExplainsClassical interp' r S g ss₁ vis₁ evs₁ →
      ¬ ReadCollisionCliClassical interp' r S g ss₁ evs₁ →
      AliceRecordPendingInSession interp' r S g (runTrace r ss₁) records₁ (activeBundleIds evs₁)) :
    AliceRecordPendingInSession interp' r S g (runTrace r ss) records₂ (activeBundleIds (evs₁ ++ evs₂)) := by
  obtain ⟨hc, hg, hrun, hm⟩ := hex
  obtain ⟨ss₁, ss₂, vis₁, vis₂, rfl, rfl, hm₁, hm₂⟩ := matchesEvents_split evs₂ evs₁ hm
  have hex₁ : _root_.DY.Libsignal.Composed.Refinement.ExplainsClassical interp' r S g ss₁ vis₁ evs₁ :=
    ⟨hc, Symbolic.Proofs.Swarm.UA.Base.ghostWF_of_append hg,
      Symbolic.Proofs.Swarm.UA.Base.modelRunWF_of_append hrun, hm₁⟩
  have hnrc₁ : ¬ ReadCollisionCliClassical interp' r S g ss₁ evs₁ :=
    fun hrc => hnrc (Symbolic.Proofs.Swarm.UA.Base.readCollisionCli_append ss₂ evs₂ hrc)
  have hap₁ := hpre ss₁ vis₁ hex₁ hnrc₁
  have habi : activeBundleIds (evs₁ ++ evs₂) = activeBundleIds evs₁ :=
    Symbolic.Proofs.Swarm.UA.Base.activeBundleIds_append_of_no_init fun ev hev => (hevs ev hev).1
  rw [habi]
  have hReach₁ : (runTrace r ss₁).Reachable reachability := modelRunWF_reachable hex₁.2.2.1
  have hwf₂ : StepsWF ss₂ (runTrace r ss₁) := by
    let rec go (a b : List Step) (tr : ExecTrace) (h : StepsWF (a ++ b) tr) : StepsWF b (runSteps a tr) :=
      match a with
      | [] => h
      | x :: xs => go xs b (x.next tr) h.2.2
    exact go ss₁ ss₂ (_root_.DY.Libsignal.Composed.Refinement.setupTrace r) hrun.2.2.1
  have hno := matchesEvents_noAliceInitOrRecv hm₂ hevs
  intro rec sess hrec₂ hcan
  rw [hrec_eq] at hrec₂
  obtain ⟨hsome₁, hnone₁⟩ := hap₁ rec sess hrec₂ hcan
  refine ⟨fun items kpk hp hk => ?_, fun hp_none => ?_⟩
  · obtain ⟨hids, hap_k⟩ := hsome₁ items kpk hp hk
    exact ⟨hids, alicePendingKeysOn_of_matchesEvents hwf hrun hm₂ hevs hap_k⟩
  · rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
    exact aliceNotPendingOn_ext (handshakeSessionValid_reachable hReach₁)
      (stepsWF_le ss₂ (runTrace r ss₁))
      (newBobSinfo_runSteps_ua ss₂ hReach₁ hwf₂ (fun s hs => (hno s hs).1))
      (noNewHs_runSteps ss₂ ⟨Nat.le_refl _, fun _ h1 h2 => absurd h1 (Nat.not_le_of_gt h2)⟩
        (fun s hs => (hno s hs).1))
      (hnone₁ hp_none)

theorem aliceRecordPendingInSession_of_no_record {interp' : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {records : Participant → Option HwBytes}
    {initIds : Option BundlePreKeyIds} (hnone : records r.alice = none) :
    AliceRecordPendingInSession interp' r S g tr records initIds := by
  intro rec _ hrec _
  rw [hnone] at hrec
  cases hrec

theorem aliceRecordPendingInSession_of_not_pending {interp' : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {records : Participant → Option HwBytes}
    {initIds : Option BundlePreKeyIds}
    (hnone : ∀ rec sess, records r.alice = some rec →
      slots_RecordCanonical_Q slots_NonEmptyV1Q rec sess → sess.pendingPreKey = none)
    (hnp : AliceNotPendingOn r.alice tr) :
    AliceRecordPendingInSession interp' r S g tr records initIds := by
  intro rec sess hrec hcan
  refine ⟨fun items _ hp _ => ?_, fun _ => hnp⟩
  rw [hnone rec sess hrec hcan] at hp
  cases hp

/-! ## Initial `AlicePendingKeysOn` at `aliceStart` -/

private theorem le_iniAliceStartTr (tr : ExecTrace) (a b : Participant) (o : AliceHandshakeOut) :
    tr ≤ iniAliceStartTr tr a b o := by
  unfold iniAliceStartTr
  dsimp only
  exact Trace.le_trans _ _ _ (Trace.append_le _ _)
    (Trace.le_trans _ _ _ (Trace.append_le _ _)
    (Trace.le_trans _ _ _ (Trace.append_le _ _)
    (Trace.le_trans _ _ _ (Trace.append_le _ _)
    (Trace.le_trans _ _ _ (Trace.append_le _ _)
    (Trace.le_trans _ _ _ (Trace.append_le _ _)
    (Trace.le_trans _ _ _ (Trace.append_le _ _)
    (Trace.le_trans _ _ _ (Trace.append_le _ _) (Trace.append_le _ _))))))))

private theorem at?_append_of_lt' {E : Type} [ExecTraceTypes.Has E] {F : Type} [ExecTraceTypes.Has F]
    (tr : ExecTrace) (f : F) {i : Nat} (hi : i < tr.length) :
    ((tr.append f).at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < (tr.append f).length := Nat.lt_of_lt_of_le hi (Trace.length_le _ _ (Trace.append_le tr f))
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append f) i hi (Trace.append_le tr f)]

@[simp] private theorem length_append_entry {T : Type} [ExecTraceTypes.Has T]
    (tr : ExecTrace) (x : T) : (tr.append x).length = tr.length + 1 := by
  simp [Trace.append, Trace.length]

private theorem at?_append_eq' {E : Type} [ExecTraceTypes.Has E] {F : Type} [ExecTraceTypes.Has F]
    (tr : ExecTrace) (f : F) {i : Nat} (hi : i = tr.length) :
    ((tr.append f).at? i : Option E) =
      (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj f : ExecTrace.Entry) : Option E) := by
  subst hi; simp [Trace.at?, Trace.append, Trace.at, Trace.length]

local macro "at?_tr9_tac" : tactic =>
  `(tactic| (dsimp only [iniAliceStartTr]
             repeat (rw [at?_append_of_lt' _ _ (by simp only [length_append_entry]; omega)])
             rw [at?_append_eq' _ _ (by simp [length_append_entry])]; rfl))

/-- Every `TRState` stored in `iniAliceStartTr tr a b o` at an index `j ≥ tr.length` is the new
state `iniAliceStartState tr b o` of `a` at `tr.length + 8`. -/
theorem trSt_iniAliceStartTr {tr : ExecTrace} {a b p : Participant} {o : AliceHandshakeOut}
    {j : Nat} {st : TRState} (hj : tr.length ≤ j)
    (hat : ((iniAliceStartTr tr a b o).at? j : Option TRStEntry) = some ⟨⟨p, st⟩⟩) :
    j = tr.length + 8 ∧ p = a ∧ st = iniAliceStartState tr b o := by
  have hj_lt : j < (iniAliceStartTr tr a b o).length := bks_lt_length_of_at? hat
  have hlen : (iniAliceStartTr tr a b o).length = tr.length + 9 :=
    Symbolic.Swarm.CREF.length_iniAliceStartTr tr a b o
  by_cases hj8 : j = tr.length + 8
  · subst hj8
    have hat8 : ((iniAliceStartTr tr a b o).at? (tr.length + 8) : Option TRStEntry) =
        some ⟨⟨a, iniAliceStartState tr b o⟩⟩ := by at?_tr9_tac
    rw [hat8] at hat; injection hat with h1; injection h1 with h2
    exact ⟨rfl, (congrArg _root_.DY.PersistentLocalState.LocalState.participant h2).symm,
      (congrArg _root_.DY.PersistentLocalState.LocalState.state h2).symm⟩
  · exfalso
    have hn (k : Nat) (hk : k < 8) :
        ((iniAliceStartTr tr a b o).at? (tr.length + k) : Option TRStEntry) = none := by
      rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _
      · at?_tr9_tac
      · at?_tr9_tac
      · at?_tr9_tac
      · at?_tr9_tac
      · at?_tr9_tac
      · at?_tr9_tac
      · at?_tr9_tac
      · at?_tr9_tac
      · omega
    rw [show j = tr.length + (j - tr.length) by omega, hn (j - tr.length) (by omega)] at hat
    cases hat

/-- `pendingPreKey` of the snapshot stored by `iniAliceStartTr` is `some (o.ek, o.ct)`. -/
theorem pendingPreKey_iniAliceStartTr {tr : ExecTrace} (hv : HandshakeSessionValid tr)
    (a b : Participant) (o : AliceHandshakeOut) :
    pendingPreKey (iniAliceStartTr tr a b o) (tr.length + 8) = some (o.ek, o.ct) := by
  set tr' := iniAliceStartTr tr a b o
  set stA := iniAliceStartState tr b o
  have hat8 : (tr'.at? (tr.length + 8) : Option TRStEntry) = some ⟨⟨a, stA⟩⟩ := by
    unfold tr'; at?_tr9_tac
  have hdec_false : sessionHasDecrypted tr' (stA.sessionInfo a) (tr.length + 8) = false := by
    unfold sessionHasDecrypted
    rw [List.any_eq_false]
    intro j hj_range
    have hj_lt8 : j < tr.length + 8 := List.mem_range.mp hj_range
    by_cases hj_tr : j < tr.length
    · rw [bks_getEventAt_of_le TREvent (le_iniAliceStartTr tr a b o) hj_tr]
      rcases hev : tr.getEventAt TREvent j with _ | ev_tr
      · simp
      · cases ev_tr with
        | MessageKey s' dir seed salt n rIdx par =>
          cases dir with
          | sender => simp
          | receiver =>
            dsimp only
            rw [Bool.not_eq_true, decide_eq_false_iff_not]
            intro hs_eq
            obtain ⟨t, _, htj, hsid⟩ := (hv.mkRecv j s' seed salt n rIdx par hev).1
              (by rw [hs_eq]; rfl)
            have hsidA : (stA.sessionInfo a).sid = concat (dhPk (randTerm (tr.length + 2) 32)) o.keys.rk := rfl
            rw [hs_eq, hsidA] at hsid
            have ht_eq := (mkRand_inj (dhPk_inj (concat_inj hsid).1)).1
            omega
        | _ => simp
    · have htr (k : Nat) (v : Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent))
          (hk : (tr'.at? k : Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) = v) :
          tr'.getEventAt TREvent k = v.map (·.ev) := by cases v <;> simp [Trace.getEventAt, hk]
      have hk_lt : j - tr.length < 8 := by omega
      rw [show j = tr.length + (j - tr.length) by omega]
      rcases hjk : j - tr.length with _ | _ | _ | _ | _ | _ | _ | _ | _
      · rw [htr _ none (by unfold tr'; at?_tr9_tac)]; simp
      · rw [htr _ none (by unfold tr'; at?_tr9_tac)]; simp
      · rw [htr _ none (by unfold tr'; at?_tr9_tac)]; simp
      · rw [htr _ none (by unfold tr'; at?_tr9_tac)]; simp
      · rw [htr _ none (by unfold tr'; at?_tr9_tac)]; simp
      · rw [htr _ none (by unfold tr'; at?_tr9_tac)]; simp
      · rw [htr _ (some ⟨.InitSession a b (dhPk (randTerm (tr.length + 2) 32)) o.spk⟩)
          (by unfold tr'; at?_tr9_tac)]; simp
      · rw [htr _ none (by unfold tr'; at?_tr9_tac)]; simp
      · omega
  rw [pendingPreKey_eq_ppkOf hat8, hdec_false]; simp only [Bool.false_eq_true, ↓reduceIte]; unfold ppkOf
  rw [Symbolic.Swarm.CREF.length_iniAliceStartTr tr a b o]
  have hrange : List.range (tr.length + 9) = List.range tr.length ++ List.range' tr.length 9 := by
    rw [List.range_eq_range', List.range_eq_range', ← List.range'_append_1]; simp only [Nat.zero_add]
  rw [hrange, List.findSome?_append]
  rw [show (List.range tr.length).findSome? _ = none from by
    rw [List.findSome?_eq_none_iff]; intro i hi
    have hilt : i < tr.length := List.mem_range.mp hi
    rw [bks_getEventAt_of_le ComposedEvent (le_iniAliceStartTr tr a b o) hilt]
    rcases hev : tr.getEventAt ComposedEvent i with _ | ⟨s', d⟩
    · rfl
    · dsimp only; by_cases hs : s' = stA.sessionInfo a
      · exfalso
        obtain ⟨t, _, hti, hsid⟩ := (hv.hs i s' d hev).2.1 (by rw [hs]; rfl)
        have hsidA : (stA.sessionInfo a).sid = concat (dhPk (randTerm (tr.length + 2) 32)) o.keys.rk := rfl
        rw [hs, hsidA] at hsid
        have ht_eq := (mkRand_inj (dhPk_inj (concat_inj hsid).1)).1; omega
      · simp [hs], Option.none_or]
  have hr9 : List.range' tr.length 9 = [tr.length, tr.length + 1, tr.length + 2, tr.length + 3,
      tr.length + 4, tr.length + 5, tr.length + 6, tr.length + 7, tr.length + 8] := rfl
  rw [hr9]
  have hc (k : Nat) (v : Option CEntry) (hk : (tr'.at? k : Option CEntry) = v) :
      tr'.getEventAt ComposedEvent k = v.map (·.ev) := by cases v <;> simp [Trace.getEventAt, hk]
  have hpq5 : tr'.getEventAt PQXDHEvent (tr.length + 5) =
      some (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys) :=
    (Symbolic.Swarm.CREF.getEventAt_pq_iniAliceStartTr tr a b o).2.2.2.2.2.1
  simp [hc tr.length none (by unfold tr'; at?_tr9_tac),
    hc (tr.length + 1) none (by unfold tr'; at?_tr9_tac),
    hc (tr.length + 2) none (by unfold tr'; at?_tr9_tac),
    hc (tr.length + 3) none (by unfold tr'; at?_tr9_tac),
    hc (tr.length + 4) none (by unfold tr'; at?_tr9_tac),
    hc (tr.length + 5) none (by unfold tr'; at?_tr9_tac),
    hc (tr.length + 6) none (by unfold tr'; at?_tr9_tac),
    hc (tr.length + 7) (some (CEvE (.HandshakeSession (stA.sessionInfo a) (tr.length + 5))))
      (by unfold tr'; at?_tr9_tac), CEvE, hpq5]

theorem alicePendingKeysOn_start {interp' : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {alice : Participant} {tr tr' : ExecTrace} {ek ct : _root_.DY.Bytes}
    (hrole : ∀ (i : Nat) (st : TRState), (tr'.at? i : Option TRStEntry) = some ⟨⟨alice, st⟩⟩ →
      st.initiator = true)
    (hex : ∃ (j : Nat) (st : TRState), tr.length ≤ j ∧
      (tr'.at? j : Option TRStEntry) = some ⟨⟨alice, st⟩⟩)
    (hnew : ∀ (j : Nat) (st : TRState), tr.length ≤ j →
      (tr'.at? j : Option TRStEntry) = some ⟨⟨alice, st⟩⟩ →
      pendingPreKey tr' j = some (ek, ct)) :
    AlicePendingKeysOn interp' S g alice tr'
      (ecKey (gamma interp' S g ek)) (kyberKey (gamma interp' S g ct)) := by
  intro k st hst hcur
  have hat := bks_stored_of_getLocalState hst
  by_cases hk : k < tr.length
  · exfalso; obtain ⟨j, st', hj, hatj⟩ := hex
    rw [isCurrentSnapshot_false_of_later hat hatj (by omega)
      (by rw [hrole _ _ hatj, hrole _ _ hat])] at hcur; cases hcur
  · exact ⟨ek, ct, hnew k st (Nat.le_of_not_lt hk) hat, rfl, rfl⟩

/-- `AlicePendingKeysOn` holds immediately after `iniAliceStartTr`. -/
theorem alicePendingKeysOn_iniAliceStartTr {interp' : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {a b : Participant} (o : AliceHandshakeOut)
    (hv : HandshakeSessionValid tr)
    (hrole : ∀ (i : Nat) (st : TRState), (tr.at? i : Option TRStEntry) = some ⟨⟨a, st⟩⟩ →
      st.initiator = true) :
    AlicePendingKeysOn interp' S g a (iniAliceStartTr tr a b o)
      (ecKey (gamma interp' S g o.ek)) (kyberKey (gamma interp' S g o.ct)) := by
  set tr' := iniAliceStartTr tr a b o
  have hat8 : (tr'.at? (tr.length + 8) : Option TRStEntry) =
      some ⟨⟨a, iniAliceStartState tr b o⟩⟩ := by unfold tr'; at?_tr9_tac
  refine alicePendingKeysOn_start (tr := tr) ?_ ⟨tr.length + 8, iniAliceStartState tr b o, by omega, hat8⟩ ?_
  · intro i st hat
    by_cases hi : i < tr.length
    · have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (Trace.length_le _ _ (le_iniAliceStartTr tr a b o))
      have hle_at : (tr'.at? i : Option TRStEntry) = (tr.at? i : Option TRStEntry) := by
        simp only [Trace.at?, hi, hi', ↓reduceDIte]
        rw [← Trace.at_le tr tr' i hi (le_iniAliceStartTr tr a b o)]
      rw [hle_at] at hat; exact hrole i st hat
    · obtain ⟨_, _, rfl⟩ := trSt_iniAliceStartTr (Nat.le_of_not_lt hi) hat; rfl
  · intro j st hj hat
    obtain ⟨rfl, _, _⟩ := trSt_iniAliceStartTr hj hat
    exact pendingPreKey_iniAliceStartTr hv a b o

/-- Any succeeding `Step.aliceStart` step produces `iniAliceStartTr` on an `aliceOut` whose
`pqpk` was read from `bh.pqpk` on `tr`. -/
theorem aliceStart_ok_eq_iniAliceStartTr {tr : ExecTrace} {a b : Participant}
    {idStateIdx regIdxB : Nat} {bh : BundleHandles}
    (hok : (Step.aliceStart a b idStateIdx regIdxB bh).ok tr = true) :
    ∃ ikA ikB spk pqpk opk,
      NetMsgAt pqpk bh.pqpk tr ∧
      (Step.aliceStart a b idStateIdx regIdxB bh).next tr =
        iniAliceStartTr tr a b (aliceOut tr ikA ikB spk pqpk opk) := by
  have hP : tr.length + 7 ≤ ((_root_.DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).2.val.length →
      ∃ ikA ikB spk pqpk opk, NetMsgAt pqpk bh.pqpk tr ∧
        ((_root_.DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).2.val =
          iniAliceStartTr tr a b (aliceOut tr ikA ikB spk pqpk opk) := by
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.aliceStart_eq_inline]
    refine bind_aliceHandshake_at (Inv := fun t => tr.length + 7 ≤ t.length →
      ∃ ikA ikB spk pqpk opk, NetMsgAt pqpk bh.pqpk tr ∧
        t = iniAliceStartTr tr a b (aliceOut tr ikA ikB spk pqpk opk))
      a b idStateIdx regIdxB bh tr (fun h => by omega)
      (fun h => by simp only [length_append_entry] at h; omega) ?_
    exact fun ikA ikB _ spk _ pqpk _ opk _ _ _ _ _ hpq _ _ _ _ _ _ _ =>
      ⟨ikA, ikB, spk, pqpk, opk, hpq, rfl⟩
  refine hP ?_
  have hsome : ((_root_.DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).1.isSome = true := hok
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.aliceStart_eq_inline] at hsome ⊢
  obtain ⟨w, hhs, _⟩ := isSome_bind hsome
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, hhs]
  set t_hs := ((_root_.DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB bh).run tr).2.val
  have hle : tr.length ≤ t_hs.length :=
    Trace.length_le _ _ ((_root_.DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB bh).run tr).2.property
  dsimp only
  simp only [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst,
    Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, _root_.DY.Random.genRand,
    _root_.DY.Network.sendMessage, _root_.DY.Libsignal.TripleRatchet.traceLength,
    _root_.DY.ProtocolEvent.logEvent,
    _root_.DY.PersistentLocalState.storeLocalState,
    _root_.DY.PersistentGlobalState.storeGlobalState,
    _root_.DY.appendEntry, Traceful.run_mk, Traceful.run_pure, length_append_entry]
  omega

end Symbolic.Proofs.Swarm.UA.PendingPreKey
