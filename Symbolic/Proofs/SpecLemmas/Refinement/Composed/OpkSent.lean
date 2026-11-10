/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Mathlib.Tactic.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Public Network Availability of Stored One-Time Prekeys

Defines the trace invariant `OpkNetOK`, stating that every stored one-time prekey secret key has
its Diffie-Hellman public key on the network. Proves that `OpkNetOK` holds on the empty trace and
is preserved by every `Move.act`, so any one-time prekey public key read by `bobOpkPk` is
attacker-known (`bobOpkPk_known`).
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.PQKem DY.Signature DY.X25519
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH
open DY.Libsignal.Composed
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompTrace

/-! ## `OpkNetOK` invariant and single-step lemmas -/

/-- Every stored one-time prekey record has its public key on the network. -/
def OpkNetOK (tr : ExecTrace) : Prop :=
  ∀ p sk i, PQXDHStoredAt tr p { kind := .oneTimePrekey, sk } i →
    ∃ j, NetMsgAt (DiffieHellman.dhPk sk) j tr

theorem opkNetOK_nil : OpkNetOK (Trace.nil : ExecTrace) := by
  intro _ _ _ h
  simp only [PQXDHStoredAt, DY.Trace.at?, Symbolic.DYBridge.DY.Trace.nil_length_not_lt,
    ↓reduceDIte, reduceCtorEq] at h

theorem opkNetOK_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace}
    (hok : OpkNetOK tr) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHStEntry) = none) :
    OpkNetOK (tr.append e) := by
  intro p sk i h
  obtain ⟨j, hj⟩ := hok p sk i (pqxdhStoredAt_append_other hnone h)
  exact ⟨j, hj.mono (Trace.append_le tr e)⟩

theorem opkNetOK_append_pqSt {tr : ExecTrace} (hok : OpkNetOK tr) (me : Participant)
    (st₀ : PQXDHState) (hk : st₀.kind ≠ .oneTimePrekey) :
    OpkNetOK (tr.append (PQStE me st₀)) := by
  intro p sk i h
  rcases pqxdhStoredAt_append_same h with ⟨_, h0⟩ | ⟨_, _, hst⟩
  · obtain ⟨j, hj⟩ := hok p sk i h0
    exact ⟨j, hj.mono (Trace.append_le tr _)⟩
  · exact absurd (hst ▸ rfl) hk

theorem opkNetOK_append_opk_net {tr : ExecTrace} (hok : OpkNetOK tr) (me : Participant)
    (sk₀ : Bytes) :
    OpkNetOK ((tr.append (PQStE me { kind := .oneTimePrekey, sk := sk₀ })).append
      (NetE (DiffieHellman.dhPk sk₀))) := by
  let tr1 := tr.append (PQStE me { kind := .oneTimePrekey, sk := sk₀ })
  have hle1 : tr ≤ tr1 := Trace.append_le tr _
  have hle2 : tr1 ≤ tr1.append (NetE (DiffieHellman.dhPk sk₀)) := Trace.append_le tr1 _
  have hnet : NetMsgAt (DiffieHellman.dhPk sk₀) tr1.length
      (tr1.append (NetE (DiffieHellman.dhPk sk₀))) :=
    Trace.at?_append tr1 (NetE (DiffieHellman.dhPk sk₀))
  intro p sk i h
  have h1 : PQXDHStoredAt tr1 p { kind := .oneTimePrekey, sk } i :=
    pqxdhStoredAt_append_other (e := NetE (DiffieHellman.dhPk sk₀)) rfl h
  rcases pqxdhStoredAt_append_same h1 with ⟨_, h0⟩ | ⟨_, _, hst⟩
  · obtain ⟨j, hj⟩ := hok p sk i h0
    exact ⟨j, (hj.mono hle1).mono hle2⟩
  · cases hst
    exact ⟨tr1.length, hnet⟩

theorem OpkNetOK.preserves_storeLocalState_pq (me : Participant) (st : PQXDHState)
    (hk : st.kind ≠ .oneTimePrekey) :
    CompTrace.Preserves OpkNetOK (PersistentLocalState.storeLocalState me st) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact opkNetOK_append_pqSt hok me st hk

theorem OpkNetOK.preserves_logEvent_pq (ev : PQXDHEvent) :
    CompTrace.Preserves OpkNetOK (ProtocolEvent.logEvent ev) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
    DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact opkNetOK_append_other hok (PQEvE ev) rfl

/-! ## Preservation across protocol actions -/

theorem OpkNetOK.preserves_sendMessage (msg : Bytes) :
    CompTrace.Preserves OpkNetOK (Network.sendMessage msg) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact opkNetOK_append_other hok (NetE msg) rfl

theorem OpkNetOK.preserves_genRand (n : Nat) :
    CompTrace.Preserves OpkNetOK (Random.genRand n) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
    DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact opkNetOK_append_other hok (RndE n) rfl

theorem OpkNetOK.preserves_storeLocalState_tr (me : Participant) (st : TRState) :
    CompTrace.Preserves OpkNetOK (PersistentLocalState.storeLocalState me st) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact opkNetOK_append_other hok (TRStE me st) rfl

theorem OpkNetOK.preserves_logEvent_tr (ev : TREvent) :
    CompTrace.Preserves OpkNetOK (ProtocolEvent.logEvent ev) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
    DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact opkNetOK_append_other hok (TREvE ev) rfl

theorem OpkNetOK.preserves_logEvent_c (ev : ComposedEvent) :
    CompTrace.Preserves OpkNetOK (ProtocolEvent.logEvent ev) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
    DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact opkNetOK_append_other hok (CEvE ev) rfl

theorem OpkNetOK.preserves_getKey (p : Participant) (stateIdx : Nat) (kind : KeyKind) :
    CompTrace.Preserves OpkNetOK (DY.Libsignal.PQXDH.getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p stateIdx) fun _ => ?_
  exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _

theorem OpkNetOK.preserves_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : Bytes) (counter : UInt32)
    (rIdx childStateIdx : Nat) (st : TRState) :
    CompTrace.Preserves OpkNetOK
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt counter rIdx childStateIdx st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
  exact OpkNetOK.preserves_storeLocalState_tr me st

theorem OpkNetOK.preserves_logSkippedKeys (s : SessionInfo) (ratchetKey : Bytes)
    (rIdx sourceStateIdx : Nat) :
    ∀ (count : Nat) (ck : Bytes) (idx : UInt32),
      CompTrace.Preserves OpkNetOK
        (DY.Libsignal.TripleRatchet.logSkippedKeys s ratchetKey rIdx sourceStateIdx ck idx count)
  | 0, _, _ => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    exact CompTrace.Preserves.pure ()
  | count + 1, ck, idx => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
    exact OpkNetOK.preserves_logSkippedKeys s ratchetKey rIdx sourceStateIdx count (DY.Libsignal.TripleRatchet.kdfCk ck).1 (idx + 1)

theorem OpkNetOK.preserves_dhRatchetStep (st : TRState) (peerRatchetKey : Bytes) :
    CompTrace.Preserves OpkNetOK (DY.Libsignal.TripleRatchet.dhRatchetStep st peerRatchetKey) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_genRand 32) fun _ => ?_
  exact CompTrace.Preserves.pure _

theorem OpkNetOK.preserves_ensureReceiverChain (st : TRState) (peerRatchetKey : Bytes) :
    CompTrace.Preserves OpkNetOK (DY.Libsignal.TripleRatchet.ensureReceiverChain st peerRatchetKey) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact CompTrace.Preserves.pure _
  · refine CompTrace.Preserves.bind (OpkNetOK.preserves_dhRatchetStep st peerRatchetKey) fun ⟨_, _⟩ => ?_
    exact CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.failure

theorem OpkNetOK.preserves_registerIdentity (p : Participant) :
    CompTrace.Preserves OpkNetOK (registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_pq _) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_sendMessage _) fun _ => ?_
  exact OpkNetOK.preserves_storeLocalState_pq p _ (by intro h; cases h)

theorem OpkNetOK.preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    CompTrace.Preserves OpkNetOK (genSignedPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_getKey b idStateIdx .identity) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_pq _) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_storeLocalState_pq b _ (by intro h; cases h)) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.pure _

theorem OpkNetOK.preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    CompTrace.Preserves OpkNetOK (genPQPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_getKey b idStateIdx .identity) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_pq _) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_storeLocalState_pq b _ (by intro h; cases h)) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.pure _

theorem OpkNetOK.preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) :
    CompTrace.Preserves OpkNetOK (aliceStart a b idStateIdx regIdxB bh) := by
  intro tr hok
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine CompTrace.bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hok
    (opkNetOK_append_other hok (RndE 32) rfl) ?_
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hok2 : OpkNetOK ((tr.append (RndE 32)).append (RndE 32)) :=
    opkNetOK_append_other (opkNetOK_append_other hok (RndE 32) rfl) (RndE 32) rfl
  refine (show CompTrace.Preserves OpkNetOK _ by
    refine CompTrace.Preserves.bind (OpkNetOK.preserves_genRand 32) fun _ => ?_
    refine CompTrace.Preserves.bind (OpkNetOK.preserves_sendMessage _) fun _ => ?_
    refine CompTrace.Preserves.bind (OpkNetOK.preserves_sendMessage _) fun _ => ?_
    refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
    refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_pq _) fun _ => ?_
    refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
    refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_c _) fun _ => ?_
    exact OpkNetOK.preserves_storeLocalState_tr a _) _ hok2

theorem OpkNetOK.preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    CompTrace.Preserves OpkNetOK (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr hok
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hok ?_
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  refine (show CompTrace.Preserves OpkNetOK _ by
    refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveSignalMsg mh.msg) fun _ => ?_
    refine CompTrace.Preserves.bind (OpkNetOK.preserves_ensureReceiverChain _ _) fun ⟨_, _, _⟩ => ?_
    dsimp only
    split
    · split
      · refine CompTrace.Preserves.bind (OpkNetOK.preserves_sendMessage _) fun _ => ?_
        refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
        refine CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
        split
        · refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => ?_
          refine CompTrace.Preserves.bind
            (OpkNetOK.preserves_logEvent_pq _) fun _ => ?_
          refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
          refine CompTrace.Preserves.bind
            (OpkNetOK.preserves_logEvent_pq _) fun _ => ?_
          split
          · refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
            refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
            refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_c _) fun _ => ?_
            refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
            refine CompTrace.Preserves.bind (OpkNetOK.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
            refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
            exact OpkNetOK.preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _
          · refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_c _) fun _ => ?_
            refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
            refine CompTrace.Preserves.bind (OpkNetOK.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
            refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
            exact OpkNetOK.preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _
        · refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
          refine CompTrace.Preserves.bind
            (OpkNetOK.preserves_logEvent_pq _) fun _ => ?_
          split
          · refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
            refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
            refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_c _) fun _ => ?_
            refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
            refine CompTrace.Preserves.bind (OpkNetOK.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
            refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
            exact OpkNetOK.preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _
          · refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_c _) fun _ => ?_
            refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
            refine CompTrace.Preserves.bind (OpkNetOK.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
            refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
            exact OpkNetOK.preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _
      · exact CompTrace.Preserves.failure
    · exact CompTrace.Preserves.failure) _ hok

theorem OpkNetOK.preserves_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat) :
    CompTrace.Preserves OpkNetOK
      (DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_genRand coinsLen) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_logMessageKeyAndStore me _ .sender _ _ _ _ _ _) fun _ => ?_
  exact OpkNetOK.preserves_sendMessage _

theorem OpkNetOK.preserves_messageEncryptAbort (me : Participant) (stH : Nat) :
    CompTrace.Preserves OpkNetOK
      (DY.Libsignal.TripleRatchet.messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_genRand 32) fun _ => ?_
  exact CompTrace.Preserves.failure

theorem OpkNetOK.preserves_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    CompTrace.Preserves OpkNetOK
      (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveSignalMsg msgH) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_ensureReceiverChain _ _) fun ⟨_, _, _⟩ => ?_
  dsimp only
  split
  · split
    · refine CompTrace.Preserves.bind (OpkNetOK.preserves_sendMessage _) fun _ => ?_
      refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
      refine CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
      split
      · refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
        refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
        refine CompTrace.Preserves.bind (OpkNetOK.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
        refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
        exact OpkNetOK.preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
      · refine CompTrace.Preserves.bind (OpkNetOK.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
        refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
        exact OpkNetOK.preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact CompTrace.Preserves.failure
  · exact CompTrace.Preserves.failure

theorem OpkNetOK.preserves_messageDecryptSkipped (me : Participant)
    (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    CompTrace.Preserves OpkNetOK
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveSignalMsg msgH) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getEntry evH) fun ⟨ev⟩ => ?_
  cases ev with
  | SkippedKeyStored _ _ _ _ _ _ =>
    dsimp only
    refine CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => ?_
    refine CompTrace.Preserves.bind (CompTrace.Preserves.guardTrace _) fun _ => ?_
    split
    · refine CompTrace.Preserves.bind (OpkNetOK.preserves_sendMessage _) fun _ => ?_
      refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
      refine CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
      refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
      refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
      exact OpkNetOK.preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact CompTrace.Preserves.failure
  | _ => exact CompTrace.Preserves.failure

theorem OpkNetOK.preserves_exposeKey (me : Participant) (stH : Nat) (k : KeyComponent) :
    CompTrace.Preserves OpkNetOK
      (DY.Libsignal.TripleRatchet.exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  cases k with
  | ckr pk =>
    dsimp only
    split
    · exact CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ =>
        OpkNetOK.preserves_sendMessage _
    · exact CompTrace.Preserves.failure
  | _ =>
    exact CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ =>
      OpkNetOK.preserves_sendMessage _

theorem OpkNetOK.preserves_exposeSpqr (me : Participant) (stH : Nat) :
    CompTrace.Preserves OpkNetOK
      (DY.Libsignal.TripleRatchet.exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
  exact OpkNetOK.preserves_sendMessage _

theorem OpkNetOK.preserves_exposeSkipped (evH : Nat) :
    CompTrace.Preserves OpkNetOK
      (DY.Libsignal.TripleRatchet.exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getEntry evH) fun ⟨ev⟩ => ?_
  cases ev with
  | SkippedKeyStored _ _ _ _ _ _ =>
    dsimp only
    refine CompTrace.Preserves.bind (CompTrace.Preserves.guardTrace _) fun _ => ?_
    refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_tr _) fun _ => ?_
    exact OpkNetOK.preserves_sendMessage _
  | _ => exact CompTrace.Preserves.failure

theorem OpkNetOK.preserves_compromiseSPK (b : Participant) (stateIdx : Nat) :
    CompTrace.Preserves OpkNetOK (compromiseSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_getKey b stateIdx .signedPrekey) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_pq _) fun _ => ?_
  exact OpkNetOK.preserves_sendMessage _

theorem OpkNetOK.preserves_compromisePQSPK (b : Participant) (stateIdx : Nat) :
    CompTrace.Preserves OpkNetOK (compromisePQSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_getKey b stateIdx .pqPrekey) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_pq _) fun _ => ?_
  exact OpkNetOK.preserves_sendMessage _

theorem OpkNetOK.preserves_compromiseOPK (b : Participant) (stateIdx : Nat) :
    CompTrace.Preserves OpkNetOK (compromiseOPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_getKey b stateIdx .oneTimePrekey) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_logEvent_pq _) fun _ => ?_
  exact OpkNetOK.preserves_sendMessage _

theorem OpkNetOK.preserves_genOneTimePrekey (b : Participant) :
    CompTrace.Preserves OpkNetOK (genOneTimePrekey b) := by
  intro tr hok
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact opkNetOK_append_opk_net
    (opkNetOK_append_other (opkNetOK_append_other hok (RndE 32) rfl) (PQEvE _) rfl) b _

theorem OpkNetOK.preserves_compromiseIK (p : Participant) (stateIdx : Nat) :
    CompTrace.Preserves OpkNetOK (compromiseIK p stateIdx) := by
  intro tr hok
  unfold DY.Libsignal.PQXDH.compromiseIK
  refine CompTrace.bind_getKey_at p stateIdx .identity tr hok fun sk _ => ?_
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact opkNetOK_append_other (opkNetOK_append_other hok (PQEvE _) rfl) (NetE sk) rfl

/-! ## Model moves preserve `OpkNetOK` -/

theorem OpkNetOK.preserves_setupAct (a b : Participant) (withOpk : Bool) :
    CompTrace.Preserves OpkNetOK (setupAct a b withOpk) := by
  unfold setupAct
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_registerIdentity a) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_registerIdentity b) fun hB => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_genSignedPrekey b hB) fun _ => ?_
  refine CompTrace.Preserves.bind (OpkNetOK.preserves_genPQPrekey b hB) fun _ => ?_
  cases withOpk
  · exact CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.bind (OpkNetOK.preserves_genOneTimePrekey b) fun _ =>
      CompTrace.Preserves.pure _

theorem Move.preserves_opkNetOK (m : Move) : CompTrace.Preserves OpkNetOK m.act := by
  cases m with
  | setup a b withOpk => exact OpkNetOK.preserves_setupAct a b withOpk
  | aliceStart a b idStateIdx regIdxB h _ =>
    exact CompTrace.Preserves.bind (OpkNetOK.preserves_aliceStart a b idStateIdx regIdxB h)
      fun _ => CompTrace.Preserves.pure _
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ =>
    exact CompTrace.Preserves.bind
      (OpkNetOK.preserves_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx)
      fun _ => CompTrace.Preserves.pure _
  | encrypt me stateIdx coinsLen pqIdx _ =>
    exact CompTrace.Preserves.bind (OpkNetOK.preserves_messageEncrypt me stateIdx coinsLen pqIdx)
      fun _ => CompTrace.Preserves.pure _
  | encryptAbort me stateIdx =>
    exact CompTrace.Preserves.bind (OpkNetOK.preserves_messageEncryptAbort me stateIdx)
      fun _ => CompTrace.Preserves.pure _
  | encryptFail me stateIdx coinsLen =>
    exact CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun n =>
      CompTrace.Preserves.bind (OpkNetOK.preserves_messageEncrypt me stateIdx coinsLen (n + 3))
        fun _ => CompTrace.Preserves.pure _
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact CompTrace.Preserves.bind
      (OpkNetOK.preserves_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx)
      fun _ => CompTrace.Preserves.pure _
  | decryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx _ =>
    exact CompTrace.Preserves.bind
      (OpkNetOK.preserves_messageDecryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx)
      fun _ => CompTrace.Preserves.pure _
  | reject _ => exact CompTrace.Preserves.pure _
  | compromiseIK p stateIdx =>
    exact CompTrace.Preserves.bind (OpkNetOK.preserves_compromiseIK p stateIdx)
      fun _ => CompTrace.Preserves.pure _
  | compromiseSPK b stateIdx =>
    exact CompTrace.Preserves.bind (OpkNetOK.preserves_compromiseSPK b stateIdx)
      fun _ => CompTrace.Preserves.pure _
  | compromisePQSPK b stateIdx =>
    exact CompTrace.Preserves.bind (OpkNetOK.preserves_compromisePQSPK b stateIdx)
      fun _ => CompTrace.Preserves.pure _
  | compromiseOPK b stateIdx =>
    exact CompTrace.Preserves.bind (OpkNetOK.preserves_compromiseOPK b stateIdx)
      fun _ => CompTrace.Preserves.pure _
  | exposeKey me stateIdx k =>
    exact CompTrace.Preserves.bind (OpkNetOK.preserves_exposeKey me stateIdx k)
      fun _ => CompTrace.Preserves.pure _
  | exposeSpqr me stateIdx =>
    exact CompTrace.Preserves.bind (OpkNetOK.preserves_exposeSpqr me stateIdx)
      fun _ => CompTrace.Preserves.pure _
  | exposeSkipped evIdx =>
    exact CompTrace.Preserves.bind (OpkNetOK.preserves_exposeSkipped evIdx)
      fun _ => CompTrace.Preserves.pure _
  | attackerSend msg =>
    exact CompTrace.Preserves.bind (OpkNetOK.preserves_sendMessage msg)
      fun _ => CompTrace.Preserves.pure _
  | brkDH =>
    exact OpkNetOK.preserves_logEvent_pq .BrokenDH
  | brkKEM =>
    exact OpkNetOK.preserves_logEvent_pq .BrokenKEM

theorem OpkNetOK.next {tr : ExecTrace} (m : Move) (h : OpkNetOK tr) : OpkNetOK (m.next tr) :=
  Move.preserves_opkNetOK m tr h

/-! ## `bobOpkPk` is attacker-known -/

theorem pqxdhStoredAt_of_getKey {me : Participant} {i : Nat} {kind : KeyKind} {tr : ExecTrace}
    {sk : Bytes} (h : ((getKey me i kind).run tr).1 = some sk) :
    PQXDHStoredAt tr me { kind, sk } i := by
  unfold DY.Libsignal.PQXDH.getKey at h
  rw [run_bind_fst, getLocalState_pq_fst, getLocalState_pq_snd] at h
  unfold PQXDHStoredAt
  rcases he : (tr.at? i : Option PQXDHStEntry) with _ | ⟨⟨p, st⟩⟩
  · rw [he] at h; cases h
  · rw [he] at h
    dsimp only at h
    by_cases hp : p = me
    · subst hp
      simp only [↓reduceIte, _root_.guard, run_bind_fst] at h
      by_cases hk : st.kind = kind
      · rcases st with ⟨k, s⟩
        simp only at hk
        subst hk
        simp only [↓reduceIte, DY.Traceful.run_pure, Option.some.injEq] at h
        subst h
        rfl
      · simp only [hk, ↓reduceIte, DY.Traceful.run_failure, reduceCtorEq] at h
    · simp only [hp, ↓reduceIte] at h
      cases h

/-- Under `OpkNetOK tr`, the one-time prekey public key returned by `bobOpkPk` is attacker-known. -/
theorem bobOpkPk_known {b : Participant} {h : BobKeyHandles} {tr : ExecTrace} {t : Bytes}
    (hs : OpkNetOK tr) (ht : t ∈ (bobOpkPk b h tr).toList) : t.AttackerKnows tr := by
  unfold bobOpkPk at ht
  rcases hopk : h.opk with _ | i
  · rw [hopk] at ht; cases ht
  · rw [hopk] at ht
    rcases hk : ((getKey b i .oneTimePrekey).run tr).1 with _ | sk
    · simp only [Option.bind_some, hk, Option.map_none] at ht; cases ht
    · simp only [Option.bind_some, hk, Option.map_some, Option.mem_toList,
        Option.some.injEq] at ht
      subst ht
      obtain ⟨j, hj⟩ := hs b sk i (pqxdhStoredAt_of_getKey hk)
      exact hj.attackerKnows

end DY.Libsignal.Composed.Refinement
