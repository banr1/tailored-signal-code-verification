/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
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
# Compromised Identity-Key Network and Publicness Invariants

Defines `CikNetOK` (every logged `CompromisedIK p ik` event has `ik = dhPk s` for some `s` sent on
the network) and proves `cikNetOK_of_reachable` by induction over `Composed.reachability` without
assuming `SpqrInv`. Combines `CikNetOK` with `SpqrInv.netPub` to establish `CikOK` and `cik_pub`
on reachable traces (`cikOK_of_reachable`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompInv

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.PQKem DY.Signature DY.X25519
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed
open Symbolic.Swarm.COMPOSED.CompKeyInversion
open Symbolic.Swarm.COMPOSED.CompTrace

/-! ## `CikOK` and `CikNetOK` definitions and single-step lemmas -/

/-- Every `CompromisedIK p ik` event on `tr` has `ik = dhPk s` for some `Pub tr s`. -/
def CikOK (tr : ExecTrace) : Prop :=
  ∀ p ik r,
    tr.EventLoggedAt (PQXDHEvent.CompromisedIK p ik) r →
    ∃ s, Pub tr s ∧ ik = DiffieHellman.dhPk s

/-- Every `CompromisedIK p ik` event on `tr` has `ik = dhPk s` for some `s` on the network. -/
def CikNetOK (tr : ExecTrace) : Prop :=
  ∀ p ik r,
    tr.EventLoggedAt (PQXDHEvent.CompromisedIK p ik) r →
    ∃ s idx, NetAt tr s idx ∧ ik = DiffieHellman.dhPk s

theorem cikOK_of_cikNetOK {tr : ExecTrace} (hnet : CikNetOK tr) (hinv : SpqrInv tr) :
    CikOK tr := by
  intro p ik r hev
  obtain ⟨s, idx, hs_net, hik⟩ := hnet p ik r hev
  exact ⟨s, hinv.netPub s (CompTrace.NetMsgAt.baseAttackerKnows hs_net), hik⟩

theorem cikNetOK_nil : CikNetOK (Trace.nil : ExecTrace) :=
  fun _ _ _ h => (eventLoggedAt_nil h).elim

theorem cikNetOK_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} (hcik : CikNetOK tr)
    (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option EvEntry) = none) :
    CikNetOK (tr.append e) := by
  have hle : tr ≤ tr.append e := Trace.append_le tr e
  intro p ik r hev
  obtain ⟨s, idx, hs, hik⟩ := hcik p ik r (CompTrace.eventLoggedAt_append_other hnone hev)
  exact ⟨s, idx, hs.mono hle, hik⟩

theorem cikNetOK_append_ev_nonCik {tr : ExecTrace} (hcik : CikNetOK tr) {ev : PQXDHEvent}
    (hno_cik : ∀ p ik, ev ≠ PQXDHEvent.CompromisedIK p ik) :
    CikNetOK (tr.append (EvE ev)) := by
  have hle : tr ≤ tr.append (EvE ev) := Trace.append_le tr (EvE ev)
  intro p ik r hev
  rcases CompTrace.eventLoggedAt_append_same hev with ⟨_, hev0⟩ | ⟨_, hEq⟩
  · obtain ⟨s, idx, hs, hik⟩ := hcik p ik r hev0
    exact ⟨s, idx, hs.mono hle, hik⟩
  · exact False.elim (hno_cik p ik hEq)

theorem cikNetOK_append_irCorrupt {tr : ExecTrace} (hcik : CikNetOK tr)
    (p : Participant) {sk : Bytes} {skIdx : Nat} (hnet : NetAt tr sk skIdx) :
    CikNetOK
      ((tr.append (EvE (PQXDHEvent.IdentityRegistered p (DiffieHellman.dhPk sk) (Signature.vk sk) false))).append
        (EvE (PQXDHEvent.CompromisedIK p (DiffieHellman.dhPk sk)))) := by
  have hle1 : tr ≤ tr.append (EvE (PQXDHEvent.IdentityRegistered p (DiffieHellman.dhPk sk) (Signature.vk sk) false)) :=
    Trace.append_le tr _
  have hle2 :
      tr.append (EvE (PQXDHEvent.IdentityRegistered p (DiffieHellman.dhPk sk) (Signature.vk sk) false)) ≤
      (tr.append (EvE (PQXDHEvent.IdentityRegistered p (DiffieHellman.dhPk sk) (Signature.vk sk) false))).append
        (EvE (PQXDHEvent.CompromisedIK p (DiffieHellman.dhPk sk))) :=
    Trace.append_le _ _
  have hle := Trace.le_trans _ _ _ hle1 hle2
  intro p' ik' r hev
  rcases CompTrace.eventLoggedAt_append_same hev with ⟨_, hev1⟩ | ⟨_, hEq⟩
  · rcases CompTrace.eventLoggedAt_append_same hev1 with ⟨_, hev0⟩ | ⟨_, hEq⟩
    · obtain ⟨s, idx, hs, hik⟩ := hcik p' ik' r hev0
      exact ⟨s, idx, hs.mono hle, hik⟩
    · cases hEq
  · cases hEq
    exact ⟨sk, skIdx, hnet.mono hle, rfl⟩

theorem cikNetOK_append_compromiseIK {tr : ExecTrace} (hcik : CikNetOK tr)
    (p : Participant) (sk : Bytes) :
    CikNetOK ((tr.append (EvE (PQXDHEvent.CompromisedIK p (DiffieHellman.dhPk sk)))).append (NetE sk)) := by
  let tr1 := tr.append (EvE (PQXDHEvent.CompromisedIK p (DiffieHellman.dhPk sk)))
  have hle1 : tr ≤ tr1 := Trace.append_le tr _
  have hle2 : tr1 ≤ tr1.append (NetE sk) := Trace.append_le tr1 (NetE sk)
  have hle : tr ≤ tr1.append (NetE sk) := Trace.le_trans _ _ _ hle1 hle2
  have hnet_sk : NetAt (tr1.append (NetE sk)) sk tr1.length :=
    Trace.at?_append tr1 (NetE sk)
  intro p' ik' r hev
  have hev1 : tr1.EventLoggedAt (PQXDHEvent.CompromisedIK p' ik') r :=
    CompTrace.eventLoggedAt_append_other (e := NetE sk) rfl hev
  rcases CompTrace.eventLoggedAt_append_same hev1 with ⟨_, hev0⟩ | ⟨_, hEq⟩
  · obtain ⟨s, idx, hs, hik⟩ := hcik p' ik' r hev0
    exact ⟨s, idx, hs.mono hle, hik⟩
  · cases hEq
    exact ⟨sk, tr1.length, hnet_sk, rfl⟩

/-! ## Preservation across protocol transitions -/

theorem CikNetOK.preserves_sendMessage (msg : Bytes) :
    CompTrace.Preserves CikNetOK (Network.sendMessage msg) := by
  intro tr hcik
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_mk]
  exact cikNetOK_append_other hcik (NetE msg) rfl

theorem CikNetOK.preserves_genRand (n : Nat) :
    CompTrace.Preserves CikNetOK (Random.genRand n) := by
  intro tr hcik
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact cikNetOK_append_other hcik (RndE n) rfl

theorem CikNetOK.preserves_storeLocalState_pq (me : Participant) (st : PQXDHState) :
    CompTrace.Preserves CikNetOK (PersistentLocalState.storeLocalState me st) := by
  intro tr hcik
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact cikNetOK_append_other hcik (StE me st) rfl

theorem CikNetOK.preserves_storeLocalState_tr (me : Participant) (st : TRState) :
    CompTrace.Preserves CikNetOK (PersistentLocalState.storeLocalState me st) := by
  intro tr hcik
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact cikNetOK_append_other hcik (TRStE me st) rfl

theorem CikNetOK.preserves_logEvent_tr (ev : TREvent) :
    CompTrace.Preserves CikNetOK (ProtocolEvent.logEvent ev) := by
  intro tr hcik
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact cikNetOK_append_other hcik (TREvE ev) rfl

theorem CikNetOK.preserves_logEvent_c (ev : ComposedEvent) :
    CompTrace.Preserves CikNetOK (ProtocolEvent.logEvent ev) := by
  intro tr hcik
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact cikNetOK_append_other hcik (CEvE ev) rfl

theorem CikNetOK.preserves_logEvent_pq_nonCik (ev : PQXDHEvent)
    (hno : ∀ p ik, ev ≠ PQXDHEvent.CompromisedIK p ik) :
    CompTrace.Preserves CikNetOK (ProtocolEvent.logEvent ev) := by
  intro tr hcik
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact cikNetOK_append_ev_nonCik hcik hno

theorem CikNetOK.preserves_getKey (p : Participant) (stateIdx : Nat) (kind : KeyKind) :
    CompTrace.Preserves CikNetOK (DY.Libsignal.PQXDH.getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p stateIdx) fun _ => ?_
  exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _

theorem CikNetOK.preserves_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : Bytes) (counter : UInt32)
    (rIdx childStateIdx : Nat) (st : TRState) :
    CompTrace.Preserves CikNetOK
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt counter rIdx childStateIdx st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
  exact CikNetOK.preserves_storeLocalState_tr me st

theorem CikNetOK.preserves_logSkippedKeys (s : SessionInfo) (ratchetKey : Bytes)
    (rIdx sourceStateIdx : Nat) :
    ∀ (count : Nat) (ck : Bytes) (idx : UInt32),
      CompTrace.Preserves CikNetOK
        (DY.Libsignal.TripleRatchet.logSkippedKeys s ratchetKey rIdx sourceStateIdx ck idx count)
  | 0, _, _ => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    exact CompTrace.Preserves.pure ()
  | count + 1, ck, idx => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
    exact CikNetOK.preserves_logSkippedKeys s ratchetKey rIdx sourceStateIdx count (kdfCk ck).1 (idx + 1)

theorem CikNetOK.preserves_dhRatchetStep (st : TRState) (peerRatchetKey : Bytes) :
    CompTrace.Preserves CikNetOK (DY.Libsignal.TripleRatchet.dhRatchetStep st peerRatchetKey) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_genRand 32) fun _ => ?_
  exact CompTrace.Preserves.pure _

theorem CikNetOK.preserves_ensureReceiverChain (st : TRState) (peerRatchetKey : Bytes) :
    CompTrace.Preserves CikNetOK (DY.Libsignal.TripleRatchet.ensureReceiverChain st peerRatchetKey) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact CompTrace.Preserves.pure _
  · refine CompTrace.Preserves.bind (CikNetOK.preserves_dhRatchetStep st peerRatchetKey) fun ⟨_, _⟩ => ?_
    exact CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.failure

theorem CikNetOK.preserves_registerIdentity (p : Participant) :
    CompTrace.Preserves CikNetOK (registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_pq_nonCik _ (by intro _ _ h; cases h)) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_sendMessage _) fun _ => ?_
  exact CikNetOK.preserves_storeLocalState_pq p _

theorem CikNetOK.preserves_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    CompTrace.Preserves CikNetOK (registerCorruptIdentity p skIdx) := by
  intro tr hcik
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
    DY.Libsignal.PQXDH.guardTrace
  rw [CompTrace.run_bind_snd, Traceful.run_mk]
  dsimp only
  split
  · refine CompTrace.bind_receiveMessage_at skIdx tr hcik fun sk hnet _ => ?_
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
    exact cikNetOK_append_irCorrupt hcik p hnet
  · exact hcik

theorem CikNetOK.preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    CompTrace.Preserves CikNetOK (genSignedPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine CompTrace.Preserves.bind (CikNetOK.preserves_getKey b idStateIdx .identity) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_pq_nonCik _ (by intro _ _ h; cases h)) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_storeLocalState_pq b _) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.pure _

theorem CikNetOK.preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    CompTrace.Preserves CikNetOK (genPQPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine CompTrace.Preserves.bind (CikNetOK.preserves_getKey b idStateIdx .identity) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_pq_nonCik _ (by intro _ _ h; cases h)) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_storeLocalState_pq b _) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.pure _

theorem CikNetOK.preserves_genOneTimePrekey (b : Participant) :
    CompTrace.Preserves CikNetOK (genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine CompTrace.Preserves.bind (CikNetOK.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_pq_nonCik _ (by intro _ _ h; cases h)) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_storeLocalState_pq b _) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.pure _

theorem CikNetOK.preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) :
    CompTrace.Preserves CikNetOK (aliceStart a b idStateIdx regIdxB bh) := by
  intro tr hcik
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine CompTrace.bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hcik
    (cikNetOK_append_other hcik (RndE 32) rfl) ?_
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hcik2 : CikNetOK ((tr.append (RndE 32)).append (RndE 32)) :=
    cikNetOK_append_other (cikNetOK_append_other hcik (RndE 32) rfl) (RndE 32) rfl
  refine (show CompTrace.Preserves CikNetOK _ by
    refine CompTrace.Preserves.bind (CikNetOK.preserves_genRand 32) fun _ => ?_
    refine CompTrace.Preserves.bind (CikNetOK.preserves_sendMessage _) fun _ => ?_
    refine CompTrace.Preserves.bind (CikNetOK.preserves_sendMessage _) fun _ => ?_
    refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
    refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_pq_nonCik _ (by intro _ _ h; cases h)) fun _ => ?_
    refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
    refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_c _) fun _ => ?_
    exact CikNetOK.preserves_storeLocalState_tr a _) _ hcik2

theorem CikNetOK.preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    CompTrace.Preserves CikNetOK (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr hcik
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hcik ?_
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  refine (show CompTrace.Preserves CikNetOK _ by
    refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveSignalMsg mh.msg) fun _ => ?_
    refine CompTrace.Preserves.bind (CikNetOK.preserves_ensureReceiverChain _ _) fun ⟨_, _, _⟩ => ?_
    dsimp only
    split
    · split
      · refine CompTrace.Preserves.bind (CikNetOK.preserves_sendMessage _) fun _ => ?_
        refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
        refine CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
        split
        · refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => ?_
          refine CompTrace.Preserves.bind
            (CikNetOK.preserves_logEvent_pq_nonCik _ (by intro _ _ h; cases h)) fun _ => ?_
          refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
          refine CompTrace.Preserves.bind
            (CikNetOK.preserves_logEvent_pq_nonCik _ (by intro _ _ h; cases h)) fun _ => ?_
          split
          · refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
            refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
            refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_c _) fun _ => ?_
            refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
            refine CompTrace.Preserves.bind (CikNetOK.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
            refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
            exact CikNetOK.preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _
          · refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_c _) fun _ => ?_
            refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
            refine CompTrace.Preserves.bind (CikNetOK.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
            refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
            exact CikNetOK.preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _
        · refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
          refine CompTrace.Preserves.bind
            (CikNetOK.preserves_logEvent_pq_nonCik _ (by intro _ _ h; cases h)) fun _ => ?_
          split
          · refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
            refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
            refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_c _) fun _ => ?_
            refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
            refine CompTrace.Preserves.bind (CikNetOK.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
            refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
            exact CikNetOK.preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _
          · refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_c _) fun _ => ?_
            refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
            refine CompTrace.Preserves.bind (CikNetOK.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
            refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
            exact CikNetOK.preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _
      · exact CompTrace.Preserves.failure
    · exact CompTrace.Preserves.failure) _ hcik

theorem CikNetOK.preserves_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat) :
    CompTrace.Preserves CikNetOK
      (DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_genRand coinsLen) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_logMessageKeyAndStore me _ .sender _ _ _ _ _ _) fun _ => ?_
  exact CikNetOK.preserves_sendMessage _

theorem CikNetOK.preserves_messageEncryptAbort (me : Participant) (stH : Nat) :
    CompTrace.Preserves CikNetOK
      (DY.Libsignal.TripleRatchet.messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_genRand 32) fun _ => ?_
  exact CompTrace.Preserves.failure

theorem CikNetOK.preserves_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    CompTrace.Preserves CikNetOK
      (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveSignalMsg msgH) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_ensureReceiverChain _ _) fun ⟨_, _, _⟩ => ?_
  dsimp only
  split
  · split
    · refine CompTrace.Preserves.bind (CikNetOK.preserves_sendMessage _) fun _ => ?_
      refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
      refine CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
      split
      · refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
        refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
        refine CompTrace.Preserves.bind (CikNetOK.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
        refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
        exact CikNetOK.preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
      · refine CompTrace.Preserves.bind (CikNetOK.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
        refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
        exact CikNetOK.preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact CompTrace.Preserves.failure
  · exact CompTrace.Preserves.failure

theorem CikNetOK.preserves_messageDecryptSkipped (me : Participant)
    (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    CompTrace.Preserves CikNetOK
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
    · refine CompTrace.Preserves.bind (CikNetOK.preserves_sendMessage _) fun _ => ?_
      refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
      refine CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
      refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
      refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
      exact CikNetOK.preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact CompTrace.Preserves.failure
  | _ => exact CompTrace.Preserves.failure

theorem CikNetOK.preserves_exposeKey (me : Participant) (stH : Nat) (k : KeyComponent) :
    CompTrace.Preserves CikNetOK
      (DY.Libsignal.TripleRatchet.exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  cases k with
  | ckr pk =>
    dsimp only
    split
    · exact CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ =>
        CikNetOK.preserves_sendMessage _
    · exact CompTrace.Preserves.failure
  | _ =>
    exact CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ =>
      CikNetOK.preserves_sendMessage _

theorem CikNetOK.preserves_exposeSpqr (me : Participant) (stH : Nat) :
    CompTrace.Preserves CikNetOK
      (DY.Libsignal.TripleRatchet.exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
  exact CikNetOK.preserves_sendMessage _

theorem CikNetOK.preserves_exposeSkipped (evH : Nat) :
    CompTrace.Preserves CikNetOK
      (DY.Libsignal.TripleRatchet.exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getEntry evH) fun ⟨ev⟩ => ?_
  cases ev with
  | SkippedKeyStored _ _ _ _ _ _ =>
    dsimp only
    refine CompTrace.Preserves.bind (CompTrace.Preserves.guardTrace _) fun _ => ?_
    refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_tr _) fun _ => ?_
    exact CikNetOK.preserves_sendMessage _
  | _ => exact CompTrace.Preserves.failure

theorem CikNetOK.preserves_compromiseIK (p : Participant) (stateIdx : Nat) :
    CompTrace.Preserves CikNetOK (compromiseIK p stateIdx) := by
  intro tr hcik
  unfold DY.Libsignal.PQXDH.compromiseIK
  refine CompTrace.bind_getKey_at p stateIdx .identity tr hcik fun sk _ => ?_
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact cikNetOK_append_compromiseIK hcik p sk

theorem CikNetOK.preserves_compromiseSPK (b : Participant) (stateIdx : Nat) :
    CompTrace.Preserves CikNetOK (compromiseSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  refine CompTrace.Preserves.bind (CikNetOK.preserves_getKey b stateIdx .signedPrekey) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_pq_nonCik _ (by intro _ _ h; cases h)) fun _ => ?_
  exact CikNetOK.preserves_sendMessage _

theorem CikNetOK.preserves_compromisePQSPK (b : Participant) (stateIdx : Nat) :
    CompTrace.Preserves CikNetOK (compromisePQSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  refine CompTrace.Preserves.bind (CikNetOK.preserves_getKey b stateIdx .pqPrekey) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_pq_nonCik _ (by intro _ _ h; cases h)) fun _ => ?_
  exact CikNetOK.preserves_sendMessage _

theorem CikNetOK.preserves_compromiseOPK (b : Participant) (stateIdx : Nat) :
    CompTrace.Preserves CikNetOK (compromiseOPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  refine CompTrace.Preserves.bind (CikNetOK.preserves_getKey b stateIdx .oneTimePrekey) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => ?_
  refine CompTrace.Preserves.bind (CikNetOK.preserves_logEvent_pq_nonCik _ (by intro _ _ h; cases h)) fun _ => ?_
  exact CikNetOK.preserves_sendMessage _

theorem CikNetOK.preserves_breakDH :
    CompTrace.Preserves CikNetOK breakDH :=
  CikNetOK.preserves_logEvent_pq_nonCik _ (by intro _ _ h; cases h)

theorem CikNetOK.preserves_breakKEM :
    CompTrace.Preserves CikNetOK breakKEM :=
  CikNetOK.preserves_logEvent_pq_nonCik _ (by intro _ _ h; cases h)

theorem CikNetOK.preserves_invertDH (msgIdx : Nat) :
    CompTrace.Preserves CikNetOK (invertDH msgIdx) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage msgIdx) fun _ => ?_
  split
  · exact CikNetOK.preserves_sendMessage _
  · exact CompTrace.Preserves.failure

theorem CikNetOK.preserves_invertKEM (msgIdx : Nat) :
    CompTrace.Preserves CikNetOK (invertKEM msgIdx) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage msgIdx) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.monadLiftErr _) fun _ => ?_
  exact CikNetOK.preserves_sendMessage _

/-- Every trace reachable under `Composed.reachability` satisfies `CikNetOK`. -/
theorem cikNetOK_of_reachable {tr : ExecTrace}
    (hReach : tr.Reachable DY.Libsignal.Composed.reachability) :
    CikNetOK tr :=
  CompTrace.composed_reachable_induction
    cikNetOK_nil
    (fun msg _ _ hcik => cikNetOK_append_other hcik (NetE msg) rfl)
    CikNetOK.preserves_registerIdentity
    CikNetOK.preserves_registerCorruptIdentity
    CikNetOK.preserves_genSignedPrekey
    CikNetOK.preserves_genPQPrekey
    CikNetOK.preserves_genOneTimePrekey
    CikNetOK.preserves_aliceStart
    CikNetOK.preserves_bobStart
    CikNetOK.preserves_messageEncrypt
    CikNetOK.preserves_messageEncryptAbort
    CikNetOK.preserves_messageDecrypt
    CikNetOK.preserves_messageDecryptSkipped
    CikNetOK.preserves_exposeKey
    CikNetOK.preserves_exposeSpqr
    CikNetOK.preserves_exposeSkipped
    CikNetOK.preserves_compromiseIK
    CikNetOK.preserves_compromiseSPK
    CikNetOK.preserves_compromisePQSPK
    CikNetOK.preserves_compromiseOPK
    CikNetOK.preserves_breakDH
    CikNetOK.preserves_breakKEM
    CikNetOK.preserves_invertDH
    CikNetOK.preserves_invertKEM
    hReach

/-- Every reachable `SpqrInv` trace satisfies `CikOK`. -/
theorem cikOK_of_reachable {tr : ExecTrace}
    (hReach : tr.Reachable DY.Libsignal.Composed.reachability)
    (hinv : SpqrInv tr) : CikOK tr :=
  cikOK_of_cikNetOK (cikNetOK_of_reachable hReach) hinv

theorem cik_pub {tr : ExecTrace} (_hinv : SpqrInv tr) (hcik : CikOK tr)
    {p : Participant} {ik : Bytes} {r : Nat}
    (h : tr.EventLoggedAt (PQXDHEvent.CompromisedIK p ik) r) :
    ∃ s, Pub tr s ∧ ik = DiffieHellman.dhPk s :=
  hcik p ik r h

end Symbolic.Swarm.COMPOSED.CompInv
