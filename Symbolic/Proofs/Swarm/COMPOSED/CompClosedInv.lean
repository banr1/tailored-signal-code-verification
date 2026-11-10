/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompTightClosed
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.COMPOSED.CompPresBob
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompLineage
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
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

/-!
# Reachable-Trace Attacker-Knowledge Closure (`CompClosedInv`)

Defines `CompClosedInv`, pairing `CompTightClosed` closure of base network messages and stored
SPQR states, and proves its preservation across all transitions of `Composed.reachability`
(`compClosedInv_of_reachable`). Concludes that every attacker-known term on a reachable trace lies
in `CompTrClosed (CompStructuredExposure tr)` (`attackerKnows_implies_compTrClosed`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompRatchet

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir RecvChain KeyComponent createChain kdfCk
  findRecvChain setRecvChain recvChainFor consumeMessageKey x25519LowOrder maxReceiverChains
  computeMac)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles
  PreKeyMsgHandles guardTrace opkUsedB registerIdentity registerCorruptIdentity genSignedPrekey
  genPQPrekey genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK compromiseOPK breakDH
  breakKEM invertDH invertKEM)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg trMsgKeys spqrA2B parseTrSignalMsg
  receiveSignalMsg ensureReceiverChain dhRatchetStep verifyMacAndDecrypt logSkippedKeys
  logMessageKeyAndStore messageEncrypt messageEncryptAbort messageDecrypt messageDecryptSkipped
  exposeKey exposeSpqr exposeSkipped traceLength)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompKeyInversion

/-! ## `CompClosedInv` and single-entry preservation -/

open Symbolic.Swarm.COMPOSED.CompInv

/-- Trace invariant asserting `CompTightClosed tr` for every base attacker-known message and every
stored `TRState.spqr` state. -/
structure CompClosedInv (tr : ExecTrace) : Prop where
  baseClosed : ∀ b, tr.BaseAttackerKnows b → CompTightClosed tr b
  spqrClosed : ∀ me st idx, TRStoredAt tr me st idx → CompTightClosed tr st.spqr

theorem compClosedInv_nil : CompClosedInv Trace.nil :=
  { baseClosed := fun _ h => by
      rw [Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1] at h
      exact False.elim h
    spqrClosed := fun _ _ idx h => by simp [TRStoredAt, Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at h }

theorem CompClosedInv.of_attackerKnows {tr : ExecTrace} (hc : CompClosedInv tr)
    {b : Bytes} (hk : b.AttackerKnows tr) : CompTightClosed tr b :=
  CompTightClosed.of_attackerKnows hc.baseClosed hk

theorem CompClosedInv.append_rnd {tr : ExecTrace} (hc : CompClosedInv tr) (n : Nat) :
    CompClosedInv (tr.append (RndE n)) := by
  have hle : tr ≤ tr.append (RndE n) := Trace.append_le tr (RndE n)
  refine ⟨fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_rnd tr n b).mp hb)).mono hle,
    fun me st idx hst => (hc.spqrClosed me st idx
      (Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CompClosedInv.append_ev {tr : ExecTrace} (hc : CompClosedInv tr) (ev : PQXDHEvent) :
    CompClosedInv (tr.append (EvE ev)) := by
  have hle : tr ≤ tr.append (EvE ev) := Trace.append_le tr (EvE ev)
  refine ⟨fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_pqEv tr ev b).mp hb)).mono hle,
    fun me st idx hst => (hc.spqrClosed me st idx
      (Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CompClosedInv.append_trEv {tr : ExecTrace} (hc : CompClosedInv tr) (ev : TREvent) :
    CompClosedInv (tr.append (TREvE ev)) := by
  have hle : tr ≤ tr.append (TREvE ev) := Trace.append_le tr (TREvE ev)
  refine ⟨fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_trEv tr ev b).mp hb)).mono hle,
    fun me st idx hst => (hc.spqrClosed me st idx
      (Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CompClosedInv.append_cEv {tr : ExecTrace} (hc : CompClosedInv tr) (ev : ComposedEvent) :
    CompClosedInv (tr.append (CEvE ev)) := by
  have hle : tr ≤ tr.append (CEvE ev) := Trace.append_le tr (CEvE ev)
  refine ⟨fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_cEv tr ev b).mp hb)).mono hle,
    fun me st idx hst => (hc.spqrClosed me st idx
      (Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CompClosedInv.append_st {tr : ExecTrace} (hc : CompClosedInv tr)
    (me : Participant) (st : PQXDHState) :
    CompClosedInv (tr.append (StE me st)) := by
  have hle : tr ≤ tr.append (StE me st) := Trace.append_le tr (StE me st)
  refine ⟨fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_pqSt tr me st b).mp hb)).mono hle,
    fun me' st' idx hst => (hc.spqrClosed me' st' idx
      (Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CompClosedInv.append_net {tr : ExecTrace} (hc : CompClosedInv tr) {msg : Bytes}
    (hmsg : CompTightClosed (tr.append (NetE msg)) msg) :
    CompClosedInv (tr.append (NetE msg)) := by
  have hle : tr ≤ tr.append (NetE msg) := Trace.append_le tr (NetE msg)
  refine ⟨fun b hb => ?_, fun me st idx hst => ?_⟩
  · rcases (CompTrace.baseAttackerKnows_append_net tr msg b).mp hb with rfl | hb'
    · exact hmsg
    · exact (hc.baseClosed b hb').mono hle
  · exact (hc.spqrClosed me st idx
      (Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle

theorem CompClosedInv.append_net_of_closed {tr : ExecTrace} (hc : CompClosedInv tr) {msg : Bytes}
    (hmsg : CompTightClosed tr msg) :
    CompClosedInv (tr.append (NetE msg)) :=
  hc.append_net (hmsg.mono (Trace.append_le tr (NetE msg)))

theorem CompClosedInv.append_net_rnd {tr : ExecTrace} (hc : CompClosedInv tr) (t n : Nat) :
    CompClosedInv (tr.append (NetE (mkRand t n))) := by
  refine hc.append_net (.exposed (.rand (.inl ?_)))
  exact Bytes.AttackerKnows.prove_from_base (mkRand t n) (tr.append (NetE (mkRand t n)))
    ((CompTrace.baseAttackerKnows_append_net tr (mkRand t n) (mkRand t n)).mpr (.inl rfl))

theorem CompClosedInv.append_trSt {tr : ExecTrace} (hc : CompClosedInv tr)
    {me : Participant} {st : TRState} (hspqr : CompTightClosed tr st.spqr) :
    CompClosedInv (tr.append (TRStE me st)) := by
  have hle : tr ≤ tr.append (TRStE me st) := Trace.append_le tr (TRStE me st)
  refine ⟨fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_trSt tr me st b).mp hb)).mono hle,
    fun me' st' idx hst => ?_⟩
  rcases Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.trStoredAt_append_same hst with
    ⟨_, hst'⟩ | ⟨_, _, rfl⟩
  · exact (hc.spqrClosed me' st' idx hst').mono hle
  · exact hspqr.mono hle

theorem CompClosedInv.logSkippedKeys_preserves (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : Bytes) (n : UInt32) (tr : ExecTrace),
      CompClosedInv tr →
      CompClosedInv ((logSkippedKeys s pk rIdx src ck n k).run tr).2.val
  | 0, _, _, _, hc => by rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc
  | k + 1, ck, n, tr, hc => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    exact CompClosedInv.logSkippedKeys_preserves s pk rIdx src k (kdfCk ck).1 (n + 1) _
      (hc.append_trEv _)

theorem CompClosedInv.append_logMessageKeyAndStore {tr : ExecTrace} (hc : CompClosedInv tr)
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (seed pqSalt : Bytes)
    (n : UInt32) (rIdx prev : Nat) (st : TRState) (hspqr : CompTightClosed tr st.spqr) :
    CompClosedInv ((logMessageKeyAndStore me s dir seed pqSalt n rIdx prev st).run tr).2.val := by
  rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logMessageKeyAndStore_snd]
  exact (hc.append_trEv _).append_trSt (hspqr.mono (Trace.append_le tr _))

/-! ## Preservation across protocol transitions -/

open Symbolic.Swarm.COMPOSED.CompPresPQXDH

theorem closed_preserves_net (msg : Bytes) (tr : ExecTrace) (hPre : msg.AttackerKnows tr)
    (hc : CompClosedInv tr) : CompClosedInv ((Network.sendMessage msg).run tr).2.val := by
  rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
  exact hc.append_net_of_closed (hc.of_attackerKnows hPre)

theorem closed_preserves_registerIdentity (p : Participant) (tr : ExecTrace)
    (hc : CompClosedInv tr) : CompClosedInv ((registerIdentity p).run tr).2.val := by
  unfold registerIdentity
  refine bind_guardOnTrace_at _ tr hc fun _ => ?_
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact ((((hc.append_rnd 32).append_ev _).append_net_of_closed
    (.dhPkRand ⟨tr.length, 32, rfl⟩)).append_net_of_closed (.vk _)).append_st p _

theorem closed_preserves_registerCorruptIdentity (p : Participant) (skIdx : Nat) (tr : ExecTrace)
    (hc : CompClosedInv tr) : CompClosedInv ((registerCorruptIdentity p skIdx).run tr).2.val := by
  unfold registerCorruptIdentity
  refine bind_guardOnTrace_at _ tr hc fun _ => ?_
  refine bind_receiveMessage_at skIdx tr hc fun _ _ _ => ?_
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact (hc.append_ev _).append_ev _

theorem closed_preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) (tr : ExecTrace)
    (hc : CompClosedInv tr) : CompClosedInv ((genSignedPrekey b idStateIdx).run tr).2.val := by
  unfold genSignedPrekey
  refine bind_getKey_at b idStateIdx .identity tr hc fun _ _ => ?_
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact (((((hc.append_rnd 32).append_rnd 64).append_ev _).append_st b _).append_net_of_closed
    (.dhPkRand ⟨tr.length, 32, rfl⟩)).append_net_of_closed (.sign _ _ _)

theorem closed_preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) (tr : ExecTrace)
    (hc : CompClosedInv tr) : CompClosedInv ((genPQPrekey b idStateIdx).run tr).2.val := by
  unfold genPQPrekey
  refine bind_getKey_at b idStateIdx .identity tr hc fun _ _ => ?_
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact (((((hc.append_rnd 64).append_rnd 64).append_ev _).append_st b _).append_net_of_closed
    (.kemPkRand ⟨tr.length, 64, rfl⟩)).append_net_of_closed (.sign _ _ _)

theorem closed_preserves_genOneTimePrekey (b : Participant) (tr : ExecTrace)
    (hc : CompClosedInv tr) : CompClosedInv ((genOneTimePrekey b).run tr).2.val := by
  unfold genOneTimePrekey
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact (((hc.append_rnd 32).append_ev _).append_st b _).append_net_of_closed
    (.dhPkRand ⟨tr.length, 32, rfl⟩)

theorem closed_preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) (tr : ExecTrace) (hc : CompClosedInv tr) :
    CompClosedInv ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hc (hc.append_rnd 32)
    fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ => ?_
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    DY.Libsignal.TripleRatchet.traceLength,
    Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  let hs := aliceOut tr ikA ikBPk spkPk pqPk opk
  let tr1 := tr.append (RndE 32)
  let tr2 := tr1.append (RndE 32)
  let dhsA := rnd tr2.length 32
  let rkA := (createChain hs.keys.rk hs.spk dhsA).1
  let cksA := (createChain hs.keys.rk hs.spk dhsA).2
  let stA : TRState :=
    { peer := b, myIk := DY.Libsignal.PQXDH.serializedIk hs.ikA,
      peerIk := DY.Libsignal.PQXDH.serializedIk hs.ikB,
      rk := rkA, dhs := dhsA, cks := cksA, ns := 0, pn := 0,
      sid := Concat.concat (DiffieHellman.dhPk dhsA) hs.keys.rk,
      initiator := true, rIdx := 1,
      recv := [{ ratchetKey := hs.spk, chainKey := hs.keys.ck, index := 0, rIdx := 1 }],
      spqr := Spqr.spqrInit hs.keys.pqr spqrA2B }
  let tr3 := tr2.append (RndE 32); let tr4 := tr3.append (NetE hs.ek)
  let tr5 := tr4.append (NetE hs.ct)
  let tr6 := tr5.append (EvE (PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys))
  let tr7 := tr6.append (TREvE (TREvent.InitSession a b (DiffieHellman.dhPk dhsA) hs.spk))
  let tr8 := tr7.append (CEvE (ComposedEvent.HandshakeSession (stA.sessionInfo a) tr5.length))
  let tr9 := tr8.append (TRStE a stA)
  change CompClosedInv tr9
  have hc3 : CompClosedInv tr3 := ((hc.append_rnd 32).append_rnd 32).append_rnd 32
  have hc4 : CompClosedInv tr4 := hc3.append_net_of_closed (.dhPkRand ⟨tr.length, 32, rfl⟩)
  have hc5 : CompClosedInv tr5 := hc4.append_net_of_closed (.kemEncap pqPk (rnd (tr.length + 1) 32))
  have hc8 : CompClosedInv tr8 := ((hc5.append_ev _).append_trEv _).append_cEv _
  exact hc8.append_trSt (.spqrInit (.exposed .pqr) (.literal _))

theorem closed_receiveSignalMsg_at {tr : ExecTrace} (hc : CompClosedInv tr) {α : Type}
    (msgIdx : Nat) {f : TRSignalMsg → Traceful α}
    (hf : ∀ msg, CompTightClosed tr msg.pqRatchet → CompClosedInv ((f msg).run tr).2.val) :
    CompClosedInv (((receiveSignalMsg msgIdx >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at msgIdx tr hc fun raw _ hraw => ?_
  rcases hparse : parseTrSignalMsg raw with _ | msg
  · rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc
  · dsimp only [MonadLiftT.monadLift, MonadLift.monadLift]
    rw [CompTrace.run_bind_assoc_snd]
    refine CompTrace.bind_guardP_at _ tr hc fun _ => ?_
    exact hf msg (CompTightClosed.parseTrSignalMsg_pqRatchet (hc.of_attackerKnows hraw) hparse)

theorem closed_bobStart_commit {tr : ExecTrace} (hc : CompClosedInv tr)
    (b a : Participant) (sB sS sQ : Bytes) (o : Option Bytes)
    (ikA ek ct : Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (dhs spqr' seed pqSalt m : Bytes) (c' : RecvChain)
    (hspqr : CompTightClosed tr spqr') :
    let st := Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.bobRatchetedSt
      a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    CompClosedInv (((do
      let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
      ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (DiffieHellman.dhPk sB) ikA
        (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys)
      if true then
        ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
        ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
      ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
      let skipped := msg.counter.toNat - c.index.toNat
      let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
      DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
        msg.counter c.rIdx childIdx
        { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr).2.val) := by
  intro st c
  have h_tl : ∀ {α : Type} (f : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= f).run t).2.val = ((f t.length).run t).2.val :=
    fun f t => by unfold DY.Libsignal.TripleRatchet.traceLength; rw [Traceful.run_bind, Traceful.run_mk]
  simp only [↓reduceIte, h_tl, Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd]
  let doneIdx := tr.length
  let tr₁ := tr.append (EvE (.BobDone b a (DiffieHellman.dhPk sB) ikA
    (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys))
  let tr₂ := tr₁.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
  let tr₃ := tr₂.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
  let tr₄ := tr₃.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
  have hc₄ : CompClosedInv tr₄ := (((hc.append_ev _).append_trEv _).append_trEv _).append_cEv _
  have hle₀₄ : tr ≤ tr₄ :=
    Trace.le_trans _ _ _ (Trace.append_le tr _)
      (Trace.le_trans _ _ _ (Trace.append_le tr₁ _)
        (Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le tr₃ _)))
  let skipped := msg.counter.toNat - c.index.toNat
  let childIdx := tr₄.length + skipped + 2
  let skipAct := DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx
    c.chainKey c.index skipped
  let restAct : Unit → Traceful Nat := fun _ => do
    ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
    DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
      msg.counter c.rIdx childIdx
      { st with recv := setRecvChain st.recv c', spqr := spqr' }
  change CompClosedInv (((skipAct >>= restAct).run tr₄).2.val)
  rw [Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.run_logSkippedKeys_bind_snd]
  let tr₅ := (skipAct.run tr₄).2.val
  have hle₄₅ : tr₄ ≤ tr₅ := (skipAct.run tr₄).2.property
  have hc₅ : CompClosedInv tr₅ :=
    CompClosedInv.logSkippedKeys_preserves (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx skipped
      c.chainKey c.index tr₄ hc₄
  dsimp only [restAct]
  rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
  let tr₆ := tr₅.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
  have hc₆ : CompClosedInv tr₆ := hc₅.append_trEv _
  have hle₀₆ : tr ≤ tr₆ :=
    Trace.le_trans _ _ _ hle₀₄ (Trace.le_trans _ _ _ hle₄₅ (Trace.append_le tr₅ _))
  exact hc₆.append_logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
    msg.counter c.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }
    (hspqr.mono hle₀₆)

theorem closed_preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace)
    (hc : CompClosedInv tr) :
    CompClosedInv ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hc
    fun sB sS sQ o ikA _ ek ct _ keys _ _ _ _ _ _ _ _ hbob => ?_
  refine closed_receiveSignalMsg_at hc mh.msg fun msg hpq => ?_
  dsimp only
  refine Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.bind_ensureReceiverChain_bobInitSt
    a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey tr hc fun _ => ?_
  let dhs := rnd tr.length 32
  let st := Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.bobRatchetedSt
    a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
  let c := Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
  let tr₁ := tr.append (RndE 32)
  have hc₁ : CompClosedInv tr₁ := hc.append_rnd 32
  rcases hConsume : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc₁
  · dsimp only
    rcases hSpqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc₁
    · dsimp only
      rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_bind_snd]
      obtain ⟨e, _, hkeys_eq⟩ := Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.kemDecap_of_bobAgreement hbob
      have hle₀₁ : tr ≤ tr₁ := Trace.append_le tr _
      have hpqr₁ : CompTightClosed tr₁ keys.pqr := by
        rw [hkeys_eq]; exact .exposed .pqr
      have hspqr₁ : CompTightClosed tr₁ spqr' :=
        CompTightClosed.spqrRecvState_of hSpqr (.spqrInit hpqr₁ (.literal _)) (hpq.mono hle₀₁)
      let tr₂ := tr₁.append (NetE key)
      have hle₁₂ : tr₁ ≤ tr₂ := Trace.append_le tr₁ _
      have hc₂ : CompClosedInv tr₂ := hc₁.append_net_of_closed (CompTightClosed.spqrRecvKey_of hSpqr)
      have hspqr₂ : CompTightClosed tr₂ spqr' := hspqr₁.mono hle₁₂
      refine CompTrace.bind_receiveMessage_at pqIdx tr₂ hc₂ fun pqSalt _ _ => ?_
      refine Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.bind_verifyMacAndDecrypt_at
        st msg pqSalt seed tr₂ hc₂ fun m _ => ?_
      cases o with
      | none =>
        dsimp only [Option.map]
        exact closed_bobStart_commit hc₂ b a sB sS sQ none ikA ek ct keys msg dhs spqr' seed pqSalt m c' hspqr₂
      | some oSk =>
        dsimp only [Option.map]
        refine bind_guardOnTrace_at (!opkUsedB · b (DiffieHellman.dhPk oSk)) tr₂ hc₂ fun _ => ?_
        rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent)]
        let tr₃ := tr₂.append (EvE (.OPKUsed b (DiffieHellman.dhPk oSk)))
        have hc₃ : CompClosedInv tr₃ := hc₂.append_ev _
        exact closed_bobStart_commit hc₃ b a sB sS sQ (some oSk) ikA ek ct keys msg dhs spqr' seed pqSalt m c'
          (hspqr₂.mono (Trace.append_le tr₂ _))

theorem closed_preserves_messageEncryptAbort (me : Participant) (stateIdx : Nat) (tr : ExecTrace)
    (hc : CompClosedInv tr) : CompClosedInv ((messageEncryptAbort me stateIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro _ _
  rw [CompTrace.run_genRand_bind_snd, Traceful.run_failure]
  exact hc.append_rnd 32

theorem closed_preserves_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInv tr) :
    CompClosedInv ((messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  obtain ⟨_, _, _, _, _, hdhs, _, _, _, _⟩ := hinv.trStOK me st stateIdx hst
  have hspqr0 : CompTightClosed tr st.spqr := hc.spqrClosed me st stateIdx hst
  apply CompTrace.bind_guardP_at _ tr hc
  intro _
  rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd,
    Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_bind_snd]
  let m := rnd tr.length 32
  let tr1 := tr.append (RndE 32)
  let coins := rnd tr1.length coinsLen
  let tr2 := tr1.append (RndE coinsLen)
  let key := (Spqr.spqrSend st.spqr coins).2.1
  let tr3 := tr2.append (NetE key)
  have hc3 : CompClosedInv tr3 :=
    ((hc.append_rnd 32).append_rnd coinsLen).append_net_of_closed
      (CompTightClosed.spqrSendKey_of st.spqr coins)
  have hle01 : tr ≤ tr1 := Trace.append_le tr _
  have hle12 : tr1 ≤ tr2 := Trace.append_le tr1 _
  have hle23 : tr2 ≤ tr3 := Trace.append_le tr2 _
  have hle03 : tr ≤ tr3 := Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 hle01 hle12) hle23
  have hle13 : tr1 ≤ tr3 := Trace.le_trans tr1 tr2 tr3 hle12 hle23
  apply CompTrace.bind_receiveMessage_at pqIdx tr3 hc3
  intro pqSalt _ _
  rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
    Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logMessageKeyAndStore_bind_snd,
    Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
  let tr4 := tr3.append (TREvE (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m))
  have hc4 : CompClosedInv tr4 := hc3.append_trEv _
  have hle34 : tr3 ≤ tr4 := Trace.append_le tr3 _
  have hle24 : tr2 ≤ tr4 := Trace.le_trans tr2 tr3 tr4 hle23 hle34
  have hle14 : tr1 ≤ tr4 := Trace.le_trans tr1 tr3 tr4 hle13 hle34
  have hle04 : tr ≤ tr4 := Trace.le_trans tr tr3 tr4 hle03 hle34
  have hlen1 : tr1.length = tr.length + 1 := by
    simp [tr1, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlen2 : tr2.length = tr.length + 2 := by
    simp [tr2, hlen1, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlen3 : tr3.length = tr.length + 3 := by
    simp [tr3, hlen2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hr_m : RandAt tr4 tr.length 32 := RandAt.mono hle14 (CompTrace.randAt_here tr 32)
  have hr_c : RandAt tr4 (tr.length + 1) coinsLen :=
    hlen1 ▸ RandAt.mono hle24 (CompTrace.randAt_here tr1 coinsLen)
  have hn_k : NetAt tr4 key (tr.length + 2) :=
    hlen2 ▸ NetAt.mono hle34 (CompTrace.at?_append_here tr2 (NetE key))
  have hev_sent : tr4.EventLoggedAt (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m) (tr.length + 3) :=
    (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr
      (hlen3 ▸ CompTrace.at?_append_here tr3 (TREvE (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m)))
  have hcoins_eq : coins = mkRand (tr.length + 1) coinsLen := by
    dsimp [coins, rnd, mkRand]; rw [hlen1]
  have hm_closed4 : CompTightClosed tr4 m :=
    .exposed (.rand (.inr (.inl ⟨tr.length, coinsLen, key, rfl, hr_m, hr_c, hn_k, _, hev_sent⟩)))
  have hcoins_closed4 : CompTightClosed tr4 coins := by
    rw [hcoins_eq]
    exact .exposed (.rand (.inr (.inr ⟨tr.length, coinsLen, key, rfl, hr_m, hr_c, hn_k, _, hev_sent⟩)))
  let st' : TRState :=
    { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := (Spqr.spqrSend st.spqr coins).1 }
  have hspqr'_closed4 : CompTightClosed tr4 st'.spqr :=
    .spqrSendState (hspqr0.mono hle04) hcoins_closed4
  have hc6 : CompClosedInv ((logMessageKeyAndStore me (st.sessionInfo me) .sender
      (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st').run tr4).2.val :=
    hc4.append_logMessageKeyAndStore me (st.sessionInfo me) .sender
      (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st' hspqr'_closed4
  rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logMessageKeyAndStore_snd] at hc6
  let tr5 := tr4.append (TREvE (TREvent.MessageKey (st.sessionInfo me) .sender
    (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx))
  let tr6 := tr5.append (TRStE me st')
  have hle46 : tr4 ≤ tr6 :=
    Trace.le_trans tr4 tr5 tr6 (Trace.append_le tr4 _) (Trace.append_le tr5 _)
  have hdhs_rnd : ∃ ts sz, st.dhs = mkRand ts sz := by
    rcases hdhs with ⟨t, hdhs_eq, _⟩ | ⟨t, _, hdhs_eq, _, _⟩
    · exact ⟨t + 2, 32, hdhs_eq⟩
    · exact ⟨t, 32, hdhs_eq⟩
  let mk := trMsgKeys pqSalt (kdfCk st.cks).2
  let wire := DY.Libsignal.TripleRatchet.trHonestWireMsg (DiffieHellman.dhPk st.dhs) st.ns st.pn
    (SymEnc.symEnc mk.cipherKey mk.iv m) (Spqr.spqrSend st.spqr coins).2.2
  have hwire_closed4 : CompTightClosed tr4 wire :=
    .trWireMsg (.dhPkRand hdhs_rnd)
      (.symEnc hm_closed4) (CompTightClosed.spqrSendMsg_of st.spqr coins)
  have hcat_closed4 :
      CompTightClosed tr4 (Concat.concat wire (computeMac mk.macKey st.myIk st.peerIk wire)) :=
    .concat hwire_closed4 (.trunc8 _)
  exact hc6.append_net_of_closed (hcat_closed4.mono hle46)

theorem closed_preserves_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32)
    (tr : ExecTrace) (hc : CompClosedInv tr) :
    CompClosedInv ((messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  have hspqr0 : CompTightClosed tr st.spqr := hc.spqrClosed me st stateIdx hst
  apply closed_receiveSignalMsg_at hc msgIdx
  intro msg hpq_closed
  apply Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hc
  intro e _
  rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
    dsimp only
    apply CompTrace.bind_guardP_at _ tr hc
    intro _
    apply Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_guardTrace_at _ tr hc
    intro _
    rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc
    · dsimp only
      rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_bind_snd]
      let tr1 := tr.append (NetE key)
      have hc1 : CompClosedInv tr1 :=
        hc.append_net_of_closed (CompTightClosed.spqrRecvKey_of hspqr_recv)
      have hle01 : tr ≤ tr1 := Trace.append_le tr _
      apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1
      intro pqSalt _ _
      apply Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1
      intro m
      rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
        Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
      let tr2 := tr1.append (TREvE (TREvent.SkippedKeyUsed s skippedKeyEventIdx))
      let tr3 := tr2.append (TREvE (TREvent.Received me st.peer pk n m))
      have hc3 : CompClosedInv tr3 := (hc1.append_trEv _).append_trEv _
      have hle03 : tr ≤ tr3 :=
        Trace.le_trans tr tr2 tr3
          (Trace.le_trans tr tr1 tr2 hle01 (Trace.append_le tr1 _))
          (Trace.append_le tr2 _)
      have hspqr'_closed3 : CompTightClosed tr3 spqr' :=
        (CompTightClosed.spqrRecvState_of hspqr_recv hspqr0 hpq_closed).mono hle03
      exact hc3.append_logMessageKeyAndStore me s .receiver seed pqSalt n rIdx stateIdx { st with spqr := spqr' } hspqr'_closed3
  | _ =>
    dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc

theorem closed_preserves_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : CompClosedInv tr) :
    CompClosedInv ((messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  have hspqr0 : CompTightClosed tr st.spqr := hc.spqrClosed me st stateIdx hst
  apply closed_receiveSignalMsg_at hc msgIdx
  intro msg hpq_closed
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor
  rcases hfind : findRecvChain st.recv msg.ratchetKey with _ | c
  · dsimp only
    rcases hlow : x25519LowOrder msg.ratchetKey with _ | _
    · simp only [Bool.false_eq_true, ↓reduceIte,
        DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_bind_assoc_snd]
      apply CompTrace.bind_guardP_at _ tr hc
      intro _
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_genRand_bind_snd,
        CompTrace.run_pure_bind_snd, CompTrace.run_pure_bind_snd]
      let tr1 := tr.append (RndE 32)
      have hc1 : CompClosedInv tr1 := hc.append_rnd 32
      have hle01 : tr ≤ tr1 := Trace.append_le tr _
      let dhs' := rnd tr.length 32
      let rk1 := (createChain st.rk msg.ratchetKey st.dhs).1
      let ckr := (createChain st.rk msg.ratchetKey st.dhs).2
      let rk2 := (createChain rk1 msg.ratchetKey dhs').1
      let cks2 := (createChain rk1 msg.ratchetKey dhs').2
      let c_new : RecvChain :=
        { ratchetKey := msg.ratchetKey, chainKey := ckr, index := 0, rIdx := st.rIdx + 2 }
      let recv1 := (st.recv ++ [c_new]).drop ((st.recv.length + 1) - maxReceiverChains)
      let pn1 := if st.ns = 0 then 0 else st.ns - 1
      let st1 : TRState :=
        { st with rk := rk2, dhs := dhs', cks := cks2, ns := 0, pn := pn1,
                  rIdx := st.rIdx + 2, recv := recv1 }
      rcases hcons : consumeMessageKey c_new msg.counter with _ | ⟨seed, c'⟩
      · dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc1
      · dsimp only
        rcases hspqr_recv : Spqr.spqrRecv st1.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
        · dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc1
        · dsimp only
          rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_bind_snd]
          let tr2 := tr1.append (NetE key)
          have hc2 : CompClosedInv tr2 :=
            hc1.append_net_of_closed (CompTightClosed.spqrRecvKey_of hspqr_recv)
          have hle12 : tr1 ≤ tr2 := Trace.append_le tr1 _
          have hle02 : tr ≤ tr2 := Trace.le_trans tr tr1 tr2 hle01 hle12
          apply CompTrace.bind_receiveMessage_at pqIdx tr2 hc2
          intro pqSalt _ _
          apply Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_verifyMacAndDecrypt_at st1 msg pqSalt seed tr2 hc2
          intro m
          simp only [↓reduceIte]
          rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
            Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
            CompTrace.run_bind_snd]
          let tr3 := tr2.append (TREvE (TREvent.DHRatchet me st1.peer msg.ratchetKey (DiffieHellman.dhPk st1.dhs)))
          let tr4 := tr3.append (TREvE (TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2)))
          have hc4 : CompClosedInv tr4 := (hc2.append_trEv _).append_trEv _
          have hle24 : tr2 ≤ tr4 :=
            Trace.le_trans tr2 tr3 tr4 (Trace.append_le tr2 _) (Trace.append_le tr3 _)
          have hle04 : tr ≤ tr4 := Trace.le_trans tr tr2 tr4 hle02 hle24
          have hc5 : CompClosedInv
              ((logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
                c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4).2.val :=
            CompClosedInv.logSkippedKeys_preserves (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
              (msg.counter.toNat - c_new.index.toNat) c_new.chainKey c_new.index tr4 hc4
          have hle45 : tr4 ≤ ((logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
              c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4).2.val :=
            ((logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
              c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4).2.property
          rcases hsk_res :
              (logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
                c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4 with
            ⟨_ | u, tr5_sub⟩
          · rw [hsk_res] at hc5; exact hc5
          · rw [hsk_res] at hc5 hle45
            dsimp only
            rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
            let tr6 := tr5_sub.val.append (TREvE (TREvent.Received me st1.peer msg.ratchetKey msg.counter m))
            have hc6 : CompClosedInv tr6 := hc5.append_trEv _
            have hle06 : tr ≤ tr6 :=
              Trace.le_trans tr tr4 tr6 hle04
                (Trace.le_trans tr4 tr5_sub.val tr6 hle45 (Trace.append_le tr5_sub.val _))
            let st2 : TRState := { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
            have hspqr'_closed6 : CompTightClosed tr6 spqr' :=
              (CompTightClosed.spqrRecvState_of hspqr_recv hspqr0 hpq_closed).mono hle06
            exact hc6.append_logMessageKeyAndStore me (st1.sessionInfo me) .receiver
              seed pqSalt msg.counter c_new.rIdx stateIdx st2 hspqr'_closed6
    · simp only [↓reduceIte]; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc
  · dsimp only
    rw [CompTrace.run_pure_bind_snd]
    rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
    · dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc
    · dsimp only
      rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
      · dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc
      · dsimp only
        rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_bind_snd]
        let tr1 := tr.append (NetE key)
        have hc1 : CompClosedInv tr1 :=
          hc.append_net_of_closed (CompTightClosed.spqrRecvKey_of hspqr_recv)
        have hle01 : tr ≤ tr1 := Trace.append_le tr _
        apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1
        intro pqSalt _ _
        apply Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1
        intro m
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [CompTrace.run_bind_snd]
        have hc2 : CompClosedInv
            ((logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
              c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1).2.val :=
          CompClosedInv.logSkippedKeys_preserves (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
            (msg.counter.toNat - c.index.toNat) c.chainKey c.index tr1 hc1
        have hle12 : tr1 ≤ ((logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
            c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1).2.val :=
          ((logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
            c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1).2.property
        rcases hsk_res :
            (logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
              c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1 with
          ⟨_ | u, tr2_sub⟩
        · rw [hsk_res] at hc2; exact hc2
        · rw [hsk_res] at hc2 hle12
          dsimp only
          rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
          let tr3 := tr2_sub.val.append (TREvE (TREvent.Received me st.peer msg.ratchetKey msg.counter m))
          have hc3 : CompClosedInv tr3 := hc2.append_trEv _
          have hle03 : tr ≤ tr3 :=
            Trace.le_trans tr tr1 tr3 hle01
              (Trace.le_trans tr1 tr2_sub.val tr3 hle12 (Trace.append_le tr2_sub.val _))
          let st2 : TRState := { st with recv := setRecvChain st.recv c', spqr := spqr' }
          have hspqr'_closed3 : CompTightClosed tr3 spqr' :=
            (CompTightClosed.spqrRecvState_of hspqr_recv hspqr0 hpq_closed).mono hle03
          exact hc3.append_logMessageKeyAndStore me (st.sessionInfo me) .receiver
            seed pqSalt msg.counter c.rIdx stateIdx st2 hspqr'_closed3

theorem closed_preserves_exposeSpqr (me : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hc : CompClosedInv tr) :
    CompClosedInv ((exposeSpqr me stateIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
    Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
  have hc1 := hc.append_trEv (TREvent.ExposedSpqr (st.sessionInfo me) st.spqr st.rIdx)
  exact hc1.append_net_of_closed ((hc.spqrClosed me st stateIdx hst).mono (Trace.append_le tr _))

theorem closed_preserves_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInv tr) :
    CompClosedInv ((exposeKey me stateIdx k).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  obtain ⟨j, keys, _, hkeys, _, hdhs, _, hrk, hcks, hrecv⟩ := hinv.trStOK me st stateIdx hst
  cases k with
  | rk =>
    dsimp only
    rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
      Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
    have hc1 := hc.append_trEv (TREvent.ExposedRK (st.sessionInfo me) st.rk st.rIdx)
    exact hc1.append_net_of_closed
      (.exposed (.exposedRK hrk (CompTrace.eventLogged_here tr _)))
  | dhs =>
    dsimp only
    rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
      Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
    have hc1 := hc.append_trEv (TREvent.ExposedDHs (st.sessionInfo me) st.dhs st.rIdx)
    rcases hdhs with ⟨t, hdhs_eq, _⟩ | ⟨t, _, hdhs_eq, _, _⟩
    · rw [hdhs_eq] at hc1 ⊢
      exact hc1.append_net_rnd (t + 2) 32
    · rw [hdhs_eq] at hc1 ⊢
      exact hc1.append_net_rnd t 32
  | cks =>
    dsimp only
    rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
      Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
    have hc1 := hc.append_trEv (TREvent.ExposedCKs (st.sessionInfo me) st.cks st.ns st.rIdx)
    obtain ⟨rkChain, pk, sk, n, _, hcks_eq⟩ := hcks
    have hsk : IsScheduleKey st.cks := by
      rw [hcks_eq]; exact isScheduleKey_chainKeyAt_createChain_snd rkChain pk sk n
    exact hc1.append_net_of_closed
      (.exposed (.exposedCKs hsk (CompTrace.eventLogged_here tr _)))
  | ckr pk =>
    dsimp only
    rcases hfind : findRecvChain st.recv pk with _ | c
    · dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc
    · dsimp only
      have hc_mem : c ∈ st.recv := Symbolic.Swarm.COMPOSED.CompPresTRExp.findRecvChain_mem hfind
      rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
        Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
      have hc1 := hc.append_trEv (TREvent.ExposedCKr (st.sessionInfo me) c.chainKey c.index c.rIdx)
      have hsk : IsScheduleKey c.chainKey := isScheduleKey_of_recvChainInv hinv hkeys (hrecv c hc_mem)
      exact hc1.append_net_of_closed
        (.exposed (.exposedCKr hsk (CompTrace.eventLogged_here tr _)))

theorem closed_preserves_exposeSkipped (skippedKeyEventIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInv tr) :
    CompClosedInv ((exposeSkipped skippedKeyEventIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  apply Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hc
  intro e he
  rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    dsimp only
    obtain ⟨_, _, _, _, hseed⟩ := hinv.skipOK s pk n seed rIdx src skippedKeyEventIdx
      ((Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr he)
    apply Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_guardTrace_at _ tr hc
    intro _
    rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
      Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
    have hc1 := hc.append_trEv (TREvent.ExposedMK s seed n rIdx)
    have hseed_shape : ∃ c, seed = (kdfCk c).2 := by
      rcases hseed with ⟨m, rfl⟩ | ⟨rkChain, pk', sk', m, _, rfl⟩ <;> exact ⟨_, rfl⟩
    exact hc1.append_net_of_closed
      (.exposed (.exposedMK hseed_shape (CompTrace.eventLogged_here tr _)))
  | _ =>
    dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc

theorem closed_preserves_compromiseIK (p : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInv tr) :
    CompClosedInv ((compromiseIK p stateIdx).run tr).2.val := by
  unfold compromiseIK
  refine bind_getKey_at p stateIdx .identity tr hc fun sk hst => ?_
  obtain ⟨t, rfl, _, _⟩ := hinv.stOK p { kind := .identity, sk := sk } stateIdx hst
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact (hc.append_ev _).append_net_rnd t 32

theorem closed_preserves_compromiseSPK (b : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInv tr) :
    CompClosedInv ((compromiseSPK b stateIdx).run tr).2.val := by
  unfold compromiseSPK
  refine bind_getKey_at b stateIdx .signedPrekey tr hc fun sk hst => ?_
  obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .signedPrekey, sk := sk } stateIdx hst
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact (hc.append_ev _).append_net_rnd t 32

theorem closed_preserves_compromisePQSPK (b : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInv tr) :
    CompClosedInv ((compromisePQSPK b stateIdx).run tr).2.val := by
  unfold compromisePQSPK
  refine bind_getKey_at b stateIdx .pqPrekey tr hc fun sk hst => ?_
  obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .pqPrekey, sk := sk } stateIdx hst
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact (hc.append_ev _).append_net_rnd t 64

theorem closed_preserves_compromiseOPK (b : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInv tr) :
    CompClosedInv ((compromiseOPK b stateIdx).run tr).2.val := by
  unfold compromiseOPK
  refine bind_getKey_at b stateIdx .oneTimePrekey tr hc fun sk hst => ?_
  refine bind_guardOnTrace_at (fun tr => !opkUsedB tr b (DiffieHellman.dhPk sk)) tr hc fun _ => ?_
  obtain ⟨t, rfl, _, _⟩ := hinv.stOK b { kind := .oneTimePrekey, sk := sk } stateIdx hst
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact (hc.append_ev _).append_net_rnd t 32

theorem closed_preserves_breakDH (tr : ExecTrace) (hc : CompClosedInv tr) :
    CompClosedInv (breakDH.run tr).2.val := by
  unfold breakDH
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact hc.append_ev _

theorem closed_preserves_breakKEM (tr : ExecTrace) (hc : CompClosedInv tr) :
    CompClosedInv (breakKEM.run tr).2.val := by
  unfold breakKEM
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact hc.append_ev _

theorem closed_preserves_invertDH (pkIdx : Nat) (tr : ExecTrace) (hc : CompClosedInv tr) :
    CompClosedInv ((invertDH pkIdx).run tr).2.val := by
  unfold invertDH
  refine Symbolic.Swarm.COMPOSED.CompPresPQXDH.Preserves.bind_guardOnTrace
    DY.Libsignal.PQXDH.brokenDHB (fun tr hc _ => ?_) tr hc
  refine bind_receiveMessage_at pkIdx tr hc fun pk _ hpk => ?_
  have hpk_closed : CompTightClosed tr (X25519.normalizeX25519Key pk) :=
    CompTightClosed.normalizeX25519Key (hc.of_attackerKnows hpk)
  rcases hdh : DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
  · dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc
  · dsimp only
    rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
    rw [dhSkOf_eq_some hdh] at hpk_closed
    rcases CompTightClosed.inv_dhPk hpk_closed with ⟨t, n, rfl⟩ | hsk_closed
    · exact hc.append_net_rnd t n
    · exact hc.append_net_of_closed hsk_closed

theorem closed_preserves_invertKEM (pkIdx : Nat) (tr : ExecTrace) (hc : CompClosedInv tr) :
    CompClosedInv ((invertKEM pkIdx).run tr).2.val := by
  unfold invertKEM
  refine Symbolic.Swarm.COMPOSED.CompPresPQXDH.Preserves.bind_guardOnTrace
    DY.Libsignal.PQXDH.brokenKEMB (fun tr hc _ => ?_) tr hc
  refine bind_receiveMessage_at pkIdx tr hc fun pk _ hpk => ?_
  have hpk_closed : CompTightClosed tr pk := hc.of_attackerKnows hpk
  rcases hkem : PQKem.invertKemPublicKey pk with _ | sk
  · dsimp only [liftM, monadLift, MonadLift.monadLift]
    rw [Traceful.run_bind, Traceful.run_mk]
    exact hc
  · dsimp only [liftM, monadLift, MonadLift.monadLift]
    rw [Traceful.run_bind, Traceful.run_mk]; dsimp only
    rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
    rw [kemPkInvert_eq_some hkem] at hpk_closed
    rcases CompTightClosed.inv_kemPk hpk_closed with ⟨t, n, rfl⟩ | hsk_closed
    · exact hc.append_net_rnd t n
    · exact hc.append_net_of_closed hsk_closed

/-! ## Reachable-trace induction -/

private theorem composed_reachable_induction {Inv : ExecTrace → Prop}
    (hBase : Inv Trace.nil)
    (hStep : ∀ (input : DY.Libsignal.Composed.reachability.Input) (tr : ExecTrace),
      tr.Reachable DY.Libsignal.Composed.reachability →
      DY.Libsignal.Composed.reachability.PreCond input tr → Inv tr →
      Inv (((DY.Libsignal.Composed.reachability.step input).snd).run tr).2.val)
    (tr : ExecTrace) (hReach : tr.Reachable DY.Libsignal.Composed.reachability) :
    Inv tr := by
  induction hReach with
  | Base => exact hBase
  | Step input hPre hReachPre ih => exact hStep input _ hReachPre hPre ih

theorem compClosedInv_of_reachable {tr : ExecTrace}
    (hr : tr.Reachable DY.Libsignal.Composed.reachability) :
    CompClosedInv tr := by
  refine composed_reachable_induction compClosedInv_nil
    (fun input tr hReachPre hPre hc => ?_) tr hr
  have hinv : SpqrInv tr := spqrInv_of_reachable tr hReachPre
  rcases input with ⟨⟨i, hi⟩, inp⟩
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · exact closed_preserves_net inp tr hPre hc
  · exact closed_preserves_registerIdentity inp tr hc
  · rcases inp with ⟨p, skIdx⟩; exact closed_preserves_registerCorruptIdentity p skIdx tr hc
  · rcases inp with ⟨b, idStateIdx⟩; exact closed_preserves_genSignedPrekey b idStateIdx tr hc
  · rcases inp with ⟨b, idStateIdx⟩; exact closed_preserves_genPQPrekey b idStateIdx tr hc
  · exact closed_preserves_genOneTimePrekey inp tr hc
  · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩
    exact closed_preserves_aliceStart a b idStateIdx regIdxB bh tr hc
  · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩
    exact closed_preserves_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx tr hc
  · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩
    exact closed_preserves_messageEncrypt me stateIdx coinsLen pqIdx tr hinv hc
  · rcases inp with ⟨me, stateIdx⟩
    exact closed_preserves_messageEncryptAbort me stateIdx tr hc
  · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩
    exact closed_preserves_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx tr hc
  · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩
    exact closed_preserves_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx tr hc
  · rcases inp with ⟨me, stateIdx, k⟩
    exact closed_preserves_exposeKey me stateIdx k tr hinv hc
  · rcases inp with ⟨me, stateIdx⟩
    exact closed_preserves_exposeSpqr me stateIdx tr hc
  · exact closed_preserves_exposeSkipped inp tr hinv hc
  · rcases inp with ⟨p, stateIdx⟩; exact closed_preserves_compromiseIK p stateIdx tr hinv hc
  · rcases inp with ⟨b, stateIdx⟩; exact closed_preserves_compromiseSPK b stateIdx tr hinv hc
  · rcases inp with ⟨b, stateIdx⟩; exact closed_preserves_compromisePQSPK b stateIdx tr hinv hc
  · rcases inp with ⟨b, stateIdx⟩; exact closed_preserves_compromiseOPK b stateIdx tr hinv hc
  · exact closed_preserves_breakDH tr hc
  · exact closed_preserves_breakKEM tr hc
  · exact closed_preserves_invertDH inp tr hc
  · exact closed_preserves_invertKEM inp tr hc
  · omega

/-- On any reachable trace `tr` of `Composed.reachability`, every attacker-known term belongs to
`CompTrClosed (CompStructuredExposure tr)`. -/
theorem attackerKnows_implies_compTrClosed {tr : ExecTrace}
    (hr : tr.Reachable DY.Libsignal.Composed.reachability)
    {t : Bytes} (hk : t.AttackerKnows tr) :
    CompTrClosed (CompStructuredExposure tr) t :=
  ((compClosedInv_of_reachable hr).of_attackerKnows hk).to_compTrClosed

end Symbolic.Swarm.COMPOSED.CompRatchet
