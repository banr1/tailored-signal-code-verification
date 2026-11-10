/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.CkSafeTRBase
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.BaseAttackerKnowledge
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Reachable-Trace Preservation of `SafeCkTR` and Chain-Key Inversion

Proves that `CkInv` is preserved across all composed protocol transitions, yielding
`safeCkTR_of_attackerKnows_reachable` and `ckKnownCasesTR : CkKnownCasesTRP`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo KeyDir KeyComponent createChain
  consumeMessageKey computeMac setRecvChain findRecvChain recvChainFor kdfCk litByte x25519LowOrder
  maxReceiverChains)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles
  PreKeyMsgHandles opkUsedB registerIdentity registerCorruptIdentity genSignedPrekey genPQPrekey
  genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK compromiseOPK breakDH breakKEM
  invertDH invertKEM)
open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED.CompRatchet

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace
/-! ## `CkInv` preservation across composed transitions -/

open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompPresPQXDH

structure CkInv (tr : ExecTrace) : Prop where
  baseSafe : ∀ b, tr.BaseAttackerKnows b → SafeCkTR tr b
  spqrSafe : ∀ me st idx, TRStoredAt tr me st idx → SafeCkTR tr st.spqr

theorem ckInv_nil : CkInv Trace.nil :=
  { baseSafe := fun _ h => False.elim ((Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1 _).mp h)
    spqrSafe := fun _ _ idx h => by simp [TRStoredAt, Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at h }

theorem CkInv.of_attackerKnows {tr : ExecTrace} (hc : CkInv tr)
    {b : DY.Bytes} (hk : b.AttackerKnows tr) : SafeCkTR tr b :=
  attackerKnows_imp_safeCkTR hc.baseSafe hk

theorem CkInv.append_rnd {tr : ExecTrace} (hc : CkInv tr) (n : Nat) :
    CkInv (tr.append (RndE n)) := by
  have hle : tr ≤ tr.append (RndE n) := Trace.append_le tr (RndE n)
  refine ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_rnd tr n b).mp hb)).mono hle,
    fun me st idx hst => (hc.spqrSafe me st idx
      (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CkInv.append_ev {tr : ExecTrace} (hc : CkInv tr) (ev : PQXDHEvent) :
    CkInv (tr.append (EvE ev)) := by
  have hle : tr ≤ tr.append (EvE ev) := Trace.append_le tr (EvE ev)
  refine ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_pqEv tr ev b).mp hb)).mono hle,
    fun me st idx hst => (hc.spqrSafe me st idx
      (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CkInv.append_trEv {tr : ExecTrace} (hc : CkInv tr) (ev : TREvent) :
    CkInv (tr.append (TREvE ev)) := by
  have hle : tr ≤ tr.append (TREvE ev) := Trace.append_le tr (TREvE ev)
  refine ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_trEv tr ev b).mp hb)).mono hle,
    fun me st idx hst => (hc.spqrSafe me st idx
      (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CkInv.append_cEv {tr : ExecTrace} (hc : CkInv tr) (ev : ComposedEvent) :
    CkInv (tr.append (CEvE ev)) := by
  have hle : tr ≤ tr.append (CEvE ev) := Trace.append_le tr (CEvE ev)
  refine ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_cEv tr ev b).mp hb)).mono hle,
    fun me st idx hst => (hc.spqrSafe me st idx
      (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CkInv.append_st {tr : ExecTrace} (hc : CkInv tr)
    (me : Participant) (st : PQXDHState) :
    CkInv (tr.append (StE me st)) := by
  have hle : tr ≤ tr.append (StE me st) := Trace.append_le tr (StE me st)
  refine ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_pqSt tr me st b).mp hb)).mono hle,
    fun me' st' idx hst => (hc.spqrSafe me' st' idx
      (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CkInv.append_net {tr : ExecTrace} (hc : CkInv tr) {msg : DY.Bytes}
    (hmsg : SafeCkTR (tr.append (NetE msg)) msg) :
    CkInv (tr.append (NetE msg)) := by
  have hle : tr ≤ tr.append (NetE msg) := Trace.append_le tr (NetE msg)
  refine ⟨fun b hb => ?_, fun me st idx hst => ?_⟩
  · rcases (CompTrace.baseAttackerKnows_append_net tr msg b).mp hb with rfl | hb'
    · exact hmsg
    · exact (hc.baseSafe b hb').mono hle
  · exact (hc.spqrSafe me st idx
      (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle

theorem CkInv.append_net_of_safe {tr : ExecTrace} (hc : CkInv tr) {msg : DY.Bytes}
    (hmsg : SafeCkTR tr msg) :
    CkInv (tr.append (NetE msg)) :=
  hc.append_net (hmsg.mono (Trace.append_le tr (NetE msg)))

theorem CkInv.append_net_rnd {tr : ExecTrace} (hc : CkInv tr) (t n : Nat) :
    CkInv (tr.append (NetE (CompTrace.mkRand t n))) :=
  hc.append_net (safeCkTR_random _ { timestamp := t, size := n })

theorem CkInv.append_trSt {tr : ExecTrace} (hc : CkInv tr)
    {me : Participant} {st : TRState} (hspqr : SafeCkTR tr st.spqr) :
    CkInv (tr.append (TRStE me st)) := by
  have hle : tr ≤ tr.append (TRStE me st) := Trace.append_le tr (TRStE me st)
  refine ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_trSt tr me st b).mp hb)).mono hle,
    fun me' st' idx hst => ?_⟩
  rcases CompInv.CompPresBob.trStoredAt_append_same hst with ⟨_, hst'⟩ | ⟨_, _, rfl⟩
  · exact (hc.spqrSafe me' st' idx hst').mono hle
  · exact hspqr.mono hle

theorem CkInv.logSkippedKeys_preserves (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32) (tr : ExecTrace),
      CkInv tr →
      CkInv ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k).run tr).2.val
  | 0, _, _, tr, hc => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    exact CompTrace.Preserves.pure () tr hc
  | k + 1, ck, n, tr, hc => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    exact CkInv.logSkippedKeys_preserves s pk rIdx src k (kdfCk ck).1 (n + 1) _ (hc.append_trEv _)

theorem CkInv.append_logMessageKeyAndStore {tr : ExecTrace} (hc : CkInv tr)
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (seed pqSalt : DY.Bytes)
    (n : UInt32) (rIdx prev : Nat) (st : TRState) (hspqr : SafeCkTR tr st.spqr) :
    CkInv ((DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx prev st).run tr).2.val := by
  rw [CompPresTRExp.run_logMessageKeyAndStore_snd]
  exact (hc.append_trEv _).append_trSt (hspqr.mono (Trace.append_le tr _))

theorem parseTrSignalMsg_pqRatchet_safeCk {T : ExecTrace} {t : DY.Bytes} {msg : TRSignalMsg}
    (ht : SafeCkTR T t) (hparse : parseTrSignalMsg t = some msg) : SafeCkTR T msg.pqRatchet := by
  unfold parseTrSignalMsg at hparse
  simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at hparse
  rcases hparse with ⟨⟨wire, mac⟩, hsplit, x, hx, rfl⟩; dsimp only at hx ⊢
  rw [← Concat.concat_split t (t.length - Trunc.trunc8Length) wire mac hsplit] at ht
  have hwire : SafeCkTR T wire := ((safeCkTR_concat_iff wire mac).mp ht).1
  rw [TrWire.trWireMsg_of_fields? hx] at hwire; exact ((safeCkTR_trWireMsg_iff x).mp hwire).2.2

theorem ckSafe_receiveSignalMsg_at {tr : ExecTrace} (hc : CkInv tr) {α : Type}
    (msgIdx : Nat) {f : TRSignalMsg → Traceful α}
    (hf : ∀ msg, SafeCkTR tr msg.pqRatchet → CkInv ((f msg).run tr).2.val) :
    CkInv (((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at msgIdx tr hc fun raw _ hraw => ?_
  rcases hparse : parseTrSignalMsg raw with _ | msg
  · dsimp only; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hc
  · dsimp only
    rw [CompTrace.run_bind_assoc_snd]
    refine CompTrace.bind_guardP_at _ tr hc fun _ => ?_
    rw [CompTrace.run_pure_bind_snd]
    exact hf msg (parseTrSignalMsg_pqRatchet_safeCk (hc.of_attackerKnows hraw) hparse)

theorem ckSafe_preserves_net (msg : DY.Bytes) (tr : ExecTrace) (hPre : msg.AttackerKnows tr)
    (hc : CkInv tr) : CkInv ((Network.sendMessage msg).run tr).2.val := by
  rw [CompPresTRExp.run_sendMessage_snd]
  exact hc.append_net_of_safe (hc.of_attackerKnows hPre)

theorem ckSafe_preserves_registerIdentity (p : Participant) (tr : ExecTrace)
    (hc : CkInv tr) : CkInv ((registerIdentity p).run tr).2.val := by
  unfold registerIdentity
  refine bind_guardOnTrace_at _ tr hc fun _ => ?_
  rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent),
    CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact ((((hc.append_rnd 32).append_ev _).append_net_of_safe
    (.dhPk (safeCkTR_random _ _))).append_net_of_safe (safeCkTR_vk _ _)).append_st p _

theorem ckSafe_preserves_registerCorruptIdentity (p : Participant) (skIdx : Nat) (tr : ExecTrace)
    (hc : CkInv tr) : CkInv ((registerCorruptIdentity p skIdx).run tr).2.val := by
  unfold registerCorruptIdentity
  refine bind_guardOnTrace_at _ tr hc fun _ => ?_
  refine bind_receiveMessage_at skIdx tr hc fun _ _ _ => ?_
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent)]
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, CompTrace.run_bind_snd, Traceful.run_mk, Traceful.run_pure]
  exact (hc.append_ev _).append_ev _

theorem ckSafe_preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) (tr : ExecTrace)
    (hc : CkInv tr) : CkInv ((genSignedPrekey b idStateIdx).run tr).2.val := by
  unfold genSignedPrekey
  refine bind_getKey_at b idStateIdx .identity tr hc fun _ _ => ?_
  rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd,
    CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent)]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
  exact (((((hc.append_rnd 32).append_rnd 64).append_ev _).append_st b _).append_net_of_safe
    (.dhPk (safeCkTR_random _ _))).append_net_of_safe (safeCkTR_sign _ _ _ _)

theorem ckSafe_preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) (tr : ExecTrace)
    (hc : CkInv tr) : CkInv ((genPQPrekey b idStateIdx).run tr).2.val := by
  unfold genPQPrekey
  refine bind_getKey_at b idStateIdx .identity tr hc fun _ _ => ?_
  rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd,
    CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent)]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
  exact (((((hc.append_rnd 64).append_rnd 64).append_ev _).append_st b _).append_net_of_safe
    (.kemPk (safeCkTR_random _ _))).append_net_of_safe (safeCkTR_sign _ _ _ _)

theorem ckSafe_preserves_genOneTimePrekey (b : Participant) (tr : ExecTrace)
    (hc : CkInv tr) : CkInv ((genOneTimePrekey b).run tr).2.val := by
  unfold genOneTimePrekey
  rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent)]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
  exact (((hc.append_rnd 32).append_ev _).append_st b _).append_net_of_safe
    (.dhPk (safeCkTR_random _ _))

theorem ckSafe_preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) (tr : ExecTrace) (hc : CkInv tr) :
    CkInv ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hc (hc.append_rnd 32)
    fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ => ?_
  let hs := aliceOut tr ikA ikBPk spkPk pqPk opk
  let tr1 := tr.append (RndE 32)
  let tr2 := tr1.append (RndE 32)
  let dhsA := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr2.length 32
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
  rw [CompTrace.run_genRand_bind_snd]
  dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd]
  unfold DY.Libsignal.TripleRatchet.traceLength
  rw [CompTrace.run_bind_snd, Traceful.run_mk]
  dsimp only
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent),
    CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
    CompPresTRExp.run_logEvent_bind_snd (Ev := ComposedEvent)]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  change CkInv tr9
  have hc3 : CkInv tr3 := ((hc.append_rnd 32).append_rnd 32).append_rnd 32
  have hc4 : CkInv tr4 := hc3.append_net_of_safe (.dhPk (safeCkTR_random _ _))
  have hc5 : CkInv tr5 := hc4.append_net_of_safe (safeCkTR_kemEncap_fst _ pqPk _)
  have hc8 : CkInv tr8 := ((hc5.append_ev _).append_trEv _).append_cEv _
  have hpqr : SafeCkTR tr8 hs.keys.pqr := by
    dsimp [hs, aliceOut, DY.Libsignal.PQXDH.aliceAgreement]
    exact safeCkTR_pqxdhKdf_pqr tr8 _
  exact hc8.append_trSt (SafeCkTR.spqrInit { authKey := hs.keys.pqr, params := spqrA2B }
    hpqr (safeCkTR_literal _ _))

theorem ckSafe_bobStart_commit {tr : ExecTrace} (hc : CkInv tr)
    (b a : Participant) (sB sS sQ : DY.Bytes) (o : Option DY.Bytes)
    (ikA ek ct : DY.Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (dhs spqr' seed pqSalt m : DY.Bytes) (c' : RecvChain)
    (hspqr : SafeCkTR tr spqr') :
    let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    CkInv (((do
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
  let doneIdx := tr.length
  let tr₁ := tr.append (EvE (.BobDone b a (DiffieHellman.dhPk sB) ikA
    (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys))
  let tr₂ := tr₁.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
  let tr₃ := tr₂.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
  let tr₄ := tr₃.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
  have hc₄ : CkInv tr₄ := (((hc.append_ev _).append_trEv _).append_trEv _).append_cEv _
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
  simp only [↓reduceIte, DY.Libsignal.TripleRatchet.traceLength]
  rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent),
    CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
    CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
    CompPresTRExp.run_logEvent_bind_snd (Ev := ComposedEvent),
    CompTrace.run_bind_snd, Traceful.run_mk]
  dsimp only
  change CkInv (((skipAct >>= restAct).run tr₄).2.val)
  rw [CompInv.CompPresBob.run_logSkippedKeys_bind_snd]
  let tr₅ := (skipAct.run tr₄).2.val
  have hle₄₅ : tr₄ ≤ tr₅ := (skipAct.run tr₄).2.property
  have hc₅ : CkInv tr₅ :=
    CkInv.logSkippedKeys_preserves (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx skipped
      c.chainKey c.index tr₄ hc₄
  let tr₆ := tr₅.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
  have hc₆ : CkInv tr₆ := hc₅.append_trEv _
  have hle₀₆ : tr ≤ tr₆ :=
    Trace.le_trans _ _ _ hle₀₄ (Trace.le_trans _ _ _ hle₄₅ (Trace.append_le tr₅ _))
  dsimp only [restAct]
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
  exact hc₆.append_logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
    msg.counter c.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }
    (hspqr.mono hle₀₆)

theorem ckSafe_preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace)
    (hc : CkInv tr) :
    CkInv ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hc
    fun sB sS sQ o ikA _ ek ct _ keys _ _ _ _ _ _ _ _ hbob => ?_
  refine ckSafe_receiveSignalMsg_at hc mh.msg fun msg hpq => ?_
  dsimp only
  refine CompInv.CompPresBob.bind_ensureReceiverChain_bobInitSt
    a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey tr hc fun _ => ?_
  let dhs := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32
  let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
  let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
  let tr₁ := tr.append (RndE 32)
  have hc₁ : CkInv tr₁ := hc.append_rnd 32
  rcases hConsume : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · dsimp only; exact CompTrace.Preserves.failure tr₁ hc₁
  · dsimp only
    rcases hSpqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; exact CompTrace.Preserves.failure tr₁ hc₁
    · dsimp only
      have hkeys_eq : ∃ ikm, keys = DY.Libsignal.PQXDH.pqxdhKdf ikm := by
        dsimp only [DY.Libsignal.PQXDH.bobAgreement, Option.pure_def] at hbob
        injection hbob with h; exact ⟨_, h.symm⟩
      obtain ⟨_, hkeys_eq⟩ := hkeys_eq
      have hle₀₁ : tr ≤ tr₁ := Trace.append_le tr _
      have hpqr₁ : SafeCkTR tr₁ keys.pqr := by
        rw [hkeys_eq]; exact safeCkTR_pqxdhKdf_pqr tr₁ _
      have hspqr₁ : SafeCkTR tr₁ spqr' :=
        safeCkTR_spqrRecv_state hSpqr
          (SafeCkTR.spqrInit { authKey := keys.pqr, params := spqrB2A } hpqr₁ (safeCkTR_literal _ _))
          (hpq.mono hle₀₁)
      let tr₂ := tr₁.append (NetE key)
      have hle₁₂ : tr₁ ≤ tr₂ := Trace.append_le tr₁ _
      have hc₂ : CkInv tr₂ := hc₁.append_net_of_safe (safeCkTR_spqrRecv_key hSpqr)
      have hspqr₂ : SafeCkTR tr₂ spqr' := hspqr₁.mono hle₁₂
      rw [CompPresTRExp.run_sendMessage_bind_snd]
      refine CompTrace.bind_receiveMessage_at pqIdx tr₂ hc₂ fun pqSalt _ _ => ?_
      refine CompInv.CompPresBob.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr₂ hc₂ fun m _ => ?_
      cases o with
      | none =>
        dsimp only [Option.map]
        exact ckSafe_bobStart_commit hc₂ b a sB sS sQ none ikA ek ct keys msg dhs spqr' seed pqSalt m c' hspqr₂
      | some oSk =>
        dsimp only [Option.map]
        rw [CompTrace.run_bind_snd]
        unfold DY.Libsignal.PQXDH.guardTrace
        rw [Traceful.run_mk]
        dsimp only
        by_cases hused : (!opkUsedB tr₂ b (DiffieHellman.dhPk oSk)) = true
        · rw [ite_eq_left_iff.mpr fun h => absurd hused h]
          dsimp only
          rw [CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent)]
          let tr₃ := tr₂.append (EvE (.OPKUsed b (DiffieHellman.dhPk oSk)))
          have hc₃ : CkInv tr₃ := hc₂.append_ev _
          exact ckSafe_bobStart_commit hc₃ b a sB sS sQ (some oSk) ikA ek ct keys msg dhs spqr' seed pqSalt m c'
            (hspqr₂.mono (Trace.append_le tr₂ _))
        · rw [ite_eq_right_iff.mpr fun h => absurd h hused]
          exact hc₂

theorem ckSafe_preserves_messageEncryptAbort (me : Participant) (stateIdx : Nat) (tr : ExecTrace)
    (hc : CkInv tr) : CkInv ((DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro _ _
  rw [CompTrace.run_genRand_bind_snd]
  exact CompTrace.Preserves.failure _ (hc.append_rnd 32)

theorem ckSafe_preserves_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CkInv tr) :
    CkInv ((DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  obtain ⟨_, _, _, _, _, hdhs, _, _, _, _⟩ := hinv.trStOK me st stateIdx hst
  have hspqr0 : SafeCkTR tr st.spqr := hc.spqrSafe me st stateIdx hst
  apply CompTrace.bind_guardP_at _ tr hc
  intro _
  rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd,
    CompPresTRExp.run_sendMessage_bind_snd]
  let m := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32
  let tr1 := tr.append (RndE 32)
  let coins := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr1.length coinsLen
  let tr2 := tr1.append (RndE coinsLen)
  let key := (Spqr.spqrSend st.spqr coins).2.1
  let tr3 := tr2.append (NetE key)
  have hc3 : CkInv tr3 :=
    ((hc.append_rnd 32).append_rnd coinsLen).append_net_of_safe
      (safeCkTR_spqrSend_key tr2 st.spqr coins)
  have hle01 : tr ≤ tr1 := Trace.append_le tr _
  have hle12 : tr1 ≤ tr2 := Trace.append_le tr1 _
  have hle23 : tr2 ≤ tr3 := Trace.append_le tr2 _
  have hle03 : tr ≤ tr3 := Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 hle01 hle12) hle23
  apply CompTrace.bind_receiveMessage_at pqIdx tr3 hc3
  intro pqSalt _ _
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
    CompPresTRExp.run_logMessageKeyAndStore_bind_snd,
    CompPresTRExp.run_sendMessage_snd]
  let tr4 := tr3.append (TREvE (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m))
  have hc4 : CkInv tr4 := hc3.append_trEv _
  have hle34 : tr3 ≤ tr4 := Trace.append_le tr3 _
  have hle04 : tr ≤ tr4 := Trace.le_trans tr tr3 tr4 hle03 hle34
  let st' : TRState :=
    { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := (Spqr.spqrSend st.spqr coins).1 }
  have hspqr'_safe4 : SafeCkTR tr4 st'.spqr :=
    safeCkTR_spqrSend_state (hspqr0.mono hle04) (safeCkTR_random tr4 _)
  have hc6 : CkInv ((DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) .sender (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st').run tr4).2.val :=
    hc4.append_logMessageKeyAndStore me (st.sessionInfo me) .sender
      (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st' hspqr'_safe4
  rw [CompPresTRExp.run_logMessageKeyAndStore_snd] at hc6
  let tr5 := tr4.append (TREvE (TREvent.MessageKey (st.sessionInfo me) .sender
    (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx))
  let tr6 := tr5.append (TRStE me st')
  have hdhs_safe : SafeCkTR tr6 st.dhs := by
    rcases hdhs with ⟨t, hdhs_eq, _⟩ | ⟨t, _, hdhs_eq, _, _⟩ <;>
      [rw [hdhs_eq]; rw [hdhs_eq]] <;> exact safeCkTR_random tr6 _
  let mk := trMsgKeys pqSalt (kdfCk st.cks).2
  let wire := DY.Libsignal.TripleRatchet.trHonestWireMsg (DiffieHellman.dhPk st.dhs) st.ns st.pn
    (SymEnc.symEnc mk.cipherKey mk.iv m) (Spqr.spqrSend st.spqr coins).2.2
  have hwire_safe6 : SafeCkTR tr6 wire :=
    safeCkTR_trHonestWireMsg st.ns st.pn (.dhPk hdhs_safe)
      (.symEnc (safeCkTR_random tr6 _)) (safeCkTR_spqrSend_msg tr6 st.spqr coins)
  have hcat_safe6 :
      SafeCkTR tr6 (Concat.concat wire (computeMac mk.macKey st.myIk st.peerIk wire)) :=
    .concat hwire_safe6 (safeCkTR_computeMac_honest tr6 pqSalt (kdfCk st.cks).2
      st.myIk st.peerIk st.dhs st.ns st.pn m (Spqr.spqrSend st.spqr coins).2.2)
  exact hc6.append_net_of_safe hcat_safe6

theorem ckSafe_preserves_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32)
    (tr : ExecTrace) (hc : CkInv tr) :
    CkInv ((DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  have hspqr0 : SafeCkTR tr st.spqr := hc.spqrSafe me st stateIdx hst
  apply ckSafe_receiveSignalMsg_at hc msgIdx
  intro msg hpq_safe
  apply CompPresTRExp.bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hc
  intro e _
  rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx _sourceStateIdx =>
    dsimp only
    apply CompTrace.bind_guardP_at _ tr hc
    intro _
    apply CompPresTRExp.bind_guardTrace_at _ tr hc
    intro _
    rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; exact CompTrace.Preserves.failure tr hc
    · dsimp only
      rw [CompPresTRExp.run_sendMessage_bind_snd]
      let tr1 := tr.append (NetE key)
      have hc1 : CkInv tr1 := hc.append_net_of_safe (safeCkTR_spqrRecv_key hspqr_recv)
      have hle01 : tr ≤ tr1 := Trace.append_le tr _
      apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1
      intro pqSalt _ _
      apply CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1
      intro m
      rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
        CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
      let tr2 := tr1.append (TREvE (TREvent.SkippedKeyUsed s skippedKeyEventIdx))
      let tr3 := tr2.append (TREvE (TREvent.Received me st.peer pk n m))
      have hc3 : CkInv tr3 := (hc1.append_trEv _).append_trEv _
      have hle03 : tr ≤ tr3 :=
        Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 hle01 (Trace.append_le tr1 _))
          (Trace.append_le tr2 _)
      have hspqr'_safe3 : SafeCkTR tr3 spqr' :=
        (safeCkTR_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle03
      exact hc3.append_logMessageKeyAndStore me s .receiver seed pqSalt n rIdx stateIdx { st with spqr := spqr' } hspqr'_safe3
  | _ => dsimp only; exact CompTrace.Preserves.failure tr hc

theorem ckSafe_preserves_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : CkInv tr) :
    CkInv ((DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  have hspqr0 : SafeCkTR tr st.spqr := hc.spqrSafe me st stateIdx hst
  apply ckSafe_receiveSignalMsg_at hc msgIdx
  intro msg hpq_safe
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor
  rcases hfind : findRecvChain st.recv msg.ratchetKey with _ | c
  · dsimp only
    rcases hlow : x25519LowOrder msg.ratchetKey with _ | _
    · simp only [Bool.false_eq_true, ↓reduceIte, DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_bind_assoc_snd]
      apply CompTrace.bind_guardP_at _ tr hc
      intro _
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_genRand_bind_snd,
        CompTrace.run_pure_bind_snd, CompTrace.run_pure_bind_snd]
      let tr1 := tr.append (RndE 32)
      have hc1 : CkInv tr1 := hc.append_rnd 32
      have hle01 : tr ≤ tr1 := Trace.append_le tr _
      let dhs' := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32
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
      · dsimp only; exact CompTrace.Preserves.failure tr1 hc1
      · dsimp only
        rcases hspqr_recv : Spqr.spqrRecv st1.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
        · dsimp only; exact CompTrace.Preserves.failure tr1 hc1
        · dsimp only
          rw [CompPresTRExp.run_sendMessage_bind_snd]
          let tr2 := tr1.append (NetE key)
          have hc2 : CkInv tr2 := hc1.append_net_of_safe (safeCkTR_spqrRecv_key hspqr_recv)
          have hle12 : tr1 ≤ tr2 := Trace.append_le tr1 _
          have hle02 : tr ≤ tr2 := Trace.le_trans tr tr1 tr2 hle01 hle12
          apply CompTrace.bind_receiveMessage_at pqIdx tr2 hc2
          intro pqSalt _ _
          apply CompPresTRExp.bind_verifyMacAndDecrypt_at st1 msg pqSalt seed tr2 hc2
          intro m
          simp only [↓reduceIte]
          rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
            CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
            CompTrace.run_bind_snd]
          let tr3 := tr2.append (TREvE (TREvent.DHRatchet me st1.peer msg.ratchetKey (DiffieHellman.dhPk st1.dhs)))
          let tr4 := tr3.append (TREvE (TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2)))
          have hc4 : CkInv tr4 := (hc2.append_trEv _).append_trEv _
          have hle24 : tr2 ≤ tr4 :=
            Trace.le_trans tr2 tr3 tr4 (Trace.append_le tr2 _) (Trace.append_le tr3 _)
          have hle04 : tr ≤ tr4 := Trace.le_trans tr tr2 tr4 hle02 hle24
          have hc5 : CkInv
              ((DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
                c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4).2.val :=
            CkInv.logSkippedKeys_preserves (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
              (msg.counter.toNat - c_new.index.toNat) c_new.chainKey c_new.index tr4 hc4
          have hle45 : tr4 ≤ ((DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
              c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4).2.val :=
            ((DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
              c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4).2.property
          rcases hsk_res :
              (DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
                c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4 with
            ⟨_ | u, tr5_sub⟩
          · rw [hsk_res] at hc5; exact hc5
          · rw [hsk_res] at hc5 hle45
            dsimp only
            rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
            let tr6 := tr5_sub.val.append (TREvE (TREvent.Received me st1.peer msg.ratchetKey msg.counter m))
            have hc6 : CkInv tr6 := hc5.append_trEv _
            have hle06 : tr ≤ tr6 :=
              Trace.le_trans tr tr4 tr6 hle04
                (Trace.le_trans tr4 tr5_sub.val tr6 hle45 (Trace.append_le tr5_sub.val _))
            let st2 : TRState := { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
            have hspqr'_safe6 : SafeCkTR tr6 spqr' :=
              (safeCkTR_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle06
            exact hc6.append_logMessageKeyAndStore me (st1.sessionInfo me) .receiver
              seed pqSalt msg.counter c_new.rIdx stateIdx st2 hspqr'_safe6
    · simp only [↓reduceIte]; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hc
  · dsimp only
    rw [CompTrace.run_pure_bind_snd]
    rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
    · dsimp only; exact CompTrace.Preserves.failure tr hc
    · dsimp only
      rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
      · dsimp only; exact CompTrace.Preserves.failure tr hc
      · dsimp only
        rw [CompPresTRExp.run_sendMessage_bind_snd]
        let tr1 := tr.append (NetE key)
        have hc1 : CkInv tr1 := hc.append_net_of_safe (safeCkTR_spqrRecv_key hspqr_recv)
        have hle01 : tr ≤ tr1 := Trace.append_le tr _
        apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1
        intro pqSalt _ _
        apply CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1
        intro m
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [CompTrace.run_bind_snd]
        have hc2 : CkInv
            ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
              c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1).2.val :=
          CkInv.logSkippedKeys_preserves (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
            (msg.counter.toNat - c.index.toNat) c.chainKey c.index tr1 hc1
        have hle12 : tr1 ≤ ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
            c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1).2.val :=
          ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
            c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1).2.property
        rcases hsk_res :
            (DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
              c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1 with
          ⟨_ | u, tr2_sub⟩
        · rw [hsk_res] at hc2; exact hc2
        · rw [hsk_res] at hc2 hle12
          dsimp only
          rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
          let tr3 := tr2_sub.val.append (TREvE (TREvent.Received me st.peer msg.ratchetKey msg.counter m))
          have hc3 : CkInv tr3 := hc2.append_trEv _
          have hle03 : tr ≤ tr3 :=
            Trace.le_trans tr tr1 tr3 hle01
              (Trace.le_trans tr1 tr2_sub.val tr3 hle12 (Trace.append_le tr2_sub.val _))
          let st2 : TRState := { st with recv := setRecvChain st.recv c', spqr := spqr' }
          have hspqr'_safe3 : SafeCkTR tr3 spqr' :=
            (safeCkTR_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle03
          exact hc3.append_logMessageKeyAndStore me (st.sessionInfo me) .receiver
            seed pqSalt msg.counter c.rIdx stateIdx st2 hspqr'_safe3

theorem ckSafe_preserves_exposeSpqr (me : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hc : CkInv tr) :
    CkInv ((DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
    CompPresTRExp.run_sendMessage_snd]
  have hc1 := hc.append_trEv (TREvent.ExposedSpqr (st.sessionInfo me) st.spqr st.rIdx)
  exact hc1.append_net_of_safe ((hc.spqrSafe me st stateIdx hst).mono (Trace.append_le tr _))

theorem ckSafe_preserves_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CkInv tr) :
    CkInv ((DY.Libsignal.TripleRatchet.exposeKey me stateIdx k).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  obtain ⟨j, keys, _, hkeys, _, hdhs, _, hrk, hcks, hrecv⟩ := hinv.trStOK me st stateIdx hst
  cases k with
  | rk =>
    dsimp only
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
      CompPresTRExp.run_sendMessage_snd]
    have hc1 := hc.append_trEv (TREvent.ExposedRK (st.sessionInfo me) st.rk st.rIdx)
    obtain ⟨r, p, s, hrk_eq⟩ := hrk
    have hrk_safe : SafeCkTR (tr.append (TREvE (TREvent.ExposedRK (st.sessionInfo me) st.rk st.rIdx))) st.rk := by
      rw [hrk_eq]; exact safeCkTR_createChain_fst _ r p s
    exact hc1.append_net_of_safe hrk_safe
  | dhs =>
    dsimp only
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
      CompPresTRExp.run_sendMessage_snd]
    have hc1 := hc.append_trEv (TREvent.ExposedDHs (st.sessionInfo me) st.dhs st.rIdx)
    rcases hdhs with ⟨t, hdhs_eq, _⟩ | ⟨t, _, hdhs_eq, _, _⟩
    · rw [hdhs_eq] at hc1 ⊢; exact hc1.append_net_rnd (t + 2) 32
    · rw [hdhs_eq] at hc1 ⊢; exact hc1.append_net_rnd t 32
  | cks =>
    dsimp only
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
      CompPresTRExp.run_sendMessage_snd]
    have hc1 := hc.append_trEv (TREvent.ExposedCKs (st.sessionInfo me) st.cks st.ns st.rIdx)
    obtain ⟨rkChain, pk, sk, n, _, hcks_eq⟩ := hcks
    have hsto : StoredCkTR (tr.append (TREvE (TREvent.ExposedCKs (st.sessionInfo me) st.cks st.ns st.rIdx)))
        st.cks :=
      ⟨me, st, stateIdx, CompTrace.trStateStoredAt_mono (Trace.append_le tr _) hst, Or.inl rfl⟩
    have hcks_safe : SafeCkTR (tr.append (TREvE (TREvent.ExposedCKs (st.sessionInfo me) st.cks st.ns st.rIdx))) st.cks := by
      rw [hcks_eq] at hsto ⊢
      exact safeCkTR_chainKeyAt _ (safeCkTR_createChain_snd _ rkChain pk sk) n hsto
    exact hc1.append_net_of_safe hcks_safe
  | ckr pk =>
    dsimp only
    rcases hfind : findRecvChain st.recv pk with _ | c
    · dsimp only; exact CompTrace.Preserves.failure tr hc
    · dsimp only
      have hc_mem : c ∈ st.recv := CompPresTRExp.findRecvChain_mem hfind
      rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
        CompPresTRExp.run_sendMessage_snd]
      let tr1 := tr.append (TREvE (TREvent.ExposedCKr (st.sessionInfo me) c.chainKey c.index c.rIdx))
      have hc1 : CkInv tr1 := hc.append_trEv _
      have hsto : StoredCkTR tr1 c.chainKey :=
        ⟨me, st, stateIdx, CompTrace.trStateStoredAt_mono (Trace.append_le tr _) hst,
          Or.inr ⟨c, hc_mem, rfl⟩⟩
      have hck_safe : SafeCkTR tr1 c.chainKey := by
        obtain ⟨ikm, hikm⟩ := CompInv.CompPubInv.handshakeKeysAt_eq_pqxdhKdf hinv hkeys
        rcases hrecv c hc_mem with ⟨_, _, hck⟩ | ⟨n, _, _, hck⟩ | ⟨rkChain, pk', sk', n, _, hck⟩
        · rw [hck, hikm]; exact safeCkTR_pqxdhKdf_ck tr1 ikm
        · rw [hck, hikm] at hsto ⊢
          exact safeCkTR_chainKeyAt tr1 (safeCkTR_pqxdhKdf_ck tr1 ikm) (n + 1) hsto
        · rw [hck] at hsto ⊢
          exact safeCkTR_chainKeyAt tr1 (safeCkTR_createChain_snd tr1 rkChain pk' sk') n hsto
      exact hc1.append_net_of_safe hck_safe

theorem ckSafe_preserves_exposeSkipped (skippedKeyEventIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CkInv tr) :
    CkInv ((DY.Libsignal.TripleRatchet.exposeSkipped skippedKeyEventIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  apply CompPresTRExp.bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hc
  intro e he
  rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    dsimp only
    have he_log : tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) skippedKeyEventIdx :=
      (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr he
    obtain ⟨_, _, _, _, hseed⟩ := hinv.skipOK s pk n seed rIdx src skippedKeyEventIdx he_log
    apply CompPresTRExp.bind_guardTrace_at _ tr hc
    intro _
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
      CompPresTRExp.run_sendMessage_snd]
    let tr1 := tr.append (TREvE (TREvent.ExposedMK s seed n rIdx))
    have hc1 : CkInv tr1 := hc.append_trEv _
    have hseed_shape : ∃ c, seed = (kdfCk c).2 := by
      rcases hseed with ⟨m, rfl⟩ | ⟨rkChain, pk', sk', m, _, rfl⟩ <;> exact ⟨_, rfl⟩
    obtain ⟨c, rfl⟩ := hseed_shape
    have hev_log : tr1.EventLoggedAt (TREvent.SkippedKeyStored s pk n (kdfCk c).2 rIdx src) skippedKeyEventIdx :=
      evAt_mono (Trace.append_le tr _) he_log
    exact hc1.append_net_of_safe (safeCkTR_kdfCk_snd tr1 c ⟨skippedKeyEventIdx, s, pk, n, rIdx, src, hev_log⟩)
  | _ => dsimp only; exact CompTrace.Preserves.failure tr hc

theorem ckSafe_preserves_compromiseIK (p : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CkInv tr) :
    CkInv ((compromiseIK p stateIdx).run tr).2.val := by
  unfold compromiseIK
  refine bind_getKey_at p stateIdx .identity tr hc fun sk hst => ?_
  obtain ⟨t, rfl, _, _⟩ := hinv.stOK p { kind := .identity, sk := sk } stateIdx hst
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent), CompPresTRExp.run_sendMessage_snd]
  exact (hc.append_ev _).append_net_rnd t 32

theorem ckSafe_preserves_compromiseSPK (b : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CkInv tr) :
    CkInv ((compromiseSPK b stateIdx).run tr).2.val := by
  unfold compromiseSPK
  refine bind_getKey_at b stateIdx .signedPrekey tr hc fun sk hst => ?_
  obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .signedPrekey, sk := sk } stateIdx hst
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent), CompPresTRExp.run_sendMessage_snd]
  exact (hc.append_ev _).append_net_rnd t 32

theorem ckSafe_preserves_compromisePQSPK (b : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CkInv tr) :
    CkInv ((compromisePQSPK b stateIdx).run tr).2.val := by
  unfold compromisePQSPK
  refine bind_getKey_at b stateIdx .pqPrekey tr hc fun sk hst => ?_
  obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .pqPrekey, sk := sk } stateIdx hst
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent), CompPresTRExp.run_sendMessage_snd]
  exact (hc.append_ev _).append_net_rnd t 64

theorem ckSafe_preserves_compromiseOPK (b : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CkInv tr) :
    CkInv ((compromiseOPK b stateIdx).run tr).2.val := by
  unfold compromiseOPK
  refine bind_getKey_at b stateIdx .oneTimePrekey tr hc fun sk hst => ?_
  obtain ⟨t, rfl, _, _⟩ := hinv.stOK b { kind := .oneTimePrekey, sk := sk } stateIdx hst
  refine CompPresPQXDH.Preserves.bind_guardOnTrace _ (fun _ hc _ => ?_) _ hc
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent), CompPresTRExp.run_sendMessage_snd]
  exact (hc.append_ev _).append_net_rnd t 32

theorem ckSafe_preserves_breakDH (tr : ExecTrace) (hc : CkInv tr) :
    CkInv (breakDH.run tr).2.val := by
  unfold breakDH
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, CompTrace.run_bind_snd, Traceful.run_mk, Traceful.run_pure]
  exact hc.append_ev _

theorem ckSafe_preserves_breakKEM (tr : ExecTrace) (hc : CkInv tr) :
    CkInv (breakKEM.run tr).2.val := by
  unfold breakKEM
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, CompTrace.run_bind_snd, Traceful.run_mk, Traceful.run_pure]
  exact hc.append_ev _

theorem ckSafe_preserves_invertDH (pkIdx : Nat) (tr : ExecTrace) (hc : CkInv tr) :
    CkInv ((invertDH pkIdx).run tr).2.val := by
  unfold invertDH
  refine CompPresPQXDH.Preserves.bind_guardOnTrace
    DY.Libsignal.PQXDH.brokenDHB (fun tr hc _ => ?_) tr hc
  refine bind_receiveMessage_at pkIdx tr hc fun pk _ hpk => ?_
  have hpk_safe : SafeCkTR tr (X25519.normalizeX25519Key pk) :=
    safeCkTR_x25519Key (hc.of_attackerKnows hpk)
  rcases hdh : DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
  · dsimp only; exact CompTrace.Preserves.failure tr hc
  · dsimp only
    rw [CompPresTRExp.run_sendMessage_snd]
    rw [dhSkOf_eq_some hdh] at hpk_safe
    exact hc.append_net_of_safe ((safeCkTR_dhPk_iff sk).mp hpk_safe)

theorem ckSafe_preserves_invertKEM (pkIdx : Nat) (tr : ExecTrace) (hc : CkInv tr) :
    CkInv ((invertKEM pkIdx).run tr).2.val := by
  unfold invertKEM
  refine CompPresPQXDH.Preserves.bind_guardOnTrace
    DY.Libsignal.PQXDH.brokenKEMB (fun tr hc _ => ?_) tr hc
  refine bind_receiveMessage_at pkIdx tr hc fun pk _ hpk => ?_
  have hpk_safe : SafeCkTR tr pk := hc.of_attackerKnows hpk
  rcases hkem : PQKem.invertKemPublicKey pk with _ | sk
  · dsimp [MonadLiftT.monadLift, MonadLift.monadLift, liftM]
    rw [CompTrace.run_bind_snd, Traceful.run_mk]; exact hc
  · dsimp [MonadLiftT.monadLift, MonadLift.monadLift, liftM]
    rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only
    rw [CompPresTRExp.run_sendMessage_snd]
    rw [kemPkInvert_eq_some hkem] at hpk_safe
    exact hc.append_net_of_safe ((safeCkTR_kemPk_iff sk).mp hpk_safe)

theorem ckInv_of_reachable {tr : ExecTrace} (hr : ReachableTrace tr) :
    CkInv tr := by
  induction hr with
  | Base => exact ckInv_nil
  | Step input hPre hReachPre hc =>
    have hinv : SpqrInv _ := spqrInv_of_reachable _ hReachPre
    rcases input with ⟨⟨i, hi⟩, inp⟩
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · exact ckSafe_preserves_net inp _ hPre hc
    · exact ckSafe_preserves_registerIdentity inp _ hc
    · rcases inp with ⟨p, skIdx⟩; exact ckSafe_preserves_registerCorruptIdentity p skIdx _ hc
    · rcases inp with ⟨b, idStateIdx⟩; exact ckSafe_preserves_genSignedPrekey b idStateIdx _ hc
    · rcases inp with ⟨b, idStateIdx⟩; exact ckSafe_preserves_genPQPrekey b idStateIdx _ hc
    · exact ckSafe_preserves_genOneTimePrekey inp _ hc
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩
      exact ckSafe_preserves_aliceStart a b idStateIdx regIdxB bh _ hc
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩
      exact ckSafe_preserves_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩
      exact ckSafe_preserves_messageEncrypt me stateIdx coinsLen pqIdx _ hinv hc
    · rcases inp with ⟨me, stateIdx⟩
      exact ckSafe_preserves_messageEncryptAbort me stateIdx _ hc
    · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩
      exact ckSafe_preserves_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩
      exact ckSafe_preserves_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, k⟩
      exact ckSafe_preserves_exposeKey me stateIdx k _ hinv hc
    · rcases inp with ⟨me, stateIdx⟩
      exact ckSafe_preserves_exposeSpqr me stateIdx _ hc
    · exact ckSafe_preserves_exposeSkipped inp _ hinv hc
    · rcases inp with ⟨p, stateIdx⟩; exact ckSafe_preserves_compromiseIK p stateIdx _ hinv hc
    · rcases inp with ⟨b, stateIdx⟩; exact ckSafe_preserves_compromiseSPK b stateIdx _ hinv hc
    · rcases inp with ⟨b, stateIdx⟩; exact ckSafe_preserves_compromisePQSPK b stateIdx _ hinv hc
    · rcases inp with ⟨b, stateIdx⟩; exact ckSafe_preserves_compromiseOPK b stateIdx _ hinv hc
    · exact ckSafe_preserves_breakDH _ hc
    · exact ckSafe_preserves_breakKEM _ hc
    · exact ckSafe_preserves_invertDH inp _ hc
    · exact ckSafe_preserves_invertKEM inp _ hc
    · omega

/-- Every attacker-known term on a reachable composed trace `T` satisfies `SafeCkTR T`. -/
theorem safeCkTR_of_attackerKnows_reachable {T : ExecTrace} (hT : ReachableTrace T)
    {b : DY.Bytes} (hAK : b.AttackerKnows T) : SafeCkTR T b :=
  (ckInv_of_reachable hT).of_attackerKnows hAK

/-! ## Chain-key knowledge inversion -/

theorem safeCkTR_ck_cases {T : ExecTrace} {ck : DY.Bytes} (h : SafeCkTR T (kdfCk ck).1) :
    ck.AttackerKnows T ∨ StoredCkTR T (kdfCk ck).1 := by
  have hvalid := (safeCkTR_kdfExtract_iff ck (litByte 0x02)).mp h
  rcases hvalid with ⟨hck, _⟩ | ⟨h1, _⟩ | ⟨_, hst⟩ | hwr1 | ⟨b1, hwr2⟩
  · exact Or.inl hck
  · exact absurd (Symbolic.Swarm.COMPOSED.CompTermAlgebra.litByte_inj h1) (by decide)
  · exact Or.inr hst
  · exact absurd hwr1.symm (lkk_concat_ne_literal _ _ _)
  · exact (IsRatchetOrPqxdhBlock23.ne_literal hwr2).elim

/-- On a reachable composed trace, an attacker-known next chain key `(kdfCk ck).1` either comes
from an attacker-known `ck` or is stored on `T`. -/
theorem ckKnownCasesTR : CkKnownCasesTRP := by
  intro T hreach ck hak
  exact safeCkTR_ck_cases (safeCkTR_of_attackerKnows_reachable hreach hak)

end Symbolic.Swarm.CREF.TR.G1
