/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.KdfProvNon01Defs
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Trace.BaseAttackerKnowledge
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTR
import Batteries.Tactic.SeqFocus
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompClosed
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge

/-!
# KDF Provenance Invariant

Proves that `KdfProvInv` holds on every reachable composed trace. As a consequence
(`kdfProv_non01_of_reachable`), if the attacker knows `kdfExtract s i` at a chain-key or root-key
label, then either the attacker knows `s` or the term is the root key, sending chain key, or a
receiving chain key of a stored `TRState`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo KeyDir KeyComponent createChain
  consumeMessageKey setRecvChain findRecvChain recvChainFor kdfCk lit litByte x25519LowOrder
  maxReceiverChains)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles
  PreKeyMsgHandles pqxdhLabel opkUsedB registerIdentity registerCorruptIdentity genSignedPrekey
  genPQPrekey genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK compromiseOPK invertDH
  invertKEM)
open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED.CompRatchet
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompPresPQXDH

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## Trace invariant `KdfProvInv` -/

structure KdfProvInv (tr : ExecTrace) : Prop where
  baseSafe : ∀ b, tr.BaseAttackerKnows b → KdfProvSafe tr b
  spqrSafe : ∀ me st idx, TRStoredAt tr me st idx → KdfProvSafe tr st.spqr

theorem kdfProvInv_nil : KdfProvInv Trace.nil :=
  { baseSafe := fun b h => False.elim (Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1 b ▸ h)
    spqrSafe := fun _ _ _ h => by
      unfold TRStoredAt at h; rw [Trace.at?_eq_some] at h
      exact False.elim (Symbolic.DYBridge.DY.Trace.nil_length_not_lt _ h.1) }

theorem KdfProvInv.of_attackerKnows {tr : ExecTrace} (hc : KdfProvInv tr) {b : DY.Bytes} (hk : b.AttackerKnows tr) :
    KdfProvSafe tr b := attackerKnows_imp_kdfProvSafe hc.baseSafe hk

theorem KdfProvInv.append_rnd {tr : ExecTrace} (hc : KdfProvInv tr) (n : Nat) : KdfProvInv (tr.append (RndE n)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_rnd tr n b).mp hb)).mono (Trace.append_le tr _),
   fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem KdfProvInv.append_ev {tr : ExecTrace} (hc : KdfProvInv tr) (ev : PQXDHEvent) : KdfProvInv (tr.append (EvE ev)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_pqEv tr ev b).mp hb)).mono (Trace.append_le tr _),
   fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem KdfProvInv.append_trEv {tr : ExecTrace} (hc : KdfProvInv tr) (ev : TREvent) : KdfProvInv (tr.append (TREvE ev)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_trEv tr ev b).mp hb)).mono (Trace.append_le tr _),
   fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem KdfProvInv.append_cEv {tr : ExecTrace} (hc : KdfProvInv tr) (ev : ComposedEvent) : KdfProvInv (tr.append (CEvE ev)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_cEv tr ev b).mp hb)).mono (Trace.append_le tr _),
   fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem KdfProvInv.append_st {tr : ExecTrace} (hc : KdfProvInv tr) (me : Participant) (st : PQXDHState) :
    KdfProvInv (tr.append (StE me st)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_pqSt tr me st b).mp hb)).mono (Trace.append_le tr _),
   fun me' st' idx hst => (hc.spqrSafe me' st' idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem KdfProvInv.append_net {tr : ExecTrace} (hc : KdfProvInv tr) {msg : DY.Bytes}
    (hmsg : KdfProvSafe (tr.append (NetE msg)) msg) : KdfProvInv (tr.append (NetE msg)) := by
  have hle : tr ≤ tr.append (NetE msg) := Trace.append_le tr (NetE msg)
  refine ⟨fun b hb => ?_, fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩
  rcases (CompTrace.baseAttackerKnows_append_net tr msg b).mp hb with rfl | hb' <;> [exact hmsg; exact (hc.baseSafe b hb').mono hle]

theorem KdfProvInv.append_net_of_safe {tr : ExecTrace} (hc : KdfProvInv tr) {msg : DY.Bytes}
    (hmsg : KdfProvSafe tr msg) : KdfProvInv (tr.append (NetE msg)) :=
  hc.append_net (hmsg.mono (Trace.append_le tr (NetE msg)))

theorem KdfProvInv.append_net_rnd {tr : ExecTrace} (hc : KdfProvInv tr) (t n : Nat) :
    KdfProvInv (tr.append (NetE (CompTrace.mkRand t n))) :=
  hc.append_net (kdfProvSafe_random _ { timestamp := t, size := n })

theorem KdfProvInv.append_trSt {tr : ExecTrace} (hc : KdfProvInv tr)
    {me : Participant} {st : TRState} (hspqr : KdfProvSafe tr st.spqr) :
    KdfProvInv (tr.append (TRStE me st)) := by
  have hle : tr ≤ tr.append (TRStE me st) := Trace.append_le tr (TRStE me st)
  refine ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_trSt tr me st b).mp hb)).mono hle,
    fun me' st' idx hst => ?_⟩
  rcases CompInv.CompPresBob.trStoredAt_append_same hst with ⟨_, hst'⟩ | ⟨_, _, rfl⟩
  · exact (hc.spqrSafe me' st' idx hst').mono hle
  · exact hspqr.mono hle

theorem KdfProvInv.logSkippedKeys_preserves (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32) (tr : ExecTrace),
      KdfProvInv tr → KdfProvInv ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k).run tr).2.val
  | 0, _, _, _, hc => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [Traceful.run_pure]; exact hc
  | k + 1, ck, n, tr, hc => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    exact KdfProvInv.logSkippedKeys_preserves s pk rIdx src k (kdfCk ck).1 (n + 1) _ (hc.append_trEv _)

theorem KdfProvInv.append_logMessageKeyAndStore {tr : ExecTrace} (hc : KdfProvInv tr)
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (seed pqSalt : DY.Bytes)
    (n : UInt32) (rIdx prev : Nat) (st : TRState) (hspqr : KdfProvSafe tr st.spqr) :
    KdfProvInv ((DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx prev st).run tr).2.val := by
  rw [CompPresTRExp.run_logMessageKeyAndStore_snd]
  exact (hc.append_trEv _).append_trSt (hspqr.mono (Trace.append_le tr _))

theorem parseTrSignalMsg_pqRatchet_kdfProvSafe {T : ExecTrace} {t : DY.Bytes} {msg : TRSignalMsg}
    (ht : KdfProvSafe T t) (hparse : parseTrSignalMsg t = some msg) : KdfProvSafe T msg.pqRatchet := by
  unfold parseTrSignalMsg at hparse
  simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at hparse
  rcases hparse with ⟨⟨wire, mac⟩, hsplit, x, hx, rfl⟩; dsimp only at hx ⊢
  rw [← Concat.concat_split t (t.length - Trunc.trunc8Length) wire mac hsplit] at ht
  have hwire : KdfProvSafe T wire := ((kdfProvSafe_concat_iff wire mac).mp ht).1
  rw [TrWire.trWireMsg_of_fields? hx] at hwire; exact ((kdfProvSafe_trWireMsg_iff x).mp hwire).2.2

theorem kdfProv_receiveSignalMsg_at {tr : ExecTrace} (hc : KdfProvInv tr) {α : Type}
    (msgIdx : Nat) {f : TRSignalMsg → Traceful α}
    (hf : ∀ msg, KdfProvSafe tr msg.pqRatchet → KdfProvInv ((f msg).run tr).2.val) :
    KdfProvInv (((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at msgIdx tr hc fun raw _ hraw => ?_
  rcases hparse : parseTrSignalMsg raw with _ | msg
  · dsimp only; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hc
  dsimp only; rw [CompTrace.run_bind_assoc_snd]
  exact CompTrace.bind_guardP_at _ tr hc fun _ =>
    hf msg (parseTrSignalMsg_pqRatchet_kdfProvSafe (hc.of_attackerKnows hraw) hparse)

theorem kdfProv_preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) (tr : ExecTrace) (hc : KdfProvInv tr) :
    KdfProvInv ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hc (hc.append_rnd 32)
    fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ => ?_
  have htl : ∀ {α : Type} (g : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= g).run t).2.val = ((g t.length).run t).2.val := fun g t => by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let hs := aliceOut tr ikA ikBPk spkPk pqPk opk
  let tr1 := tr.append (RndE 32); let tr2 := tr1.append (RndE 32)
  let dhsA := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr2.length 32
  let stA : TRState :=
    { peer := b, myIk := DY.Libsignal.PQXDH.serializedIk hs.ikA, peerIk := DY.Libsignal.PQXDH.serializedIk hs.ikB,
      rk := (createChain hs.keys.rk hs.spk dhsA).1, dhs := dhsA, cks := (createChain hs.keys.rk hs.spk dhsA).2,
      ns := 0, pn := 0,
      sid := Concat.concat (DiffieHellman.dhPk dhsA) hs.keys.rk,
      initiator := true, rIdx := 1,
      recv := [{ ratchetKey := hs.spk, chainKey := hs.keys.ck, index := 0, rIdx := 1 }],
      spqr := Spqr.spqrInit hs.keys.pqr spqrA2B }
  let tr3 := tr2.append (RndE 32); let tr4 := tr3.append (NetE hs.ek); let tr5 := tr4.append (NetE hs.ct)
  let tr6 := tr5.append (EvE (PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys))
  let tr7 := tr6.append (TREvE (TREvent.InitSession a b (DiffieHellman.dhPk dhsA) hs.spk))
  let tr8 := tr7.append (CEvE (ComposedEvent.HandshakeSession (stA.sessionInfo a) tr5.length))
  rw [CompTrace.run_genRand_bind_snd]; dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, htl,
    CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  change KdfProvInv (tr8.append (TRStE a stA))
  have hc3 : KdfProvInv tr3 := ((hc.append_rnd 32).append_rnd 32).append_rnd 32
  have hc4 : KdfProvInv tr4 := hc3.append_net_of_safe (.dhPk (kdfProvSafe_random _ _))
  have hc5 : KdfProvInv tr5 := hc4.append_net_of_safe (kdfProvSafe_kemEncap_fst _ pqPk _)
  have hc8 : KdfProvInv tr8 := ((hc5.append_ev _).append_trEv _).append_cEv _
  have hpqr : KdfProvSafe tr8 hs.keys.pqr := by
    dsimp [hs, aliceOut, DY.Libsignal.PQXDH.aliceAgreement]; exact kdfProvSafe_pqxdhKdf_pqr tr8 _
  exact hc8.append_trSt (.spqrInit { authKey := hs.keys.pqr, params := spqrA2B } hpqr (kdfProvSafe_literal _ _))

theorem kdfProv_bobStart_commit {tr : ExecTrace} (hc : KdfProvInv tr)
    (b a : Participant) (sB sS sQ : DY.Bytes) (o : Option DY.Bytes) (ikA ek ct : DY.Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (dhs spqr' seed pqSalt m : DY.Bytes) (c' : RecvChain) (hspqr : KdfProvSafe tr spqr') :
    let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    KdfProvInv (((do
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
  intro st c; let doneIdx := tr.length
  have htl : ∀ {α : Type} (g : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= g).run t).2.val = ((g t.length).run t).2.val := fun g t => by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let tr₁ := tr.append (EvE (.BobDone b a (DiffieHellman.dhPk sB) ikA
    (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys))
  let tr₂ := tr₁.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
  let tr₃ := tr₂.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
  let tr₄ := tr₃.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
  have hc₄ : KdfProvInv tr₄ := (((hc.append_ev _).append_trEv _).append_trEv _).append_cEv _
  have hle₀₄ : tr ≤ tr₄ := Trace.le_trans _ _ _ (Trace.append_le tr _)
    (Trace.le_trans _ _ _ (Trace.append_le tr₁ _) (Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le tr₃ _)))
  let skipped := msg.counter.toNat - c.index.toNat; let childIdx := tr₄.length + skipped + 2
  let skipAct := DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
  let restAct : Unit → Traceful Nat := fun _ => do
    ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
    DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
      msg.counter c.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }
  rw [htl, CompPresTRExp.run_logEvent_bind_snd]; simp only [↓reduceIte]
  rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, htl]
  change KdfProvInv (((skipAct >>= restAct).run tr₄).2.val)
  rw [CompInv.CompPresBob.run_logSkippedKeys_bind_snd]
  let tr₅ := (skipAct.run tr₄).2.val; have hle₄₅ : tr₄ ≤ tr₅ := (skipAct.run tr₄).2.property
  have hc₅ : KdfProvInv tr₅ := KdfProvInv.logSkippedKeys_preserves (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx skipped c.chainKey c.index tr₄ hc₄
  let tr₆ := tr₅.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
  have hc₆ : KdfProvInv tr₆ := hc₅.append_trEv _
  have hle₀₆ : tr ≤ tr₆ := Trace.le_trans _ _ _ hle₀₄ (Trace.le_trans _ _ _ hle₄₅ (Trace.append_le tr₅ _))
  dsimp only [restAct]; rw [CompPresTRExp.run_logEvent_bind_snd]
  exact hc₆.append_logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
    msg.counter c.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' } (hspqr.mono hle₀₆)

theorem kdfProv_preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : KdfProvInv tr) :
    KdfProvInv ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hc
    fun sB sS sQ o ikA _ ek ct _ keys _ _ _ _ _ _ _ _ hbob => ?_
  refine kdfProv_receiveSignalMsg_at hc mh.msg fun msg hpq => ?_; dsimp only
  refine CompInv.CompPresBob.bind_ensureReceiverChain_bobInitSt
    a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey tr hc fun _ => ?_
  let dhs := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32
  let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
  let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
  let tr₁ := tr.append (RndE 32); have hc₁ : KdfProvInv tr₁ := hc.append_rnd 32
  rcases hConsume : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · dsimp only; rw [Traceful.run_failure]; exact hc₁
  dsimp only; rcases hSpqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
  · dsimp only; rw [Traceful.run_failure]; exact hc₁
  dsimp only
  have hkeys_eq : ∃ ikm, keys = DY.Libsignal.PQXDH.pqxdhKdf ikm := by
    dsimp only [DY.Libsignal.PQXDH.bobAgreement, Option.pure_def] at hbob
    injection hbob with h; exact ⟨_, h.symm⟩
  obtain ⟨_, hkeys_eq⟩ := hkeys_eq
  have hle₀₁ : tr ≤ tr₁ := Trace.append_le tr _
  have hpqr₁ : KdfProvSafe tr₁ keys.pqr := by rw [hkeys_eq]; exact kdfProvSafe_pqxdhKdf_pqr tr₁ _
  have hspqr₁ : KdfProvSafe tr₁ spqr' :=
    kdfProvSafe_spqrRecv_state hSpqr (.spqrInit { authKey := keys.pqr, params := spqrB2A } hpqr₁ (kdfProvSafe_literal _ _)) (hpq.mono hle₀₁)
  let tr₂ := tr₁.append (NetE key); have hle₁₂ : tr₁ ≤ tr₂ := Trace.append_le tr₁ _
  have hc₂ : KdfProvInv tr₂ := hc₁.append_net_of_safe (kdfProvSafe_spqrRecv_key hSpqr)
  have hspqr₂ : KdfProvSafe tr₂ spqr' := hspqr₁.mono hle₁₂
  rw [CompPresTRExp.run_sendMessage_bind_snd]
  change KdfProvInv (((Network.receiveMessage pqIdx >>= fun pqSalt =>
    DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed >>= fun m => _).run tr₂).2.val)
  refine CompTrace.bind_receiveMessage_at pqIdx tr₂ hc₂ fun pqSalt _ _ => ?_
  refine CompInv.CompPresBob.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr₂ hc₂ fun m _ => ?_
  cases o with
  | none =>
    dsimp only [Option.map]
    exact kdfProv_bobStart_commit hc₂ b a sB sS sQ none ikA ek ct keys msg dhs spqr' seed pqSalt m c' hspqr₂
  | some oSk =>
    dsimp only [Option.map]; rw [CompTrace.run_bind_snd]
    unfold DY.Libsignal.PQXDH.guardTrace; rw [Traceful.run_mk]; dsimp only
    by_cases hused : (!opkUsedB tr₂ b (DiffieHellman.dhPk oSk)) = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hused h]; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd]
      exact kdfProv_bobStart_commit (hc₂.append_ev _) b a sB sS sQ (some oSk) ikA ek ct keys msg dhs spqr' seed pqSalt m c'
        (hspqr₂.mono (Trace.append_le tr₂ _))
    · rw [ite_eq_right_iff.mpr fun h => absurd h hused]; dsimp only; exact hc₂

theorem kdfProv_preserves_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : KdfProvInv tr) :
    KdfProvInv ((DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  obtain ⟨_, _, _, _, _, hdhs, _, _, _, _⟩ := hinv.trStOK me st stateIdx hst
  have hspqr0 : KdfProvSafe tr st.spqr := hc.spqrSafe me st stateIdx hst
  apply CompTrace.bind_guardP_at _ tr hc; intro _
  rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_sendMessage_bind_snd]
  let m := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32; let tr1 := tr.append (RndE 32)
  let coins := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr1.length coinsLen; let tr2 := tr1.append (RndE coinsLen)
  let key := (Spqr.spqrSend st.spqr coins).2.1; let tr3 := tr2.append (NetE key)
  have hc3 : KdfProvInv tr3 := ((hc.append_rnd 32).append_rnd coinsLen).append_net_of_safe (kdfProvSafe_spqrSend_key tr2 st.spqr coins)
  have hle03 : tr ≤ tr3 := Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 (Trace.append_le tr _) (Trace.append_le tr1 _)) (Trace.append_le tr2 _)
  apply CompTrace.bind_receiveMessage_at pqIdx tr3 hc3; intro pqSalt _ _
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
    CompPresTRExp.run_logMessageKeyAndStore_bind_snd, CompPresTRExp.run_sendMessage_snd]
  let tr4 := tr3.append (TREvE (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m))
  have hc4 : KdfProvInv tr4 := hc3.append_trEv _
  have hle04 : tr ≤ tr4 := Trace.le_trans tr tr3 tr4 hle03 (Trace.append_le tr3 _)
  let st' : TRState := { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := (Spqr.spqrSend st.spqr coins).1 }
  have hspqr'_safe4 : KdfProvSafe tr4 st'.spqr := kdfProvSafe_spqrSend_state (hspqr0.mono hle04) (kdfProvSafe_random tr4 _)
  have hc6 : KdfProvInv ((DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) .sender (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st').run tr4).2.val :=
    hc4.append_logMessageKeyAndStore me (st.sessionInfo me) .sender
      (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st' hspqr'_safe4
  rw [CompPresTRExp.run_logMessageKeyAndStore_snd] at hc6
  let tr5 := tr4.append (TREvE (TREvent.MessageKey (st.sessionInfo me) .sender
    (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx))
  let tr6 := tr5.append (TRStE me st')
  have hdhs_safe : KdfProvSafe tr6 st.dhs := by
    rcases hdhs with ⟨t, hdhs_eq, _⟩ | ⟨t, _, hdhs_eq, _, _⟩ <;> [rw [hdhs_eq]; rw [hdhs_eq]] <;> exact kdfProvSafe_random tr6 _
  let mk := trMsgKeys pqSalt (kdfCk st.cks).2
  let wire := DY.Libsignal.TripleRatchet.trHonestWireMsg (DiffieHellman.dhPk st.dhs) st.ns st.pn
    (SymEnc.symEnc mk.cipherKey mk.iv m) (Spqr.spqrSend st.spqr coins).2.2
  have hwire_safe6 : KdfProvSafe tr6 wire :=
    kdfProvSafe_trHonestWireMsg st.ns st.pn (.dhPk hdhs_safe) (.symEnc (kdfProvSafe_random tr6 _)) (kdfProvSafe_spqrSend_msg tr6 st.spqr coins)
  exact hc6.append_net_of_safe (.concat hwire_safe6 (kdfProvSafe_computeMac_honest tr6 pqSalt (kdfCk st.cks).2
    st.myIk st.peerIk st.dhs st.ns st.pn m (Spqr.spqrSend st.spqr coins).2.2))

theorem kdfProv_preserves_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : KdfProvInv tr) :
    KdfProvInv ((DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  have hspqr0 : KdfProvSafe tr st.spqr := hc.spqrSafe me st stateIdx hst
  apply kdfProv_receiveSignalMsg_at hc msgIdx; intro msg hpq_safe
  apply CompPresTRExp.bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hc; intro ⟨ev⟩ _
  cases ev with
  | SkippedKeyStored s pk n seed rIdx _sourceStateIdx =>
    dsimp only; apply CompTrace.bind_guardP_at _ tr hc; intro _
    apply CompPresTRExp.bind_guardTrace_at _ tr hc; intro _
    rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; rw [CompPresTRExp.run_sendMessage_bind_snd]
    let tr1 := tr.append (NetE key); have hc1 : KdfProvInv tr1 := hc.append_net_of_safe (kdfProvSafe_spqrRecv_key hspqr_recv)
    have hle01 : tr ≤ tr1 := Trace.append_le tr _
    apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1; intro pqSalt _ _
    apply CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1; intro m
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    let tr2 := tr1.append (TREvE (TREvent.SkippedKeyUsed s skippedKeyEventIdx))
    let tr3 := tr2.append (TREvE (TREvent.Received me st.peer pk n m))
    have hc3 : KdfProvInv tr3 := (hc1.append_trEv _).append_trEv _
    have hle03 : tr ≤ tr3 := Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 hle01 (Trace.append_le tr1 _)) (Trace.append_le tr2 _)
    exact hc3.append_logMessageKeyAndStore me s .receiver seed pqSalt n rIdx stateIdx { st with spqr := spqr' } ((kdfProvSafe_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle03)
  | _ => dsimp only; rw [Traceful.run_failure]; exact hc

theorem kdfProv_preserves_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : KdfProvInv tr) :
    KdfProvInv ((DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  have hspqr0 : KdfProvSafe tr st.spqr := hc.spqrSafe me st stateIdx hst
  apply kdfProv_receiveSignalMsg_at hc msgIdx; intro msg hpq_safe
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor
  rcases hfind : findRecvChain st.recv msg.ratchetKey with _ | c
  · dsimp only; rcases hlow : x25519LowOrder msg.ratchetKey with _ | _
    · simp only [Bool.false_eq_true, ↓reduceIte, DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_bind_assoc_snd]
      apply CompTrace.bind_guardP_at _ tr hc; intro _
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_genRand_bind_snd, CompTrace.run_pure_bind_snd, CompTrace.run_pure_bind_snd]
      let tr1 := tr.append (RndE 32); have hc1 : KdfProvInv tr1 := hc.append_rnd 32
      have hle01 : tr ≤ tr1 := Trace.append_le tr _
      let dhs' := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32
      let rk1 := (createChain st.rk msg.ratchetKey st.dhs).1; let ckr := (createChain st.rk msg.ratchetKey st.dhs).2
      let rk2 := (createChain rk1 msg.ratchetKey dhs').1; let cks2 := (createChain rk1 msg.ratchetKey dhs').2
      let c_new : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := ckr, index := 0, rIdx := st.rIdx + 2 }
      let recv1 := (st.recv ++ [c_new]).drop ((st.recv.length + 1) - maxReceiverChains)
      let pn1 := if st.ns = 0 then 0 else st.ns - 1
      let st1 : TRState := { st with rk := rk2, dhs := dhs', cks := cks2, ns := 0, pn := pn1, rIdx := st.rIdx + 2, recv := recv1 }
      rcases hcons : consumeMessageKey c_new msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hc1
      dsimp only; rcases hspqr_recv : Spqr.spqrRecv st1.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hc1
      dsimp only; rw [CompPresTRExp.run_sendMessage_bind_snd]
      let tr2 := tr1.append (NetE key); have hc2 : KdfProvInv tr2 := hc1.append_net_of_safe (kdfProvSafe_spqrRecv_key hspqr_recv)
      have hle02 : tr ≤ tr2 := Trace.le_trans tr tr1 tr2 hle01 (Trace.append_le tr1 _)
      apply CompTrace.bind_receiveMessage_at pqIdx tr2 hc2; intro pqSalt _ _
      apply CompPresTRExp.bind_verifyMacAndDecrypt_at st1 msg pqSalt seed tr2 hc2; intro m
      simp only [↓reduceIte]; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
        CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompTrace.run_bind_snd]
      let tr3 := tr2.append (TREvE (TREvent.DHRatchet me st1.peer msg.ratchetKey (DiffieHellman.dhPk st1.dhs)))
      let tr4 := tr3.append (TREvE (TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2)))
      have hc4 : KdfProvInv tr4 := (hc2.append_trEv _).append_trEv _
      have hle04 : tr ≤ tr4 := Trace.le_trans tr tr2 tr4 hle02 (Trace.le_trans tr2 tr3 tr4 (Trace.append_le tr2 _) (Trace.append_le tr3 _))
      have hc5 := KdfProvInv.logSkippedKeys_preserves (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
        (msg.counter.toNat - c_new.index.toNat) c_new.chainKey c_new.index tr4 hc4
      have hle45 := ((DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
        c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4).2.property
      rcases hsk_res : (DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
          c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4 with ⟨_ | u, tr5_sub⟩
      · rw [hsk_res] at hc5; exact hc5
      · rw [hsk_res] at hc5 hle45; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
        let tr6 := tr5_sub.val.append (TREvE (TREvent.Received me st1.peer msg.ratchetKey msg.counter m))
        have hc6 : KdfProvInv tr6 := hc5.append_trEv _
        have hle06 : tr ≤ tr6 := Trace.le_trans tr tr4 tr6 hle04 (Trace.le_trans tr4 tr5_sub.val tr6 hle45 (Trace.append_le tr5_sub.val _))
        exact hc6.append_logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed pqSalt msg.counter
          c_new.rIdx stateIdx { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
          ((kdfProvSafe_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle06)
    · simp only [↓reduceIte]; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hc
  · dsimp only; rw [CompTrace.run_pure_bind_snd]
    rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; rw [CompPresTRExp.run_sendMessage_bind_snd]
    let tr1 := tr.append (NetE key); have hc1 : KdfProvInv tr1 := hc.append_net_of_safe (kdfProvSafe_spqrRecv_key hspqr_recv)
    have hle01 : tr ≤ tr1 := Trace.append_le tr _
    apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1; intro pqSalt _ _
    apply CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1; intro m
    simp only [Bool.false_eq_true, ↓reduceIte]; rw [CompTrace.run_bind_snd]
    have hc2 := KdfProvInv.logSkippedKeys_preserves (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
      (msg.counter.toNat - c.index.toNat) c.chainKey c.index tr1 hc1
    have hle12 := ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
      c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1).2.property
    rcases hsk_res : (DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
        c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1 with ⟨_ | u, tr2_sub⟩
    · rw [hsk_res] at hc2; exact hc2
    · rw [hsk_res] at hc2 hle12; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
      let tr3 := tr2_sub.val.append (TREvE (TREvent.Received me st.peer msg.ratchetKey msg.counter m))
      have hc3 : KdfProvInv tr3 := hc2.append_trEv _
      have hle03 : tr ≤ tr3 := Trace.le_trans tr tr1 tr3 hle01 (Trace.le_trans tr1 tr2_sub.val tr3 hle12 (Trace.append_le tr2_sub.val _))
      exact hc3.append_logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter
        c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }
        ((kdfProvSafe_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle03)

private theorem kdfProvSafe_of_eq_createChain_fst {T : ExecTrace} {rk pk sk x : DY.Bytes}
    (hx : x = (createChain rk pk sk).1) (h : HonestKdfOut T x) : KdfProvSafe T x := by
  subst hx; exact kdfProvSafe_createChain_fst T rk pk sk h

theorem kdfProv_preserves_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : KdfProvInv tr) :
    KdfProvInv ((DY.Libsignal.TripleRatchet.exposeKey me stateIdx k).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  obtain ⟨_, keys, _, hkeys, _, hdhs, _, hrk, hcks, hrecv⟩ := hinv.trStOK me st stateIdx hst
  cases k with
  | rk =>
    dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    obtain ⟨r, p, s, hrk_eq⟩ := hrk
    refine (hc.append_trEv _).append_net_of_safe ?_
    exact kdfProvSafe_of_eq_createChain_fst hrk_eq
      ⟨me, st, stateIdx, TRStoredAt.mono (Trace.append_le tr _) hst, Or.inl rfl⟩
  | dhs =>
    dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    have hc1 := hc.append_trEv (TREvent.ExposedDHs (st.sessionInfo me) st.dhs st.rIdx)
    rcases hdhs with ⟨t, hdhs_eq, _⟩ | ⟨t, _, hdhs_eq, _, _⟩
    · rw [hdhs_eq] at hc1 ⊢; exact hc1.append_net_rnd (t + 2) 32
    · rw [hdhs_eq] at hc1 ⊢; exact hc1.append_net_rnd t 32
  | cks =>
    dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    obtain ⟨rkChain, pk, sk, n, _, hcks_eq⟩ := hcks
    refine (hc.append_trEv _).append_net_of_safe ?_
    exact kdfProvSafe_of_eq_chainKeyAt_createChain_snd hcks_eq
      ⟨me, st, stateIdx, TRStoredAt.mono (Trace.append_le tr _) hst, Or.inr (Or.inl rfl)⟩
  | ckr pk =>
    dsimp only; rcases hfind : findRecvChain st.recv pk with _ | c; · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; have hc_mem : c ∈ st.recv := CompPresTRExp.findRecvChain_mem hfind
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    let tr1 := tr.append (TREvE (TREvent.ExposedCKr (st.sessionInfo me) c.chainKey c.index c.rIdx))
    have hc1 : KdfProvInv tr1 := hc.append_trEv _
    refine hc1.append_net_of_safe ?_
    have ho : HonestKdfOut tr1 c.chainKey :=
      ⟨me, st, stateIdx, TRStoredAt.mono (Trace.append_le tr _) hst, Or.inr (Or.inr ⟨c, hc_mem, rfl⟩)⟩
    obtain ⟨ikm, hikm⟩ := CompInv.CompPubInv.handshakeKeysAt_eq_pqxdhKdf hinv hkeys
    rcases hrecv c hc_mem with ⟨_, _, hck⟩ | ⟨n, _, _, hck⟩ | ⟨rkChain, pk', sk', n, _, hck⟩
    · exact kdfProvSafe_of_eq_chainKeyAt_pqxdhKdf_ck (n := 0) (by rw [hck, hikm]; rfl) ho
    · exact kdfProvSafe_of_eq_chainKeyAt_pqxdhKdf_ck (n := n + 1) (by rw [hck, hikm]) ho
    · exact kdfProvSafe_of_eq_chainKeyAt_createChain_snd hck ho

theorem kdfProv_preserves_exposeSkipped (skippedKeyEventIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : KdfProvInv tr) :
    KdfProvInv ((DY.Libsignal.TripleRatchet.exposeSkipped skippedKeyEventIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  apply CompPresTRExp.bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hc; intro ⟨ev⟩ he
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    dsimp only
    have hev : tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) skippedKeyEventIdx := by
      rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
    obtain ⟨_, _, _, _, hseed⟩ := hinv.skipOK s pk n seed rIdx src skippedKeyEventIdx hev
    apply CompPresTRExp.bind_guardTrace_at _ tr hc; intro _
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    let tr1 := tr.append (TREvE (TREvent.ExposedMK s seed n rIdx))
    have hc1 : KdfProvInv tr1 := hc.append_trEv _
    have hseed_shape : ∃ c, seed = (kdfCk c).2 := by rcases hseed with ⟨m, rfl⟩ | ⟨_, _, _, m, _, rfl⟩ <;> exact ⟨_, rfl⟩
    obtain ⟨c, rfl⟩ := hseed_shape
    exact hc1.append_net_of_safe (kdfProvSafe_kdfCk_snd tr1 c ⟨skippedKeyEventIdx, s, pk, n, rIdx, src, evAt_mono (Trace.append_le tr _) hev⟩)
  | _ => dsimp only; rw [Traceful.run_failure]; exact hc

theorem kdfProvInv_of_reachable {tr : ExecTrace} (hr : ReachableTrace tr) : KdfProvInv tr := by
  induction hr with
  | Base => exact kdfProvInv_nil
  | Step input hPre hReachPre hc =>
    have hinv : SpqrInv _ := spqrInv_of_reachable _ hReachPre
    have hst_bind : ∀ {S α : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
        (p : Participant) (s : S) (k : Nat → Traceful α) (t : ExecTrace),
        ((PersistentLocalState.storeLocalState p s >>= k).run t).2.val =
          ((k t.length).run (t.append (⟨⟨p, s⟩⟩ : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState S)))).2.val :=
      fun p s k t => by
        simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
        rw [CompTrace.run_bind_snd, Traceful.run_mk]
    have hst_snd : ∀ {S : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
        (p : Participant) (s : S) (t : ExecTrace),
        ((PersistentLocalState.storeLocalState p s).run t).2.val =
          t.append (⟨⟨p, s⟩⟩ : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState S)) :=
      fun p s t => by
        simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
    have hlog_snd : ∀ {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)] (ev : E) (t : ExecTrace),
        ((ProtocolEvent.logEvent ev).run t).2.val = t.append (⟨ev⟩ : ProtocolEvent.ExecEntryT E) := fun ev t => by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
      rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
    rcases input with ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k, _⟩, inp⟩
    · change DY.Bytes at inp; change KdfProvInv ((Network.sendMessage inp).run _).2.val; rw [CompPresTRExp.run_sendMessage_snd]
      exact hc.append_net_of_safe (hc.of_attackerKnows hPre)
    · change Participant at inp; change KdfProvInv ((registerIdentity inp).run _).2.val; unfold registerIdentity
      refine bind_guardOnTrace_at _ _ hc fun _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, hst_snd]
      exact ((((hc.append_rnd 32).append_ev _).append_net_of_safe
        (.dhPk (kdfProvSafe_random _ _))).append_net_of_safe (kdfProvSafe_vk _ _)).append_st inp _
    · rcases inp with ⟨p, skIdx⟩; change KdfProvInv ((registerCorruptIdentity p skIdx).run _).2.val; unfold registerCorruptIdentity
      refine bind_guardOnTrace_at _ _ hc fun _ => bind_receiveMessage_at skIdx _ hc fun _ _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, hlog_snd]; exact (hc.append_ev _).append_ev _
    · rcases inp with ⟨b, idStateIdx⟩; change KdfProvInv ((genSignedPrekey b idStateIdx).run _).2.val; unfold genSignedPrekey
      refine bind_getKey_at b idStateIdx .identity _ hc fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact (((((hc.append_rnd 32).append_rnd 64).append_ev _).append_st b _).append_net_of_safe
        (.dhPk (kdfProvSafe_random _ _))).append_net_of_safe (kdfProvSafe_sign _ _ _ _)
    · rcases inp with ⟨b, idStateIdx⟩; change KdfProvInv ((genPQPrekey b idStateIdx).run _).2.val; unfold genPQPrekey
      refine bind_getKey_at b idStateIdx .identity _ hc fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact (((((hc.append_rnd 64).append_rnd 64).append_ev _).append_st b _).append_net_of_safe
        (.kemPk (kdfProvSafe_random _ _))).append_net_of_safe (kdfProvSafe_sign _ _ _ _)
    · change Participant at inp; change KdfProvInv ((genOneTimePrekey inp).run _).2.val; unfold genOneTimePrekey
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd, hst_bind,
        CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact (((hc.append_rnd 32).append_ev _).append_st inp _).append_net_of_safe (.dhPk (kdfProvSafe_random _ _))
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩; exact kdfProv_preserves_aliceStart a b idStateIdx regIdxB bh _ hc
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩; exact kdfProv_preserves_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩; exact kdfProv_preserves_messageEncrypt me stateIdx coinsLen pqIdx _ hinv hc
    · rcases inp with ⟨me, stateIdx⟩; change KdfProvInv ((DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx).run _).2.val
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
      refine CompTrace.bind_getLocalState_tr_at me stateIdx _ hc fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, Traceful.run_failure]; exact hc.append_rnd 32
    · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩; exact kdfProv_preserves_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩; exact kdfProv_preserves_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, k⟩; exact kdfProv_preserves_exposeKey me stateIdx k _ hinv hc
    · rcases inp with ⟨me, stateIdx⟩; change KdfProvInv ((DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx).run _).2.val
      unfold DY.Libsignal.TripleRatchet.exposeSpqr
      apply CompTrace.bind_getLocalState_tr_at me stateIdx _ hc; intro st hst
      rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
      exact (hc.append_trEv _).append_net_of_safe ((hc.spqrSafe me st stateIdx hst).mono (Trace.append_le _ _))
    · exact kdfProv_preserves_exposeSkipped inp _ hinv hc
    · rcases inp with ⟨p, stateIdx⟩; change KdfProvInv ((compromiseIK p stateIdx).run _).2.val; unfold compromiseIK
      refine bind_getKey_at p stateIdx .identity _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _⟩ := hinv.stOK p { kind := .identity, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]; exact (hc.append_ev _).append_net_rnd t 32
    · rcases inp with ⟨b, stateIdx⟩; change KdfProvInv ((compromiseSPK b stateIdx).run _).2.val; unfold compromiseSPK
      refine bind_getKey_at b stateIdx .signedPrekey _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .signedPrekey, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]; exact (hc.append_ev _).append_net_rnd t 32
    · rcases inp with ⟨b, stateIdx⟩; change KdfProvInv ((compromisePQSPK b stateIdx).run _).2.val; unfold compromisePQSPK
      refine bind_getKey_at b stateIdx .pqPrekey _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .pqPrekey, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]; exact (hc.append_ev _).append_net_rnd t 64
    · rcases inp with ⟨b, stateIdx⟩; change KdfProvInv ((compromiseOPK b stateIdx).run _).2.val; unfold compromiseOPK
      refine bind_getKey_at b stateIdx .oneTimePrekey _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _⟩ := hinv.stOK b { kind := .oneTimePrekey, sk := sk } stateIdx hst
      refine CompPresPQXDH.Preserves.bind_guardOnTrace _ (fun _ hc _ => ?_) _ hc
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]; exact (hc.append_ev _).append_net_rnd t 32
    · change KdfProvInv ((DY.Libsignal.PQXDH.breakDH).run _).2.val; unfold DY.Libsignal.PQXDH.breakDH
      rw [hlog_snd]; exact hc.append_ev _
    · change KdfProvInv ((DY.Libsignal.PQXDH.breakKEM).run _).2.val; unfold DY.Libsignal.PQXDH.breakKEM
      rw [hlog_snd]; exact hc.append_ev _
    · change Nat at inp; change KdfProvInv ((invertDH inp).run _).2.val; unfold invertDH
      refine CompPresPQXDH.Preserves.bind_guardOnTrace DY.Libsignal.PQXDH.brokenDHB (fun tr hc _ => ?_) _ hc
      refine bind_receiveMessage_at inp tr hc fun pk _ hpk => ?_
      have hpk_safe : KdfProvSafe tr (X25519.normalizeX25519Key pk) := kdfProvSafe_x25519Key (hc.of_attackerKnows hpk)
      rcases hdh : DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
      · dsimp only; rw [Traceful.run_failure]; exact hc
      dsimp only; rw [CompPresTRExp.run_sendMessage_snd]; rw [dhSkOf_eq_some hdh] at hpk_safe
      exact hc.append_net_of_safe ((kdfProvSafe_dhPk_iff sk).mp hpk_safe)
    · change Nat at inp; change KdfProvInv ((invertKEM inp).run _).2.val; unfold invertKEM
      refine CompPresPQXDH.Preserves.bind_guardOnTrace DY.Libsignal.PQXDH.brokenKEMB (fun tr hc _ => ?_) _ hc
      refine bind_receiveMessage_at inp tr hc fun pk _ hpk => ?_
      have hpk_safe : KdfProvSafe tr pk := hc.of_attackerKnows hpk
      rcases hkem : PQKem.invertKemPublicKey pk with _ | sk
      · dsimp only [liftM, monadLift, MonadLift.monadLift]; rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; exact hc
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [CompPresTRExp.run_sendMessage_snd]
      rw [kemPkInvert_eq_some hkem] at hpk_safe; exact hc.append_net_of_safe ((kdfProvSafe_kemPk_iff sk).mp hpk_safe)
    · omega

theorem kdfProvSafe_of_attackerKnows_reachable {T : ExecTrace} (hT : ReachableTrace T)
    {b : DY.Bytes} (hAK : b.AttackerKnows T) : KdfProvSafe T b := (kdfProvInv_of_reachable hT).of_attackerKnows hAK

theorem kdfInputValidProv_of_attackerKnows_reachable {T : ExecTrace} (hT : ReachableTrace T)
    {s i : DY.Bytes} (h : (KdfExtract.kdfExtract s i).AttackerKnows T) : KdfInputValidProv T s i :=
  (kdfProvSafe_kdfExtract_iff s i).mp (kdfProvSafe_of_attackerKnows_reachable hT h)

/-! ## Label-case provenance corollaries -/

/-- If the attacker knows `kdfExtract s i` on a reachable trace, with `i` neither the message-key
label `0x01` nor an SPQR auth-key label `concat _ (concat pqxdhLabel (litByte 3))`, then either
`s` is attacker-known or the term satisfies `HonestKdfOut`. -/
theorem kdfProv_non01_of_reachable {T : ExecTrace} (hT : ReachableTrace T) {s i : DY.Bytes}
    (hk : (KdfExtract.kdfExtract s i).AttackerKnows T)
    (h01 : i ≠ litByte 0x01)
    (hpq3 : ∀ b1, i ≠ Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3))) :
    s.AttackerKnows T ∨ HonestKdfOut T (KdfExtract.kdfExtract s i) := by
  rcases kdfInputValidProv_of_attackerKnows_reachable hT hk with
    ⟨hs, _⟩ | ⟨hi, _⟩ | ⟨_, ho⟩ | ⟨_, ho⟩ | ⟨_, _, ho⟩ | ⟨_, _, ho⟩ | ⟨b1, hi⟩
  · exact .inl hs
  · exact absurd hi h01
  · exact .inr ho
  · exact .inr ho
  · exact .inr ho
  · exact .inr ho
  · exact absurd hi (hpq3 b1)

private theorem litByte_ne_pq3 (x : UInt8) (b1 : DY.Bytes) :
    litByte x ≠ Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3)) :=
  Symbolic.Swarm.COMPOSED.CompRatchet.litByte_ne_concat x _ _

private theorem concat_concat_ne_pq3 (a l : DY.Bytes) {x : UInt8} (hx : x ≠ 3) (b1 : DY.Bytes) :
    Concat.concat a (Concat.concat l (litByte x)) ≠
      Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3)) := by
  intro h
  exact hx (Symbolic.Swarm.COMPOSED.CompTermAlgebra.litByte_inj
    (Symbolic.Swarm.COMPOSED.CompTermAlgebra.concat_inj
      (Symbolic.Swarm.COMPOSED.CompTermAlgebra.concat_inj h).2).2)

theorem kdfProv_litByte02_of_reachable {T : ExecTrace} (hT : ReachableTrace T) {s : DY.Bytes}
    (hk : (KdfExtract.kdfExtract s (litByte 0x02)).AttackerKnows T) :
    s.AttackerKnows T ∨ HonestKdfOut T (KdfExtract.kdfExtract s (litByte 0x02)) :=
  kdfProv_non01_of_reachable hT hk
    (fun h => absurd (Symbolic.Swarm.COMPOSED.CompTermAlgebra.litByte_inj h) (by decide))
    (litByte_ne_pq3 _)

theorem kdfProv_wr2_of_reachable {T : ExecTrace} (hT : ReachableTrace T) {s b1 : DY.Bytes}
    (hk : (KdfExtract.kdfExtract s
      (Concat.concat b1 (Concat.concat (lit "WhisperRatchet") (litByte 2)))).AttackerKnows T) :
    s.AttackerKnows T ∨ HonestKdfOut T (KdfExtract.kdfExtract s
      (Concat.concat b1 (Concat.concat (lit "WhisperRatchet") (litByte 2)))) :=
  kdfProv_non01_of_reachable hT hk
    (fun h => Symbolic.Swarm.COMPOSED.CompRatchet.litByte_ne_concat _ _ _ h.symm)
    (concat_concat_ne_pq3 _ _ (by decide))

end Symbolic.Swarm.CREF.TR.G1
