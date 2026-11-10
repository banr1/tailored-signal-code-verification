/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompSchedule
public import Symbolic.Proofs.Swarm.COMPOSED.CompPcsGlue
import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.Misc.Fixpoint
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
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
public import Symbolic.Proofs.Swarm.COMPOSED.CompPresBob
import Symbolic.Proofs.Swarm.COMPOSED.CompHsClass
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompLineage
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.Misc.Fixpoint
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

/-!
# Composed Post-Compromise Security

Proves `DY.Libsignal.Composed.Security.PostCompromiseSecurity` by showing preservation of the
witness-based closure invariant `CompClosedInvW` across reachable composed traces, discharging the
handshake-excuse bridge under `CompPcsWitnessExposure`, and instantiating `ReachableCompPCSBundle`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompRatchet

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir RecvChain KeyComponent hmac createChain kdfCk
  chainKeyAt findRecvChain setRecvChain recvChainFor consumeMessageKey x25519LowOrder
  maxReceiverChains zeroSalt computeMac)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles
  PreKeyMsgHandles pqxdhKdf pqxdhIkm agree guardTrace opkUsedB registerIdentity
  registerCorruptIdentity genSignedPrekey genPQPrekey genOneTimePrekey compromiseIK compromiseSPK
  compromisePQSPK compromiseOPK breakDH breakKEM invertDH invertKEM HandshakeKeysAt
  HandshakeWasCompromisedAt)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg trMsgKeys spqrA2B parseTrSignalMsg
  receiveSignalMsg ensureReceiverChain dhRatchetStep verifyMacAndDecrypt logSkippedKeys
  logMessageKeyAndStore messageEncrypt messageEncryptAbort messageDecrypt messageDecryptSkipped
  exposeKey exposeSpqr exposeSkipped traceLength)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompTermAlgebra
open Symbolic.Swarm.COMPOSED.CompKeyInversion

/-! ## `CompClosedInvW` Reachability Preservation -/

section ClosedInvW

open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED.CompPresPQXDH

private theorem isScheduleKey_chainKeyAt_createChain_snd_pcs (rk pk sk : Bytes) (n : Nat) :
    CompPcsEngine.IsScheduleKey (chainKeyAt (createChain rk pk sk).2 n) := by
  cases n with
  | zero => exact .inr (.inl ⟨rk, pk, sk, rfl⟩)
  | succ m =>
    exact .inr (.inr (.inr (.inl ⟨chainKeyAt (createChain rk pk sk).2 m,
      chainKeyAt_succ_eq_kdfCk_fst (createChain rk pk sk).2 m⟩)))

private theorem isScheduleKey_of_recvChainInv_pcs {tr : ExecTrace}
    (hinv : SpqrInv tr) {j : Nat} {keys : HandshakeKeys}
    (hkeys : HandshakeKeysAt tr j keys)
    {c : RecvChain} (hc : Symbolic.Swarm.COMPOSED.CompPresTRExp.RecvChainInv keys c) :
    CompPcsEngine.IsScheduleKey c.chainKey := by
  rcases hc with ⟨_, _, hck⟩ | ⟨n, _, _, hck⟩ | ⟨rkChain, pk, sk, n, _, hck⟩
  · obtain ⟨ikm, hikm⟩ := CompPubInv.handshakeKeysAt_eq_pqxdhKdf hinv hkeys
    exact .inr (.inr (.inl ⟨ikm, hck.trans (congrArg HandshakeKeys.ck hikm)⟩))
  · exact .inr (.inr (.inr (.inl ⟨chainKeyAt keys.ck n,
      hck.trans (chainKeyAt_succ_eq_kdfCk_fst keys.ck n)⟩)))
  · rw [hck]
    exact isScheduleKey_chainKeyAt_createChain_snd_pcs rkChain pk sk n

/-- Trace invariant closing network messages and stored `TRState` SPQR states under
`CompTightClosedW`. -/
structure CompClosedInvW (tr : ExecTrace) : Prop where
  baseClosed : ∀ b, tr.BaseAttackerKnows b → CompTightClosedW tr b
  spqrClosed : ∀ me st idx, TRStoredAt tr me st idx → CompTightClosedW tr st.spqr

theorem compClosedInvW_nil : CompClosedInvW Trace.nil :=
  { baseClosed := fun _ h => False.elim ((Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1 _).mp h)
    spqrClosed := fun _ _ idx h => by simp [TRStoredAt, Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at h }

theorem CompClosedInvW.of_attackerKnows {tr : ExecTrace} (hc : CompClosedInvW tr)
    {b : Bytes} (hk : b.AttackerKnows tr) : CompTightClosedW tr b :=
  CompTightClosedW.of_attackerKnows hc.baseClosed hk

theorem CompClosedInvW.append_rnd {tr : ExecTrace} (hc : CompClosedInvW tr) (n : Nat) :
    CompClosedInvW (tr.append (RndE n)) := by
  have hle : tr ≤ tr.append (RndE n) := Trace.append_le tr (RndE n)
  refine ⟨fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_rnd tr n b).mp hb)).mono hle,
    fun me st idx hst => (hc.spqrClosed me st idx
      (CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CompClosedInvW.append_ev {tr : ExecTrace} (hc : CompClosedInvW tr) (ev : PQXDHEvent) :
    CompClosedInvW (tr.append (EvE ev)) := by
  have hle : tr ≤ tr.append (EvE ev) := Trace.append_le tr (EvE ev)
  refine ⟨fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_pqEv tr ev b).mp hb)).mono hle,
    fun me st idx hst => (hc.spqrClosed me st idx
      (CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CompClosedInvW.append_trEv {tr : ExecTrace} (hc : CompClosedInvW tr) (ev : TREvent) :
    CompClosedInvW (tr.append (TREvE ev)) := by
  have hle : tr ≤ tr.append (TREvE ev) := Trace.append_le tr (TREvE ev)
  refine ⟨fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_trEv tr ev b).mp hb)).mono hle,
    fun me st idx hst => (hc.spqrClosed me st idx
      (CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CompClosedInvW.append_cEv {tr : ExecTrace} (hc : CompClosedInvW tr) (ev : ComposedEvent) :
    CompClosedInvW (tr.append (CEvE ev)) := by
  have hle : tr ≤ tr.append (CEvE ev) := Trace.append_le tr (CEvE ev)
  refine ⟨fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_cEv tr ev b).mp hb)).mono hle,
    fun me st idx hst => (hc.spqrClosed me st idx
      (CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CompClosedInvW.append_st {tr : ExecTrace} (hc : CompClosedInvW tr)
    (me : Participant) (st : PQXDHState) :
    CompClosedInvW (tr.append (StE me st)) := by
  have hle : tr ≤ tr.append (StE me st) := Trace.append_le tr (StE me st)
  refine ⟨fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_pqSt tr me st b).mp hb)).mono hle,
    fun me' st' idx hst => (hc.spqrClosed me' st' idx
      (CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩

theorem CompClosedInvW.append_net {tr : ExecTrace} (hc : CompClosedInvW tr) {msg : Bytes}
    (hmsg : CompTightClosedW (tr.append (NetE msg)) msg) :
    CompClosedInvW (tr.append (NetE msg)) := by
  have hle : tr ≤ tr.append (NetE msg) := Trace.append_le tr (NetE msg)
  refine ⟨fun b hb => ?_, fun me st idx hst => ?_⟩
  · rcases (CompTrace.baseAttackerKnows_append_net tr msg b).mp hb with rfl | hb'
    · exact hmsg
    · exact (hc.baseClosed b hb').mono hle
  · exact (hc.spqrClosed me st idx
      (CompPresBob.trStoredAt_append_other rfl hst)).mono hle

theorem CompClosedInvW.append_net_of_closed {tr : ExecTrace} (hc : CompClosedInvW tr) {msg : Bytes}
    (hmsg : CompTightClosedW tr msg) :
    CompClosedInvW (tr.append (NetE msg)) :=
  hc.append_net (hmsg.mono (Trace.append_le tr (NetE msg)))

theorem CompClosedInvW.append_net_rnd {tr : ExecTrace} (hc : CompClosedInvW tr) (t n : Nat) :
    CompClosedInvW (tr.append (NetE (mkRand t n))) := by
  refine hc.append_net (.exposed (.rand (.inl ?_)))
  exact Bytes.AttackerKnows.prove_from_base (mkRand t n) (tr.append (NetE (mkRand t n)))
    ((CompTrace.baseAttackerKnows_append_net tr (mkRand t n) (mkRand t n)).mpr (.inl rfl))

theorem CompClosedInvW.append_trSt_at {tr : ExecTrace} (hc : CompClosedInvW tr)
    {me : Participant} {st : TRState}
    (hspqr : CompTightClosedW (tr.append (TRStE me st)) st.spqr) :
    CompClosedInvW (tr.append (TRStE me st)) := by
  have hle : tr ≤ tr.append (TRStE me st) := Trace.append_le tr (TRStE me st)
  refine ⟨fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_trSt tr me st b).mp hb)).mono hle,
    fun me' st' idx hst => ?_⟩
  rcases CompPresBob.trStoredAt_append_same hst with ⟨_, hst'⟩ | ⟨_, _, rfl⟩
  · exact (hc.spqrClosed me' st' idx hst').mono hle
  · exact hspqr

theorem CompClosedInvW.append_trSt {tr : ExecTrace} (hc : CompClosedInvW tr)
    {me : Participant} {st : TRState} (hspqr : CompTightClosedW tr st.spqr) :
    CompClosedInvW (tr.append (TRStE me st)) :=
  hc.append_trSt_at (hspqr.mono (Trace.append_le tr (TRStE me st)))

theorem CompClosedInvW.logSkippedKeys_preserves (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : Bytes) (n : UInt32) (tr : ExecTrace),
      CompClosedInvW tr →
      CompClosedInvW ((logSkippedKeys s pk rIdx src ck n k).run tr).2.val
  | 0, _, _, _, hc => by rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc
  | k + 1, ck, n, tr, hc => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    exact CompClosedInvW.logSkippedKeys_preserves s pk rIdx src k (kdfCk ck).1 (n + 1) _
      (hc.append_trEv _)

theorem CompClosedInvW.append_logMessageKeyAndStore {tr : ExecTrace} (hc : CompClosedInvW tr)
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (seed pqSalt : Bytes)
    (n : UInt32) (rIdx prev : Nat) (st : TRState) (hspqr : CompTightClosedW tr st.spqr) :
    CompClosedInvW ((logMessageKeyAndStore me s dir seed pqSalt n rIdx prev st).run tr).2.val := by
  rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logMessageKeyAndStore_snd]
  exact (hc.append_trEv _).append_trSt (hspqr.mono (Trace.append_le tr _))

theorem closedW_preserves_net (msg : Bytes) (tr : ExecTrace) (hPre : msg.AttackerKnows tr)
    (hc : CompClosedInvW tr) : CompClosedInvW ((Network.sendMessage msg).run tr).2.val := by
  rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
  exact hc.append_net_of_closed (hc.of_attackerKnows hPre)

theorem closedW_preserves_registerIdentity (p : Participant) (tr : ExecTrace)
    (hc : CompClosedInvW tr) : CompClosedInvW ((registerIdentity p).run tr).2.val := by
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

theorem closedW_preserves_registerCorruptIdentity (p : Participant) (skIdx : Nat) (tr : ExecTrace)
    (hc : CompClosedInvW tr) : CompClosedInvW ((registerCorruptIdentity p skIdx).run tr).2.val := by
  unfold registerCorruptIdentity
  refine bind_guardOnTrace_at _ tr hc fun _ => ?_
  refine bind_receiveMessage_at skIdx tr hc fun _ _ _ => ?_
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact (hc.append_ev _).append_ev _

theorem closedW_preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) (tr : ExecTrace)
    (hc : CompClosedInvW tr) : CompClosedInvW ((genSignedPrekey b idStateIdx).run tr).2.val := by
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

theorem closedW_preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) (tr : ExecTrace)
    (hc : CompClosedInvW tr) : CompClosedInvW ((genPQPrekey b idStateIdx).run tr).2.val := by
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

theorem closedW_preserves_genOneTimePrekey (b : Participant) (tr : ExecTrace)
    (hc : CompClosedInvW tr) : CompClosedInvW ((genOneTimePrekey b).run tr).2.val := by
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

theorem closedW_preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) (tr : ExecTrace) (hc : CompClosedInvW tr) :
    CompClosedInvW ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
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
  change CompClosedInvW tr9
  have hc3 : CompClosedInvW tr3 := ((hc.append_rnd 32).append_rnd 32).append_rnd 32
  have hc4 : CompClosedInvW tr4 := hc3.append_net_of_closed (.dhPkRand ⟨tr.length, 32, rfl⟩)
  have hc5 : CompClosedInvW tr5 := hc4.append_net_of_closed (.kemEncap pqPk (rnd (tr.length + 1) 32))
  have hc8 : CompClosedInvW tr8 := ((hc5.append_ev _).append_trEv _).append_cEv _
  exact hc8.append_trSt (.spqrInit (.exposed .pqr) (.literal _))

theorem closedW_receiveSignalMsg_at {tr : ExecTrace} (hc : CompClosedInvW tr) {α : Type}
    (msgIdx : Nat) {f : TRSignalMsg → Traceful α}
    (hf : ∀ msg, CompTightClosedW tr msg.pqRatchet → CompClosedInvW ((f msg).run tr).2.val) :
    CompClosedInvW (((receiveSignalMsg msgIdx >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at msgIdx tr hc fun raw _ hraw => ?_
  rcases hparse : parseTrSignalMsg raw with _ | msg
  · rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc
  · dsimp only [MonadLiftT.monadLift, MonadLift.monadLift]
    rw [CompTrace.run_bind_assoc_snd]
    refine CompTrace.bind_guardP_at _ tr hc fun _ => ?_
    exact hf msg (CompTightClosedW.parseTrSignalMsg_pqRatchet (hc.of_attackerKnows hraw) hparse)

theorem closedW_bobStart_commit {tr : ExecTrace} (hc : CompClosedInvW tr)
    (b a : Participant) (sB sS sQ : Bytes) (o : Option Bytes)
    (ikA ek ct : Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (dhs spqr' seed pqSalt m : Bytes) (c' : RecvChain)
    (hspqr : CompTightClosedW tr spqr') :
    let st := CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    CompClosedInvW (((do
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
  have hc₄ : CompClosedInvW tr₄ := (((hc.append_ev _).append_trEv _).append_trEv _).append_cEv _
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
  change CompClosedInvW (((skipAct >>= restAct).run tr₄).2.val)
  rw [CompPresBob.run_logSkippedKeys_bind_snd]
  let tr₅ := (skipAct.run tr₄).2.val
  have hle₄₅ : tr₄ ≤ tr₅ := (skipAct.run tr₄).2.property
  have hc₅ : CompClosedInvW tr₅ :=
    CompClosedInvW.logSkippedKeys_preserves (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx skipped
      c.chainKey c.index tr₄ hc₄
  dsimp only [restAct]
  rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
  let tr₆ := tr₅.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
  have hc₆ : CompClosedInvW tr₆ := hc₅.append_trEv _
  have hle₀₆ : tr ≤ tr₆ :=
    Trace.le_trans _ _ _ hle₀₄ (Trace.le_trans _ _ _ hle₄₅ (Trace.append_le tr₅ _))
  exact hc₆.append_logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
    msg.counter c.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }
    (hspqr.mono hle₀₆)

theorem closedW_preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace)
    (hc : CompClosedInvW tr) :
    CompClosedInvW ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hc
    fun sB sS sQ o ikA _ ek ct _ keys _ _ _ _ _ _ _ _ hbob => ?_
  refine closedW_receiveSignalMsg_at hc mh.msg fun msg hpq => ?_
  dsimp only
  refine CompPresBob.bind_ensureReceiverChain_bobInitSt
    a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey tr hc fun _ => ?_
  let dhs := rnd tr.length 32
  let st := CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
  let c := CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
  let tr₁ := tr.append (RndE 32)
  have hc₁ : CompClosedInvW tr₁ := hc.append_rnd 32
  rcases hConsume : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc₁
  · dsimp only
    rcases hSpqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc₁
    · dsimp only
      rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_bind_snd]
      obtain ⟨e, _, hkeys_eq⟩ := CompPresBob.kemDecap_of_bobAgreement hbob
      have hle₀₁ : tr ≤ tr₁ := Trace.append_le tr _
      have hpqr₁ : CompTightClosedW tr₁ keys.pqr := by
        rw [hkeys_eq]; exact .exposed .pqr
      have hspqr₁ : CompTightClosedW tr₁ spqr' :=
        CompTightClosedW.spqrRecvState_of hSpqr (.spqrInit hpqr₁ (.literal _)) (hpq.mono hle₀₁)
      let tr₂ := tr₁.append (NetE key)
      have hle₁₂ : tr₁ ≤ tr₂ := Trace.append_le tr₁ _
      have hc₂ : CompClosedInvW tr₂ := hc₁.append_net_of_closed (CompTightClosedW.spqrRecvKey_of hSpqr)
      have hspqr₂ : CompTightClosedW tr₂ spqr' := hspqr₁.mono hle₁₂
      refine CompTrace.bind_receiveMessage_at pqIdx tr₂ hc₂ fun pqSalt _ _ => ?_
      refine CompPresBob.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr₂ hc₂ fun m _ => ?_
      cases o with
      | none =>
        dsimp only [Option.map]
        exact closedW_bobStart_commit hc₂ b a sB sS sQ none ikA ek ct keys msg dhs spqr' seed pqSalt m c' hspqr₂
      | some oSk =>
        dsimp only [Option.map]
        refine bind_guardOnTrace_at (!opkUsedB · b (DiffieHellman.dhPk oSk)) tr₂ hc₂ fun _ => ?_
        rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := PQXDHEvent)]
        let tr₃ := tr₂.append (EvE (.OPKUsed b (DiffieHellman.dhPk oSk)))
        have hc₃ : CompClosedInvW tr₃ := hc₂.append_ev _
        exact closedW_bobStart_commit hc₃ b a sB sS sQ (some oSk) ikA ek ct keys msg dhs spqr' seed pqSalt m c'
          (hspqr₂.mono (Trace.append_le tr₂ _))

theorem closedW_preserves_messageEncryptAbort (me : Participant) (stateIdx : Nat) (tr : ExecTrace)
    (hc : CompClosedInvW tr) : CompClosedInvW ((messageEncryptAbort me stateIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro _ _
  rw [CompTrace.run_genRand_bind_snd, Traceful.run_failure]
  exact hc.append_rnd 32

theorem closedW_preserves_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInvW tr) :
    CompClosedInvW ((messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  obtain ⟨_, _, _, _, _, hdhs, _, _, _, _⟩ := hinv.trStOK me st stateIdx hst
  have hspqr0 : CompTightClosedW tr st.spqr := hc.spqrClosed me st stateIdx hst
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
  have hc3 : CompClosedInvW tr3 :=
    ((hc.append_rnd 32).append_rnd coinsLen).append_net_of_closed
      (CompTightClosedW.spqrSendKey_of st.spqr coins)
  have hle03 : tr ≤ tr3 :=
    Trace.le_trans tr tr2 tr3
      (Trace.le_trans tr tr1 tr2 (Trace.append_le tr _) (Trace.append_le tr1 _))
      (Trace.append_le tr2 _)
  apply CompTrace.bind_receiveMessage_at pqIdx tr3 hc3
  intro pqSalt _ _
  rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
    Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logMessageKeyAndStore_bind_snd,
    Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
  let tr4 := tr3.append (TREvE (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m))
  let tr5 := tr4.append (TREvE (TREvent.MessageKey (st.sessionInfo me) .sender
    (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx))
  let st' : TRState :=
    { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := (Spqr.spqrSend st.spqr coins).1 }
  let tr6 := tr5.append (TRStE me st')
  have hc5 : CompClosedInvW tr5 := (hc3.append_trEv _).append_trEv _
  have hle06 : tr ≤ tr6 :=
    Trace.le_trans tr tr3 tr6 hle03
      (Trace.le_trans tr3 tr5 tr6
        (Trace.le_trans tr3 tr4 tr5 (Trace.append_le tr3 _) (Trace.append_le tr4 _))
        (Trace.append_le tr5 _))
  have hcoins_w6 : MsgEncWitnessAt tr6 coins :=
    .inl ⟨me, st', tr5.length, st.spqr, CompTrace.at?_append_here tr5 (TRStE me st'), rfl⟩
  have hcoins_closed6 : CompTightClosedW tr6 coins := .exposed (.rand (.inr hcoins_w6))
  have hspqr'_closed6 : CompTightClosedW tr6 st'.spqr :=
    .spqrSendState (hspqr0.mono hle06) hcoins_closed6
  have hc6 : CompClosedInvW tr6 := hc5.append_trSt_at hspqr'_closed6
  have hdhs_rnd : ∃ ts sz, st.dhs = mkRand ts sz := by
    rcases hdhs with ⟨t, hdhs_eq, _⟩ | ⟨t, _, hdhs_eq, _, _⟩
    · exact ⟨t + 2, 32, hdhs_eq⟩
    · exact ⟨t, 32, hdhs_eq⟩
  let mk := trMsgKeys pqSalt (kdfCk st.cks).2
  let wire := DY.Libsignal.TripleRatchet.trHonestWireMsg (DiffieHellman.dhPk st.dhs) st.ns st.pn
    (SymEnc.symEnc mk.cipherKey mk.iv m) (Spqr.spqrSend st.spqr coins).2.2
  let mac := computeMac mk.macKey st.myIk st.peerIk wire
  let tr7 := tr6.append (NetE (Concat.concat wire mac))
  have hm_w7 : MsgEncWitnessAt tr7 m :=
    .inr ⟨_, _, _, _, _, _, _, _, _, (CompTrace.baseAttackerKnows_append_net tr6 (Concat.concat wire mac) _).mpr (.inl rfl)⟩
  have hm_closed7 : CompTightClosedW tr7 m := .exposed (.rand (.inr hm_w7))
  have hwire_closed7 : CompTightClosedW tr7 wire :=
    .trWireMsg (.dhPkRand hdhs_rnd) (.symEnc hm_closed7)
      (CompTightClosedW.spqrSendMsg_of st.spqr coins)
  exact hc6.append_net (.concat hwire_closed7 (.trunc8 _))

theorem closedW_preserves_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32)
    (tr : ExecTrace) (hc : CompClosedInvW tr) :
    CompClosedInvW ((messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  have hspqr0 : CompTightClosedW tr st.spqr := hc.spqrClosed me st stateIdx hst
  apply closedW_receiveSignalMsg_at hc msgIdx
  intro msg hpq_closed
  apply Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hc
  intro e _; rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
    dsimp only
    apply CompTrace.bind_guardP_at _ tr hc; intro _
    apply Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_guardTrace_at _ tr hc; intro _
    rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc
    · dsimp only
      rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_bind_snd]
      let tr1 := tr.append (NetE key)
      have hc1 : CompClosedInvW tr1 :=
        hc.append_net_of_closed (CompTightClosedW.spqrRecvKey_of hspqr_recv)
      have hle01 : tr ≤ tr1 := Trace.append_le tr _
      apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1
      intro pqSalt _ _
      apply Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1
      intro m
      rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
        Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
      let tr2 := tr1.append (TREvE (TREvent.SkippedKeyUsed s skippedKeyEventIdx))
      let tr3 := tr2.append (TREvE (TREvent.Received me st.peer pk n m))
      have hc3 : CompClosedInvW tr3 := (hc1.append_trEv _).append_trEv _
      have hle03 : tr ≤ tr3 :=
        Trace.le_trans tr tr2 tr3
          (Trace.le_trans tr tr1 tr2 hle01 (Trace.append_le tr1 _))
          (Trace.append_le tr2 _)
      have hspqr'_closed3 : CompTightClosedW tr3 spqr' :=
        (CompTightClosedW.spqrRecvState_of hspqr_recv hspqr0 hpq_closed).mono hle03
      exact hc3.append_logMessageKeyAndStore me s .receiver seed pqSalt n rIdx stateIdx { st with spqr := spqr' } hspqr'_closed3
  | _ => dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc

theorem closedW_preserves_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : CompClosedInvW tr) :
    CompClosedInvW ((messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  have hspqr0 : CompTightClosedW tr st.spqr := hc.spqrClosed me st stateIdx hst
  apply closedW_receiveSignalMsg_at hc msgIdx
  intro msg hpq_closed
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor
  rcases hfind : findRecvChain st.recv msg.ratchetKey with _ | c
  · dsimp only
    rcases hlow : x25519LowOrder msg.ratchetKey with _ | _
    · simp only [Bool.false_eq_true, ↓reduceIte, DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_bind_assoc_snd]
      apply CompTrace.bind_guardP_at _ tr hc; intro _
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_genRand_bind_snd,
        CompTrace.run_pure_bind_snd, CompTrace.run_pure_bind_snd]
      let tr1 := tr.append (RndE 32)
      have hc1 : CompClosedInvW tr1 := hc.append_rnd 32
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
          have hc2 : CompClosedInvW tr2 :=
            hc1.append_net_of_closed (CompTightClosedW.spqrRecvKey_of hspqr_recv)
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
          have hc4 : CompClosedInvW tr4 := (hc2.append_trEv _).append_trEv _
          have hle24 : tr2 ≤ tr4 :=
            Trace.le_trans tr2 tr3 tr4 (Trace.append_le tr2 _) (Trace.append_le tr3 _)
          have hle04 : tr ≤ tr4 := Trace.le_trans tr tr2 tr4 hle02 hle24
          have hc5 : CompClosedInvW
              ((logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
                c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4).2.val :=
            CompClosedInvW.logSkippedKeys_preserves (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
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
          · rw [hsk_res] at hc5 hle45; dsimp only
            rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
            let tr6 := tr5_sub.val.append (TREvE (TREvent.Received me st1.peer msg.ratchetKey msg.counter m))
            have hc6 : CompClosedInvW tr6 := hc5.append_trEv _
            have hle06 : tr ≤ tr6 :=
              Trace.le_trans tr tr4 tr6 hle04
                (Trace.le_trans tr4 tr5_sub.val tr6 hle45 (Trace.append_le tr5_sub.val _))
            let st2 : TRState := { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
            have hspqr'_closed6 : CompTightClosedW tr6 spqr' :=
              (CompTightClosedW.spqrRecvState_of hspqr_recv hspqr0 hpq_closed).mono hle06
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
        have hc1 : CompClosedInvW tr1 :=
          hc.append_net_of_closed (CompTightClosedW.spqrRecvKey_of hspqr_recv)
        have hle01 : tr ≤ tr1 := Trace.append_le tr _
        apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1
        intro pqSalt _ _
        apply Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1
        intro m
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [CompTrace.run_bind_snd]
        have hc2 : CompClosedInvW
            ((logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
              c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1).2.val :=
          CompClosedInvW.logSkippedKeys_preserves (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
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
        · rw [hsk_res] at hc2 hle12; dsimp only
          rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
          let tr3 := tr2_sub.val.append (TREvE (TREvent.Received me st.peer msg.ratchetKey msg.counter m))
          have hc3 : CompClosedInvW tr3 := hc2.append_trEv _
          have hle03 : tr ≤ tr3 :=
            Trace.le_trans tr tr1 tr3 hle01
              (Trace.le_trans tr1 tr2_sub.val tr3 hle12 (Trace.append_le tr2_sub.val _))
          let st2 : TRState := { st with recv := setRecvChain st.recv c', spqr := spqr' }
          have hspqr'_closed3 : CompTightClosedW tr3 spqr' :=
            (CompTightClosedW.spqrRecvState_of hspqr_recv hspqr0 hpq_closed).mono hle03
          exact hc3.append_logMessageKeyAndStore me (st.sessionInfo me) .receiver
            seed pqSalt msg.counter c.rIdx stateIdx st2 hspqr'_closed3

theorem closedW_preserves_exposeSpqr (me : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hc : CompClosedInvW tr) :
    CompClosedInvW ((exposeSpqr me stateIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
    Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
  have hc1 := hc.append_trEv (TREvent.ExposedSpqr (st.sessionInfo me) st.spqr st.rIdx)
  exact hc1.append_net_of_closed ((hc.spqrClosed me st stateIdx hst).mono (Trace.append_le tr _))

theorem closedW_preserves_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInvW tr) :
    CompClosedInvW ((exposeKey me stateIdx k).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc
  intro st hst
  obtain ⟨_, keys, _, hkeys, _, hdhs, _, hrk, hcks, hrecv⟩ := hinv.trStOK me st stateIdx hst
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
    · rw [hdhs_eq] at hc1 ⊢; exact hc1.append_net_rnd (t + 2) 32
    · rw [hdhs_eq] at hc1 ⊢; exact hc1.append_net_rnd t 32
  | cks =>
    dsimp only
    rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
      Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
    have hc1 := hc.append_trEv (TREvent.ExposedCKs (st.sessionInfo me) st.cks st.ns st.rIdx)
    obtain ⟨rkChain, pk, sk, n, _, hcks_eq⟩ := hcks
    have hsk : CompPcsEngine.IsScheduleKey st.cks := by
      rw [hcks_eq]; exact isScheduleKey_chainKeyAt_createChain_snd_pcs rkChain pk sk n
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
      have hsk : CompPcsEngine.IsScheduleKey c.chainKey :=
        isScheduleKey_of_recvChainInv_pcs hinv hkeys (hrecv c hc_mem)
      exact hc1.append_net_of_closed
        (.exposed (.exposedCKr hsk (CompTrace.eventLogged_here tr _)))

theorem closedW_preserves_exposeSkipped (skippedKeyEventIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInvW tr) :
    CompClosedInvW ((exposeSkipped skippedKeyEventIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  apply Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hc
  intro e he; rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    dsimp only
    obtain ⟨_, _, _, _, hseed⟩ := hinv.skipOK s pk n seed rIdx src skippedKeyEventIdx
      ((Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr he)
    apply Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_guardTrace_at _ tr hc; intro _
    rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
      Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
    have hc1 := hc.append_trEv (TREvent.ExposedMK s seed n rIdx)
    have hseed_shape : ∃ c, seed = (kdfCk c).2 := by
      rcases hseed with ⟨m, rfl⟩ | ⟨rkChain, pk', sk', m, _, rfl⟩ <;> exact ⟨_, rfl⟩
    exact hc1.append_net_of_closed
      (.exposed (.exposedMK hseed_shape (CompTrace.eventLogged_here tr _)))
  | _ => dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc

theorem closedW_preserves_compromiseIK (p : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInvW tr) :
    CompClosedInvW ((compromiseIK p stateIdx).run tr).2.val := by
  unfold compromiseIK
  refine bind_getKey_at p stateIdx .identity tr hc fun sk hst => ?_
  obtain ⟨t, rfl, _, _⟩ := hinv.stOK p { kind := .identity, sk := sk } stateIdx hst
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact (hc.append_ev _).append_net_rnd t 32

theorem closedW_preserves_compromiseSPK (b : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInvW tr) :
    CompClosedInvW ((compromiseSPK b stateIdx).run tr).2.val := by
  unfold compromiseSPK
  refine bind_getKey_at b stateIdx .signedPrekey tr hc fun sk hst => ?_
  obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .signedPrekey, sk := sk } stateIdx hst
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact (hc.append_ev _).append_net_rnd t 32

theorem closedW_preserves_compromisePQSPK (b : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInvW tr) :
    CompClosedInvW ((compromisePQSPK b stateIdx).run tr).2.val := by
  unfold compromisePQSPK
  refine bind_getKey_at b stateIdx .pqPrekey tr hc fun sk hst => ?_
  obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .pqPrekey, sk := sk } stateIdx hst
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact (hc.append_ev _).append_net_rnd t 64

theorem closedW_preserves_compromiseOPK (b : Participant) (stateIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CompClosedInvW tr) :
    CompClosedInvW ((compromiseOPK b stateIdx).run tr).2.val := by
  unfold compromiseOPK
  refine bind_getKey_at b stateIdx .oneTimePrekey tr hc fun sk hst => ?_
  refine bind_guardOnTrace_at (fun tr => !opkUsedB tr b (DiffieHellman.dhPk sk)) tr hc fun _ => ?_
  obtain ⟨t, rfl, _, _⟩ := hinv.stOK b { kind := .oneTimePrekey, sk := sk } stateIdx hst
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact (hc.append_ev _).append_net_rnd t 32

theorem closedW_preserves_breakDH (tr : ExecTrace) (hc : CompClosedInvW tr) :
    CompClosedInvW (breakDH.run tr).2.val := by
  unfold breakDH
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact hc.append_ev _

theorem closedW_preserves_breakKEM (tr : ExecTrace) (hc : CompClosedInvW tr) :
    CompClosedInvW (breakKEM.run tr).2.val := by
  unfold breakKEM
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  exact hc.append_ev _

theorem closedW_preserves_invertDH (pkIdx : Nat) (tr : ExecTrace) (hc : CompClosedInvW tr) :
    CompClosedInvW ((invertDH pkIdx).run tr).2.val := by
  unfold invertDH
  refine Preserves.bind_guardOnTrace DY.Libsignal.PQXDH.brokenDHB (fun tr hc _ => ?_) tr hc
  refine bind_receiveMessage_at pkIdx tr hc fun pk _ hpk => ?_
  have hpk_closed : CompTightClosedW tr (X25519.normalizeX25519Key pk) :=
    CompTightClosedW.normalizeX25519Key (hc.of_attackerKnows hpk)
  rcases hdh : DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
  · dsimp only; rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hc
  · dsimp only
    rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
    rw [dhSkOf_eq_some hdh] at hpk_closed
    rcases CompTightClosedW.inv_dhPk hpk_closed with ⟨t, n, rfl⟩ | hsk_closed
    · exact hc.append_net_rnd t n
    · exact hc.append_net_of_closed hsk_closed

theorem closedW_preserves_invertKEM (pkIdx : Nat) (tr : ExecTrace) (hc : CompClosedInvW tr) :
    CompClosedInvW ((invertKEM pkIdx).run tr).2.val := by
  unfold invertKEM
  refine Preserves.bind_guardOnTrace DY.Libsignal.PQXDH.brokenKEMB (fun tr hc _ => ?_) tr hc
  refine bind_receiveMessage_at pkIdx tr hc fun pk _ hpk => ?_
  have hpk_closed : CompTightClosedW tr pk := hc.of_attackerKnows hpk
  rcases hkem : PQKem.invertKemPublicKey pk with _ | sk
  · dsimp only [liftM, monadLift, MonadLift.monadLift]
    rw [Traceful.run_bind, Traceful.run_mk]
    exact hc
  · dsimp only [liftM, monadLift, MonadLift.monadLift]
    rw [Traceful.run_bind, Traceful.run_mk]; dsimp only
    rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_sendMessage_snd]
    rw [kemPkInvert_eq_some hkem] at hpk_closed
    rcases CompTightClosedW.inv_kemPk hpk_closed with ⟨t, n, rfl⟩ | hsk_closed
    · exact hc.append_net_rnd t n
    · exact hc.append_net_of_closed hsk_closed

private theorem composed_reachable_induction_w {Inv : ExecTrace → Prop}
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

theorem compClosedInvW_of_reachable {tr : ExecTrace}
    (hr : tr.Reachable DY.Libsignal.Composed.reachability) :
    CompClosedInvW tr := by
  refine composed_reachable_induction_w compClosedInvW_nil
    (fun input tr hReachPre hPre hc => ?_) tr hr
  have hinv : SpqrInv tr := spqrInv_of_reachable tr hReachPre
  rcases input with ⟨⟨i, hi⟩, inp⟩
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · exact closedW_preserves_net inp tr hPre hc
  · exact closedW_preserves_registerIdentity inp tr hc
  · rcases inp with ⟨p, skIdx⟩; exact closedW_preserves_registerCorruptIdentity p skIdx tr hc
  · rcases inp with ⟨b, idStateIdx⟩; exact closedW_preserves_genSignedPrekey b idStateIdx tr hc
  · rcases inp with ⟨b, idStateIdx⟩; exact closedW_preserves_genPQPrekey b idStateIdx tr hc
  · exact closedW_preserves_genOneTimePrekey inp tr hc
  · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩
    exact closedW_preserves_aliceStart a b idStateIdx regIdxB bh tr hc
  · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩
    exact closedW_preserves_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx tr hc
  · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩
    exact closedW_preserves_messageEncrypt me stateIdx coinsLen pqIdx tr hinv hc
  · rcases inp with ⟨me, stateIdx⟩; exact closedW_preserves_messageEncryptAbort me stateIdx tr hc
  · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩
    exact closedW_preserves_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx tr hc
  · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩
    exact closedW_preserves_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx tr hc
  · rcases inp with ⟨me, stateIdx, k⟩; exact closedW_preserves_exposeKey me stateIdx k tr hinv hc
  · rcases inp with ⟨me, stateIdx⟩; exact closedW_preserves_exposeSpqr me stateIdx tr hc
  · exact closedW_preserves_exposeSkipped inp tr hinv hc
  · rcases inp with ⟨p, stateIdx⟩; exact closedW_preserves_compromiseIK p stateIdx tr hinv hc
  · rcases inp with ⟨b, stateIdx⟩; exact closedW_preserves_compromiseSPK b stateIdx tr hinv hc
  · rcases inp with ⟨b, stateIdx⟩; exact closedW_preserves_compromisePQSPK b stateIdx tr hinv hc
  · rcases inp with ⟨b, stateIdx⟩; exact closedW_preserves_compromiseOPK b stateIdx tr hinv hc
  · exact closedW_preserves_breakDH tr hc
  · exact closedW_preserves_breakKEM tr hc
  · exact closedW_preserves_invertDH inp tr hc
  · exact closedW_preserves_invertKEM inp tr hc
  · omega

/-- On any reachable trace `tr` of the composed model, every attacker-known term `t` belongs to
`CompTrClosed (CompPcsWitnessExposure tr)`. -/
theorem attackerKnows_implies_compTrClosed_witness {tr : ExecTrace}
    (hr : tr.Reachable DY.Libsignal.Composed.reachability)
    {t : Bytes} (hk : t.AttackerKnows tr) :
    CompTrClosed (CompPcsWitnessExposure tr) t :=
  ((compClosedInvW_of_reachable hr).of_attackerKnows hk).to_compTrClosed

end ClosedInvW

/-! ## Handshake Excuse Bridge over `CompPcsWitnessExposure` -/

section HandshakeWitnessBridge
unseal Bytes

open Symbolic.Swarm.COMPOSED.CompInv
open DY.Libsignal.PQXDH (aliceAgreement OPKAbsentOrCompromised)

theorem pub_of_msgEncWitnessAt {tr : ExecTrace} (hinv : SpqrInv tr) {r : Bytes}
    (hw : MsgEncWitnessAt tr r) : Pub tr r := by
  rcases hw with ⟨me, st, idx, s, hst, hspqr⟩ | ⟨v, rk, c, pc, k, iv, pq, ev, mac, hbase⟩
  · obtain ⟨_, keys, _, _, _, _, hspqr_from, _, _, _⟩ := hinv.trStOK me st idx hst
    rw [hspqr] at hspqr_from
    generalize hq : (Spqr.spqrSend s r).1 = q at hspqr_from
    cases hspqr_from with
    | send _ hc =>
      have hv := congrArg (fun b : Bytes => b.view? Spqr.SendState.SubF) hq
      simp only [Spqr.spqrSend, BytesView.view_pack, Option.some.injEq,
        Spqr.SendState.SubF.mk.injEq] at hv
      exact hv.2 ▸ hc
    | _ =>
      dsimp [Spqr.spqrSend, Spqr.spqrInit] at hq
      exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  · have hcat := hinv.netPub _ hbase
    have hwire := (CompPubInv.Pub.inv_cat hinv hcat).1
    have hct := (CompPubInv.Pub.inv_trWire hinv hwire).2.1
    exact CompPubInv.Pub.inv_enc hinv hct

theorem compPcsWitnessExposure_mkRand_iff (tr : ExecTrace) (ts sz : Nat) :
    CompPcsWitnessExposure tr (mkRand ts sz) ↔
      ((mkRand ts sz).AttackerKnows tr ∨ MsgEncWitnessAt tr (mkRand ts sz)) := by
  refine ⟨fun h => ?_, CompPcsWitnessExposure.rand⟩
  generalize hq : mkRand ts sz = q at h
  cases h with
  | rand hr => obtain ⟨rfl, rfl⟩ := mkRand_inj hq; exact hr
  | pqr => have hd := congrArg saltDepth hq; simp [pqxdhKdf, DY.Libsignal.TripleRatchet.hkdfBlock3] at hd
  | exposedRK hrk _ => obtain ⟨_, _, _, rfl⟩ := hrk; have hd := congrArg saltDepth hq; simp at hd
  | exposedCKs hsk _ | exposedCKr hsk _ =>
    rcases hsk with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      (have hd := congrArg saltDepth hq; simp at hd)
  | exposedMK hm _ => obtain ⟨_, rfl⟩ := hm; have hd := congrArg saltDepth hq; simp at hd

end HandshakeWitnessBridge

section HandshakeExcuseProof

unseal Bytes

open Symbolic.Swarm.COMPOSED.CompInv
open DY.Libsignal.PQXDH (aliceAgreement OPKAbsentOrCompromised)

private theorem not_compPcsWitnessExposure_dh_pack (tr : ExecTrace) (sk pk : Bytes) :
    ¬ CompPcsWitnessExposure tr (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack) := by
  intro hexp
  rcases hexp.exists_mkRand_or_kdfExtract with ⟨_, _, hq⟩ | ⟨_, _, hq⟩
  · dsimp [mkRand] at hq
    exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq
  · dsimp [kdfExtract] at hq
    exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq

private theorem CompTrClosed.inv_agree_dhPk_witness {tr : ExecTrace} {a b : Bytes}
    (h : CompTrClosed (CompPcsWitnessExposure tr) (agree (DiffieHellman.dhPk a) b)) :
    CompTrClosed (CompPcsWitnessExposure tr) a ∨ CompTrClosed (CompPcsWitnessExposure tr) b := by
  have hnorm : X25519.normalizeX25519Key (DiffieHellman.dhPk a) = DiffieHellman.dhPk a := by
    unfold X25519.normalizeX25519Key
    dsimp only [DiffieHellman.dhPk]
    rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Variant.SubF]
  unfold DY.Libsignal.PQXDH.agree at h
  rw [hnorm] at h
  exact CompTrClosed.inv_dh_dhPk_of_nonDh (not_compPcsWitnessExposure_dh_pack tr) h

private theorem CompTrClosed.inv_ss_witness {tr : ExecTrace} {pk e : Bytes}
    (h : CompTrClosed (CompPcsWitnessExposure tr) (PQKem.kemEncap pk e).2) :
    (CompTrClosed (CompPcsWitnessExposure tr) pk ∧ CompTrClosed (CompPcsWitnessExposure tr) e) ∨
    (∃ sk, pk = PQKem.kemPk sk ∧ CompTrClosed (CompPcsWitnessExposure tr) sk) := by
  generalize hq : (PQKem.kemEncap pk e).2 = q at h
  cases h with
  | exposed hexp =>
    rcases hexp.exists_mkRand_or_kdfExtract with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
    · dsimp [PQKem.kemEncap, mkRand] at hq
      exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
    · dsimp [PQKem.kemEncap, kdfExtract] at hq
      exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | kemSs _ _ hpk he => obtain ⟨rfl, rfl⟩ := kemEncap_snd_inj hq; exact .inl ⟨hpk, he⟩
  | kemSsKey _ _ hsk => obtain ⟨rfl, rfl⟩ := kemEncap_snd_inj hq; exact .inr ⟨_, rfl, hsk⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

private theorem not_compPcsWitnessExposure_hmac_zeroSalt_concat (tr : ExecTrace) (a b : Bytes) :
    ¬ CompPcsWitnessExposure tr (hmac zeroSalt (Concat.concat a b)) := by
  intro hexp
  generalize hq : hmac zeroSalt (Concat.concat a b) = q at hexp
  cases hexp with
  | rand _ => have hd := congrArg saltDepth hq; simp at hd
  | pqr => have hd := congrArg saltDepth hq; simp [pqxdhKdf, DY.Libsignal.TripleRatchet.hkdfBlock3] at hd
  | exposedRK hrk _ =>
    obtain ⟨_, _, _, rfl⟩ := hrk
    have hd := congrArg saltDepth hq; simp at hd
  | exposedCKs hsk _ | exposedCKr hsk _ =>
    rcases hsk with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · have hd := congrArg saltDepth hq; simp at hd
    · have hd := congrArg saltDepth hq; simp at hd
    · have hd := congrArg saltDepth hq; simp at hd
    · exact litByte_ne_concat _ a b (hmac_inj hq).2.symm
    · exact litByte_ne_concat _ a b (hmac_inj hq).2.symm
  | exposedMK hm _ =>
    obtain ⟨_, rfl⟩ := hm
    exact litByte_ne_concat _ a b (hmac_inj hq).2.symm

private theorem pub_of_compTrClosed_witness_mkRand {tr : ExecTrace} (hinv : SpqrInv tr) {t sz : Nat}
    (h : CompTrClosed (CompPcsWitnessExposure tr) (mkRand t sz)) :
    Pub tr (mkRand t sz) := by
  rcases (compPcsWitnessExposure_mkRand_iff tr t sz).mp (CompTrClosed.inv_rnd h) with hk | hw
  · exact pub_of_knows hinv hk
  · exact pub_of_msgEncWitnessAt hinv hw

private theorem pub_of_compTrClosed_witness_ikAt {tr : ExecTrace} (hinv : SpqrInv tr)
    {p : Participant} {r : Bytes} (hik : IKAt tr p r)
    (h : CompTrClosed (CompPcsWitnessExposure tr) r) : Pub tr r := by
  obtain ⟨_, rfl, _, _⟩ := hik; exact pub_of_compTrClosed_witness_mkRand hinv h

private theorem pub_of_compTrClosed_witness_spkAt {tr : ExecTrace} (hinv : SpqrInv tr)
    {b : Participant} {r : Bytes} (hspk : SPKAt tr b r)
    (h : CompTrClosed (CompPcsWitnessExposure tr) r) : Pub tr r := by
  obtain ⟨_, rfl, _, _, _⟩ := hspk; exact pub_of_compTrClosed_witness_mkRand hinv h

private theorem pub_of_compTrClosed_witness_pqAt {tr : ExecTrace} (hinv : SpqrInv tr)
    {b : Participant} {r : Bytes} (hpq : PQAt tr b r)
    (h : CompTrClosed (CompPcsWitnessExposure tr) r) : Pub tr r := by
  obtain ⟨_, rfl, _, _, _⟩ := hpq; exact pub_of_compTrClosed_witness_mkRand hinv h

private theorem pub_of_compTrClosed_witness_opkAt {tr : ExecTrace} (hinv : SpqrInv tr)
    {b : Participant} {r : Bytes} (hopk : OPKAt tr b r)
    (h : CompTrClosed (CompPcsWitnessExposure tr) r) : Pub tr r := by
  obtain ⟨_, rfl, _, _⟩ := hopk; exact pub_of_compTrClosed_witness_mkRand hinv h

/-- If `SpqrInv tr` holds and `CompTrClosed (CompPcsWitnessExposure tr) (hmac zeroSalt ikm)` holds
for a handshake at `doneIdx` (`HandshakeKeysAt tr doneIdx (pqxdhKdf ikm)`), then
`HandshakeWasCompromisedAt tr doneIdx` holds. -/
theorem handshakeExcusedAt_of_compTrClosed_witness_hmac_zeroSalt {tr : ExecTrace}
    (hinv : SpqrInv tr) {doneIdx : Nat} {ikm : Bytes}
    (hhk : HandshakeKeysAt tr doneIdx (pqxdhKdf ikm))
    (hclosed : CompTrClosed (CompPcsWitnessExposure tr) (hmac zeroSalt ikm)) :
    HandshakeWasCompromisedAt tr doneIdx := by
  have hE := isAtomic_compPcsWitnessExposure tr
  rcases hhk with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hA⟩ | ⟨ek, ct, hB⟩⟩
  · refine .inl ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, pqxdhKdf ikm, hA, ?_⟩
    obtain ⟨t, sA, rfl, hslot, _hA_ik, _hikA, _hek, hagr, hbundle⟩ :=
      hinv.aliceDone a b ikA ikB spk pqpk opk ek ct (pqxdhKdf ikm) doneIdx hA
    rcases hbundle with ⟨sB, sS, sQ, hB, rfl, hS, rfl, hQ, rfl⟩ | ⟨j, hj, hlt⟩ | ⟨j, hj, hlt⟩
    rotate_left
    · exact .inl ⟨j, hj, .inl hlt⟩
    · exact .inr ⟨j, hj, .inl hlt⟩
    have hikm : ikm = pqxdhIkm (agree (DiffieHellman.dhPk sS) sA)
        (agree (DiffieHellman.dhPk sB) (rnd t 32))
        (agree (DiffieHellman.dhPk sS) (rnd t 32))
        (opk.map (agree · (rnd t 32)))
        (PQKem.kemEncap (PQKem.kemPk sQ) (rnd (t + 1) 32)).2 := by
      rcases hKem : PQKem.kemEncap (PQKem.kemPk sQ) (rnd (t + 1) 32) with ⟨c, s⟩
      simp only [aliceAgreement, hKem, Prod.mk.injEq] at hagr
      exact pqxdhKdf_rk_inj (congrArg HandshakeKeys.rk hagr.2)
    rw [hikm] at hclosed
    rcases CompTrClosed.inv_kdfExtract_ikm hclosed with hexp | hikm_closed
    · exact False.elim (not_compPcsWitnessExposure_hmac_zeroSalt_concat tr _ _ hexp)
    obtain ⟨_, hd2, hd3, _, hss⟩ :=
      pqxdhIkm_inv_generic (CompTrClosed.inv_concat hE) hikm_closed
    have hPQ : tr.EventLogged (PQXDHEvent.CompromisedPQSPK b (PQKem.kemPk sQ)) ∨
        tr.EventLogged PQXDHEvent.BrokenKEM := by
      rcases CompTrClosed.inv_ss_witness hss with ⟨_, hc⟩ | ⟨sk, hsk, hpk⟩
      · exact absurd (pub_of_compTrClosed_witness_mkRand hinv hc) (not_pub_coins hinv hslot)
      · obtain rfl := kemPk_inj hsk
        exact pub_PQ hinv hQ (pub_of_compTrClosed_witness_pqAt hinv hQ hpk)
    rcases CompTrClosed.inv_agree_dhPk_witness hd2 with h2 | h2
    · rcases pub_IK hinv hB (pub_of_compTrClosed_witness_ikAt hinv hB h2) with ⟨j, hj⟩ | ⟨j, hj⟩
      · rcases CompTrClosed.inv_agree_dhPk_witness hd3 with h3 | h3
        · rcases pub_SPK hinv hS (pub_of_compTrClosed_witness_spkAt hinv hS h3) with hcs | ⟨j', hj'⟩
          · exact .inl ⟨j, hj, .inr ⟨hcs, hPQ⟩⟩
          · exact .inr ⟨j', hj', .inr hPQ⟩
        · obtain ⟨j', hj'⟩ := pub_EK hinv hslot (pub_of_compTrClosed_witness_mkRand hinv h3)
          exact .inr ⟨j', hj', .inr hPQ⟩
      · exact .inr ⟨j, hj, .inr hPQ⟩
    · obtain ⟨j, hj⟩ := pub_EK hinv hslot (pub_of_compTrClosed_witness_mkRand hinv h2)
      exact .inr ⟨j, hj, .inr hPQ⟩
  · refine .inr ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, pqxdhKdf ikm, hB, ?_⟩
    obtain ⟨sB, sS, sQ, o, ss, hsB, hikB, hsS, hspk, hsQ, hpqpk, ho, hopk,
      _hcan, hdec, hkeys, _hreg, hauth⟩ :=
      hinv.bobDone b a ikB ikA spk pqpk opk ek ct (pqxdhKdf ikm) doneIdx hB
    rcases hauth with ⟨j, a', b', spk', opk', _, hAlice⟩ | hCIK | hCSPK | hBDH
    · obtain ⟨t, sA, _, hSlot, _, _, hek_eq, hAliceAgree, _⟩ :=
        hinv.aliceDone a' b' ikA ikB spk' pqpk opk' ek ct (pqxdhKdf ikm) j hAlice
      have hct : ct = (PQKem.kemEncap (PQKem.kemPk sQ) (rnd (t + 1) 32)).1 := by
        simpa [aliceAgreement, hpqpk] using congrArg Prod.fst hAliceAgree
      have hss_eq : ss = (PQKem.kemEncap (PQKem.kemPk sQ) (rnd (t + 1) 32)).2 := by
        have hkd : DY.Libsignal.PQXDH.errToOption
            (PQKem.kemDecap sQ (PQKem.kemEncap (PQKem.kemPk sQ) (rnd (t + 1) 32)).1) =
            some (PQKem.kemEncap (PQKem.kemPk sQ) (rnd (t + 1) 32)).2 :=
          kemDecap_kemEncap sQ (rnd (t + 1) 32)
        rw [hdec, hct, hkd]; rfl
      have hikm : ikm = pqxdhIkm (agree ikA sS) (agree ek sB) (agree ek sS) (o.map (agree ek ·)) ss :=
        pqxdhKdf_rk_inj (congrArg HandshakeKeys.rk hkeys)
      rw [hikm] at hclosed
      rcases CompTrClosed.inv_kdfExtract_ikm hclosed with hexp | hikm_closed
      · exact False.elim (not_compPcsWitnessExposure_hmac_zeroSalt_concat tr _ _ hexp)
      obtain ⟨_, hdh2, hdh3, hdh4, hssPub⟩ :=
        pqxdhIkm_inv_generic (CompTrClosed.inv_concat hE) hikm_closed
      rw [hss_eq] at hssPub
      have hpqPub : CompTrClosed (CompPcsWitnessExposure tr) sQ := by
        rcases CompTrClosed.inv_ss_witness hssPub with ⟨_, hcoins⟩ | ⟨sk, heq, hsk⟩
        · exact False.elim (not_pub_coins hinv hSlot (pub_of_compTrClosed_witness_mkRand hinv hcoins))
        · exact kemPk_inj heq ▸ hsk
      have hpqLeak : tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨
          tr.EventLogged PQXDHEvent.BrokenKEM :=
        hpqpk ▸ pub_PQ hinv hsQ (pub_of_compTrClosed_witness_pqAt hinv hsQ hpqPub)
      by_cases hBDH : tr.EventLogged PQXDHEvent.BrokenDH
      · exact .inr (.inr ⟨hBDH, hpqLeak⟩)
      · have hnotEk : ¬ CompTrClosed (CompPcsWitnessExposure tr) (rnd t 32) := fun hekPub =>
          let ⟨j', hj'⟩ := pub_EK hinv hSlot (pub_of_compTrClosed_witness_mkRand hinv hekPub)
          hBDH ⟨j', hj'⟩
        rw [hek_eq] at hdh2 hdh3 hdh4
        have hsBPub := (CompTrClosed.inv_agree_dhPk_witness hdh2).resolve_left hnotEk
        have hsSPub := (CompTrClosed.inv_agree_dhPk_witness hdh3).resolve_left hnotEk
        have hikBComp : tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) := by
          rw [hikB]
          rcases pub_IK hinv hsB (pub_of_compTrClosed_witness_ikAt hinv hsB hsBPub) with ⟨j', hj'⟩ | ⟨j', hj'⟩
          · exact ⟨j', hj'⟩
          · exact False.elim (hBDH ⟨j', hj'⟩)
        have hspkComp : tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) := by
          rw [hspk]
          rcases pub_SPK hinv hsS (pub_of_compTrClosed_witness_spkAt hinv hsS hsSPub) with hcs | ⟨j', hj'⟩
          · exact hcs
          · exact False.elim (hBDH ⟨j', hj'⟩)
        have hopkExc : OPKAbsentOrCompromised b opk doneIdx tr := by
          cases o with
          | none =>
            subst hopk
            exact .inl rfl
          | some sO =>
            subst hopk
            have hd4 := hdh4 (agree (DiffieHellman.dhPk (rnd t 32)) sO) rfl
            have hsOPub := (CompTrClosed.inv_agree_dhPk_witness hd4).resolve_left hnotEk
            exact .inr ⟨DiffieHellman.dhPk sO, rfl,
              hinv.compOpk_loggedBefore hB
                ((pub_OPK hinv (ho sO rfl) (pub_of_compTrClosed_witness_opkAt hinv (ho sO rfl) hsOPub)).resolve_right hBDH)⟩
        exact .inr (.inl ⟨hikBComp, hspkComp, hopkExc, hpqLeak⟩)
    · exact .inl (.inl hCIK)
    · exact .inl (.inr (.inl hCSPK))
    · exact .inl (.inr (.inr hBDH))

end HandshakeExcuseProof

/-! ## Schedule Bridges and Post-Compromise Security -/

theorem CompRkSteps.to_engine {dh₁ rk₀ rk : Bytes} {d : Nat}
    (h : CompRkSteps dh₁ d rk₀ rk) : CompPcsEngine.CompRkSteps dh₁ d rk₀ rk := by
  induction h with
  | zero rk₀ => exact .zero rk₀
  | step_one rk₀ => exact .step_one rk₀
  | step_succ _ ih => exact .step_succ ih

theorem CompChainRootFrom1.to_engine {dh₁ ikm ck₀ : Bytes} {m : Nat}
    (h : CompChainRootFrom1 dh₁ ikm m ck₀) :
    CompPcsEngine.CompChainRootFrom1 dh₁ ikm m ck₀ := by
  rcases m with _ | _ | k
  · exact h
  · exact h
  · obtain ⟨rk, pk, sk, hrk, hck⟩ := h
    exact ⟨rk, pk, sk, hrk.to_engine, hck⟩

theorem compEventScheduleOKFor_of_scheduleOK {tr : ExecTrace} {ev : TREvent}
    (h : CompEventScheduleOK tr ev) :
    CompPcsEngine.CompEventScheduleOKFor (CompSessionAt tr) tr ev := by
  cases ev with
  | MessageKey s dir seed pqSalt n rIdx par =>
    cases dir <;> {
      obtain ⟨hpos, _, doneIdx, ikm, dh₁, ck₀, hs, hroot, hseed⟩ := h
      exact ⟨hpos, doneIdx, ikm, dh₁, ck₀, hs, hroot.to_engine, hseed⟩ }
  | ExposedRK s rk rIdx =>
    obtain ⟨hpos, _, hshape, doneIdx, ikm, dh₁, hs, hrk⟩ := h
    exact ⟨hpos, hshape, doneIdx, ikm, dh₁, hs, hrk.to_engine⟩
  | ExposedCKs s ck ns rIdx =>
    obtain ⟨hpos, _, doneIdx, ikm, dh₁, ck₀, hs, hroot, hck⟩ := h
    exact ⟨hpos, doneIdx, ikm, dh₁, ck₀, hs, hroot.to_engine, hck⟩
  | ExposedCKr s ck nr rIdx =>
    obtain ⟨hpos, _, doneIdx, ikm, dh₁, ck₀, hs, hroot, hck⟩ := h
    exact ⟨hpos, doneIdx, ikm, dh₁, ck₀, hs, hroot.to_engine, hck⟩
  | ExposedMK s seed n rIdx =>
    obtain ⟨hpos, _, doneIdx, ikm, dh₁, ck₀, hs, hroot, hseed⟩ := h
    exact ⟨hpos, doneIdx, ikm, dh₁, ck₀, hs, hroot.to_engine, hseed⟩
  | _ => trivial

theorem compPcsWitnessExposure_iff_structuredFor (tr : ExecTrace) (b : Bytes) :
    CompPcsWitnessExposure tr b ↔
      CompPcsEngine.CompStructuredExposureFor (MsgEncWitnessAt tr) tr b := by
  constructor
  · intro h; cases h with
    | rand hr => exact .rand hr
    | pqr => exact .pqr
    | exposedRK hrk hev => exact .exposedRK hrk hev
    | exposedCKs hsk hev => exact .exposedCKs hsk hev
    | exposedCKr hsk hev => exact .exposedCKr hsk hev
    | exposedMK hm hev => exact .exposedMK hm hev
  · intro h; cases h with
    | rand hr => exact .rand hr
    | pqr => exact .pqr
    | exposedRK hrk hev => exact .exposedRK hrk hev
    | exposedCKs hsk hev => exact .exposedCKs hsk hev
    | exposedCKr hsk hev => exact .exposedCKr hsk hev
    | exposedMK hm hev => exact .exposedMK hm hev

/-- Every PQXDH handshake on a `SpqrInv` trace `tr` producing `(pqxdhKdf ikm).rk` is excused when
`hmac zeroSalt ikm` lies in `CompTrClosed (CompPcsWitnessExposure tr)`. -/
theorem handshakeRootCompromised_of_compTrClosed_witness_hmac_zeroSalt {tr : ExecTrace}
    (hInv : Symbolic.Swarm.COMPOSED.CompInv.SpqrInv tr) {doneIdx : Nat} {ikm : Bytes}
    (hhk : HandshakeKeysAt tr doneIdx (pqxdhKdf ikm))
    (hcl : CompTrClosed (CompPcsWitnessExposure tr) (hmac zeroSalt ikm)) :
    DY.Libsignal.TripleRatchet.Cheval.HandshakeRootCompromised tr (pqxdhKdf ikm).rk := by
  refine ⟨⟨pqxdhKdf ikm, doneIdx, hhk, .inl rfl⟩, fun keys' j' hhk' hEq => ?_⟩
  obtain ⟨ikm', rfl⟩ := Symbolic.Swarm.COMPOSED.CompInv.CompPubInv.handshakeKeysAt_eq_pqxdhKdf hInv hhk'
  rcases hEq with hrk | hck
  · obtain rfl := pqxdhKdf_rk_inj hrk
    exact handshakeExcusedAt_of_compTrClosed_witness_hmac_zeroSalt hInv hhk' hcl
  · exact False.elim (hkdfBlock1_ne_hkdfBlock2 _ _ _ _ hck)

theorem reachableCompPCSBundle_of_reachable {tr : ExecTrace}
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability) :
    CompPcsEngine.ReachableCompPCSBundle tr := by
  have hSched := compScheduleInv_reachable hreach
  have hInv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable tr hreach
  have hdhs := honestDH_rand_of_reachable hreach
  have hexpDH := exposedDHs_rand_of_reachable hreach
  refine ⟨CompSessionAt tr,
    MsgEncWitnessAt tr,
    MsgEncWitnessAt tr,
    CompTrClosed (CompPcsEngine.CompStructuredExposureFor (MsgEncWitnessAt tr) tr),
    CompTrClosed (CompPcsEngine.CompPcsWitnessExposureFor (MsgEncWitnessAt tr) tr),
    fun hs => ⟨hs.2.1, hs.exists_dh⟩,
    fun ev hev => compEventScheduleOKFor_of_scheduleOK (hSched.eventOK ev hev),
    hdhs,
    hexpDH,
    pcsKdfClosureInv_compTrClosed _,
    fun t hk => CompTrClosed.mono
      (fun b hb => (compPcsWitnessExposure_iff_structuredFor tr b).mp hb)
      (attackerKnows_implies_compTrClosed_witness hreach hk),
    fun hhk hcl => handshakeRootCompromised_of_compTrClosed_witness_hmac_zeroSalt hInv hhk
      (CompTrClosed.mono
        (fun b hb => (compPcsWitnessExposure_iff_structuredFor tr b).mpr hb) hcl),
    pcsWitnessClosureInv_compTrClosed (not_witnessExposureFor_dh_pack hdhs hexpDH),
    fun t hk => CompTrClosed.mono
      (fun _ hb => hb.to_engineExposure hreach)
      (attackerKnows_implies_compTrClosed_witness hreach hk)⟩

/-- `PCSQuery tr` holds on every reachable trace `tr` of `DY.Libsignal.Composed`. -/
theorem post_compromise_security :
    DY.Libsignal.Composed.Security.PostCompromiseSecurity :=
  CompPcsEngine.post_compromise_security_of_compInvariants
    fun _ hreach => reachableCompPCSBundle_of_reachable hreach

end Symbolic.Swarm.COMPOSED.CompRatchet
