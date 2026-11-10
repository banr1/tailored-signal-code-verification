/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
import DY.Bytes.Basic
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
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.DYBridge.DY.Bytes.Basic
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
# Composed Triple Ratchet Invariant Preservation

Proves preservation of `SpqrInv` across the Triple Ratchet state-exposure (`exposeKey`,
`exposeSpqr`, `exposeSkipped`) and messaging (`messageEncrypt`, `messageEncryptAbort`,
`messageDecrypt`, `messageDecryptSkipped`) transitions of `DY.Libsignal.Composed`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompPresTRExp

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed
open Symbolic.Swarm.COMPOSED.CompTermAlgebra
open Symbolic.Swarm.COMPOSED.CompKeyInversion
open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED.CompInv.CompPubInv

/-! ## Single-Step Append Preservation and Monad Helpers -/

theorem append_net {tr : ExecTrace} (hinv : SpqrInv tr) {msg : Bytes}
    (hpub : Pub (tr.append (NetE msg)) msg) :
    SpqrInv (tr.append (NetE msg)) := by
  have hle : tr ≤ tr.append (NetE msg) := Trace.append_le tr (NetE msg)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hinv.opkOrder.append_other rfl⟩
  · intro x hx
    rcases (CompTrace.baseAttackerKnows_append_net tr msg x).mp hx with rfl | hx'
    · exact hpub
    · exact Pub.mono hle (hinv.netPub x hx')
  · intro me st idx hst
    exact KindOK.mono hle (hinv.stOK me st idx (CompTrace.pqxdhStoredAt_append_other rfl hst))
  · intro me st idx hst
    exact TRStateOK.mono hle (hinv.trStOK me st idx (CompTrace.trStateStoredAt_append_other rfl hst))
  · intro s rPk ctr seed rIdx src idx hsk
    exact SkippedKeyOK.mono hle
      (hinv.skipOK s rPk ctr seed rIdx src idx (CompTrace.eventLoggedAt_append_other rfl hsk))
  · intro p ik vkp r hir
    obtain ⟨s, hs, h1, h2⟩ :=
      hinv.irHonest p ik vkp r (CompTrace.eventLoggedAt_append_other rfl hir)
    exact ⟨s, hs.mono hle, h1, h2⟩
  · intro p ik vkp r hir
    exact evAt_mono hle (hinv.irCorrupt p ik vkp r (CompTrace.eventLoggedAt_append_other rfl hir))
  · intro a b ikA ikB spk pqpk opk ek ct keys i had
    exact AliceDoneFacts.mono hle (hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys i
      (CompTrace.eventLoggedAt_append_other rfl had))
  · intro b a ikB ikA spk pqpk opk ek ct keys i hbd
    exact BobDoneFacts.mono hle (hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys i
      (CompTrace.eventLoggedAt_append_other rfl hbd))

theorem append_net_of_pub {tr : ExecTrace} (hinv : SpqrInv tr) {msg : Bytes}
    (hpub : Pub tr msg) :
    SpqrInv (tr.append (NetE msg)) :=
  append_net hinv (Pub.mono (Trace.append_le tr (NetE msg)) hpub)

theorem append_rnd {tr : ExecTrace} (n : Nat) (hinv : SpqrInv tr) :
    SpqrInv (tr.append (RndE n)) := by
  have hle : tr ≤ tr.append (RndE n) := Trace.append_le tr (RndE n)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hinv.opkOrder.append_other rfl⟩
  · intro x hx
    exact Pub.mono hle (hinv.netPub x ((CompTrace.baseAttackerKnows_append_rnd tr n x).mp hx))
  · intro me st idx hst
    exact KindOK.mono hle (hinv.stOK me st idx (CompTrace.pqxdhStoredAt_append_other rfl hst))
  · intro me st idx hst
    exact TRStateOK.mono hle (hinv.trStOK me st idx (CompTrace.trStateStoredAt_append_other rfl hst))
  · intro s rPk ctr seed rIdx src idx hsk
    exact SkippedKeyOK.mono hle
      (hinv.skipOK s rPk ctr seed rIdx src idx (CompTrace.eventLoggedAt_append_other rfl hsk))
  · intro p ik vkp r hir
    obtain ⟨s, hs, h1, h2⟩ :=
      hinv.irHonest p ik vkp r (CompTrace.eventLoggedAt_append_other rfl hir)
    exact ⟨s, hs.mono hle, h1, h2⟩
  · intro p ik vkp r hir
    exact evAt_mono hle (hinv.irCorrupt p ik vkp r (CompTrace.eventLoggedAt_append_other rfl hir))
  · intro a b ikA ikB spk pqpk opk ek ct keys i had
    exact AliceDoneFacts.mono hle (hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys i
      (CompTrace.eventLoggedAt_append_other rfl had))
  · intro b a ikB ikA spk pqpk opk ek ct keys i hbd
    exact BobDoneFacts.mono hle (hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys i
      (CompTrace.eventLoggedAt_append_other rfl hbd))

theorem append_trEv {tr : ExecTrace} {ev : TREvent} (hinv : SpqrInv tr)
    (hskip : ∀ s rPk ctr seed rIdx src,
      ev = TREvent.SkippedKeyStored s rPk ctr seed rIdx src → SkippedKeyOK tr seed) :
    SpqrInv (tr.append (TREvE ev)) := by
  have hle : tr ≤ tr.append (TREvE ev) := Trace.append_le tr (TREvE ev)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hinv.opkOrder.append_other rfl⟩
  · intro x hx
    exact Pub.mono hle (hinv.netPub x ((CompTrace.baseAttackerKnows_append_trEv tr ev x).mp hx))
  · intro me st idx hst
    exact KindOK.mono hle (hinv.stOK me st idx (CompTrace.pqxdhStoredAt_append_other rfl hst))
  · intro me st idx hst
    exact TRStateOK.mono hle (hinv.trStOK me st idx (CompTrace.trStateStoredAt_append_other rfl hst))
  · intro s rPk ctr seed rIdx src idx hsk
    rcases CompTrace.eventLoggedAt_append_same hsk with ⟨_, hsk'⟩ | ⟨_, heq⟩
    · exact SkippedKeyOK.mono hle (hinv.skipOK s rPk ctr seed rIdx src idx hsk')
    · exact SkippedKeyOK.mono hle (hskip s rPk ctr seed rIdx src heq)
  · intro p ik vkp r hir
    obtain ⟨s, hs, h1, h2⟩ :=
      hinv.irHonest p ik vkp r (CompTrace.eventLoggedAt_append_other rfl hir)
    exact ⟨s, hs.mono hle, h1, h2⟩
  · intro p ik vkp r hir
    exact evAt_mono hle (hinv.irCorrupt p ik vkp r (CompTrace.eventLoggedAt_append_other rfl hir))
  · intro a b ikA ikB spk pqpk opk ek ct keys i had
    exact AliceDoneFacts.mono hle (hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys i
      (CompTrace.eventLoggedAt_append_other rfl had))
  · intro b a ikB ikA spk pqpk opk ek ct keys i hbd
    exact BobDoneFacts.mono hle (hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys i
      (CompTrace.eventLoggedAt_append_other rfl hbd))

theorem append_trEv_nonSkip {tr : ExecTrace} {ev : TREvent} (hinv : SpqrInv tr)
    (hnoSkip : ∀ s rPk ctr seed rIdx src, ev ≠ TREvent.SkippedKeyStored s rPk ctr seed rIdx src) :
    SpqrInv (tr.append (TREvE ev)) :=
  append_trEv hinv (fun s rPk ctr seed rIdx src heq => (hnoSkip s rPk ctr seed rIdx src heq).elim)

theorem append_trSt {tr : ExecTrace} {me : Participant} {st : TRState}
    (hinv : SpqrInv tr) (hok : TRStateOK tr me st) :
    SpqrInv (tr.append (TRStE me st)) := by
  have hle : tr ≤ tr.append (TRStE me st) := Trace.append_le tr (TRStE me st)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hinv.opkOrder.append_other rfl⟩
  · intro x hx
    exact Pub.mono hle (hinv.netPub x ((CompTrace.baseAttackerKnows_append_trSt tr me st x).mp hx))
  · intro me' st' idx hst
    exact KindOK.mono hle (hinv.stOK me' st' idx (CompTrace.pqxdhStoredAt_append_other rfl hst))
  · intro me' st' idx hst
    rcases CompTrace.trStateStoredAt_append_same hst with ⟨_, hst'⟩ | ⟨_, rfl, rfl⟩
    · exact TRStateOK.mono hle (hinv.trStOK me' st' idx hst')
    · exact TRStateOK.mono hle hok
  · intro s rPk ctr seed rIdx src idx hsk
    exact SkippedKeyOK.mono hle
      (hinv.skipOK s rPk ctr seed rIdx src idx (CompTrace.eventLoggedAt_append_other rfl hsk))
  · intro p ik vkp r hir
    obtain ⟨s, hs, h1, h2⟩ :=
      hinv.irHonest p ik vkp r (CompTrace.eventLoggedAt_append_other rfl hir)
    exact ⟨s, hs.mono hle, h1, h2⟩
  · intro p ik vkp r hir
    exact evAt_mono hle (hinv.irCorrupt p ik vkp r (CompTrace.eventLoggedAt_append_other rfl hir))
  · intro a b ikA ikB spk pqpk opk ek ct keys i had
    exact AliceDoneFacts.mono hle (hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys i
      (CompTrace.eventLoggedAt_append_other rfl had))
  · intro b a ikB ikA spk pqpk opk ek ct keys i hbd
    exact BobDoneFacts.mono hle (hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys i
      (CompTrace.eventLoggedAt_append_other rfl hbd))

theorem spqrSendKey_of {tr : ExecTrace} (st coins : Bytes) :
    Pub tr (Spqr.spqrSend st coins).2.1 := by
  unfold Spqr.spqrSend
  dsimp only
  cases st.view? Spqr.InitState.SubF with
  | none => exact .spqrSendKey st coins
  | some x => exact .spqrChainKey x.authKey x.params (Spqr.encodeSpqrIndexTerm 1)

theorem spqrSendMsg_of {tr : ExecTrace} (st coins : Bytes) :
    Pub tr (Spqr.spqrSend st coins).2.2 :=
  .spqrSendMsg st coins

theorem spqrRecvKey_of {tr : ExecTrace}
    {st msg : Bytes} {idx : UInt32} {r : Bytes × Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r) :
    Pub tr r.2 := by
  unfold Spqr.spqrRecv at hrecv
  split at hrecv
  · cases hrecv
  · cases hv : st.view? Spqr.InitState.SubF with
    | none =>
      rw [hv] at hrecv
      injection hrecv with hrecv'
      subst hrecv'
      exact .spqrRecvKey st msg
    | some x =>
      rw [hv] at hrecv
      rcases x with ⟨authKey, params⟩
      dsimp only at hrecv
      cases hd : Spqr.spqrParamsDir? params with
      | none =>
        rw [hd] at hrecv
        cases hrecv
      | some dir =>
        rw [hd] at hrecv
        injection hrecv with hrecv'
        subst hrecv'
        dsimp only
        split
        · exact .literal _
        · exact .spqrChainKey authKey _ (Spqr.encodeSpqrIndexTerm idx)

theorem pub_pqRatchet_of_parseTrSignalMsg {tr : ExecTrace} (hinv : SpqrInv tr)
    {raw : Bytes} {msg : TRSignalMsg} (hraw : Pub tr raw)
    (hparse : parseTrSignalMsg raw = some msg) :
    Pub tr msg.pqRatchet := by
  unfold DY.Libsignal.TripleRatchet.parseTrSignalMsg at hparse
  dsimp only [bind, Option.bind] at hparse
  rcases hsplit : Concat.split raw (raw.length - Trunc.trunc8Length) with _ | ⟨wire, mac⟩
  · rw [hsplit] at hparse; cases hparse
  · rw [hsplit] at hparse
    dsimp only at hparse
    have hraw_eq : raw = Concat.concat wire mac :=
      (Concat.concat_split raw (raw.length - Trunc.trunc8Length) wire mac hsplit).symm
    have hwire_pub : Pub tr wire := (Pub.inv_cat hinv (hraw_eq ▸ hraw)).1
    rcases hfields : TrWire.trWireMsgFields? wire with _ | x
    · rw [hfields] at hparse; cases hparse
    · rw [hfields] at hparse
      dsimp only [pure] at hparse
      injection hparse with hmsg_eq
      have hpq_eq : msg.pqRatchet = x.pqRatchet := by rw [← hmsg_eq]
      rw [hpq_eq]
      have hwire_eq := TrWire.trWireMsg_of_fields? hfields
      rw [hwire_eq] at hwire_pub
      exact (Pub.inv_trWire hinv hwire_pub).2.2

theorem findRecvChain_mem {recv : List RecvChain} {pk : Bytes} {c : RecvChain}
    (h : findRecvChain recv pk = some c) : c ∈ recv := by
  unfold findRecvChain at h
  exact List.mem_of_find?_eq_some h

theorem bind_getEntry_at {Inv : ExecTrace → Prop} {E α : Type} [ExecTraceTypes.Has E]
    (idx : Nat) {f : E → Traceful α} (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ e : E, (tr.at? idx : Option E) = some e → Inv ((f e).run tr).2.val) :
    Inv ((((DY.getEntry idx : Traceful E) >>= f).run tr).2.val) := by
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [CompTrace.run_bind_snd, Traceful.run_mk]
  dsimp only
  rcases he : (tr.at? idx : Option E) with _ | e
  · exact hInv
  · exact hf e he

theorem bind_guardTrace_at {Inv : ExecTrace → Prop} {α : Type}
    (p : ExecTrace → Bool) {f : Unit → Traceful α} (tr : ExecTrace) (hInv : Inv tr)
    (hf : p tr = true → Inv ((f ()).run tr).2.val) :
    Inv (((guardTrace p >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.guardTrace
  rw [CompTrace.run_bind_snd, Traceful.run_mk]
  dsimp only
  by_cases hp : p tr = true
  · rw [ite_eq_left_iff.mpr fun h => absurd hp h]
    exact hf hp
  · rw [ite_eq_right_iff.mpr fun h => absurd h hp]
    exact hInv

theorem bind_receiveSignalMsg_at {α : Type}
    (msgIdx : Nat) {f : TRSignalMsg → Traceful α} (tr : ExecTrace) (hinv : SpqrInv tr)
    (hf : ∀ msg : TRSignalMsg, Pub tr msg.pqRatchet → SpqrInv ((f msg).run tr).2.val) :
    SpqrInv (((receiveSignalMsg msgIdx >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  rw [CompTrace.run_bind_assoc_snd]
  apply CompTrace.bind_receiveMessage_at msgIdx tr hinv
  intro raw hnet _
  have hraw : Pub tr raw := hinv.netPub raw (CompTrace.NetMsgAt.baseAttackerKnows hnet)
  rcases hparse : parseTrSignalMsg raw with _ | msg
  · dsimp only; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hinv
  · dsimp only
    rw [CompTrace.run_bind_assoc_snd]
    apply CompTrace.bind_guardP_at _ tr hinv
    intro _
    exact hf msg (pub_pqRatchet_of_parseTrSignalMsg hinv hraw hparse)

theorem bind_verifyMacAndDecrypt_at {Inv : ExecTrace → Prop} {α : Type}
    (st : TRState) (msg : TRSignalMsg) (pqSalt seed : Bytes) {f : Bytes → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ m : Bytes, Inv ((f m).run tr).2.val) :
    Inv (((verifyMacAndDecrypt st msg pqSalt seed >>= f).run tr).2.val) := by
  rw [CompTrace.run_bind_snd, CompTrace.verifyMacAndDecrypt_trace]
  rcases ((verifyMacAndDecrypt st msg pqSalt seed).run tr).1 with _ | m
  · exact hInv
  · exact hf m

theorem run_logEvent_bind_snd {Ev α : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    (ev : Ev) (f : Unit → Traceful α) (tr : ExecTrace) :
    ((ProtocolEvent.logEvent ev >>= f).run tr).2.val =
      ((f ()).run (tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT Ev))).2.val := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, CompTrace.run_bind_assoc_snd,
    CompTrace.run_bind_snd, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  dsimp only
  exact CompTrace.run_pure_bind_snd () f _

theorem run_sendMessage_snd (msg : Bytes) (tr : ExecTrace) :
    ((Network.sendMessage msg).run tr).2.val = tr.append (NetE msg) := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_mk]

theorem run_sendMessage_bind_snd {α : Type} (msg : Bytes) (f : Nat → Traceful α) (tr : ExecTrace) :
    ((Network.sendMessage msg >>= f).run tr).2.val =
      ((f tr.length).run (tr.append (NetE msg))).2.val := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, CompTrace.run_bind_snd,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]

theorem run_logMessageKeyAndStore_snd (me : Participant) (s : SessionInfo) (dir : KeyDir)
    (seed pqSalt : Bytes) (n : UInt32) (rIdx parIdx : Nat) (st : TRState)
    (tr : ExecTrace) :
    ((logMessageKeyAndStore me s dir seed pqSalt n rIdx parIdx st).run tr).2.val =
      (tr.append
        (TREvE (TREvent.MessageKey s dir seed pqSalt n rIdx parIdx))).append
        (TRStE me st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  rw [run_logEvent_bind_snd (Ev := TREvent),
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]

theorem run_logMessageKeyAndStore_bind_snd {α : Type}
    (me : Participant) (s : SessionInfo) (dir : KeyDir)
    (seed pqSalt : Bytes) (n : UInt32) (rIdx parIdx : Nat) (st : TRState)
    (f : Nat → Traceful α) (tr : ExecTrace) :
    ((logMessageKeyAndStore me s dir seed pqSalt n rIdx parIdx st >>= f).run tr).2.val =
      ((f (tr.length + 1)).run
        ((tr.append
          (TREvE (TREvent.MessageKey s dir seed pqSalt n rIdx parIdx))).append
          (TRStE me st))).2.val := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  rw [CompTrace.run_bind_assoc_snd, run_logEvent_bind_snd (Ev := TREvent),
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    CompTrace.run_bind_snd, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  dsimp
  have hlen :
      (tr.append
        (TREvE (TREvent.MessageKey s dir seed pqSalt n rIdx parIdx))).length =
      tr.length + 1 := by
    rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [hlen]

theorem append_logMessageKeyAndStore {tr : ExecTrace} (hinv : SpqrInv tr)
    (me : Participant) (s : SessionInfo) (dir : KeyDir)
    (seed pqSalt : Bytes) (n : UInt32) (rIdx parIdx : Nat) (st : TRState)
    (hok : TRStateOK tr me st) :
    SpqrInv ((logMessageKeyAndStore me s dir seed pqSalt n rIdx parIdx st).run tr).2.val := by
  rw [run_logMessageKeyAndStore_snd]
  have hinv1 := append_trEv_nonSkip hinv
    (ev := TREvent.MessageKey s dir seed pqSalt n rIdx parIdx)
    (by intro _ _ _ _ _ _ h; cases h)
  exact append_trSt hinv1 (hok.mono (Trace.append_le tr _))

/-! ## Receiver-Chain and `logSkippedKeys` Helpers -/

def RecvChainInv (keys : HandshakeKeys) (c : RecvChain) : Prop :=
  (c.index = 0 ∧ c.rIdx = 1 ∧ c.chainKey = keys.ck) ∨
  (∃ n, c.index.toNat = n + 1 ∧ c.rIdx = 1 ∧ c.chainKey = chainKeyAt keys.ck (n + 1)) ∨
  (∃ rkChain pk sk n,
    (rkChain = keys.rk ∨ ∃ r₀ p₀ s₀, rkChain = (createChain r₀ p₀ s₀).1) ∧
    c.chainKey = chainKeyAt (createChain rkChain pk sk).2 n)

theorem chainKeyAt_add (ck : Bytes) :
    ∀ a b : Nat, chainKeyAt (chainKeyAt ck a) b = chainKeyAt ck (a + b)
  | 0, b => by simp [chainKeyAt]
  | a + 1, b => by
    calc chainKeyAt (chainKeyAt ck (a + 1)) b
      _ = chainKeyAt (chainKeyAt (kdfCk ck).1 a) b := rfl
      _ = chainKeyAt (kdfCk ck).1 (a + b) := chainKeyAt_add (kdfCk ck).1 a b
      _ = chainKeyAt ck (a + 1 + b) := by rw [Nat.add_right_comm]; rfl

theorem skippedKeyOK_of_recvChainInv {tr : ExecTrace} {j : Nat} {keys : HandshakeKeys}
    {c : RecvChain} (hj : j < tr.length) (hkeys : HandshakeKeysAt tr j keys)
    (hc : RecvChainInv keys c) (m : Nat) :
    SkippedKeyOK tr (kdfCk (chainKeyAt c.chainKey m)).2 := by
  rcases hc with ⟨_, _, hck⟩ | ⟨n, _, _, hck⟩ | ⟨rkChain, pk, sk, n, hrk_c, hck⟩
  · exact ⟨j, keys, hj, hkeys, .inl ⟨m, by rw [hck]⟩⟩
  · refine ⟨j, keys, hj, hkeys, .inl ⟨n + 1 + m, ?_⟩⟩
    rw [hck, chainKeyAt_add]
  · refine ⟨j, keys, hj, hkeys, .inr ⟨rkChain, pk, sk, n + m, hrk_c, ?_⟩⟩
    rw [hck, chainKeyAt_add]

theorem u32_add_one_toNat {counter : UInt32} (hmax : counter ≠ u32Max) :
    (counter + 1).toNat = counter.toNat + 1 := by
  have hlt : counter.toNat < 4294967295 := by
    apply Classical.byContradiction
    intro hge
    apply hmax
    apply UInt32.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    have := counter.toBitVec.isLt
    change counter.toNat < 4294967296 at this
    change counter.toNat = 4294967295
    omega
  rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)]

theorem recvChainInv_of_consumeMessageKey {keys : HandshakeKeys}
    {c c' : RecvChain} {counter : UInt32} {seed : Bytes}
    (hc : RecvChainInv keys c)
    (hcons : consumeMessageKey c counter = some (seed, c')) :
    RecvChainInv keys c' := by
  unfold consumeMessageKey at hcons
  split at hcons
  · cases hcons
  · rename_i hnot_lt
    split at hcons
    · cases hcons
    · split at hcons
      · cases hcons
      · rename_i hnot_max
        injection hcons with hpair
        have hc'_eq : c' = { c with
            chainKey := (kdfCk (chainKeyAt c.chainKey (counter.toNat - c.index.toNat))).1,
            index := counter + 1 } := (congrArg Prod.snd hpair).symm
        have hle_idx : c.index.toNat ≤ counter.toNat := by
          change ¬ (counter.toNat < c.index.toNat) at hnot_lt
          omega
        have hadd1 : (counter + 1).toNat = counter.toNat + 1 := u32_add_one_toNat hnot_max
        have hck_step :
            (kdfCk (chainKeyAt c.chainKey (counter.toNat - c.index.toNat))).1 =
              chainKeyAt c.chainKey (counter.toNat - c.index.toNat + 1) :=
          (chainKeyAt_succ_eq_kdfCk_fst c.chainKey (counter.toNat - c.index.toNat)).symm
        rw [hc'_eq]
        rcases hc with ⟨hidx0, hrIdx1, hck⟩ | ⟨n, hidx, hrIdx1, hck⟩ |
          ⟨rkChain, pk, sk, n, hrk_c, hck⟩
        · right; left
          refine ⟨counter.toNat, hadd1, hrIdx1, ?_⟩
          have hidx0_nat : c.index.toNat = 0 := by rw [hidx0]; rfl
          rw [hck_step, hck, hidx0_nat, Nat.sub_zero]
        · right; left
          refine ⟨counter.toNat, hadd1, hrIdx1, ?_⟩
          rw [hck_step, hck, chainKeyAt_add, hidx]
          rw [hidx] at hle_idx
          exact congrArg (chainKeyAt keys.ck) (by omega)
        · right; right
          refine ⟨rkChain, pk, sk, n + (counter.toNat - c.index.toNat + 1), hrk_c, ?_⟩
          rw [hck_step, hck, chainKeyAt_add]

theorem setRecvChain_mem_cases {recv : List RecvChain} {c' d : RecvChain}
    (hd : d ∈ setRecvChain recv c') : d = c' ∨ d ∈ recv := by
  unfold setRecvChain at hd
  rw [List.mem_map] at hd
  obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := hd
  split at hc₀_eq
  · exact .inl hc₀_eq.symm
  · exact .inr (hc₀_eq ▸ hc₀_mem)

theorem logSkippedKeys_trace (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : Bytes) (n : UInt32) (tr : ExecTrace),
      ∃ tr', ((logSkippedKeys s pk rIdx src ck n k).run tr).2.val = tr' ∧
        tr ≤ tr' ∧
        (∀ j keys, j < tr.length → HandshakeKeysAt tr j keys →
          (∀ m, SkippedKeyOK tr (kdfCk (chainKeyAt ck m)).2) →
          SpqrInv tr → SpqrInv tr')
  | 0, ck, n, tr =>
    ⟨tr, by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [Traceful.run_pure],
      Trace.le_refl tr, fun _ _ _ _ _ hinv => hinv⟩
  | k + 1, ck, n, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [run_logEvent_bind_snd (Ev := TREvent)]
    let tr1 := tr.append (TREvE (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx src))
    obtain ⟨tr', hrun, hle1, hpres⟩ := logSkippedKeys_trace s pk rIdx src k (kdfCk ck).1 (n + 1) tr1
    have hle0 : tr ≤ tr1 := Trace.append_le tr _
    refine ⟨tr', hrun, Trace.le_trans tr tr1 tr' hle0 hle1, ?_⟩
    intro j keys hj hkeys hck_ok hinv
    have hinv1 : SpqrInv tr1 := by
      refine append_trEv hinv ?_
      intro s' rPk' ctr' seed' rIdx' src' heq
      injection heq with _ _ _ hseed_eq _ _
      rw [← hseed_eq]
      exact hck_ok 0
    have hj1 : j < tr1.length := Nat.lt_of_lt_of_le hj (Trace.length_le tr tr1 hle0)
    have hkeys1 : HandshakeKeysAt tr1 j keys := handshakeKeysAt_mono hle0 hkeys
    have hck_ok1 : ∀ m, SkippedKeyOK tr1 (kdfCk (chainKeyAt (kdfCk ck).1 m)).2 := by
      intro m
      exact (hck_ok (m + 1)).mono hle0
    exact hpres j keys hj1 hkeys1 hck_ok1 hinv1

end Symbolic.Swarm.COMPOSED.CompPresTRExp

namespace Symbolic.Swarm.COMPOSED.CompInv

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed
open Symbolic.Swarm.COMPOSED.CompTermAlgebra
open Symbolic.Swarm.COMPOSED.CompKeyInversion
open Symbolic.Swarm.COMPOSED.CompPresTRExp
open Symbolic.Swarm.COMPOSED.CompInv.CompPubInv

/-! ## State-Exposure Transitions -/

theorem preserves_exposeSpqr (me : Participant) (stateIdx : Nat) :
    Preserves SpqrInv (DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx) := by
  intro tr hinv
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hinv
  intro st hst
  obtain ⟨j, keys, hj, hkeys, hhs, _, hspqr, _, _, _⟩ := hinv.trStOK me st stateIdx hst
  rw [run_logEvent_bind_snd (Ev := TREvent), run_sendMessage_snd]
  have hinv1 : SpqrInv (tr.append (TREvE (TREvent.ExposedSpqr (st.sessionInfo me) st.spqr st.rIdx))) :=
    append_trEv_nonSkip hinv (by intro _ _ _ _ _ _ h; cases h)
  have hle1 : tr ≤ tr.append (TREvE (TREvent.ExposedSpqr (st.sessionInfo me) st.spqr st.rIdx)) :=
    Trace.append_le tr _
  have hexp :
      SessionStateExposed
        (tr.append (TREvE (TREvent.ExposedSpqr (st.sessionInfo me) st.spqr st.rIdx)))
        keys keys.pqr :=
    ⟨st.sessionInfo me, j, ev_mono hle1 hhs, handshakeKeysAt_mono hle1 hkeys,
      .inl ⟨rfl, st.spqr, st.rIdx,
        CompTrace.eventLogged_here tr (TREvent.ExposedSpqr (st.sessionInfo me) st.spqr st.rIdx)⟩⟩
  have hpqr :
      Pub (tr.append (TREvE (TREvent.ExposedSpqr (st.sessionInfo me) st.spqr st.rIdx))) keys.pqr :=
    .exp (.pqr hexp)
  have hspqr_pub :
      Pub (tr.append (TREvE (TREvent.ExposedSpqr (st.sessionInfo me) st.spqr st.rIdx))) st.spqr :=
    SpqrStateFrom.pub_of_pub (hspqr.mono hle1) hpqr
  exact append_net_of_pub hinv1 hspqr_pub

theorem preserves_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    Preserves SpqrInv (DY.Libsignal.TripleRatchet.exposeKey me stateIdx k) := by
  intro tr hinv
  unfold DY.Libsignal.TripleRatchet.exposeKey
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hinv
  intro st hst
  obtain ⟨j, keys, hj, hkeys, hhs, hdhs, _, hrk, hcks, hrecv⟩ := hinv.trStOK me st stateIdx hst
  cases k with
  | rk =>
    dsimp only
    rw [run_logEvent_bind_snd (Ev := TREvent), run_sendMessage_snd]
    have hinv1 : SpqrInv (tr.append (TREvE (TREvent.ExposedRK (st.sessionInfo me) st.rk st.rIdx))) :=
      append_trEv_nonSkip hinv (by intro _ _ _ _ _ _ h; cases h)
    obtain ⟨r, p, s, hrk_eq⟩ := hrk
    have hpub0 : Pub tr st.rk := by rw [hrk_eq]; exact .exp (.rkRatchet r p s)
    exact append_net_of_pub hinv1 (hpub0.mono (Trace.append_le tr _))
  | dhs =>
    dsimp only
    rw [run_logEvent_bind_snd (Ev := TREvent), run_sendMessage_snd]
    rcases hdhs with ⟨t, hdhs_eq, hslot⟩ | ⟨t, msg, hdhs_eq, hr, hn⟩
    · rw [hdhs_eq]
      have hinv1 :
          SpqrInv (tr.append (TREvE (TREvent.ExposedDHs (st.sessionInfo me) (rnd (t + 2) 32) st.rIdx))) :=
        append_trEv_nonSkip hinv (by intro _ _ _ _ _ _ h; cases h)
      have hle1 :
          tr ≤ tr.append (TREvE (TREvent.ExposedDHs (st.sessionInfo me) (rnd (t + 2) 32) st.rIdx)) :=
        Trace.append_le tr _
      have hpub :
          Pub (tr.append (TREvE (TREvent.ExposedDHs (st.sessionInfo me) (rnd (t + 2) 32) st.rIdx)))
            (rnd (t + 2) 32) :=
        .rand (.inr (.inr (.inr (.inr (.inr (.inr (.inl
          ⟨.inl ⟨t, rfl, hslot.mono hle1⟩, st.sessionInfo me, st.rIdx,
           CompTrace.eventLogged_here tr
             (TREvent.ExposedDHs (st.sessionInfo me) (rnd (t + 2) 32) st.rIdx)⟩)))))))
      exact append_net_of_pub hinv1 hpub
    · rw [hdhs_eq]
      have hinv1 :
          SpqrInv (tr.append (TREvE (TREvent.ExposedDHs (st.sessionInfo me) (rnd t 32) st.rIdx))) :=
        append_trEv_nonSkip hinv (by intro _ _ _ _ _ _ h; cases h)
      have hle1 :
          tr ≤ tr.append (TREvE (TREvent.ExposedDHs (st.sessionInfo me) (rnd t 32) st.rIdx)) :=
        Trace.append_le tr _
      have hpub :
          Pub (tr.append (TREvE (TREvent.ExposedDHs (st.sessionInfo me) (rnd t 32) st.rIdx)))
            (rnd t 32) :=
        .rand (.inr (.inr (.inr (.inr (.inr (.inr (.inl
          ⟨.inr ⟨t, msg, rfl, hr.mono hle1, hn.mono hle1⟩, st.sessionInfo me, st.rIdx,
           CompTrace.eventLogged_here tr
             (TREvent.ExposedDHs (st.sessionInfo me) (rnd t 32) st.rIdx)⟩)))))))
      exact append_net_of_pub hinv1 hpub
  | cks =>
    dsimp only
    rw [run_logEvent_bind_snd (Ev := TREvent), run_sendMessage_snd]
    have hinv1 :
        SpqrInv (tr.append (TREvE (TREvent.ExposedCKs (st.sessionInfo me) st.cks st.ns st.rIdx))) :=
      append_trEv_nonSkip hinv (by intro _ _ _ _ _ _ h; cases h)
    obtain ⟨rkChain, pk, sk, n, hrk_c, hcks_eq⟩ := hcks
    have hpub0 : Pub tr st.cks := by rw [hcks_eq]; exact .exp (.chainRatchet hj hkeys hrk_c)
    exact append_net_of_pub hinv1 (hpub0.mono (Trace.append_le tr _))
  | ckr pk =>
    dsimp only
    rcases hfind : findRecvChain st.recv pk with _ | c
    · dsimp only; rw [Traceful.run_failure]; exact hinv
    · dsimp only
      have hc_mem : c ∈ st.recv := findRecvChain_mem hfind
      rw [run_logEvent_bind_snd (Ev := TREvent), run_sendMessage_snd]
      rcases hrecv c hc_mem with ⟨_, _, hck_eq⟩ |
        ⟨n, _, _, hck_eq⟩ | ⟨rkChain, pk', sk', n, hrk_c, hck_eq⟩
      · rw [hck_eq]
        have hinv1 :
            SpqrInv (tr.append (TREvE (TREvent.ExposedCKr (st.sessionInfo me) keys.ck c.index c.rIdx))) :=
          append_trEv_nonSkip hinv (by intro _ _ _ _ _ _ h; cases h)
        have hle1 :
            tr ≤ tr.append (TREvE (TREvent.ExposedCKr (st.sessionInfo me) keys.ck c.index c.rIdx)) :=
          Trace.append_le tr _
        have hexp :
            SessionStateExposed
              (tr.append (TREvE (TREvent.ExposedCKr (st.sessionInfo me) keys.ck c.index c.rIdx)))
              keys keys.ck :=
          ⟨st.sessionInfo me, j, ev_mono hle1 hhs, handshakeKeysAt_mono hle1 hkeys,
            .inr (.inl ⟨rfl, c.index, c.rIdx,
              CompTrace.eventLogged_here tr
                (TREvent.ExposedCKr (st.sessionInfo me) keys.ck c.index c.rIdx)⟩)⟩
        exact append_net_of_pub hinv1 (.exp (.ck0 hexp))
      · have hinv1 :
            SpqrInv (tr.append (TREvE (TREvent.ExposedCKr (st.sessionInfo me) c.chainKey c.index c.rIdx))) :=
          append_trEv_nonSkip hinv (by intro _ _ _ _ _ _ h; cases h)
        have hpub0 : Pub tr c.chainKey := by rw [hck_eq]; exact .exp (.ckStep hj hkeys)
        exact append_net_of_pub hinv1 (hpub0.mono (Trace.append_le tr _))
      · have hinv1 :
            SpqrInv (tr.append (TREvE (TREvent.ExposedCKr (st.sessionInfo me) c.chainKey c.index c.rIdx))) :=
          append_trEv_nonSkip hinv (by intro _ _ _ _ _ _ h; cases h)
        have hpub0 : Pub tr c.chainKey := by rw [hck_eq]; exact .exp (.chainRatchet hj hkeys hrk_c)
        exact append_net_of_pub hinv1 (hpub0.mono (Trace.append_le tr _))

theorem preserves_exposeSkipped (skippedKeyEventIdx : Nat) :
    Preserves SpqrInv (DY.Libsignal.TripleRatchet.exposeSkipped skippedKeyEventIdx) := by
  intro tr hinv
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  apply bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hinv
  intro e he
  rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    dsimp only
    have hsk : SkippedKeyOK tr seed :=
      hinv.skipOK s pk n seed rIdx src skippedKeyEventIdx
        (by rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact he)
    obtain ⟨j, keys, hj, hkeys, hseed⟩ := hsk
    apply bind_guardTrace_at _ tr hinv
    intro _
    rw [run_logEvent_bind_snd (Ev := TREvent), run_sendMessage_snd]
    have hinv1 : SpqrInv (tr.append (TREvE (TREvent.ExposedMK s seed n rIdx))) :=
      append_trEv_nonSkip hinv (by intro _ _ _ _ _ _ h; cases h)
    have hle1 : tr ≤ tr.append (TREvE (TREvent.ExposedMK s seed n rIdx)) :=
      Trace.append_le tr _
    have hj1 : j < (tr.append (TREvE (TREvent.ExposedMK s seed n rIdx))).length :=
      Nat.lt_of_lt_of_le hj (Trace.length_le tr _ hle1)
    have hkeys1 : HandshakeKeysAt (tr.append (TREvE (TREvent.ExposedMK s seed n rIdx))) j keys :=
      handshakeKeysAt_mono hle1 hkeys
    have hpub : Pub (tr.append (TREvE (TREvent.ExposedMK s seed n rIdx))) seed := by
      rcases hseed with ⟨m, rfl⟩ | ⟨rkChain, pk', sk', m, hrk_c, rfl⟩
      · exact .exp (.seedCk hj1 hkeys1)
      · exact .exp (.seedRatchet hj1 hkeys1 hrk_c)
    exact append_net_of_pub hinv1 hpub
  | _ => dsimp only; rw [Traceful.run_failure]; exact hinv

/-! ## Messaging Transitions -/

theorem preserves_messageEncryptAbort (me : Participant) (stateIdx : Nat) :
    Preserves SpqrInv (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) := by
  intro tr hinv
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hinv
  intro _ _
  rw [CompTrace.run_genRand_bind_snd, Traceful.run_failure]
  exact append_rnd 32 hinv

theorem preserves_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    Preserves SpqrInv (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
  intro tr hinv
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hinv
  intro st hst
  obtain ⟨j, keys, hj, hkeys, hhs, hdhs, hspqr, hrk, hcks, hrecv⟩ := hinv.trStOK me st stateIdx hst
  apply CompTrace.bind_guardP_at _ tr hinv
  intro _
  rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, run_sendMessage_bind_snd]
  let m := rnd tr.length 32
  let tr1 := tr.append (RndE 32)
  let coins := rnd tr1.length coinsLen
  let tr2 := tr1.append (RndE coinsLen)
  let key := (Spqr.spqrSend st.spqr coins).2.1
  let tr3 := tr2.append (NetE key)
  have hinv1 : SpqrInv tr1 := append_rnd 32 hinv
  have hinv2 : SpqrInv tr2 := append_rnd coinsLen hinv1
  have hinv3 : SpqrInv tr3 := append_net_of_pub hinv2 (spqrSendKey_of st.spqr coins)
  have hle01 : tr ≤ tr1 := Trace.append_le tr _
  have hle12 : tr1 ≤ tr2 := Trace.append_le tr1 _
  have hle23 : tr2 ≤ tr3 := Trace.append_le tr2 _
  have hle03 : tr ≤ tr3 := Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 hle01 hle12) hle23
  have hle13 : tr1 ≤ tr3 := Trace.le_trans tr1 tr2 tr3 hle12 hle23
  apply CompTrace.bind_receiveMessage_at pqIdx tr3 hinv3
  intro pqSalt _ _
  rw [run_logEvent_bind_snd (Ev := TREvent), run_logMessageKeyAndStore_bind_snd, run_sendMessage_snd]
  let tr4 := tr3.append (TREvE (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m))
  have hinv4 : SpqrInv tr4 := append_trEv_nonSkip hinv3 (by intro _ _ _ _ _ _ h; cases h)
  have hle34 : tr3 ≤ tr4 := Trace.append_le tr3 _
  have hle24 : tr2 ≤ tr4 := Trace.le_trans tr2 tr3 tr4 hle23 hle34
  have hle14 : tr1 ≤ tr4 := Trace.le_trans tr1 tr3 tr4 hle13 hle34
  have hle04 : tr ≤ tr4 := Trace.le_trans tr tr3 tr4 hle03 hle34
  have hlen1 : tr1.length = tr.length + 1 := by
    dsimp only [tr1]; rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlen2 : tr2.length = tr.length + 2 := by
    dsimp only [tr2]; rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, hlen1]
  have hlen3 : tr3.length = tr.length + 3 := by
    dsimp only [tr3]; rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, hlen2]
  have hr_m : RandAt tr4 tr.length 32 := RandAt.mono hle14 (CompTrace.randAt_here tr 32)
  have hr_c : RandAt tr4 (tr.length + 1) coinsLen :=
    hlen1 ▸ RandAt.mono hle24 (CompTrace.randAt_here tr1 coinsLen)
  have hn_k : NetAt tr4 key (tr.length + 2) :=
    hlen2 ▸ NetAt.mono hle34 (CompTrace.at?_append_here tr2 (NetE key))
  have hev_sent : tr4.EventLoggedAt (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m) (tr.length + 3) :=
    hlen3 ▸ CompTrace.eventLoggedAt_here tr3 (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m)
  have hm_pub4 : Pub tr4 m :=
    .rand (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inl ⟨tr.length, coinsLen, key, rfl, hr_m, hr_c, hn_k, _, hev_sent⟩))))))))
  have hcoins_pub4 : Pub tr4 coins :=
    .rand (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inr ⟨tr.length, coinsLen, key, congrArg (rnd · coinsLen) hlen1, hr_m, hr_c, hn_k, _, hev_sent⟩))))))))
  let st' : TRState :=
    { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := (Spqr.spqrSend st.spqr coins).1 }
  obtain ⟨rkChain, pk_c, sk_c, n_c, hrk_c, hcks_eq⟩ := hcks
  have hst'_ok4 : TRStateOK tr4 me st' := by
    refine ⟨j, keys, Nat.lt_of_lt_of_le hj (Trace.length_le tr tr4 hle04),
      handshakeKeysAt_mono hle04 hkeys, ev_mono hle04 hhs, ?_,
      SpqrStateFrom.of_spqrSend (hspqr.mono hle04) hcoins_pub4, hrk,
      ⟨rkChain, pk_c, sk_c, n_c + 1, hrk_c, ?_⟩, hrecv⟩
    · rcases hdhs with h | h
      · exact .inl (h.mono hle04)
      · exact .inr (h.mono hle04)
    · dsimp only [st']
      rw [hcks_eq, ← chainKeyAt_succ_eq_kdfCk_fst]
  have hinv6 : SpqrInv ((logMessageKeyAndStore me (st.sessionInfo me) .sender
      (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st').run tr4).2.val :=
    append_logMessageKeyAndStore hinv4 me (st.sessionInfo me) .sender
      (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st' hst'_ok4
  rw [run_logMessageKeyAndStore_snd] at hinv6
  let tr5 := tr4.append (TREvE (TREvent.MessageKey (st.sessionInfo me) .sender
    (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx))
  let tr6 := tr5.append (TRStE me st')
  have hle46 : tr4 ≤ tr6 :=
    Trace.le_trans tr4 tr5 tr6 (Trace.append_le tr4 _) (Trace.append_le tr5 _)
  have hdh_pub4 : Pub tr4 (DiffieHellman.dhPk st.dhs) := by
    rcases hdhs with h | h
    · exact .dhPub (.inr (.inr (.inr (.inr (.inl (h.mono hle04))))))
    · exact .dhPub (.inr (.inr (.inr (.inr (.inr (h.mono hle04))))))
  let mk := trMsgKeys pqSalt (kdfCk st.cks).2
  let wire := trHonestWireMsg (DiffieHellman.dhPk st.dhs) st.ns st.pn
    (SymEnc.symEnc mk.cipherKey mk.iv m) (Spqr.spqrSend st.spqr coins).2.2
  have hwire_pub4 : Pub tr4 wire :=
    .trWire hdh_pub4 (.enc hm_pub4) (spqrSendMsg_of st.spqr coins)
  have hmac_hon4 :
      HonestMac tr4
        (hmac mk.macKey
          (Concat.concat st.myIk (Concat.concat st.peerIk wire))) := by
    refine ⟨j, keys, rkChain, pk_c, sk_c, n_c, pqSalt, st.myIk, st.peerIk, wire,
      Nat.lt_of_lt_of_le hj (Trace.length_le tr tr4 hle04),
      handshakeKeysAt_mono hle04 hkeys, hrk_c, ?_⟩
    dsimp only [mk]
    rw [hcks_eq]
  have hmac_pub4 : Pub tr4 (computeMac mk.macKey st.myIk st.peerIk wire) :=
    .truncHonest hmac_hon4
  have hcat_pub4 : Pub tr4 (Concat.concat wire (computeMac mk.macKey st.myIk st.peerIk wire)) :=
    .cat hwire_pub4 hmac_pub4
  exact append_net_of_pub hinv6 (hcat_pub4.mono hle46)

theorem preserves_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves SpqrInv
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me
        stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  intro tr hinv
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hinv
  intro st hst
  obtain ⟨j, keys, hj, hkeys, hhs, hdhs, hspqr, hrk, hcks, hrecv⟩ := hinv.trStOK me st stateIdx hst
  apply bind_receiveSignalMsg_at msgIdx tr hinv
  intro msg hpq_pub
  apply bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hinv
  intro e _
  rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx _sourceStateIdx =>
    dsimp only
    apply CompTrace.bind_guardP_at _ tr hinv
    intro _
    apply bind_guardTrace_at _ tr hinv
    intro _
    rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; rw [Traceful.run_failure]; exact hinv
    · dsimp only
      rw [run_sendMessage_bind_snd]
      let tr1 := tr.append (NetE key)
      have hinv1 : SpqrInv tr1 := append_net_of_pub hinv (spqrRecvKey_of hspqr_recv)
      have hle01 : tr ≤ tr1 := Trace.append_le tr _
      apply CompTrace.bind_receiveMessage_at pqIdx tr1 hinv1
      intro pqSalt _ _
      apply bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hinv1
      intro m
      rw [run_logEvent_bind_snd (Ev := TREvent), run_logEvent_bind_snd (Ev := TREvent)]
      let tr2 := tr1.append (TREvE (TREvent.SkippedKeyUsed s skippedKeyEventIdx))
      let tr3 := tr2.append (TREvE (TREvent.Received me st.peer pk n m))
      have hinv2 : SpqrInv tr2 := append_trEv_nonSkip hinv1 (by intro _ _ _ _ _ _ h; cases h)
      have hinv3 : SpqrInv tr3 := append_trEv_nonSkip hinv2 (by intro _ _ _ _ _ _ h; cases h)
      have hle03 : tr ≤ tr3 :=
        Trace.le_trans tr tr2 tr3
          (Trace.le_trans tr tr1 tr2 hle01 (Trace.append_le tr1 _))
          (Trace.append_le tr2 _)
      have hst'_ok3 : TRStateOK tr3 me { st with spqr := spqr' } := by
        refine ⟨j, keys, Nat.lt_of_lt_of_le hj (Trace.length_le tr tr3 hle03),
          handshakeKeysAt_mono hle03 hkeys, ev_mono hle03 hhs, ?_,
          (SpqrStateFrom.of_spqrRecv hspqr_recv hspqr hpq_pub).mono hle03, hrk, hcks, hrecv⟩
        rcases hdhs with h | h
        · exact .inl (h.mono hle03)
        · exact .inr (h.mono hle03)
      exact append_logMessageKeyAndStore hinv3 me s .receiver seed pqSalt n
        rIdx stateIdx { st with spqr := spqr' } hst'_ok3
  | _ => dsimp only; rw [Traceful.run_failure]; exact hinv

theorem preserves_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    Preserves SpqrInv
      (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  intro tr hinv
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hinv
  intro st hst
  obtain ⟨j, keys, hj, hkeys, hhs, hdhs, hspqr, hrk, hcks, hrecv⟩ := hinv.trStOK me st stateIdx hst
  apply bind_receiveSignalMsg_at msgIdx tr hinv
  intro msg hpq_pub
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor
  rcases hfind : findRecvChain st.recv msg.ratchetKey with _ | c
  ·
    dsimp only
    rcases hlow : x25519LowOrder msg.ratchetKey with _ | _
    · simp only [Bool.false_eq_true, ↓reduceIte,
        DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_bind_assoc_snd]
      apply CompTrace.bind_guardP_at _ tr hinv
      intro _
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_genRand_bind_snd,
        CompTrace.run_pure_bind_snd, CompTrace.run_pure_bind_snd]
      let tr1 := tr.append (RndE 32)
      have hinv1 : SpqrInv tr1 := append_rnd 32 hinv
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
      · dsimp only; rw [Traceful.run_failure]; exact hinv1
      · dsimp only
        rcases hspqr_recv : Spqr.spqrRecv st1.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
        · dsimp only; rw [Traceful.run_failure]; exact hinv1
        · dsimp only
          rw [run_sendMessage_bind_snd]
          let tr2 := tr1.append (NetE key)
          have hinv2 : SpqrInv tr2 := append_net_of_pub hinv1 (spqrRecvKey_of hspqr_recv)
          have hle12 : tr1 ≤ tr2 := Trace.append_le tr1 _
          have hle02 : tr ≤ tr2 := Trace.le_trans tr tr1 tr2 hle01 hle12
          have hlen1 : tr1.length = tr.length + 1 := by
            dsimp only [tr1]; rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
          have hdhs'_tr : TRRatchetAt tr2 dhs' :=
            ⟨tr.length, key, rfl, RandAt.mono hle12 (CompTrace.randAt_here tr 32),
              hlen1 ▸ CompTrace.at?_append_here tr1 (NetE key)⟩
          obtain ⟨r₀, p₀, s₀, hrk_eq⟩ := hrk
          have hc_new_inv : RecvChainInv keys c_new :=
            .inr (.inr ⟨st.rk, msg.ratchetKey, st.dhs, 0, .inr ⟨r₀, p₀, s₀, hrk_eq⟩, rfl⟩)
          have hc'_inv : RecvChainInv keys c' :=
            recvChainInv_of_consumeMessageKey hc_new_inv hcons
          apply CompTrace.bind_receiveMessage_at pqIdx tr2 hinv2
          intro pqSalt _ _
          apply bind_verifyMacAndDecrypt_at st1 msg pqSalt seed tr2 hinv2
          intro m
          simp only [↓reduceIte]
          rw [run_logEvent_bind_snd (Ev := TREvent), run_logEvent_bind_snd (Ev := TREvent),
            CompTrace.run_bind_snd]
          let tr3 := tr2.append (TREvE (TREvent.DHRatchet me st1.peer msg.ratchetKey (DiffieHellman.dhPk st1.dhs)))
          let tr4 := tr3.append (TREvE (TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2)))
          have hinv3 : SpqrInv tr3 := append_trEv_nonSkip hinv2 (by intro _ _ _ _ _ _ h; cases h)
          have hinv4 : SpqrInv tr4 := append_trEv_nonSkip hinv3 (by intro _ _ _ _ _ _ h; cases h)
          have hle24 : tr2 ≤ tr4 :=
            Trace.le_trans tr2 tr3 tr4 (Trace.append_le tr2 _) (Trace.append_le tr3 _)
          have hle04 : tr ≤ tr4 := Trace.le_trans tr tr2 tr4 hle02 hle24
          have hj4 : j < tr4.length := Nat.lt_of_lt_of_le hj (Trace.length_le tr tr4 hle04)
          have hkeys4 : HandshakeKeysAt tr4 j keys := handshakeKeysAt_mono hle04 hkeys
          have hck_ok4 : ∀ k, SkippedKeyOK tr4 (kdfCk (chainKeyAt c_new.chainKey k)).2 :=
            skippedKeyOK_of_recvChainInv hj4 hkeys4 hc_new_inv
          obtain ⟨tr5, hrun5, hle45, hpres5⟩ :=
            logSkippedKeys_trace (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
              (msg.counter.toNat - c_new.index.toNat) c_new.chainKey c_new.index tr4
          have hinv5 : SpqrInv tr5 := hpres5 j keys hj4 hkeys4 hck_ok4 hinv4
          rcases hsk_res :
              (logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
                c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4 with
            ⟨_ | u, tr5_sub⟩
          · have htr5_eq : tr5_sub.val = tr5 := by rw [← hrun5, hsk_res]
            rw [htr5_eq]; exact hinv5
          · have htr5_eq : tr5_sub.val = tr5 := by rw [← hrun5, hsk_res]
            dsimp only
            rw [htr5_eq, run_logEvent_bind_snd (Ev := TREvent)]
            let tr6 := tr5.append (TREvE (TREvent.Received me st1.peer msg.ratchetKey msg.counter m))
            have hinv6 : SpqrInv tr6 := append_trEv_nonSkip hinv5 (by intro _ _ _ _ _ _ h; cases h)
            have hle26 : tr2 ≤ tr6 :=
              Trace.le_trans tr2 tr5 tr6 (Trace.le_trans tr2 tr4 tr5 hle24 hle45) (Trace.append_le tr5 _)
            have hle06 : tr ≤ tr6 := Trace.le_trans tr tr2 tr6 hle02 hle26
            let st2 : TRState := { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
            have hst2_ok6 : TRStateOK tr6 me st2 := by
              refine ⟨j, keys, Nat.lt_of_lt_of_le hj (Trace.length_le tr tr6 hle06),
                handshakeKeysAt_mono hle06 hkeys, ev_mono hle06 hhs,
                .inr (hdhs'_tr.mono hle26),
                (SpqrStateFrom.of_spqrRecv hspqr_recv hspqr hpq_pub).mono hle06,
                ⟨rk1, msg.ratchetKey, dhs', rfl⟩,
                ⟨rk1, msg.ratchetKey, dhs', 0, .inr ⟨st.rk, msg.ratchetKey, st.dhs, rfl⟩, rfl⟩,
                ?_⟩
              intro d hd
              rcases setRecvChain_mem_cases hd with rfl | hd_mem1
              · exact hc'_inv
              · have hd_app : d ∈ st.recv ++ [c_new] := List.mem_of_mem_drop hd_mem1
                rcases List.mem_append.mp hd_app with hd_old | hd_new
                · exact hrecv d hd_old
                · rw [List.mem_singleton] at hd_new
                  subst hd_new
                  exact hc_new_inv
            exact append_logMessageKeyAndStore hinv6 me (st1.sessionInfo me) .receiver
              seed pqSalt msg.counter c_new.rIdx stateIdx st2 hst2_ok6
    · simp only [↓reduceIte]; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hinv
  ·
    dsimp only
    rw [CompTrace.run_pure_bind_snd]
    have hc_mem : c ∈ st.recv := findRecvChain_mem hfind
    have hc_inv : RecvChainInv keys c := hrecv c hc_mem
    rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
    · dsimp only; rw [Traceful.run_failure]; exact hinv
    · dsimp only
      have hc'_inv : RecvChainInv keys c' := recvChainInv_of_consumeMessageKey hc_inv hcons
      rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
      · dsimp only; rw [Traceful.run_failure]; exact hinv
      · dsimp only
        rw [run_sendMessage_bind_snd]
        let tr1 := tr.append (NetE key)
        have hinv1 : SpqrInv tr1 := append_net_of_pub hinv (spqrRecvKey_of hspqr_recv)
        have hle01 : tr ≤ tr1 := Trace.append_le tr _
        apply CompTrace.bind_receiveMessage_at pqIdx tr1 hinv1
        intro pqSalt _ _
        apply bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hinv1
        intro m
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [CompTrace.run_bind_snd]
        have hj1 : j < tr1.length := Nat.lt_of_lt_of_le hj (Trace.length_le tr tr1 hle01)
        have hkeys1 : HandshakeKeysAt tr1 j keys := handshakeKeysAt_mono hle01 hkeys
        have hck_ok1 : ∀ k, SkippedKeyOK tr1 (kdfCk (chainKeyAt c.chainKey k)).2 :=
          skippedKeyOK_of_recvChainInv hj1 hkeys1 hc_inv
        obtain ⟨tr2, hrun2, hle12, hpres2⟩ :=
          logSkippedKeys_trace (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
            (msg.counter.toNat - c.index.toNat) c.chainKey c.index tr1
        have hinv2 : SpqrInv tr2 := hpres2 j keys hj1 hkeys1 hck_ok1 hinv1
        rcases hsk_res :
            (logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
              c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1 with
          ⟨_ | u, tr2_sub⟩
        · have htr2_eq : tr2_sub.val = tr2 := by rw [← hrun2, hsk_res]
          rw [htr2_eq]; exact hinv2
        · have htr2_eq : tr2_sub.val = tr2 := by rw [← hrun2, hsk_res]
          dsimp only
          rw [htr2_eq, run_logEvent_bind_snd (Ev := TREvent)]
          let tr3 := tr2.append (TREvE (TREvent.Received me st.peer msg.ratchetKey msg.counter m))
          have hinv3 : SpqrInv tr3 := append_trEv_nonSkip hinv2 (by intro _ _ _ _ _ _ h; cases h)
          have hle03 : tr ≤ tr3 :=
            Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 hle01 hle12) (Trace.append_le tr2 _)
          let st2 : TRState := { st with recv := setRecvChain st.recv c', spqr := spqr' }
          have hst2_ok3 : TRStateOK tr3 me st2 := by
            refine ⟨j, keys, Nat.lt_of_lt_of_le hj (Trace.length_le tr tr3 hle03),
              handshakeKeysAt_mono hle03 hkeys, ev_mono hle03 hhs, ?_,
              (SpqrStateFrom.of_spqrRecv hspqr_recv hspqr hpq_pub).mono hle03, hrk, hcks, ?_⟩
            · rcases hdhs with h | h
              · exact .inl (h.mono hle03)
              · exact .inr (h.mono hle03)
            · intro d hd
              rcases setRecvChain_mem_cases hd with rfl | hd_old
              · exact hc'_inv
              · exact hrecv d hd_old
          exact append_logMessageKeyAndStore hinv3 me (st.sessionInfo me) .receiver
            seed pqSalt msg.counter c.rIdx stateIdx st2 hst2_ok3

end Symbolic.Swarm.COMPOSED.CompInv
