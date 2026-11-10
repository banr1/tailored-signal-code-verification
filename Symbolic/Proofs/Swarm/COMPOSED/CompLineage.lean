/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import all DY.Bytes.Basic
import all DY.Actions.Network
import all DY.Actions.ProtocolEvent
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.ALaCarte.Basic
import all DY.Trace.BaseAttackerKnowledge
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Actions.Random

/-!
# Composed Session-Origin and Receiver-Chain Lineage Invariant

Defines the `InertOnPQXDH` preservation combinator and the `CompSessionOriginInv` invariant
tracking PQXDH handshake origins, stored `TRState` ratchet indices, and receiver-chain lineage
across transitions of `DY.Libsignal.Composed`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompRatchet

open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain createChain kdfCk findRecvChain setRecvChain
  recvChainFor consumeMessageKey x25519LowOrder maxReceiverChains)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys HandshakeKeysAt BundleHandles
  BobKeyHandles PreKeyMsgHandles pqxdhKdf serializedIk bobAgreement getKey lookupIdentity
  guardTrace opkUsedB registerIdentity registerCorruptIdentity genSignedPrekey genPQPrekey
  genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK compromiseOPK breakDH breakKEM
  invertDH invertKEM)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg spqrA2B spqrB2A
  receiveSignalMsg ensureReceiverChain dhRatchetStep verifyMacAndDecrypt
  logSkippedKeys logMessageKeyAndStore
  messageEncrypt messageEncryptAbort messageDecrypt messageDecryptSkipped
  exposeKey exposeSpqr exposeSkipped traceLength guardTrace)
open DY.Libsignal.TripleRatchet.Cheval (StateStoredAt)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open Symbolic.Swarm.COMPOSED.CompTrace

/-! ## `InertOnPQXDH` Preservation Combinator -/

theorem handshakeKeysAt_lt_length {tr : ExecTrace} {doneIdx : Nat} {keys : HandshakeKeys}
    (h : HandshakeKeysAt tr doneIdx keys) : doneIdx < tr.length := by
  rcases h with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hev⟩ | ⟨ek, ct, hev⟩⟩
  · exact Trace.EventLoggedAt_implies_i_le_length _ doneIdx tr hev
  · exact Trace.EventLoggedAt_implies_i_le_length _ doneIdx tr hev

theorem handshakeKeysAt_mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {doneIdx : Nat}
    {keys : HandshakeKeys} (h : HandshakeKeysAt tr doneIdx keys) :
    HandshakeKeysAt tr' doneIdx keys := by
  rcases h with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hev⟩ | ⟨ek, ct, hev⟩⟩
  · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct, eventLoggedAt_mono hle hev⟩⟩
  · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inr ⟨ek, ct, eventLoggedAt_mono hle hev⟩⟩

theorem handshakeKeysAt_append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHEntry) = none)
    {doneIdx : Nat} {keys : HandshakeKeys}
    (h : HandshakeKeysAt (tr.append e) doneIdx keys) :
    HandshakeKeysAt tr doneIdx keys := by
  rcases h with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hev⟩ | ⟨ek, ct, hev⟩⟩
  · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct, eventLoggedAt_append_other hnone hev⟩⟩
  · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inr ⟨ek, ct, eventLoggedAt_append_other hnone hev⟩⟩

theorem handshakeKeysAt_append_nonDone {tr : ExecTrace} {ev : PQXDHEvent}
    (hne : ∀ a b ikA ikB spk pqpk opk ek ct keys,
      ev ≠ .AliceDone a b ikA ikB spk pqpk opk ek ct keys ∧
      ev ≠ .BobDone a b ikA ikB spk pqpk opk ek ct keys)
    {doneIdx : Nat} {keys : HandshakeKeys}
    (h : HandshakeKeysAt (tr.append (PQEvE ev)) doneIdx keys) :
    HandshakeKeysAt tr doneIdx keys := by
  rcases h with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hev⟩ | ⟨ek, ct, hev⟩⟩
  · rcases eventLoggedAt_append_same hev with ⟨_, hev⟩ | ⟨_, heq⟩
    · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct, hev⟩⟩
    · exact absurd heq (hne a b ikA ikB spk pqpk opk ek ct keys).1
  · rcases eventLoggedAt_append_same hev with ⟨_, hev⟩ | ⟨_, heq⟩
    · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inr ⟨ek, ct, hev⟩⟩
    · exact absurd heq (hne b a ikB ikA spk pqpk opk ek ct keys).2

theorem handshakeKeysAt_append_done {tr : ExecTrace} {ev : PQXDHEvent}
    {doneIdx : Nat} {keys : HandshakeKeys}
    (h : HandshakeKeysAt (tr.append (PQEvE ev)) doneIdx keys) :
    HandshakeKeysAt tr doneIdx keys ∨
    (doneIdx = tr.length ∧
      ((∃ a b ikA ikB spk pqpk opk ek ct, ev = .AliceDone a b ikA ikB spk pqpk opk ek ct keys) ∨
       (∃ b a ikB ikA spk pqpk opk ek ct, ev = .BobDone b a ikB ikA spk pqpk opk ek ct keys))) := by
  rcases h with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hev⟩ | ⟨ek, ct, hev⟩⟩
  · rcases eventLoggedAt_append_same hev with ⟨_, hev⟩ | ⟨rfl, heq⟩
    · exact .inl ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct, hev⟩⟩
    · exact .inr ⟨rfl, .inl ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, heq⟩⟩
  · rcases eventLoggedAt_append_same hev with ⟨_, hev⟩ | ⟨rfl, heq⟩
    · exact .inl ⟨a, b, ikA, ikB, spk, pqpk, opk, .inr ⟨ek, ct, hev⟩⟩
    · exact .inr ⟨rfl, .inr ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, heq⟩⟩

theorem Preserves.getKey {Inv : ExecTrace → Prop} (p : Participant) (stateIdx : Nat)
    (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves Inv (getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p stateIdx) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

/-- Structure bundling preservation of `Inv` under non-session-ratchet trace entries (`Network`,
`Random`, `PQXDHState`, and non-`AliceDone`/`BobDone` `PQXDHEvent`s). -/
structure InertOnPQXDH (Inv : ExecTrace → Prop) : Prop where
  append_net : ∀ tr m, Inv tr → Inv (tr.append (NetE m))
  append_rnd : ∀ tr n, Inv tr → Inv (tr.append (RndE n))
  append_pqxSt : ∀ tr p st, Inv tr → Inv (tr.append (PQStE p st))
  append_pqxEv_nonDone : ∀ tr (ev : PQXDHEvent),
    (∀ a b ikA ikB spk pqpk opk ek ct keys,
      ev ≠ .AliceDone a b ikA ikB spk pqpk opk ek ct keys ∧
      ev ≠ .BobDone a b ikA ikB spk pqpk opk ek ct keys) →
    Inv tr → Inv (tr.append (PQEvE ev))

namespace InertOnPQXDH

variable {Inv : ExecTrace → Prop} (hI : InertOnPQXDH Inv)

include hI

theorem preserves_sendMessage (m : Bytes) : Preserves Inv (Network.sendMessage m) :=
  fun tr h => hI.append_net tr m h

theorem preserves_genRand (n : Nat) : Preserves Inv (Random.genRand n) :=
  fun tr h => hI.append_rnd tr n h

theorem preserves_storePQX (p : Participant) (st : PQXDHState) :
    Preserves Inv (PersistentLocalState.storeLocalState p st) :=
  fun tr h => hI.append_pqxSt tr p st h

theorem preserves_logPQX_nonDone (ev : PQXDHEvent)
    (hne : ∀ a b ikA ikB spk pqpk opk ek ct keys,
      ev ≠ .AliceDone a b ikA ikB spk pqpk opk ek ct keys ∧
      ev ≠ .BobDone a b ikA ikB spk pqpk opk ek ct keys) :
    Preserves Inv (ProtocolEvent.logEvent ev) :=
  fun tr h => hI.append_pqxEv_nonDone tr ev hne h

theorem preserves_registerIdentity (p : Participant) :
    Preserves Inv (registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (hI.preserves_genRand 32) fun _ => ?_
  refine Preserves.bind (hI.preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  refine Preserves.bind (hI.preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (hI.preserves_sendMessage _) fun _ => ?_
  exact hI.preserves_storePQX p _

theorem preserves_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    Preserves Inv (registerCorruptIdentity p skIdx) := by
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  refine Preserves.bind (hI.preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  exact hI.preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))

theorem preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves Inv (genSignedPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (hI.preserves_genRand 32) fun _ => ?_
  refine Preserves.bind (hI.preserves_genRand 64) fun _ => ?_
  refine Preserves.bind (hI.preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  refine Preserves.bind (hI.preserves_storePQX b _) fun _ => ?_
  refine Preserves.bind (hI.preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (hI.preserves_sendMessage _) fun _ => ?_
  exact Preserves.pure _

theorem preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves Inv (genPQPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (hI.preserves_genRand 64) fun _ => ?_
  refine Preserves.bind (hI.preserves_genRand 64) fun _ => ?_
  refine Preserves.bind (hI.preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  refine Preserves.bind (hI.preserves_storePQX b _) fun _ => ?_
  refine Preserves.bind (hI.preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (hI.preserves_sendMessage _) fun _ => ?_
  exact Preserves.pure _

theorem preserves_genOneTimePrekey (b : Participant) :
    Preserves Inv (genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine Preserves.bind (hI.preserves_genRand 32) fun _ => ?_
  refine Preserves.bind (hI.preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  refine Preserves.bind (hI.preserves_storePQX b _) fun _ => ?_
  refine Preserves.bind (hI.preserves_sendMessage _) fun _ => ?_
  exact Preserves.pure _

theorem preserves_compromiseIK (p : Participant) (stateIdx : Nat) :
    Preserves Inv (compromiseIK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (hI.preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  exact hI.preserves_sendMessage _

theorem preserves_compromiseSPK (b : Participant) (stateIdx : Nat) :
    Preserves Inv (compromiseSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (hI.preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  exact hI.preserves_sendMessage _

theorem preserves_compromisePQSPK (b : Participant) (stateIdx : Nat) :
    Preserves Inv (compromisePQSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (hI.preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  exact hI.preserves_sendMessage _

theorem preserves_compromiseOPK (b : Participant) (stateIdx : Nat) :
    Preserves Inv (compromiseOPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (hI.preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  exact hI.preserves_sendMessage _

theorem preserves_breakDH : Preserves Inv breakDH :=
  hI.preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))

theorem preserves_breakKEM : Preserves Inv breakKEM :=
  hI.preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))

theorem preserves_invertDH (pkIdx : Nat) : Preserves Inv (invertDH pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  split
  · exact hI.preserves_sendMessage _
  · exact Preserves.failure

theorem preserves_invertKEM (pkIdx : Nat) : Preserves Inv (invertKEM pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  refine Preserves.bind (Preserves.monadLiftErr _) fun _ => ?_
  exact hI.preserves_sendMessage _

theorem preserves_messageEncryptAbort (me : Participant) (stH : Nat) :
    Preserves Inv (messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  refine Preserves.bind (Preserves.getLocalState_tr _ _) fun _ => ?_
  exact Preserves.bind (hI.preserves_genRand 32) fun _ => Preserves.failure

theorem reachable_induction
    (hBase : Inv Trace.nil)
    (hAliceStart : ∀ a b idStateIdx regIdxB bh, Preserves Inv (aliceStart a b idStateIdx regIdxB bh))
    (hBobStart : ∀ b a kh regIdxA mh pqIdx spqrMsgIdx,
      Preserves Inv (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx))
    (hMsgEnc : ∀ me stH coinsLen pqIdx, Preserves Inv (messageEncrypt me stH coinsLen pqIdx))
    (hMsgDec : ∀ me stH msgH pqIdx spqrMsgIdx,
      Preserves Inv (messageDecrypt me stH msgH pqIdx spqrMsgIdx))
    (hMsgDecSkip : ∀ me stH msgH evH pqIdx spqrMsgIdx,
      Preserves Inv (messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx))
    (hExpKey : ∀ me stH k, Preserves Inv (exposeKey me stH k))
    (hExpSpqr : ∀ me stH, Preserves Inv (exposeSpqr me stH))
    (hExpSkip : ∀ evH, Preserves Inv (exposeSkipped evH))
    {tr : ExecTrace} (hReach : tr.Reachable DY.Libsignal.Composed.reachability) :
    Inv tr :=
  composed_reachable_induction hBase
    (fun msg t _ hInv => hI.append_net t msg hInv)
    hI.preserves_registerIdentity
    hI.preserves_registerCorruptIdentity
    hI.preserves_genSignedPrekey
    hI.preserves_genPQPrekey
    hI.preserves_genOneTimePrekey
    hAliceStart
    hBobStart
    hMsgEnc
    hI.preserves_messageEncryptAbort
    hMsgDec
    hMsgDecSkip
    hExpKey
    hExpSpqr
    hExpSkip
    hI.preserves_compromiseIK
    hI.preserves_compromiseSPK
    hI.preserves_compromisePQSPK
    hI.preserves_compromiseOPK
    hI.preserves_breakDH
    hI.preserves_breakKEM
    hI.preserves_invertDH
    hI.preserves_invertKEM
    hReach

end InertOnPQXDH

/-! ## Session Origin and Receiver-Chain Lineage -/

/-- Session `s` on `tr` was started by a PQXDH handshake at `doneIdx` (`ComposedEvent.HandshakeSession s doneIdx`)
with `HandshakeKeysAt tr doneIdx keys`. -/
def CompSessionOrigin (tr : ExecTrace) (s : SessionInfo) : Prop :=
  ∃ doneIdx keys,
    tr.EventLogged (ComposedEvent.HandshakeSession s doneIdx) ∧
    HandshakeKeysAt tr doneIdx keys

theorem CompSessionOrigin.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {s : SessionInfo}
    (h : CompSessionOrigin tr s) : CompSessionOrigin tr' s := by
  obtain ⟨doneIdx, keys, hsess, hhk⟩ := h
  exact ⟨doneIdx, keys, eventLogged_mono hle hsess, handshakeKeysAt_mono hle hhk⟩

/-- A receiver chain `(pk, i)` of session `s` is held by some stored snapshot of `s.me` on `tr`,
with `1 ≤ i`. -/
def ChainHeldOnTrace (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (i : Nat) : Prop :=
  1 ≤ i ∧ ∃ st j, StateStoredAt s.me st j tr ∧ st.sessionInfo s.me = s ∧
    ∃ c ∈ st.recv, c.ratchetKey = pk ∧ c.rIdx = i

theorem ChainHeldOnTrace.mono {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {s : SessionInfo} {pk : Bytes} {i : Nat} (h : ChainHeldOnTrace tr s pk i) :
    ChainHeldOnTrace tr' s pk i := by
  obtain ⟨hi, st, j, hst, hs, c, hc, hpk, hr⟩ := h
  exact ⟨hi, st, j, trStateStoredAt_mono hle hst, hs, c, hc, hpk, hr⟩

/-- Reachable-trace invariant bundling PQXDH KDF shape, stored `TRState` `rIdx ≥ 1` and session
origins, `ExposedRK` root-key structure, `HonestDH` randomness, `SkippedKeyStored` receiver chains,
and `MessageKey` session origins. -/
structure CompSessionOriginInv (tr : ExecTrace) : Prop where
  handshakeKdf : ∀ doneIdx keys, HandshakeKeysAt tr doneIdx keys → ∃ ikm, keys = pqxdhKdf ikm
  storedOK : ∀ p st j, StateStoredAt p st j tr →
    1 ≤ st.rIdx ∧ (∃ r₀ p₀ s₀, st.rk = (createChain r₀ p₀ s₀).1) ∧
    CompSessionOrigin tr (st.sessionInfo p) ∧ (∀ c ∈ st.recv, 1 ≤ c.rIdx)
  exposedRK : ∀ s rk r, tr.EventLogged (TREvent.ExposedRK s rk r) →
    1 ≤ r ∧ ∃ r₀ p₀ s₀, rk = (createChain r₀ p₀ s₀).1
  honestDH : ∀ s dhs rIdx, tr.EventLogged (TREvent.HonestDH s dhs rIdx) →
    ∃ t < tr.length, dhs = mkRand t 32
  skippedOK : ∀ s pk n seed i src,
    tr.EventLogged (TREvent.SkippedKeyStored s pk n seed i src) →
    ChainHeldOnTrace tr s pk i ∧ CompSessionOrigin tr s
  mkSession : ∀ s dir seed pqSalt n i par,
    tr.EventLogged (TREvent.MessageKey s dir seed pqSalt n i par) →
    CompSessionOrigin tr s

theorem CompSessionOriginInv.nil : CompSessionOriginInv Trace.nil where
  handshakeKdf _ _ h := by
    rcases h with ⟨_, _, _, _, _, _, _, ⟨_, _, hev⟩ | ⟨_, _, hev⟩⟩ <;> cases hev
  storedOK _ _ _ hst := by cases hst
  exposedRK _ _ _ h := by obtain ⟨_, hev⟩ := h; cases hev
  honestDH _ _ _ h := by obtain ⟨_, hev⟩ := h; cases hev
  skippedOK _ _ _ _ _ _ h := by obtain ⟨_, hev⟩ := h; cases hev
  mkSession _ _ _ _ _ _ _ h := by obtain ⟨_, hev⟩ := h; cases hev

theorem CompSessionOriginInv.append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone_pq : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHEntry) = none)
    (hnone_tr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    (h : CompSessionOriginInv tr) : CompSessionOriginInv (tr.append e) := by
  have hle : tr ≤ tr.append e := Trace.append_le tr e
  have hlen : tr.length < (tr.append e).length := by simp [Trace.append, Trace.length]
  refine ⟨fun doneIdx keys hhk => h.handshakeKdf doneIdx keys (handshakeKeysAt_append_other hnone_pq hhk),
    fun p st j hst => ?_,
    fun s rk r ⟨k, hk⟩ => h.exposedRK s rk r ⟨k, eventLoggedAt_append_other hnone_tr hk⟩,
    fun s dhs rIdx ⟨k, hk⟩ => ?_,
    fun s pk n seed i src ⟨k, hk⟩ => ?_,
    fun s dir seed pqSalt n i par ⟨k, hk⟩ => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.storedOK p st j (trStateStoredAt_append_other hnone_st hst)
    exact ⟨h1, h2, h3.mono hle, h4⟩
  · obtain ⟨t, ht, hdhs⟩ := h.honestDH s dhs rIdx ⟨k, eventLoggedAt_append_other hnone_tr hk⟩
    exact ⟨t, by omega, hdhs⟩
  · obtain ⟨hc, hs⟩ := h.skippedOK s pk n seed i src ⟨k, eventLoggedAt_append_other hnone_tr hk⟩
    exact ⟨hc.mono hle, hs.mono hle⟩
  · exact (h.mkSession s dir seed pqSalt n i par
      ⟨k, eventLoggedAt_append_other hnone_tr hk⟩).mono hle

theorem CompSessionOriginInv.append_pqx_done {tr : ExecTrace} {ev : PQXDHEvent}
    (hdone : ∀ doneIdx keys,
      HandshakeKeysAt (tr.append (PQEvE ev)) doneIdx keys →
      HandshakeKeysAt tr doneIdx keys ∨ ∃ ikm, keys = pqxdhKdf ikm)
    (h : CompSessionOriginInv tr) : CompSessionOriginInv (tr.append (PQEvE ev)) := by
  have hle : tr ≤ tr.append (PQEvE ev) := Trace.append_le tr _
  have hlen : tr.length < (tr.append (PQEvE ev)).length := by simp [Trace.append, Trace.length]
  refine ⟨fun doneIdx keys hhk => ?_,
    fun p st j hst => ?_,
    fun s rk r ⟨k, hk⟩ => h.exposedRK s rk r ⟨k, eventLoggedAt_append_other rfl hk⟩,
    fun s dhs rIdx ⟨k, hk⟩ => ?_,
    fun s pk n seed i src ⟨k, hk⟩ => ?_,
    fun s dir seed pqSalt n i par ⟨k, hk⟩ => ?_⟩
  · rcases hdone doneIdx keys hhk with hhk' | hikm
    · exact h.handshakeKdf doneIdx keys hhk'
    · exact hikm
  · obtain ⟨h1, h2, h3, h4⟩ := h.storedOK p st j (trStateStoredAt_append_other rfl hst)
    exact ⟨h1, h2, h3.mono hle, h4⟩
  · obtain ⟨t, ht, hdhs⟩ := h.honestDH s dhs rIdx ⟨k, eventLoggedAt_append_other rfl hk⟩
    exact ⟨t, by omega, hdhs⟩
  · obtain ⟨hc, hs⟩ := h.skippedOK s pk n seed i src ⟨k, eventLoggedAt_append_other rfl hk⟩
    exact ⟨hc.mono hle, hs.mono hle⟩
  · exact (h.mkSession s dir seed pqSalt n i par
      ⟨k, eventLoggedAt_append_other rfl hk⟩).mono hle

theorem CompSessionOriginInv.append_pqx_nonDone {tr : ExecTrace} {ev : PQXDHEvent}
    (hne : ∀ a b ikA ikB spk pqpk opk ek ct keys,
      ev ≠ .AliceDone a b ikA ikB spk pqpk opk ek ct keys ∧
      ev ≠ .BobDone a b ikA ikB spk pqpk opk ek ct keys)
    (h : CompSessionOriginInv tr) : CompSessionOriginInv (tr.append (PQEvE ev)) :=
  h.append_pqx_done fun _ _ hhk => .inl (handshakeKeysAt_append_nonDone hne hhk)

theorem CompSessionOriginInv.inertOnPQXDH : InertOnPQXDH CompSessionOriginInv where
  append_net _ _ h := h.append_other rfl rfl rfl
  append_rnd _ _ h := h.append_other rfl rfl rfl
  append_pqxSt _ _ _ h := h.append_other rfl rfl rfl
  append_pqxEv_nonDone _ _ hne h := h.append_pqx_nonDone hne

theorem CompSessionOriginInv.append_trEv {tr : ExecTrace} {ev : TREvent}
    (hrk : ∀ s rk r, ev = .ExposedRK s rk r → 1 ≤ r ∧ ∃ r₀ p₀ s₀, rk = (createChain r₀ p₀ s₀).1)
    (hdh : ∀ s dhs rIdx, ev = .HonestDH s dhs rIdx → ∃ t < tr.length, dhs = mkRand t 32)
    (hsk : ∀ s pk n seed i src, ev = .SkippedKeyStored s pk n seed i src →
      ChainHeldOnTrace tr s pk i ∧ CompSessionOrigin tr s)
    (hmk : ∀ s dir seed pqSalt n i par,
      ev = .MessageKey s dir seed pqSalt n i par →
      CompSessionOrigin tr s)
    (h : CompSessionOriginInv tr) : CompSessionOriginInv (tr.append (TREvE ev)) := by
  have hle : tr ≤ tr.append (TREvE ev) := Trace.append_le tr _
  have hlen : tr.length < (tr.append (TREvE ev)).length := by simp [Trace.append, Trace.length]
  refine ⟨fun doneIdx keys hhk => h.handshakeKdf doneIdx keys (handshakeKeysAt_append_other rfl hhk),
    fun p st j hst => ?_,
    fun s rk r ⟨k, hk⟩ => ?_,
    fun s dhs rIdx ⟨k, hk⟩ => ?_,
    fun s pk n seed i src ⟨k, hk⟩ => ?_,
    fun s dir seed pqSalt n i par ⟨k, hk⟩ => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.storedOK p st j (trStateStoredAt_append_other rfl hst)
    exact ⟨h1, h2, h3.mono hle, h4⟩
  · rcases eventLoggedAt_append_same hk with ⟨_, hk⟩ | ⟨_, heq⟩
    · exact h.exposedRK s rk r ⟨k, hk⟩
    · exact hrk s rk r heq
  · rcases eventLoggedAt_append_same hk with ⟨_, hk⟩ | ⟨_, heq⟩
    · obtain ⟨t, ht, hdhs⟩ := h.honestDH s dhs rIdx ⟨k, hk⟩
      exact ⟨t, by omega, hdhs⟩
    · obtain ⟨t, ht, hdhs⟩ := hdh s dhs rIdx heq
      exact ⟨t, by omega, hdhs⟩
  · rcases eventLoggedAt_append_same hk with ⟨_, hk⟩ | ⟨_, heq⟩
    · obtain ⟨hc, hs⟩ := h.skippedOK s pk n seed i src ⟨k, hk⟩
      exact ⟨hc.mono hle, hs.mono hle⟩
    · obtain ⟨hc, hs⟩ := hsk s pk n seed i src heq
      exact ⟨hc.mono hle, hs.mono hle⟩
  · rcases eventLoggedAt_append_same hk with ⟨_, hk⟩ | ⟨_, heq⟩
    · exact (h.mkSession s dir seed pqSalt n i par ⟨k, hk⟩).mono hle
    · exact (hmk s dir seed pqSalt n i par heq).mono hle

theorem CompSessionOriginInv.append_tr_inert {tr : ExecTrace} {ev : TREvent}
    (hne_rk : ∀ s rk r, ev ≠ .ExposedRK s rk r)
    (hne_dh : ∀ s dhs rIdx, ev ≠ .HonestDH s dhs rIdx)
    (hne_sk : ∀ s pk n seed i src, ev ≠ .SkippedKeyStored s pk n seed i src)
    (hne_mk : ∀ s dir seed pqSalt n i par,
      ev ≠ .MessageKey s dir seed pqSalt n i par)
    (h : CompSessionOriginInv tr) : CompSessionOriginInv (tr.append (TREvE ev)) :=
  h.append_trEv (fun s rk r he => absurd he (hne_rk s rk r))
    (fun s dhs r he => absurd he (hne_dh s dhs r))
    (fun s pk n seed i src he => absurd he (hne_sk s pk n seed i src))
    (fun s dir seed pqSalt n i par he =>
      absurd he (hne_mk s dir seed pqSalt n i par))

theorem CompSessionOriginInv.append_honestDH {tr : ExecTrace} {s₀ : SessionInfo} {dhs₀ : Bytes}
    {r₀ : Nat} (hdhs₀ : ∃ t < tr.length, dhs₀ = mkRand t 32)
    (h : CompSessionOriginInv tr) :
    CompSessionOriginInv (tr.append (TREvE (.HonestDH s₀ dhs₀ r₀))) :=
  h.append_trEv (fun _ _ _ he => by cases he)
    (fun _ _ _ he => by cases he; exact hdhs₀)
    (fun _ _ _ _ _ _ he => by cases he) (fun _ _ _ _ _ _ _ he => by cases he)

theorem CompSessionOriginInv.append_exposedRK {tr : ExecTrace} {s₀ : SessionInfo} {rk₀ : Bytes}
    {r₀ : Nat} (hrk₀ : 1 ≤ r₀ ∧ ∃ a b c, rk₀ = (createChain a b c).1)
    (h : CompSessionOriginInv tr) :
    CompSessionOriginInv (tr.append (TREvE (.ExposedRK s₀ rk₀ r₀))) :=
  h.append_trEv (fun _ _ _ he => by cases he; exact hrk₀)
    (fun _ _ _ he => by cases he) (fun _ _ _ _ _ _ he => by cases he)
    (fun _ _ _ _ _ _ _ he => by cases he)

theorem CompSessionOriginInv.append_storeTR {tr : ExecTrace} {p₀ : Participant} {st₀ : TRState}
    (hrIdx : 1 ≤ st₀.rIdx)
    (hrk : ∃ r₀ p₀ s₀, st₀.rk = (createChain r₀ p₀ s₀).1)
    (hsess : CompSessionOrigin tr (st₀.sessionInfo p₀))
    (hrecv : ∀ c ∈ st₀.recv, 1 ≤ c.rIdx)
    (h : CompSessionOriginInv tr) :
    CompSessionOriginInv (tr.append (TRStE p₀ st₀)) := by
  have hle : tr ≤ tr.append (TRStE p₀ st₀) := Trace.append_le tr _
  have hlen : tr.length < (tr.append (TRStE p₀ st₀)).length := by simp [Trace.append, Trace.length]
  refine ⟨fun doneIdx keys hhk => h.handshakeKdf doneIdx keys (handshakeKeysAt_append_other rfl hhk),
    fun p st j hst => ?_,
    fun s rk r ⟨k, hk⟩ => h.exposedRK s rk r ⟨k, eventLoggedAt_append_other rfl hk⟩,
    fun s dhs rIdx ⟨k, hk⟩ => ?_,
    fun s pk n seed i src ⟨k, hk⟩ => ?_,
    fun s dir seed pqSalt n i par ⟨k, hk⟩ => ?_⟩
  · rcases trStateStoredAt_append_same hst with ⟨_, hst⟩ | ⟨_, rfl, rfl⟩
    · obtain ⟨h1, h2, h3, h4⟩ := h.storedOK p st j hst
      exact ⟨h1, h2, h3.mono hle, h4⟩
    · exact ⟨hrIdx, hrk, hsess.mono hle, hrecv⟩
  · obtain ⟨t, ht, hdhs⟩ := h.honestDH s dhs rIdx ⟨k, eventLoggedAt_append_other rfl hk⟩
    exact ⟨t, by omega, hdhs⟩
  · obtain ⟨hc, hs⟩ := h.skippedOK s pk n seed i src ⟨k, eventLoggedAt_append_other rfl hk⟩
    exact ⟨hc.mono hle, hs.mono hle⟩
  · exact (h.mkSession s dir seed pqSalt n i par
      ⟨k, eventLoggedAt_append_other rfl hk⟩).mono hle

theorem CompSessionOriginInv.append_sendMK {tr : ExecTrace}
    {s₀ : SessionInfo} {seed₀ pqSalt₀ : Bytes} {n₀ : UInt32} {i₀ par₀ : Nat}
    (hsess : CompSessionOrigin tr s₀)
    (h : CompSessionOriginInv tr) :
    CompSessionOriginInv
      (tr.append (TREvE (.MessageKey s₀ .sender seed₀ pqSalt₀ n₀ i₀ par₀))) :=
  h.append_trEv (fun _ _ _ he => by cases he) (fun _ _ _ he => by cases he)
    (fun _ _ _ _ _ _ he => by cases he)
    (fun _ _ _ _ _ _ _ he => by cases he; exact hsess)

theorem CompSessionOriginInv.append_recvMK {tr : ExecTrace}
    {s₀ : SessionInfo} {seed₀ pqSalt₀ : Bytes} {n₀ : UInt32} {i₀ par₀ : Nat}
    (hsess : CompSessionOrigin tr s₀)
    (h : CompSessionOriginInv tr) :
    CompSessionOriginInv
      (tr.append (TREvE (.MessageKey s₀ .receiver seed₀ pqSalt₀ n₀ i₀ par₀))) :=
  h.append_trEv (fun _ _ _ he => by cases he) (fun _ _ _ he => by cases he)
    (fun _ _ _ _ _ _ he => by cases he)
    (fun _ _ _ _ _ _ _ he => by cases he; exact hsess)

private theorem mem_drop_append_singleton {α : Type} :
    ∀ (L : List α) (c : α) (k : Nat), k ≤ L.length → c ∈ (L ++ [c]).drop k
  | [], c, 0, _ => List.mem_singleton_self c
  | [], _, _ + 1, hk => by simp at hk
  | a :: L, c, 0, _ => List.mem_cons_of_mem a (List.mem_append_right L (List.mem_singleton_self c))
  | _ :: L, c, k + 1, hk => mem_drop_append_singleton L c k (by simp at hk; omega)

private theorem findRecvChain_some {recv : List RecvChain} {pk : Bytes} {c : RecvChain}
    (h : findRecvChain recv pk = some c) : c ∈ recv ∧ c.ratchetKey = pk := by
  unfold DY.Libsignal.TripleRatchet.findRecvChain at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

private theorem consumeMessageKey_some {c c' : RecvChain} {counter : UInt32} {seed : Bytes}
    (h : consumeMessageKey c counter = some (seed, c')) :
    c'.ratchetKey = c.ratchetKey ∧ c'.rIdx = c.rIdx := by
  unfold DY.Libsignal.TripleRatchet.consumeMessageKey at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; exact ⟨rfl, rfl⟩

private theorem mem_setRecvChain {recv : List RecvChain} {c c' : RecvChain}
    (hc : c ∈ recv) (hpk : c'.ratchetKey = c.ratchetKey) :
    c' ∈ setRecvChain recv c' := by
  unfold DY.Libsignal.TripleRatchet.setRecvChain
  rw [List.mem_map]
  exact ⟨c, hc, by simp [hpk]⟩

private theorem pos_setRecvChain {recv : List RecvChain} {c' : RecvChain}
    (hrecv : ∀ c ∈ recv, 1 ≤ c.rIdx) (hc' : 1 ≤ c'.rIdx) :
    ∀ x ∈ setRecvChain recv c', 1 ≤ x.rIdx := by
  intro x hx
  unfold DY.Libsignal.TripleRatchet.setRecvChain at hx
  rw [List.mem_map] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  split
  · exact hc'
  · exact hrecv c hc

private def OnlySkippedFor (s : SessionInfo) (pk : Bytes) (rIdx : Nat) (t t' : ExecTrace) : Prop :=
  t ≤ t' ∧ t.length ≤ t'.length ∧ ∀ i (h : i < t'.length), t.length ≤ i →
    (TraceEntryHas.proj (t'.at i h) : Option PQXDHEntry) = none ∧
    (TraceEntryHas.proj (t'.at i h) : Option TRStEntry) = none ∧
    ∀ e : TREntry, TraceEntryHas.proj (t'.at i h) = some e →
      (∀ s' rk' r', e.ev ≠ .ExposedRK s' rk' r') ∧
      (∀ s' dhs' r', e.ev ≠ .HonestDH s' dhs' r') ∧
      (∀ s' pk' n' seed' r' src', e.ev = .SkippedKeyStored s' pk' n' seed' r' src' →
        s' = s ∧ pk' = pk ∧ r' = rIdx) ∧
      (∀ s' dir' seed' pqSalt' n' r' par',
        e.ev = .MessageKey s' dir' seed' pqSalt' n' r' par' →
        s' = s ∧ dir' = .receiver ∧ r' = rIdx)

private theorem OnlySkippedFor.refl (s : SessionInfo) (pk : Bytes) (rIdx : Nat) (t : ExecTrace) :
    OnlySkippedFor s pk rIdx t t :=
  ⟨Trace.le_refl t, Nat.le_refl _, fun _ h hi => by omega⟩

private theorem OnlySkippedFor.trans {s : SessionInfo} {pk : Bytes} {rIdx : Nat}
    {t t1 t2 : ExecTrace} (a : OnlySkippedFor s pk rIdx t t1)
    (b : OnlySkippedFor s pk rIdx t1 t2) : OnlySkippedFor s pk rIdx t t2 := by
  refine ⟨Trace.le_trans _ _ _ a.1 b.1, Nat.le_trans a.2.1 b.2.1, fun i h hi => ?_⟩
  by_cases hl : i < t1.length
  · rw [← Trace.at_le t1 t2 i hl b.1]; exact a.2.2 i hl hi
  · exact b.2.2 i h (by omega)

private theorem OnlySkippedFor.append_tr (s : SessionInfo) (pk : Bytes) (rIdx : Nat)
    (t : ExecTrace) (ev : TREvent)
    (hrk : ∀ s' rk' r', ev ≠ .ExposedRK s' rk' r')
    (hdh : ∀ s' dhs' r', ev ≠ .HonestDH s' dhs' r')
    (hsk : ∀ s' pk' n' seed' r' src', ev = .SkippedKeyStored s' pk' n' seed' r' src' →
      s' = s ∧ pk' = pk ∧ r' = rIdx)
    (hmk : ∀ s' dir' seed' pqSalt' n' r' par',
      ev = .MessageKey s' dir' seed' pqSalt' n' r' par' →
      s' = s ∧ dir' = .receiver ∧ r' = rIdx) :
    OnlySkippedFor s pk rIdx t (t.append (TREvE ev)) := by
  refine ⟨Trace.append_le _ _, by simp [Trace.append, Trace.length], fun i h hi => ?_⟩
  have : i = t.length := by simp [Trace.append, Trace.length] at h; omega
  subst this
  simp only [Trace.append, Trace.at, ↓reduceDIte]
  refine ⟨rfl, rfl, fun ⟨ev'⟩ he => ?_⟩
  rw [TraceEntryHas.inj_proj_eq] at he
  rcases he with ⟨⟩
  exact ⟨hrk, hdh, hsk, hmk⟩

private theorem logSkippedKeys_onlySkippedFor (s : SessionInfo) (pk : Bytes)
    (rIdx sourceStateIdx : Nat) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat) (t : ExecTrace),
      OnlySkippedFor s pk rIdx t ((logSkippedKeys s pk rIdx sourceStateIdx ck n k).run t).2.val
  | _, _, 0, t => OnlySkippedFor.refl s pk rIdx t
  | ck, n, k + 1, t => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [Traceful.run_bind]
    have h1 : OnlySkippedFor s pk rIdx t
        (t.append (TREvE (.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx))) :=
      OnlySkippedFor.append_tr s pk rIdx t _
        (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h)
        (by intro _ _ _ _ _ _ h; injection h with h1 h2 _ _ h3 _; exact ⟨h1.symm, h2.symm, h3.symm⟩)
        (by intro _ _ _ _ _ _ _ h; cases h)
    exact OnlySkippedFor.trans h1
      (logSkippedKeys_onlySkippedFor s pk rIdx sourceStateIdx _ _ k _)

private theorem logSkippedKeys_fst (s : SessionInfo) (pk : Bytes) (rIdx sourceStateIdx : Nat) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat) (t : ExecTrace),
      ((logSkippedKeys s pk rIdx sourceStateIdx ck n k).run t).1 = some ()
  | _, _, 0, _ => rfl
  | ck, n, k + 1, t => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [run_bind_fst]
    exact logSkippedKeys_fst s pk rIdx sourceStateIdx (kdfCk ck).1 (n + 1) k _

private theorem CompSessionOriginInv.of_onlySkippedFor {s : SessionInfo} {pk : Bytes} {rIdx : Nat}
    {t t1 : ExecTrace} {me : Participant} {stOut : TRState}
    (hInv : CompSessionOriginInv t) (hos : OnlySkippedFor s pk rIdx t t1)
    (hme : s.me = me) (hs : stOut.sessionInfo me = s) (hrIdx : 1 ≤ rIdx)
    (hst_rIdx : 1 ≤ stOut.rIdx)
    (hst_rk : ∃ r₀ p₀ s₀, stOut.rk = (createChain r₀ p₀ s₀).1)
    (hsess : CompSessionOrigin t s)
    (hchain : ∃ c ∈ stOut.recv, c.ratchetKey = pk ∧ c.rIdx = rIdx)
    (hpos : ∀ x ∈ stOut.recv, 1 ≤ x.rIdx) :
    CompSessionOriginInv (t1.append (TRStE me stOut)) := by
  have hheld : ChainHeldOnTrace (t1.append (TRStE me stOut)) s pk rIdx := by
    obtain ⟨c, hc, hpk, hr⟩ := hchain
    refine ⟨hrIdx, stOut, t1.length, ?_, hme ▸ hs, c, hc, hpk, hr⟩
    unfold StateStoredAt; rw [hme]; exact Trace.at?_append t1 (TRStE me stOut)
  have hle : t ≤ t1.append (TRStE me stOut) := Trace.le_trans _ _ _ hos.1 (Trace.append_le _ _)
  have hsess' : CompSessionOrigin (t1.append (TRStE me stOut)) s := hsess.mono hle
  have hlen : t.length < (t1.append (TRStE me stOut)).length := by
    have := hos.2.1; simp [Trace.append, Trace.length]; omega
  refine ⟨fun doneIdx keys hhk => ?_,
    fun p st j hst => ?_,
    fun s' rk' r' ⟨k, hk⟩ => ?_,
    fun s' dhs' r' ⟨k, hk⟩ => ?_,
    fun s' pk' n' seed' r' src' ⟨k, hk⟩ => ?_,
    fun s' dir' seed' pqSalt' n' r' par' ⟨k, hk⟩ => ?_⟩
  · have hhk1 := handshakeKeysAt_append_other rfl hhk
    have hj_lt : doneIdx < t1.length := handshakeKeysAt_lt_length hhk1
    by_cases hjt : doneIdx < t.length
    · have hhk_t : HandshakeKeysAt t doneIdx keys := by
        rcases hhk1 with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hev⟩ | ⟨ek, ct, hev⟩⟩
        · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct,
            Trace.EventLoggedAt_le' _ doneIdx t t1 hjt hos.1 hev⟩⟩
        · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inr ⟨ek, ct,
            Trace.EventLoggedAt_le' _ doneIdx t t1 hjt hos.1 hev⟩⟩
      exact hInv.handshakeKdf doneIdx keys hhk_t
    · rcases hhk1 with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hev⟩ | ⟨ek, ct, hev⟩⟩ <;> {
        unfold Trace.EventLoggedAt Trace.at? at hev
        simp only [hj_lt, ↓reduceDIte] at hev
        rw [(hos.2.2 doneIdx hj_lt (by omega)).1] at hev; cases hev }
  · rcases trStateStoredAt_append_same hst with ⟨hj1, hst1⟩ | ⟨_, rfl, rfl⟩
    · by_cases hjt : j < t.length
      · have hst_t : StateStoredAt p st j t := by
          unfold TRStateStoredAt at hst1
          change ((t.at? j : Option TRStEntry) = some ⟨⟨p, st⟩⟩)
          simp only [Trace.at?, hj1, hjt, ↓reduceDIte] at hst1 ⊢
          rw [Trace.at_le t t1 j hjt hos.1]; exact hst1
        obtain ⟨h1, h2, h3, h4⟩ := hInv.storedOK p st j hst_t
        exact ⟨h1, h2, h3.mono hle, h4⟩
      · unfold TRStateStoredAt Trace.at? at hst1
        simp only [hj1, ↓reduceDIte] at hst1
        rw [(hos.2.2 j hj1 (by omega)).2.1] at hst1; cases hst1
    · exact ⟨hst_rIdx, hst_rk, hs ▸ hsess', hpos⟩
  · have hk1 := eventLoggedAt_append_other rfl hk
    have hk_lt : k < t1.length := Trace.EventLoggedAt_implies_i_le_length _ k t1 hk1
    by_cases hkt : k < t.length
    · exact hInv.exposedRK s' rk' r' ⟨k, Trace.EventLoggedAt_le' _ k t t1 hkt hos.1 hk1⟩
    · unfold Trace.EventLoggedAt Trace.at? at hk1; simp only [hk_lt, ↓reduceDIte] at hk1
      exact absurd rfl (((hos.2.2 k hk_lt (by omega)).2.2 _ hk1).1 s' rk' r')
  · have hk1 := eventLoggedAt_append_other rfl hk
    have hk_lt : k < t1.length := Trace.EventLoggedAt_implies_i_le_length _ k t1 hk1
    by_cases hkt : k < t.length
    · obtain ⟨t₀, ht₀, hdhs₀⟩ :=
        hInv.honestDH s' dhs' r' ⟨k, Trace.EventLoggedAt_le' _ k t t1 hkt hos.1 hk1⟩
      exact ⟨t₀, by omega, hdhs₀⟩
    · unfold Trace.EventLoggedAt Trace.at? at hk1; simp only [hk_lt, ↓reduceDIte] at hk1
      exact absurd rfl (((hos.2.2 k hk_lt (by omega)).2.2 _ hk1).2.1 s' dhs' r')
  · have hk1 := eventLoggedAt_append_other rfl hk
    have hk_lt : k < t1.length := Trace.EventLoggedAt_implies_i_le_length _ k t1 hk1
    by_cases hkt : k < t.length
    · obtain ⟨hc, hs'⟩ :=
        hInv.skippedOK s' pk' n' seed' r' src' ⟨k, Trace.EventLoggedAt_le' _ k t t1 hkt hos.1 hk1⟩
      exact ⟨hc.mono hle, hs'.mono hle⟩
    · unfold Trace.EventLoggedAt Trace.at? at hk1; simp only [hk_lt, ↓reduceDIte] at hk1
      obtain ⟨rfl, rfl, rfl⟩ :=
        ((hos.2.2 k hk_lt (by omega)).2.2 _ hk1).2.2.1 s' pk' n' seed' r' src' rfl
      exact ⟨hheld, hsess'⟩
  · have hk1 := eventLoggedAt_append_other rfl hk
    have hk_lt : k < t1.length := Trace.EventLoggedAt_implies_i_le_length _ k t1 hk1
    by_cases hkt : k < t.length
    · exact (hInv.mkSession s' dir' seed' pqSalt' n' r' par'
          ⟨k, Trace.EventLoggedAt_le' _ k t t1 hkt hos.1 hk1⟩).mono hle
    · unfold Trace.EventLoggedAt Trace.at? at hk1; simp only [hk_lt, ↓reduceDIte] at hk1
      obtain ⟨rfl, rfl, rfl⟩ :=
        ((hos.2.2 k hk_lt (by omega)).2.2 _ hk1).2.2.2 s' dir' seed' pqSalt' n' r' par' rfl
      exact hsess'

private theorem CompSessionOriginInv.decryptTail (me : Participant) (_origIdx parIdx : Nat)
    (st : TRState) (msg : TRSignalMsg) (c c' : RecvChain) (seed pqSalt m spqr' : Bytes)
    (hc_mem : c ∈ st.recv) (hc_pk : c.ratchetKey = msg.ratchetKey)
    (hc_pos : 1 ≤ c.rIdx) (hpos_st : ∀ x ∈ st.recv, 1 ≤ x.rIdx)
    (hc'_pk : c'.ratchetKey = c.ratchetKey) (hc'_rIdx : c'.rIdx = c.rIdx)
    (hst_rIdx : 1 ≤ st.rIdx) (hst_rk : ∃ r₀ p₀ s₀, st.rk = (createChain r₀ p₀ s₀).1)
    (tr5 : ExecTrace) (hInv5 : CompSessionOriginInv tr5)
    (hsess5 : CompSessionOrigin tr5 (st.sessionInfo me)) :
    CompSessionOriginInv ((do
      logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx parIdx c.chainKey c.index
        (msg.counter.toNat - c.index.toNat)
      ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
      logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx parIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr5).2.val := by
  rw [Traceful.run_bind]
  have hfst := logSkippedKeys_fst (st.sessionInfo me) msg.ratchetKey c.rIdx parIdx c.chainKey c.index
    (msg.counter.toNat - c.index.toNat) tr5
  have hos6 := logSkippedKeys_onlySkippedFor (st.sessionInfo me) msg.ratchetKey c.rIdx parIdx c.chainKey
    c.index (msg.counter.toNat - c.index.toNat) tr5
  rcases h6 : (logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx parIdx c.chainKey c.index
      (msg.counter.toNat - c.index.toNat)).run tr5 with ⟨o6, tr6, _⟩
  rw [h6] at hfst hos6; cases hfst
  dsimp only at hos6 ⊢
  have hos7 : OnlySkippedFor (st.sessionInfo me) msg.ratchetKey c.rIdx tr5
      (tr6.append (TREvE (.Received me st.peer msg.ratchetKey msg.counter m))) :=
    hos6.trans (OnlySkippedFor.append_tr _ _ _ tr6 _
      (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h)
      (by intro _ _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ _ _ h; cases h))
  let tr7 := tr6.append (TREvE (.Received me st.peer msg.ratchetKey msg.counter m))
  have hos8 : OnlySkippedFor (st.sessionInfo me) msg.ratchetKey c.rIdx tr5
      (tr7.append
        (TREvE (.MessageKey (st.sessionInfo me) .receiver seed pqSalt msg.counter
          c.rIdx parIdx))) :=
    hos7.trans (OnlySkippedFor.append_tr _ _ _ _ _
      (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h)
      (by intro _ _ _ _ _ _ h; cases h)
      (by intro _ _ _ _ _ _ _ h; injection h with h1 h2 _ _ _ h4 _
          exact ⟨h1.symm, h2.symm, h4.symm⟩))
  exact CompSessionOriginInv.of_onlySkippedFor hInv5 hos8 rfl rfl hc_pos hst_rIdx hst_rk hsess5
    ⟨c', mem_setRecvChain hc_mem hc'_pk, hc'_pk.trans hc_pk, hc'_rIdx⟩
    (pos_setRecvChain hpos_st (hc'_rIdx ▸ hc_pos))

private theorem bobAgreement_eq_pqxdhKdf {ikB spkSk pqsk : Bytes} {opkSk : Option Bytes}
    {ikA ek ct : Bytes} {keys : HandshakeKeys}
    (h : bobAgreement ikB spkSk pqsk opkSk ikA ek ct = some keys) :
    ∃ ikm, keys = pqxdhKdf ikm := by
  unfold DY.Libsignal.PQXDH.bobAgreement at h
  change some (pqxdhKdf _) = some keys at h
  injection h with h
  exact ⟨_, h.symm⟩

private theorem run_sendMessage_bind_snd {α : Type} (msg : Bytes) (f : Nat → Traceful α)
    (tr : ExecTrace) :
    ((Network.sendMessage msg >>= f).run tr).2.val =
      ((f tr.length).run (tr.append (NetE msg))).2.val :=
  rfl

theorem CompSessionOriginInv.preserves_aliceStart
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles) :
    Preserves CompSessionOriginInv (aliceStart a b idStateIdx regIdxB bh) := by
  intro tr hInv
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hInv
    (hInv.append_other rfl rfl rfl)
    fun ikA ikB vkB spk spkSig pqpk pqpkSig opk honest _ _ _ _ _ _ _ _ _ _ _ => ?_
  let o := aliceOut tr ikA ikB spk pqpk opk
  let tr2 := (tr.append (RndE 32)).append (RndE 32)
  have hInv2 : CompSessionOriginInv tr2 :=
    (hInv.append_other rfl rfl rfl).append_other rfl rfl rfl
  let dhsA := mkRand tr2.length 32
  let tr3 := tr2.append (RndE 32)
  have hInv3 : CompSessionOriginInv tr3 := hInv2.append_other rfl rfl rfl
  let tr4 := tr3.append (NetE o.ek)
  have hInv4 : CompSessionOriginInv tr4 := hInv3.append_other rfl rfl rfl
  let tr5 := tr4.append (NetE o.ct)
  have hInv5 : CompSessionOriginInv tr5 := hInv4.append_other rfl rfl rfl
  let doneIdx := tr5.length
  let evDone := PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys
  let tr6 := tr5.append (PQEvE evDone)
  have hInv6 : CompSessionOriginInv tr6 := by
    refine hInv5.append_pqx_done fun j keys hhk => ?_
    rcases handshakeKeysAt_append_done hhk with hhk5 | ⟨_, heq⟩
    · exact .inl hhk5
    · rcases heq with ⟨_, _, _, _, _, _, _, _, _, hEq⟩ | ⟨_, _, _, _, _, _, _, _, _, hEq⟩
      · dsimp [evDone] at hEq
        injection hEq with _ _ _ _ _ _ _ _ _ hkeys
        exact .inr ⟨_, hkeys.symm⟩
      · dsimp [evDone] at hEq; nomatch hEq
  have hhk6 : HandshakeKeysAt tr6 doneIdx o.keys :=
    ⟨a, b, o.ikA, o.ikB, o.spk, o.pqpk, o.opk, .inl ⟨o.ek, o.ct,
      Trace.at?_append tr5 (PQEvE evDone)⟩⟩
  let tr7 := tr6.append (TREvE (.InitSession a b (dhPk dhsA) o.spk))
  have hInv7 : CompSessionOriginInv tr7 :=
    hInv6.append_tr_inert (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h)
      (by intro _ _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ _ _ h; cases h)
  let stA : TRState := {
    peer := b, myIk := serializedIk o.ikA, peerIk := serializedIk o.ikB,
    rk := (createChain o.keys.rk o.spk dhsA).1, dhs := dhsA,
    cks := (createChain o.keys.rk o.spk dhsA).2, ns := 0, pn := 0,
    sid := Concat.concat (dhPk dhsA) o.keys.rk, initiator := true, rIdx := 1,
    recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }],
    spqr := Spqr.spqrInit o.keys.pqr spqrA2B }
  let tr8 := tr7.append (CEvE (.HandshakeSession (stA.sessionInfo a) doneIdx))
  have hInv8 : CompSessionOriginInv tr8 := hInv7.append_other rfl rfl rfl
  have hle68 : tr6 ≤ tr8 :=
    Trace.le_trans _ _ _ (Trace.append_le tr6 _) (Trace.append_le tr7 _)
  have hsess8 : CompSessionOrigin tr8 (stA.sessionInfo a) :=
    ⟨doneIdx, o.keys, ⟨tr7.length, Trace.at?_append tr7 _⟩, handshakeKeysAt_mono hle68 hhk6⟩
  exact hInv8.append_storeTR (Nat.le_refl 1) ⟨_, _, _, rfl⟩ hsess8
    (by intro c hc; rw [List.mem_singleton] at hc; subst hc; exact Nat.le_refl 1)

private theorem Preserves.bind_ensureReceiverChain_origin {α : Type}
    (me : Participant) (st₀ : TRState) (pk : Bytes) (tr₀ : ExecTrace)
    (hpos₀ : ∀ x ∈ st₀.recv, 1 ≤ x.rIdx)
    {f : TRState × RecvChain × Bool → Traceful α}
    (hf : ∀ st c ratcheted t,
      c ∈ st.recv → c.ratchetKey = pk → 1 ≤ c.rIdx → (∀ x ∈ st.recv, 1 ≤ x.rIdx) →
      st.sessionInfo me = st₀.sessionInfo me →
      ((ratcheted = false ∧ t = tr₀ ∧ st = st₀) ∨
        (ratcheted = true ∧ t = tr₀.append (RndE 32) ∧ st.rIdx = st₀.rIdx + 2 ∧
         st.dhs = mkRand tr₀.length 32 ∧ ∃ r₀ p₀ s₀, st.rk = (createChain r₀ p₀ s₀).1)) →
      CompSessionOriginInv t →
      CompSessionOriginInv ((f (st, c, ratcheted)).run t).2.val)
    (hInv₀ : CompSessionOriginInv tr₀) :
    CompSessionOriginInv (((ensureReceiverChain st₀ pk >>= f).run tr₀).2.val) := by
  rw [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  unfold DY.Libsignal.TripleRatchet.recvChainFor
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  dsimp only [TRState.toDRState]
  rw [run_bind_snd]
  cases hfind : findRecvChain st₀.recv pk with
  | some c =>
    dsimp only
    obtain ⟨hmem, hpk⟩ := findRecvChain_some hfind
    exact hf st₀ c false tr₀ hmem hpk (hpos₀ c hmem) hpos₀ rfl (.inl ⟨rfl, rfl, rfl⟩) hInv₀
  | none =>
    dsimp only
    by_cases hlo : x25519LowOrder pk = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hlo h]; exact hInv₀
    · rw [ite_eq_right_iff.mpr fun h => absurd h hlo]
      dsimp only; unfold _root_.guard
      have hlo' : (!x25519LowOrder pk) = true := by
        cases h : x25519LowOrder pk <;> simp_all
      rw [ite_eq_left_iff.mpr fun h => absurd hlo' h]
      refine hf _ _ true (tr₀.append (RndE 32)) ?_ rfl ?_ ?_ rfl
        (.inr ⟨rfl, rfl, rfl, rfl, _, _, _, rfl⟩) (hInv₀.append_other rfl rfl rfl)
      · apply mem_drop_append_singleton
        have : 1 ≤ DY.Libsignal.TripleRatchet.maxReceiverChains := by decide
        omega
      · dsimp; omega
      · intro x hx
        rcases List.mem_append.mp (List.mem_of_mem_drop hx) with hx' | hx'
        · exact hpos₀ x hx'
        · rw [List.mem_singleton] at hx'; subst hx'; dsimp; omega

theorem CompSessionOriginInv.preserves_bobStart
    (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat) (mh : PreKeyMsgHandles)
    (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves CompSessionOriginInv (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr hInv
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hInv
    fun ikB spkSk pqsk opkSk ikA vkA ek ct honest keys _ _ _ _ _ _ _ _ hagree => ?_
  have hkdf : ∃ ikm, keys = pqxdhKdf ikm := bobAgreement_eq_pqxdhKdf hagree
  rw [run_bind_snd]
  have htr1 : ((receiveSignalMsg mh.msg).run tr).2.val = tr :=
    Preserves.receiveSignalMsg (Inv := fun t => t = tr) mh.msg tr rfl
  rcases hmsg : ((receiveSignalMsg mh.msg).run tr).1 with _ | msg
  · rw [htr1]; exact hInv
  dsimp only; rw [htr1]
  let st0 : TRState := {
    peer := a, myIk := serializedIk (dhPk ikB), peerIk := serializedIk ikA, rk := keys.rk,
    dhs := spkSk, cks := keys.ck, ns := 0, pn := 0,
    sid := Concat.concat (X25519.normalizeX25519Key msg.ratchetKey) keys.rk,
    initiator := false, rIdx := 0, recv := [], spqr := Spqr.spqrInit keys.pqr spqrB2A }
  refine Preserves.bind_ensureReceiverChain_origin b st0 msg.ratchetKey tr
    (by intro x hx; nomatch hx)
    (fun st c ratcheted tr2 hc_mem hc_pk hc_pos hpos_st _ hcases hInv2 => ?_)
    hInv
  rcases hcases with ⟨_, _, hst⟩ | ⟨hrat, htr2, hst_rIdx, hdhs, hst_rk⟩
  · subst hst; nomatch hc_mem
  subst hrat htr2
  have hst_pos : 1 ≤ st.rIdx := by omega
  dsimp only
  cases hcons : consumeMessageKey c msg.counter with
  | none => exact hInv2
  | some sc =>
    rcases sc with ⟨seed, c'⟩
    obtain ⟨hc'_pk, hc'_rIdx⟩ := consumeMessageKey_some hcons
    dsimp only
    cases hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with
    | none => exact hInv2
    | some sk =>
      rcases sk with ⟨spqr', key⟩
      dsimp only; rw [run_sendMessage_bind_snd]
      let tr3 := (tr.append (RndE 32)).append (NetE key)
      have hInv3 : CompSessionOriginInv tr3 := hInv2.append_other rfl rfl rfl
      refine bind_receiveMessage_at pqIdx tr3 hInv3 fun pqSalt _ _ => ?_
      rw [run_bind_snd, verifyMacAndDecrypt_trace]
      rcases hdec : ((verifyMacAndDecrypt st msg pqSalt seed).run tr3).1 with _ | m
      · exact hInv3
      dsimp only
      have h_commit_opk : ∀ (t : ExecTrace), tr.length < t.length → CompSessionOriginInv t →
          CompSessionOriginInv ((do
            let doneIdx ← traceLength
            ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (dhPk ikB) ikA (dhPk spkSk) (PQKem.kemPk pqsk)
              (opkSk.map dhPk) ek ct keys)
            if true = true then
              ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (dhPk st.dhs))
              ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
            ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
            let skipped := msg.counter.toNat - c.index.toNat
            let childIdx := (← traceLength) + skipped + 2
            logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
            ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
            logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
              msg.counter c.rIdx childIdx
              { st with recv := setRecvChain st.recv c', spqr := spqr' }).run t).2.val := by
        intro t4 hlt4 hInv4
        let doneIdx := t4.length
        let evDone := PQXDHEvent.BobDone b a (dhPk ikB) ikA (dhPk spkSk) (PQKem.kemPk pqsk)
          (opkSk.map dhPk) ek ct keys
        let t5 := t4.append (PQEvE evDone)
        have hInv5 : CompSessionOriginInv t5 := by
          refine hInv4.append_pqx_done fun j keys' hhk => ?_
          rcases handshakeKeysAt_append_done hhk with hhk4 | ⟨_, heq⟩
          · exact .inl hhk4
          · rcases heq with ⟨_, _, _, _, _, _, _, _, _, hEq⟩ | ⟨_, _, _, _, _, _, _, _, _, hEq⟩
            · dsimp [evDone] at hEq; nomatch hEq
            · dsimp [evDone] at hEq
              injection hEq with _ _ _ _ _ _ _ _ _ hkeys
              subst hkeys; exact .inr hkdf
        have hhk5 : HandshakeKeysAt t5 doneIdx keys :=
          ⟨a, b, ikA, dhPk ikB, dhPk spkSk, PQKem.kemPk pqsk, opkSk.map dhPk, .inr ⟨ek, ct,
            Trace.at?_append t4 (PQEvE evDone)⟩⟩
        let t6 := t5.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (dhPk st.dhs)))
        have hInv6 : CompSessionOriginInv t6 :=
          hInv5.append_tr_inert (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h)
            (by intro _ _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ _ _ h; cases h)
        have hlen_t6 : tr.length < t6.length := by simp [t5, t6, Trace.append, Trace.length]; omega
        let t7 := t6.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
        have hInv7 : CompSessionOriginInv t7 := hInv6.append_honestDH ⟨tr.length, hlen_t6, hdhs⟩
        let t8 := t7.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
        have hInv8 : CompSessionOriginInv t8 := hInv7.append_other rfl rfl rfl
        have hle58 : t5 ≤ t8 :=
          Trace.le_trans _ _ _ (Trace.append_le t5 _)
            (Trace.le_trans _ _ _ (Trace.append_le t6 _) (Trace.append_le t7 _))
        have hsess8 : CompSessionOrigin t8 (st.sessionInfo b) :=
          ⟨doneIdx, keys, ⟨t7.length, Trace.at?_append t7 _⟩, handshakeKeysAt_mono hle58 hhk5⟩
        exact CompSessionOriginInv.decryptTail b
          (t8.length + (msg.counter.toNat - c.index.toNat) + 2)
          (t8.length + (msg.counter.toNat - c.index.toNat) + 2)
          st msg c c' seed pqSalt m spqr'
          hc_mem hc_pk hc_pos hpos_st hc'_pk hc'_rIdx hst_pos hst_rk t8 hInv8 hsess8
      have hlt3 : tr.length < tr3.length := by simp [tr3, Trace.append, Trace.length]; omega
      rcases opkSk with _ | o
      · exact h_commit_opk tr3 hlt3 hInv3
      · dsimp only [Option.map]
        have hguard : ((DY.Libsignal.PQXDH.guardTrace fun tr => !opkUsedB tr b (dhPk o)).run tr3).2.val = tr3 :=
          Preserves.requireTracePredicate (Inv := fun t => t = tr3) _ tr3 rfl
        rw [run_bind_snd]
        rcases ((DY.Libsignal.PQXDH.guardTrace fun tr => !opkUsedB tr b (dhPk o)).run tr3).1 with _ | _
        · rw [hguard]; exact hInv3
        · dsimp only; rw [hguard]
          exact h_commit_opk (tr3.append (PQEvE (.OPKUsed b (dhPk o))))
            (by simp [Trace.append, Trace.length]; omega)
            (hInv3.append_pqx_nonDone (fun _ _ _ _ _ _ _ _ _ _ =>
              And.intro (fun h => by cases h) (fun h => by cases h)))

private theorem Preserves.sessionOrigin (s : SessionInfo) {α : Type} (x : Traceful α) :
    Preserves (fun t => CompSessionOrigin t s) x :=
  fun tr h => h.mono (x.run tr).2.property

private theorem Preserves.and {P Q : ExecTrace → Prop} {α : Type} {x : Traceful α}
    (hP : Preserves P x) (hQ : Preserves Q x) :
    Preserves (fun tr => P tr ∧ Q tr) x :=
  fun tr ⟨hp, hq⟩ => ⟨hP tr hp, hQ tr hq⟩

private theorem bind_getEntry_tr_at {Inv : ExecTrace → Prop} {α : Type}
    (evH : Nat) {f : TREntry → Traceful α} (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ e, tr.EventLogged e.ev → Inv ((f e).run tr).2.val) :
    Inv (((DY.getEntry evH : Traceful TREntry) >>= f).run tr).2.val := by
  unfold DY.getEntry
  simp only [Traceful.run_bind, Traceful.run_mk]
  rcases he : (tr.at? evH : Option TREntry) with _ | e
  · exact hInv
  · exact hf e ⟨evH, he⟩

theorem CompSessionOriginInv.preserves_messageEncrypt
    (me : Participant) (stH coinsLen pqIdx : Nat) :
    Preserves CompSessionOriginInv (messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
    DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine Preserves.bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  obtain ⟨hrIdx, hrk, hsess₀, hpos⟩ := hInv₀.storedOK me st stH hst₀
  let s := st.sessionInfo me
  suffices hpres : Preserves (fun t => CompSessionOriginInv t ∧ CompSessionOrigin t s) _ by
    exact (hpres tr₀ ⟨hInv₀, hsess₀⟩).1
  refine Preserves.bind (Preserves.and (Preserves.guardP _) (Preserves.sessionOrigin s _)) fun _ => ?_
  refine Preserves.bind
    (Preserves.and (fun _ h => h.append_other rfl rfl rfl) (Preserves.sessionOrigin s _)) fun _ => ?_
  refine Preserves.bind
    (Preserves.and (fun _ h => h.append_other rfl rfl rfl) (Preserves.sessionOrigin s _)) fun _ => ?_
  refine Preserves.bind
    (Preserves.and (fun _ h => h.append_other rfl rfl rfl) (Preserves.sessionOrigin s _)) fun _ => ?_
  refine Preserves.bind
    (Preserves.and (Preserves.receiveMessage _) (Preserves.sessionOrigin s _)) fun _ => ?_
  refine Preserves.bind
    (Preserves.and (fun _ h => h.append_tr_inert (by intro _ _ _ h; cases h)
      (by intro _ _ _ h; cases h) (by intro _ _ _ _ _ _ h; cases h)
      (by intro _ _ _ _ _ _ _ h; cases h)) (Preserves.sessionOrigin s _)) fun _ => ?_
  refine Preserves.bind
    (Preserves.bind
      (fun t ⟨hI, hS⟩ => ⟨hI.append_sendMK hS, hS.mono (Trace.append_le t _)⟩)
      (fun _ t ⟨hI, hS⟩ => ⟨hI.append_storeTR hrIdx hrk hS hpos, hS.mono (Trace.append_le t _)⟩))
    fun _ => ?_
  exact Preserves.and (fun _ h => h.append_other rfl rfl rfl) (Preserves.sessionOrigin s _)

theorem CompSessionOriginInv.preserves_messageDecrypt
    (me : Participant) (stH msgH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves CompSessionOriginInv (messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine Preserves.bind_getLocalState_tr me stH fun st₀ tr₀ hInv₀ hst₀ => ?_
  obtain ⟨hrIdx₀, hrk₀, hsess₀, hpos₀⟩ := hInv₀.storedOK me st₀ stH hst₀
  rw [run_bind_snd]
  have htr1 : ((receiveSignalMsg msgH).run tr₀).2.val = tr₀ :=
    Preserves.receiveSignalMsg (Inv := fun t => t = tr₀) msgH tr₀ rfl
  rcases ((receiveSignalMsg msgH).run tr₀).1 with _ | msg
  · rw [htr1]; exact hInv₀
  dsimp only; rw [htr1]
  refine Preserves.bind_ensureReceiverChain_origin me st₀ msg.ratchetKey tr₀ hpos₀
    (fun st c ratcheted t1 hc_mem hc_pk hc_pos hpos_st hsinfo hcases hInv1 => ?_)
    hInv₀
  have hst_rIdx : 1 ≤ st.rIdx := by
    rcases hcases with ⟨_, _, rfl⟩ | ⟨_, _, hr, _, _⟩
    · exact hrIdx₀
    · omega
  have hst_rk : ∃ r₀ p₀ s₀, st.rk = (createChain r₀ p₀ s₀).1 := by
    rcases hcases with ⟨_, _, rfl⟩ | ⟨_, _, _, _, hrk⟩
    · exact hrk₀
    · exact hrk
  have hsess1 : CompSessionOrigin t1 (st.sessionInfo me) := by
    rw [hsinfo]
    rcases hcases with ⟨_, rfl, _⟩ | ⟨_, rfl, _, _, _⟩
    · exact hsess₀
    · exact hsess₀.mono (Trace.append_le tr₀ _)
  dsimp only
  cases hcons : consumeMessageKey c msg.counter with
  | none => exact hInv1
  | some sc =>
    rcases sc with ⟨seed, c'⟩
    obtain ⟨hc'_pk, hc'_rIdx⟩ := consumeMessageKey_some hcons
    dsimp only
    cases hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with
    | none => exact hInv1
    | some sk =>
      rcases sk with ⟨spqr', key⟩
      dsimp only; rw [run_sendMessage_bind_snd]
      let t2 := t1.append (NetE key)
      have hInv2 : CompSessionOriginInv t2 := hInv1.append_other rfl rfl rfl
      have hsess2 : CompSessionOrigin t2 (st.sessionInfo me) := hsess1.mono (Trace.append_le t1 _)
      refine bind_receiveMessage_at pqIdx t2 hInv2 fun pqSalt _ _ => ?_
      rw [run_bind_snd, verifyMacAndDecrypt_trace]
      rcases ((verifyMacAndDecrypt st msg pqSalt seed).run t2).1 with _ | m
      · exact hInv2
      dsimp only
      rcases hcases with ⟨rfl, _, _⟩ | ⟨rfl, rfl, _, hdhs_eq, _⟩
      · exact CompSessionOriginInv.decryptTail me stH stH st msg c c' seed pqSalt m spqr'
          hc_mem hc_pk hc_pos hpos_st hc'_pk hc'_rIdx hst_rIdx hst_rk t2 hInv2 hsess2
      · let t3 := t2.append (TREvE (.DHRatchet me st.peer msg.ratchetKey (dhPk st.dhs)))
        have hInv3 : CompSessionOriginInv t3 :=
          hInv2.append_tr_inert (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h)
            (by intro _ _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ _ _ h; cases h)
        have htd3 : tr₀.length < t3.length := by simp [t2, t3, Trace.append, Trace.length]; omega
        let t4 := t3.append (TREvE (.HonestDH (st.sessionInfo me) st.dhs (st.rIdx - 2)))
        have hInv4 : CompSessionOriginInv t4 := hInv3.append_honestDH ⟨tr₀.length, htd3, hdhs_eq⟩
        have hsess4 : CompSessionOrigin t4 (st.sessionInfo me) :=
          (hsess2.mono (Trace.append_le t2 _)).mono (Trace.append_le t3 _)
        exact CompSessionOriginInv.decryptTail me stH stH st msg c c' seed pqSalt m spqr'
          hc_mem hc_pk hc_pos hpos_st hc'_pk hc'_rIdx hst_rIdx hst_rk t4 hInv4 hsess4

theorem CompSessionOriginInv.preserves_messageDecryptSkipped
    (me : Participant) (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves CompSessionOriginInv (messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine Preserves.bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  obtain ⟨hrIdx, hrk, hsess₀, hpos⟩ := hInv₀.storedOK me st stH hst₀
  rw [run_bind_snd]
  have htr1 : ((receiveSignalMsg msgH).run tr₀).2.val = tr₀ :=
    Preserves.receiveSignalMsg (Inv := fun t => t = tr₀) msgH tr₀ rfl
  rcases ((receiveSignalMsg msgH).run tr₀).1 with _ | msg
  · rw [htr1]; exact hInv₀
  dsimp only; rw [htr1]
  refine bind_getEntry_tr_at evH tr₀ hInv₀ fun e hev => ?_
  rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
    dsimp only
    obtain ⟨hheld₀, hsess_s₀⟩ := hInv₀.skippedOK s pk n seed rIdx sourceStateIdx hev
    let R (t : ExecTrace) : Prop :=
      CompSessionOrigin t s ∧ CompSessionOrigin t (st.sessionInfo me) ∧ ChainHeldOnTrace t s pk rIdx
    have hR : ∀ {α : Type} (x : Traceful α), Preserves R x := fun x tr ⟨h1, h2, h3⟩ =>
      ⟨h1.mono (x.run tr).2.property, h2.mono (x.run tr).2.property, h3.mono (x.run tr).2.property⟩
    suffices hpres : Preserves (fun t => CompSessionOriginInv t ∧ R t) _ by
      exact (hpres tr₀ ⟨hInv₀, hsess_s₀, hsess₀, hheld₀⟩).1
    refine Preserves.bind (Preserves.and (Preserves.guardP _) (hR _)) fun _ => ?_
    refine Preserves.bind (Preserves.and (Preserves.guardTrace _) (hR _)) fun _ => ?_
    split
    · next spqr' key _ =>
      refine Preserves.bind (Preserves.and (fun _ h => h.append_other rfl rfl rfl) (hR _)) fun _ => ?_
      refine Preserves.bind (Preserves.and (Preserves.receiveMessage _) (hR _)) fun pqSalt => ?_
      refine Preserves.bind (Preserves.and (Preserves.verifyMacAndDecrypt _ _ _ _) (hR _)) fun _ => ?_
      refine Preserves.bind (Preserves.and (fun _ h => h.append_tr_inert
        (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ _ _ _ _ _ h; cases h)
        (by intro _ _ _ _ _ _ _ h; cases h)) (hR _)) fun _ => ?_
      refine Preserves.bind (Preserves.and (fun _ h => h.append_tr_inert
        (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ _ _ _ _ _ h; cases h)
        (by intro _ _ _ _ _ _ _ h; cases h)) (hR _)) fun _ => ?_
      intro t ⟨hI, hS, hS_st, hC⟩
      unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
      let t' := t.append (TREvE (.MessageKey s .receiver seed pqSalt n rIdx stH))
      have hI' : CompSessionOriginInv t' := hI.append_recvMK hS
      have hle' : t ≤ t' := Trace.append_le t _
      have hI'' : CompSessionOriginInv (t'.append (TRStE me { st with spqr := spqr' })) :=
        hI'.append_storeTR hrIdx hrk (hS_st.mono hle') hpos
      have hle'' : t ≤ t'.append (TRStE me { st with spqr := spqr' }) :=
        Trace.le_trans _ _ _ hle' (Trace.append_le t' _)
      exact ⟨hI'', hS.mono hle'', hS_st.mono hle'', hC.mono hle''⟩
    · exact Preserves.failure
  | _ => exact hInv₀

end Symbolic.Swarm.COMPOSED.CompRatchet
