/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.TripleRatchet
public import Symbolic.Specifications.Model.PQXDH
public import Symbolic.Specifications.Model.Composed
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Trace.Monad

/-!
# Model Proof Definitions and Unfolding Lemmas

Auxiliary receiver-chain lookup helper `recvChainFor`, `Traceful` monad laws, and inline
characterization lemmas for `TripleRatchet` and `Composed` state-machine transitions.
-/

@[expose] public section

namespace DY.Libsignal.TripleRatchet

section KeyScheduleLemmas

variable [HasExecBytes]

/-- Looks up or derives the receiver chain for `theirPk`: returns `some (c, false)` if `theirPk` is
already in `st.recv`, `some (c, true)` for a freshly derived chain, or `none` if `theirPk` is
low-order. -/
def recvChainFor (st : DRState) (theirPk : Bytes) : Option (RecvChain × Bool) :=
  match findRecvChain st.recv theirPk with
  | some c => some (c, false)
  | none =>
    if x25519LowOrder theirPk then none
    else
      let (_rk1, ckr) := createChain st.rk theirPk st.dhs
      some ({ ratchetKey := theirPk, chainKey := ckr, index := 0, rIdx := st.rIdx + 2 }, true)

theorem recvChainFor_eq_find_recvHalfStep (st : DRState) (theirPk : Bytes) :
    recvChainFor st theirPk =
      match findRecvChain st.recv theirPk with
      | some c => some (c, false)
      | none => (recvHalfStep st theirPk).map (fun (_, c) => (c, true)) := by
  unfold recvChainFor recvHalfStep
  cases findRecvChain st.recv theirPk with
  | some c => rfl
  | none =>
    cases x25519LowOrder theirPk <;> rfl

theorem match_find_recvHalfStep_eq_recvChainFor {α : Type} (st : TRState) (pk : Bytes)
    (onFresh : RecvChain → α) (onOther : α) :
    (match findRecvChain st.recv pk, recvHalfStep st.toDRState pk with
     | none, some (_, c) => onFresh c
     | _, _ => onOther) =
    (match recvChainFor st.toDRState pk with
     | some (c, true) => onFresh c
     | _ => onOther) := by
  unfold recvChainFor recvHalfStep
  cases findRecvChain st.recv pk with
  | some _ => rfl
  | none => cases x25519LowOrder pk <;> rfl

end KeyScheduleLemmas

section TraceHelperLemmas

theorem traceful_ext [ExecTraceTypes] {α : Type} {x y : Traceful α}
    (h : ∀ tr, (x.run tr).1 = (y.run tr).1 ∧ (x.run tr).2.val = (y.run tr).2.val) :
    x = y := by
  funext tr
  have heq : x.run tr = y.run tr := by
    rcases hx : x.run tr with ⟨ox, tx, htx⟩
    rcases hy : y.run tr with ⟨oy, ty, hty⟩
    have ⟨h1, h2⟩ := h tr
    rw [hx, hy] at h1 h2
    dsimp only at h1 h2
    subst h1 h2
    rfl
  exact (Symbolic.DYBridge.DY.Traceful.run_eq_1 x tr).symm.trans
    (heq.trans (Symbolic.DYBridge.DY.Traceful.run_eq_1 y tr))

theorem traceful_pure_bind [ExecTraceTypes] {α β : Type} (a : α) (f : α → Traceful β) :
    (Pure.pure a >>= f) = f a := by
  apply traceful_ext
  intro tr
  rw [Traceful.run_bind, Traceful.run_pure]
  exact ⟨rfl, rfl⟩

theorem traceful_failure_bind [ExecTraceTypes] {α β : Type} (f : α → Traceful β) :
    ((failure : Traceful α) >>= f) = failure := by
  apply traceful_ext
  intro tr
  rw [Traceful.run_bind, Traceful.run_failure, Traceful.run_failure]
  exact ⟨rfl, rfl⟩

theorem traceful_bind_assoc [ExecTraceTypes] {α β γ : Type}
    (m : Traceful α) (f : α → Traceful β) (g : β → Traceful γ) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  apply traceful_ext
  intro tr
  rw [Traceful.run_bind, Traceful.run_bind, Traceful.run_bind]
  rcases h1 : m.run tr with ⟨_ | a, tr1⟩
  · exact ⟨rfl, rfl⟩
  · dsimp only
    rw [Traceful.run_bind (f a) g]
    rcases h2 : (f a).run tr1.val with ⟨_ | b, tr2⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

theorem anyEventOnTrace_eq_at? (EventT : Type) [ExecTraceTypes]
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
    (tr : ExecTrace) (p : EventT → Bool) :
    anyEventOnTrace EventT tr p =
      (List.range tr.length).any fun i =>
        match (tr.at? i : Option (ProtocolEvent.ExecEntryT EventT)) with
        | some e => p e.ev
        | none => false := by
  unfold anyEventOnTrace
  apply List.any_congr rfl
  intro i
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  cases (tr.at? i : Option (ProtocolEvent.ExecEntryT EventT)) <;> rfl

end TraceHelperLemmas

section SpecificationLemmas

variable [HasExecTrace]

open DiffieHellman
open PersistentLocalState (getLocalState)
open Network (sendMessage receiveMessage)
open Random (genRand)
open ProtocolEvent (logEvent)

theorem dhRatchetStep_eq_guard (st : TRState) (theirPk : Bytes) :
    dhRatchetStep st theirPk = (do
      guard (!x25519LowOrder theirPk)
      let (rk1, ckr) := createChain st.rk theirPk st.dhs
      let dhs ← genRand 32
      let (rk2, cks) := createChain rk1 theirPk dhs
      let c : RecvChain := { ratchetKey := theirPk, chainKey := ckr, index := 0, rIdx := st.rIdx + 2 }
      let recv := (st.recv ++ [c]).drop ((st.recv.length + 1) - maxReceiverChains)
      let pn := if st.ns = 0 then 0 else st.ns - 1
      pure ({ st with rk := rk2, dhs, cks, ns := 0, pn, rIdx := st.rIdx + 2, recv }, c)) := by
  unfold dhRatchetStep recvHalfStep pushRecvChain _root_.guard
  cases hlo : x25519LowOrder theirPk
  · simp only [Bool.false_eq_true, Bool.not_false, ↓reduceIte, traceful_pure_bind]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, traceful_failure_bind]

theorem ensureReceiverChain_eq_recvChainFor (st : TRState) (theirPk : Bytes) :
    ensureReceiverChain st theirPk = (do
      match recvChainFor st.toDRState theirPk with
      | some (c, false) => pure (st, c, false)
      | some (_, true) =>
        let (st, c) ← dhRatchetStep st theirPk
        pure (st, c, true)
      | none => failure) := by
  unfold ensureReceiverChain recvChainFor
  cases findRecvChain st.recv theirPk with
  | some c => rfl
  | none =>
    unfold dhRatchetStep recvHalfStep
    cases x25519LowOrder theirPk
    · rfl
    · simp only [↓reduceIte, traceful_failure_bind]

theorem messageDecrypt_eq_inline (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx = (do
      let st : TRState ← getLocalState me stateIdx
      let msg ← receiveSignalMsg msgIdx
      let (st, c, ratcheted) ← ensureReceiverChain st msg.ratchetKey
      let some (seed, c') := consumeMessageKey c msg.counter | failure
      let some (spqr', key) := Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx | failure
      let _ ← sendMessage key
      let pqSalt ← receiveMessage pqIdx
      let m ← verifyMacAndDecrypt st msg pqSalt seed
      if ratcheted then
        logEvent (TREvent.DHRatchet me st.peer msg.ratchetKey (dhPk st.dhs))
        logEvent (TREvent.HonestDH (st.sessionInfo me) st.dhs (st.rIdx - 2))
      logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
        (msg.counter.toNat - c.index.toNat)
      logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
      logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter
        c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) := by
  unfold messageDecrypt decryptInMemory PendingDecrypt.logRatchet PendingDecrypt.commit
  simp only [traceful_bind_assoc]
  congr 1; funext st0
  congr 1; funext msg
  congr 1; funext ⟨st, c, ratcheted⟩
  cases consumeMessageKey c msg.counter with
  | none => exact traceful_failure_bind _
  | some p1 =>
    rcases p1 with ⟨seed, c'⟩
    dsimp only
    cases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with
    | none => exact traceful_failure_bind _
    | some p2 =>
      rcases p2 with ⟨spqr', key⟩
      cases ratcheted <;>
        simp only [Bool.false_eq_true, ↓reduceIte, traceful_bind_assoc, traceful_pure_bind]

theorem isCurrentSnapshot_eq_at? (tr : ExecTrace) (stateIdx : Nat) :
    isCurrentSnapshot tr stateIdx =
      match (tr.at? stateIdx : Option (PersistentGlobalState.State.ExecEntryT
          (PersistentLocalState.LocalState TRState))) with
      | some e =>
        (List.range' (stateIdx + 1) (tr.length - (stateIdx + 1))).all fun j =>
          match (tr.at? j : Option (PersistentGlobalState.State.ExecEntryT
              (PersistentLocalState.LocalState TRState))) with
          | some e' => e'.st.participant != e.st.participant ||
              e'.st.state.initiator != e.st.state.initiator
          | none => true
      | none => false := by
  unfold isCurrentSnapshot getStoredLocalStateAt?
  cases (tr.at? stateIdx : Option (PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState TRState))) with
  | none => rfl
  | some e =>
    dsimp only [Option.map]
    apply List.all_congr rfl
    intro j
    cases (tr.at? j : Option (PersistentGlobalState.State.ExecEntryT
        (PersistentLocalState.LocalState TRState))) <;> rfl

end SpecificationLemmas

end DY.Libsignal.TripleRatchet

namespace DY.Libsignal.PQXDH

export DY.Libsignal.TripleRatchet (anyEventOnTrace_eq_at?)

end DY.Libsignal.PQXDH

namespace DY.Libsignal.Composed

section SpecificationLemmas

variable [HasExecTrace]

open DiffieHellman
open PersistentLocalState (storeLocalState)
open Network (sendMessage receiveMessage)
open Random (genRand)
open ProtocolEvent (logEvent)

theorem aliceStart_eq_inline (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : PQXDH.BundleHandles) :
    aliceStart a b idStateIdx regIdxB h = (do
      let o ← PQXDH.aliceHandshake a b idStateIdx regIdxB h
      let dhsA ← genRand 32
      let (rkA, cksA) := TripleRatchet.createChain o.keys.rk o.spk dhsA
      let stA : TripleRatchet.TRState := {
        peer := b, myIk := PQXDH.serializedIk o.ikA, peerIk := PQXDH.serializedIk o.ikB,
        rk := rkA, dhs := dhsA, cks := cksA, ns := 0, pn := 0,
        sid := Concat.concat (dhPk dhsA) o.keys.rk, initiator := true, rIdx := 1,
        recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }],
        spqr := Spqr.spqrInit o.keys.pqr TripleRatchet.spqrA2B }
      let _ ← sendMessage o.ek
      let _ ← sendMessage o.ct
      let doneIdx ← TripleRatchet.traceLength
      logEvent (PQXDH.PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys)
      logEvent (TripleRatchet.TREvent.InitSession a b (dhPk dhsA) o.spk)
      logEvent (ComposedEvent.HandshakeSession (stA.sessionInfo a) doneIdx)
      storeLocalState a stA) := by
  rfl

theorem bobStart_eq_inline (b a : Participant) (kh : PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    bobStart b a kh regIdxA mh pqIdx spqrMsgIdx = (do
      let o ← PQXDH.bobHandshake b a kh regIdxA mh.ek mh.ct
      let msg ← TripleRatchet.receiveSignalMsg mh.msg
      let st0 : TripleRatchet.TRState := {
        peer := a, myIk := PQXDH.serializedIk o.ikB, peerIk := PQXDH.serializedIk o.ikA,
        rk := o.keys.rk, dhs := o.spkSk, cks := o.keys.ck, ns := 0, pn := 0,
        sid := Concat.concat (X25519.normalizeX25519Key msg.ratchetKey) o.keys.rk,
        initiator := false, rIdx := 0, recv := [],
        spqr := Spqr.spqrInit o.keys.pqr TripleRatchet.spqrB2A }
      let (st, c, ratcheted) ← TripleRatchet.ensureReceiverChain st0 msg.ratchetKey
      let some (seed, c') := TripleRatchet.consumeMessageKey c msg.counter | failure
      let some (spqr', key) := Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx | failure
      let _ ← sendMessage key
      let pqSalt ← receiveMessage pqIdx
      let m ← TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed
      match o.opk with
      | some opk =>
        PQXDH.guardTrace fun tr => !PQXDH.opkUsedB tr b opk
        logEvent (PQXDH.PQXDHEvent.OPKUsed b opk)
      | none => pure ()
      let doneIdx ← TripleRatchet.traceLength
      logEvent (PQXDH.PQXDHEvent.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys)
      if ratcheted then
        logEvent (TripleRatchet.TREvent.DHRatchet b st.peer msg.ratchetKey (dhPk st.dhs))
        logEvent (TripleRatchet.TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
      logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
      let skipped := msg.counter.toNat - c.index.toNat
      let childIdx := (← TripleRatchet.traceLength) + skipped + 2
      TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey
        c.index skipped
      logEvent (TripleRatchet.TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
        msg.counter c.rIdx childIdx
        { st with recv := TripleRatchet.setRecvChain st.recv c', spqr := spqr' }) := by
  unfold bobStart TripleRatchet.initBobState TripleRatchet.decryptInMemory
    TripleRatchet.PendingDecrypt.logRatchet TripleRatchet.PendingDecrypt.commit
  simp only [TripleRatchet.traceful_bind_assoc]
  congr 1; funext o
  congr 1; funext msg
  congr 1; funext ⟨st, c, ratcheted⟩
  cases TripleRatchet.consumeMessageKey c msg.counter with
  | none => exact TripleRatchet.traceful_failure_bind _
  | some p1 =>
    rcases p1 with ⟨seed, c'⟩
    dsimp only
    cases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with
    | none => exact TripleRatchet.traceful_failure_bind _
    | some p2 =>
      rcases p2 with ⟨spqr', key⟩
      cases o.opk <;> cases ratcheted <;>
        simp only [Bool.false_eq_true, ↓reduceIte, TripleRatchet.traceful_bind_assoc,
          TripleRatchet.traceful_pure_bind]

end SpecificationLemmas

end DY.Libsignal.Composed
