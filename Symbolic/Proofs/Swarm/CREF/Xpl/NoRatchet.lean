/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
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
import Mathlib.Data.List.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.Prelude
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
# Non-Ratcheting Decrypt Inversion

Proves `noRatchet_of_rngFree` and `noRatchet_of_matched`: an accepting `Move.decrypt` step with no
`.rng` entry reuses an existing receiving chain
(`recvChainFor st.toDRState msg.ratchetKey = some (c, false)`) without running `dhRatchetStep`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

open DY
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain recvChainFor findRecvChain setRecvChain
  consumeMessageKey kdfCk computeMac messageVersion x25519LowOrder createChain maxReceiverChains)
open CryptoProofLib.Refinement (ExternInterpretation)

private abbrev B4StEntry :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
private abbrev B4TREntry := DY.ProtocolEvent.ExecEntryT TREvent

/-! ## Trace-append algebra -/

private theorem b4_length_append {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem b4_at?_append_lt {E E2 : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

private theorem b4_at?_append_length {E E2 : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E) :
    ((tr.append e).at? tr.length : Option E2) =
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  have hlt : tr.length < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  simp only [Trace.at?, hlt, ↓reduceDIte]
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

private theorem b4_at?_append_self {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    ((tr.append e).at? tr.length : Option E) = some e := by
  rw [b4_at?_append_length, TraceEntryHas.inj_proj_eq]

private theorem b4_getEventAt_append_lt {E : Type} [ExecTraceTypes.Has E]
    (EventT : Type) [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
    (tr : ExecTrace) (e : E) {i : Nat} (hi : i < tr.length) :
    (tr.append e).getEventAt EventT i = tr.getEventAt EventT i := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, b4_at?_append_lt tr e hi]

private theorem b4_newRandoms_self (tr : ExecTrace) : newRandoms tr tr = [] := by
  simp [newRandoms, newIndices]

private theorem b4_receivedPlaintext_self (tr : ExecTrace) : receivedPlaintext tr tr = none := by
  simp [receivedPlaintext, newIndices]

private theorem b4_mem_newIndices {tr0 tr : ExecTrace} {i : Nat} :
    i ∈ newIndices tr0 tr ↔ tr0.length ≤ i ∧ i < tr.length := by
  simp only [newIndices, List.mem_range'_1]
  omega

private theorem b4_newIndices_append {E : Type} [ExecTraceTypes.Has E]
    {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E) :
    newIndices tr0 (tr.append e) = newIndices tr0 tr ++ [tr.length] := by
  simp only [newIndices, b4_length_append]
  rw [show tr.length + 1 - tr0.length = (tr.length - tr0.length) + 1 by omega, List.range'_concat]
  congr 2
  omega

private theorem b4_newRandoms_append {E : Type} [ExecTraceTypes.Has E]
    {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E) :
    newRandoms tr0 (tr.append e) = newRandoms tr0 tr ++
      (((tr.append e).at? tr.length : Option DY.Random.ExecEntryT).map
        fun r => (randTerm tr.length r.length, r.length)).toList := by
  unfold newRandoms
  rw [b4_newIndices_append h, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  congr 1
  refine List.filterMap_congr fun i hi => ?_
  rw [b4_at?_append_lt tr e (b4_mem_newIndices.mp hi).2]

private theorem b4_newRandoms_append_rnd {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (n : Nat) :
    newRandoms tr0 (tr.append (DY.Random.ExecEntryT.mk n)) =
      newRandoms tr0 tr ++ [(randTerm tr.length n, n)] := by
  rw [b4_newRandoms_append h, b4_at?_append_self]
  rfl

private theorem b4_newRandoms_append_of_proj {E : Type} [ExecTraceTypes.Has E]
    {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) = none) :
    newRandoms tr0 (tr.append e) = newRandoms tr0 tr := by
  rw [b4_newRandoms_append h, b4_at?_append_length, hproj]
  simp

private def b4_receivedAt (tr : ExecTrace) (i : Nat) : Option DY.Bytes :=
  match tr.getEventAt TREvent i with
  | some (.Received _ _ _ _ m) => some m
  | _ => none

private theorem b4_findSome?_congr {α β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ x ∈ l, f x = g x) : l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findSome?_cons, List.findSome?_cons, h a (by simp), ih fun x hx => h x (by simp [hx])]

private theorem b4_receivedPlaintext_eq (tr0 tr : ExecTrace) :
    receivedPlaintext tr0 tr = (newIndices tr0 tr).findSome? (b4_receivedAt tr) := rfl

private theorem b4_receivedAt_append_lt {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) {i : Nat} (hi : i < tr.length) :
    b4_receivedAt (tr.append e) i = b4_receivedAt tr i := by
  simp only [b4_receivedAt, b4_getEventAt_append_lt TREvent tr e hi]

private theorem b4_receivedPlaintext_append {E : Type} [ExecTraceTypes.Has E]
    {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E) :
    receivedPlaintext tr0 (tr.append e) =
      (receivedPlaintext tr0 tr).or (b4_receivedAt (tr.append e) tr.length) := by
  rw [b4_receivedPlaintext_eq, b4_receivedPlaintext_eq, b4_newIndices_append h, List.findSome?_append]
  have hcongr : (newIndices tr0 tr).findSome? (b4_receivedAt (tr.append e)) =
      (newIndices tr0 tr).findSome? (b4_receivedAt tr) := by
    refine b4_findSome?_congr fun i hi => ?_
    exact b4_receivedAt_append_lt tr e (b4_mem_newIndices.mp hi).2
  rw [hcongr, List.findSome?_singleton]

private theorem b4_receivedPlaintext_append_of_proj {E : Type} [ExecTraceTypes.Has E]
    {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT TREvent)) = none) :
    receivedPlaintext tr0 (tr.append e) = receivedPlaintext tr0 tr := by
  rw [b4_receivedPlaintext_append h]
  have hnone : b4_receivedAt (tr.append e) tr.length = none := by
    simp only [b4_receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, b4_at?_append_length, hproj]
  rw [hnone, Option.or_none]

/-! ## `Traceful` bind and step helpers -/

private theorem b4_run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem b4_run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem b4_run_bind_pure_val {α : Type} (m : Traceful α) (tr : ExecTrace) :
    (((m >>= fun _ => (pure () : Traceful Unit))).run tr).2.val = (m.run tr).2.val := by
  rw [Traceful.run_bind]; rcases m.run tr with ⟨_ | _, _⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem b4_getLocalState_snd (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1, _root_.guard]
  rw [b4_run_bind_snd, b4_run_bind_fst, b4_run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option B4StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only; rw [Traceful.run_pure]; dsimp only
    by_cases hp : p = me
    · simp only [hp, ↓reduceIte, b4_run_bind_snd, Traceful.run_pure]
    · simp only [hp, ↓reduceIte, b4_run_bind_snd, Traceful.run_failure]

private theorem b4_receiveMessage_fst (idx : Nat) (tr : ExecTrace) :
    ((DY.Network.receiveMessage idx).run tr).1 = tr.getMessageSentAt idx := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  rw [b4_run_bind_fst, Traceful.run_mk]
  rcases (tr.at? idx : Option Network.ExecEntryT) with _ | ⟨t⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem b4_receiveMessage_snd (idx : Nat) (tr : ExecTrace) :
    ((DY.Network.receiveMessage idx).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [b4_run_bind_snd, Traceful.run_mk]
  rcases (tr.at? idx : Option Network.ExecEntryT) with _ | ⟨t⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem b4_receiveSignalMsg_snd (msgIdx : Nat) (tr : ExecTrace) :
    ((receiveSignalMsg msgIdx).run tr).2.val = tr := by
  unfold receiveSignalMsg
  rw [b4_run_bind_snd, b4_receiveMessage_snd]
  rcases ((DY.Network.receiveMessage msgIdx).run tr).1 with _ | raw
  · rfl
  · dsimp only
    rcases parseTrSignalMsg raw with _ | msg
    · (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
    · dsimp only
      by_cases hv : msg.version = messageVersion
      · simp only [_root_.guard, hv, ↓reduceIte]; (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
      · simp only [_root_.guard, hv, ↓reduceIte]; (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem b4_receiveSignalMsg_some_iff {msgIdx : Nat} {tr : ExecTrace} {msg : TRSignalMsg} :
    ((receiveSignalMsg msgIdx).run tr).1 = some msg ↔
      ∃ t, tr.getMessageSentAt msgIdx = some t ∧
        parseTrSignalMsg t = some msg ∧ msg.version = messageVersion := by
  unfold receiveSignalMsg
  rw [b4_run_bind_fst, b4_receiveMessage_fst, b4_receiveMessage_snd]
  constructor
  · intro h
    rcases hmsg : tr.getMessageSentAt msgIdx with _ | t
    · rw [hmsg] at h; cases h
    · rw [hmsg] at h; dsimp only at h
      rcases hp : parseTrSignalMsg t with _ | m
      · rw [hp] at h; dsimp only at h; rw [Traceful.run_failure] at h; cases h
      · rw [hp] at h; dsimp only at h
        by_cases hv : m.version = messageVersion
        · simp only [_root_.guard, hv, ↓reduceIte, b4_run_bind_fst, Traceful.run_pure] at h
          injection h with h
          subst h
          exact ⟨t, rfl, hp, hv⟩
        · simp only [_root_.guard, hv, ↓reduceIte, b4_run_bind_fst, Traceful.run_failure] at h
          cases h
  · rintro ⟨t, hmsg, hp, hv⟩
    rw [hmsg]; dsimp only
    rw [hp]; dsimp only
    simp only [_root_.guard, hv, ↓reduceIte, b4_run_bind_fst, Traceful.run_pure]

private theorem b4_verifyMacAndDecrypt_snd (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) (tr : ExecTrace) :
    ((verifyMacAndDecrypt st msg pqSalt seed).run tr).2.val = tr := by
  unfold verifyMacAndDecrypt
  by_cases hm : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire
  · simp only [_root_.guard, hm, ↓reduceIte, b4_run_bind_snd, Traceful.run_pure]
    dsimp only [liftM, monadLift, MonadLift.monadLift]
    rcases DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext <;>
      simp only [Traceful.run_mk, Traceful.run_pure]
  · simp only [_root_.guard, hm, ↓reduceIte, b4_run_bind_snd, Traceful.run_failure]

private theorem b4_verifyMacAndDecrypt_some_iff {st : TRState} {msg : TRSignalMsg}
    {pqSalt seed ptTerm : DY.Bytes} {tr : ExecTrace} :
    ((verifyMacAndDecrypt st msg pqSalt seed).run tr).1 = some ptTerm ↔
      msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire ∧
        DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
          msg.ciphertext = some ptTerm := by
  unfold verifyMacAndDecrypt
  by_cases hm : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire
  · simp only [_root_.guard, hm, ↓reduceIte, b4_run_bind_fst, Traceful.run_pure, true_and]
    dsimp only [liftM, monadLift, MonadLift.monadLift]
    rcases hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext with _ | pt
    · simp only [Traceful.run_mk]
    · simp only [Traceful.run_mk]
  · simp only [_root_.guard, hm, ↓reduceIte, b4_run_bind_fst, Traceful.run_failure, false_and]
    constructor
    · intro h; cases h
    · intro h; exact False.elim h

/-! ## Pure trace of `logSkippedKeys` and `messageDecrypt` tail -/

private def b4_logSkippedKeysTr (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat) :
    DY.Bytes → UInt32 → Nat → ExecTrace → ExecTrace
  | _, _, 0, tr => tr
  | ck, n, k + 1, tr =>
    b4_logSkippedKeysTr s pk rIdx sourceStateIdx (kdfCk ck).1 (n + 1) k
      (tr.append (⟨TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx⟩ : B4TREntry))

private theorem b4_logSkippedKeys_run (s : SessionInfo) (pk : DY.Bytes)
    (rIdx sourceStateIdx : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    ((logSkippedKeys s pk rIdx sourceStateIdx ck n k).run tr).1 = some () ∧
      ((logSkippedKeys s pk rIdx sourceStateIdx ck n k).run tr).2.val =
        b4_logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr := by
  induction k generalizing ck n tr with
  | zero => unfold logSkippedKeys b4_logSkippedKeysTr; simp [Traceful.run_pure]
  | succ k ih =>
    unfold logSkippedKeys b4_logSkippedKeysTr
    have hlog : ((DY.ProtocolEvent.logEvent (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx)).run tr).1 = some () ∧
        ((DY.ProtocolEvent.logEvent (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx)).run tr).2.val =
          tr.append (⟨TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx⟩ : B4TREntry) := by
      simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
    rw [b4_run_bind_fst, b4_run_bind_snd, hlog.1, hlog.2]
    exact ih (kdfCk ck).1 (n + 1) _

private theorem b4_logSkippedKeysTr_length (s : SessionInfo) (pk : DY.Bytes)
    (rIdx sourceStateIdx : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    (b4_logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).length = tr.length + k := by
  induction k generalizing ck n tr with
  | zero => unfold b4_logSkippedKeysTr; omega
  | succ k ih =>
    unfold b4_logSkippedKeysTr
    rw [ih, b4_length_append]; omega

private theorem b4_newRandoms_logSkippedKeysTr {tr0 tr : ExecTrace} (hle : tr0.length ≤ tr.length)
    (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    newRandoms tr0 (b4_logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr) =
      newRandoms tr0 tr := by
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih =>
    unfold b4_logSkippedKeysTr
    rw [ih (by rw [b4_length_append]; omega),
        b4_newRandoms_append_of_proj hle _ rfl]

private theorem b4_receivedPlaintext_logSkippedKeysTr {tr0 tr : ExecTrace}
    (hle : tr0.length ≤ tr.length) (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    receivedPlaintext tr0 (b4_logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr) =
      receivedPlaintext tr0 tr := by
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih =>
    unfold b4_logSkippedKeysTr
    rw [ih (by rw [b4_length_append]; omega),
        b4_receivedPlaintext_append hle]
    have hnone : b4_receivedAt
        (tr.append (⟨TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx⟩ : B4TREntry))
        tr.length = none := by
      simp [b4_receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, b4_at?_append_self]
    rw [hnone, Option.or_none]

private def b4_decTailTr (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes)
    (n : UInt32) : ExecTrace :=
  let tr_sk := b4_logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  let tr_rcv := tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : B4TREntry)
  (tr_rcv.append
    (⟨TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stateIdx⟩ : B4TREntry)).append
    (⟨⟨me, { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }⟩⟩ : B4StEntry)

private theorem b4_newRandoms_decTailTr {tr0 tr_pre : ExecTrace} (hle : tr0.length ≤ tr_pre.length)
    (me : Participant) (stateIdx : Nat) (st1 : TRState) (c c' : RecvChain)
    (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    newRandoms tr0 (b4_decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n) =
      newRandoms tr0 tr_pre := by
  unfold b4_decTailTr; dsimp only
  let tr_sk := b4_logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  have hlen_sk : tr_sk.length = tr_pre.length + (n.toNat - c.index.toNat) :=
    b4_logSkippedKeysTr_length ..
  dsimp only [tr_sk] at hlen_sk
  rw [b4_newRandoms_append_of_proj (by simp only [b4_length_append]; omega) _ rfl,
      b4_newRandoms_append_of_proj (by simp only [b4_length_append]; omega) _ rfl,
      b4_newRandoms_append_of_proj (by omega) _ rfl,
      b4_newRandoms_logSkippedKeysTr hle]

private theorem b4_receivedPlaintext_decTailTr {tr0 tr_pre : ExecTrace}
    (hle : tr0.length ≤ tr_pre.length) (hpre : receivedPlaintext tr0 tr_pre = none)
    (me : Participant) (stateIdx : Nat) (st1 : TRState) (c c' : RecvChain)
    (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    receivedPlaintext tr0
      (b4_decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n) = some ptTerm := by
  unfold b4_decTailTr; dsimp only
  let tr_sk := b4_logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  have hlen_sk : tr_sk.length = tr_pre.length + (n.toNat - c.index.toNat) :=
    b4_logSkippedKeysTr_length ..
  dsimp only [tr_sk] at hlen_sk
  rw [b4_receivedPlaintext_append_of_proj (by simp only [b4_length_append]; omega) _ rfl]
  rw [b4_receivedPlaintext_append (by simp only [b4_length_append]; omega)]
  have hmk : b4_receivedAt
      ((tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : B4TREntry)).append
        (⟨TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stateIdx⟩ : B4TREntry))
      (tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : B4TREntry)).length = none := by
    simp only [b4_receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, b4_at?_append_self]
  rw [hmk, Option.or_none]
  rw [b4_receivedPlaintext_append (by omega)]
  have hsk : receivedPlaintext tr0 tr_sk = none := by
    rw [b4_receivedPlaintext_logSkippedKeysTr hle, hpre]
  have hrcv : b4_receivedAt (tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : B4TREntry))
      tr_sk.length = some ptTerm := by
    simp only [b4_receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, b4_at?_append_self]
  dsimp only [tr_sk] at hsk hrcv
  simp only [hsk, hrcv, Option.none_or]

/-! ## Visible-entry kind characterizations -/

/-- Every entry in `exposures tr tr'` has kind `.leak`. -/
theorem exposures_kind_eq_leak {tr tr' : ExecTrace} {v : VisEntry}
    (hv : v ∈ exposures tr tr') : v.kind = .leak := by
  unfold exposures at hv
  rw [List.mem_append] at hv
  rcases hv with hv | hv
  · rw [List.mem_filterMap] at hv
    rcases hv with ⟨j, _, hj⟩
    unfold pqExposureAt at hj
    split at hj <;> simp only [Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;> rfl
  · rw [List.mem_filterMap] at hv
    rcases hv with ⟨j, _, hj⟩
    unfold trExposureAt at hj
    split at hj <;> simp only [Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;> rfl

/-- `decVis` has no `.rng` entry iff `newRandoms tr tr' = []`. -/
theorem newRandoms_eq_nil_iff_no_rng_decVis
    (tr tr' : ExecTrace) (stateIdx msgIdx : Nat) (wrapped : Bool) :
    (∀ v ∈ decVis tr tr' stateIdx msgIdx wrapped, v.kind ≠ .rng) ↔ newRandoms tr tr' = [] := by
  constructor
  · intro h
    cases hnr : newRandoms tr tr' with
    | nil => rfl
    | cons r rs =>
      exfalso
      have hmem : rngEntry r.1 ∈ decVis tr tr' stateIdx msgIdx wrapped := by
        unfold decVis
        rw [hnr]
        simp [List.mem_append]
      exact h (rngEntry r.1) hmem rfl
  · intro hnr v hv
    unfold decVis at hv
    rw [hnr] at hv
    simp only [List.map_nil, List.append_nil, List.mem_append] at hv
    rcases hv with hv | hv
    · cases hmsg : tr.getMessageSentAt msgIdx <;> simp [hmsg] at hv
      subst hv; rintro ⟨⟩
    · cases hpt : receivedPlaintext tr tr' <;> simp [hpt] at hv
      subst hv; rintro ⟨⟩

/-- `(Move.decrypt ...).vis tr` has no `.rng` entry iff `newRandoms tr (m.next tr) = []`. -/
theorem newRandoms_eq_nil_iff_no_rng_vis_decrypt
    (me : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32)
    (wrapped : Bool) (tr : ExecTrace) :
    (∀ v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr, v.kind ≠ .rng) ↔
      newRandoms tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) = [] := by
  change (∀ v ∈ decVis tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr)
      stateIdx msgIdx wrapped ++ exposures tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr),
      v.kind ≠ .rng) ↔ _
  rw [← newRandoms_eq_nil_iff_no_rng_decVis tr _ stateIdx msgIdx wrapped]
  constructor
  · intro h v hv
    exact h v (List.mem_append_left _ hv)
  · intro h v hv
    rw [List.mem_append] at hv
    rcases hv with hv | hv
    · exact h v hv
    · rw [exposures_kind_eq_leak hv]; rintro ⟨⟩

/-- `decVis` has an `.accept` entry iff `(receivedPlaintext tr tr').isSome`. -/
theorem accept_in_decVis_iff_receivedPlaintext_isSome
    (tr tr' : ExecTrace) (stateIdx msgIdx : Nat) (wrapped : Bool) :
    (∃ v ∈ decVis tr tr' stateIdx msgIdx wrapped, v.kind = .accept) ↔
      ∃ ptTerm, receivedPlaintext tr tr' = some ptTerm := by
  constructor
  · rintro ⟨v, hv, hkind⟩
    unfold decVis at hv
    simp only [List.mem_append] at hv
    rcases hv with (hv | hv) | hv
    · cases hmsg : tr.getMessageSentAt msgIdx <;> simp [hmsg] at hv
      subst hv; cases hkind
    · rw [List.mem_map] at hv
      rcases hv with ⟨r, _, rfl⟩
      cases hkind
    · cases hpt : receivedPlaintext tr tr' with
      | none => simp [hpt] at hv
      | some ptTerm => exact ⟨ptTerm, rfl⟩
  · rintro ⟨ptTerm, hpt⟩
    refine ⟨⟨.accept, [ptTerm], .single, none⟩, ?_, rfl⟩
    unfold decVis
    rw [hpt]
    simp [List.mem_append]

/-- `(Move.decrypt ...).vis tr` has an `.accept` entry iff `receivedPlaintext` is `some`. -/
theorem accept_in_vis_decrypt_iff_receivedPlaintext_isSome
    (me : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32)
    (wrapped : Bool) (tr : ExecTrace) :
    (∃ v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr, v.kind = .accept) ↔
      ∃ ptTerm, receivedPlaintext tr
        ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) = some ptTerm := by
  change (∃ v ∈ decVis tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr)
      stateIdx msgIdx wrapped ++ exposures tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr),
      v.kind = .accept) ↔ _
  rw [← accept_in_decVis_iff_receivedPlaintext_isSome _ _ stateIdx msgIdx wrapped]
  constructor
  · rintro ⟨v, hv, hk⟩
    rw [List.mem_append] at hv
    rcases hv with hv | hv
    · exact ⟨v, hv, hk⟩
    · rw [exposures_kind_eq_leak hv] at hk; cases hk
  · rintro ⟨v, hv, hk⟩
    exact ⟨v, List.mem_append_left _ hv, hk⟩

/-! ## Step behavior of `ensureReceiverChain` and `messageDecrypt` -/

private def b4_trDhRatchetState (st : TRState) (theirPk : DY.Bytes) (rngIdx : Nat) :
    TRState × RecvChain :=
  let (rk1, ckr) := createChain st.rk theirPk st.dhs
  let dhs := randTerm rngIdx 32
  let (rk2, cks) := createChain rk1 theirPk dhs
  let c : RecvChain := { ratchetKey := theirPk, chainKey := ckr, index := 0, rIdx := st.rIdx + 2 }
  let recv := (st.recv ++ [c]).drop ((st.recv.length + 1) - maxReceiverChains)
  let pn := if st.ns = 0 then 0 else st.ns - 1
  ({ st with rk := rk2, dhs, cks, ns := 0, pn, rIdx := st.rIdx + 2, recv }, c)

private theorem b4_dhRatchetStep_run {st : TRState} {pk : DY.Bytes}
    (tr : ExecTrace) (hlow : x25519LowOrder pk = false) :
    ((dhRatchetStep st pk).run tr).1 = some (b4_trDhRatchetState st pk tr.length) ∧
      ((dhRatchetStep st pk).run tr).2.val = tr.append (⟨32⟩ : DY.Random.ExecEntryT) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]; unfold b4_trDhRatchetState
  have hg1 : ((_root_.guard (!x25519LowOrder pk) : Traceful Unit).run tr).1 = some () := by
    simp only [_root_.guard, hlow, Bool.not_false, ↓reduceIte, Traceful.run_pure]
  have hg2 : ((_root_.guard (!x25519LowOrder pk) : Traceful Unit).run tr).2.val = tr := by
    simp only [_root_.guard, hlow, Bool.not_false, ↓reduceIte, Traceful.run_pure]
  rw [b4_run_bind_fst, b4_run_bind_snd, hg1, hg2]; dsimp only
  have hr1 : ((DY.Random.genRand 32).run tr).1 = some (randTerm tr.length 32) := by
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]; rfl
  have hr2 : ((DY.Random.genRand 32).run tr).2.val = tr.append (⟨32⟩ : DY.Random.ExecEntryT) := by
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  rw [b4_run_bind_fst, b4_run_bind_snd, hr1, hr2]; dsimp only
  simp [Traceful.run_pure]

/-- When `recvChainFor st.toDRState msg.ratchetKey = some (c, true)`, `Move.decrypt` always draws
`(randTerm tr.length 32, 32)` as its sole `newRandoms` entry (whether later steps succeed or fail). -/
theorem newRandoms_decrypt_of_recvChainFor_true
    {me : Participant} {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    {tr : ExecTrace} {st : TRState} {msg : TRSignalMsg} {c : RecvChain}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hmsg : ((receiveSignalMsg msgIdx).run tr).1 = some msg)
    (hrc : recvChainFor st.toDRState msg.ratchetKey = some (c, true)) :
    newRandoms tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) =
      [(randTerm tr.length 32, 32)] := by
  have hrc' := hrc
  unfold recvChainFor TRState.toDRState at hrc'
  rcases hfind : findRecvChain st.recv msg.ratchetKey with _ | c0
  · rw [hfind] at hrc'
    rcases hlow : x25519LowOrder msg.ratchetKey with _ | _
    · obtain ⟨hd1, hd2⟩ := b4_dhRatchetStep_run (st := st) tr hlow
      have hens1 : ((ensureReceiverChain st msg.ratchetKey).run tr).1 =
          some ((b4_trDhRatchetState st msg.ratchetKey tr.length).1,
            (b4_trDhRatchetState st msg.ratchetKey tr.length).2, true) := by
        simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor TRState.toDRState; dsimp only
        rw [hfind]; simp only [hlow, Bool.false_eq_true, ↓reduceIte]
        rw [b4_run_bind_fst, hd1, hd2]; (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
      have hens2 : ((ensureReceiverChain st msg.ratchetKey).run tr).2.val =
          tr.append (⟨32⟩ : DY.Random.ExecEntryT) := by
        simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor TRState.toDRState; dsimp only
        rw [hfind]; simp only [hlow, Bool.false_eq_true, ↓reduceIte]
        rw [b4_run_bind_snd, hd1, hd2]; (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
      let st1 := (b4_trDhRatchetState st msg.ratchetKey tr.length).1
      let c1 := (b4_trDhRatchetState st msg.ratchetKey tr.length).2
      let tr_r := tr.append (⟨32⟩ : DY.Random.ExecEntryT)
      have hnr_r : newRandoms tr tr_r = [(randTerm tr.length 32, 32)] := by
        dsimp only [tr_r]
        rw [b4_newRandoms_append_rnd (Nat.le_refl _) 32, b4_newRandoms_self, List.nil_append]
      unfold Move.next Move.act
      rw [b4_run_bind_pure_val]
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
      rw [b4_run_bind_snd, hst, b4_getLocalState_snd]; dsimp only
      rw [b4_run_bind_snd, hmsg, b4_receiveSignalMsg_snd]; dsimp only
      rw [b4_run_bind_snd, hens1, hens2]; dsimp only
      rcases hcons : consumeMessageKey c1 msg.counter with _ | ⟨seed, c'⟩
      · dsimp only; rw [Traceful.run_failure]; exact hnr_r
      · dsimp only
        rcases hspqr : Spqr.spqrRecv st1.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
        · dsimp only; rw [Traceful.run_failure]; exact hnr_r
        · dsimp only
          let tr_k := tr_r.append (⟨key⟩ : Network.ExecEntryT)
          have hsm1 : ((DY.Network.sendMessage key).run tr_r).1 = some tr_r.length := by
            simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
              Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
          have hsm2 : ((DY.Network.sendMessage key).run tr_r).2.val = tr_k := by
            simp only [tr_k, Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
              Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
          have hnr_k : newRandoms tr tr_k = [(randTerm tr.length 32, 32)] := by
            dsimp only [tr_k]
            rw [b4_newRandoms_append_of_proj (by dsimp only [tr_r]; rw [b4_length_append]; omega) _ rfl, hnr_r]
          rw [b4_run_bind_snd, hsm1, hsm2]; dsimp only
          rw [b4_run_bind_snd, b4_receiveMessage_snd]
          rcases ((DY.Network.receiveMessage pqIdx).run tr_k).1 with _ | pqSalt
          · exact hnr_k
          · dsimp only
            rw [b4_run_bind_snd, b4_verifyMacAndDecrypt_snd]
            rcases ((verifyMacAndDecrypt st1 msg pqSalt seed).run tr_k).1 with _ | ptTerm
            · exact hnr_k
            · dsimp only; simp only [↓reduceIte]
              let tr_pre := (tr_k.append
                (⟨TREvent.DHRatchet me st1.peer msg.ratchetKey (DY.DiffieHellman.dhPk st1.dhs)⟩ : B4TREntry)).append
                (⟨TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2)⟩ : B4TREntry)
              obtain ⟨hsk1, hsk2⟩ := b4_logSkippedKeys_run (st1.sessionInfo me) msg.ratchetKey c1.rIdx stateIdx
                c1.chainKey c1.index (msg.counter.toNat - c1.index.toNat) tr_pre
              have hlog1 : ((DY.ProtocolEvent.logEvent (TREvent.DHRatchet me st1.peer msg.ratchetKey (DY.DiffieHellman.dhPk st1.dhs))).run tr_k).1 = some () ∧
                  ((DY.ProtocolEvent.logEvent (TREvent.DHRatchet me st1.peer msg.ratchetKey (DY.DiffieHellman.dhPk st1.dhs))).run tr_k).2.val =
                    tr_k.append (⟨TREvent.DHRatchet me st1.peer msg.ratchetKey (DY.DiffieHellman.dhPk st1.dhs)⟩ : B4TREntry) := by
                simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                  Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
              have hlog2 : ((DY.ProtocolEvent.logEvent (TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2))).run
                  (tr_k.append (⟨TREvent.DHRatchet me st1.peer msg.ratchetKey (DY.DiffieHellman.dhPk st1.dhs)⟩ : B4TREntry))).1 = some () ∧
                  ((DY.ProtocolEvent.logEvent (TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2))).run
                    (tr_k.append (⟨TREvent.DHRatchet me st1.peer msg.ratchetKey (DY.DiffieHellman.dhPk st1.dhs)⟩ : B4TREntry))).2.val = tr_pre := by
                dsimp only [tr_pre]
                simp [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                  Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
              rw [b4_run_bind_snd, hlog1.1, hlog1.2]; dsimp only
              rw [b4_run_bind_snd, hlog2.1, hlog2.2]; dsimp only
              rw [b4_run_bind_snd, hsk1, hsk2]
              have htail : ((fun _ =>
                  DY.ProtocolEvent.logEvent (TREvent.Received me st1.peer msg.ratchetKey msg.counter ptTerm) >>= fun _ =>
                  logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed pqSalt msg.counter
                    c1.rIdx stateIdx { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }) ()).run
                  (b4_logSkippedKeysTr (st1.sessionInfo me) msg.ratchetKey c1.rIdx stateIdx c1.chainKey c1.index
                    (msg.counter.toNat - c1.index.toNat) tr_pre) |>.2.val =
                  b4_decTailTr tr_pre me stateIdx st1 c1 c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter := by
                unfold logMessageKeyAndStore b4_decTailTr
                simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                  Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
                  Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
                  Symbolic.DYBridge.DY.appendEntry_eq_1,
                  Traceful.run_bind, Traceful.run_mk, Traceful.run_pure, b4_length_append]
              dsimp only; rw [htail]
              rw [b4_newRandoms_decTailTr (by dsimp only [tr_pre, tr_k, tr_r]; simp only [b4_length_append]; omega)]
              dsimp only [tr_pre]
              rw [b4_newRandoms_append_of_proj (by dsimp only [tr_k, tr_r]; simp only [b4_length_append]; omega) _ rfl,
                  b4_newRandoms_append_of_proj (by dsimp only [tr_k, tr_r]; simp only [b4_length_append]; omega) _ rfl,
                  hnr_k]
    · simp [hlow] at hrc'
  · rw [hfind] at hrc'
    simp at hrc'

/-- If `Move.decrypt` has no `.rng` entry in `m.vis tr`, any `recvChainFor` hit has `b = false` and
`findRecvChain st.recv msg.ratchetKey = some c`. -/
theorem noRatchet_of_rngFree_recvChainFor
    {me : Participant} {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    {tr : ExecTrace} {st : TRState} {msg : TRSignalMsg} {c : RecvChain} {b : Bool}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hmsg : ((receiveSignalMsg msgIdx).run tr).1 = some msg)
    (hrc : recvChainFor st.toDRState msg.ratchetKey = some (c, b))
    (hno_rng : ∀ v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind ≠ .rng) :
    b = false ∧
      recvChainFor st.toDRState msg.ratchetKey = some (c, false) ∧
      findRecvChain st.recv msg.ratchetKey = some c := by
  have hnr : newRandoms tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) = [] :=
    (newRandoms_eq_nil_iff_no_rng_vis_decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped tr).mp hno_rng
  cases b with
  | false =>
    refine ⟨rfl, hrc, ?_⟩
    rcases hfind : findRecvChain st.recv msg.ratchetKey with _ | c0
    · rcases hlow : x25519LowOrder msg.ratchetKey with _ | _ <;>
        simp [recvChainFor, hfind, hlow] at hrc
    · simp only [recvChainFor, hfind, Option.some.injEq, Prod.mk.injEq,
        and_true] at hrc
      subst hrc; rfl
  | true =>
    have h1 := newRandoms_decrypt_of_recvChainFor_true (wrapped := wrapped)
      (pqIdx := pqIdx) (spqrMsgIdx := spqrMsgIdx) hst hmsg hrc
    rw [hnr] at h1
    cases h1

theorem index_le_of_consumeMessageKey_some {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (hcons : consumeMessageKey c counter = some (seed, c')) :
    c.index ≤ counter := by
  unfold consumeMessageKey at hcons
  by_cases hlt : counter < c.index
  · simp [hlt] at hcons
  · exact UInt32.not_lt.mp hlt

/-- An accepting `Move.decrypt` with no `.rng` entry in `m.vis tr` reuses an existing receiving
chain (`recvChainFor st.toDRState msg.ratchetKey = some (c, false)`) and succeeds through
`consumeMessageKey`, `spqrRecv`, and `verifyMacAndDecrypt`. -/
theorem noRatchet_of_rngFree
    {me : Participant} {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    {tr : ExecTrace}
    (hno_rng : ∀ v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind ≠ .rng)
    (hacc : ∃ v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind = .accept) :
    ∃ (st : TRState) (t : DY.Bytes) (msg : TRSignalMsg) (c c' : RecvChain)
      (seed spqr' key pqSalt ptTerm : DY.Bytes),
      ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st ∧
      tr.getMessageSentAt msgIdx = some t ∧
      parseTrSignalMsg t = some msg ∧
      msg.version = messageVersion ∧
      recvChainFor st.toDRState msg.ratchetKey = some (c, false) ∧
      findRecvChain st.recv msg.ratchetKey = some c ∧
      c.index ≤ msg.counter ∧
      consumeMessageKey c msg.counter = some (seed, c') ∧
      Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key) ∧
      ((tr.append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) =
        some ⟨pqSalt⟩ ∧
      msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
        msg.ciphertext = some ptTerm ∧
      receivedPlaintext tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) =
        some ptTerm := by
  obtain ⟨ptTerm0, hpt0⟩ :=
    (accept_in_vis_decrypt_iff_receivedPlaintext_isSome me stateIdx msgIdx pqIdx spqrMsgIdx
      wrapped tr).mp hacc
  have hpt_eq := hpt0
  unfold Move.next Move.act at hpt0
  rw [b4_run_bind_pure_val] at hpt0
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline] at hpt0
  rw [b4_run_bind_snd, b4_getLocalState_snd] at hpt0
  rcases hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with _ | st
  · rw [hst, b4_receivedPlaintext_self] at hpt0; cases hpt0
  · rw [hst] at hpt0; dsimp only at hpt0
    rw [b4_run_bind_snd, b4_receiveSignalMsg_snd] at hpt0
    rcases hmsg : ((receiveSignalMsg msgIdx).run tr).1 with _ | msg
    · rw [hmsg, b4_receivedPlaintext_self] at hpt0; cases hpt0
    · rw [hmsg] at hpt0; dsimp only at hpt0
      obtain ⟨t, ht_sent, hparse, hver⟩ := b4_receiveSignalMsg_some_iff.mp hmsg
      rcases hrc : recvChainFor st.toDRState msg.ratchetKey with _ | ⟨c, b⟩
      · have hens_none : ((ensureReceiverChain st msg.ratchetKey).run tr).1 = none ∧
            ((ensureReceiverChain st msg.ratchetKey).run tr).2.val = tr := by
          simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; rw [hrc]; dsimp only; simp [Traceful.run_failure]
        rw [b4_run_bind_snd, hens_none.1, hens_none.2, b4_receivedPlaintext_self] at hpt0
        cases hpt0
      · obtain ⟨hb, hrc_false, hfind⟩ :=
          noRatchet_of_rngFree_recvChainFor hst hmsg hrc hno_rng
        subst hb
        have hens : ((ensureReceiverChain st msg.ratchetKey).run tr).1 = some (st, c, false) ∧
            ((ensureReceiverChain st msg.ratchetKey).run tr).2.val = tr := by
          simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; rw [hrc_false]; dsimp only; simp [Traceful.run_pure]
        rw [b4_run_bind_snd, hens.1, hens.2] at hpt0; dsimp only at hpt0
        rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
        · rw [hcons] at hpt0; dsimp only at hpt0
          rw [Traceful.run_failure, b4_receivedPlaintext_self] at hpt0; cases hpt0
        · rw [hcons] at hpt0; dsimp only at hpt0
          rcases hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
          · rw [hspqr] at hpt0; dsimp only at hpt0
            rw [Traceful.run_failure, b4_receivedPlaintext_self] at hpt0; cases hpt0
          · rw [hspqr] at hpt0; dsimp only at hpt0
            let tr_k := tr.append (⟨key⟩ : Network.ExecEntryT)
            have hsm1 : ((DY.Network.sendMessage key).run tr).1 = some tr.length := by
              simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
                Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
            have hsm2 : ((DY.Network.sendMessage key).run tr).2.val = tr_k := by
              simp only [tr_k, Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
                Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
            have hpt_k : receivedPlaintext tr tr_k = none := by
              dsimp only [tr_k]
              rw [b4_receivedPlaintext_append_of_proj (Nat.le_refl _) _ rfl, b4_receivedPlaintext_self]
            rw [b4_run_bind_snd, hsm1, hsm2] at hpt0; dsimp only at hpt0
            rw [b4_run_bind_snd, b4_receiveMessage_snd] at hpt0
            rcases hpq : ((DY.Network.receiveMessage pqIdx).run tr_k).1 with _ | pqSalt
            · rw [hpq, hpt_k] at hpt0; cases hpt0
            · rw [hpq] at hpt0; dsimp only at hpt0
              have hpq_at : (tr_k.at? pqIdx : Option Network.ExecEntryT) = some ⟨pqSalt⟩ := by
                rw [b4_receiveMessage_fst] at hpq
                simpa only [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1] using
                  (Trace.MessageSentAt_eq_getMessageSentAt pqSalt pqIdx tr_k).mpr hpq
              rw [b4_run_bind_snd, b4_verifyMacAndDecrypt_snd] at hpt0
              rcases hv : ((verifyMacAndDecrypt st msg pqSalt seed).run tr_k).1 with _ | ptTerm
              · rw [hv, hpt_k] at hpt0; cases hpt0
              · obtain ⟨hmac_eq, hdec⟩ := b4_verifyMacAndDecrypt_some_iff.mp hv
                refine ⟨st, t, msg, c, c', seed, spqr', key, pqSalt, ptTerm,
                  rfl, ht_sent, hparse, hver, hrc_false, hfind,
                  index_le_of_consumeMessageKey_some hcons, hcons, hspqr, hpq_at, hmac_eq, hdec, ?_⟩
                rw [hv] at hpt0; dsimp only at hpt0
                simp only [Bool.false_eq_true, ↓reduceIte] at hpt0
                obtain ⟨hsk1, hsk2⟩ := b4_logSkippedKeys_run (st.sessionInfo me) msg.ratchetKey c.rIdx
                  stateIdx c.chainKey c.index (msg.counter.toNat - c.index.toNat) tr_k
                rw [b4_run_bind_snd, hsk1, hsk2] at hpt0
                have htail : ((fun _ =>
                    DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter ptTerm) >>= fun _ =>
                    logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter
                      c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) ()).run
                    (b4_logSkippedKeysTr (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                      (msg.counter.toNat - c.index.toNat) tr_k) |>.2.val =
                    b4_decTailTr tr_k me stateIdx st c c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter := by
                  unfold logMessageKeyAndStore b4_decTailTr
                  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
                    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
                    Symbolic.DYBridge.DY.appendEntry_eq_1,
                    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure, b4_length_append]
                dsimp only at hpt0; rw [htail] at hpt0
                rw [b4_receivedPlaintext_decTailTr (by dsimp only [tr_k]; rw [b4_length_append]; omega) hpt_k] at hpt0
                injection hpt0 with hpt_same
                subst hpt_same
                exact hpt_eq

private theorem b4_forall₂_mem_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => cases hy
  | cons hr _ ih =>
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨x, hx, hxy⟩ := ih hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩

private theorem b4_forall₂_mem_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => cases hx
  | cons hr _ ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨y, hy, hxy⟩ := ih hx'
      exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

/-- Corollary of `noRatchet_of_rngFree` for a hardware event block `blk` matched by
`List.Forall₂ (EventMatchesEntry interpretation r S g) blk (m.vis tr)`. -/
theorem noRatchet_of_matched
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {me : Participant} {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    {tr : ExecTrace} {blk : List HwEvents.MachineEvent}
    (hmatch : List.Forall₂ (EventMatchesEntry interpretation r S g) blk
      ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr))
    (hno_rng : ∀ e ∈ blk, eventKind e ≠ .rng)
    (hacc : ∃ e ∈ blk, eventKind e = .accept) :
    ∃ (st : TRState) (t : DY.Bytes) (msg : TRSignalMsg) (c c' : RecvChain)
      (seed spqr' key pqSalt ptTerm : DY.Bytes),
      ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st ∧
      tr.getMessageSentAt msgIdx = some t ∧
      parseTrSignalMsg t = some msg ∧
      msg.version = messageVersion ∧
      recvChainFor st.toDRState msg.ratchetKey = some (c, false) ∧
      findRecvChain st.recv msg.ratchetKey = some c ∧
      c.index ≤ msg.counter ∧
      consumeMessageKey c msg.counter = some (seed, c') ∧
      Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key) ∧
      ((tr.append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) =
        some ⟨pqSalt⟩ ∧
      msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
        msg.ciphertext = some ptTerm ∧
      receivedPlaintext tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) =
        some ptTerm := by
  have hno_rng_vis : ∀ v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind ≠ .rng := by
    intro v hv
    obtain ⟨e, he, hev⟩ := b4_forall₂_mem_right hmatch hv
    rw [← hev.1]
    exact hno_rng e he
  have hacc_vis : ∃ v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind = .accept := by
    obtain ⟨e, he, hk⟩ := hacc
    obtain ⟨v, hv, hev⟩ := b4_forall₂_mem_left hmatch he
    exact ⟨v, hv, hev.1.symm.trans hk⟩
  exact noRatchet_of_rngFree hno_rng_vis hacc_vis

end Symbolic.Swarm.CREF
