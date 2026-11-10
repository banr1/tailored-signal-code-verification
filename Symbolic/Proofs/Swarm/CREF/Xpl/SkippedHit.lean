/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

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
import Mathlib.Tactic.Push
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
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
# Skipped-Key Decrypt Unpacking

Proves `skippedHit_of_decryptSkipped`: an accepting `Move.decryptSkipped` step hits an unused
`TREvent.SkippedKeyStored` entry matching `(st.sessionInfo me, msg.ratchetKey, msg.counter)` and
decrypts under the stored seed.
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
open DY.Libsignal.TripleRatchet (computeMac messageVersion)
open Symbolic.Swarm.COMPOSED

private abbrev B4StEntry :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
private abbrev B4TREntry := DY.ProtocolEvent.ExecEntryT TREvent

/-! ## Trace-append algebra -/

private theorem b4_length_append {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem b4_at?_append_lt {E E2 : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) :=
  CompTrace.at?_append_of_lt tr e hi

private theorem b4_at?_append_length {E E2 : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E) :
    ((tr.append e).at? tr.length : Option E2) =
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  have hlt : tr.length < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  simp only [Trace.at?, hlt, ↓reduceDIte]
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

private theorem b4_at?_append_self {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    ((tr.append e).at? tr.length : Option E) = some e :=
  CompTrace.at?_append_here tr e

private theorem b4_getEventAt_append_lt {E : Type} [ExecTraceTypes.Has E]
    (EventT : Type) [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
    (tr : ExecTrace) (e : E) {i : Nat} (hi : i < tr.length) :
    (tr.append e).getEventAt EventT i = tr.getEventAt EventT i := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, b4_at?_append_lt tr e hi]

private theorem b4_receivedPlaintext_self (tr : ExecTrace) : receivedPlaintext tr tr = none := by
  simp [receivedPlaintext, newIndices]

private theorem b4_mem_newIndices {tr0 tr : ExecTrace} {i : Nat} :
    i ∈ newIndices tr0 tr ↔ tr0.length ≤ i ∧ i < tr.length := by
  simp only [newIndices, List.mem_range'_1]; omega

private theorem b4_newIndices_append {E : Type} [ExecTraceTypes.Has E]
    {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E) :
    newIndices tr0 (tr.append e) = newIndices tr0 tr ++ [tr.length] := by
  simp only [newIndices, b4_length_append]
  rw [show tr.length + 1 - tr0.length = (tr.length - tr0.length) + 1 by omega, List.range'_concat]
  congr 2; omega

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
      (newIndices tr0 tr).findSome? (b4_receivedAt tr) :=
    b4_findSome?_congr fun i hi => b4_receivedAt_append_lt tr e (b4_mem_newIndices.mp hi).2
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
      | none => none :=
  CompTrace.run_bind_fst x f tr

private theorem b4_run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val :=
  CompTrace.run_bind_snd x f tr

private theorem b4_run_bind_pure_val {α : Type} (m : Traceful α) (tr : ExecTrace) :
    (((m >>= fun _ => (pure () : Traceful Unit))).run tr).2.val = (m.run tr).2.val := by
  rw [Traceful.run_bind]; rcases m.run tr with ⟨_ | _, _⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem b4_getLocalState_snd (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).2.val = tr :=
  CompTrace.getLocalState_tr_snd me stH tr

private theorem b4_receiveMessage_fst (idx : Nat) (tr : ExecTrace) :
    ((DY.Network.receiveMessage idx).run tr).1 = tr.getMessageSentAt idx := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  rw [b4_run_bind_fst, Traceful.run_mk]
  rcases (tr.at? idx : Option Network.ExecEntryT) with _ | ⟨t⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem b4_receiveMessage_snd (idx : Nat) (tr : ExecTrace) :
    ((DY.Network.receiveMessage idx).run tr).2.val = tr :=
  CompTrace.receiveMessage_snd idx tr

private theorem b4_receiveSignalMsg_snd (msgIdx : Nat) (tr : ExecTrace) :
    ((receiveSignalMsg msgIdx).run tr).2.val = tr :=
  CompTrace.Preserves.receiveSignalMsg (Inv := fun t => t = tr) msgIdx tr rfl

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
        · simp only [_root_.guard, hv, ↓reduceIte, Traceful.run_bind, Traceful.run_pure] at h
          injection h with h; subst h; exact ⟨t, rfl, hp, hv⟩
        · simp only [_root_.guard, hv, ↓reduceIte, Traceful.run_bind, Traceful.run_failure] at h
          cases h
  · rintro ⟨t, hmsg, hp, hv⟩
    rw [hmsg]; dsimp only; rw [hp]; dsimp only
    simp only [_root_.guard, hv, ↓reduceIte]; (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem b4_verifyMacAndDecrypt_snd (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) (tr : ExecTrace) :
    ((verifyMacAndDecrypt st msg pqSalt seed).run tr).2.val = tr :=
  CompTrace.verifyMacAndDecrypt_trace st msg pqSalt seed tr

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
    · simp only [Traceful.run_mk, reduceCtorEq]
    · simp only [Traceful.run_mk]
  · simp only [_root_.guard, hm, ↓reduceIte, b4_run_bind_fst, Traceful.run_failure,
      reduceCtorEq, false_and]

/-! ## Pure trace of `decSkippedTr` -/

private def b4_decSkippedTr (tr : ExecTrace) (me : Participant) (stateIdx skIdx rIdx _srcIdx : Nat)
    (st : TRState) (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) : ExecTrace :=
  let tr2 := ((tr.append (⟨key⟩ : Network.ExecEntryT)).append
    (⟨TREvent.SkippedKeyUsed (st.sessionInfo me) skIdx⟩ : B4TREntry)).append
    (⟨TREvent.Received me st.peer pk n ptTerm⟩ : B4TREntry)
  (tr2.append
    (⟨TREvent.MessageKey (st.sessionInfo me) .receiver seed pqSalt n rIdx stateIdx⟩ : B4TREntry)).append
    (⟨⟨me, { st with spqr := spqr' }⟩⟩ : B4StEntry)

private theorem b4_receivedPlaintext_decSkippedTr (tr : ExecTrace) (me : Participant)
    (stateIdx skIdx rIdx srcIdx : Nat) (st : TRState)
    (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    receivedPlaintext tr (b4_decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt
      ptTerm spqr' n) = some ptTerm := by
  unfold b4_decSkippedTr; dsimp only
  let tr1 := tr.append (⟨key⟩ : Network.ExecEntryT)
  let tr2 := tr1.append (⟨TREvent.SkippedKeyUsed (st.sessionInfo me) skIdx⟩ : B4TREntry)
  let tr3 := tr2.append (⟨TREvent.Received me st.peer pk n ptTerm⟩ : B4TREntry)
  rw [b4_receivedPlaintext_append_of_proj (by simp only [b4_length_append]; omega) _ rfl]
  rw [b4_receivedPlaintext_append (by simp only [b4_length_append]; omega)]
  have h3 : b4_receivedAt
      (tr3.append (⟨TREvent.MessageKey (st.sessionInfo me) .receiver seed pqSalt n rIdx stateIdx⟩ : B4TREntry))
      tr3.length = none := by
    simp only [b4_receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, b4_at?_append_self]
  dsimp only [tr3, tr2, tr1] at h3
  rw [h3, Option.or_none]
  rw [b4_receivedPlaintext_append (by simp only [b4_length_append]; omega)]
  have h2 : b4_receivedAt tr3 tr2.length = some ptTerm := by
    dsimp only [tr3]; simp only [b4_receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, b4_at?_append_self]
  have h1 : receivedPlaintext tr tr2 = none := by
    dsimp only [tr2, tr1]
    rw [b4_receivedPlaintext_append (by simp only [b4_length_append]; omega),
        b4_receivedPlaintext_append_of_proj (Nat.le_refl _) _ rfl, b4_receivedPlaintext_self]
    simp only [b4_receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, b4_at?_append_self, Option.none_or]
  dsimp only [tr3, tr2, tr1] at h1 h2
  simp only [h1, h2, Option.none_or]

/-! ## `Move.decryptSkipped` unpacking -/

private theorem b4_exposures_kind_eq_leak {tr tr' : ExecTrace} {v : VisEntry}
    (hv : v ∈ exposures tr tr') : v.kind = .leak := by
  unfold exposures at hv
  rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_filterMap.mp hv with ⟨j, _, hj⟩
    unfold pqExposureAt at hj
    split at hj <;> simp only [Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;> rfl
  · rcases List.mem_filterMap.mp hv with ⟨j, _, hj⟩
    unfold trExposureAt at hj
    split at hj <;> simp only [Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;> rfl

private theorem b4_accept_in_decVis_iff {tr tr' : ExecTrace} {stateIdx msgIdx : Nat}
    {wrapped : Bool} :
    (∃ v ∈ decVis tr tr' stateIdx msgIdx wrapped, v.kind = .accept) ↔
      ∃ ptTerm, receivedPlaintext tr tr' = some ptTerm := by
  constructor
  · rintro ⟨v, hv, hkind⟩
    unfold decVis at hv; simp only [List.mem_append] at hv
    rcases hv with (hv | hv) | hv
    · cases hmsg : tr.getMessageSentAt msgIdx <;> simp [hmsg] at hv; subst hv; cases hkind
    · rcases List.mem_map.mp hv with ⟨r, _, rfl⟩; cases hkind
    · cases hpt : receivedPlaintext tr tr' with
      | none => simp [hpt] at hv
      | some ptTerm => exact ⟨ptTerm, rfl⟩
  · rintro ⟨ptTerm, hpt⟩
    refine ⟨⟨.accept, [ptTerm], .single, none⟩, ?_, rfl⟩
    unfold decVis; rw [hpt]; simp [List.mem_append]

/-- If `(Move.decryptSkipped ...).vis tr` has an `.accept` entry, the skipped-key lookup at `skIdx`
hits an unused `TREvent.SkippedKeyStored` matching `(st.sessionInfo me, msg.ratchetKey, msg.counter)`
and decryption succeeds. -/
theorem skippedHit_of_decryptSkipped
    {me : Participant} {stateIdx msgIdx skIdx pqIdx : Nat} {spqrMsgIdx : UInt32}
    {wrapped : Bool} {tr : ExecTrace}
    (hacc : ∃ v ∈ (Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind = .accept) :
    ∃ (st : TRState) (t : DY.Bytes) (msg : TRSignalMsg) (seed : DY.Bytes)
      (rIdx srcIdx : Nat) (spqr' key pqSalt ptTerm : DY.Bytes),
      ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st ∧
      tr.getMessageSentAt msgIdx = some t ∧ parseTrSignalMsg t = some msg ∧
      msg.version = messageVersion ∧
      (tr.at? skIdx : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some ⟨TREvent.SkippedKeyStored (st.sessionInfo me) msg.ratchetKey msg.counter seed rIdx srcIdx⟩ ∧
      skippedKeyUsedB tr skIdx = false ∧
      Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key) ∧
      ((tr.append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) =
        some ⟨pqSalt⟩ ∧
      msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
        msg.ciphertext = some ptTerm ∧
      receivedPlaintext tr
        ((Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next tr) =
        some ptTerm ∧
      (findRecvChain st.toDRState.recv msg.ratchetKey).isSome = true := by
  have hacc_dec : ∃ v ∈ decVis tr
      ((Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next tr)
      stateIdx msgIdx wrapped, v.kind = .accept := by
    rcases hacc with ⟨v, hv, hk⟩
    change v ∈ decVis tr _ stateIdx msgIdx wrapped ++ exposures tr _ at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ⟨v, hv, hk⟩
    · rw [b4_exposures_kind_eq_leak hv] at hk; cases hk
  obtain ⟨ptTerm0, hpt0⟩ := b4_accept_in_decVis_iff.mp hacc_dec
  have hpt_eq := hpt0
  unfold Move.next Move.act at hpt0; rw [b4_run_bind_pure_val] at hpt0
  unfold messageDecryptSkipped at hpt0; rw [b4_run_bind_snd, b4_getLocalState_snd] at hpt0
  rcases hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with _ | st
  · rw [hst, b4_receivedPlaintext_self] at hpt0; cases hpt0
  · rw [hst] at hpt0; dsimp only at hpt0
    rw [b4_run_bind_snd, b4_receiveSignalMsg_snd] at hpt0
    rcases hmsg : ((receiveSignalMsg msgIdx).run tr).1 with _ | msg
    · rw [hmsg, b4_receivedPlaintext_self] at hpt0; cases hpt0
    · rw [hmsg] at hpt0; dsimp only at hpt0
      obtain ⟨t, ht_sent, hparse, hver⟩ := b4_receiveSignalMsg_some_iff.mp hmsg
      have hge_fst : ((DY.getEntry skIdx : Traceful B4TREntry).run tr).1 =
          (tr.at? skIdx : Option B4TREntry) := by
        simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
      have hge_snd : ((DY.getEntry skIdx : Traceful B4TREntry).run tr).2.val = tr := by
        simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
      rw [b4_run_bind_snd, hge_fst, hge_snd] at hpt0
      rcases hsk : (tr.at? skIdx : Option B4TREntry) with _ | ⟨⟨ev⟩⟩
      · rw [hsk, b4_receivedPlaintext_self] at hpt0; cases hpt0
      · rw [hsk] at hpt0; dsimp only at hpt0
        cases ev with
        | SkippedKeyStored s pk n seed rIdx srcIdx =>
          by_cases hguard : s = st.sessionInfo me ∧ pk = msg.ratchetKey ∧ n = msg.counter ∧
              (findRecvChain st.toDRState.recv pk).isSome
          · rcases hguard with ⟨rfl, rfl, rfl, hfind⟩
            simp only [_root_.guard, hfind, true_and, ↓reduceIte, CompTrace.run_pure_bind_snd] at hpt0
            rcases hused : skippedKeyUsedB tr skIdx with _ | _
            · have hgt1 : ((guardTrace fun tr => !skippedKeyUsedB tr skIdx).run tr).1 = some () := by
                unfold guardTrace; simp [Traceful.run_mk, hused]
              have hgt2 : ((guardTrace fun tr => !skippedKeyUsedB tr skIdx).run tr).2.val = tr := by
                unfold guardTrace; simp [Traceful.run_mk, hused]
              rw [b4_run_bind_snd, hgt1, hgt2] at hpt0; dsimp only at hpt0
              rcases hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
              · rw [hspqr] at hpt0; dsimp only at hpt0
                rw [Traceful.run_failure, b4_receivedPlaintext_self] at hpt0; cases hpt0
              · rw [hspqr] at hpt0; dsimp only at hpt0
                let tr_k := tr.append (⟨key⟩ : Network.ExecEntryT)
                have hsm1 : ((DY.Network.sendMessage key).run tr).1 = some tr.length := by
                  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
                    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
                have hsm2 : ((DY.Network.sendMessage key).run tr).2.val = tr_k := by
                  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
                    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
                  rfl
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
                    refine ⟨st, t, msg, seed, rIdx, srcIdx, spqr', key, pqSalt, ptTerm,
                      rfl, ht_sent, hparse, hver, rfl, rfl,
                      hspqr, hpq_at, hmac_eq, hdec, ?_, hfind⟩
                    rw [hv] at hpt0; dsimp only at hpt0
                    have htail : ((do
                        DY.ProtocolEvent.logEvent (TREvent.SkippedKeyUsed (st.sessionInfo me) skIdx)
                        DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter ptTerm)
                        logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt
                          msg.counter rIdx stateIdx { st with spqr := spqr' }).run tr_k).2.val =
                        b4_decSkippedTr tr me stateIdx skIdx rIdx srcIdx st
                          msg.ratchetKey seed key pqSalt ptTerm spqr' msg.counter := by
                      unfold logMessageKeyAndStore b4_decSkippedTr
                      dsimp [tr_k]
                      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                        Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
                        Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
                        Symbolic.DYBridge.DY.appendEntry_eq_1,
                        Traceful.run_bind, Traceful.run_pure, Traceful.run_mk]
                    rw [htail, b4_receivedPlaintext_decSkippedTr] at hpt0
                    injection hpt0 with hpt_same
                    subst hpt_same
                    exact hpt_eq
            · have hgt_none : ((guardTrace fun tr => !skippedKeyUsedB tr skIdx).run tr).1 = none ∧
                  ((guardTrace fun tr => !skippedKeyUsedB tr skIdx).run tr).2.val = tr := by
                unfold guardTrace; simp [Traceful.run_mk, hused]
              rw [b4_run_bind_snd, hgt_none.1, hgt_none.2, b4_receivedPlaintext_self] at hpt0
              cases hpt0
          · simp only [_root_.guard, hguard, ↓reduceIte, b4_run_bind_snd, Traceful.run_failure,
              b4_receivedPlaintext_self] at hpt0
            cases hpt0
        | _ =>
          dsimp only at hpt0
          rw [Traceful.run_failure, b4_receivedPlaintext_self] at hpt0; cases hpt0

end Symbolic.Swarm.CREF
