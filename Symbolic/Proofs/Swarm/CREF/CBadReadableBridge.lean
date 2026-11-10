/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Bytes.AttackerKnowledge
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.Random
import DY.Actions.ProtocolEvent
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.MatchedPrefix
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.ReadFaithful
import Symbolic.Proofs.Swarm.CREF.ReadVis
import Symbolic.Proofs.Swarm.CREF.Sanitize
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState

/-!
# Step Extension of `RecvCollision`, `ReadFaithful`, and `ExplainsMoves` for Decrypt

Establishes `RecvCollision` invariance under `.attackerSend` of attacker-known terms and extends
`ReadFaithful` and `ExplainsMoves` across `[.attackerSend pqSalt, .attackerSend t] ++ [m]` for an
accepting `decrypt` or `decryptSkipped` move `m`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open Sanitize
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg SessionInfo parseTrSignalMsg)
open DY.Libsignal.PQXDH (PQXDHEvent PQXDHState)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open Symbolic.Swarm.CREF.TR.RecvDec (logSkippedKeysTr getLocalState_snd)

/-! ## Trace preservation across `.attackerSend` -/

private abbrev TRStEntryB :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
private abbrev TREvEntryB := DY.ProtocolEvent.ExecEntryT TREvent
private abbrev PQStEntryB :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState PQXDHState)
private abbrev CEvEntryB := DY.ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent

theorem runTrace_append_two_attackerSend (r : ProtocolSetup) (ms : List Move) (pqSalt t : DY.Bytes) :
    runTraceMoves r (ms ++ [.attackerSend pqSalt, .attackerSend t]) =
      ((runTraceMoves r ms).append (⟨pqSalt⟩ : DY.Network.ExecEntryT)).append
        (⟨t⟩ : DY.Network.ExecEntryT) := by
  have h2 : ms ++ [Move.attackerSend pqSalt, Move.attackerSend t] =
      (ms ++ [Move.attackerSend pqSalt]) ++ [Move.attackerSend t] := by simp
  rw [h2, TR.runTrace_snoc, TR.runTrace_snoc, b5_attackerSend_next, b5_attackerSend_next]

theorem runVis_append_two_attackerSend (r : ProtocolSetup) (ms : List Move) (pqSalt t : DY.Bytes) :
    runVis r (ms ++ [.attackerSend pqSalt, .attackerSend t]) = runVis r ms := by
  have h2 : ms ++ [Move.attackerSend pqSalt, Move.attackerSend t] =
      (ms ++ [Move.attackerSend pqSalt]) ++ [Move.attackerSend t] := by simp
  rw [h2, TR.runVis_snoc, vis_attackerSend_nil, List.append_nil,
    TR.runVis_snoc, vis_attackerSend_nil, List.append_nil]

theorem storedStates_append_network (r : ProtocolSetup) (tr : ExecTrace) (b : DY.Bytes) :
    storedStates r (tr.append (⟨b⟩ : DY.Network.ExecEntryT)) = storedStates r tr := by
  unfold storedStates newIndices DY.ExecTrace.getLocalStateAt
  have hlen : (tr.append (⟨b⟩ : DY.Network.ExecEntryT)).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  by_cases hs : (setupTrace r).length ≤ tr.length
  · rw [hlen, show tr.length + 1 - (setupTrace r).length =
        (tr.length - (setupTrace r).length) + 1 by omega,
      ← List.range'_append_1, List.filterMap_append]
    have hcongr :
        List.filterMap
          (fun i => (((tr.append (⟨b⟩ : DY.Network.ExecEntryT)).at? i : Option TRStEntryB)).map
            fun e => e.st)
          (List.range' (setupTrace r).length (tr.length - (setupTrace r).length)) =
        List.filterMap
          (fun i => ((tr.at? i : Option TRStEntryB)).map fun e => e.st)
          (List.range' (setupTrace r).length (tr.length - (setupTrace r).length)) := by
      refine List.filterMap_congr fun i hi => ?_
      rw [List.mem_range'_1] at hi
      rw [at?_of_le (DY.Trace.append_le tr (⟨b⟩ : DY.Network.ExecEntryT)) (by omega)]
    have hlast :
        (((tr.append (⟨b⟩ : DY.Network.ExecEntryT)).at?
          ((setupTrace r).length + (tr.length - (setupTrace r).length)) : Option TRStEntryB)) =
          none := by
      rw [show (setupTrace r).length + (tr.length - (setupTrace r).length) = tr.length by omega,
        at?_append_length]
      rfl
    simp [hcongr, List.range'_one, hlast]
  · by_cases hs2 : (setupTrace r).length ≤ tr.length + 1
    · have hEq : (setupTrace r).length = tr.length + 1 := by omega
      have h0 : tr.length - (setupTrace r).length = 0 := by omega
      rw [h0, hlen, hEq, Nat.sub_self]; rfl
    · simp [hlen, show tr.length + 1 - (setupTrace r).length = 0 by omega,
        show tr.length - (setupTrace r).length = 0 by omega]

theorem availableStates_append_network (r : ProtocolSetup) (tr : ExecTrace) (b : DY.Bytes) :
    availableStates r (tr.append (⟨b⟩ : DY.Network.ExecEntryT)) = availableStates r tr := by
  unfold availableStates
  rw [storedStates_append_network]

theorem ownKeys_append_network (r : ProtocolSetup) (tr : ExecTrace) (b : DY.Bytes)
    (st : TRState) (msg : TRSignalMsg) :
    ownKeys r (tr.append (⟨b⟩ : DY.Network.ExecEntryT)) st msg = ownKeys r tr st msg := by
  unfold ownKeys
  rw [availableStates_append_network]

theorem storedSecrets_append_network (tr : ExecTrace) (b : DY.Bytes) :
    storedSecrets (tr.append (⟨b⟩ : DY.Network.ExecEntryT)) = storedSecrets tr := by
  unfold storedSecrets DY.ExecTrace.getLocalStateAt
  simp only [Option.map_map, Function.comp_def]
  rw [show (tr.append (⟨b⟩ : DY.Network.ExecEntryT)).length = tr.length + 1 by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2],
    List.range_succ, List.filterMap_append]
  have hcongr :
      (List.range tr.length).filterMap
        (fun i => ((tr.append (⟨b⟩ : DY.Network.ExecEntryT)).at? i : Option PQStEntryB).map
          fun e => serialize e.st) =
      (List.range tr.length).filterMap
        (fun i => (tr.at? i : Option PQStEntryB).map fun e => serialize e.st) := by
    refine List.filterMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [at?_of_le (DY.Trace.append_le tr (⟨b⟩ : DY.Network.ExecEntryT)) hi]
  rw [hcongr]
  have hnone : ((tr.append (⟨b⟩ : DY.Network.ExecEntryT)).at? tr.length : Option PQStEntryB) =
      none := by
    rw [at?_append_length]; rfl
  simp [hnone]

private def trSkippedAt (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (tr : ExecTrace) (st : TRState) (msg : TRSignalMsg) (own : List DY.Bytes)
    (i : Nat) : Option TrialCtx :=
  match tr.getEventAt TREvent i with
  | some (.SkippedKeyStored s pk n seed _ _) =>
    if (TripleRatchet.findRecvChain st.toDRState.recv pk).isSome ∧
        gamma interpretation S g pk = gamma interpretation S g msg.ratchetKey ∧
        n = msg.counter then
      some { peerIk := st.peerIk, myIk := st.myIk, extra := [],
             ownSalts := if st.sessionInfo s.me = s then own else [],
             seed? := some seed }
    else none
  | _ => none

theorem whisperTrials_append_network (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) (b : DY.Bytes) (msg : TRSignalMsg) :
    whisperTrials interpretation r S g (tr.append (⟨b⟩ : DY.Network.ExecEntryT)) msg =
      whisperTrials interpretation r S g tr msg := by
  unfold whisperTrials
  split_ifs with hver
  · dsimp only
    rw [availableStates_append_network]
    refine List.flatMap_congr fun st _ => ?_
    rw [ownKeys_append_network]
    refine congrArg (_ ++ ·) ?_
    change (List.range (tr.append (⟨b⟩ : DY.Network.ExecEntryT)).length).filterMap
        (trSkippedAt interpretation S g (tr.append (⟨b⟩ : DY.Network.ExecEntryT))
          st msg (ownKeys r tr st msg)) =
      (List.range tr.length).filterMap
        (trSkippedAt interpretation S g tr st msg (ownKeys r tr st msg))
    rw [show (tr.append (⟨b⟩ : DY.Network.ExecEntryT)).length = tr.length + 1 by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2],
      List.range_succ, List.filterMap_append]
    have hcongr :
        (List.range tr.length).filterMap
          (trSkippedAt interpretation S g (tr.append (⟨b⟩ : DY.Network.ExecEntryT))
            st msg (ownKeys r tr st msg)) =
        (List.range tr.length).filterMap
          (trSkippedAt interpretation S g tr st msg (ownKeys r tr st msg)) := by
      refine List.filterMap_congr fun i hi => ?_
      rw [List.mem_range] at hi
      unfold trSkippedAt
      rw [getEventAt_append_lt _ tr _ hi]
    have hlast : trSkippedAt interpretation S g (tr.append (⟨b⟩ : DY.Network.ExecEntryT))
        st msg (ownKeys r tr st msg) tr.length = none := by
      (unfold trSkippedAt; simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1])
      rw [at?_append_length]; rfl
    simp [hcongr, hlast]
  · rfl

theorem honestKeysFrom_append_attackerSend (tr : ExecTrace) (ms : List Move) (b : DY.Bytes) :
    honestKeysFrom tr (ms ++ [.attackerSend b]) = honestKeysFrom tr ms := by
  induction ms generalizing tr with
  | nil => simp [honestKeysFrom]
  | cons m ms ih =>
    cases m <;> simp [honestKeysFrom, ih]

theorem honestSalts_append_attackerSend (r : ProtocolSetup) (ms : List Move) (b : DY.Bytes) :
    honestSalts r (ms ++ [.attackerSend b]) = honestSalts r ms := by
  unfold honestSalts
  rw [honestKeysFrom_append_attackerSend]

/-! ## `RecvCollision` invariance across `.attackerSend` -/

theorem attackerKnows_of_base_imp {tr tr' : ExecTrace}
    (hbase : ∀ b, DY.Trace.BaseAttackerKnows tr' b → b.AttackerKnows tr)
    {u : DY.Bytes} (hu : u.AttackerKnows tr') : u.AttackerKnows tr := by
  refine DY.Bytes.AttackerKnows.is_least_fixpoint (fun x => x.AttackerKnows tr) u tr'
    (fun x hx => DY.Bytes.AttackerKnows.prove DY.AttackerKnowledge.attackerKnowledge x tr hx)
    (fun x hx => ?_) hu
  simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, DY.SubAttackerKnowledge.fromPred] at hx
  exact hbase x hx

theorem attackerKnows_append_net_iff {tr : ExecTrace} {msg : DY.Bytes}
    (hmsg : msg.AttackerKnows tr) (u : DY.Bytes) :
    u.AttackerKnows (tr.append (⟨msg⟩ : DY.Network.ExecEntryT)) ↔ u.AttackerKnows tr := by
  constructor
  · refine attackerKnows_of_base_imp fun b hb => ?_
    rw [Symbolic.Swarm.COMPOSED.CompTrace.baseAttackerKnows_append_net] at hb
    rcases hb with rfl | hb
    · exact hmsg
    · exact DY.Bytes.AttackerKnows.prove_from_base b tr hb
  · exact DY.Bytes.AttackerKnows_le u tr _ (DY.Trace.append_le tr _)

/-- Appending `.attackerSend u` for `u` attacker-known on `runTraceMoves r ms` preserves
`RecvCollision`. -/
theorem recvCollision_append_one_attackerSend_iff
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms : List Move} {u t : DY.Bytes}
    (hu : u.AttackerKnows (runTraceMoves r ms)) :
    RecvCollision interpretation r S g (ms ++ [.attackerSend u]) t ↔
      RecvCollision interpretation r S g ms t := by
  have htr : runTraceMoves r (ms ++ [.attackerSend u]) =
      (runTraceMoves r ms).append (⟨u⟩ : DY.Network.ExecEntryT) := by
    rw [TR.runTrace_snoc, b5_attackerSend_next]
  have hvis : runVis r (ms ++ [.attackerSend u]) = runVis r ms := by
    rw [TR.runVis_snoc, vis_attackerSend_nil, List.append_nil]
  have hkn : (fun x : DY.Bytes => x.AttackerKnows (runTraceMoves r (ms ++ [.attackerSend u]))) =
      (fun x : DY.Bytes => x.AttackerKnows (runTraceMoves r ms)) := by
    funext x
    exact propext (by rw [htr]; exact attackerKnows_append_net_iff hu x)
  have hsalts : honestSalts r (ms ++ [.attackerSend u]) = honestSalts r ms :=
    honestSalts_append_attackerSend r ms u
  have hpref : prefixTerms r (runTraceMoves r (ms ++ [.attackerSend u]))
      (runVis r (ms ++ [.attackerSend u])) = prefixTerms r (runTraceMoves r ms) (runVis r ms) := by
    unfold prefixTerms principalTerms
    rw [hvis, htr, storedStates_append_network, storedSecrets_append_network]
  unfold RecvCollision
  cases hp : parseTrSignalMsg t with
  | none =>
    dsimp only
    unfold MemoCollisionOn
    rw [hkn, hpref, hvis]
  | some msg =>
    dsimp only
    have hwt : whisperTrials interpretation r S g (runTraceMoves r (ms ++ [.attackerSend u])) msg =
        whisperTrials interpretation r S g (runTraceMoves r ms) msg := by
      rw [htr]; exact whisperTrials_append_network interpretation r S g (runTraceMoves r ms) u msg
    rw [hwt, hsalts, hkn]
    unfold MemoCollisionOn
    rw [hpref, hvis]

theorem not_recvCollision_append_one_attackerSend_of_known
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms : List Move} {u t : DY.Bytes}
    (hu : u.AttackerKnows (runTraceMoves r ms))
    (hnc : ¬ RecvCollision interpretation r S g ms t) :
    ¬ RecvCollision interpretation r S g (ms ++ [.attackerSend u]) t :=
  fun hc => hnc ((recvCollision_append_one_attackerSend_iff hu).mp hc)

/-! ## `ReadFaithful` across a decrypt step -/

private theorem mem_snd_of_mem_zip_bridge {α β : Type} {a : α} {b : β} :
    ∀ {xs : List α} {ys : List β}, (a, b) ∈ xs.zip ys → b ∈ ys
  | _ :: _, _ :: _, h => by
    rcases List.mem_cons.mp h with ⟨rfl, rfl⟩ | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_snd_of_mem_zip_bridge h)

private theorem mem_zip_decVis_of_kind_recv {tr tr' : ExecTrace} {stateIdx msgIdx : Nat}
    {wrapped : Bool} {t : DY.Bytes} {e₀ e : MachineEvent} {tail_blk : List MachineEvent}
    {v : VisEntry}
    (ht : tr.getMessageSentAt msgIdx = some t)
    (hev : (e, v) ∈ (e₀ :: tail_blk).zip
      (decVis tr tr' stateIdx msgIdx wrapped ++ exposures tr tr'))
    (hvk : v.kind = .recv) :
    e = e₀ ∧ v = ⟨.recv, [t], if wrapped then .preKeyInner (sessionBaseKeys tr stateIdx)
      else .whisper, none⟩ := by
  rw [decVis_cons_of_getMessageSentAt_some ht, List.cons_append, List.zip_cons_cons,
    List.mem_cons] at hev
  rcases hev with hhead | htail
  · exact Prod.mk.inj hhead
  · exfalso
    have hv := mem_snd_of_mem_zip_bridge htail
    rw [List.mem_append, List.mem_append] at hv
    rcases hv with (hv | hv) | hv
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      cases hvk
    · rcases hp : receivedPlaintext tr tr' with _ | m
      · simp [hp] at hv
      · simp only [hp, Option.map_some, Option.toList_some, List.mem_singleton] at hv
        subst hv; cases hvk
    · exact exposures_kind_ne_recv hv hvk

/-- Extends `ReadFaithful` across `[.attackerSend pqSalt, .attackerSend t] ++ [m]` for an
accepting `decrypt` or `decryptSkipped` move `m`. -/
theorem readFaithful_append_decrypt_step
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g₁ : Ghost}
    {ms : List Move} {acc mid : List MachineEvent}
    {p : Participant} {stateIdx : Nat} {spqrMsgIdx : UInt32}
    {pqSalt t : DY.Bytes} {tag : BitVec 8} {body b pt : HwBytes} {m : Move}
    (hrf₀ : ReadFaithful interpretation r S g₁ ms acc)
    (hlen : acc.length = (runVis r ms).length)
    (ht : t ∈ recvRepresentations interpretation r S g₁ ms b)
    (hm : m = Move.decrypt p stateIdx ((runTraceMoves r ms).length + 1) (runTraceMoves r ms).length
            spqrMsgIdx (decide (tag ≠ wireWhisperTag)) ∨
          ∃ skIdx, m = Move.decryptSkipped p stateIdx ((runTraceMoves r ms).length + 1) skIdx
            (runTraceMoves r ms).length spqrMsgIdx (decide (tag ≠ wireWhisperTag)))
    (hrb : (tag = wireWhisperTag ∧ b = body) ∨
      (tag ≠ wireWhisperTag ∧ ∃ pf, parsePreKeyWire (tag :: body) = some pf ∧ b = pf.message)) :
    ReadFaithful interpretation r S g₁
      (ms ++ ([.attackerSend pqSalt, .attackerSend t] ++ [m]))
      (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt])) := by
  have hrf₁ : ReadFaithful interpretation r S g₁
      (ms ++ [Move.attackerSend pqSalt, Move.attackerSend t]) acc := by
    have h2 : ms ++ [Move.attackerSend pqSalt, Move.attackerSend t] =
        (ms ++ [Move.attackerSend pqSalt]) ++ [Move.attackerSend t] := by simp
    rw [h2]
    exact readFaithful_snoc_attackerSend (readFaithful_snoc_attackerSend hrf₀)
  have hlen₁ : acc.length =
      (runVis r (ms ++ [Move.attackerSend pqSalt, Move.attackerSend t])).length := by
    rw [runVis_append_two_attackerSend]
    exact hlen
  have hget_t :
      (runTraceMoves r (ms ++ [Move.attackerSend pqSalt, Move.attackerSend t])).getMessageSentAt
        ((runTraceMoves r ms).length + 1) = some t := by
    rw [runTrace_append_two_attackerSend]
    have hg := TR.RecvDec.getMessageSentAt_attackerSend
      ((runTraceMoves r ms).append (⟨pqSalt⟩ : DY.Network.ExecEntryT)) t
    rw [b5_attackerSend_next, show ((runTraceMoves r ms).append (⟨pqSalt⟩ : DY.Network.ExecEntryT)).length =
      (runTraceMoves r ms).length + 1 by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2]] at hg
    exact hg
  have ht_ext : t ∈ recvRepresentations interpretation r S g₁
      ((ms ++ [Move.attackerSend pqSalt, Move.attackerSend t]) ++ [m]) b :=
    ⟨DY.Bytes.AttackerKnows_le t _ _
      (by rw [List.append_assoc]; exact runTrace_le_append r ms _) ht.1, ht.2⟩
  rw [← List.append_assoc]
  refine readFaithful_append hlen₁ hrf₁
    (blk := .recv (tag :: body) :: (mid ++ [.accept pt])) ?_
  rintro ⟨e, v⟩ hev hvk
  rw [runMoves_cons_snd, show (runMoves [] _).2 = [] from rfl, List.append_nil] at hev
  have hev_eq : e = .recv (tag :: body) ∧
      v = ⟨.recv, [t], if decide (tag ≠ wireWhisperTag) then
        .preKeyInner (sessionBaseKeys (runTraceMoves r (ms ++ [Move.attackerSend pqSalt,
          Move.attackerSend t])) stateIdx) else .whisper, none⟩ := by
    rcases hm with rfl | ⟨skIdx, rfl⟩
    · rw [xpl_vis_eq] at hev
      exact mem_zip_decVis_of_kind_recv hget_t hev hvk
    · rw [xpl_vis_eq] at hev
      exact mem_zip_decVis_of_kind_recv hget_t hev hvk
  obtain ⟨rfl, rfl⟩ := hev_eq
  rcases hrb with ⟨rfl, rfl⟩ | ⟨hne_tag, pf, hpf, rfl⟩
  · have hw : decide (wireWhisperTag ≠ wireWhisperTag) = false := decide_eq_false (not_not.mpr rfl)
    rw [hw]
    exact ht_ext
  · have hw : decide (tag ≠ wireWhisperTag) = true := decide_eq_true hne_tag
    rw [hw]
    intro p₀ hp₀
    change parsePreKeyWire (tag :: body) = some p₀ at hp₀
    rw [hpf, Option.some.injEq] at hp₀
    subst hp₀
    exact ht_ext

/-! ## `bobDoneBaseKeys` invariance across non-`bobStart` moves -/

private def rpkT_bdKey (tr : ExecTrace) (i : Nat) : Option DY.Bytes :=
  match tr.getEventAt PQXDHEvent i with
  | some (.BobDone _ _ _ _ _ _ _ ek _ _) => some ek
  | _ => none

private theorem rpkT_bobDoneBaseKeys_eq (tr : ExecTrace) :
    bobDoneBaseKeys tr = (List.range tr.length).filterMap (rpkT_bdKey tr) := rfl

private theorem rpkT_bobDoneBaseKeys_append {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace)
    (x : E) :
    bobDoneBaseKeys (tr.append x) =
      bobDoneBaseKeys tr ++ (rpkT_bdKey (tr.append x) tr.length).toList := by
  rw [rpkT_bobDoneBaseKeys_eq, rpkT_bobDoneBaseKeys_eq, length_append', List.range_succ,
    List.filterMap_append]
  congr 1
  refine List.filterMap_congr fun i hi => ?_
  rw [List.mem_range] at hi
  unfold rpkT_bdKey
  rw [getEventAt_append_lt _ tr x hi]

private theorem rpkT_bdKey_append_other {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace)
    (x : E)
    (hx : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none) :
    rpkT_bdKey (tr.append x) tr.length = none := by
  (unfold rpkT_bdKey; simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1])
  rw [at?_append_length, hx]

private theorem rpkT_bobDoneBaseKeys_append_other {E : Type} [DY.ExecTraceTypes.Has E]
    (tr : ExecTrace) (x : E)
    (hx : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none) :
    bobDoneBaseKeys (tr.append x) = bobDoneBaseKeys tr := by
  rw [rpkT_bobDoneBaseKeys_append, rpkT_bdKey_append_other tr x hx, Option.toList_none,
    List.append_nil]

@[reducible] private def isBobDoneEv : PQXDHEvent → Bool
  | .BobDone _ _ _ _ _ _ _ _ _ _ => true
  | _ => false

private theorem rpkT_bobDoneBaseKeys_append_pq (tr : ExecTrace)
    (ev : PQXDHEvent) (hne : isBobDoneEv ev = false) :
    bobDoneBaseKeys (tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
      bobDoneBaseKeys tr := by
  rw [rpkT_bobDoneBaseKeys_append]
  have hnone :
      rpkT_bdKey (tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent)) tr.length = none := by
    (unfold rpkT_bdKey; simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1])
    rw [at?_append_self']
    cases ev <;> first | rfl | cases hne
  rw [hnone, Option.toList_none, List.append_nil]

theorem bobDoneBaseKeys_append_network (tr : ExecTrace) (b : DY.Bytes) :
    bobDoneBaseKeys (tr.append (⟨b⟩ : DY.Network.ExecEntryT)) = bobDoneBaseKeys tr :=
  rpkT_bobDoneBaseKeys_append_other tr (⟨b⟩ : DY.Network.ExecEntryT) rfl

private def NoBobDone {α : Type} (c : Traceful α) : Prop :=
  ∀ tr, bobDoneBaseKeys (c.run tr).2.val = bobDoneBaseKeys tr

private theorem NoBobDone.of_id {α : Type} {c : Traceful α}
    (h : ∀ tr, (c.run tr).2.val = tr) : NoBobDone c :=
  fun tr => by rw [h tr]

private theorem NoBobDone.pure {α : Type} (a : α) :
    NoBobDone (Pure.pure a : Traceful α) := NoBobDone.of_id (XplSteps.xfix_pure a)
private theorem NoBobDone.failure {α : Type} :
    NoBobDone (Alternative.failure : Traceful α) := NoBobDone.of_id XplSteps.xfix_failure
private theorem NoBobDone.getEntry {E : Type} [ExecTraceTypes.Has E] (i : Nat) :
    NoBobDone (DY.getEntry i : Traceful E) := NoBobDone.of_id (XplSteps.xfix_getEntry i)
private theorem NoBobDone.getLocalState (p : Participant) (h : Nat) :
    NoBobDone (PersistentLocalState.getLocalState p h : Traceful TRState) :=
  NoBobDone.of_id (getLocalState_snd p h)
private theorem NoBobDone.getLocalStatePQ (p : Participant) (h : Nat) :
    NoBobDone (PersistentLocalState.getLocalState p h : Traceful PQXDHState) :=
  NoBobDone.of_id (XplSteps.xfix_getLocalState p h)
private theorem NoBobDone.guardTrace (p : ExecTrace → Bool) :
    NoBobDone (TripleRatchet.guardTrace p) := NoBobDone.of_id (XplSteps.xfix_guardTrace p)
private theorem NoBobDone.requireTracePredicate (p : ExecTrace → Bool) :
    NoBobDone (DY.Libsignal.PQXDH.guardTrace p) := NoBobDone.of_id (XplSteps.xfix_guardOnTrace p)
private theorem NoBobDone.monadLiftErr {α : Type} (x : Err α) :
    NoBobDone (monadLift x : Traceful α) := NoBobDone.of_id fun _ => by
      dsimp only [monadLift, MonadLift.monadLift]; cases x <;> simp only [DY.Traceful.run_mk]
private theorem NoBobDone.traceLength : NoBobDone TripleRatchet.traceLength :=
  NoBobDone.of_id XplSteps.xfix_traceLength
private theorem NoBobDone.receiveMessage (h : Nat) :
    NoBobDone (Network.receiveMessage h) := NoBobDone.of_id (XplSteps.xfix_receiveMessage h)
private theorem NoBobDone.guardP (p : Prop) [Decidable p] :
    NoBobDone (_root_.guard p : Traceful Unit) := NoBobDone.of_id (XplSteps.xfix_guard p)

private theorem NoBobDone.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : NoBobDone x) (hf : ∀ a, NoBobDone (f a)) : NoBobDone (x >>= f) := by
  intro tr
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  rcases (x.run tr).1 with _ | a
  · exact hx tr
  · exact (hf a (x.run tr).2.val).trans (hx tr)

private theorem NoBobDone.prodCasesOn {α β γ : Type}
    (p : α × β) (f : α → β → Traceful γ) (hf : ∀ a b, NoBobDone (f a b)) :
    NoBobDone (Prod.casesOn p f) := by rcases p with ⟨a, b⟩; exact hf a b

private theorem NoBobDone.optionCasesOn {α β : Type} (o : Option α)
    (noneCase : Traceful β) (someCase : α → Traceful β)
    (hn : NoBobDone noneCase) (hs : ∀ a, NoBobDone (someCase a)) :
    NoBobDone (Option.casesOn o noneCase someCase) := by rcases o with _ | a; exact hn; exact hs a

private theorem NoBobDone.getKey (p : Participant) (h : Nat)
    (kind : DY.Libsignal.PQXDH.KeyKind) :
    NoBobDone (DY.Libsignal.PQXDH.getKey p h kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact NoBobDone.bind (NoBobDone.getLocalStatePQ p h) fun _ =>
    NoBobDone.bind (NoBobDone.guardP _) fun _ => NoBobDone.pure _

private theorem NoBobDone.lookupIdentity (p : Participant) (h : Nat) :
    NoBobDone (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine NoBobDone.bind (NoBobDone.getEntry h) fun _ => ?_
  split
  · exact NoBobDone.bind (NoBobDone.guardP _) fun _ => NoBobDone.pure _
  · exact NoBobDone.failure

private theorem NoBobDone.genRand (n : Nat) :
    NoBobDone (Random.genRand n : Traceful DY.Bytes) := fun tr => by
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact rpkT_bobDoneBaseKeys_append_other tr (⟨n⟩ : Random.ExecEntryT) rfl
private theorem NoBobDone.sendMessage (m : DY.Bytes) :
    NoBobDone (Network.sendMessage m) := fun tr => by
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact rpkT_bobDoneBaseKeys_append_other tr (⟨m⟩ : Network.ExecEntryT) rfl
private theorem NoBobDone.storeLocalState (p : Participant) (st : TRState) :
    NoBobDone (PersistentLocalState.storeLocalState p st) := fun tr => by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact rpkT_bobDoneBaseKeys_append_other tr (⟨⟨p, st⟩⟩ : TRStEntryB) rfl
private theorem NoBobDone.logEventPQ (ev : PQXDHEvent)
    (hne : isBobDoneEv ev = false) : NoBobDone (DY.ProtocolEvent.logEvent ev) := fun tr => by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact rpkT_bobDoneBaseKeys_append_pq tr ev hne
private theorem NoBobDone.logEventC (ev : DY.Libsignal.Composed.ComposedEvent) :
    NoBobDone (DY.ProtocolEvent.logEvent ev) := fun tr => by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact rpkT_bobDoneBaseKeys_append_other tr (⟨ev⟩ : CEvEntryB) rfl
private theorem NoBobDone.logEventTR (ev : TREvent) :
    NoBobDone (DY.ProtocolEvent.logEvent ev) := fun tr => by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact rpkT_bobDoneBaseKeys_append_other tr (⟨ev⟩ : TREvEntryB) rfl

private theorem NoBobDone.logMessageKeyAndStore (me : Participant)
    (s : SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes)
    (n : UInt32) (r par : Nat) (st : TRState) :
    NoBobDone (TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) := by
  unfold TripleRatchet.logMessageKeyAndStore
  exact NoBobDone.bind (NoBobDone.logEventTR _) fun _ => NoBobDone.storeLocalState _ _

private theorem NoBobDone.receiveSignalMsg (msgIdx : Nat) :
    NoBobDone (TripleRatchet.receiveSignalMsg msgIdx) := by
  unfold TripleRatchet.receiveSignalMsg
  refine NoBobDone.bind (NoBobDone.receiveMessage msgIdx) fun _ => ?_
  split
  · exact NoBobDone.bind (NoBobDone.guardP _) fun _ => NoBobDone.pure _
  · exact NoBobDone.failure

private theorem NoBobDone.verifyMacAndDecrypt (st : TRState)
    (msg : TRSignalMsg) (pqSalt seed : DY.Bytes) :
    NoBobDone (TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold TripleRatchet.verifyMacAndDecrypt
  exact NoBobDone.bind (NoBobDone.guardP _) fun _ => NoBobDone.monadLiftErr _

private theorem NoBobDone.dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    NoBobDone (TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact NoBobDone.bind (NoBobDone.guardP _) fun _ =>
    NoBobDone.bind (NoBobDone.genRand 32) fun _ => NoBobDone.pure _

private theorem NoBobDone.ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    NoBobDone (TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact NoBobDone.pure _
  · exact NoBobDone.bind (NoBobDone.dhRatchetStep st pk) fun _ => NoBobDone.pure _
  · exact NoBobDone.failure

private theorem bobDoneBaseKeys_logSkippedKeysTr (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    bobDoneBaseKeys (logSkippedKeysTr s pk rIdx src ck n k tr) = bobDoneBaseKeys tr := by
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih =>
    unfold logSkippedKeysTr
    exact (ih _ _ _).trans (rpkT_bobDoneBaseKeys_append_other tr _ rfl)

private theorem NoBobDone.logSkippedKeys (s : SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    NoBobDone (TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  intro tr
  rw [(Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeys_run s pk rIdx src ck n k tr).2]
  exact bobDoneBaseKeys_logSkippedKeysTr s pk rIdx src ck n k tr

local macro "noBobDone_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply NoBobDone.bind | with_reducible apply NoBobDone.prodCasesOn
  | with_reducible apply NoBobDone.optionCasesOn
  | with_reducible apply NoBobDone.pure | with_reducible apply NoBobDone.failure
  | with_reducible apply NoBobDone.genRand | with_reducible apply NoBobDone.storeLocalState
  | with_reducible apply NoBobDone.sendMessage | with_reducible apply NoBobDone.getLocalState
  | with_reducible apply NoBobDone.getLocalStatePQ | with_reducible apply NoBobDone.getKey
  | with_reducible apply NoBobDone.lookupIdentity | with_reducible apply NoBobDone.receiveMessage
  | with_reducible apply NoBobDone.getEntry | with_reducible apply NoBobDone.receiveSignalMsg
  | with_reducible apply NoBobDone.verifyMacAndDecrypt | with_reducible apply NoBobDone.dhRatchetStep
  | with_reducible apply NoBobDone.ensureReceiverChain | with_reducible apply NoBobDone.logSkippedKeys
  | with_reducible apply NoBobDone.guardP | with_reducible apply NoBobDone.monadLiftErr
  | with_reducible apply NoBobDone.guardTrace | with_reducible apply NoBobDone.requireTracePredicate
  | with_reducible apply NoBobDone.traceLength | with_reducible apply NoBobDone.logMessageKeyAndStore
  | with_reducible apply NoBobDone.logEventPQ _ (by rfl)
  | with_reducible apply NoBobDone.logEventC | with_reducible apply NoBobDone.logEventTR
  | split | with_reducible intro))

private theorem NoBobDone.aliceHandshake (a b : Participant)
    (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) :
    NoBobDone (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake; noBobDone_tac

private theorem NoBobDone.aliceStart (a b : Participant)
    (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) :
    NoBobDone (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine NoBobDone.bind (NoBobDone.aliceHandshake a b idStateIdx regIdxB h) fun _ => ?_; noBobDone_tac

private theorem NoBobDone.compromiseIK (p : Participant) (stateIdx : Nat) :
    NoBobDone (DY.Libsignal.PQXDH.compromiseIK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseIK; noBobDone_tac
private theorem NoBobDone.compromiseSPK (p : Participant) (stateIdx : Nat) :
    NoBobDone (DY.Libsignal.PQXDH.compromiseSPK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK; noBobDone_tac
private theorem NoBobDone.compromisePQSPK (p : Participant) (stateIdx : Nat) :
    NoBobDone (DY.Libsignal.PQXDH.compromisePQSPK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK; noBobDone_tac
private theorem NoBobDone.compromiseOPK (p : Participant) (stateIdx : Nat) :
    NoBobDone (DY.Libsignal.PQXDH.compromiseOPK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK; noBobDone_tac

private theorem noBobDone_move (tr : ExecTrace) (m : Move) (hm : m.isSetup = false)
    (hnot_bob : ∀ b a kh regA mh pqIdx spqrMsgIdx shown,
      m ≠ .bobStart b a kh regA mh pqIdx spqrMsgIdx shown) :
    bobDoneBaseKeys (m.next tr) = bobDoneBaseKeys tr := by
  cases m with
  | setup a b withOpk => cases hm
  | aliceStart a b idStateIdx regIdxB bh shown =>
    unfold Move.next Move.act
    exact (NoBobDone.bind (NoBobDone.aliceStart a b idStateIdx regIdxB bh) fun _ => NoBobDone.pure _) tr
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
    exact False.elim (hnot_bob b a kh regIdxA mh pqIdx spqrMsgIdx shown rfl)
  | encrypt me stateIdx coinsLen pqIdx wrap =>
    unfold Move.next Move.act TripleRatchet.messageEncrypt
    exact (by noBobDone_tac : NoBobDone _) tr
  | encryptAbort me stateIdx =>
    unfold Move.next Move.act TripleRatchet.messageEncryptAbort
    exact (by noBobDone_tac : NoBobDone _) tr
  | encryptFail me stateIdx coinsLen =>
    unfold Move.next Move.act TripleRatchet.messageEncrypt
    exact (by noBobDone_tac : NoBobDone _) tr
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    unfold Move.next Move.act; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
    exact (by noBobDone_tac : NoBobDone _) tr
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx wrapped =>
    unfold Move.next Move.act TripleRatchet.messageDecryptSkipped
    exact (by noBobDone_tac : NoBobDone _) tr
  | reject draws =>
    unfold Move.next Move.act; exact (by noBobDone_tac : NoBobDone _) tr
  | compromiseIK p stateIdx =>
    unfold Move.next Move.act
    exact (NoBobDone.bind (NoBobDone.compromiseIK p stateIdx) fun _ => NoBobDone.pure _) tr
  | compromiseSPK p stateIdx =>
    unfold Move.next Move.act
    exact (NoBobDone.bind (NoBobDone.compromiseSPK p stateIdx) fun _ => NoBobDone.pure _) tr
  | compromisePQSPK p stateIdx =>
    unfold Move.next Move.act
    exact (NoBobDone.bind (NoBobDone.compromisePQSPK p stateIdx) fun _ => NoBobDone.pure _) tr
  | compromiseOPK p stateIdx =>
    unfold Move.next Move.act
    exact (NoBobDone.bind (NoBobDone.compromiseOPK p stateIdx) fun _ => NoBobDone.pure _) tr
  | exposeKey me stateIdx k =>
    unfold Move.next Move.act TripleRatchet.exposeKey
    exact (by noBobDone_tac : NoBobDone _) tr
  | exposeSpqr me stateIdx =>
    unfold Move.next Move.act TripleRatchet.exposeSpqr
    exact (by noBobDone_tac : NoBobDone _) tr
  | exposeSkipped skippedKeyEventIdx =>
    unfold Move.next Move.act TripleRatchet.exposeSkipped
    exact (by noBobDone_tac : NoBobDone _) tr
  | attackerSend msg =>
    unfold Move.next Move.act; exact (by noBobDone_tac : NoBobDone _) tr
  | brkDH =>
    exact NoBobDone.logEventPQ .BrokenDH rfl tr
  | brkKEM =>
    exact NoBobDone.logEventPQ .BrokenKEM rfl tr

private theorem callStarts_decrypt_blk (tag : BitVec 8) (body : HwBytes)
    (mid : List MachineEvent) (pt : HwBytes)
    (hmid : mid = [] ∨ ∃ d, mid = [.rng d]) :
    callStarts (.recv (tag :: body) :: (mid ++ [.accept pt])) = [.recv (tag :: body)] := by
  rcases hmid with rfl | ⟨d, rfl⟩ <;> rfl

private theorem callCount_append_bridge (u v : List VisEntry) :
    callCount (u ++ v) = callCount u + callCount v := by
  unfold callCount
  rw [List.filter_append, List.length_append]

private theorem callCount_bobStart_pos {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles}
    {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat}
    {spqrMsgIdx : UInt32} {shown : Nat} {tr : ExecTrace}
    (ha : (Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).LogsSessionCompletion tr) :
    0 < callCount ((Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).vis tr) := by
  obtain ⟨hsh, -⟩ := ha
  obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, by omega⟩
  rw [xpl_vis_eq, callCount_append_bridge]
  dsimp only [xpl_ownVis, bobVis]
  unfold callCount
  rw [List.cons_append, List.take_succ_cons, List.filter_cons_of_pos rfl, List.length_cons]
  omega

private theorem bobDoneBaseKeys_eq_of_callCount_zero :
    ∀ (L : List Move) (tr : ExecTrace),
      (∀ m ∈ L, m.isSetup = false) →
      MovesAnchored L tr →
      callCount (runMoves L tr).2 = 0 →
      bobDoneBaseKeys (runMoves L tr).1 = bobDoneBaseKeys tr ∧
        ∀ m ∈ L, ∀ promote, m.prekeyPath? = some promote → promote = true
  | [], _, _, _, _ => ⟨rfl, fun _ hm => False.elim (List.not_mem_nil hm)⟩
  | m :: L, tr, hns, ⟨ha, hancL⟩, hcc => by
    rw [runMoves_cons_snd, callCount_append_bridge] at hcc
    have hcc_m : callCount (m.vis tr) = 0 := by omega
    have hcc_L : callCount (runMoves L (m.next tr)).2 = 0 := by omega
    have hnot_bob : ∀ b a kh regA mh pqIdx spqrMsgIdx shown,
        m ≠ .bobStart b a kh regA mh pqIdx spqrMsgIdx shown := by
      rintro b a kh regA mh pqIdx spqrMsgIdx shown rfl
      have hpos := callCount_bobStart_pos ha
      omega
    have hm_ns : m.isSetup = false := hns m List.mem_cons_self
    obtain ⟨ih_bd, ih_pr⟩ := bobDoneBaseKeys_eq_of_callCount_zero L (m.next tr)
      (fun m' hm' => hns m' (List.mem_cons_of_mem m hm')) hancL hcc_L
    have hm_bd : bobDoneBaseKeys (m.next tr) = bobDoneBaseKeys tr :=
      noBobDone_move tr m hm_ns hnot_bob
    refine ⟨ih_bd.trans hm_bd, fun m' hm' promote hp => ?_⟩
    rcases List.mem_cons.mp hm' with rfl | hm'
    · cases m' <;> simp only [Move.prekeyPath?] at hp
      case bobStart b a kh regA mh pqIdx spqrMsgIdx shown =>
        exact False.elim (hnot_bob b a kh regA mh pqIdx spqrMsgIdx shown rfl)
      case decrypt _ _ _ _ _ w =>
        cases w <;> simp at hp; exact hp
      case decryptSkipped _ _ _ _ _ _ w =>
        cases w <;> simp at hp; exact hp
      all_goals cases hp
    · exact ih_pr m' hm' promote hp

/-! ## `ExplainsMoves` across a decrypt step -/

/-- Pre-faithfulness matching obligations (`GhostAndSemMatchSetup`, `ModelRun`, and
`Forall₂ EventMatchesEntry`) for an extended decrypt trace. -/
abbrev RawDecryptMatched (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g₁ : Ghost) (ms : List Move) (acc : List MachineEvent) : Prop :=
  GhostAndSemMatchSetup interpretation r S g₁ ∧
    ModelRun r ms ∧
    List.Forall₂ (EventMatchesEntry interpretation r S g₁) acc (runVis r ms)

/-- Extends `ExplainsMoves` across `[.attackerSend pqSalt, .attackerSend t] ++ [m]` for an
accepting `decrypt` or `decryptSkipped` move `m`. -/
theorem explains_append_decrypt_step
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g₁ : Ghost}
    {ms : List Move} {acc mid : List MachineEvent}
    {p : Participant} {stateIdx : Nat} {spqrMsgIdx : UInt32}
    {pqSalt t : DY.Bytes} {tag : BitVec 8} {body b pt : HwBytes} {m : Move}
    (hf₀ : ExplainsMoves interpretation r S who ok g₁ ms acc)
    (ht : t ∈ recvRepresentations interpretation r S g₁ ms b)
    (hwho : who[(callStarts acc).length]? = some p)
    (hok : ok (callStarts acc).length = true)
    (hm : m = Move.decrypt p stateIdx ((runTraceMoves r ms).length + 1) (runTraceMoves r ms).length
            spqrMsgIdx (decide (tag ≠ wireWhisperTag)) ∨
          ∃ skIdx, m = Move.decryptSkipped p stateIdx ((runTraceMoves r ms).length + 1) skIdx
            (runTraceMoves r ms).length spqrMsgIdx (decide (tag ≠ wireWhisperTag)))
    (hmid : mid = [] ∨ ∃ d, mid = [.rng d])
    (hrb : (tag = wireWhisperTag ∧ b = body ∧
        parsePreKeyWire (wireWhisperTag :: body) = none) ∨
      (tag ≠ wireWhisperTag ∧ ∃ pf, parsePreKeyWire (tag :: body) = some pf ∧
        b = pf.message ∧
        (∃ ek ∈ bobDoneBaseKeys (runTraceMoves r ms),
          ecKey (gamma interpretation S g₁ ek) = pf.baseKey.take 33)))
    (hraw : RawDecryptMatched interpretation r S g₁
      (ms ++ ([.attackerSend pqSalt, .attackerSend t] ++ [m]))
      (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt]))) :
    ExplainsMoves interpretation r S who ok g₁
      (ms ++ ([.attackerSend pqSalt, .attackerSend t] ++ [m]))
      (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt])) := by
  let pre : List Move := [.attackerSend pqSalt, .attackerSend t]
  let blk : List MachineEvent := .recv (tag :: body) :: (mid ++ [.accept pt])
  have hcs_app : callStarts (acc ++ blk) = callStarts acc ++ [.recv (tag :: body)] := by
    unfold callStarts
    rw [List.filter_append]
    exact congrArg (callStarts acc ++ ·) (callStarts_decrypt_blk tag body mid pt hmid)
  have hF₀ := hf₀.1.2.2.2.2.2
  have hcc_ms : callCount (runVis r ms) = (callStarts acc).length :=
    callCount_of_forall₂ hF₀
  have hrb_rf : (tag = wireWhisperTag ∧ b = body) ∨
      (tag ≠ wireWhisperTag ∧ ∃ pf, parsePreKeyWire (tag :: body) = some pf ∧ b = pf.message) := by
    rcases hrb with ⟨h1, h2, _⟩ | ⟨h1, pf, h2, h3, _⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, pf, h2, h3⟩
  have hrf₁ : ReadFaithful interpretation r S g₁ (ms ++ (pre ++ [m])) (acc ++ blk) :=
    readFaithful_append_decrypt_step hf₀.1.2.2.2.2.1 hF₀.length_eq ht hm hrb_rf
  refine ⟨⟨hraw.1, hraw.2.1, ?_, ?_, hrf₁, hraw.2.2⟩, ?_⟩
  · -- RoleFaithful
    intro i m' q hi hq_party
    rcases Nat.lt_or_ge i ms.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hi
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hf₀.1.2.2.1 i m' q hi hq_party
    · rw [List.getElem?_append_right hge] at hi
      rcases hidx : i - ms.length with _ | _ | _ | k
      · rw [hidx] at hi; simp at hi; subst hi; cases hq_party
      · rw [hidx] at hi; simp at hi; subst hi; cases hq_party
      · rw [hidx] at hi; simp at hi; subst hi
        have hi_eq : i = ms.length + 2 := by omega
        subst hi_eq
        have htk : (ms ++ (pre ++ [m])).take (ms.length + 2) = ms ++ pre := by
          rw [← List.append_assoc]
          exact List.take_left' (by simp [pre])
        rw [htk, runVis_append_two_attackerSend, hcc_ms]
        have hp_eq : q = p := by
          rcases hm with rfl | ⟨skIdx, rfl⟩ <;>
            simp [Move.party?] at hq_party <;> exact hq_party.symm
        subst hp_eq
        exact hwho
      · rw [hidx] at hi; simp at hi
  · -- PathFaithful
    intro i m' promote b' pf' hi hpath hcall hparse
    rcases Nat.lt_or_ge i ms.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hi
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at hcall ⊢
      have hsplit_ms : ms = ms.take i ++ ms.drop i := (List.take_append_drop i ms).symm
      have hvis_split : runVis r ms =
          runVis r (ms.take i) ++ (runMoves (ms.drop i) (runTraceMoves r (ms.take i))).2 := by
        conv_lhs => rw [hsplit_ms]
        exact runVis_append r (ms.take i) (ms.drop i)
      have hcc_le : callCount (runVis r (ms.take i)) ≤ (callStarts acc).length := by
        rw [← hcc_ms, hvis_split, callCount_append_bridge]
        omega
      rcases Nat.lt_or_eq_of_le hcc_le with hk_lt | hk_eq
      · rw [hcs_app, List.getElem?_append_left hk_lt] at hcall
        exact hf₀.1.2.2.2.1 i m' promote b' pf' hi hpath hcall hparse
      · rw [hcs_app, hk_eq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq, MachineEvent.recv.injEq] at hcall
        subst hcall
        rcases hrb with ⟨rfl, _, hnone⟩ | ⟨_, pf, hpf, _, hek_ms⟩
        · rw [hnone] at hparse; cases hparse
        · rw [hpf, Option.some.injEq] at hparse; subst hparse
          have hcc_drop : callCount (runMoves (ms.drop i) (runTraceMoves r (ms.take i))).2 = 0 := by
            have := congrArg callCount hvis_split
            rw [callCount_append_bridge, hcc_ms, hk_eq] at this
            omega
          have hanc_ms := hf₀.1.2.1.2.2.1.2.1
          rw [hsplit_ms] at hanc_ms
          have hanc_drop : MovesAnchored (ms.drop i) (runTraceMoves r (ms.take i)) :=
            (b5_movesAnchored_append (ms.take i) (ms.drop i) (setupTrace r)).mp hanc_ms |>.2
          have hns_drop : ∀ m'' ∈ ms.drop i, m''.isSetup = false :=
            fun m'' hm'' => hf₀.1.2.1.2.1 m'' (List.mem_of_mem_drop hm'')
          obtain ⟨hbd_eq, hpr_true⟩ := bobDoneBaseKeys_eq_of_callCount_zero
            (ms.drop i) (runTraceMoves r (ms.take i)) hns_drop hanc_drop hcc_drop
          have htr_ms : (runMoves (ms.drop i) (runTraceMoves r (ms.take i))).1 = runTraceMoves r ms := by
            rw [← runTrace_append, ← hsplit_ms]
          rw [htr_ms] at hbd_eq
          have hm'_mem : m' ∈ ms.drop i := by
            have hdrop_eq : ms.drop i = m' :: ms.drop (i + 1) := by
              rw [← List.cons_getElem_drop_succ (h := hlt)]
              rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hi
              rw [hi]
            rw [hdrop_eq]
            exact List.mem_cons_self
          have hprom : promote = true := hpr_true m' hm'_mem promote hpath
          rw [← hbd_eq]
          exact ⟨fun _ => hek_ms, fun _ => hprom⟩
    · rw [List.getElem?_append_right hge] at hi
      rcases hidx : i - ms.length with _ | _ | _ | k
      · rw [hidx] at hi; simp at hi; subst hi; cases hpath
      · rw [hidx] at hi; simp at hi; subst hi; cases hpath
      · rw [hidx] at hi; simp at hi; subst hi
        have hi_eq : i = ms.length + 2 := by omega
        subst hi_eq
        have htk : (ms ++ (pre ++ [m])).take (ms.length + 2) = ms ++ pre := by
          rw [← List.append_assoc]
          exact List.take_left' (by simp [pre])
        rw [htk, runVis_append_two_attackerSend, hcc_ms, hcs_app,
          List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq, MachineEvent.recv.injEq] at hcall
        subst hcall
        rw [htk, runTrace_append_two_attackerSend,
          bobDoneBaseKeys_append_network, bobDoneBaseKeys_append_network]
        rcases hrb with ⟨rfl, _, hnone⟩ | ⟨hne_tag, pf, hpf, _, hek_ms⟩
        · rw [hnone] at hparse; cases hparse
        · rw [hpf, Option.some.injEq] at hparse; subst hparse
          have hprom : promote = true := by
            rcases hm with rfl | ⟨skIdx, rfl⟩ <;>
              simp [Move.prekeyPath?, hne_tag] at hpath <;> exact hpath
          exact ⟨fun _ => hek_ms, fun _ => hprom⟩
      · rw [hidx] at hi; simp at hi
  · -- OutcomeFaithful
    intro i m' hi
    rcases Nat.lt_or_ge i ms.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hi
      simpa only [List.take_append_of_le_length (Nat.le_of_lt hlt)] using hf₀.2 i m' hi
    · rw [List.getElem?_append_right hge] at hi
      rcases hidx : i - ms.length with _ | _ | _ | k
      · rw [hidx] at hi; simp at hi; subst hi
        have hi_eq : i = ms.length := by omega
        subst hi_eq
        have htk : (ms ++ (pre ++ [m])).take ms.length = ms := List.take_left
        rw [htk, hcc_ms]
        exact ⟨(fun _ h => nomatch h), fun _ => hok⟩
      · rw [hidx] at hi; simp at hi; subst hi
        have hi_eq : i = ms.length + 1 := by omega
        subst hi_eq
        have htk : (ms ++ (pre ++ [m])).take (ms.length + 1) = ms ++ [.attackerSend pqSalt] := by
          have : ms ++ (pre ++ [m]) = (ms ++ [.attackerSend pqSalt]) ++ [.attackerSend t, m] := by
            simp [pre]
          rw [this]
          exact List.take_left' (by simp)
        rw [htk, TR.runVis_snoc, vis_attackerSend_nil, List.append_nil, hcc_ms]
        exact ⟨(fun _ h => nomatch h), fun _ => hok⟩
      · rw [hidx] at hi; simp at hi; subst hi
        have hi_eq : i = ms.length + 2 := by omega
        subst hi_eq
        have htk : (ms ++ (pre ++ [m])).take (ms.length + 2) = ms ++ pre := by
          rw [← List.append_assoc]
          exact List.take_left' (by simp [pre])
        rw [htk, runVis_append_two_attackerSend, hcc_ms]
        refine ⟨fun ds h => ?_, fun _ => hok⟩
        rcases hm with rfl | ⟨skIdx, rfl⟩ <;> cases h
      · rw [hidx] at hi; simp at hi

end Symbolic.Swarm.CREF
