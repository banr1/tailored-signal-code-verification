/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.UA.Defs
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ReadVis
import Symbolic.Proofs.Swarm.CREF.StateFaithfulMoves
import Symbolic.Proofs.Swarm.CREF.TR.MessageKeyCurrentInv
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.Coinsplit.Probe.P3SuffixExcuses
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.UA.SlotInitTransfer
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Swarm.UA.XlateInv -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Forward Acceptance Bridge from Moves to Steps

Proves `acceptsViaCliMoves_to_acceptsViaCli`: on an accepted 32-byte-coins `recv` run `ev`, any
`ModelAcceptsTermAfterAttackerSendsMoves` extension of `(τ₁', g', ms')` lifts to a `Step`-level
`ModelAcceptsTermAfterAttackerSendsClassical` extension of `(g', ss')`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.XlateMovesToCli

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession (Address)
open Symbolic.Swarm.CREF (SemReady)
open _root_.DY.Libsignal.TripleRatchet (parseTrSignalMsg)
open Symbolic.Proofs.Swarm.UA.Defs (runOk failedSend flatEvents callsOf SchedFits)
open Symbolic.Proofs.Swarm.UA.XlateSteps (
  recvRepresentations_eq stepIn_next stepIn_ok stepIn_pre
  network_preCond attackerSend_next_eq_network
  eventMatchesEntry_recv_iff eventMatchesEntry_rng_iff eventMatchesEntry_accept_iff
  gamma_randTerm_eq exposures_kind
  exposures_layout_ne_preKeySend decVis_layout_ne_preKeySend
  exposures_layout_ne_preKeyInner decVis_layout_ne_preKeyInner_of_kind_ne_recv
  run_bind_pure_isSome run_bind_pure_snd
  messageDecrypt_newRandoms_32 messageDecryptSkipped_newRandoms_32
  callStarts_eq_of_coinSplit)
open Symbolic.Proofs.Swarm.UA.XlateInv
  (stepsWF_split_append forall₂_rng_of_bytesMatchEntry schedFits_prefix)

private def StepHasMove (s : Step) : Prop :=
  s.cls = .invisible ∨ s.cls = .party ∨ s.IsLeak

private def stepToDummyMove : Step → Move
  | .network msg => .attackerSend msg
  | .aliceStart a b idIdx regB bh => .aliceStart a b idIdx regB bh 0
  | .bobStart b a kh regA mh pqIdx spqrIdx => .bobStart b a kh regA mh pqIdx spqrIdx 0
  | .messageEncrypt me stIdx cLen pqIdx => .encrypt me stIdx cLen pqIdx none
  | .messageEncryptAbort me stIdx => .encryptAbort me stIdx
  | .messageDecrypt me stIdx msgIdx pqIdx spqrIdx => .decrypt me stIdx msgIdx pqIdx spqrIdx false
  | .messageDecryptSkipped me stIdx msgIdx skIdx pqIdx spqrIdx =>
      .decryptSkipped me stIdx msgIdx skIdx pqIdx spqrIdx false
  | .compromiseIK q idx => .compromiseIK q idx
  | .compromiseSPK q idx => .compromiseSPK q idx
  | .compromisePQSPK q idx => .compromisePQSPK q idx
  | .compromiseOPK q idx => .compromiseOPK q idx
  | .exposeKey me idx kc => .exposeKey me idx kc
  | .exposeSpqr me idx => .exposeSpqr me idx
  | .exposeSkipped skIdx => .exposeSkipped skIdx
  | _ => .reject []

private theorem stepToDummyMove_next {s : Step} (hs : StepHasMove s) (tr : ExecTrace) :
    (stepToDummyMove s).next tr = s.next tr := by
  cases s with
  | network msg => exact attackerSend_next_eq_network msg tr
  | registerIdentity _ | registerCorruptIdentity _ _ | genSignedPrekey _ _ | genPQPrekey _ _
  | genOneTimePrekey _ | breakDH | breakKEM | invertDH _ | invertKEM _ =>
    rcases hs with h | h | h <;> cases h
  | _ =>
    dsimp only [stepToDummyMove, Move.next, Move.act, Step.next, Step.toInput]
    erw [stepIn_next]; exact run_bind_pure_snd _ tr

private theorem stepToDummyMove_stateLoad (s : Step) :
    (stepToDummyMove s).stateLoad? = s.stateLoad? := by
  cases s <;> rfl

private theorem stepToDummyMove_ok_of_stateLoad {s : Step} {p : Participant} {k : Nat} {b : Bool}
    (h : s.stateLoad? = some (p, k, b)) (tr : ExecTrace) :
    ((stepToDummyMove s).act.run tr).1.isSome = s.ok tr := by
  cases s <;> try cases h
  all_goals
    dsimp only [stepToDummyMove, Move.act, Step.ok, Step.toInput]
    erw [stepIn_ok]; exact run_bind_pure_isSome _ tr

private theorem runMoves_fst_stepToDummyMove :
    ∀ {ss : List Step} (_hss : ∀ s ∈ ss, StepHasMove s) (tr : ExecTrace),
      (runMoves (ss.map stepToDummyMove) tr).1 = runSteps ss tr
  | [], _, _ => rfl
  | s :: ss, hss, tr => by
    simp only [List.map_cons, runMoves, runSteps,
      stepToDummyMove_next (hss s (List.mem_cons_self ..))]
    exact runMoves_fst_stepToDummyMove (fun x hx => hss x (List.mem_cons_of_mem _ hx)) (s.next tr)

private theorem runTraceMoves_stepToDummyMove {r : ProtocolSetup} {ss : List Step}
    (hss : ∀ s ∈ ss, StepHasMove s) :
    runTraceMoves r (ss.map stepToDummyMove) = runTrace r ss := by
  unfold runTraceMoves
  dsimp only [runMoves]
  rw [setupMove_next_nil]
  exact runMoves_fst_stepToDummyMove hss (setupTrace r)

private theorem matchesEvents_stepHasMove {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
    {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsClassicalAt interp r S g initIds tr ss evs vis) :
    ∀ s ∈ ss, StepHasMove s := by
  induction hme with
  | nil hinv => exact fun s hs => Or.inl (hinv s hs)
  | run1 hpre hrm _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hp | hx
    · exact Or.inl (hpre x hp)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr (Or.inl hrm.1)
      · exact ih x hx
  | run0 hpre _ _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hp | hx
    · exact Or.inl (hpre x hp)
    · exact ih x hx
  | @env _ _ _ s _ ev _ _ _ hpre hem _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hp | hx
    · exact Or.inl (hpre x hp)
    · rcases List.mem_cons.mp hx with rfl | hx
      · cases ev <;> try exact False.elim hem
        exact Or.inr (Or.inr hem.2.1)
      · exact ih x hx

private theorem stateFaithful_iff_stepsStateFaithful {r : ProtocolSetup} {ss : List Step}
    (hss : ∀ s ∈ ss, StepHasMove s) :
    StateFaithful r (ss.map stepToDummyMove) ↔ StepsStateFaithful r ss := by
  constructor
  · intro hsf i j si sj p k b hij hsi hsj hli hok hlj
    have hmi : (ss.map stepToDummyMove)[i]? = some (stepToDummyMove si) := by simp [hsi]
    have hmj : (ss.map stepToDummyMove)[j]? = some (stepToDummyMove sj) := by simp [hsj]
    have hmli : (stepToDummyMove si).stateLoad? = some (p, k, true) := by
      rwa [stepToDummyMove_stateLoad]
    have hmlj : (stepToDummyMove sj).stateLoad? = some (p, k, b) := by
      rwa [stepToDummyMove_stateLoad]
    have htake : ∀ x ∈ ss.take i, StepHasMove x :=
      fun x hx => hss x (List.mem_of_mem_take hx)
    have hmok : ((stepToDummyMove si).act.run
        (runTraceMoves r ((ss.map stepToDummyMove).take i))).1.isSome = true := by
      rw [← List.map_take, runTraceMoves_stepToDummyMove htake, stepToDummyMove_ok_of_stateLoad hli]
      exact hok
    exact hsf i j _ _ p k b hij hmi hmj hmli hmok hmlj
  · intro hssf i j mi mj p k b hij hmi hmj hmli hmok hmlj
    simp only [List.getElem?_map] at hmi hmj
    rcases hsi : ss[i]? with _ | si <;> simp [hsi] at hmi
    rcases hsj : ss[j]? with _ | sj <;> simp [hsj] at hmj
    subst hmi hmj
    rw [stepToDummyMove_stateLoad] at hmli hmlj
    have htake : ∀ x ∈ ss.take i, StepHasMove x :=
      fun x hx => hss x (List.mem_of_mem_take hx)
    rw [← List.map_take, runTraceMoves_stepToDummyMove htake,
      stepToDummyMove_ok_of_stateLoad hmli] at hmok
    exact hssf i j si sj p k b hij hsi hsj hmli hmok hmlj

private theorem stepsStateFaithful_snoc_of_isCurrentSnapshot {r : ProtocolSetup} {ss : List Step}
    {s : Step} (hss : ∀ x ∈ ss, StepHasMove x) (hs : StepHasMove s) (hsf : StepsStateFaithful r ss)
    (hcur : ∀ p k b, s.stateLoad? = some (p, k, b) →
      _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTrace r ss) k = true) :
    StepsStateFaithful r (ss ++ [s]) := by
  have hall : ∀ x ∈ ss ++ [s], StepHasMove x := fun x hx => by
    rcases List.mem_append.mp hx with h1 | h2
    · exact hss x h1
    · rcases List.mem_singleton.mp h2 with rfl; exact hs
  rw [← stateFaithful_iff_stepsStateFaithful hall, List.map_append, List.map_singleton]
  refine Symbolic.Swarm.CREF.stateFaithful_snoc_of_isCurrentSnapshot
    ((stateFaithful_iff_stepsStateFaithful hss).mpr hsf) fun p k b hl => ?_
  rw [runTraceMoves_stepToDummyMove hss]
  rw [stepToDummyMove_stateLoad] at hl
  exact hcur p k b hl

private theorem stepsWF_network_map :
    ∀ (ext : List _root_.DY.Bytes) (tr : ExecTrace),
      (∀ x ∈ ext, x.AttackerKnows tr) → StepsWF (ext.map .network) tr
  | [], _, _ => trivial
  | x :: xs, tr, hkn => by
    have hx : x.AttackerKnows tr := hkn x (List.mem_cons_self ..)
    refine ⟨by rw [network_preCond]; exact hx, trivial,
      stepsWF_network_map xs ((Step.network x).next tr) ?_⟩
    intro y hy
    exact _root_.DY.Bytes.AttackerKnows_le y tr _
      (Symbolic.Proofs.Swarm.UA.SlotInitTransfer.step_le_next (.network x) tr)
      (hkn y (List.mem_cons_of_mem _ hy))

private theorem runMoves_fst_attackerSend :
    ∀ (ext : List _root_.DY.Bytes) (tr : ExecTrace),
      (runMoves (ext.map .attackerSend) tr).1 = runSteps (ext.map .network) tr ∧
        (runMoves (ext.map .attackerSend) tr).2 = []
  | [], _ => ⟨rfl, rfl⟩
  | x :: xs, tr => by
    obtain ⟨h1, h2⟩ := runMoves_fst_attackerSend xs ((Step.network x).next tr)
    have hvis : (Move.attackerSend x).vis tr = [] :=
      Symbolic.Swarm.CREF.TR.RecvDec.exposures_attackerSend tr x
    simp only [List.map_cons, runMoves, runSteps, attackerSend_next_eq_network, hvis,
      List.nil_append]
    exact ⟨h1, h2⟩

private abbrev TREntry :=
  _root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.TripleRatchet.TREvent

private theorem sf_at?_eq_of_le_of_lt {E : Type} [_root_.DY.ExecTraceTypes.Has E]
    {tr tr' : ExecTrace} (hle : tr ≤ tr') {i : Nat} (hi : i < tr.length) :
    (tr'.at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (_root_.DY.Trace.length_le _ _ hle)
  simp only [_root_.DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← _root_.DY.Trace.at_le tr tr' i hi hle]

private theorem sf_run_bind_fst {α β : Type} (x : _root_.DY.Traceful α)
    (f : α → _root_.DY.Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [_root_.DY.Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr₁⟩
  · rfl
  · rcases (f a).run tr₁.val with ⟨_, _⟩; rfl

private theorem sf_run_bind_snd {α β : Type} (x : _root_.DY.Traceful α)
    (f : α → _root_.DY.Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [_root_.DY.Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr₁⟩
  · rfl
  · rcases (f a).run tr₁.val with ⟨_, _⟩; rfl

private def NoNewTREvent (tr t : ExecTrace) : Prop :=
  ∀ i, tr.length ≤ i → (t.at? i : Option TREntry) = none

private theorem noNewTREvent_refl (tr : ExecTrace) : NoNewTREvent tr tr :=
  fun _ hi => Symbolic.Swarm.CREF.TR.RecvDec.at?_eq_none_of_le tr hi

private theorem noNewTREvent_trans {tr t₁ t₂ : ExecTrace} (hle : t₁ ≤ t₂)
    (h1 : NoNewTREvent tr t₁) (h2 : NoNewTREvent t₁ t₂) : NoNewTREvent tr t₂ := by
  intro i hi
  by_cases hlt : i < t₁.length
  · rw [sf_at?_eq_of_le_of_lt hle hlt]; exact h1 i hi
  · exact h2 i (by omega)

private theorem noNewTREvent_of_xquiet {α : Type} {x : _root_.DY.Traceful α}
    (hx : Symbolic.Swarm.CREF.XplSteps.XQuiet x) (tr : ExecTrace) :
    NoNewTREvent tr (x.run tr).2.val :=
  fun i hi => (hx tr i hi).2.2.1

private theorem fail_bind_noNewTREvent {α β : Type} {x : _root_.DY.Traceful α}
    {f : α → _root_.DY.Traceful β} {tr : ExecTrace}
    (hx : NoNewTREvent tr (x.run tr).2.val)
    (hf : ∀ a, ((f a).run (x.run tr).2.val).1 = none →
      NoNewTREvent (x.run tr).2.val ((f a).run (x.run tr).2.val).2.val)
    (hnone : ((x >>= f).run tr).1 = none) :
    NoNewTREvent tr ((x >>= f).run tr).2.val := by
  rw [sf_run_bind_fst] at hnone
  rw [sf_run_bind_snd]
  cases hxr : (x.run tr).1 with
  | none => exact hx
  | some a =>
    rw [hxr] at hnone
    exact noNewTREvent_trans ((f a).run (x.run tr).2.val).2.property hx (hf a hnone)

private theorem not_accept_of_noNewTREvent {tr t : ExecTrace} (stateIdx msgIdx : Nat)
    (wrapped : Bool) (h : NoNewTREvent tr t) :
    ¬ ∃ v ∈ decVis tr t stateIdx msgIdx wrapped ++ exposures tr t, v.kind = .accept := by
  have hrp : receivedPlaintext tr t = none := by
    unfold receivedPlaintext
    rw [List.findSome?_eq_none_iff]
    intro i hi
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    rw [h i (List.mem_range'_1.mp hi).1]
  rintro ⟨v, hv, hk⟩
  rcases List.mem_append.mp hv with hv | hv
  · unfold decVis at hv
    rw [hrp] at hv
    simp only [Option.map_none, Option.toList_none, List.append_nil, List.mem_append,
      List.mem_map] at hv
    rcases hv with hv | ⟨_, _, rfl⟩
    · rcases hm : tr.getMessageSentAt msgIdx with _ | b
      · simp [hm] at hv
      · simp only [hm, Option.map_some, Option.toList_some, List.mem_singleton] at hv
        subst hv; cases hk
    · cases hk
  · have hk' := exposures_kind hv; rw [hk] at hk'; cases hk'

private theorem receiveSignalMsg_snd (msgIdx : Nat) (tr : ExecTrace) :
    ((_root_.DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx).run tr).2.val = tr := by
  unfold _root_.DY.Libsignal.TripleRatchet.receiveSignalMsg
  rw [sf_run_bind_snd,
    Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage msgIdx tr]
  rcases ((_root_.DY.Network.receiveMessage msgIdx).run tr).1 with _ | raw
  · rfl
  · dsimp only
    rcases parseTrSignalMsg raw with _ | msg
    · (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
    · dsimp only
      by_cases hv : msg.version = _root_.DY.Libsignal.TripleRatchet.messageVersion <;>
        simp only [_root_.guard, hv, ↓reduceIte] <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem verifyMacAndDecrypt_snd {st : _root_.DY.Libsignal.TripleRatchet.TRState}
    {msg : _root_.DY.Libsignal.TripleRatchet.TRSignalMsg}
    {pqSalt seed : _root_.DY.Bytes} (tr : ExecTrace) :
    ((_root_.DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed).run tr).2.val =
      tr := by
  unfold _root_.DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  by_cases hm : msg.mac = _root_.DY.Libsignal.TripleRatchet.computeMac
      (_root_.DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire
  · simp only [_root_.guard, hm, ↓reduceIte, sf_run_bind_snd]
    erw [_root_.DY.Traceful.run_pure]
    dsimp only
    rcases _root_.DY.SymEnc.CanSymEnc.symDec
      (_root_.DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey
      (_root_.DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext
    · dsimp only [liftM, monadLift, MonadLift.monadLift]; erw [_root_.DY.Traceful.run_mk]
    · dsimp only [liftM, monadLift, MonadLift.monadLift]; erw [_root_.DY.Traceful.run_mk]
  · simp only [_root_.guard, hm, ↓reduceIte]; (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem logEvent_fst {E : Type} [_root_.DY.ExecTraceTypes.Has (_root_.DY.ProtocolEvent.ExecEntryT E)]
    (e : E) (tr : ExecTrace) :
    ((_root_.DY.ProtocolEvent.logEvent e).run tr).1 = some tr.length := by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, _root_.DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  erw [_root_.DY.Traceful.run_mk]
  dsimp only
  erw [_root_.DY.Traceful.run_pure]
  rfl

private theorem logMessageKeyAndStore_fst (me : Participant)
    (s : _root_.DY.Libsignal.TripleRatchet.SessionInfo)
    (dir : _root_.DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : _root_.DY.Bytes)
    (n : UInt32) (rIdx par : Nat) (st : _root_.DY.Libsignal.TripleRatchet.TRState)
    (tr : ExecTrace) :
    ((_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx
      par st).run tr).1 = some (tr.length + 1) := by
  unfold _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  rw [sf_run_bind_fst, logEvent_fst]
  let mkEv : TREntry := ⟨_root_.DY.Libsignal.TripleRatchet.TREvent.MessageKey s dir seed pqSalt
    n rIdx par⟩
  have hlog_snd : ((_root_.DY.ProtocolEvent.logEvent mkEv.ev).run tr).2.val =
      tr.append mkEv := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, _root_.DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1]
    erw [_root_.DY.Traceful.run_mk]
    dsimp only
    erw [_root_.DY.Traceful.run_pure]
  rw [hlog_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  erw [_root_.DY.Traceful.run_mk]
  dsimp only
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rfl

private theorem decrypt_ok_of_accept {tr : ExecTrace} {me : Participant}
    {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    (hacc : ∃ v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind = .accept) :
    (Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).ok tr = true := by
  dsimp only [Step.ok, Step.toInput]
  erw [stepIn_ok]
  rcases hfst : ((_root_.DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx
      spqrMsgIdx).run tr).1 with _ | u
  · exfalso
    have hnext : (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr =
        ((_root_.DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx
          spqrMsgIdx).run tr).2.val :=
      run_bind_pure_snd _ tr
    have hno : NoNewTREvent tr
        ((_root_.DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx
          spqrMsgIdx).run tr).2.val := by
      revert hfst
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
      refine fail_bind_noNewTREvent
        (by rw [Symbolic.Swarm.CREF.TR.RecvDec.getLocalState_snd me stateIdx tr]
            exact noNewTREvent_refl tr) fun st₀ => ?_
      rw [Symbolic.Swarm.CREF.TR.RecvDec.getLocalState_snd me stateIdx tr]
      refine fail_bind_noNewTREvent
        (noNewTREvent_of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_receiveSignalMsg msgIdx) tr)
        fun msg => ?_
      rw [receiveSignalMsg_snd msgIdx tr]
      refine fail_bind_noNewTREvent
        (noNewTREvent_of_xquiet
          (Symbolic.Swarm.CREF.XplSteps.xquiet_ensureReceiverChain st₀ msg.ratchetKey) tr)
        fun ⟨st, c, ratcheted⟩ => ?_
      dsimp only
      let tr₁ := ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st₀ msg.ratchetKey).run tr).2.val
      rcases _root_.DY.Libsignal.TripleRatchet.consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
      · intro _; dsimp only; erw [_root_.DY.Traceful.run_failure]; exact noNewTREvent_refl tr₁
      · dsimp only
        rcases _root_.DY.Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
        · intro _; dsimp only; erw [_root_.DY.Traceful.run_failure]; exact noNewTREvent_refl tr₁
        · dsimp only
          have hnet : NoNewTREvent tr₁ ((_root_.DY.Network.sendMessage key).run tr₁).2.val := by
            have hsend : ((_root_.DY.Network.sendMessage key).run tr₁).2.val =
                tr₁.append ({ msg := key } : _root_.DY.Network.ExecEntryT) := by
              simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
                Symbolic.DYBridge.DY.appendEntry_eq_1]
              erw [_root_.DY.Traceful.run_mk]
            rw [hsend]
            intro i hi
            rw [Symbolic.Swarm.CREF.TR.RecvDec.at?_append_non_entry _ _ rfl]
            exact Symbolic.Swarm.CREF.TR.RecvDec.at?_eq_none_of_le tr₁ hi
          refine fail_bind_noNewTREvent hnet fun _ => ?_
          let tr₂ := ((_root_.DY.Network.sendMessage key).run tr₁).2.val
          refine fail_bind_noNewTREvent
            (by rw [Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage pqIdx tr₂]
                exact noNewTREvent_refl tr₂) fun pqSalt => ?_
          rw [Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage pqIdx tr₂]
          refine fail_bind_noNewTREvent
            (by rw [verifyMacAndDecrypt_snd tr₂]
                exact noNewTREvent_refl tr₂) fun ptTerm => ?_
          rw [verifyMacAndDecrypt_snd tr₂]
          have hTail : ∀ t₃, ((do
              let _ ← _root_.DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey
                c.rIdx stateIdx c.chainKey c.index (msg.counter.toNat - c.index.toNat)
              let _ ← _root_.DY.ProtocolEvent.logEvent
                (_root_.DY.Libsignal.TripleRatchet.TREvent.Received me st.peer msg.ratchetKey
                  msg.counter ptTerm)
              _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stateIdx
                { st with recv := _root_.DY.Libsignal.TripleRatchet.setRecvChain st.recv c',
                          spqr := spqr' }).run t₃).1 ≠ none := by
            intro t₃
            rw [Symbolic.Swarm.CREF.XplSteps.xrun_bind_fst,
              (Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeys_run _ _ _ _ _ _ _ t₃).1]
            dsimp only
            rw [Symbolic.Swarm.CREF.XplSteps.xrun_bind_fst, logEvent_fst,
              logMessageKeyAndStore_fst]
            intro h; cases h
          cases ratcheted <;> intro hnone
          · simp only [Bool.false_eq_true, ↓reduceIte] at hnone
            exact False.elim (hTail tr₂ hnone)
          · simp only [↓reduceIte] at hnone
            rw [Symbolic.Swarm.CREF.XplSteps.xrun_bind_fst, logEvent_fst,
              Symbolic.Swarm.CREF.XplSteps.xrun_bind_fst, logEvent_fst] at hnone
            exact False.elim (hTail _ hnone)
    rw [← hnext] at hno
    exact not_accept_of_noNewTREvent stateIdx msgIdx wrapped hno hacc
  · change ((_root_.DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx
      spqrMsgIdx).run tr).1.isSome = true
    rw [hfst]; rfl

private theorem decryptSkipped_ok_of_accept {tr : ExecTrace} {me : Participant}
    {stateIdx msgIdx evIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    (hacc : ∃ v ∈ (Move.decryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind = .accept) :
    (Step.messageDecryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx).ok tr = true := by
  dsimp only [Step.ok, Step.toInput]
  erw [stepIn_ok]
  rcases hfst : ((_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx evIdx
      pqIdx spqrMsgIdx).run tr).1 with _ | u
  · exfalso
    have hnext : (Move.decryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx wrapped).next tr =
        ((_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx evIdx
          pqIdx spqrMsgIdx).run tr).2.val :=
      run_bind_pure_snd _ tr
    have hno : NoNewTREvent tr
        ((_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx evIdx
          pqIdx spqrMsgIdx).run tr).2.val := by
      revert hfst
      unfold _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
      refine fail_bind_noNewTREvent
        (by rw [Symbolic.Swarm.CREF.TR.RecvDec.getLocalState_snd me stateIdx tr]
            exact noNewTREvent_refl tr) fun st => ?_
      rw [Symbolic.Swarm.CREF.TR.RecvDec.getLocalState_snd me stateIdx tr]
      refine fail_bind_noNewTREvent
        (noNewTREvent_of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_receiveSignalMsg msgIdx) tr)
        fun msg => ?_
      rw [receiveSignalMsg_snd msgIdx tr]
      refine fail_bind_noNewTREvent
        (noNewTREvent_of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix
          (Symbolic.Swarm.CREF.XplSteps.xfix_getEntry evIdx)) tr) fun ⟨ev⟩ => ?_
      rw [Symbolic.Swarm.CREF.XplSteps.xfix_getEntry evIdx tr]
      cases ev with
      | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
        dsimp only
        refine fail_bind_noNewTREvent
          (noNewTREvent_of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix
            (Symbolic.Swarm.CREF.XplSteps.xfix_guard _)) tr) fun _ => ?_
        rw [Symbolic.Swarm.CREF.XplSteps.xfix_guard _ tr]
        refine fail_bind_noNewTREvent
          (noNewTREvent_of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix
            (Symbolic.Swarm.CREF.XplSteps.xfix_guardTrace _)) tr) fun _ => ?_
        rw [Symbolic.Swarm.CREF.XplSteps.xfix_guardTrace _ tr]
        rcases _root_.DY.Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
        · intro _; dsimp only; erw [_root_.DY.Traceful.run_failure]; exact noNewTREvent_refl tr
        · dsimp only
          have hnet : NoNewTREvent tr ((_root_.DY.Network.sendMessage key).run tr).2.val := by
            have hsend : ((_root_.DY.Network.sendMessage key).run tr).2.val =
                tr.append ({ msg := key } : _root_.DY.Network.ExecEntryT) := by
              simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
                Symbolic.DYBridge.DY.appendEntry_eq_1]
              erw [_root_.DY.Traceful.run_mk]
            rw [hsend]
            intro i hi
            rw [Symbolic.Swarm.CREF.TR.RecvDec.at?_append_non_entry _ _ rfl]
            exact Symbolic.Swarm.CREF.TR.RecvDec.at?_eq_none_of_le tr hi
          refine fail_bind_noNewTREvent hnet fun _ => ?_
          let tr₁ := ((_root_.DY.Network.sendMessage key).run tr).2.val
          refine fail_bind_noNewTREvent
            (by rw [Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage pqIdx tr₁]
                exact noNewTREvent_refl tr₁) fun pqSalt => ?_
          rw [Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage pqIdx tr₁]
          refine fail_bind_noNewTREvent
            (by rw [verifyMacAndDecrypt_snd tr₁]
                exact noNewTREvent_refl tr₁) fun ptTerm => ?_
          rw [verifyMacAndDecrypt_snd tr₁]
          rw [Symbolic.Swarm.CREF.XplSteps.xrun_bind_fst, logEvent_fst,
            Symbolic.Swarm.CREF.XplSteps.xrun_bind_fst, logEvent_fst,
            logMessageKeyAndStore_fst]
          intro hnone; cases hnone
      | _ => intro _; dsimp only; erw [_root_.DY.Traceful.run_failure]; exact noNewTREvent_refl tr
    rw [← hnext] at hno
    exact not_accept_of_noNewTREvent stateIdx msgIdx wrapped hno hacc
  · change ((_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx evIdx
      pqIdx spqrMsgIdx).run tr).1.isSome = true
    rw [hfst]; rfl

private theorem forall₂_append_cancel_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {r₁ r₂ : List β},
      l₁.length = r₁.length →
      List.Forall₂ R (l₁ ++ l₂) (r₁ ++ r₂) →
      List.Forall₂ R l₁ r₁ ∧ List.Forall₂ R l₂ r₂
  | [], _, [], _, _, h => ⟨.nil, h⟩
  | _ :: _, _, [], _, hlen, _ => by cases hlen
  | [], _, _ :: _, _, hlen, _ => by cases hlen
  | _ :: _, _, _ :: _, _, hlen, .cons hhd htl =>
    let ⟨h1, h2⟩ := forall₂_append_cancel_left (Nat.succ.inj hlen) htl
    ⟨.cons hhd h1, h2⟩

private theorem forall₂_append_inv {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {rs : List β},
      List.Forall₂ R (l₁ ++ l₂) rs →
      ∃ r₁ r₂, rs = r₁ ++ r₂ ∧ List.Forall₂ R l₁ r₁ ∧ List.Forall₂ R l₂ r₂
  | [], _, rs, h => ⟨[], rs, rfl, .nil, h⟩
  | _ :: _, _, _ :: _, .cons hhd htl =>
    let ⟨r₁, r₂, heq, h1, h2⟩ := forall₂_append_inv htl
    ⟨_ :: r₁, r₂, congrArg (_ :: ·) heq, .cons hhd h1, h2⟩

private theorem runSteps_append :
    ∀ (s₁ s₂ : List Step) (tr : ExecTrace),
      runSteps (s₁ ++ s₂) tr = runSteps s₂ (runSteps s₁ tr)
  | [], _, _ => rfl
  | s :: s₁, s₂, tr => runSteps_append s₁ s₂ (s.next tr)

private theorem decVis_rng_mem_inv {tr tr' : ExecTrace} {stateIdx msgIdx : Nat}
    {wrapped : Bool} {v : VisEntry}
    (hv : v ∈ decVis tr tr' stateIdx msgIdx wrapped ++ exposures tr tr') (hk : v.kind = .rng) :
    ∃ x ∈ newRandoms tr tr', v = ⟨.rng, [x.1], .single, none⟩ := by
  rcases List.mem_append.mp hv with hv | hv
  · unfold decVis at hv
    simp only [List.mem_append, List.mem_map] at hv
    rcases hv with (hv | ⟨x, hx, rfl⟩) | hv
    · rcases hm : tr.getMessageSentAt msgIdx with _ | b
      · simp [hm] at hv
      · simp only [hm, Option.map_some, Option.toList_some, List.mem_singleton] at hv
        subst hv; cases hk
    · exact ⟨x, hx, rfl⟩
    · rcases hr : receivedPlaintext tr tr' with _ | m
      · simp [hr] at hv
      · simp only [hr, Option.map_some, Option.toList_some, List.mem_singleton] at hv
        subst hv; cases hk
  · exfalso; have hk' := exposures_kind hv; rw [hk] at hk'; cases hk'

private theorem parsePreKeyWire_head_ne_whisper {b : HwBytes} {p : PreKeyFields}
    (hp : parsePreKeyWire b = some p) :
    (b.head? != some _root_.DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) = true := by
  cases b with
  | nil => cases hp
  | cons hd tl =>
    dsimp only [parsePreKeyWire] at hp
    by_cases htag : hd = _root_.DY.Libsignal.PQXDH.Refinement.wirePrekeyTag
    · subst htag; dsimp only [List.head?]; decide
    · simp [htag] at hp

private theorem randTerm_inj {ts₁ sz₁ ts₂ sz₂ : Nat} (h : randTerm ts₁ sz₁ = randTerm ts₂ sz₂) :
    ts₁ = ts₂ ∧ sz₁ = sz₂ := by
  have hv := congrArg (fun b : _root_.DY.Bytes => b.view? _root_.DY.Random.Random) h
  dsimp only [randTerm] at hv
  rw [_root_.DY.BytesView.view_pack, _root_.DY.BytesView.view_pack] at hv
  injection hv with hr; cases hr; exact ⟨rfl, rfl⟩

/-- On an accepted 32-byte-coins `recv` run `ev`, any `ModelAcceptsTermAfterAttackerSendsMoves`
extension of `(τ₁', g', ms')` lifts to a `Step`-level `ModelAcceptsTermAfterAttackerSendsClassical`
extension of `(g', ss')`. -/
theorem acceptsViaCliMoves_to_acceptsViaCli
    {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {ok : Nat → Bool} {evs : List CliEvent} {ev : RunEvent} {g' : Ghost} {ss' : List Step}
    {vis' : List VisEntry} {τ₁' : List MachineEvent} {ms' : List Move}
    {peer : Address} {out : HwBytes} {σ_rest : List MachineEvent} {t : _root_.DY.Bytes}
    (_hwf : ProtocolSetupWF r) (_hS : SemReady interp' r S)
    (hsched : SchedFits (callsOf (evs ++ [.run ev])) who ok)
    (hexp : ExplainsClassical interp' r S g' ss' vis' evs)
    (hexp_c : ExplainsCli interp' r S who ok (flatEvents evs) τ₁' g' ms')
    (htr' : runTraceMoves r ms' = runTrace r ss')
    (hcmd : ev.cmd = .recv peer) (hexit : ev.exit = some (0, out))
    (hcoins : ev.coins.length = 32)
    (hpk_hdr : ∀ p, parsePreKeyWire ev.input = some p →
      p.version = 4 ∧ p.identityKey.take 33 = ecKey (pubBytes interp' (secretBytes r 0)))
    (hacc_m : ModelAcceptsTermAfterAttackerSendsMoves interp' r S who ok g' ms' τ₁' (.recv ev.input)
      (.rng ev.coins :: .accept out :: σ_rest) t) :
    ModelAcceptsTermAfterAttackerSendsClassical interp' r S g' ss' evs ev t := by
  obtain ⟨hcompat₀, hgwf₀, ⟨hsetup_len, hsetup_reach, hswf₀, hssf₀⟩, hmev₀⟩ := hexp
  obtain ⟨hcs₁, ⟨_, _, _, _, _, hf₂₀⟩, _, _⟩ := hexp_c
  have htwo : ∃ pieces : List HwBytes, (pieces = [] ∨ pieces = [ev.coins]) ∧
      ModelAcceptsTermAfterCoinSplit interp' r S who ok g' ms' τ₁' (.recv ev.input)
        (pieces.map .rng ++ [.accept out]) t := by
    rcases (Symbolic.Swarm.Coinsplit.P3.acceptsViaCli_iff_two_mids hcoins).mp hacc_m with h0 | h1
    · exact ⟨[], Or.inl rfl, h0⟩
    · exact ⟨[ev.coins], Or.inr rfl, h1⟩
  obtain ⟨pieces, hpieces_cases, ext, m, msgIdx, k, pt, g₁,
    hext_m, hdec_m, haddr, hσ_m, hmsg_m, hk_acc, _, hexm₁⟩ := htwo
  have htake_eq : out = pt ∧
      (pieces.map MachineEvent.rng ++ [MachineEvent.accept pt]).take (k + 1) =
        pieces.map MachineEvent.rng ++ [MachineEvent.accept pt] := by
    rcases hpieces_cases with rfl | rfl
    · cases k with
      | zero =>
        simp only [List.map_nil, List.nil_append, List.getElem?_cons_zero, Option.some.injEq,
          MachineEvent.accept.injEq] at hk_acc
        exact ⟨hk_acc, rfl⟩
      | succ k => simp at hk_acc
    · cases k with
      | zero => simp at hk_acc
      | succ k =>
        cases k with
        | zero =>
          simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
            List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
            MachineEvent.accept.injEq] at hk_acc
          exact ⟨hk_acc, rfl⟩
        | succ k => simp at hk_acc
  rcases htake_eq with ⟨hpt_eq, htake_k⟩
  subst hpt_eq
  rw [htake_k] at hexm₁
  have hext : ∀ x ∈ ext, x.AttackerKnows (runTrace r ss') := by
    rwa [← htr']
  have hσ : ∀ i, i < (runTrace r ss').length → g₁.σ i = g'.σ i := by
    rwa [← htr']
  let ms_net := ms' ++ ext.map Move.attackerSend
  let ss_net := ss' ++ ext.map Step.network
  let tr_net := runTrace r ss_net
  have htr_net_eq : tr_net = runSteps (ext.map Step.network) (runSteps ss' (setupTrace r)) :=
    runSteps_append ss' (ext.map Step.network) (setupTrace r)
  obtain ⟨hnet_fst, hnet_snd⟩ := runMoves_fst_attackerSend ext (runTrace r ss')
  have hrm_split₁ :=
    Symbolic.Swarm.CREF.runMoves_append (r.setupMove :: ms') (ext.map Move.attackerSend)
      _root_.DY.Trace.nil
  have htr_m_net : runTraceMoves r ms_net = tr_net := by
    unfold runTraceMoves
    dsimp only [ms_net]
    rw [← List.cons_append, hrm_split₁]
    dsimp only
    change (runMoves (ext.map Move.attackerSend) (runTraceMoves r ms')).1 = tr_net
    rw [htr', hnet_fst]; exact htr_net_eq.symm
  have hvis_m_net : runVis r ms_net = runVis r ms' := by
    unfold runVis
    dsimp only [ms_net]
    rw [← List.cons_append, hrm_split₁]
    dsimp only
    change runVis r ms' ++ (runMoves (ext.map Move.attackerSend) (runTraceMoves r ms')).2 =
      runVis r ms'
    rw [htr', hnet_snd, List.append_nil]
  have hmsg : tr_net.getMessageSentAt msgIdx = some t := by
    rwa [← htr_m_net]
  have hrm_split₂ :=
    Symbolic.Swarm.CREF.runMoves_append (r.setupMove :: ms_net) [m] _root_.DY.Trace.nil
  have htr_full : runTraceMoves r (ms_net ++ [m]) = m.next tr_net := by
    unfold runTraceMoves
    rw [← List.cons_append, hrm_split₂]
    dsimp only
    change (runMoves [m] (runTraceMoves r ms_net)).1 = m.next tr_net
    rw [htr_m_net]; rfl
  have hvis_full : runVis r (ms_net ++ [m]) = runVis r ms' ++ m.vis tr_net := by
    unfold runVis
    rw [← List.cons_append, hrm_split₂]
    dsimp only
    change runVis r ms_net ++ (runMoves [m] (runTraceMoves r ms_net)).2 =
      runVis r ms' ++ m.vis tr_net
    rw [hvis_m_net, htr_m_net]; simp [runMoves]
  obtain ⟨⟨hcompat₁, hmr₁, hrole₁, hpath₁, hread₁, hf₂_all⟩, _⟩ := hexm₁
  rw [hvis_full] at hf₂_all
  have hf₂_step : List.Forall₂ (EventMatchesEntry interp' r S g₁)
      (MachineEvent.recv ev.input ::
        (pieces.map MachineEvent.rng ++ [MachineEvent.accept out])) (m.vis tr_net) :=
    (forall₂_append_cancel_left hf₂₀.length_eq hf₂_all).2
  generalize hm_vis_eq : m.vis tr_net = vis_m at hf₂_step
  cases hf₂_step with
  | cons hinp_ev hf₂_tail =>
    rename_i inp v_tail
    obtain ⟨drs, outs, hv_tail, hf₂_drs, hf₂_outs⟩ := forall₂_append_inv hf₂_tail
    cases hf₂_outs with
    | cons hvacc_ev hf₂_nil =>
      rename_i v_acc _
      cases hf₂_nil
      subst hv_tail
      have hvacc_mem : v_acc ∈ m.vis tr_net := by rw [hm_vis_eq]; simp
      have hacc_vis : ∃ v ∈ m.vis tr_net, v.kind = .accept :=
        ⟨v_acc, hvacc_mem, hvacc_ev.1.symm⟩
      have hreach_m_next : (m.next tr_net).Reachable reachability := by
        have hr0 : (runTraceMoves r (ms_net ++ [m])).Reachable reachability := hmr₁.2.2.1.1
        rwa [htr_full] at hr0
      have hm_facts : ∃ (s_dec : Step) (me : Participant) (stateIdx : Nat) (wrapped : Bool),
          s_dec.decryptMsgIdx? = some msgIdx ∧
          s_dec.cls = .party ∧
          m.party? = some me ∧ s_dec.party? = some me ∧
          s_dec.FitsCmd (.recv peer) ∧ s_dec.MatchesSetupPeer r ∧
          s_dec.ok tr_net = true ∧ s_dec.PreCond tr_net ∧ s_dec.LocalOk tr_net ∧
          (∀ p' k' b', s_dec.stateLoad? = some (p', k', b') →
            _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot tr_net k' = true) ∧
          m.next tr_net = s_dec.next tr_net ∧
          m.vis tr_net = decVis tr_net (s_dec.next tr_net) stateIdx msgIdx wrapped ++
            exposures tr_net (s_dec.next tr_net) ∧
          stepView s_dec tr_net wrapped = m.vis tr_net ∧
          (∀ x ∈ newRandoms tr_net (s_dec.next tr_net), ∃ ts', x.1 = randTerm ts' 32) ∧
          m.prekeyPath? = (if wrapped then some true else none) ∧
          (∀ p, parsePreKeyWire ev.input = some p →
            (∃ ek ∈ bobDoneBaseKeys tr_net,
              ecKey (gamma interp' S g₁ ek) = p.baseKey.take 33) →
            PathFaithfulAt interp' S g₁ tr_net s_dec ev.input) := by
        cases m with
        | decrypt me stateIdx msgIdx' pqIdx spqrMsgIdx wrapped =>
          injection hdec_m with hmi; subst msgIdx'
          let s_dec := Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx
          have hok : s_dec.ok tr_net = true := decrypt_ok_of_accept hacc_vis
          have hcur : _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot tr_net stateIdx = true :=
            Symbolic.Swarm.CREF.TR.isCurrentSnapshot_of_decrypt_accept
              hreach_m_next hacc_vis
          have hpre : s_dec.PreCond tr_net := by
            dsimp only [s_dec, Step.PreCond, Step.toInput]; erw [stepIn_pre]; exact hcur
          have hnext : (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr_net =
              s_dec.next tr_net := by
            dsimp only [s_dec, Move.next, Move.act, Step.next, Step.toInput]
            erw [stepIn_next]; exact run_bind_pure_snd _ tr_net
          refine ⟨s_dec, me, stateIdx, wrapped, rfl, rfl, rfl, rfl, trivial, trivial, hok, hpre,
            trivial, ?_, hnext, ?_, ?_, ?_, rfl, ?_⟩
          · intro _ k' _ hl
            have hk' : stateIdx = k' := congrArg (fun x => x.2.1) (Option.some.inj hl)
            exact hk' ▸ hcur
          · dsimp only [Move.vis]; rw [hnext]
          · dsimp only [s_dec, stepView, Move.vis]; rw [hok]; simp only [↓reduceIte]; rw [hnext]
          · intro x hx
            obtain ⟨ts', hts'⟩ :=
              messageDecrypt_newRandoms_32 me stateIdx msgIdx pqIdx spqrMsgIdx tr_net x hx
            exact ⟨ts', congrArg Prod.fst hts'⟩
          · intro p₀ hp₀ hex_ek p' hp'
            have hp_eq : p' = p₀ := Option.some.inj (hp'.symm.trans hp₀)
            subst hp_eq; exact hex_ek
        | decryptSkipped me stateIdx msgIdx' evIdx pqIdx spqrMsgIdx wrapped =>
          injection hdec_m with hmi; subst msgIdx'
          let s_dec := Step.messageDecryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx
          have hok : s_dec.ok tr_net = true := decryptSkipped_ok_of_accept hacc_vis
          have hcur : _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot tr_net stateIdx = true :=
            Symbolic.Swarm.CREF.TR.isCurrentSnapshot_of_decryptSkipped_accept
              hreach_m_next hacc_vis
          have hpre : s_dec.PreCond tr_net := by
            dsimp only [s_dec, Step.PreCond, Step.toInput]; erw [stepIn_pre]; exact hcur
          have hnext :
              (Move.decryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx wrapped).next tr_net =
                s_dec.next tr_net := by
            dsimp only [s_dec, Move.next, Move.act, Step.next, Step.toInput]
            erw [stepIn_next]; exact run_bind_pure_snd _ tr_net
          refine ⟨s_dec, me, stateIdx, wrapped, rfl, rfl, rfl, rfl, trivial, trivial, hok, hpre,
            trivial, ?_, hnext, ?_, ?_, ?_, rfl, ?_⟩
          · intro _ k' _ hl
            have hk' : stateIdx = k' := congrArg (fun x => x.2.1) (Option.some.inj hl)
            exact hk' ▸ hcur
          · dsimp only [Move.vis]; rw [hnext]
          · dsimp only [s_dec, stepView, Move.vis]; rw [hok]; simp only [↓reduceIte]; rw [hnext]
          · intro x hx
            obtain ⟨ts', hts'⟩ := messageDecryptSkipped_newRandoms_32 me stateIdx msgIdx evIdx
              pqIdx spqrMsgIdx tr_net x hx
            exact ⟨ts', congrArg Prod.fst hts'⟩
          · intro p₀ hp₀ hex_ek p' hp'
            have hp_eq : p' = p₀ := Option.some.inj (hp'.symm.trans hp₀)
            subst hp_eq; exact hex_ek
        | _ => cases hdec_m
      obtain ⟨s_dec, me, stateIdx, wrapped, hs_dec_idx, hs_cls, hm_party, hs_party, hs_fits,
        hs_peer, hs_ok, hs_pre, hs_loc, hs_cur, hm_next, hm_vis_dec, hstepView, hnr_32, hm_pp,
        hs_path⟩ := hm_facts
      have hm_vis_npre : ∀ v ∈ m.vis tr_net, v.layout ≠ .preKeySend := fun v hv =>
        (List.mem_append.mp (hm_vis_dec ▸ hv)).elim
          decVis_layout_ne_preKeySend exposures_layout_ne_preKeySend
      have hm_vis_npki : ∀ v ∈ m.vis tr_net, v.kind ≠ .recv → ∀ eks, v.layout ≠ .preKeyInner eks :=
        fun v hv hk eks =>
          (List.mem_append.mp (hm_vis_dec ▸ hv)).elim
            (fun h => decVis_layout_ne_preKeyInner_of_kind_ne_recv h hk eks)
            (fun h => exposures_layout_ne_preKeyInner h eks)
      have hvacc_bm : BytesMatchEntry interp' r S g₁ .accept out v_acc :=
        (eventMatchesEntry_accept_iff (hm_vis_npre v_acc hvacc_mem)
          (hm_vis_npki v_acc hvacc_mem (by rw [← hvacc_ev.1]; nofun))).mp hvacc_ev
      have hdec_cons := Symbolic.Swarm.CREF.decVis_cons_of_getMessageSentAt_some
        (tr' := s_dec.next tr_net) (stateIdx := stateIdx) (wrapped := wrapped) hmsg
      have hinp_eq : inp = ⟨.recv, [t],
          if wrapped then .preKeyInner (sessionBaseKeys tr_net stateIdx) else .whisper, none⟩ := by
        have h1 : inp :: (drs ++ [v_acc]) =
            decVis tr_net (s_dec.next tr_net) stateIdx msgIdx wrapped ++
              exposures tr_net (s_dec.next tr_net) := hm_vis_eq.symm.trans hm_vis_dec
        rw [hdec_cons, List.cons_append] at h1
        exact (List.cons.inj h1).1
      have hinp_mem : inp ∈ m.vis tr_net := by rw [hm_vis_eq]; simp
      have hinp_bm : BytesMatchEntry interp' r S g₁ .recv ev.input inp :=
        (eventMatchesEntry_recv_iff (hm_vis_npre inp hinp_mem) (fun _ _ => hpk_hdr)).mp hinp_ev
      have hwrap_eq : wrapped = runWrapped ev := by
        have hbm := hinp_bm.2
        rw [hinp_eq] at hbm
        have hrw : runWrapped ev = (ev.input.head? !=
            some _root_.DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) := by
          unfold runWrapped; rw [hcmd]
        rw [hrw]
        cases wrapped
        · dsimp only at hbm
          obtain ⟨t', ht', hb_eq⟩ := hbm
          rw [hb_eq]; simp
        · dsimp only at hbm
          obtain ⟨t', p, _, hp_wire, _⟩ := hbm
          exact (parsePreKeyWire_head_ne_whisper hp_wire).symm
      have hcc_ms : callCount (runVis r ms') = (callStarts τ₁').length :=
        Symbolic.Swarm.CREF.callCount_eq_callStarts_length hf₂₀
      have hcs_len : (callStarts τ₁').length = (callsOf evs).length := by
        rw [callStarts_eq_of_coinSplit hcs₁,
          Symbolic.Proofs.Swarm.UA.Base.callStarts_flatEvents_length]
      have hwho_me : who[(callsOf evs).length]? = some me := by
        have hget : (ms_net ++ [m])[ms_net.length]? = some m := by simp
        have htake : (ms_net ++ [m]).take ms_net.length = ms_net := by simp
        have hr := hrole₁ ms_net.length m me hget hm_party
        rwa [htake, hvis_m_net, hcc_ms, hcs_len] at hr
      have hwho_ev : who[(callsOf evs).length]? = some ev.party := by
        have hfs : failedSend ev = false := by unfold failedSend; rw [hcmd]
        have hc_eq : callsOf (evs ++ [.run ev]) = callsOf evs ++ [(ev.party, runOk ev)] := by
          rw [Symbolic.Proofs.Swarm.UA.Base.callsOf_append]
          simp [callsOf, hfs]
        have hpfx := hsched.1
        rw [hc_eq, List.map_append] at hpfx
        obtain ⟨rest_w, hwho_eq⟩ := hpfx
        rw [List.append_assoc] at hwho_eq
        rw [← hwho_eq]
        have hlen_map : ((callsOf evs).map Prod.fst).length = (callsOf evs).length :=
          List.length_map ..
        rw [List.getElem?_append_right (by rw [hlen_map]), hlen_map, Nat.sub_self]
        rfl
      have hme_eq : me = ev.party := Option.some.inj (hwho_me.symm.trans hwho_ev)
      have ht_kn : t.AttackerKnows tr_net :=
        getMessageSentAt_attackerKnows hmsg
      have hzip_mem : (MachineEvent.recv ev.input, inp) ∈
          (τ₁' ++ (MachineEvent.recv ev.input ::
            (pieces.map MachineEvent.rng ++ [MachineEvent.accept out]))).zip
            (runVis r (ms_net ++ [m])) := by
        rw [hvis_full, hm_vis_eq, List.zip_append hf₂₀.length_eq]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      have hrf_step : ReadsFaithfully interp' r S g₁ tr_net inp ev.input := by
        have hrd := hread₁ (MachineEvent.recv ev.input, inp) hzip_mem
          (by rw [hinp_eq])
        dsimp only [ReadsFaithfully, eventBytes] at hrd ⊢
        rw [hinp_eq] at hrd ⊢
        cases wrapped
        · simp only [Bool.false_eq_true, ↓reduceIte] at hrd ⊢
          cases h_in : ev.input with
          | nil => trivial
          | cons hd body =>
            rw [h_in] at hrd
            dsimp only at hrd ⊢
            exact ⟨ht_kn, hrd.2⟩
        · simp only [↓reduceIte] at hrd ⊢
          intro p hp
          exact ⟨ht_kn, (hrd p hp).2⟩
      have hpf_step : PathFaithfulAt interp' S g₁ tr_net s_dec ev.input := by
        intro p hp
        have hw_true : wrapped = true := by
          rw [hwrap_eq]
          have hrw : runWrapped ev = (ev.input.head? !=
              some _root_.DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) := by
            unfold runWrapped; rw [hcmd]
          rw [hrw]
          exact parsePreKeyWire_head_ne_whisper hp
        have hget : (ms_net ++ [m])[ms_net.length]? = some m := by simp
        have htake : (ms_net ++ [m]).take ms_net.length = ms_net := by simp
        have hpp : m.prekeyPath? = some true := by rw [hm_pp, hw_true]; rfl
        have hcs_app : (callStarts (τ₁' ++ (MachineEvent.recv ev.input ::
            (pieces.map MachineEvent.rng ++ [MachineEvent.accept out]))))[callCount
              (runVis r ((ms_net ++ [m]).take ms_net.length))]? =
              some (MachineEvent.recv ev.input) := by
          rw [htake, hvis_m_net, hcc_ms]
          unfold callStarts
          rw [List.filter_append, List.filter_cons_of_pos (by rfl),
            List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        have hex_ek : ∃ ek ∈ bobDoneBaseKeys tr_net,
            ecKey (gamma interp' S g₁ ek) = p.baseKey.take 33 := by
          have hiff := hpath₁ ms_net.length m true ev.input p hget hpp hcs_app hp
          rw [htake, htr_m_net] at hiff
          exact hiff.mp rfl
        exact hs_path p hp hex_ek p hp
      have hpieces_ne : ∀ p ∈ pieces, p ≠ [] := by
        rcases hpieces_cases with rfl | rfl
        · intro _ h; cases h
        · intro p hp
          rcases List.mem_singleton.mp hp with rfl
          intro hnil; rw [hnil] at hcoins; cases hcoins
      have hpieces_pfx : pieces.flatten <+: ev.coins := by
        rcases hpieces_cases with rfl | rfl
        · exact List.nil_prefix
        · simp
      have hdrs_match : DrawsMatch interp' r S g₁ drs ev.coins := by
        refine ⟨pieces, hpieces_ne, hpieces_pfx, ?_⟩
        rcases hpieces_cases with rfl | rfl
        · rw [List.map_nil] at hf₂_drs; cases hf₂_drs; exact List.Forall₂.nil
        · rw [List.map_cons, List.map_nil] at hf₂_drs
          rcases drs with _ | ⟨v_rng, drs_tl⟩
          · cases hf₂_drs
          · cases hf₂_drs with
            | cons hd_rng htl_rng =>
              cases htl_rng
              have hv_mem : v_rng ∈ m.vis tr_net := by rw [hm_vis_eq]; simp
              exact List.Forall₂.cons
                ((eventMatchesEntry_rng_iff (hm_vis_npre v_rng hv_mem)
                  (hm_vis_npki v_rng hv_mem (by rw [← hd_rng.1]; nofun))).mp hd_rng)
                List.Forall₂.nil
      have hgwf_m_rng :
          ∀ v ∈ m.vis tr_net, v.kind = .rng → ∀ ts n, n ≠ 0 → randTerm ts n ∈ v.terms →
            (g₁.σ ts n).length = n := by
        intro v hv hk ts n _ hrt
        have hdec_mem : v ∈ decVis tr_net (s_dec.next tr_net) stateIdx msgIdx wrapped ++
            exposures tr_net (s_dec.next tr_net) := hm_vis_dec ▸ hv
        obtain ⟨x, hx_nr, hv_eq⟩ := decVis_rng_mem_inv hdec_mem hk
        obtain ⟨ts', hts'⟩ := hnr_32 x hx_nr
        rw [hv_eq, hts'] at hrt
        dsimp only at hrt
        simp only [List.mem_singleton] at hrt
        obtain ⟨hts_eq, hn_eq⟩ := randTerm_inj hrt
        have hv_drs : v ∈ drs := by
          rw [hm_vis_eq] at hv
          rcases List.mem_cons.mp hv with h1 | h2
          · exfalso
            have hk1 : v.kind = .recv := by rw [h1, hinp_eq]
            rw [hk] at hk1; cases hk1
          · rcases List.mem_append.mp h2 with hd | ha
            · exact hd
            · exfalso
              rcases List.mem_singleton.mp ha with h_eq
              have hk_acc' := hvacc_bm.1.symm
              rw [← h_eq, hk] at hk_acc'; cases hk_acc'
        rcases hpieces_cases with h_nil | h_cons
        · rw [h_nil, List.map_nil] at hf₂_drs
          cases hf₂_drs; cases hv_drs
        · rw [h_cons, List.map_cons, List.map_nil] at hf₂_drs
          rcases drs with _ | ⟨v_rng, drs_tl⟩
          · cases hf₂_drs
          · cases hf₂_drs with
            | cons hd_rng htl_rng =>
              cases htl_rng
              rcases List.mem_singleton.mp hv_drs with hv_d
              have hv_mem : v_rng ∈ m.vis tr_net := by rw [hm_vis_eq]; simp
              have hbm_rng :=
                ((eventMatchesEntry_rng_iff (initIds := none) (hm_vis_npre v_rng hv_mem)
                  (hm_vis_npki v_rng hv_mem (by rw [← hd_rng.1]; nofun))).mp hd_rng).2
              rw [← hv_d, hv_eq, hts'] at hbm_rng
              dsimp only [BytesMatchEntry, List.map] at hbm_rng
              have hgam_eq : gamma interp' S g₁ (randTerm ts' 32) = ev.coins :=
                (List.cons.inj hbm_rng).1
              rw [gamma_randTerm_eq interp' S g₁ ts' 32 (by decide)] at hgam_eq
              rw [hts_eq, hn_eq, hgam_eq, hcoins]
      have hfr : Symbolic.Swarm.CREF.CBadSigmaFrame g' g₁ (runTrace r ss').length :=
        ⟨fun i hi len => congrFun (hσ i hi) len, haddr⟩
      have hreach_ss' : (runTrace r ss').Reachable reachability :=
        Symbolic.Proofs.Swarm.UA.SlotInitTransfer.runSteps_reachable ss' hsetup_reach hswf₀
      have htr_lt : Symbolic.Swarm.CREF.TR.FreshSigma.TraceEntriesLt interp' S g'
          (runTrace r ss').length (runTrace r ss') :=
        Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_of_reachable interp' S g'
          (runTrace r ss').length hreach_ss' (Nat.le_refl _)
      have hvis_lt := Symbolic.Proofs.Swarm.UA.SlotInitTransfer.matchesEvents_visStampsLt
        hmev₀ hsetup_reach hswf₀ (Nat.le_refl _) htr_lt
      have hgwf₁_pre : GhostWF g₁ vis' :=
        Symbolic.Proofs.Swarm.UA.SlotInitTransfer.ghostWF_transfer hfr hvis_lt hgwf₀
      have hgwf₁ : GhostWF g₁ (vis' ++ m.vis tr_net) := by
        refine ⟨?_, hgwf₁_pre.2.1, ?_⟩
        · intro v hv
          rcases List.mem_append.mp hv with h1 | h2
          · exact hgwf₁_pre.1 v h1
          · exact hgwf_m_rng v h2
        · intro v hv hk
          rcases List.mem_append.mp hv with h1 | h2
          · exact hgwf₁_pre.2.2 v h1 hk
          · exfalso
            rw [hm_vis_eq] at h2
            rcases List.mem_cons.mp h2 with h_eq | h2
            · have hk1 : inp.kind = VisEventKind.recv := hinp_ev.1.symm
              rw [← h_eq, hk] at hk1; cases hk1
            · rcases List.mem_append.mp h2 with hd | ha
              · rcases hpieces_cases with h_nil | h_cons
                · rw [h_nil, List.map_nil] at hf₂_drs
                  cases hf₂_drs; cases hd
                · rw [h_cons, List.map_cons, List.map_nil] at hf₂_drs
                  rcases drs with _ | ⟨v_rng, drs_tl⟩
                  · cases hf₂_drs
                  · cases hf₂_drs with
                    | cons hd_rng htl_rng =>
                      cases htl_rng
                      rcases List.mem_singleton.mp hd with h_eq
                      have hk1 : v_rng.kind = VisEventKind.rng := hd_rng.1.symm
                      rw [← h_eq, hk] at hk1; cases hk1
              · rcases List.mem_singleton.mp ha with h_eq
                have hk1 : v_acc.kind = VisEventKind.accept := hvacc_ev.1.symm
                rw [← h_eq, hk] at hk1; cases hk1
      have hmev₁_pre : MatchesEventsClassical interp' r S g₁ (setupTrace r) ss' evs vis' :=
        Symbolic.Proofs.Swarm.UA.SlotInitTransfer.matchesEvents_transfer hfr hmev₀ hsetup_reach
          hswf₀ (Nat.le_refl _)
      have hswf_net : StepsWF ss_net (setupTrace r) :=
        (Symbolic.Proofs.Swarm.UA.SlotInitTransfer.stepsWF_append_iff ss' (ext.map Step.network)
          (setupTrace r)).mpr ⟨hswf₀, stepsWF_network_map ext (runTrace r ss') hext⟩
      have hswf_s : StepsWF [s_dec] tr_net := ⟨hs_pre, hs_loc, trivial⟩
      have hswf_all : StepsWF (ss_net ++ [s_dec]) (setupTrace r) :=
        (Symbolic.Proofs.Swarm.UA.SlotInitTransfer.stepsWF_append_iff
          ss_net [s_dec] (setupTrace r)).mpr ⟨hswf_net, hswf_s⟩
      have hssf_net : StepsStateFaithful r ss_net :=
        Symbolic.Proofs.Swarm.UA.SlotInitTransfer.stepsStateFaithful_append_noLoad hssf₀
          fun x hx => by
            rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; rfl
      have hshm_net : ∀ x ∈ ss_net, StepHasMove x := by
        intro x hx
        rcases List.mem_append.mp hx with h1 | h2
        · exact matchesEvents_stepHasMove hmev₀ x h1
        · rcases List.mem_map.mp h2 with ⟨_, _, rfl⟩; exact Or.inl rfl
      have hssf_all : StepsStateFaithful r (ss_net ++ [s_dec]) :=
        stepsStateFaithful_snoc_of_isCurrentSnapshot hshm_net (Or.inr (Or.inl hs_cls))
          hssf_net hs_cur
      have hrm_ev : RunMatches interp' r S g₁ tr_net s_dec ev (m.vis tr_net) (activeBundleIds evs) := by
        refine ⟨hs_cls, by rw [hs_party, hme_eq], by rw [hcmd]; exact hs_fits, hs_peer, hs_ok,
          ⟨out, hexit⟩, ?_, inp, drs, [v_acc], hm_vis_eq, ?_, hdrs_match, ?_, hrf_step, hpf_step⟩
        · rw [← hwrap_eq, hstepView]
        · have hik : inputKind ev = .recv := by unfold inputKind; rw [hcmd]
          rw [hik]; exact hinp_bm
        · unfold OutputsMatch; rw [hexit, hcmd]; exact ⟨v_acc, rfl, hvacc_bm⟩
      have hmev_all : MatchesEventsClassical interp' r S g₁ (setupTrace r)
          (ss_net ++ [s_dec]) (evs ++ [.run ev]) (vis' ++ m.vis tr_net) :=
        Symbolic.Proofs.Swarm.UA.SlotInitTransfer.matchesEvents_snoc_run1 hmev₁_pre
          (fun x hx => by rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; rfl)
          (htr_net_eq ▸ hrm_ev)
      exact ⟨ext, s_dec, msgIdx, g₁, vis' ++ m.vis tr_net, hext, hs_dec_idx, haddr, hσ, hmsg,
        hcompat₁, hgwf₁, ⟨hsetup_len, hsetup_reach, hswf_all, hssf_all⟩, hmev_all⟩

end Symbolic.Proofs.Swarm.UA.XlateMovesToCli
