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
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.StateFaithfulMoves
import Symbolic.Proofs.Swarm.CREF.TRView
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Composed Model-Run and Faithfulness Extension Lemmas

Provides list-append and single-step extension lemmas for `runMoves`, `ModelRun` (`MoveOK`,
`modelRun_snoc`), `RoleFaithful`, `PathFaithful`, `OutcomeFaithful`, `MatchedPrefix`, and
`ExplainsMoves`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoProofLib.Refinement (ExternInterpretation)
open PQXDH (PQXDHEvent BundleHandles BobKeyHandles PreKeyMsgHandles)

theorem b5_runMoves_append_fst : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    (runMoves (ms₁ ++ ms₂) tr).1 = (runMoves ms₂ (runMoves ms₁ tr).1).1
  | [], _, _ => rfl
  | m :: ms₁, ms₂, tr => b5_runMoves_append_fst ms₁ ms₂ (m.next tr)

theorem b5_runMoves_append_snd : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    (runMoves (ms₁ ++ ms₂) tr).2 = (runMoves ms₁ tr).2 ++ (runMoves ms₂ (runMoves ms₁ tr).1).2
  | [], _, _ => rfl
  | m :: ms₁, ms₂, tr => by
    rw [List.cons_append, runMoves_cons_snd, b5_runMoves_append_snd ms₁ ms₂ (m.next tr),
      runMoves_cons_snd, runMoves_cons_fst, List.append_assoc]

theorem b5_runTrace_eq (r : ProtocolSetup) (ms : List Move) :
    runTraceMoves r ms = (runMoves ms (setupTrace r)).1 := rfl

theorem b5_runVis_eq (r : ProtocolSetup) (ms : List Move) :
    runVis r ms = r.setupMove.vis Trace.nil ++ (runMoves ms (setupTrace r)).2 := rfl

theorem runMoves_append (ms ms' : List Move) (tr : ExecTrace) :
    runMoves (ms ++ ms') tr =
      ((runMoves ms' (runMoves ms tr).1).1, (runMoves ms tr).2 ++ (runMoves ms' (runMoves ms tr).1).2) :=
  Prod.ext (b5_runMoves_append_fst ms ms' tr) (b5_runMoves_append_snd ms ms' tr)

theorem runTrace_append (r : ProtocolSetup) (ms ms' : List Move) :
    runTraceMoves r (ms ++ ms') = (runMoves ms' (runTraceMoves r ms)).1 :=
  b5_runMoves_append_fst ms ms' (setupTrace r)

theorem runVis_append (r : ProtocolSetup) (ms ms' : List Move) :
    runVis r (ms ++ ms') = runVis r ms ++ (runMoves ms' (runTraceMoves r ms)).2 := by
  rw [b5_runVis_eq, b5_runVis_eq, b5_runMoves_append_snd, List.append_assoc]; rfl

theorem runTrace_snoc (r : ProtocolSetup) (ms : List Move) (m : Move) :
    runTraceMoves r (ms ++ [m]) = m.next (runTraceMoves r ms) := by
  rw [runTrace_append]; rfl

theorem runVis_snoc (r : ProtocolSetup) (ms : List Move) (m : Move) :
    runVis r (ms ++ [m]) = runVis r ms ++ m.vis (runTraceMoves r ms) := by
  rw [runVis_append]; simp [runMoves]

/-! ## Per-move `next` / reachability -/

private theorem b5_run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β)
    (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem b5_run_bind_pure_val {α : Type} (x : Traceful α) (tr : ExecTrace) :
    ((x >>= fun _ => pure ()).run tr).2.val = (x.run tr).2.val := by
  rw [b5_run_bind_snd]
  rcases (x.run tr).1 with _ | _
  · rfl
  · rw [Traceful.run_pure]

theorem b5_aliceStart_next (a b : Participant) (idStateIdx regIdxB : Nat) (hh : BundleHandles)
    (shown : Nat) (tr : ExecTrace) :
    (Move.aliceStart a b idStateIdx regIdxB hh shown).next tr =
      ((Composed.aliceStart a b idStateIdx regIdxB hh).run tr).2.val :=
  b5_run_bind_pure_val _ tr

theorem b5_bobStart_next (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (shown : Nat) (tr : ExecTrace) :
    (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next tr =
      ((Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val :=
  b5_run_bind_pure_val _ tr

theorem b5_aliceStart_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    (a b : Participant) (idStateIdx regIdxB : Nat) (hh : BundleHandles) (shown : Nat) :
    ((Move.aliceStart a b idStateIdx regIdxB hh shown).next tr).Reachable reachability := by
  rw [b5_aliceStart_next]
  exact (Traceful.PreservesReachability_base aliceStart.reachability reachability
    (a, b, idStateIdx, regIdxB, hh) tr h trivial).1

theorem b5_bobStart_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat) (mh : PreKeyMsgHandles)
    (pqIdx : Nat) (spqrMsgIdx : UInt32) (shown : Nat) :
    ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next tr).Reachable
      reachability := by
  rw [b5_bobStart_next]
  exact (Traceful.PreservesReachability_base bobStart.reachability reachability
    (b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx) tr h trivial).1

theorem b5_reject_next (draws : List Nat) (tr : ExecTrace) : (Move.reject draws).next tr = tr := by
  dsimp only [Move.next, Move.act]
  rw [Traceful.run_pure]

theorem b5_reject_reachable {tr : ExecTrace} (h : tr.Reachable reachability) (draws : List Nat) :
    ((Move.reject draws).next tr).Reachable reachability := by
  rw [b5_reject_next]
  exact h

theorem b5_attackerSend_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    (msg : DY.Bytes) (hk : msg.AttackerKnows tr) :
    ((Move.attackerSend msg).next tr).Reachable reachability := by
  dsimp only [Move.next, Move.act]
  rw [b5_run_bind_pure_val]
  exact (Traceful.PreservesReachability_base DY.Network.reachability reachability msg tr h hk).1

/-! ## `ModelRun` algebra -/

theorem b5_movesAnchored_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    MovesAnchored (ms₁ ++ ms₂) tr ↔
      MovesAnchored ms₁ tr ∧ MovesAnchored ms₂ (runMoves ms₁ tr).1
  | [], _, _ => by simp [MovesAnchored, runMoves]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, MovesAnchored, runMoves_cons_fst,
      b5_movesAnchored_append ms₁ ms₂ (m.next tr), and_assoc]

theorem b5_compromisesCurrentFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    compromisesCurrentFrom tr (ms₁ ++ ms₂) =
      (compromisesCurrentFrom tr ms₁ && compromisesCurrentFrom (runMoves ms₁ tr).1 ms₂)
  | [], _, _ => by simp [compromisesCurrentFrom, runMoves]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, compromisesCurrentFrom, runMoves_cons_fst,
      b5_compromisesCurrentFrom_append ms₁ ms₂ (m.next tr), Bool.and_assoc]

theorem b5_ownSaltsFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    ownSaltsFrom tr (ms₁ ++ ms₂) =
      (ownSaltsFrom tr ms₁ && ownSaltsFrom (runMoves ms₁ tr).1 ms₂)
  | [], _, _ => by simp [ownSaltsFrom, runMoves]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, ownSaltsFrom, runMoves_cons_fst,
      b5_ownSaltsFrom_append ms₁ ms₂ (m.next tr), Bool.and_assoc]

theorem b5_modelRun_snoc {r : ProtocolSetup} {ms : List Move} {m : Move} (hrun : ModelRun r ms)
    (hset : m.isSetup = false)
    (hreach : (m.next (runTraceMoves r ms)).Reachable reachability)
    (hanch : m.LogsSessionCompletion (runTraceMoves r ms))
    (hcur : compromisesCurrentFrom (runTraceMoves r ms) [m] = true)
    (hsalt : ownSaltsFrom (runTraceMoves r ms) [m] = true)
    (hpeer : m.MatchesSetupPeer r)
    (hload : ∀ p k b, m.stateLoad? = some (p, k, b) →
      TripleRatchet.isCurrentSnapshot (runTraceMoves r ms) k = true) :
    ModelRun r (ms ++ [m]) := by
  refine modelRun_snoc_of_old hrun ?_ hpeer
    (stateFaithful_snoc_of_isCurrentSnapshot hrun.2.2.2.2.2.2 hload)
  obtain ⟨hlen, hns, ⟨_, hanc, -⟩, hcc, hos, -, -⟩ := hrun
  refine ⟨hlen, fun m' hm' => ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rcases List.mem_append.mp hm' with hm' | hm'
    · exact hns m' hm'
    · rw [List.mem_singleton.mp hm']; exact hset
  · rw [runTrace_snoc]; exact hreach
  · rw [b5_movesAnchored_append]
    exact ⟨hanc, hanch, trivial⟩
  · rw [b5_compromisesCurrentFrom_append, hcc]; exact hcur
  · rw [b5_ownSaltsFrom_append, hos]; exact hsalt

/-- Conditions under which a single move `m` validly extends a `ModelRun` at trace `tr`. -/
def MoveOK (r : ProtocolSetup) (tr : ExecTrace) (m : Move) : Prop :=
  m.isSetup = false ∧ (m.next tr).Reachable reachability ∧ m.LogsSessionCompletion tr ∧
    compromisesCurrentFrom tr [m] = true ∧ ownSaltsFrom tr [m] = true ∧
    m.MatchesSetupPeer r ∧
    (∀ p k b, m.stateLoad? = some (p, k, b) → TripleRatchet.isCurrentSnapshot tr k = true)

/-- `ModelRun` is closed under appending a `MoveOK` move. -/
theorem modelRun_snoc (r : ProtocolSetup) (ms : List Move) (m : Move) (h : ModelRun r ms)
    (hm : MoveOK r (runTraceMoves r ms) m) : ModelRun r (ms ++ [m]) :=
  b5_modelRun_snoc h hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2.1 hm.2.2.2.2.2.1 hm.2.2.2.2.2.2

theorem b5_modelRun_reachable {r : ProtocolSetup} {ms : List Move} (hrun : ModelRun r ms) :
    (runTraceMoves r ms).Reachable reachability := hrun.2.2.1.1

/-! ## Per-move `MoveOK` and `ModelRun` corollaries -/

theorem moveOK_reject {r : ProtocolSetup} {tr : ExecTrace} (h : tr.Reachable reachability)
    (draws : List Nat) : MoveOK r tr (.reject draws) :=
  ⟨rfl, b5_reject_reachable h draws, trivial, rfl, rfl, trivial, fun _ _ _ hm => nomatch hm⟩

theorem modelRun_snoc_reject {r : ProtocolSetup} {ms : List Move} (hrun : ModelRun r ms)
    (draws : List Nat) : ModelRun r (ms ++ [.reject draws]) :=
  modelRun_snoc r ms _ hrun (moveOK_reject (b5_modelRun_reachable hrun) draws)

theorem moveOK_attackerSend {r : ProtocolSetup} {tr : ExecTrace} (h : tr.Reachable reachability)
    (msg : DY.Bytes) (hk : msg.AttackerKnows tr) : MoveOK r tr (.attackerSend msg) :=
  ⟨rfl, b5_attackerSend_reachable h msg hk, trivial, rfl, rfl, trivial,
    fun _ _ _ hm => nomatch hm⟩

/-! ## `callCount`, `callStarts`, `RoleFaithful`, `PathFaithful`, and `OutcomeFaithful` -/

@[simp] theorem callCount_nil : callCount [] = 0 := rfl
@[simp] theorem callStarts_nil : callStarts [] = [] := rfl

theorem callCount_append (vs₁ vs₂ : List VisEntry) :
    callCount (vs₁ ++ vs₂) = callCount vs₁ + callCount vs₂ := by
  unfold callCount; rw [List.filter_append, List.length_append]

theorem callStarts_append (τ₁ τ₂ : List MachineEvent) :
    callStarts (τ₁ ++ τ₂) = callStarts τ₁ ++ callStarts τ₂ := by
  unfold callStarts; rw [List.filter_append]

theorem callCount_eq_callStarts_length {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {τ : List MachineEvent} {vs : List VisEntry}
    (h : List.Forall₂ (EventMatchesEntry interpretation r S g) τ vs) :
    callCount vs = (callStarts τ).length := by
  induction h with
  | nil => rfl
  | @cons _ _ _ _ hm _ ih =>
    unfold callCount callStarts at ih ⊢
    simp only [List.filter_cons, hm.1]
    split <;> simp [ih]

theorem roleFaithful_nil (r : ProtocolSetup) (who : List Participant) : RoleFaithful r who [] := by
  intro _ _ _ hi; simp at hi

theorem roleFaithful_prefix {r : ProtocolSetup} {who : List Participant} {ms₁ ms₂ : List Move}
    (h : RoleFaithful r who (ms₁ ++ ms₂)) : RoleFaithful r who ms₁ := by
  intro i m p hi hp
  have hlt : i < ms₁.length := (List.getElem?_eq_some_iff.mp hi).1
  simpa [List.take_append_of_le_length (Nat.le_of_lt hlt)] using
    h i m p ((List.getElem?_append_left hlt).trans hi) hp

theorem roleFaithful_append {r : ProtocolSetup} {who : List Participant} {ms₁ ms₂ : List Move}
    (h₁ : RoleFaithful r who ms₁)
    (h₂ : ∀ j m p, ms₂[j]? = some m → m.party? = some p →
      who[callCount (runVis r (ms₁ ++ ms₂.take j))]? = some p) :
    RoleFaithful r who (ms₁ ++ ms₂) := by
  intro i m p hi hp
  by_cases hlt : i < ms₁.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact h₁ i m p hi hp
  · have hge := Nat.le_of_not_lt hlt
    rw [List.getElem?_append_right hge] at hi
    rw [List.take_append, List.take_of_length_le hge]
    exact h₂ (i - ms₁.length) m p hi hp

theorem roleFaithful_snoc_none {r : ProtocolSetup} {who : List Participant} {ms : List Move} {m : Move}
    (h : RoleFaithful r who ms) (hm : m.party? = none) :
    RoleFaithful r who (ms ++ [m]) := by
  refine roleFaithful_append h fun j _ _ hj hp => ?_
  rcases j with _ | j
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj; rw [hm] at hp; cases hp
  · simp at hj

theorem roleFaithful_snoc_party {r : ProtocolSetup} {who : List Participant} {ms : List Move}
    {m : Move} {p : Participant} (h : RoleFaithful r who ms) (hm : m.party? = some p)
    (hwho : who[callCount (runVis r ms)]? = some p) :
    RoleFaithful r who (ms ++ [m]) := by
  refine roleFaithful_append h fun j _ _ hj hq => ?_
  rcases j with _ | j
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj; rw [hm, Option.some.injEq] at hq; subst hq; simpa using hwho
  · simp at hj

theorem pathFaithful_nil (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (τ₁ : List MachineEvent) : PathFaithful interpretation r S g [] τ₁ := by
  intro _ _ _ _ _ hi; simp at hi

theorem pathFaithful_prefix {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms₁ ms₂ : List Move} {acc₁ acc₂ : List MachineEvent}
    (h : PathFaithful interpretation r S g (ms₁ ++ ms₂) (acc₁ ++ acc₂)) :
    PathFaithful interpretation r S g ms₁ acc₁ := by
  intro i m promote b p hi hpath hcall hparse
  have hlt_i : i < ms₁.length := (List.getElem?_eq_some_iff.mp hi).1
  have hlt_k : callCount (runVis r (ms₁.take i)) < (callStarts acc₁).length :=
    (List.getElem?_eq_some_iff.mp hcall).1
  have htake : (ms₁ ++ ms₂).take i = ms₁.take i :=
    List.take_append_of_le_length (Nat.le_of_lt hlt_i)
  have hcall' :
      (callStarts (acc₁ ++ acc₂))[callCount (runVis r ((ms₁ ++ ms₂).take i))]? = some (.recv b) := by
    rw [htake, callStarts_append, List.getElem?_append_left hlt_k]
    exact hcall
  simpa [htake] using h i m promote b p ((List.getElem?_append_left hlt_i).trans hi) hpath hcall' hparse

theorem pathFaithful_snoc_none {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {m : Move} {τ₁ : List MachineEvent}
    (h : PathFaithful interpretation r S g ms τ₁) (hm : m.prekeyPath? = none) :
    PathFaithful interpretation r S g (ms ++ [m]) τ₁ := by
  intro i m' promote b p hi hpath hcall hparse
  by_cases hlt : i < ms.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at hcall ⊢
    exact h i m' promote b p hi hpath hcall hparse
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
    rcases heq : i - ms.length with _ | _
    · rw [heq, List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi; rw [hm] at hpath; cases hpath
    · rw [heq] at hi; simp at hi

theorem outcomeFaithful_append {r : ProtocolSetup} {ok : Nat → Bool} {ms₁ ms₂ : List Move}
    (h₁ : OutcomeFaithful r ok ms₁)
    (h₂ : ∀ j m, ms₂[j]? = some m →
      let k := callCount (runVis r (ms₁ ++ ms₂.take j))
      (∀ ds, m = .reject ds → ok k = false) ∧
      ((eventIdx isAliceDone (runTraceMoves r (ms₁ ++ ms₂.take j))
        (m.next (runTraceMoves r (ms₁ ++ ms₂.take j)))).isSome → ok k = true)) :
    OutcomeFaithful r ok (ms₁ ++ ms₂) := by
  intro i m hi
  by_cases hlt : i < ms₁.length
  · rw [List.getElem?_append_left hlt] at hi
    simpa [List.take_append_of_le_length (Nat.le_of_lt hlt)] using h₁ i m hi
  · have hge := Nat.le_of_not_lt hlt
    rw [List.getElem?_append_right hge] at hi
    simpa [List.take_append, List.take_of_length_le hge] using h₂ (i - ms₁.length) m hi

theorem outcomeFaithful_snoc_neutral {r : ProtocolSetup} {ok : Nat → Bool} {ms : List Move} {m : Move}
    (h : OutcomeFaithful r ok ms) (hnotRej : ∀ ds, m ≠ .reject ds)
    (hnoDone : eventIdx isAliceDone (runTraceMoves r ms) (m.next (runTraceMoves r ms)) = none) :
    OutcomeFaithful r ok (ms ++ [m]) := by
  refine outcomeFaithful_append h fun j _ hj => ?_
  rcases j with _ | j
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    simp only [List.take_zero, List.append_nil]
    exact ⟨fun ds hrej => absurd hrej (hnotRej ds), fun hs => by rw [hnoDone] at hs; cases hs⟩
  · simp at hj

theorem outcomeFaithful_snoc_reject {r : ProtocolSetup} {ok : Nat → Bool} {ms : List Move}
    (draws : List Nat) (h : OutcomeFaithful r ok ms)
    (hok : ok (callCount (runVis r ms)) = false) :
    OutcomeFaithful r ok (ms ++ [.reject draws]) := by
  refine outcomeFaithful_append h fun j _ hj => ?_
  rcases j with _ | j
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    simp only [List.take_zero, List.append_nil, b5_reject_next]
    exact ⟨fun _ _ => hok, fun hs => by simp [eventIdx, newIndices] at hs⟩
  · simp at hj

/-! ## Hidden moves & `attackerSend` on `MatchedPrefix` / `ExplainsMoves` -/

private theorem b5_readFaithful_snoc_hidden {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move}
    {τ : List MachineEvent} {m : Move}
    (hrf : ReadFaithful interpretation r S g ms τ)
    (hvis : m.vis (runTraceMoves r ms) = []) :
    ReadFaithful interpretation r S g (ms ++ [m]) τ := by
  intro ev hev hk
  rw [runVis_snoc, hvis, List.append_nil] at hev
  have hok := hrf ev hev hk
  have hle : runTraceMoves r ms ≤ runTraceMoves r (ms ++ [m]) := by
    rw [runTrace_snoc]
    exact (m.act.run (runTraceMoves r ms)).2.property
  revert hok
  dsimp only [ReadFaithful] at *
  generalize ev.2.layout = l
  generalize ev.2.terms = ts
  generalize eventBytes ev.1 = b
  cases l <;> try exact id
  case whisper =>
    rcases ts with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> try exact id
    rcases b with _ | ⟨_, body⟩
    · exact id
    · exact fun ⟨hkn, hrest⟩ => ⟨Bytes.AttackerKnows_le _ _ _ hle hkn, hrest⟩
  case preKeyInner =>
    rcases ts with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> try exact id
    exact fun h p hp => ⟨Bytes.AttackerKnows_le _ _ _ hle (h p hp).1, (h p hp).2⟩
  case preKeyRecv =>
    rcases ts with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg, _⟩⟩⟩ <;> try exact id
    exact fun ⟨h1, h2, h3, hrest⟩ =>
      ⟨Bytes.AttackerKnows_le _ _ _ hle h1,
       Bytes.AttackerKnows_le _ _ _ hle h2,
       Bytes.AttackerKnows_le _ _ _ hle h3, hrest⟩

/-- A `MoveOK` move with `party? = none`, `prekeyPath? = none`, and `vis = []` preserves
`MatchedPrefix` against the same machine event trace. -/
theorem matchedPrefix_snoc_hidden {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move}
    {τ : List MachineEvent} {m : Move}
    (hmp : MatchedPrefix interpretation r S who g ms τ)
    (hm : MoveOK r (runTraceMoves r ms) m)
    (hvis : m.vis (runTraceMoves r ms) = [])
    (hparty : m.party? = none)
    (hpath : m.prekeyPath? = none) :
    MatchedPrefix interpretation r S who g (ms ++ [m]) τ := by
  obtain ⟨hcompat, hrun, hrole, hpf, hrf, hfor⟩ := hmp
  refine ⟨hcompat, modelRun_snoc r ms m hrun hm,
    roleFaithful_snoc_none hrole hparty,
    pathFaithful_snoc_none hpf hpath,
    b5_readFaithful_snoc_hidden hrf hvis, ?_⟩
  rw [runVis_snoc, hvis, List.append_nil]
  exact hfor

theorem b5_attackerSend_next (msg : DY.Bytes) (tr : ExecTrace) :
    (Move.attackerSend msg).next tr = tr.append (Network.ExecEntryT.mk msg) := by
  dsimp only [Move.next, Move.act]
  rw [b5_run_bind_pure_val, Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]

theorem vis_attackerSend_nil (msg : DY.Bytes) (tr : ExecTrace) :
    (Move.attackerSend msg).vis tr = [] := by
  rw [vis_attackerSend (b5_attackerSend_next msg tr)]
  apply exposures_eq_nil
  intro j hj
  rw [newIndices_append (Nat.le_refl _), newIndices_self, List.nil_append,
    List.mem_singleton] at hj
  subst hj
  constructor
  · apply pqExposureAt_of_getEventAt_none
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_length]
    rfl
  · apply trExposureAt_of_getEventAt_none
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_length]
    rfl

theorem eventIdx_attackerSend_none (p : PQXDHEvent → Bool) (msg : DY.Bytes) (tr : ExecTrace) :
    eventIdx p tr ((Move.attackerSend msg).next tr) = none := by
  unfold eventIdx
  rw [b5_attackerSend_next, newIndices_append (Nat.le_refl _), newIndices_self, List.nil_append]
  have hnone : ((tr.append (Network.ExecEntryT.mk msg)).getEventAt PQXDHEvent tr.length) = none := by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_length]
    rfl
  simp [hnone]

theorem matchedPrefix_attackerSend {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move}
    {τ : List MachineEvent} {msg : DY.Bytes}
    (hmp : MatchedPrefix interpretation r S who g ms τ)
    (hk : msg.AttackerKnows (runTraceMoves r ms)) :
    MatchedPrefix interpretation r S who g (ms ++ [.attackerSend msg]) τ :=
  matchedPrefix_snoc_hidden hmp (moveOK_attackerSend (b5_modelRun_reachable hmp.2.1) msg hk)
    (vis_attackerSend_nil msg _) rfl rfl

theorem explains_attackerSend {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {ms : List Move} {τ : List MachineEvent} {msg : DY.Bytes}
    (hex : ExplainsMoves interpretation r S who ok g ms τ)
    (hk : msg.AttackerKnows (runTraceMoves r ms)) :
    ExplainsMoves interpretation r S who ok g (ms ++ [.attackerSend msg]) τ :=
  ⟨matchedPrefix_attackerSend hex.1 hk,
    outcomeFaithful_snoc_neutral hex.2 (fun _ h => nomatch h)
      (eventIdx_attackerSend_none isAliceDone msg _)⟩

end Symbolic.Swarm.CREF
