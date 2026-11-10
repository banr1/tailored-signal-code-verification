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
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import ProofLib.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Move-Run Algebra, Faithfulness Predicates, and `MatchedPrefix` Combinators

Compositional append and snoc lemmas for `runMoves`, `ModelRun`, `RoleFaithful`, `PathFaithful`,
`ReadFaithful`, `OutcomeFaithful`, `ReadCollision`, `MatchedPrefix`, `ExplainsMoves`, and `Clean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Leaves.IC12Stage1MP

open DY DY.Comparse DY.Libsignal
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TREvent)
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoProofLib.Refinement (ExternInterpretation)

/-! ## `runMoves`, `runTraceMoves`, `runVis`, and `ModelRun` Algebra -/

theorem move_le_next (m : Move) (tr : ExecTrace) : tr ≤ m.next tr := (m.act.run tr).2.property
@[simp] theorem runMoves_nil (tr : ExecTrace) : runMoves [] tr = (tr, []) := rfl
theorem runMoves_cons_fst (m : Move) (ms : List Move) (tr : ExecTrace) : (runMoves (m :: ms) tr).1 = (runMoves ms (m.next tr)).1 := rfl

theorem runMoves_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    runMoves (ms₁ ++ ms₂) tr = ((runMoves ms₂ (runMoves ms₁ tr).1).1, (runMoves ms₁ tr).2 ++ (runMoves ms₂ (runMoves ms₁ tr).1).2)
  | [], _, _ => by simp [runMoves]
  | m :: ms₁, ms₂, tr => by simp only [List.cons_append, runMoves, runMoves_append ms₁ ms₂ (m.next tr), List.append_assoc]

theorem runMoves_le : ∀ (ms : List Move) (tr : ExecTrace), tr ≤ (runMoves ms tr).1
  | [], tr => Trace.le_refl tr
  | m :: ms, tr => Trace.le_trans _ _ _ (move_le_next m tr) (runMoves_le ms (m.next tr))

theorem runTrace_nil (r : ProtocolSetup) : runTraceMoves r [] = setupTrace r := rfl
theorem runTrace_append (r : ProtocolSetup) (ms₁ ms₂ : List Move) : runTraceMoves r (ms₁ ++ ms₂) = (runMoves ms₂ (runTraceMoves r ms₁)).1 := by
  unfold runTraceMoves; change (runMoves ((r.setupMove :: ms₁) ++ ms₂) Trace.nil).1 = _; rw [runMoves_append]
theorem runTrace_snoc (r : ProtocolSetup) (ms : List Move) (m : Move) : runTraceMoves r (ms ++ [m]) = m.next (runTraceMoves r ms) := by
  rw [runTrace_append]; rfl
theorem runVis_append (r : ProtocolSetup) (ms₁ ms₂ : List Move) : runVis r (ms₁ ++ ms₂) = runVis r ms₁ ++ (runMoves ms₂ (runTraceMoves r ms₁)).2 := by
  unfold runVis runTraceMoves; change (runMoves ((r.setupMove :: ms₁) ++ ms₂) Trace.nil).2 = _; rw [runMoves_append]
theorem runTrace_le_append (r : ProtocolSetup) (ms₁ ms₂ : List Move) : runTraceMoves r ms₁ ≤ runTraceMoves r (ms₁ ++ ms₂) := by
  rw [runTrace_append]; exact runMoves_le ms₂ _
theorem setupTrace_le_runTrace (r : ProtocolSetup) (ms : List Move) : setupTrace r ≤ runTraceMoves r ms := by
  simpa [runTrace_nil] using runTrace_le_append r [] ms
theorem attackerKnows_append {r : ProtocolSetup} {ms : List Move} (ms' : List Move) {t : DY.Bytes}
    (hk : t.AttackerKnows (runTraceMoves r ms)) : t.AttackerKnows (runTraceMoves r (ms ++ ms')) :=
  Bytes.AttackerKnows_le _ _ _ (runTrace_le_append r ms ms') hk

theorem movesAnchored_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    MovesAnchored (ms₁ ++ ms₂) tr ↔ MovesAnchored ms₁ tr ∧ MovesAnchored ms₂ (runMoves ms₁ tr).1
  | [], _, _ => by simp [MovesAnchored]
  | m :: ms₁, ms₂, tr => by simp only [List.cons_append, MovesAnchored, runMoves_cons_fst, movesAnchored_append ms₁ ms₂ (m.next tr), and_assoc]

theorem compromisesCurrentFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    compromisesCurrentFrom tr (ms₁ ++ ms₂) = (compromisesCurrentFrom tr ms₁ && compromisesCurrentFrom (runMoves ms₁ tr).1 ms₂)
  | [], _, _ => by simp [compromisesCurrentFrom]
  | m :: ms₁, ms₂, tr => by simp only [List.cons_append, compromisesCurrentFrom, runMoves_cons_fst, compromisesCurrentFrom_append ms₁ ms₂ (m.next tr), Bool.and_assoc]

theorem ownSaltsFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    ownSaltsFrom tr (ms₁ ++ ms₂) = (ownSaltsFrom tr ms₁ && ownSaltsFrom (runMoves ms₁ tr).1 ms₂)
  | [], _, _ => by simp [ownSaltsFrom]
  | m :: ms₁, ms₂, tr => by simp only [List.cons_append, ownSaltsFrom, runMoves_cons_fst, ownSaltsFrom_append ms₁ ms₂ (m.next tr), Bool.and_assoc]

theorem peerFaithful_append {r : ProtocolSetup} {ms₁ ms₂ : List Move} : PeerFaithful r (ms₁ ++ ms₂) ↔ PeerFaithful r ms₁ ∧ PeerFaithful r ms₂ := List.forall_mem_append
theorem peerFaithful_snoc {r : ProtocolSetup} {ms : List Move} {m : Move} (h : PeerFaithful r ms) (hm : m.MatchesSetupPeer r) : PeerFaithful r (ms ++ [m]) :=
  peerFaithful_append.mpr ⟨h, fun _ hx => by rcases List.mem_singleton.mp hx with rfl; exact hm⟩

theorem stateFaithful_append {r : ProtocolSetup} {ms₁ ms₂ : List Move} (h₁ : StateFaithful r ms₁)
    (hcross : ∀ (i j : Nat) (mi mj : Move) (p : Participant) (k : Nat) (b : Bool), ms₁[i]? = some mi → ms₂[j]? = some mj →
      mi.stateLoad? = some (p, k, true) → (mi.act.run (runTraceMoves r (ms₁.take i))).1.isSome = true → mj.stateLoad? = some (p, k, b) → False)
    (h₂ : ∀ (i j : Nat) (mi mj : Move) (p : Participant) (k : Nat) (b : Bool), i < j → ms₂[i]? = some mi → ms₂[j]? = some mj →
      mi.stateLoad? = some (p, k, true) → (mi.act.run (runTraceMoves r (ms₁ ++ ms₂.take i))).1.isSome = true → mj.stateLoad? = some (p, k, b) → False) :
    StateFaithful r (ms₁ ++ ms₂) := by
  intro i j mi mj p k b hij hi hj hli hok hlj
  by_cases hj1 : j < ms₁.length
  · have hi1 : i < ms₁.length := Nat.lt_trans hij hj1
    rw [List.getElem?_append_left hi1] at hi; rw [List.getElem?_append_left hj1] at hj
    rw [List.take_append_of_le_length (Nat.le_of_lt hi1)] at hok
    exact h₁ i j mi mj p k b hij hi hj hli hok hlj
  · have hj_ge : ms₁.length ≤ j := Nat.le_of_not_lt hj1
    rw [List.getElem?_append_right hj_ge] at hj
    by_cases hi1 : i < ms₁.length
    · rw [List.getElem?_append_left hi1] at hi; rw [List.take_append_of_le_length (Nat.le_of_lt hi1)] at hok
      exact hcross i (j - ms₁.length) mi mj p k b hi hj hli hok hlj
    · have hi_ge : ms₁.length ≤ i := Nat.le_of_not_lt hi1
      rw [List.getElem?_append_right hi_ge] at hi; rw [List.take_append, List.take_of_length_le hi_ge] at hok
      exact h₂ (i - ms₁.length) (j - ms₁.length) mi mj p k b (by omega) hi hj hli hok hlj

theorem stateFaithful_snoc {r : ProtocolSetup} {ms : List Move} {m : Move} (h : StateFaithful r ms)
    (hfresh : ∀ (i : Nat) (mi : Move) (p : Participant) (k : Nat) (b : Bool), ms[i]? = some mi → mi.stateLoad? = some (p, k, true) →
      (mi.act.run (runTraceMoves r (ms.take i))).1.isSome = true → m.stateLoad? = some (p, k, b) → False) :
    StateFaithful r (ms ++ [m]) := by
  refine stateFaithful_append h (fun i j mi mj p k b hi hj hli hok hlj => ?_) (fun _ j _ _ _ _ _ hij _ hj _ _ _ => ?_)
  · rcases j with _ | j
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; exact hfresh i mi p k b hi hli hok hlj
    · simp at hj
  · cases j with | zero => omega | succ _ => simp at hj

theorem runTrace_take_reach_append {r : ProtocolSetup} {ms δ : List Move}
    (hall : ∀ k, (runTraceMoves r (ms.take k)).Reachable reachability)
    (hδ : ∀ j, (runTraceMoves r (ms ++ δ.take j)).Reachable reachability) :
    ∀ k, (runTraceMoves r ((ms ++ δ).take k)).Reachable reachability := by
  intro k; rw [List.take_append]
  by_cases hk : k ≤ ms.length
  · rw [Nat.sub_eq_zero_of_le hk, List.take_zero, List.append_nil]; exact hall k
  · rw [List.take_of_length_le (by omega)]; exact hδ (k - ms.length)

theorem runTrace_take_reach_snoc {r : ProtocolSetup} {ms : List Move} {m : Move}
    (hall : ∀ k, (runTraceMoves r (ms.take k)).Reachable reachability)
    (hlast : (runTraceMoves r (ms ++ [m])).Reachable reachability) :
    ∀ k, (runTraceMoves r ((ms ++ [m]).take k)).Reachable reachability :=
  runTrace_take_reach_append hall fun
    | 0 => by have h := hall ms.length; rw [List.take_length] at h; simpa using h
    | _ + 1 => by simpa using hlast

def MoveOK (r : ProtocolSetup) (m : Move) (tr : ExecTrace) : Prop :=
  m.isSetup = false ∧ m.LogsSessionCompletion tr ∧ m.MatchesSetupPeer r ∧
  (match m with | .exposeKey _ s _ | .exposeSpqr _ s => TripleRatchet.isCurrentSnapshot tr s = true | _ => True) ∧
  (match m with | .encrypt _ _ _ pqIdx _ => pqIdx = tr.length + 2 | _ => True)

theorem modelRun_snoc {r : ProtocolSetup} {ms : List Move} {m : Move}
    (hrun : ModelRun r ms) (hm : MoveOK r m (runTraceMoves r ms))
    (hreach : (runTraceMoves r (ms ++ [m])).Reachable reachability)
    (hstate : ∀ (i : Nat) (mi : Move) (p : Participant) (k : Nat) (b : Bool), ms[i]? = some mi →
      mi.stateLoad? = some (p, k, true) → (mi.act.run (runTraceMoves r (ms.take i))).1.isSome = true →
      m.stateLoad? = some (p, k, b) → False) :
    ModelRun r (ms ++ [m]) := by
  obtain ⟨hsetup, hnosetup, ⟨_, hanc, hreach_all⟩, hcomp, hown, hpeer, hst⟩ := hrun
  obtain ⟨hms, hmanc, hmpeer, hmcomp, hmown⟩ := hm
  refine ⟨hsetup, fun x hx => (List.mem_append.mp hx).elim (hnosetup x) (fun h1 => by rcases List.mem_singleton.mp h1 with rfl; exact hms),
    ⟨hreach, (movesAnchored_append _ _ _).mpr ⟨hanc, hmanc, trivial⟩, runTrace_take_reach_snoc hreach_all hreach⟩, ?_, ?_,
    peerFaithful_snoc hpeer hmpeer, stateFaithful_snoc hst hstate⟩
  · rw [compromisesCurrentFrom_append, Bool.and_eq_true]; refine ⟨hcomp, ?_⟩
    cases m <;> simp_all [compromisesCurrentFrom, setupTrace, setupMove_next_nil', runTraceMoves, runMoves]
  · rw [ownSaltsFrom_append, Bool.and_eq_true]; refine ⟨hown, ?_⟩
    cases m <;> simp_all [ownSaltsFrom, setupTrace, setupMove_next_nil', runTraceMoves, runMoves]

@[simp] theorem reject_next (draws : List Nat) (tr : ExecTrace) : (Move.reject draws).next tr = tr := by
  unfold Move.next Move.act; rw [Traceful.run_pure]
@[simp] theorem attackerSend_next (msg : DY.Bytes) (tr : ExecTrace) :
    (Move.attackerSend msg).next tr = tr.append ({ msg := msg } : Network.ExecEntryT) := by
  unfold Move.next Move.act; dsimp only
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]

theorem modelRun_snoc_reject {r : ProtocolSetup} {ms : List Move} (draws : List Nat) (hrun : ModelRun r ms) :
    ModelRun r (ms ++ [.reject draws]) :=
  modelRun_snoc hrun ⟨rfl, trivial, trivial, trivial, trivial⟩
    (by rw [runTrace_snoc, reject_next]; exact hrun.2.2.1.1) (fun _ _ _ _ _ _ _ _ hm => nomatch hm)

/-! ## `callCount`, `callStarts`, and Faithfulness Predicates -/

@[simp] theorem callCount_nil : callCount [] = 0 := rfl
@[simp] theorem callStarts_nil : callStarts [] = [] := rfl

theorem callCount_eq_callStarts_length {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {τ : List MachineEvent} {vs : List VisEntry}
    (h : List.Forall₂ (EventMatchesEntry interpretation r S g) τ vs) : callCount vs = (callStarts τ).length := by
  induction h with
  | nil => rfl
  | @cons _ _ _ _ hm _ ih => unfold callCount callStarts at ih ⊢; simp only [List.filter_cons, hm.1]; split <;> simp [ih]

theorem roleFaithful_append {r : ProtocolSetup} {who : List Participant} {ms₁ ms₂ : List Move} (h₁ : RoleFaithful r who ms₁)
    (h₂ : ∀ j m p, ms₂[j]? = some m → m.party? = some p → who[callCount (runVis r (ms₁ ++ ms₂.take j))]? = some p) :
    RoleFaithful r who (ms₁ ++ ms₂) := by
  intro i m p hi hp
  by_cases hlt : i < ms₁.length
  · rw [List.getElem?_append_left hlt] at hi; rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]; exact h₁ i m p hi hp
  · have hge := Nat.le_of_not_lt hlt
    rw [List.getElem?_append_right hge] at hi; rw [List.take_append, List.take_of_length_le hge]; exact h₂ (i - ms₁.length) m p hi hp

theorem roleFaithful_snoc_none {r : ProtocolSetup} {who : List Participant} {ms : List Move} {m : Move}
    (h : RoleFaithful r who ms) (hm : m.party? = none) : RoleFaithful r who (ms ++ [m]) := by
  refine roleFaithful_append h fun j _ _ hj hp => ?_
  rcases j with _ | j; · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; rw [hm] at hp; cases hp
  · simp at hj

theorem pathFaithful_snoc_none {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {m : Move} {τ₁ : List MachineEvent}
    (h : PathFaithful interpretation r S g ms τ₁) (hm : m.prekeyPath? = none) :
    PathFaithful interpretation r S g (ms ++ [m]) τ₁ := by
  intro i m' promote b p hi hpath hcall hparse
  by_cases hlt : i < ms.length
  · rw [List.getElem?_append_left hlt] at hi; rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at hcall ⊢
    exact h i m' promote b p hi hpath hcall hparse
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
    rcases heq : i - ms.length with _ | _
    · rw [heq, List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; rw [hm] at hpath; cases hpath
    · rw [heq] at hi; simp at hi

private theorem mem_snd_of_mem_zip :
    ∀ {α β : Type} {xs : List α} {ys : List β} {p : α × β}, p ∈ xs.zip ys → p.2 ∈ ys
  | _, _, [], _, _, h => nomatch h
  | _, _, _ :: _, [], _, h => nomatch h
  | _, _, _ :: _, _ :: _, _, h =>
    (List.mem_cons.mp h).elim (fun heq => heq ▸ List.mem_cons_self)
      (fun h' => List.mem_cons_of_mem _ (mem_snd_of_mem_zip h'))

def ReadOKWith (R : HwBytes → Set DY.Bytes) (P : HwBytes → Set PreKeyRep)
    (e : MachineEvent) (v : VisEntry) : Prop :=
  match v.layout, v.terms, eventBytes e with
  | .whisper, [t], _ :: body => t ∈ R body
  | .preKeyInner _, [t], b => ∀ p, parsePreKeyWire b = some p → t ∈ R p.message
  | .preKeyRecv, ek :: ct :: msg :: _, b => ⟨ek, ct, msg⟩ ∈ P b
  | _, _, _ => True

theorem ReadOKWith.mono {R R' : HwBytes → Set DY.Bytes} {P P' : HwBytes → Set PreKeyRep}
    (hR : ∀ b, R b ⊆ R' b) (hP : ∀ b, P b ⊆ P' b) {e : MachineEvent} {v : VisEntry}
    (h : ReadOKWith R P e v) : ReadOKWith R' P' e v := by
  revert h; unfold ReadOKWith
  generalize v.layout = l; generalize v.terms = ts; generalize eventBytes e = b
  cases l <;> try exact id
  case whisper =>
    rcases ts with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> try exact id
    rcases b with _ | ⟨_, body⟩
    · exact id
    · exact fun h => hR _ h
  case preKeyInner =>
    rcases ts with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> try exact id
    exact fun h p hp => hR _ (h p hp)
  case preKeyRecv =>
    rcases ts with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg, _⟩⟩⟩ <;> try exact id
    exact fun h => hP _ h

theorem recvRepresentations_append_subset (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ms ms' : List Move) (b : HwBytes) :
    recvRepresentations interpretation r S g ms b ⊆ recvRepresentations interpretation r S g (ms ++ ms') b :=
  fun _ ⟨hk, hrest⟩ => ⟨attackerKnows_append ms' hk, hrest⟩

theorem preKeyRepresentations_append_subset (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ms ms' : List Move) (b : HwBytes) :
    preKeyRepresentations interpretation r S g ms b ⊆ preKeyRepresentations interpretation r S g (ms ++ ms') b :=
  fun _ ⟨h1, h2, h3, hrest⟩ => ⟨attackerKnows_append ms' h1, attackerKnows_append ms' h2, attackerKnows_append ms' h3, hrest⟩

theorem readFaithful_append {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms ms' : List Move} {acc blk : List MachineEvent}
    (hlen : acc.length = (runVis r ms).length) (h : ReadFaithful interpretation r S g ms acc)
    (hblk : ∀ ev ∈ blk.zip (runMoves ms' (runTraceMoves r ms)).2, ev.2.kind = .recv →
      ReadOKWith (recvRepresentations interpretation r S g (ms ++ ms')) (preKeyRepresentations interpretation r S g (ms ++ ms')) ev.1 ev.2) :
    ReadFaithful interpretation r S g (ms ++ ms') (acc ++ blk) := by
  intro ev hev hk; rw [runVis_append, List.zip_append hlen] at hev
  exact (List.mem_append.mp hev).elim
    (fun h1 => ReadOKWith.mono (recvRepresentations_append_subset interpretation r S g ms ms')
      (preKeyRepresentations_append_subset interpretation r S g ms ms') (h ev h1 hk)) (fun h2 => hblk ev h2 hk)

theorem outcomeFaithful_append {r : ProtocolSetup} {ok : Nat → Bool} {ms₁ ms₂ : List Move} (h₁ : OutcomeFaithful r ok ms₁)
    (h₂ : ∀ j m, ms₂[j]? = some m → let k := callCount (runVis r (ms₁ ++ ms₂.take j))
      (∀ ds, m = .reject ds → ok k = false) ∧ ((eventIdx isAliceDone (runTraceMoves r (ms₁ ++ ms₂.take j)) (m.next (runTraceMoves r (ms₁ ++ ms₂.take j)))).isSome → ok k = true)) :
    OutcomeFaithful r ok (ms₁ ++ ms₂) := by
  intro i m hi
  by_cases hlt : i < ms₁.length
  · rw [List.getElem?_append_left hlt] at hi; simpa [List.take_append_of_le_length (Nat.le_of_lt hlt)] using h₁ i m hi
  · have hge := Nat.le_of_not_lt hlt; rw [List.getElem?_append_right hge] at hi
    simpa [List.take_append, List.take_of_length_le hge] using h₂ (i - ms₁.length) m hi

theorem outcomeFaithful_snoc_reject {r : ProtocolSetup} {ok : Nat → Bool} {ms : List Move}
    (draws : List Nat) (h : OutcomeFaithful r ok ms) (hok : ok (callCount (runVis r ms)) = false) :
    OutcomeFaithful r ok (ms ++ [.reject draws]) := by
  refine outcomeFaithful_append h fun j _ hj => ?_
  rcases j with _ | j
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; simp only [List.take_zero, List.append_nil, reject_next]
    exact ⟨fun _ _ => hok, fun hs => by simp [eventIdx, newIndices] at hs⟩
  · simp at hj

private theorem append_split_of_mem_not_mem {α : Type} :
    ∀ {acc blk τ₁ : List α} {e x : α} {τ₂ : List α},
      acc ++ blk = τ₁ ++ e :: τ₂ → x ∈ τ₂ → x ∉ blk → ∃ τ₂₀, acc = τ₁ ++ e :: τ₂₀ ∧ τ₂ = τ₂₀ ++ blk
  | [], _, _, _, _, _, h, hx, hnb => by
    rw [List.nil_append] at h; subst h
    exact absurd (List.mem_append_right _ (List.mem_cons_of_mem _ hx)) hnb
  | a :: acc', _, [], _, _, _, h, _, _ => by
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact ⟨acc', by rw [h.1]; rfl, h.2.symm⟩
  | a :: acc', _, b :: τ₁', _, _, _, h, hx, hnb => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨τ₂₀, hacc', hτ₂⟩ := append_split_of_mem_not_mem h.2 hx hnb
    exact ⟨τ₂₀, by rw [h.1, hacc']; rfl, hτ₂⟩

theorem not_readCollision_append_noAccept {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms ms' : List Move} {acc blk : List MachineEvent}
    (hnoRc : ¬ ReadCollision interpretation r S g ms acc)
    (hnoAcc : ∀ e ∈ blk, ∀ pt, e ≠ .accept pt)
    (hnoCol : ∀ m ∈ ms', ∀ pre e, ¬ MoveReadsCollidingMsg interpretation r S g pre e m) :
    ¬ ReadCollision interpretation r S g (ms ++ ms') (acc ++ blk) := by
  rintro ⟨i, τ₁, e, τ₂, m, hsplit, hmi, hF₁, ⟨pt, hpt⟩, hcol⟩
  by_cases hlt : i < ms.length
  · rw [List.getElem?_append_left hlt] at hmi
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at hF₁ hcol
    have hmem_τ₂ : MachineEvent.accept pt ∈ τ₂ := (List.mem_filter.mp (List.mem_of_head? hpt)).1
    obtain ⟨τ₂₀, hacc_eq, hτ₂_eq⟩ := append_split_of_mem_not_mem hsplit hmem_τ₂ (fun hb => hnoAcc _ hb pt rfl)
    rw [hτ₂_eq, List.filter_append] at hpt
    have hpt₀ : (τ₂₀.filter fun ev => eventKind ev != .rng).head? = some (.accept pt) := by
      rcases hf : τ₂₀.filter (fun ev => eventKind ev != .rng) with _ | _
      · rw [hf, List.nil_append] at hpt
        exact absurd rfl (hnoAcc _ (List.mem_filter.mp (List.mem_of_head? hpt)).1 pt)
      · rw [hf, List.cons_append] at hpt; exact hpt
    exact hnoRc ⟨i, τ₁, e, τ₂₀, m, hacc_eq, hmi, hF₁, ⟨pt, hpt₀⟩, hcol⟩
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hmi
    exact hnoCol m (List.mem_of_getElem? hmi) _ e hcol

/-! ## `MatchedPrefix`, `ExplainsMoves`, and `Clean` Combinators -/

def Clean (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost) (ms : List Move) (τ₁ : List MachineEvent) : Prop :=
  ExplainsMoves interpretation r S who ok g ms τ₁ ∧ ¬ ReadCollision interpretation r S g ms τ₁

theorem matchedPrefix_length_eq {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (h : MatchedPrefix interpretation r S who g ms τ) : τ.length = (runVis r ms).length :=
  h.2.2.2.2.2.length_eq

theorem matchedPrefix_callCount_eq {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (h : MatchedPrefix interpretation r S who g ms τ) : callCount (runVis r ms) = (callStarts τ).length :=
  callCount_eq_callStarts_length h.2.2.2.2.2

private theorem forall₂_append_join {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m₁ m₂ : List β},
      List.Forall₂ R l₁ m₁ → List.Forall₂ R l₂ m₂ → List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂)
  | _, _, _, _, .nil, h₂ => h₂
  | _, _, _, _, .cons hab h₁, h₂ => .cons hab (forall₂_append_join h₁ h₂)

theorem matchedPrefix_append {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms ms' : List Move} {acc blk : List MachineEvent}
    (hmp : MatchedPrefix interpretation r S who g ms acc) (hrun : ModelRun r (ms ++ ms'))
    (hrole : RoleFaithful r who (ms ++ ms'))
    (hpath : PathFaithful interpretation r S g (ms ++ ms') (acc ++ blk))
    (hread_blk : ∀ ev ∈ blk.zip (runMoves ms' (runTraceMoves r ms)).2, ev.2.kind = .recv →
      ReadOKWith (recvRepresentations interpretation r S g (ms ++ ms'))
        (preKeyRepresentations interpretation r S g (ms ++ ms')) ev.1 ev.2)
    (hF_blk : List.Forall₂ (EventMatchesEntry interpretation r S g) blk (runMoves ms' (runTraceMoves r ms)).2) :
    MatchedPrefix interpretation r S who g (ms ++ ms') (acc ++ blk) := by
  refine ⟨hmp.1, hrun, hrole, hpath, readFaithful_append (matchedPrefix_length_eq hmp) hmp.2.2.2.2.1 hread_blk, ?_⟩
  rw [runVis_append]; exact forall₂_append_join hmp.2.2.2.2.2 hF_blk

theorem matchedPrefix_snoc_hidden {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {m : Move} {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r S who g ms τ) (hmok : MoveOK r m (runTraceMoves r ms))
    (hreach : (runTraceMoves r (ms ++ [m])).Reachable reachability) (hvis : m.vis (runTraceMoves r ms) = [])
    (hparty : m.party? = none) (hpath : m.prekeyPath? = none) (hload : m.stateLoad? = none) :
    MatchedPrefix interpretation r S who g (ms ++ [m]) τ := by
  have hrun' := modelRun_snoc hmp.2.1 hmok hreach (fun _ _ _ _ _ _ _ _ hl => by rw [hload] at hl; cases hl)
  simpa using matchedPrefix_append (blk := []) hmp hrun' (roleFaithful_snoc_none hmp.2.2.1 hparty)
    (by simpa using pathFaithful_snoc_none hmp.2.2.2.1 hpath) (by simp) (by simp [runMoves, hvis])

private theorem append_at_length {Entry E1 : Type} [DY.TraceEntryHas E1 Entry]
    (tr : DY.Trace Entry) (e : E1) (h : tr.length < (tr.append e).length) :
    (tr.append e).at tr.length h = DY.TraceEntryHas.inj e := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

private theorem attackerSend_newIndices (msg : DY.Bytes) (tr : ExecTrace) :
    newIndices tr ((Move.attackerSend msg).next tr) = [tr.length] := by
  have hlen : (tr.append ({ msg := msg } : Network.ExecEntryT)).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  simp [attackerSend_next, newIndices, hlen]

private theorem attackerSend_at?_pq (msg : DY.Bytes) (tr : ExecTrace) :
    ((tr.append ({ msg := msg } : Network.ExecEntryT)).at? tr.length :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by
  have hlt : tr.length < (tr.append ({ msg := msg } : Network.ExecEntryT)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, ↓reduceDIte, append_at_length]; rfl

private theorem attackerSend_at?_tr (msg : DY.Bytes) (tr : ExecTrace) :
    ((tr.append ({ msg := msg } : Network.ExecEntryT)).at? tr.length :
      Option (ProtocolEvent.ExecEntryT TREvent)) = none := by
  have hlt : tr.length < (tr.append ({ msg := msg } : Network.ExecEntryT)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, ↓reduceDIte, append_at_length]; rfl

private theorem attackerSend_vis (msg : DY.Bytes) (tr : ExecTrace) : (Move.attackerSend msg).vis tr = [] := by
  unfold Move.vis; dsimp only [List.nil_append]; unfold exposures
  rw [attackerSend_newIndices, attackerSend_next]
  simp [pqExposureAt, trExposureAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, attackerSend_at?_pq, attackerSend_at?_tr]

theorem matchedPrefix_attackerSend {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {msg : DY.Bytes} {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r S who g ms τ)
    (hreach : (runTraceMoves r (ms ++ [.attackerSend msg])).Reachable reachability) :
    MatchedPrefix interpretation r S who g (ms ++ [.attackerSend msg]) τ :=
  matchedPrefix_snoc_hidden hmp ⟨rfl, trivial, trivial, trivial, trivial⟩ hreach (attackerSend_vis msg _) rfl rfl rfl

private theorem forall₂_reject_rng (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) :
    ∀ (ds : List HwBytes), List.Forall₂ (EventMatchesEntry interpretation r S g) (ds.map .rng)
      ((ds.map List.length).map fun n => ⟨.rng, [], .fresh n, none⟩)
  | [] => .nil
  | _ :: tl => .cons ⟨rfl, rfl⟩ (forall₂_reject_rng interpretation r S g tl)

theorem matchedPrefix_snoc_reject {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    (b : HwBytes) (ds : List HwBytes) (hmp : MatchedPrefix interpretation r S who g ms acc)
    (hpath : PathFaithful interpretation r S g ms (acc ++ (.recv b :: ds.map .rng))) :
    MatchedPrefix interpretation r S who g (ms ++ [.reject (ds.map List.length)]) (acc ++ (.recv b :: ds.map .rng)) := by
  have hF_blk : List.Forall₂ (EventMatchesEntry interpretation r S g) (.recv b :: ds.map .rng)
      (runMoves [.reject (ds.map List.length)] (runTraceMoves r ms)).2 := by
    simp only [runMoves, List.append_nil, Move.vis, reject_next, exposures, newIndices, Nat.sub_self, List.range'_zero, List.filterMap_nil]
    exact .cons ⟨rfl, trivial⟩ (forall₂_reject_rng interpretation r S g ds)
  exact matchedPrefix_append hmp (modelRun_snoc_reject _ hmp.2.1)
    (roleFaithful_snoc_none hmp.2.2.1 rfl) (pathFaithful_snoc_none hpath rfl)
    (fun ev hev hk => by
      simp only [runMoves, List.append_nil] at hev; have hv := mem_snd_of_mem_zip hev
      simp only [Move.vis, reject_next, exposures, newIndices, Nat.sub_self, List.range'_zero, List.filterMap_nil, List.append_nil, List.mem_cons] at hv
      rcases hv with heq | hv; · rw [heq]; trivial
      · obtain ⟨_, _, heq⟩ := List.mem_map.mp hv; rw [← heq] at hk; cases hk) hF_blk

theorem explains_snoc_reject {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    (b : HwBytes) (ds : List HwBytes) (hex : ExplainsMoves interpretation r S who ok g ms acc)
    (hpath : PathFaithful interpretation r S g ms (acc ++ (.recv b :: ds.map .rng)))
    (hok : ok (callStarts acc).length = false) :
    ExplainsMoves interpretation r S who ok g (ms ++ [.reject (ds.map List.length)]) (acc ++ (.recv b :: ds.map .rng)) :=
  ⟨matchedPrefix_snoc_reject b ds hex.1 hpath, outcomeFaithful_snoc_reject _ hex.2 (by rwa [matchedPrefix_callCount_eq hex.1])⟩

theorem clean_snoc_reject {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    (b : HwBytes) (ds : List HwBytes) (hcl : Clean interpretation r S who ok g ms acc)
    (hpath : PathFaithful interpretation r S g ms (acc ++ (.recv b :: ds.map .rng)))
    (hok : ok (callStarts acc).length = false) :
    Clean interpretation r S who ok g (ms ++ [.reject (ds.map List.length)]) (acc ++ (.recv b :: ds.map .rng)) := by
  refine ⟨explains_snoc_reject b ds hcl.1 hpath hok, not_readCollision_append_noAccept hcl.2 (fun e he _ heq => ?_)
    (fun m hm _ _ hc => by rcases List.mem_singleton.mp hm with rfl; exact hc)⟩
  rcases List.mem_cons.mp he with rfl | he; · cases heq
  · obtain ⟨_, _, h'⟩ := List.mem_map.mp he; rw [← h'] at heq; cases heq

end Symbolic.Swarm.Leaves.IC12Stage1MP
