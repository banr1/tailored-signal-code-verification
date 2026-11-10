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
import Mathlib.Data.List.Forall2
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
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
# Composed Trace-Prefix Explanation Combinators

Prefix-cutting and single-step extension lemmas for `runMoves`, `ModelRun`, `RoleFaithful`,
`PathFaithful`, `ReadFaithful`, `OutcomeFaithful`, `ReadCollision`, `MatchedPrefix`,
`ExplainsMoves`, and `Clean`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement

open DY DY.Comparse DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TREvent)
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoProofLib.Refinement (ExternInterpretation)

/-! ## Trace Execution and `MoveOK` Steppers -/

private theorem mp_move_le_next (m : Move) (tr : ExecTrace) : tr ≤ m.next tr :=
  (m.act.run tr).2.property

private theorem mp_runMoves_le : ∀ (ms : List Move) (tr : ExecTrace), tr ≤ (runMoves ms tr).1
  | [], tr => Trace.le_refl tr
  | m :: ms, tr => Trace.le_trans _ _ _ (mp_move_le_next m tr) (mp_runMoves_le ms (m.next tr))

theorem runMoves_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    runMoves (ms₁ ++ ms₂) tr =
      ((runMoves ms₂ (runMoves ms₁ tr).1).1, (runMoves ms₁ tr).2 ++ (runMoves ms₂ (runMoves ms₁ tr).1).2)
  | [], _, _ => by simp [runMoves]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, runMoves, runMoves_append ms₁ ms₂ (m.next tr), List.append_assoc]

theorem runTrace_nil (r : ProtocolSetup) : runTraceMoves r [] = setupTrace r := rfl

theorem runTrace_append (r : ProtocolSetup) (ms₁ ms₂ : List Move) :
    runTraceMoves r (ms₁ ++ ms₂) = (runMoves ms₂ (runTraceMoves r ms₁)).1 := by
  unfold runTraceMoves
  change (runMoves ((r.setupMove :: ms₁) ++ ms₂) Trace.nil).1 = _
  rw [runMoves_append]

theorem runTrace_snoc (r : ProtocolSetup) (ms : List Move) (m : Move) :
    runTraceMoves r (ms ++ [m]) = m.next (runTraceMoves r ms) := by
  rw [runTrace_append]; rfl

theorem runVis_append (r : ProtocolSetup) (ms₁ ms₂ : List Move) :
    runVis r (ms₁ ++ ms₂) = runVis r ms₁ ++ (runMoves ms₂ (runTraceMoves r ms₁)).2 := by
  unfold runVis runTraceMoves
  change (runMoves ((r.setupMove :: ms₁) ++ ms₂) Trace.nil).2 = _
  rw [runMoves_append]

theorem runVis_snoc (r : ProtocolSetup) (ms : List Move) (m : Move) :
    runVis r (ms ++ [m]) = runVis r ms ++ m.vis (runTraceMoves r ms) := by
  rw [runVis_append]; simp [runMoves]

theorem runTrace_le_append (r : ProtocolSetup) (ms₁ ms₂ : List Move) :
    runTraceMoves r ms₁ ≤ runTraceMoves r (ms₁ ++ ms₂) := by
  rw [runTrace_append]; exact mp_runMoves_le ms₂ _

theorem attackerKnows_append {r : ProtocolSetup} {ms : List Move} (ms' : List Move) {t : DY.Bytes}
    (hk : t.AttackerKnows (runTraceMoves r ms)) : t.AttackerKnows (runTraceMoves r (ms ++ ms')) :=
  Bytes.AttackerKnows_le _ _ _ (runTrace_le_append r ms ms') hk

private theorem mp_getMessageSentAt_attackerKnows {tr : ExecTrace} {i : Nat} {t : DY.Bytes}
    (h : tr.getMessageSentAt i = some t) : t.AttackerKnows tr :=
  Trace.MessageSentAt_implies_AttackerKnows tr t i ((Trace.MessageSentAt_eq_getMessageSentAt t i tr).mpr h)

private theorem mp_movesAnchored_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    MovesAnchored (ms₁ ++ ms₂) tr ↔ MovesAnchored ms₁ tr ∧ MovesAnchored ms₂ (runMoves ms₁ tr).1
  | [], _, _ => by simp [MovesAnchored, runMoves]
  | m :: ms₁, ms₂, tr => by
    have hfst : (runMoves (m :: ms₁) tr).1 = (runMoves ms₁ (m.next tr)).1 := rfl
    simp only [List.cons_append, MovesAnchored, hfst, mp_movesAnchored_append ms₁ ms₂ (m.next tr), and_assoc]

private theorem mp_compromisesCurrentFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    compromisesCurrentFrom tr (ms₁ ++ ms₂) =
      (compromisesCurrentFrom tr ms₁ && compromisesCurrentFrom (runMoves ms₁ tr).1 ms₂)
  | [], _, _ => by simp [compromisesCurrentFrom, runMoves]
  | m :: ms₁, ms₂, tr => by
    have hfst : (runMoves (m :: ms₁) tr).1 = (runMoves ms₁ (m.next tr)).1 := rfl
    simp only [List.cons_append, compromisesCurrentFrom, hfst,
      mp_compromisesCurrentFrom_append ms₁ ms₂ (m.next tr), Bool.and_assoc]

private theorem mp_ownSaltsFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    ownSaltsFrom tr (ms₁ ++ ms₂) =
      (ownSaltsFrom tr ms₁ && ownSaltsFrom (runMoves ms₁ tr).1 ms₂)
  | [], _, _ => by simp [ownSaltsFrom, runMoves]
  | m :: ms₁, ms₂, tr => by
    have hfst : (runMoves (m :: ms₁) tr).1 = (runMoves ms₁ (m.next tr)).1 := rfl
    simp only [List.cons_append, ownSaltsFrom, hfst,
      mp_ownSaltsFrom_append ms₁ ms₂ (m.next tr), Bool.and_assoc]

private theorem mp_peerFaithful_prefix {r : ProtocolSetup} {ms₁ ms₂ : List Move}
    (h : PeerFaithful r (ms₁ ++ ms₂)) : PeerFaithful r ms₁ :=
  (List.forall_mem_append.mp h).1

private theorem mp_peerFaithful_snoc {r : ProtocolSetup} {ms : List Move} {m : Move}
    (h : PeerFaithful r ms) (hm : m.MatchesSetupPeer r) : PeerFaithful r (ms ++ [m]) :=
  List.forall_mem_append.mpr ⟨h, fun _ hx => by rcases List.mem_singleton.mp hx with rfl; exact hm⟩

private theorem mp_stateFaithful_prefix {r : ProtocolSetup} {ms₁ ms₂ : List Move}
    (h : StateFaithful r (ms₁ ++ ms₂)) : StateFaithful r ms₁ := by
  intro i j mi mj p k b hij hi hj hli hok hlj
  have hj_lt : j < ms₁.length := (List.getElem?_eq_some_iff.mp hj).1
  have hi_lt : i < ms₁.length := Nat.lt_trans hij hj_lt
  have htake : (ms₁ ++ ms₂).take i = ms₁.take i := List.take_append_of_le_length (Nat.le_of_lt hi_lt)
  exact h i j mi mj p k b hij ((List.getElem?_append_left hi_lt).trans hi)
    ((List.getElem?_append_left hj_lt).trans hj) hli (htake.symm ▸ hok) hlj

private theorem mp_stateFaithful_snoc {r : ProtocolSetup} {ms : List Move} {m : Move}
    (h : StateFaithful r ms)
    (hfresh : ∀ (i : Nat) (mi : Move) (p : Participant) (k : Nat) (b : Bool),
      ms[i]? = some mi → mi.stateLoad? = some (p, k, true) →
      (mi.act.run (runTraceMoves r (ms.take i))).1.isSome = true →
      m.stateLoad? = some (p, k, b) → False) :
    StateFaithful r (ms ++ [m]) := by
  intro i j mi mj p k b hij hi hj hli hok hlj
  by_cases hj1 : j < ms.length
  · have hi1 : i < ms.length := Nat.lt_trans hij hj1
    rw [List.getElem?_append_left hi1] at hi
    rw [List.getElem?_append_left hj1] at hj
    rw [List.take_append_of_le_length (Nat.le_of_lt hi1)] at hok
    exact h i j mi mj p k b hij hi hj hli hok hlj
  · have hj_ge : ms.length ≤ j := Nat.le_of_not_lt hj1
    rw [List.getElem?_append_right hj_ge] at hj
    have hj0 : j - ms.length = 0 := by
      have hlt1 : j - ms.length < 1 := (List.getElem?_eq_some_iff.mp hj).1
      omega
    rw [hj0, List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    have hi1 : i < ms.length := by omega
    rw [List.getElem?_append_left hi1] at hi
    rw [List.take_append_of_le_length (Nat.le_of_lt hi1)] at hok
    exact hfresh i mi p k b hi hli hok hlj

private theorem mp_runTrace_take_reach_snoc {r : ProtocolSetup} {ms : List Move} {m : Move}
    (hall : ∀ k, (runTraceMoves r (ms.take k)).Reachable reachability)
    (hlast : (runTraceMoves r (ms ++ [m])).Reachable reachability) :
    ∀ k, (runTraceMoves r ((ms ++ [m]).take k)).Reachable reachability := by
  intro k; rw [List.take_append]
  by_cases hk : k ≤ ms.length
  · rw [Nat.sub_eq_zero_of_le hk, List.take_zero, List.append_nil]; exact hall k
  · rw [List.take_of_length_le (by omega)]
    rcases heq : k - ms.length with _ | _
    · omega
    · simpa using hlast

private theorem mp_runTrace_take_reach_prefix {r : ProtocolSetup} {ms₀ δ : List Move}
    (hall : ∀ k, (runTraceMoves r ((ms₀ ++ δ).take k)).Reachable reachability) :
    ∀ k, (runTraceMoves r (ms₀.take k)).Reachable reachability := by
  intro k
  by_cases hk : k ≤ ms₀.length
  · have h := hall k; rwa [List.take_append_of_le_length hk] at h
  · rw [List.take_of_length_le (by omega)]
    have h := hall ms₀.length
    rwa [List.take_append_of_le_length (Nat.le_refl _), List.take_length] at h

private theorem mp_modelRun_prefix {r : ProtocolSetup} {ms₀ δ : List Move}
    (h : ModelRun r (ms₀ ++ δ)) : ModelRun r ms₀ := by
  obtain ⟨hsetup, hnosetup, ⟨_, hanc, hreach_all⟩, hcomp, hown, hpeer, hstate⟩ := h
  have hr₀ : (runTraceMoves r ms₀).Reachable reachability := by
    have hk := hreach_all ms₀.length
    rwa [List.take_append_of_le_length (Nat.le_refl _), List.take_length] at hk
  rw [mp_compromisesCurrentFrom_append, Bool.and_eq_true] at hcomp
  rw [mp_ownSaltsFrom_append, Bool.and_eq_true] at hown
  exact ⟨hsetup, fun m hm => hnosetup m (List.mem_append_left _ hm),
    ⟨hr₀, ((mp_movesAnchored_append ms₀ δ (setupTrace r)).mp hanc).1,
      mp_runTrace_take_reach_prefix hreach_all⟩,
    hcomp.1, hown.1, mp_peerFaithful_prefix hpeer, mp_stateFaithful_prefix hstate⟩

/-- Pointwise single-move well-formedness side conditions on `tr` for `modelRun_snoc`. -/
def MoveOK (r : ProtocolSetup) (m : Move) (tr : ExecTrace) : Prop :=
  m.isSetup = false ∧ m.LogsSessionCompletion tr ∧ m.MatchesSetupPeer r ∧
  (match m with
   | .exposeKey _ s _ | .exposeSpqr _ s => TripleRatchet.isCurrentSnapshot tr s = true
   | _ => True) ∧
  (match m with
   | .encrypt _ _ _ pqIdx _ => pqIdx = tr.length + 2
   | _ => True)

theorem modelRun_snoc {r : ProtocolSetup} {ms : List Move} {m : Move}
    (hrun : ModelRun r ms) (hm : MoveOK r m (runTraceMoves r ms))
    (hreach : (runTraceMoves r (ms ++ [m])).Reachable reachability)
    (hstate : ∀ (i : Nat) (mi : Move) (p : Participant) (k : Nat) (b : Bool),
      ms[i]? = some mi → mi.stateLoad? = some (p, k, true) →
      (mi.act.run (runTraceMoves r (ms.take i))).1.isSome = true →
      m.stateLoad? = some (p, k, b) → False) :
    ModelRun r (ms ++ [m]) := by
  obtain ⟨hsetup, hnosetup, ⟨_, hanc, hreach_all⟩, hcomp, hown, hpeer, hst⟩ := hrun
  obtain ⟨hms, hmanc, hmpeer, hmcomp, hmown⟩ := hm
  refine ⟨hsetup,
    fun x hx => (List.mem_append.mp hx).elim (hnosetup x)
      (fun h1 => by rcases List.mem_singleton.mp h1 with rfl; exact hms),
    ⟨hreach, (mp_movesAnchored_append _ _ _).mpr ⟨hanc, hmanc, trivial⟩,
      mp_runTrace_take_reach_snoc hreach_all hreach⟩,
    ?_, ?_, mp_peerFaithful_snoc hpeer hmpeer, mp_stateFaithful_snoc hst hstate⟩
  · rw [mp_compromisesCurrentFrom_append, Bool.and_eq_true]; refine ⟨hcomp, ?_⟩
    cases m <;> simp_all [compromisesCurrentFrom, setupTrace, setupMove_next_nil', runTraceMoves, runMoves]
  · rw [mp_ownSaltsFrom_append, Bool.and_eq_true]; refine ⟨hown, ?_⟩
    cases m <;> simp_all [ownSaltsFrom, setupTrace, setupMove_next_nil', runTraceMoves, runMoves]

@[scoped simp] theorem reject_next (draws : List Nat) (tr : ExecTrace) :
    (Move.reject draws).next tr = tr := by
  unfold Move.next Move.act; rw [Traceful.run_pure]

@[scoped simp] theorem attackerSend_next (msg : DY.Bytes) (tr : ExecTrace) :
    (Move.attackerSend msg).next tr = tr.append ({ msg := msg } : Network.ExecEntryT) := by
  unfold Move.next Move.act; dsimp only
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]

theorem modelRun_snoc_reject {r : ProtocolSetup} {ms : List Move} (draws : List Nat)
    (hrun : ModelRun r ms) : ModelRun r (ms ++ [.reject draws]) :=
  modelRun_snoc hrun ⟨rfl, trivial, trivial, trivial, trivial⟩
    (by rw [runTrace_snoc, reject_next]; exact hrun.2.2.1.1)
    (fun _ _ _ _ _ _ _ _ hm => nomatch hm)

/-! ## Faithfulness Predicates -/

@[scoped simp] theorem callCount_nil : callCount [] = 0 := rfl
@[scoped simp] theorem callStarts_nil : callStarts [] = [] := rfl

theorem callCount_append (vs₁ vs₂ : List VisEntry) :
    callCount (vs₁ ++ vs₂) = callCount vs₁ + callCount vs₂ := by
  unfold callCount; rw [List.filter_append, List.length_append]

theorem callStarts_append (τ₁ τ₂ : List MachineEvent) :
    callStarts (τ₁ ++ τ₂) = callStarts τ₁ ++ callStarts τ₂ := by
  unfold callStarts; rw [List.filter_append]

theorem callStarts_length_append (τ₁ τ₂ : List MachineEvent) :
    (callStarts (τ₁ ++ τ₂)).length = (callStarts τ₁).length + (callStarts τ₂).length := by
  rw [callStarts_append, List.length_append]

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

/-! ### `RoleFaithful` -/

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
    (h : RoleFaithful r who ms) (hm : m.party? = none) : RoleFaithful r who (ms ++ [m]) := by
  refine roleFaithful_append h fun j _ _ hj hp => ?_
  rcases j with _ | j
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; rw [hm] at hp; cases hp
  · simp at hj

theorem roleFaithful_snoc_party {r : ProtocolSetup} {who : List Participant} {ms : List Move} {m : Move}
    {p : Participant} (h : RoleFaithful r who ms) (hm : m.party? = some p)
    (hwho : who[callCount (runVis r ms)]? = some p) : RoleFaithful r who (ms ++ [m]) := by
  refine roleFaithful_append h fun j _ _ hj hq => ?_
  rcases j with _ | j
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj; rw [hm, Option.some.injEq] at hq; subst hq; simpa using hwho
  · simp at hj

/-! ### `PathFaithful` -/

theorem pathFaithful_prefix {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms₁ ms₂ : List Move} {acc₁ acc₂ : List MachineEvent}
    (h : PathFaithful interpretation r S g (ms₁ ++ ms₂) (acc₁ ++ acc₂)) :
    PathFaithful interpretation r S g ms₁ acc₁ := by
  intro i m promote b p hi hpath hcall hparse
  have hlt_i : i < ms₁.length := (List.getElem?_eq_some_iff.mp hi).1
  have hlt_k : callCount (runVis r (ms₁.take i)) < (callStarts acc₁).length :=
    (List.getElem?_eq_some_iff.mp hcall).1
  have htake : (ms₁ ++ ms₂).take i = ms₁.take i := List.take_append_of_le_length (Nat.le_of_lt hlt_i)
  have hcall' : (callStarts (acc₁ ++ acc₂))[callCount (runVis r ((ms₁ ++ ms₂).take i))]? =
      some (.recv b) := by
    rw [htake, callStarts_append, List.getElem?_append_left hlt_k]; exact hcall
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
    · rw [heq, List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; rw [hm] at hpath; cases hpath
    · rw [heq] at hi; simp at hi

/-! ### `ReadFaithful` -/

private theorem mp_mem_snd_of_mem_zip :
    ∀ {α β : Type} {xs : List α} {ys : List β} {p : α × β}, p ∈ xs.zip ys → p.2 ∈ ys
  | _, _, [], _, _, h => nomatch h
  | _, _, _ :: _, [], _, h => nomatch h
  | _, _, _ :: _, _ :: _, _, h =>
    (List.mem_cons.mp h).elim (fun heq => heq ▸ List.mem_cons_self)
      (fun h' => List.mem_cons_of_mem _ (mp_mem_snd_of_mem_zip h'))

/-- Pointwise `.recv` entry read-representation predicate parameterized by `(R, P)`. -/
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
    recvRepresentations interpretation r S g ms b ⊆
      recvRepresentations interpretation r S g (ms ++ ms') b :=
  fun _ ⟨hk, hrest⟩ => ⟨attackerKnows_append ms' hk, hrest⟩

theorem preKeyRepresentations_append_subset (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ms ms' : List Move) (b : HwBytes) :
    preKeyRepresentations interpretation r S g ms b ⊆
      preKeyRepresentations interpretation r S g (ms ++ ms') b :=
  fun _ ⟨h1, h2, h3, hrest⟩ =>
    ⟨attackerKnows_append ms' h1, attackerKnows_append ms' h2, attackerKnows_append ms' h3, hrest⟩

theorem readFaithful_append {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms ms' : List Move} {acc blk : List MachineEvent}
    (hlen : acc.length = (runVis r ms).length) (h : ReadFaithful interpretation r S g ms acc)
    (hblk : ∀ ev ∈ blk.zip (runMoves ms' (runTraceMoves r ms)).2, ev.2.kind = .recv →
      ReadOKWith (recvRepresentations interpretation r S g (ms ++ ms'))
        (preKeyRepresentations interpretation r S g (ms ++ ms')) ev.1 ev.2) :
    ReadFaithful interpretation r S g (ms ++ ms') (acc ++ blk) := by
  intro ev hev hk; rw [runVis_append, List.zip_append hlen] at hev
  exact (List.mem_append.mp hev).elim
    (fun h1 => ReadOKWith.mono (recvRepresentations_append_subset interpretation r S g ms ms')
      (preKeyRepresentations_append_subset interpretation r S g ms ms') (h ev h1 hk))
    (fun h2 => hblk ev h2 hk)

private def MpVisKnown (tr : ExecTrace) (v : VisEntry) : Prop :=
  (v.kind = .send ∨ v.kind = .recv ∨ v.kind = .leak) → ∀ t ∈ v.terms, t.AttackerKnows tr

private theorem mp_visKnown_mono {tr₁ tr₂ : ExecTrace} {v : VisEntry} (hle : tr₁ ≤ tr₂)
    (h : MpVisKnown tr₁ v) : MpVisKnown tr₂ v :=
  fun hk t ht => Bytes.AttackerKnows_le _ _ _ hle (h hk t ht)

private theorem mp_visKnown_of_kind {tr : ExecTrace} {v : VisEntry}
    (h : v.kind = .rng ∨ v.kind = .pt ∨ v.kind = .accept) : MpVisKnown tr v := by
  intro hk; rcases h with h | h | h <;> rw [h] at hk <;> simp at hk

private theorem mp_received_known {tr tr' : ExecTrace} (hle : tr ≤ tr') {hs : List Nat}
    {t : DY.Bytes} (ht : t ∈ received tr hs) : t.AttackerKnows tr' :=
  let ⟨_, _, hi⟩ := List.mem_filterMap.mp ht
  Bytes.AttackerKnows_le _ _ _ hle (mp_getMessageSentAt_attackerKnows hi)

private theorem mp_exposures_known {tr tr' : ExecTrace} {v : VisEntry}
    (hv : v ∈ exposures tr tr') : MpVisKnown tr' v := by
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨_, _, hj⟩ := List.mem_filterMap.mp hv; unfold pqExposureAt at hj; intro _ t ht
    split at hj <;> (try cases hj) <;>
      exact mp_getMessageSentAt_attackerKnows (Option.mem_toList.mp ht)
  · obtain ⟨_, _, hj⟩ := List.mem_filterMap.mp hv; unfold trExposureAt at hj; intro _ t ht
    split at hj <;> (try cases hj) <;>
      exact mp_getMessageSentAt_attackerKnows (Option.mem_toList.mp ht)

private theorem mp_aliceDraws_kind (done : Option Nat) :
    ∀ (L : List DY.Bytes) {v : VisEntry}, v ∈ aliceDraws done L → v.kind = .rng
  | [], _, hv => by simp [aliceDraws] at hv
  | [_], _, hv => by simp [aliceDraws, rngEntry] at hv; subst hv; rfl
  | _ :: _ :: _, _, hv => by
    simp only [aliceDraws, List.cons_append, List.mem_cons, List.mem_append] at hv
    rcases hv with rfl | hv | hv
    · rfl
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv; rfl
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv; rfl

private theorem mp_encVis_known {tr tr' : ExecTrace} (hle : tr ≤ tr') {wrap : Option (Nat × Nat)}
    {withSend : Bool} {v : VisEntry} (hv : v ∈ encVis tr tr' wrap withSend) : MpVisKnown tr' v := by
  unfold encVis at hv
  rcases List.mem_append.mp hv with hv | hv
  · cases hL : newRandoms tr tr' with
    | nil => rw [hL] at hv; simp [encDraws] at hv
    | cons _ _ =>
      rw [hL] at hv; simp only [encDraws, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact mp_visKnown_of_kind (Or.inr (Or.inl rfl))
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv; exact mp_visKnown_of_kind (Or.inl rfl)
  · cases withSend with
    | false => simp at hv
    | true =>
      simp only [↓reduceIte] at hv; unfold encSend at hv
      split at hv
      · rename_i w hw
        have hw_kn : w.AttackerKnows tr' := by
          unfold lastSent at hw; split at hw; exact mp_getMessageSentAt_attackerKnows hw; cases hw
        split at hv <;> rcases List.mem_singleton.mp hv with rfl <;> intro _ t ht
        · rcases List.mem_singleton.mp ht with rfl; exact hw_kn
        · exact (List.mem_append.mp ht).elim (mp_received_known hle)
            (fun h1 => by rcases List.mem_singleton.mp h1 with rfl; exact hw_kn)
      · cases hv

private theorem mp_decVis_known {tr tr' : ExecTrace} (hle : tr ≤ tr') {stateIdx msgIdx : Nat}
    {wrapped : Bool} {v : VisEntry} (hv : v ∈ decVis tr tr' stateIdx msgIdx wrapped) :
    MpVisKnown tr' v := by
  unfold decVis at hv
  rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_append.mp hv with hv | hv
    · rcases hm : tr.getMessageSentAt msgIdx with _ | _
      · rw [hm] at hv; cases hv
      · rw [hm] at hv; rcases List.mem_singleton.mp hv with rfl; intro _ t ht
        rcases List.mem_singleton.mp ht with rfl
        exact Bytes.AttackerKnows_le _ _ _ hle (mp_getMessageSentAt_attackerKnows hm)
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv; exact mp_visKnown_of_kind (Or.inl rfl)
  · rcases hp : receivedPlaintext tr tr' with _ | _
    · rw [hp] at hv; cases hv
    · rw [hp] at hv; rcases List.mem_singleton.mp hv with rfl
      exact mp_visKnown_of_kind (Or.inr (Or.inr rfl))

private theorem mp_move_known (m : Move) {tr : ExecTrace} (hs : OpkNetOK tr) {v : VisEntry}
    (hv : v ∈ m.vis tr) : MpVisKnown (m.next tr) v := by
  have hle := mp_move_le_next m tr; unfold Move.vis at hv
  rcases List.mem_append.mp hv with hv | hv
  · cases m <;> try exact absurd hv List.not_mem_nil
    case aliceStart =>
      have hv' := List.mem_of_mem_take hv; unfold aliceVis at hv'
      exact (List.mem_cons.mp hv').elim (fun heq => heq ▸ fun _ _ ht => mp_received_known hle ht)
        (fun hv' => mp_visKnown_of_kind (Or.inl (mp_aliceDraws_kind _ _ hv')))
    case bobStart =>
      have hv' := List.mem_of_mem_take hv; unfold bobVis at hv'
      rcases List.mem_cons.mp hv' with rfl | hv'
      · intro _ t ht
        exact (List.mem_append.mp ht).elim (mp_received_known hle)
          (fun ht => Bytes.AttackerKnows_le _ _ _ hle (bobOpkPk_known hs ht))
      · rcases List.mem_append.mp hv' with hv' | hv'
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv'; exact mp_visKnown_of_kind (Or.inl rfl)
        · rcases hp : receivedPlaintext tr _ with _ | _
          · rw [hp] at hv'; cases hv'
          · rw [hp] at hv'; rcases List.mem_singleton.mp hv' with rfl
            exact mp_visKnown_of_kind (Or.inr (Or.inr rfl))
    case encrypt => exact mp_encVis_known hle hv
    case encryptAbort => exact mp_encVis_known hle hv
    case encryptFail => exact mp_encVis_known hle hv
    case decrypt => exact mp_decVis_known hle hv
    case decryptSkipped => exact mp_decVis_known hle hv
    case reject =>
      rcases List.mem_cons.mp hv with rfl | hv
      · exact fun _ _ ht => nomatch ht
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv; exact mp_visKnown_of_kind (Or.inl rfl)
  · exact mp_exposures_known hv

private theorem mp_runMoves_known :
    ∀ (L : List Move) {tr : ExecTrace}, OpkNetOK tr →
      ∀ v ∈ (runMoves L tr).2, MpVisKnown (runMoves L tr).1 v
  | [], _, _, _, hv => nomatch hv
  | m :: L, tr, hs, v, hv => by
    have hsnd : (runMoves (m :: L) tr).2 = m.vis tr ++ (runMoves L (m.next tr)).2 := rfl
    have hfst : (runMoves (m :: L) tr).1 = (runMoves L (m.next tr)).1 := rfl
    rw [hsnd] at hv; rw [hfst]
    exact (List.mem_append.mp hv).elim
      (fun h1 => mp_visKnown_mono (mp_runMoves_le L (m.next tr)) (mp_move_known m hs h1))
      (fun h2 => mp_runMoves_known L (hs.next m) v h2)

private theorem mp_runVis_known (r : ProtocolSetup) (ms : List Move) {v : VisEntry}
    (hv : v ∈ runVis r ms) : MpVisKnown (runTraceMoves r ms) v :=
  mp_runMoves_known (r.setupMove :: ms) opkNetOK_nil v hv

theorem readOKWith_of_termsKnown {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms₁ ms₂ : List Move} {e : MachineEvent} {v : VisEntry}
    (hknown : ∀ t ∈ v.terms, t.AttackerKnows (runTraceMoves r ms₁))
    (hok : ReadOKWith (recvRepresentations interpretation r S g (ms₁ ++ ms₂))
      (preKeyRepresentations interpretation r S g (ms₁ ++ ms₂)) e v) :
    ReadOKWith (recvRepresentations interpretation r S g ms₁)
      (preKeyRepresentations interpretation r S g ms₁) e v := by
  revert hok hknown; unfold ReadOKWith
  generalize v.layout = l; generalize v.terms = ts; generalize eventBytes e = b
  intro hknown hok; cases l <;> try trivial
  case whisper =>
    rcases ts with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> try trivial
    rcases b with _ | ⟨_, _⟩; · trivial
    · exact ⟨hknown t List.mem_cons_self, hok.2⟩
  case preKeyInner =>
    rcases ts with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> try trivial
    exact fun p hp => ⟨hknown t List.mem_cons_self, (hok p hp).2⟩
  case preKeyRecv =>
    rcases ts with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg, _⟩⟩⟩ <;> try trivial
    exact ⟨hknown ek List.mem_cons_self,
      hknown ct (List.mem_cons_of_mem _ List.mem_cons_self),
      hknown msg (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      hok.2.2.2⟩

/-- Restricts `ReadFaithful` from `(ms₁ ++ ms₂, acc₁ ++ acc₂)` to `(ms₁, acc₁)`. -/
theorem readFaithful_prefix {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms₁ ms₂ : List Move} {acc₁ acc₂ : List MachineEvent}
    (hlen : acc₁.length = (runVis r ms₁).length)
    (h : ReadFaithful interpretation r S g (ms₁ ++ ms₂) (acc₁ ++ acc₂)) :
    ReadFaithful interpretation r S g ms₁ acc₁ := by
  intro ev hev hk
  have hev' : ev ∈ (acc₁ ++ acc₂).zip (runVis r (ms₁ ++ ms₂)) := by
    rw [runVis_append, List.zip_append hlen]; exact List.mem_append_left _ hev
  exact readOKWith_of_termsKnown
    (mp_runVis_known r ms₁ (mp_mem_snd_of_mem_zip hev) (Or.inr (Or.inl hk)))
    (h ev hev' hk)

/-! ### `OutcomeFaithful` and `ReadCollision` -/

theorem outcomeFaithful_prefix {r : ProtocolSetup} {ok : Nat → Bool} {ms₁ ms₂ : List Move}
    (h : OutcomeFaithful r ok (ms₁ ++ ms₂)) : OutcomeFaithful r ok ms₁ := by
  intro i m hi
  have hlt : i < ms₁.length := (List.getElem?_eq_some_iff.mp hi).1
  simpa [List.take_append_of_le_length (Nat.le_of_lt hlt)] using
    h i m ((List.getElem?_append_left hlt).trans hi)

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
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
    simp only [List.take_zero, List.append_nil]
    exact ⟨fun ds hrej => absurd hrej (hnotRej ds), fun hs => by rw [hnoDone] at hs; cases hs⟩
  · simp at hj

theorem outcomeFaithful_snoc_reject {r : ProtocolSetup} {ok : Nat → Bool} {ms : List Move}
    (draws : List Nat) (h : OutcomeFaithful r ok ms)
    (hok : ok (callCount (runVis r ms)) = false) :
    OutcomeFaithful r ok (ms ++ [.reject draws]) := by
  refine outcomeFaithful_append h fun j _ hj => ?_
  rcases j with _ | j
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
    simp only [List.take_zero, List.append_nil, reject_next]
    exact ⟨fun _ _ => hok, fun hs => by simp [eventIdx, newIndices] at hs⟩
  · simp at hj

private theorem mp_head?_append_of_some {α : Type} {l₁ l₂ : List α} {x : α}
    (h : l₁.head? = some x) : (l₁ ++ l₂).head? = some x := by
  cases l₁ with
  | nil => simp at h
  | cons _ _ => simpa using h

theorem readCollision_append {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {τ : List MachineEvent} (ms' : List Move) (τ' : List MachineEvent)
    (h : ReadCollision interpretation r S g ms τ) :
    ReadCollision interpretation r S g (ms ++ ms') (τ ++ τ') := by
  obtain ⟨i, τ₁, e, τ₂, m, rfl, hmi, hF₁, ⟨pt, hpt⟩, hcol⟩ := h
  have hlt : i < ms.length := (List.getElem?_eq_some_iff.mp hmi).1
  have htake : (ms ++ ms').take i = ms.take i := List.take_append_of_le_length (Nat.le_of_lt hlt)
  refine ⟨i, τ₁, e, τ₂ ++ τ', m, by simp [List.append_assoc],
    (List.getElem?_append_left hlt).trans hmi, htake ▸ hF₁, ⟨pt, ?_⟩, htake ▸ hcol⟩
  rw [List.filter_append]; exact mp_head?_append_of_some hpt

theorem not_readCollision_prefix {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms ms' : List Move} {τ τ' : List MachineEvent}
    (h : ¬ ReadCollision interpretation r S g (ms ++ ms') (τ ++ τ')) :
    ¬ ReadCollision interpretation r S g ms τ :=
  fun hrc => h (readCollision_append ms' τ' hrc)

private theorem mp_append_split_of_mem_not_mem {α : Type} :
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
    obtain ⟨τ₂₀, hacc', hτ₂⟩ := mp_append_split_of_mem_not_mem h.2 hx hnb
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
    obtain ⟨τ₂₀, hacc_eq, hτ₂_eq⟩ :=
      mp_append_split_of_mem_not_mem hsplit hmem_τ₂ (fun hb => hnoAcc _ hb pt rfl)
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

/-- Collision-free trace explanation: `ExplainsMoves` together with `¬ ReadCollision`. -/
def Clean (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost) (ms : List Move)
    (τ₁ : List MachineEvent) : Prop :=
  ExplainsMoves interpretation r S who ok g ms τ₁ ∧ ¬ ReadCollision interpretation r S g ms τ₁

theorem matchedPrefix_length_eq {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (h : MatchedPrefix interpretation r S who g ms τ) : τ.length = (runVis r ms).length :=
  h.2.2.2.2.2.length_eq

theorem matchedPrefix_callCount_eq {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (h : MatchedPrefix interpretation r S who g ms τ) :
    callCount (runVis r ms) = (callStarts τ).length :=
  callCount_eq_callStarts_length h.2.2.2.2.2

private theorem mp_forall₂_append_split {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m₁ m₂ : List β}, l₁.length = m₁.length →
      List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) → List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂
  | [], _, [], _, _, h => ⟨.nil, h⟩
  | [], _, _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, _, [], _, hlen, _ => by simp at hlen
  | _ :: _, _, _ :: _, _, hlen, .cons hab h =>
    have ⟨h1, h2⟩ := mp_forall₂_append_split (by simpa using hlen) h
    ⟨.cons hab h1, h2⟩

private theorem mp_forall₂_append_join {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m₁ m₂ : List β},
      List.Forall₂ R l₁ m₁ → List.Forall₂ R l₂ m₂ → List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂)
  | _, _, _, _, .nil, h₂ => h₂
  | _, _, _, _, .cons hab h₁, h₂ => .cons hab (mp_forall₂_append_join h₁ h₂)

/-- Restricts `MatchedPrefix` on `(ms₁ ++ ms₂, τ₁ ++ τ₂)` to `(ms₁, τ₁)` and yields the suffix
`Forall₂` alignment. -/
theorem matchedPrefix_prefix {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₁ ms₂ : List Move}
    {τ₁ τ₂ : List MachineEvent} (hlen : τ₁.length = (runVis r ms₁).length)
    (h : MatchedPrefix interpretation r S who g (ms₁ ++ ms₂) (τ₁ ++ τ₂)) :
    MatchedPrefix interpretation r S who g ms₁ τ₁ ∧
      List.Forall₂ (EventMatchesEntry interpretation r S g) τ₂ (runMoves ms₂ (runTraceMoves r ms₁)).2 := by
  obtain ⟨hcompat, hrun, hrole, hpath, hread, hF⟩ := h
  rw [runVis_append] at hF
  obtain ⟨hF₁, hF₂⟩ := mp_forall₂_append_split hlen hF
  exact ⟨⟨hcompat, mp_modelRun_prefix hrun, roleFaithful_prefix hrole,
    pathFaithful_prefix hpath, readFaithful_prefix hlen hread, hF₁⟩, hF₂⟩

theorem explains_prefix {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms₁ ms₂ : List Move}
    {τ₁ τ₂ : List MachineEvent} (hlen : τ₁.length = (runVis r ms₁).length)
    (h : ExplainsMoves interpretation r S who ok g (ms₁ ++ ms₂) (τ₁ ++ τ₂)) :
    ExplainsMoves interpretation r S who ok g ms₁ τ₁ :=
  ⟨(matchedPrefix_prefix hlen h.1).1, outcomeFaithful_prefix h.2⟩

theorem clean_prefix {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms₁ ms₂ : List Move}
    {τ₁ τ₂ : List MachineEvent} (hlen : τ₁.length = (runVis r ms₁).length)
    (h : Clean interpretation r S who ok g (ms₁ ++ ms₂) (τ₁ ++ τ₂)) :
    Clean interpretation r S who ok g ms₁ τ₁ :=
  ⟨explains_prefix hlen h.1, not_readCollision_prefix h.2⟩

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
  refine ⟨hmp.1, hrun, hrole, hpath,
    readFaithful_append (matchedPrefix_length_eq hmp) hmp.2.2.2.2.1 hread_blk, ?_⟩
  rw [runVis_append]; exact mp_forall₂_append_join hmp.2.2.2.2.2 hF_blk

theorem matchedPrefix_snoc_hidden {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {m : Move} {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r S who g ms τ) (hmok : MoveOK r m (runTraceMoves r ms))
    (hreach : (runTraceMoves r (ms ++ [m])).Reachable reachability) (hvis : m.vis (runTraceMoves r ms) = [])
    (hparty : m.party? = none) (hpath : m.prekeyPath? = none) (hload : m.stateLoad? = none) :
    MatchedPrefix interpretation r S who g (ms ++ [m]) τ := by
  have hrun' := modelRun_snoc hmp.2.1 hmok hreach
    (fun _ _ _ _ _ _ _ _ hl => by rw [hload] at hl; cases hl)
  simpa using matchedPrefix_append (blk := []) hmp hrun' (roleFaithful_snoc_none hmp.2.2.1 hparty)
    (by simpa using pathFaithful_snoc_none hmp.2.2.2.1 hpath) (by simp) (by simp [runMoves, hvis])

private theorem mp_append_at_length {Entry E1 : Type} [DY.TraceEntryHas E1 Entry]
    (tr : DY.Trace Entry) (e : E1) (h : tr.length < (tr.append e).length) :
    (tr.append e).at tr.length h = DY.TraceEntryHas.inj e := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

private theorem mp_attackerSend_newIndices (msg : DY.Bytes) (tr : ExecTrace) :
    newIndices tr ((Move.attackerSend msg).next tr) = [tr.length] := by
  have hlen : (tr.append ({ msg := msg } : Network.ExecEntryT)).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  simp [attackerSend_next, newIndices, hlen]

private theorem mp_attackerSend_at?_pq (msg : DY.Bytes) (tr : ExecTrace) :
    ((tr.append ({ msg := msg } : Network.ExecEntryT)).at? tr.length :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by
  have hlt : tr.length < (tr.append ({ msg := msg } : Network.ExecEntryT)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, ↓reduceDIte, mp_append_at_length]; rfl

private theorem mp_attackerSend_at?_tr (msg : DY.Bytes) (tr : ExecTrace) :
    ((tr.append ({ msg := msg } : Network.ExecEntryT)).at? tr.length :
      Option (ProtocolEvent.ExecEntryT TREvent)) = none := by
  have hlt : tr.length < (tr.append ({ msg := msg } : Network.ExecEntryT)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, ↓reduceDIte, mp_append_at_length]; rfl

private theorem mp_attackerSend_vis (msg : DY.Bytes) (tr : ExecTrace) :
    (Move.attackerSend msg).vis tr = [] := by
  unfold Move.vis; dsimp only [List.nil_append]; unfold exposures
  rw [mp_attackerSend_newIndices, attackerSend_next]
  simp [pqExposureAt, trExposureAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, mp_attackerSend_at?_pq, mp_attackerSend_at?_tr]

private theorem mp_attackerSend_eventIdx_none (p : PQXDHEvent → Bool) (msg : DY.Bytes) (tr : ExecTrace) :
    eventIdx p tr ((Move.attackerSend msg).next tr) = none := by
  unfold eventIdx; rw [mp_attackerSend_newIndices, attackerSend_next]
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, mp_attackerSend_at?_pq]

theorem matchedPrefix_attackerSend {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {msg : DY.Bytes} {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r S who g ms τ)
    (hreach : (runTraceMoves r (ms ++ [.attackerSend msg])).Reachable reachability) :
    MatchedPrefix interpretation r S who g (ms ++ [.attackerSend msg]) τ :=
  matchedPrefix_snoc_hidden hmp ⟨rfl, trivial, trivial, trivial, trivial⟩ hreach
    (mp_attackerSend_vis msg _) rfl rfl rfl

theorem explains_attackerSend {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {msg : DY.Bytes}
    {τ : List MachineEvent} (hex : ExplainsMoves interpretation r S who ok g ms τ)
    (hreach : (runTraceMoves r (ms ++ [.attackerSend msg])).Reachable reachability) :
    ExplainsMoves interpretation r S who ok g (ms ++ [.attackerSend msg]) τ :=
  ⟨matchedPrefix_attackerSend hex.1 hreach,
    outcomeFaithful_snoc_neutral hex.2 (fun _ h => nomatch h)
      (mp_attackerSend_eventIdx_none isAliceDone msg _)⟩

theorem clean_attackerSend {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {msg : DY.Bytes}
    {τ : List MachineEvent} (hcl : Clean interpretation r S who ok g ms τ)
    (hreach : (runTraceMoves r (ms ++ [.attackerSend msg])).Reachable reachability) :
    Clean interpretation r S who ok g (ms ++ [.attackerSend msg]) τ :=
  ⟨explains_attackerSend hcl.1 hreach, by
    simpa using not_readCollision_append_noAccept (ms' := [.attackerSend msg]) (blk := []) hcl.2
      (fun _ he => nomatch he) (fun m hm _ _ hc => by rcases List.mem_singleton.mp hm with rfl; exact hc)⟩

private theorem mp_forall₂_reject_rng (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) :
    ∀ (ds : List HwBytes), List.Forall₂ (EventMatchesEntry interpretation r S g) (ds.map .rng)
      ((ds.map List.length).map fun n => ⟨.rng, [], .fresh n, none⟩)
  | [] => .nil
  | _ :: tl => .cons ⟨rfl, rfl⟩ (mp_forall₂_reject_rng interpretation r S g tl)

theorem matchedPrefix_snoc_reject {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    (b : HwBytes) (ds : List HwBytes) (hmp : MatchedPrefix interpretation r S who g ms acc)
    (hpath : PathFaithful interpretation r S g ms (acc ++ (.recv b :: ds.map .rng))) :
    MatchedPrefix interpretation r S who g
      (ms ++ [.reject (ds.map List.length)]) (acc ++ (.recv b :: ds.map .rng)) := by
  have hF_blk : List.Forall₂ (EventMatchesEntry interpretation r S g) (.recv b :: ds.map .rng)
      (runMoves [.reject (ds.map List.length)] (runTraceMoves r ms)).2 := by
    simp only [runMoves, List.append_nil, Move.vis, reject_next, exposures, newIndices,
      Nat.sub_self, List.range'_zero, List.filterMap_nil]
    exact .cons ⟨rfl, trivial⟩ (mp_forall₂_reject_rng interpretation r S g ds)
  exact matchedPrefix_append hmp (modelRun_snoc_reject _ hmp.2.1)
    (roleFaithful_snoc_none hmp.2.2.1 rfl) (pathFaithful_snoc_none hpath rfl)
    (fun ev hev hk => by
      simp only [runMoves, List.append_nil] at hev
      have hv := mp_mem_snd_of_mem_zip hev
      simp only [Move.vis, reject_next, exposures, newIndices, Nat.sub_self, List.range'_zero,
        List.filterMap_nil, List.append_nil, List.mem_cons] at hv
      rcases hv with heq | hv
      · rw [heq]; trivial
      · obtain ⟨_, _, heq⟩ := List.mem_map.mp hv; rw [← heq] at hk; cases hk) hF_blk

theorem explains_snoc_reject {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    (b : HwBytes) (ds : List HwBytes) (hex : ExplainsMoves interpretation r S who ok g ms acc)
    (hpath : PathFaithful interpretation r S g ms (acc ++ (.recv b :: ds.map .rng)))
    (hok : ok (callStarts acc).length = false) :
    ExplainsMoves interpretation r S who ok g
      (ms ++ [.reject (ds.map List.length)]) (acc ++ (.recv b :: ds.map .rng)) :=
  ⟨matchedPrefix_snoc_reject b ds hex.1 hpath,
    outcomeFaithful_snoc_reject _ hex.2 (by rwa [matchedPrefix_callCount_eq hex.1])⟩

theorem clean_snoc_reject {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    (b : HwBytes) (ds : List HwBytes) (hcl : Clean interpretation r S who ok g ms acc)
    (hpath : PathFaithful interpretation r S g ms (acc ++ (.recv b :: ds.map .rng)))
    (hok : ok (callStarts acc).length = false) :
    Clean interpretation r S who ok g
      (ms ++ [.reject (ds.map List.length)]) (acc ++ (.recv b :: ds.map .rng)) := by
  refine ⟨explains_snoc_reject b ds hcl.1 hpath hok,
    not_readCollision_append_noAccept hcl.2 (fun e he _ heq => ?_)
      (fun m hm _ _ hc => by rcases List.mem_singleton.mp hm with rfl; exact hc)⟩
  rcases List.mem_cons.mp he with rfl | he
  · cases heq
  · obtain ⟨_, _, h'⟩ := List.mem_map.mp he; rw [← h'] at heq; cases heq

end DY.Libsignal.Composed.Refinement
