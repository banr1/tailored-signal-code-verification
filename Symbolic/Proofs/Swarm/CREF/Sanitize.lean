/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Set.Operations
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.ReadFaithful
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.Steps

/-!
# Move Sanitization and Faithfulness Preservation

Defines `clearStuckWrap` and `sanitizeMoves`, which clear `wrapped = true` on `decrypt` and
`decryptSkipped` moves whose message index is out of range, and proves that sanitization preserves
`runTraceMoves`, `runVis`, `ModelRun`, `RoleFaithful`, `ReadFaithful`, `OutcomeFaithful`, and
`ReadCollision`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)

namespace Sanitize

/-- Clears `wrapped = true` on a `decrypt` or `decryptSkipped` move whose message index `mi` is out
of range on `tr`, leaving `Move.next` and `Move.vis` unchanged so stuck wrapped moves do not report
`prekeyPath? = some true`. -/
def clearStuckWrap (tr : ExecTrace) : Move → Move
  | .decrypt me si mi pq sp w =>
    .decrypt me si mi pq sp (w && (tr.getMessageSentAt mi).isSome)
  | .decryptSkipped me si mi k pq sp w =>
    .decryptSkipped me si mi k pq sp (w && (tr.getMessageSentAt mi).isSome)
  | m => m

@[simp] theorem clearStuckWrap_next (tr t : ExecTrace) (m : Move) :
    (clearStuckWrap tr m).next t = m.next t := by
  cases m <;> rfl

@[simp] theorem clearStuckWrap_vis (tr : ExecTrace) (m : Move) :
    (clearStuckWrap tr m).vis tr = m.vis tr := by
  cases m <;> try rfl
  case decrypt me si mi pq sp w =>
    rcases hm : tr.getMessageSentAt mi with _ | b
    · simp only [clearStuckWrap, hm, Option.isSome_none, Bool.and_false, Move.vis, decVis]; rfl
    · simp [clearStuckWrap, hm]
  case decryptSkipped me si mi k pq sp w =>
    rcases hm : tr.getMessageSentAt mi with _ | b
    · simp only [clearStuckWrap, hm, Option.isSome_none, Bool.and_false, Move.vis, decVis]; rfl
    · simp [clearStuckWrap, hm]

@[simp] theorem clearStuckWrap_party? (tr : ExecTrace) (m : Move) :
    (clearStuckWrap tr m).party? = m.party? := by
  cases m <;> rfl

@[simp] theorem clearStuckWrap_isSetup (tr : ExecTrace) (m : Move) :
    (clearStuckWrap tr m).isSetup = m.isSetup := by
  cases m <;> rfl

@[simp] theorem clearStuckWrap_peerOk (r : ProtocolSetup) (tr : ExecTrace) (m : Move) :
    (clearStuckWrap tr m).MatchesSetupPeer r ↔ m.MatchesSetupPeer r := by
  cases m <;> exact Iff.rfl

@[simp] theorem clearStuckWrap_anchored (tr t : ExecTrace) (m : Move) :
    (clearStuckWrap tr m).LogsSessionCompletion t ↔ m.LogsSessionCompletion t := by
  cases m <;> exact Iff.rfl

@[simp] theorem clearStuckWrap_eq_reject (tr : ExecTrace) (m : Move) (ds : List Nat) :
    (clearStuckWrap tr m = .reject ds) ↔ (m = .reject ds) := by
  cases m <;> simp [clearStuckWrap]

theorem callCount_pos_of_clearStuckWrap_prekeyPath? {m : Move} {tr : ExecTrace}
    {promote : Bool} (ha : m.LogsSessionCompletion tr)
    (hp : (clearStuckWrap tr m).prekeyPath? = some promote) :
    0 < callCount (m.vis tr) := by
  rw [xpl_vis_eq]
  unfold callCount
  rw [List.filter_append, List.length_append]
  cases m <;> simp only [clearStuckWrap, Move.prekeyPath?] at hp
  case bobStart b a kh i mh pq sp shown =>
    obtain ⟨hsh, -⟩ := ha
    obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, by omega⟩
    simp [xpl_ownVis, bobVis]; omega
  case decrypt me si mi pq sp w =>
    rcases hm : tr.getMessageSentAt mi with _ | b
    · simp [hm] at hp
    · simp [xpl_ownVis, decVis, hm]; omega
  case decryptSkipped me si mi k pq sp w =>
    rcases hm : tr.getMessageSentAt mi with _ | b
    · simp [hm] at hp
    · simp [xpl_ownVis, decVis, hm]; omega
  all_goals cases hp

/-- Sanitize a move sequence from initial trace `tr` by applying `clearStuckWrap` at each step's
running trace. -/
def sanitizeMoves : ExecTrace → List Move → List Move
  | _, [] => []
  | tr, m :: ms => clearStuckWrap tr m :: sanitizeMoves (m.next tr) ms

@[simp] theorem sanitizeMoves_take (tr : ExecTrace) (ms : List Move) (i : Nat) :
    (sanitizeMoves tr ms).take i = sanitizeMoves tr (ms.take i) := by
  induction ms generalizing tr i with
  | nil => simp [sanitizeMoves]
  | cons m ms ih =>
    cases i with
    | zero => rfl
    | succ i => simp [sanitizeMoves, ih]

@[simp] theorem runMoves_sanitizeMoves (tr : ExecTrace) (ms : List Move) :
    runMoves (sanitizeMoves tr ms) tr = runMoves ms tr := by
  induction ms generalizing tr with
  | nil => rfl
  | cons m ms ih => simp [sanitizeMoves, runMoves, ih]

@[simp] theorem runTrace_sanitizeMoves (r : ProtocolSetup) (ms : List Move) :
    runTraceMoves r (sanitizeMoves (setupTrace r) ms) = runTraceMoves r ms := by
  simp [xpl_runTrace_eq]

@[simp] theorem runVis_sanitizeMoves (r : ProtocolSetup) (ms : List Move) :
    runVis r (sanitizeMoves (setupTrace r) ms) = runVis r ms := by
  simp [runVis, runMoves, setupMove_next_nil]

theorem getElem?_sanitizeMoves (tr : ExecTrace) (ms : List Move) (i : Nat) :
    (sanitizeMoves tr ms)[i]? =
      (ms[i]?).map (clearStuckWrap (runMoves (ms.take i) tr).1) := by
  induction ms generalizing tr i with
  | nil => rfl
  | cons m ms ih =>
    cases i with
    | zero => rfl
    | succ i => simp [sanitizeMoves, runMoves, ih]

@[simp] theorem clearStuckWrap_stateLoad? (tr : ExecTrace) (m : Move) :
    (clearStuckWrap tr m).stateLoad? = m.stateLoad? := by
  cases m <;> rfl

@[simp] theorem clearStuckWrap_act (tr : ExecTrace) (m : Move) :
    (clearStuckWrap tr m).act = m.act := by
  cases m <;> rfl

@[simp] theorem movesAnchored_sanitizeMoves (tr : ExecTrace) (ms : List Move) :
    MovesAnchored (sanitizeMoves tr ms) tr ↔ MovesAnchored ms tr := by
  induction ms generalizing tr with
  | nil => exact Iff.rfl
  | cons m ms ih => simp [sanitizeMoves, MovesAnchored, ih]

@[simp] theorem compromisesCurrentFrom_sanitizeMoves (tr : ExecTrace) (ms : List Move) :
    compromisesCurrentFrom tr (sanitizeMoves tr ms) = compromisesCurrentFrom tr ms := by
  induction ms generalizing tr with
  | nil => rfl
  | cons m ms ih =>
    cases m <;> simp only [sanitizeMoves, clearStuckWrap, compromisesCurrentFrom] <;>
      exact congrArg _ (ih _)

@[simp] theorem ownSaltsFrom_sanitizeMoves (tr : ExecTrace) (ms : List Move) :
    ownSaltsFrom tr (sanitizeMoves tr ms) = ownSaltsFrom tr ms := by
  induction ms generalizing tr with
  | nil => rfl
  | cons m ms ih =>
    cases m <;> simp only [sanitizeMoves, clearStuckWrap, ownSaltsFrom] <;>
      exact congrArg _ (ih _)

@[simp] theorem honestKeysFrom_sanitizeMoves (tr : ExecTrace) (ms : List Move) :
    honestKeysFrom tr (sanitizeMoves tr ms) = honestKeysFrom tr ms := by
  induction ms generalizing tr with
  | nil => rfl
  | cons m ms ih =>
    cases m <;> simp only [sanitizeMoves, clearStuckWrap, honestKeysFrom] <;>
      exact congrArg _ (ih _)

@[simp] theorem honestSalts_sanitizeMoves (r : ProtocolSetup) (ms : List Move) :
    honestSalts r (sanitizeMoves (setupTrace r) ms) = honestSalts r ms := by
  simp [honestSalts]

theorem mem_sanitizeMoves {tr : ExecTrace} {ms : List Move} {m' : Move}
    (hm' : m' ∈ sanitizeMoves tr ms) :
    ∃ t m, m ∈ ms ∧ m' = clearStuckWrap t m := by
  induction ms generalizing tr with
  | nil => cases hm'
  | cons m ms ih =>
    rcases List.mem_cons.mp hm' with rfl | hrest
    · exact ⟨tr, m, List.mem_cons_self, rfl⟩
    · obtain ⟨t, m₀, hm₀, rfl⟩ := ih hrest
      exact ⟨t, m₀, List.mem_cons_of_mem _ hm₀, rfl⟩

theorem modelRun_sanitizeMoves {r : ProtocolSetup} {ms : List Move} (h : ModelRun r ms) :
    ModelRun r (sanitizeMoves (setupTrace r) ms) := by
  obtain ⟨hsetup, hns, ⟨hreach, hanc, hall⟩, hcomp, hown, hpeer, hstate⟩ := h
  refine ⟨hsetup, ?_, ⟨by simpa using hreach, (movesAnchored_sanitizeMoves _ _).mpr hanc,
      fun k => by simpa using hall k⟩,
    by simpa using hcomp, by simpa using hown, ?_, ?_⟩
  · intro m' hm'
    obtain ⟨t, m, hm, rfl⟩ := mem_sanitizeMoves hm'
    simp [hns m hm]
  · intro m' hm'
    obtain ⟨t, m, hm, rfl⟩ := mem_sanitizeMoves hm'
    exact (clearStuckWrap_peerOk r t m).mpr (hpeer m hm)
  · intro i j mi' mj' p k b hij hi hj hli hok hlj
    rw [getElem?_sanitizeMoves] at hi hj
    rcases hmi : ms[i]? with _ | mi
    · simp [hmi] at hi
    · rcases hmj : ms[j]? with _ | mj
      · simp [hmj] at hj
      · simp only [hmi, hmj, Option.map_some, Option.some.injEq] at hi hj
        subst hi; subst hj
        simp only [clearStuckWrap_stateLoad?] at hli hlj
        rw [clearStuckWrap_act, sanitizeMoves_take, runTrace_sanitizeMoves] at hok
        exact hstate i j mi mj p k b hij hmi hmj hli hok hlj

theorem roleFaithful_sanitizeMoves {r : ProtocolSetup} {who : List Participant} {ms : List Move}
    (h : RoleFaithful r who ms) :
    RoleFaithful r who (sanitizeMoves (setupTrace r) ms) := by
  intro i m' p hi hp
  rw [getElem?_sanitizeMoves] at hi
  rcases hmi : ms[i]? with _ | m
  · simp [hmi] at hi
  · simp only [hmi, Option.map_some, Option.some.injEq] at hi
    subst hi
    simp only [clearStuckWrap_party?, sanitizeMoves_take, runVis_sanitizeMoves] at hp ⊢
    exact h i m p hmi hp

theorem outcomeFaithful_sanitizeMoves {r : ProtocolSetup} {ok : Nat → Bool} {ms : List Move}
    (h : OutcomeFaithful r ok ms) :
    OutcomeFaithful r ok (sanitizeMoves (setupTrace r) ms) := by
  intro i m' hi
  rw [getElem?_sanitizeMoves] at hi
  rcases hmi : ms[i]? with _ | m
  · simp [hmi] at hi
  · simp only [hmi, Option.map_some, Option.some.injEq] at hi
    subst hi
    simp only [sanitizeMoves_take, runVis_sanitizeMoves, runTrace_sanitizeMoves,
      clearStuckWrap_next, clearStuckWrap_eq_reject]
    exact h i m hmi

@[simp] theorem readColMove_clearStuckWrap {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {pre : List Move} {e : MachineEvent}
    (tr : ExecTrace) (m : Move) :
    MoveReadsCollidingMsg interpretation r S g pre e (clearStuckWrap tr m) ↔
      MoveReadsCollidingMsg interpretation r S g pre e m := by
  cases m <;> exact Iff.rfl

@[simp] theorem recvCollision_sanitizeMoves_iff {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {t : DY.Bytes} :
    RecvCollision interpretation r S g (sanitizeMoves (setupTrace r) ms) t ↔
      RecvCollision interpretation r S g ms t := by
  unfold RecvCollision
  simp only [runTrace_sanitizeMoves, runVis_sanitizeMoves, honestSalts_sanitizeMoves]

@[simp] theorem readColMove_sanitizeMoves_iff {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {pre : List Move} {e : MachineEvent} {m : Move} :
    MoveReadsCollidingMsg interpretation r S g (sanitizeMoves (setupTrace r) pre) e m ↔
      MoveReadsCollidingMsg interpretation r S g pre e m := by
  cases m <;> simp [MoveReadsCollidingMsg]

@[simp] theorem readCollision_sanitizeMoves_iff {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {τ : List MachineEvent} :
    ReadCollision interpretation r S g (sanitizeMoves (setupTrace r) ms) τ ↔
      ReadCollision interpretation r S g ms τ := by
  constructor
  · rintro ⟨i, τ₁, e, τ₂, m', rfl, hmi, hF₁, hacc, hcol⟩
    rw [getElem?_sanitizeMoves] at hmi
    rcases hm : ms[i]? with _ | m
    · simp [hm] at hmi
    · simp only [hm, Option.map_some, Option.some.injEq] at hmi
      subst hmi
      simp only [sanitizeMoves_take, runVis_sanitizeMoves, readColMove_clearStuckWrap,
        readColMove_sanitizeMoves_iff] at hF₁ hcol
      exact ⟨i, τ₁, e, τ₂, m, rfl, hm, hF₁, hacc, hcol⟩
  · rintro ⟨i, τ₁, e, τ₂, m, rfl, hm, hF₁, hacc, hcol⟩
    refine ⟨i, τ₁, e, τ₂, clearStuckWrap (runMoves (ms.take i) (setupTrace r)).1 m, rfl, ?_, ?_,
      hacc, ?_⟩
    · rw [getElem?_sanitizeMoves, hm]; rfl
    · simpa [sanitizeMoves_take, runVis_sanitizeMoves] using hF₁
    · simpa [sanitizeMoves_take, readColMove_clearStuckWrap, readColMove_sanitizeMoves_iff]
        using hcol

theorem callCount_of_forall₂ {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {τ : List MachineEvent} {vis : List VisEntry}
    (h : List.Forall₂ (EventMatchesEntry interpretation r S g) τ vis) :
    callCount vis = (callStarts τ).length := by
  induction h with
  | nil => rfl
  | @cons hw ev τ vis hrel _ ih =>
    have hk : ev.kind = eventKind hw := hrel.1.symm
    unfold callCount callStarts at ih ⊢
    simp only [List.filter_cons, hk]
    split <;> simp [ih]

theorem callCount_take_lt_of_sanitizeMoves_prekeyPath?
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms : List Move} {acc : List MachineEvent} {i : Nat} {m' : Move} {promote : Bool}
    (hm : MatchedPrefix interpretation r S who g ms acc)
    (hi : (sanitizeMoves (setupTrace r) ms)[i]? = some m')
    (hp : m'.prekeyPath? = some promote) :
    callCount (runVis r ((sanitizeMoves (setupTrace r) ms).take i)) <
      (callStarts acc).length := by
  simp only [sanitizeMoves_take, runVis_sanitizeMoves]
  rw [getElem?_sanitizeMoves] at hi
  rcases hmi : ms[i]? with _ | m
  · simp [hmi] at hi
  · simp only [hmi, Option.map_some, Option.some.injEq] at hi
    subst hi
    rw [← callCount_of_forall₂ hm.2.2.2.2.2]
    have hlt : i < ms.length := (List.getElem?_eq_some_iff.mp hmi).1
    have hdrop : ms.drop i = m :: ms.drop (i + 1) := by
      rw [← List.cons_getElem_drop_succ (h := hlt)]
      rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hmi
      rw [hmi]
    have hms : ms = ms.take i ++ (m :: ms.drop (i + 1)) := by
      rw [← hdrop, List.take_append_drop]
    have hanc := hm.2.1.2.2.1.2.1
    rw [hms] at hanc
    have hanc_m : m.LogsSessionCompletion (runTraceMoves r (ms.take i)) := by
      rw [xpl_runTrace_eq]
      exact (xpl_movesAnchored_append_right (ms.take i) (m :: ms.drop (i + 1)) (setupTrace r) hanc).1
    have htr_eq : (runMoves (ms.take i) (setupTrace r)).1 = runTraceMoves r (ms.take i) := by
      rw [xpl_runTrace_eq]
    rw [htr_eq] at hp
    have hpos := callCount_pos_of_clearStuckWrap_prekeyPath? hanc_m hp
    have hvis : runVis r ms = runVis r (ms.take i) ++
        (m.vis (runTraceMoves r (ms.take i)) ++
          (runMoves (ms.drop (i + 1)) (m.next (runTraceMoves r (ms.take i)))).2) := by
      conv_lhs => rw [hms]
      rw [runVis_append, runMoves_cons_snd]
    rw [hvis]
    unfold callCount at hpos ⊢
    simp only [List.filter_append, List.length_append]
    omega

@[simp] theorem recvRepresentations_sanitizeMoves (interpretation : ExternInterpretation)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move) :
    recvRepresentations interpretation r S g (sanitizeMoves (setupTrace r) ms) =
      recvRepresentations interpretation r S g ms := by
  ext b t
  simp [recvRepresentations, runTrace_sanitizeMoves]

@[simp] theorem preKeyRepresentations_sanitizeMoves (interpretation : ExternInterpretation)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move) :
    preKeyRepresentations interpretation r S g (sanitizeMoves (setupTrace r) ms) =
      preKeyRepresentations interpretation r S g ms := by
  ext b x
  simp [preKeyRepresentations, runTrace_sanitizeMoves]

@[simp] theorem readFaithful_sanitizeMoves_iff {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {acc : List MachineEvent} :
    ReadFaithful interpretation r S g (sanitizeMoves (setupTrace r) ms) acc ↔
      ReadFaithful interpretation r S g ms acc := by
  simp [readFaithful_iff]

theorem readFaithful_sanitizeMoves {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    (hrf : ReadFaithful interpretation r S g ms acc) :
    ReadFaithful interpretation r S g (sanitizeMoves (setupTrace r) ms) acc :=
  readFaithful_sanitizeMoves_iff.mpr hrf

end Sanitize

export Sanitize (readFaithful_sanitizeMoves)

end Symbolic.Swarm.CREF
