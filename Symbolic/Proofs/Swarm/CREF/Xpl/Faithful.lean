/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
public import Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas

/-!
# Faithful Trace Explanations and Call-Block Predicates

Defines participant attribution (`moveActor`, `visActorsFrom`, `DeltaFaithful`), session-effect
invariance (`NoSessionEffect`, `InvisibleNoEffect`), split call-block matching (`XplBlock`), move
classification predicates, and single-visible-move block decompositions (`OneMove`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.TripleRatchet (TREvent TRState)
open DY.Libsignal.PQXDH (PQXDHEvent)
open CryptoProofLib.Refinement (ExternInterpretation)

/-- The participant a move acts for, if any. -/
def moveActor : Move → Option Participant
  | .setup .. => none
  | .aliceStart a .. => some a
  | .bobStart b .. => some b
  | .encrypt me .. => some me
  | .encryptAbort me _ => some me
  | .encryptFail me .. => some me
  | .decrypt me .. => some me
  | .decryptSkipped me .. => some me
  | .reject _ => none
  | .compromiseIK p _ => some p
  | .compromiseSPK b _ => some b
  | .compromisePQSPK b _ => some b
  | .compromiseOPK b _ => some b
  | .exposeKey me .. => some me
  | .exposeSpqr me _ => some me
  | .exposeSkipped _ => none
  | .attackerSend _ => none
  | .brkDH => none
  | .brkKEM => none

/-- The actor associated with each visible entry of `runMoves ms tr`, in trace order. -/
def visActorsFrom : List Move → ExecTrace → List (Option Participant)
  | [], _ => []
  | m :: ms, tr => List.replicate (m.vis tr).length (moveActor m) ++ visActorsFrom ms (m.next tr)

theorem visActorsFrom_append :
    ∀ (ms δ : List Move) (tr : ExecTrace),
      visActorsFrom (ms ++ δ) tr = visActorsFrom ms tr ++ visActorsFrom δ (runMoves ms tr).1
  | [], _, _ => rfl
  | m :: ms, δ, tr => by
    simp only [List.cons_append, visActorsFrom, runMoves, visActorsFrom_append ms δ (m.next tr),
      List.append_assoc]

/-- Two optional actor tags agree when equal or when at least one is `none`. -/
def ActorAgrees (a l : Option Participant) : Prop := a = none ∨ l = none ∨ a = l

/-- `P` holds at every move of `δ` from the trace at which that move executes. -/
def MovesFrom (P : ExecTrace → Move → Prop) : ExecTrace → List Move → Prop
  | _, [] => True
  | tr, m :: δ => P tr m ∧ MovesFrom P (m.next tr) δ

theorem movesFrom_append (P : ExecTrace → Move → Prop) :
    ∀ (ms δ : List Move) (tr : ExecTrace),
      MovesFrom P tr (ms ++ δ) ↔ MovesFrom P tr ms ∧ MovesFrom P (runMoves ms tr).1 δ
  | [], _, _ => by simp [MovesFrom, runMoves]
  | m :: ms, δ, tr => by
    simp only [List.cons_append, MovesFrom, runMoves, movesFrom_append P ms δ (m.next tr),
      and_assoc]

theorem movesFrom_mono {P Q : ExecTrace → Move → Prop} (hPQ : ∀ tr m, P tr m → Q tr m) :
    ∀ (tr : ExecTrace) (δ : List Move), MovesFrom P tr δ → MovesFrom Q tr δ
  | _, [], _ => trivial
  | tr, m :: δ, ⟨h, hδ⟩ => ⟨hPQ tr m h, movesFrom_mono hPQ (m.next tr) δ hδ⟩

/-- Every new trace index produced by `m` from `tr` holds no stored `TRState`, no session-related
`PQXDHEvent` (`NonSessionPQAt`), no `TREvent`, and no `ComposedEvent`. -/
def NoSessionEffect (tr : ExecTrace) (m : Move) : Prop :=
  ∀ i ∈ newIndices tr (m.next tr),
    ((m.next tr).at? i : Option (PersistentGlobalState.State.ExecEntryT
        (PersistentLocalState.LocalState TRState))) = none ∧
      Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.NonSessionPQAt (m.next tr) i ∧
      ((m.next tr).at? i : Option (ProtocolEvent.ExecEntryT TREvent)) = none ∧
      ((m.next tr).at? i : Option (ProtocolEvent.ExecEntryT ComposedEvent)) = none

/-- `m` acts for `p` or has no actor. -/
def ActorIn (p : Participant) (m : Move) : Prop := moveActor m = none ∨ moveActor m = some p

/-- `m` emits no visible entries and satisfies `NoSessionEffect tr m`. -/
def InvisibleNoEffect (tr : ExecTrace) (m : Move) : Prop := m.vis tr = [] ∧ NoSessionEffect tr m

/-! ## Call-Block Hypotheses -/

/-- Split form of `MatchedPrefix` for a call block `blk` explained by moves `δ` after `(ms₀, acc)`. -/
structure XplBlock (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (g : Ghost) (ms₀ δ : List Move) (acc blk : List MachineEvent) : Prop where
  pre : MatchedPrefix interpretation r S who g ms₀ acc
  run : ModelRun r (ms₀ ++ δ)
  matched : List.Forall₂ (EventMatchesEntry interpretation r S g) blk (runMoves δ (runTraceMoves r ms₀)).2

/-- Every visible entry produced by `δ` from `tr` comes from a move acting for `p` or for nobody. -/
def DeltaFaithful (p : Participant) (tr : ExecTrace) (δ : List Move) : Prop :=
  ∀ a ∈ visActorsFrom δ tr, ActorAgrees a (some p)

theorem xpl_forall₂_append_split {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m₁ m₂ : List β}, l₁.length = m₁.length →
      List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) → List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂
  | [], _, [], _, _, h => ⟨.nil, h⟩
  | [], _, _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, _, [], _, hlen, _ => by simp at hlen
  | _ :: _, _, _ :: _, _, hlen, .cons hab h =>
    have ⟨h1, h2⟩ := xpl_forall₂_append_split (by simpa using hlen) h
    ⟨.cons hab h1, h2⟩

/-! ## Move Kinds and Inversion Conclusions -/

/-- Moves that can explain a whisper `recv_wire` call. -/
def RecvKind : Move → Prop
  | .decrypt .. | .decryptSkipped .. | .reject _ => True
  | _ => False

/-- Moves that can explain a `recv_prekey` call. -/
def RpkKind : Move → Prop
  | .bobStart .. | .decrypt .. | .decryptSkipped .. | .reject _ => True
  | _ => False

/-- Encrypt-family moves (`encrypt`, `encryptAbort`, `encryptFail`). -/
def SendKind : Move → Prop
  | .encrypt .. | .encryptAbort .. | .encryptFail .. => True
  | _ => False

/-- Moves that can explain a `session_initiate` call. -/
def IniKind : Move → Prop
  | .aliceStart .. | .reject _ | .attackerSend _ => True
  | _ => False

/-- Compromise and key-exposure moves. -/
def LeakKind : Move → Prop
  | .compromiseIK .. | .compromiseSPK .. | .compromisePQSPK .. | .compromiseOPK ..
  | .exposeKey .. | .exposeSpqr .. | .exposeSkipped _ => True
  | _ => False

/-- Decrypt or skipped-key decrypt move acting for `p`. -/
def DecryptBy (p : Participant) : Move → Prop
  | .decrypt me .. | .decryptSkipped me .. => me = p
  | _ => False

/-- `Move.bobStart` acting for `p`. -/
def BobStartBy (p : Participant) : Move → Prop
  | .bobStart b .. => b = p
  | _ => False

/-- Decomposition of `δ` into one move `m` satisfying `Q` surrounded by `InvisibleNoEffect` moves. -/
def OneMove (Q : ExecTrace → Move → Prop) (tr : ExecTrace) (δ : List Move) : Prop :=
  ∃ pre m post, δ = pre ++ m :: post ∧
    MovesFrom InvisibleNoEffect tr pre ∧ Q (runMoves pre tr).1 m ∧
    MovesFrom InvisibleNoEffect (m.next (runMoves pre tr).1) post

end Symbolic.Swarm.CREF
