/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.MatchedPrefix
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Opk
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
import VCVio.Prelude.Core

/-!
# One-Time Pre-Key Relation over Prefix-Closed Explanation Classes

Defines `COpkRelOn r P used acc` asserting that no explanation in class `P` logs Bob's `OPKUsed`
event when `r.withOpk = true` and `used = false`, and proves transfer lemmas across call blocks
for prefix-closed classes (`XplPrefixClosed`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open DY
open DY.Libsignal
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace

/-- One-time pre-key relation over explanation class `P`: if `r.withOpk = true` and `used = false`,
no explanation `(g, ms)` of `acc` in `P` logs Bob's `OPKUsed` for `setupPublic r 8`. -/
def COpkRelOn (r : ProtocolSetup)
    (P : Ghost → List Move → List MachineEvent → Prop) (used : Bool)
    (acc : List MachineEvent) : Prop :=
  r.withOpk = true → used = false →
    ∀ g ms, P g ms acc →
      DY.Libsignal.PQXDH.opkUsedB (runTraceMoves r ms) r.bob (setupPublic r 8) = false

/-- An explanation class `P` that implies `MatchedPrefix` and restricts to split prefixes. -/
def XplPrefixClosed (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (P : Ghost → List Move → List MachineEvent → Prop) : Prop :=
  (∀ g ms τ, P g ms τ → MatchedPrefix interpretation r S who g ms τ) ∧
  (∀ g ms₀ δ acc blk, P g (ms₀ ++ δ) (acc ++ blk) →
    MatchedPrefix interpretation r S who g ms₀ acc → P g ms₀ acc)

section Basic
variable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
  {P Q : Ghost → List Move → List MachineEvent → Prop} {used used' : Bool}
  {acc blk : List MachineEvent}

/-- Base case at `[]`: any `MatchedPrefix`-implied class `P` satisfies `COpkRelOn r P used []`. -/
theorem cOpkRelOn_nil
    (hP : ∀ g ms, P g ms [] → MatchedPrefix interpretation r S who g ms []) :
    COpkRelOn r P used [] := by
  intro _ _ g ms hp
  have hmp := hP g ms hp
  obtain ⟨_, hrun, _, _, _, hF⟩ := hmp
  obtain ⟨_, hs, ⟨_, hanc, _⟩, _⟩ := hrun
  have hvis_nil : runVis r ms = [] := by
    cases h : runVis r ms with
    | nil => rfl
    | cons _ _ => rw [h] at hF; cases hF
  have hrm_nil : (runMoves ms (setupTrace r)).2 = [] := by
    have hsplit := runVis_append r [] ms
    rw [List.nil_append, hvis_nil] at hsplit
    exact (List.append_eq_nil_iff.mp hsplit.symm).2
  have hF_ms : List.Forall₂ (EventMatchesEntry interpretation r S g) []
      (runMoves ms (setupTrace r)).2 := by
    rw [hrm_nil]; exact .nil
  have htr : runTraceMoves r ms = (runMoves ms (setupTrace r)).1 := by
    simpa [runTrace_nil] using runTrace_append r [] ms
  rw [htr, opkUsedB_runMoves_eq_of_forall₂ r.bob (setupPublic r 8) ms (setupTrace r) []
    (xpl_movesFrom_of ms (setupTrace r) hs hanc) hF_ms (Or.inl fun _ he => nomatch he)]
  exact opkUsedB_setupTrace r r.bob (setupPublic r 8)

end Basic

section Transfer
variable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
  {P : Ghost → List Move → List MachineEvent → Prop} {used used' : Bool}
  {acc blk : List MachineEvent}

/-- If every split `(ms₀, δ)` of a `P`-explanation of `acc ++ blk` leaves `opkUsedB` unchanged
across `δ`, `COpkRelOn r P` transfers from `acc` to `acc ++ blk`. -/
theorem cOpkRelOn_transfer' (hP : XplPrefixClosed interpretation r S who P)
    (hopk : COpkRelOn r P used acc)
    (hused : used' = false → used = false)
    (hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt)
    (heq : ∀ g ms₀ δ, P g (ms₀ ++ δ) (acc ++ blk) →
      XplBlock interpretation r S who g ms₀ δ acc blk →
      DY.Libsignal.PQXDH.opkUsedB (runTraceMoves r (ms₀ ++ δ)) r.bob (setupPublic r 8) =
        DY.Libsignal.PQXDH.opkUsedB (runTraceMoves r ms₀) r.bob (setupPublic r 8)) :
    COpkRelOn r P used' (acc ++ blk) := by
  intro hw hu' g ms hp
  have hmp := hP.1 g ms _ hp
  obtain ⟨ms₀, δ, rfl, hpre, hmatch⟩ := matchedPrefix_split hmp hhead
  have hB : XplBlock interpretation r S who g ms₀ δ acc blk := ⟨hpre, hmp.2.1, hmatch⟩
  rw [heq g ms₀ δ hp hB]
  exact hopk hw (hused hu') g ms₀ (hP.2 g ms₀ δ acc blk hp hpre)

theorem cOpkRelOn_of_no_accept' (hP : XplPrefixClosed interpretation r S who P)
    (hopk : COpkRelOn r P used acc)
    (hused : used' = false → used = false)
    (hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt)
    (hnoacc : ∀ e ∈ blk, eventKind e ≠ .accept) :
    COpkRelOn r P used' (acc ++ blk) :=
  cOpkRelOn_transfer' hP hopk hused hhead fun _ _ _ _ hB =>
    opkUsedB_xplBlock_eq r.bob (setupPublic r 8) hB (Or.inl hnoacc)

theorem cOpkRelOn_of_no_accept (hP : XplPrefixClosed interpretation r S who P)
    (hopk : COpkRelOn r P used acc)
    (hused : used' = false → used = false)
    (hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt)
    (_hreach : ∀ g ms, MatchedPrefix interpretation r S who g ms (acc ++ blk) →
      ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable Composed.reachability)
    (hnoacc : ∀ e ∈ blk, eventKind e ≠ .accept) :
    COpkRelOn r P used' (acc ++ blk) :=
  cOpkRelOn_of_no_accept' hP hopk hused hhead hnoacc

theorem cOpkRelOn_of_no_opkNamed_recv' (hP : XplPrefixClosed interpretation r S who P)
    (hopk : COpkRelOn r P used acc)
    (hused : used' = false → used = false)
    (hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt)
    (hnoopk : ∀ b, MachineEvent.recv b ∈ blk → ¬ OpkNamed r b true) :
    COpkRelOn r P used' (acc ++ blk) :=
  cOpkRelOn_transfer' hP hopk hused hhead fun _ _ _ _ hB =>
    opkUsedB_xplBlock_eq r.bob (setupPublic r 8) hB (Or.inr hnoopk)

theorem cOpkRelOn_of_no_opkNamed_recv (hP : XplPrefixClosed interpretation r S who P)
    (hopk : COpkRelOn r P used acc)
    (hused : used' = false → used = false)
    (hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt)
    (_hreach : ∀ g ms, MatchedPrefix interpretation r S who g ms (acc ++ blk) →
      ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable Composed.reachability)
    (hnoopk : ∀ b, MachineEvent.recv b ∈ blk → ¬ OpkNamed r b true) :
    COpkRelOn r P used' (acc ++ blk) :=
  cOpkRelOn_of_no_opkNamed_recv' hP hopk hused hhead hnoopk

end Transfer

theorem not_opkNamed_of_bobStart_opk_none {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {b d pt : HwBytes}
    (hex : ¬ OpkNamed r b true ∨
      ∃ g₀ ms₀ b' a kh regIdxA mh pqIdx spqrMsgIdx n,
        kh.opk = none ∧
        List.Forall₂ (EventMatchesEntry interpretation r S g₀)
          [.recv b, .rng d, .accept pt]
          ((Move.bobStart b' a kh regIdxA mh pqIdx spqrMsgIdx (n + 1)).vis (runTraceMoves r ms₀))) :
    ¬ OpkNamed r b true := by
  rcases hex with hnot | ⟨g₀, ms₀, b', a, kh, regIdxA, mh, pqIdx, spqrMsgIdx, n, hnone, hm⟩
  · exact hnot
  · have hbob : bobOpkPk b' kh (runTraceMoves r ms₀) = none := by
      unfold bobOpkPk; rw [hnone]; rfl
    rw [xpl_vis_eq, exposures_nil_of_not_leakKind rfl (by rintro ⟨⟩), List.append_nil] at hm
    dsimp only [xpl_ownVis, bobVis] at hm
    rw [hbob, Option.toList_none, List.append_nil] at hm
    cases hm with
    | cons he₀ _ =>
      obtain ⟨_, hlay⟩ := he₀
      dsimp only [eventBytes] at hlay
      rcases hrec : received (runTraceMoves r ms₀) [mh.ek, mh.ct, mh.msg] with
        _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, rest⟩⟩⟩⟩⟩
      · rw [hrec] at hlay; exact False.elim hlay
      · rw [hrec] at hlay; exact False.elim hlay
      · rw [hrec] at hlay; exact False.elim hlay
      · rw [hrec] at hlay; exact not_opkNamed_true_of_opkNamed_false hlay.2
      · exfalso
        have hlen :=
          List.length_filterMap_le (runTraceMoves r ms₀).getMessageSentAt [mh.ek, mh.ct, mh.msg]
        change (received (runTraceMoves r ms₀) [mh.ek, mh.ct, mh.msg]).length ≤ 3 at hlen
        rw [hrec] at hlen
        contradiction
      · rw [hrec] at hlay; exact False.elim hlay

theorem cOpkRelOn_of_exists' {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {P : Ghost → List Move → List MachineEvent → Prop}
    {used used' : Bool} {acc : List MachineEvent} {b d pt : HwBytes}
    (hP : XplPrefixClosed interpretation r S who P)
    (hopk : COpkRelOn r P used acc)
    (hused : used' = false → used = false)
    (hex : ¬ OpkNamed r b true ∨
      ∃ g₀ ms₀ b' a kh regIdxA mh pqIdx spqrMsgIdx n,
        kh.opk = none ∧
        List.Forall₂ (EventMatchesEntry interpretation r S g₀)
          [.recv b, .rng d, .accept pt]
          ((Move.bobStart b' a kh regIdxA mh pqIdx spqrMsgIdx (n + 1)).vis (runTraceMoves r ms₀))) :
    COpkRelOn r P used' (acc ++ [.recv b, .rng d, .accept pt]) := by
  have hhead : ∀ e ∈ ([MachineEvent.recv b, .rng d, .accept pt] : List MachineEvent).head?,
      eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he; exact Or.inl rfl
  have hnot := not_opkNamed_of_bobStart_opk_none hex
  refine cOpkRelOn_of_no_opkNamed_recv' hP hopk hused hhead ?_
  intro b' hb'
  simp only [List.mem_cons, MachineEvent.recv.injEq, reduceCtorEq, List.not_mem_nil, or_false] at hb'
  subst hb'
  exact hnot

theorem cOpkRelOn_of_exists {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {P : Ghost → List Move → List MachineEvent → Prop}
    {used used' : Bool} {acc : List MachineEvent} {b d pt : HwBytes}
    (hP : XplPrefixClosed interpretation r S who P)
    (hopk : COpkRelOn r P used acc)
    (hused : used' = false → used = false)
    (_hreach : ∀ g ms,
      MatchedPrefix interpretation r S who g ms (acc ++ [.recv b, .rng d, .accept pt]) →
      ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable Composed.reachability)
    (hex : ¬ OpkNamed r b true ∨
      ∃ g₀ ms₀ b' a kh regIdxA mh pqIdx spqrMsgIdx n,
        kh.opk = none ∧
        List.Forall₂ (EventMatchesEntry interpretation r S g₀)
          [.recv b, .rng d, .accept pt]
          ((Move.bobStart b' a kh regIdxA mh pqIdx spqrMsgIdx (n + 1)).vis (runTraceMoves r ms₀))) :
    COpkRelOn r P used' (acc ++ [.recv b, .rng d, .accept pt]) :=
  cOpkRelOn_of_exists' hP hopk hused hex

end Symbolic.Swarm.CREF
