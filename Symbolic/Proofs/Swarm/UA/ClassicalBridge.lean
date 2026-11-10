/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredClassical

/-!
# Equivalence of Classical and Unified-Attacker Predicates on Break-Free Traces

Proves that on CLI event lists containing no break or invert event (`BreakFree`), `CliTraces`,
`Explains`, and `CollisionAfterExplainedPrefix` coincide with their classical counterparts.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.ClassicalBridge

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession (Inputs Outcome)

/-! ## Break-Free Event Lists -/

/-- No environment event in `evs` is a break or invert event. -/
def BreakFree (evs : List CliEvent) : Prop :=
  ∀ e : EnvEvent, CliEvent.env e ∈ evs → ¬ e.IsBreakInvert

theorem breakFree_nil : BreakFree [] := fun _ he => by cases he

theorem breakFree_of_cons {x : CliEvent} {evs : List CliEvent} (h : BreakFree (x :: evs)) :
    BreakFree evs :=
  fun e he => h e (List.mem_cons_of_mem x he)

theorem breakFree_append {a b : List CliEvent} :
    BreakFree (a ++ b) ↔ BreakFree a ∧ BreakFree b := by
  constructor
  · intro h
    exact ⟨fun e he => h e (List.mem_append_left b he), fun e he => h e (List.mem_append_right a he)⟩
  · rintro ⟨ha, hb⟩ e he
    rcases List.mem_append.mp he with he | he
    · exact ha e he
    · exact hb e he

theorem breakFree_run_cons {ev : RunEvent} {evs : List CliEvent} :
    BreakFree (.run ev :: evs) ↔ BreakFree evs := by
  constructor
  · exact breakFree_of_cons
  · intro h e he
    rcases List.mem_cons.mp he with he | he
    · cases he
    · exact h e he

theorem breakFree_of_leaksFrom {r : ProtocolSetup} {t : CliTurn} {leaks : List CliEvent}
    (h : LeaksFrom r t leaks) : BreakFree leaks := by
  intro e he hbi
  obtain ⟨p, k, _, heq⟩ := h _ he
  cases heq
  exact hbi

/-! ## Traces and Explanations -/

theorem cliTracesClassical_of_breakFree {Rel : Inputs → Option Outcome → Prop}
    {interp : ExternInterpretation} {r : ProtocolSetup} {t : CliTurn} {evs : List CliEvent}
    (htr : CliTraces Rel interp r t evs) (hbf : BreakFree evs) :
    CliTracesClassical Rel interp r t evs := by
  induction htr with
  | done t => exact .done t
  | clear p _ ih => exact .clear p (ih hbf)
  | breakInvert hbi _ _ => exact absurd hbi (hbf _ (List.mem_cons_self ..))
  | step hleak hnext hin hRel _ ih =>
    refine .step hleak hnext hin hRel (ih fun e he => hbf e ?_)
    exact List.mem_append_right _ (List.mem_cons_of_mem _ he)
  | stop hleak hnext hin hRel habort => exact .stop hleak hnext hin hRel habort

theorem envMatches_of_classical {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {s : Step} {ev : EnvEvent} {vis : List VisEntry}
    (h : EnvMatchesClassical interp r S g tr s ev vis) : EnvMatches interp r S g tr s ev vis := by
  cases ev with
  | leak p k => exact h
  | breakDH | breakKEM | invertDH _ _ | invertKEM _ _ | registerCorrupt _ _ => exact h.elim

theorem envMatchesClassical_of {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {s : Step} {ev : EnvEvent} {vis : List VisEntry}
    (h : EnvMatches interp r S g tr s ev vis) (hbi : ¬ ev.IsBreakInvert) :
    EnvMatchesClassical interp r S g tr s ev vis := by
  cases ev with
  | leak p k => exact h
  | breakDH | breakKEM | invertDH _ _ | invertKEM _ _ => exact (hbi trivial).elim
  | registerCorrupt _ _ => exact h.elim

theorem matchesEventsAt_of_classical {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEventsClassicalAt interp r S g initIds tr ss evs vis) :
    MatchesEventsAt interp r S g initIds tr ss evs vis := by
  induction h with
  | nil hinv => exact .nil hinv
  | run1 hpre hrm _ ih => exact .run1 hpre hrm ih
  | run0 hpre hrej _ ih => exact .run0 hpre hrej ih
  | env hpre hem _ ih => exact .env hpre (envMatches_of_classical hem) ih

theorem matchesEvents_of_classical {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEventsClassical interp r S g tr ss evs vis) :
    MatchesEvents interp r S g tr ss evs vis :=
  matchesEventsAt_of_classical h

theorem matchesEventsClassicalAt_of {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEventsAt interp r S g initIds tr ss evs vis) (hbf : BreakFree evs) :
    MatchesEventsClassicalAt interp r S g initIds tr ss evs vis := by
  revert hbf
  induction h with
  | nil hinv => exact fun _ => .nil hinv
  | run1 hpre hrm _ ih => exact fun hbf => .run1 hpre hrm (ih (breakFree_of_cons hbf))
  | run0 hpre hrej _ ih => exact fun hbf => .run0 hpre hrej (ih (breakFree_of_cons hbf))
  | env hpre hem _ ih =>
    exact fun hbf => .env hpre (envMatchesClassical_of hem (hbf _ (List.mem_cons_self ..)))
      (ih (breakFree_of_cons hbf))

theorem matchesEventsClassical_of {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEvents interp r S g tr ss evs vis) (hbf : BreakFree evs) :
    MatchesEventsClassical interp r S g tr ss evs vis :=
  matchesEventsClassicalAt_of h hbf

theorem explains_of_classical {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs : List CliEvent}
    (h : ExplainsClassical interp r S g ss vis evs) : Explains interp r S g ss vis evs :=
  ⟨h.1, h.2.1, h.2.2.1, matchesEvents_of_classical h.2.2.2⟩

theorem explainsClassical_of {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs : List CliEvent}
    (h : Explains interp r S g ss vis evs) (hbf : BreakFree evs) :
    ExplainsClassical interp r S g ss vis evs :=
  ⟨h.1, h.2.1, h.2.2.1, matchesEventsClassical_of h.2.2.2 hbf⟩

/-! ## Collisions -/

theorem readCollisionCli_of_classical {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {evs : List CliEvent}
    (h : ReadCollisionCliClassical interp r S g ss evs) : ReadCollisionCli interp r S g ss evs := by
  obtain ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t, h1, h2, h3, h4, h5, hme, h7⟩ := h
  exact ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t, h1, h2, h3, h4, h5,
    matchesEvents_of_classical hme, h7⟩

theorem readCollisionCliClassical_of {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {evs : List CliEvent}
    (h : ReadCollisionCli interp r S g ss evs) (hbf : BreakFree evs) :
    ReadCollisionCliClassical interp r S g ss evs := by
  obtain ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t, h1, h2, h3, h4, h5, hme, h7⟩ := h
  subst h1
  exact ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t, rfl, h2, h3, h4, h5,
    matchesEventsClassical_of hme (breakFree_append.mp hbf).1, h7⟩

theorem acceptsViaCli_iff {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {evs₁ : List CliEvent} {ev : RunEvent} (hbf : BreakFree evs₁) (t : DY.Bytes) :
    ModelAcceptsTermAfterAttackerSends interp r S g ss evs₁ ev t ↔ ModelAcceptsTermAfterAttackerSendsClassical interp r S g ss evs₁ ev t := by
  have hbf' : BreakFree (evs₁ ++ [.run ev]) :=
    breakFree_append.mpr ⟨hbf, breakFree_run_cons.mpr breakFree_nil⟩
  constructor
  · rintro ⟨ext, m, msgIdx, g₁, vis₁, h1, h2, h3, h4, h5, hex⟩
    exact ⟨ext, m, msgIdx, g₁, vis₁, h1, h2, h3, h4, h5, explainsClassical_of hex hbf'⟩
  · rintro ⟨ext, m, msgIdx, g₁, vis₁, h1, h2, h3, h4, h5, hex⟩
    exact ⟨ext, m, msgIdx, g₁, vis₁, h1, h2, h3, h4, h5, explains_of_classical hex⟩

theorem acceptsViaCli_eq {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {evs₁ : List CliEvent} {ev : RunEvent} (hbf : BreakFree evs₁) :
    ModelAcceptsTermAfterAttackerSends interp r S g ss evs₁ ev = ModelAcceptsTermAfterAttackerSendsClassical interp r S g ss evs₁ ev :=
  funext fun t => propext (acceptsViaCli_iff hbf t)

theorem whisperExcusedCli_of_classical {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {evs₁ : List CliEvent} {ev : RunEvent} {b : HwBytes}
    (hbf : BreakFree evs₁) (h : SignalMsgAcceptedOnlyViaCollisionClassical interp r S g ss evs₁ ev b) :
    SignalMsgAcceptedOnlyViaCollision interp r S g ss evs₁ ev b := by
  obtain ⟨hrep, hall⟩ := h
  refine ⟨hrep, fun g' ss' vis' hex hnrc => ?_⟩
  have := hall g' ss' vis' (explainsClassical_of hex hbf)
    (fun hrc => hnrc (readCollisionCli_of_classical hrc))
  dsimp only [RepresentationsCollideOrAcceptedCollide,
    RepresentationsCollideOrAcceptedCollideClassical] at this ⊢
  rw [acceptsViaCli_eq hbf]
  exact this

theorem preKeyExcusedCli_of_classical {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {evs₁ : List CliEvent} {b : HwBytes} {p : PreKeyFields}
    (hbf : BreakFree evs₁) (h : PreKeyStartCollidesOrRejectsClassical interp r S g ss evs₁ b p) :
    PreKeyStartCollidesOrRejects interp r S g ss evs₁ b p := by
  obtain ⟨hrep, hk | hall⟩ := h
  · exact ⟨hrep, Or.inl hk⟩
  · exact ⟨hrep, Or.inr fun g' ss' vis' hex hnrc => hall g' ss' vis' (explainsClassical_of hex hbf)
      (fun hrc => hnrc (readCollisionCli_of_classical hrc))⟩

theorem prefixGhostsCli_sub {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {evs₁ : List CliEvent} (hbf : BreakFree evs₁) {g' : Ghost}
    (h : g' ∈ PrefixExplainingGhosts interp r S g ss evs₁) :
    g' ∈ PrefixExplainingGhostsClassical interp r S g ss evs₁ := by
  obtain ⟨hσ, vis', hex⟩ := h
  exact ⟨hσ, vis', explainsClassical_of hex hbf⟩

/-- Transfers `CollisionAfterExplainedPrefixClassical` to `CollisionAfterExplainedPrefix` on a
`BreakFree` event list. -/
theorem collisionAtCli_of_classical {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {evs : List CliEvent} (hbf : BreakFree evs) (h : CollisionAfterExplainedPrefixClassical interp r S evs) :
    CollisionAfterExplainedPrefix interp r S evs := by
  obtain ⟨evs₁, ev, evs₂, g, ss, vis, heq, hex, hrest⟩ := h
  subst heq
  have hbf₁ : BreakFree evs₁ := (breakFree_append.mp hbf).1
  refine ⟨evs₁, ev, evs₂, g, ss, vis, rfl, explains_of_classical hex, ?_⟩
  revert hrest
  dsimp only [NextEventCollides, NextEventCollidesClassical]
  generalize ev.cmd = cmd
  cases cmd with
  | init _ _ => exact id
  | send _ =>
    rintro ⟨hpt, hall⟩
    exact ⟨hpt, fun g' hg' => hall g' (prefixGhostsCli_sub hbf₁ hg')⟩
  | recv _ =>
    rintro ⟨hexit, hin⟩
    refine ⟨hexit, ?_⟩
    revert hin
    generalize ev.input = inp
    cases inp with
    | nil => exact id
    | cons tag body =>
      rintro (⟨htag, hw⟩ | ⟨p, hp, ⟨hkb, hver, hik, hw⟩ | ⟨hnkb, hpk⟩⟩)
      · exact Or.inl ⟨htag, whisperExcusedCli_of_classical hbf₁ hw⟩
      · exact Or.inr ⟨p, hp, Or.inl ⟨hkb, hver, hik, whisperExcusedCli_of_classical hbf₁ hw⟩⟩
      · exact Or.inr ⟨p, hp, Or.inr ⟨hnkb, preKeyExcusedCli_of_classical hbf₁ hpk⟩⟩

end Symbolic.Proofs.Swarm.UA.ClassicalBridge
