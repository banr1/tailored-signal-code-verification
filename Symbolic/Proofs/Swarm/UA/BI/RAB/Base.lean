/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
import Symbolic.Proofs.Swarm.UA.Base

/-!
# Collision Monotonicity and Rejected-Run Explanation Lemmas

Basic list-extension lemmas for `CollisionAfterExplainedPrefix`, `MatchesEvents`, `Explains` on
rejected runs, and `ReadCollisionCli`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.RAB.Base

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.Base (modelRunWF_of_append ghostWF_of_append)

theorem collisionAtCli_append {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {evs : List CliEvent} (more : List CliEvent) (h : CollisionAfterExplainedPrefix interp r S evs) :
    CollisionAfterExplainedPrefix interp r S (evs ++ more) := by
  obtain ⟨evs₁, ev, evs₂, g, ss, vis, heq, hrest⟩ := h
  exact ⟨evs₁, ev, evs₂ ++ more, g, ss, vis, by simp [heq], hrest⟩

theorem matchesEventsAt_snoc_rejected {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {ev : RunEvent} (hrej : RunRejected ev)
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEventsAt interp r S g initIds tr ss evs vis) :
    MatchesEventsAt interp r S g initIds tr ss (evs ++ [.run ev]) vis := by
  induction h with
  | @nil initIds tr ss hinv =>
    have h0 : MatchesEventsAt interp r S g initIds tr (ss ++ []) [.run ev] [] :=
      .run0 hinv hrej (.nil (by simp))
    simpa using h0
  | run1 hpre hrm _ ih => exact .run1 hpre hrm ih
  | run0 hpre hrej' _ ih => exact .run0 hpre hrej' ih
  | env hpre hem _ ih => exact .env hpre hem ih

theorem matchesEvents_snoc_rejected {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ev : RunEvent} (hrej : RunRejected ev) {tr : ExecTrace} {ss : List Step}
    {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEvents interp r S g tr ss evs vis) :
    MatchesEvents interp r S g tr ss (evs ++ [.run ev]) vis :=
  matchesEventsAt_snoc_rejected hrej h

/-- A rejected run extends an explanation with zero additional model steps. -/
theorem explains_snoc_rejected {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs : List CliEvent} {ev : RunEvent}
    (hrej : RunRejected ev) (h : Explains interp r S g ss vis evs) :
    Explains interp r S g ss vis (evs ++ [.run ev]) :=
  ⟨h.1, h.2.1, h.2.2.1, matchesEvents_snoc_rejected hrej h.2.2.2⟩

theorem readCollisionCli_append {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss₁ : List Step} {evs : List CliEvent} (ss₂ : List Step) (more : List CliEvent)
    (h : ReadCollisionCli interp r S g ss₁ evs) :
    ReadCollisionCli interp r S g (ss₁ ++ ss₂) (evs ++ more) := by
  obtain ⟨e₁, ev, e₂, s₁, s₂, m, vis₁, msgIdx, out, b, t, rfl, rfl, hrest⟩ := h
  exact ⟨e₁, ev, e₂ ++ more, s₁, s₂ ++ ss₂, m, vis₁, msgIdx, out, b, t, by simp, by simp, hrest⟩

end Symbolic.Proofs.Swarm.UA.BI.RAB.Base
