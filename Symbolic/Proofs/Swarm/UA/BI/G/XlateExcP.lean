/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.BI.RAB.Defs
import Symbolic.Proofs.Swarm.UA.BI.G.SlotRpkNOHelpers
import Symbolic.Proofs.Swarm.UA.Base

/-!
# Pre-Key Start Collision Translation

Proves `xlate_exc_p_b_of : XlateInvSpecB -> XlateExcPSpecB`: absence of
`CollisionAfterExplainedPrefix` on `evs ++ [.run ev]` for an accepted pre-key `recv` run with an
unknown base key refutes `PreKeyStartCollidesOrRejectsMoves` at the call's cut.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.G.XlateExcP

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (RunEvent CliEvent)
open _root_.DY.Libsignal.Composed.Refinement (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry Move ProtocolSetupWF
  Explains ReadCollision PreKeyFields parsePreKeyWire KnownBaseKeyOn
  preKeyRepresentations preKeyRepresentationsOn BobSessionStartCollidesOrImplicitRejects BobSessionStartCollidesOrImplicitRejectsOn
  runTrace runTraceMoves runVis honestSalts honestSaltsOf prefixTerms plaintextTerms)
open _root_.DY.Libsignal.Composed.Refinement.Cli (CliTurn ExplainsCli CollisionAfterExplainedPrefix
  ReadCollisionCli PreKeyStartCollidesOrRejectsMoves)
open Symbolic.Swarm.CREF (SemReady)
open Symbolic.Proofs.Swarm.UA.Defs (callsOf SchedFits)
open Symbolic.Proofs.Swarm.UA.Base (callsOf_append schedFits_of_append)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Defs (XlateInvSpecB XlateExcPSpecB)
open Symbolic.Proofs.Swarm.UA.BI.G.SlotRpkNOHelpers (preKeyRepresentations_iff_on
  bobStartCollision_iff_on)

/-- Absence of `CollisionAfterExplainedPrefix` refutes `PreKeyStartCollidesOrRejectsMoves` at the
call's cut, given `XlateInvSpecB`. -/
theorem xlate_exc_p_b_of (hXI : XlateInvSpecB) : XlateExcPSpecB := by
  intro interp' r S who ok evs ev g₀ ss₀ vis₀ peer out p t_clean accepted
    hwf hS hsched _ hexp₀ _ hcmd hexit hpw hnk hrep₀ hncol τ₁ g ms _ _ hexc_m
  have hsched₀ : SchedFits (callsOf evs) who ok := by
    rw [callsOf_append] at hsched
    exact schedFits_of_append hsched
  rcases hinp : ev.input with _ | ⟨tag, body⟩
  · rw [hinp] at hpw; cases hpw
  · apply hncol
    refine ⟨evs, ev, [], g₀, ss₀, vis₀, rfl, hexp₀, ?_⟩
    simp only [_root_.DY.Libsignal.Composed.Refinement.Cli.NextEventCollides, hcmd]
    refine ⟨⟨out, hexit⟩, ?_⟩
    rw [hinp] at hpw hrep₀ ⊢
    refine Or.inr ⟨p, hpw, Or.inr ⟨hnk, hrep₀, ?_⟩⟩
    rcases hexc_m.2 with hkm | hall
    · exact Or.inl hkm
    · refine Or.inr fun g' ss' vis' hexp' hnrc' x hx => ?_
      obtain ⟨τ₁', ms', hexp_c', hnrc_c', htr', hsalts', hpre', hpt'⟩ :=
        hXI hwf hS hsched₀ hexp' hnrc'
      have hx_m : x ∈ preKeyRepresentations interp' r S g' ms' ev.input := by
        rw [hinp]
        exact (preKeyRepresentations_iff_on htr').mpr hx
      exact (bobStartCollision_iff_on htr' hsalts' hpre' hpt').mp
        (hall τ₁' g' ms' hexp_c' hnrc_c' x hx_m)

end Symbolic.Proofs.Swarm.UA.BI.G.XlateExcP
