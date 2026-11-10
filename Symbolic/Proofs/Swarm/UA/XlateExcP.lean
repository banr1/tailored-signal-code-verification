/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.UA.XlateInv
import Symbolic.Proofs.Swarm.UA.XlateSteps

/-!
# Pre-Key Start Excuse Transfer

Proves `xlate_exc_p : XlateExcPSpec`: on an accepted pre-key `recv` run with unknown base key,
`¬ CollisionAfterExplainedPrefixClassical (evs ++ [.run ev])` refutes
`PreKeyStartCollidesOrRejectsMoves` via `XlateInv.xlate_inv`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.XlateExcP

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (RunEvent CliEvent)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF (SemReady)
open Symbolic.Proofs.Swarm.UA.Defs (XlateExcPSpec callsOf SchedFits)
open Symbolic.Proofs.Swarm.UA.XlateSteps (preKeyRepresentations_eq bobStartCollision_iff)
open Symbolic.Proofs.Swarm.UA.XlateInv (xlate_inv schedFits_prefix)

/-- `¬ CollisionAfterExplainedPrefixClassical` refutes `PreKeyStartCollidesOrRejectsMoves` at an
accepted pre-key `recv` run with unknown base key. -/
theorem xlate_exc_p : XlateExcPSpec := by
  intro interp' r S who ok evs ev g₀ ss₀ vis₀ peer out p t_clean accepted
    hwf hS hsched _ hexp₀ _ hcmd hexit hpw hnk hrep₀ hncol τ₁ g ms _ _ hexc_m
  have hsched₀ : SchedFits (callsOf evs) who ok := by
    rw [Symbolic.Proofs.Swarm.UA.Base.callsOf_append] at hsched
    exact schedFits_prefix hsched
  rcases hinp : ev.input with _ | ⟨tag, body⟩
  · rw [hinp] at hpw; cases hpw
  · apply hncol
    refine ⟨evs, ev, [], g₀, ss₀, vis₀, rfl, hexp₀, ?_⟩
    simp only [NextEventCollidesClassical, hcmd]
    refine ⟨⟨out, hexit⟩, ?_⟩
    rw [hinp] at hpw hrep₀ ⊢
    refine Or.inr ⟨p, hpw, Or.inr ⟨hnk, hrep₀, ?_⟩⟩
    rcases hexc_m.2 with hkm | hall
    · exact Or.inl hkm
    · refine Or.inr fun g' ss' vis' hexp' hnrc' x hx => ?_
      obtain ⟨τ₁', ms', hexp_c', hnrc_c', htr', hsalts', hpre', hpt'⟩ :=
        xlate_inv hwf hS hsched₀ hexp' hnrc'
      have hx_m : x ∈ preKeyRepresentations interp' r S g' ms' ev.input := by
        rw [hinp]; rwa [preKeyRepresentations_eq htr']
      exact (bobStartCollision_iff htr' hsalts' hpre' hpt').mp
        (hall τ₁' g' ms' hexp_c' hnrc_c' x hx_m)

end Symbolic.Proofs.Swarm.UA.XlateExcP
