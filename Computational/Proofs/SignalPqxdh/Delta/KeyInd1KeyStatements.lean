/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyCoupling -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveBounds
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindBundle

/-!
# One-Key PQXDH δ Key Indistinguishability Headline Proof

**Checked by Lean.** Proves the one-key `KeyInd` δ-security theorem `pqxdh_key_indδ`
(`PqxdhKeyIndSecureδ S`, DEV-CLI16, DEV-PQ21) by assembling the per-query-kind costed
`ReductionDsl` family `pqxdhKeyInd1KeyCostedSims` with its resource bounds and active `G0 -> G3`
and `G3` game-hop bounds.
-/

public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security

/-- Equivalence of the one-key `G3` hybrid advantages `keyInd1KeyAdvG3` and `keyIndAdvG3_1Key`. -/
theorem keyInd1KeyAdvG3_eq_keyIndAdvG3_1Key (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) :
    keyInd1KeyAdvG3 S P A = keyIndAdvG3_1Key S P A := by
  have hImpl : pqxdhKeyInd1KeyShCrImpl false S P = pqxdhKeyIndShCrImpl1Key false S P := by
    funext q; cases q <;> rfl
  have hRun : runKeyInd1KeyShCrSim S P A = runKeyIndShCrSim1Key S P A := by
    unfold runKeyInd1KeyShCrSim runKeyIndShCrSim1Key
    rw [hImpl]
  unfold keyInd1KeyAdvG3 keyIndAdvG3_1Key keyInd1KeyExpG3 keyIndExpG3_1Key
    finalizeKeyIndG3 keyInd1KeyAllTestedClean
  rw [hRun]

/-- Per-query-kind `ReductionDsl` costed reduction family for one-key `KeyInd` at setup `S`. -/
def pqxdhKeyInd1KeyCostedSims (S : Setup) : KeyIndCostedReductionFamily S :=
  Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs.pqxdhKeyInd1KeyKindCostedSims S

theorem pqxdhKeyInd1KeyCostedSims_costedBounds (S : Setup) :
    KeyIndCostedReductionBounds S (pqxdhKeyInd1KeyCostedSims S) :=
  Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindBundle.pqxdhKeyInd1KeyKindCostedSims_bounds S

theorem pqxdhKeyInd1KeyCostedSims_simBounds (S : Setup) :
    KeyIndReductionQueryBounds S (pqxdhKeyInd1KeyCostedSims S).eval :=
  Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindBundle.pqxdhKeyInd1KeyKindCostedSims_queryBounds_of_active S
    (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveBounds.pqxdhKeyInd1KeyActiveCostedSims_simBounds S)

theorem ki1KeyActiveHopG0G3 (S : Setup) :
    PqxdhDelta.KI1KeyActiveHopG0G3Stmt S
      (pqxdhKeyInd1KeyCostedSims S).eval.sig
      (pqxdhKeyInd1KeyCostedSims S).eval.shcr :=
  Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindBundle.ki1KeyKindActiveHopG0G3 S

theorem ki1KeyActiveGapDhDsl (S : Setup) :
    PqxdhDelta.KI1KeyActiveG3BoundStmt S
      (pqxdhKeyInd1KeyCostedSims S).eval.gdh :=
  Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindBundle.ki1KeyKindActiveGapDhDsl S

theorem ki1KeyGapDhDsl (S : Setup) :
    PqxdhDelta.KI1KeyG3BoundStmt S (pqxdhKeyInd1KeyCostedSims S).eval.gdh :=
  Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindBundle.ki1KeyKindGapDhDsl S

theorem pqxdhKeyInd1KeyCostedSims_securityδ (S : Setup) :
    PqxdhKeyIndReductionBoundδ S (pqxdhKeyInd1KeyCostedSims S).eval :=
  Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindBundle.pqxdhKeyInd1KeyKindCostedSims_securityδ S

end Proofs.SignalPqxdh.Security

namespace SignalPqxdh.Security

open SignalPqxdh

/-- One-key random-oracle key indistinguishability at setup `S` under a δ-correct KEM. -/
theorem pqxdh_key_indδ (S : Setup) : PqxdhKeyIndSecureδ S :=
  _root_.Proofs.SignalPqxdh.Security.PqxdhDelta.pqxdhKeyIndSecureδ_of_activeFamily S
    (_root_.Proofs.SignalPqxdh.Security.pqxdhKeyInd1KeyCostedSims S)
    (_root_.Proofs.SignalPqxdh.Security.pqxdhKeyInd1KeyCostedSims_costedBounds S)
    (_root_.Proofs.SignalPqxdh.Security.pqxdhKeyInd1KeyCostedSims_simBounds S)
    (_root_.Proofs.SignalPqxdh.Security.ki1KeyActiveHopG0G3 S)
    (_root_.Proofs.SignalPqxdh.Security.ki1KeyActiveGapDhDsl S)

end SignalPqxdh.Security

end
