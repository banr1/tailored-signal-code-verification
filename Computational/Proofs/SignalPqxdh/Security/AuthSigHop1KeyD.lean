/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyC3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSig

/-!
# One-key `Auth` bad-signature hop: final assembly

Instantiates `Auth1KeySigCoupling` to prove `authSig1KeyPerKBound_holds` and the frozen-game
bad-signature hop `auth1Key_hop_sigEufCma_frozen_le`.
-/

@[expose] public section

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal

namespace Proofs.SignalPqxdh.Security

noncomputable def auth1KeySigCoupling (S : Setup) (P : Primitives) (b : QueryBudget)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (sk : Bytes) (hsk : sk.length = 32) :
    Auth1KeySigCoupling S P b k sk where
  Inv := FgAuthSimInvSig1Key S b P hP k sk hsk
  inv_empty := fgAuthSimInvSig1Key_empty S b P hP k sk hsk
  inv_prinLen := fun rem hst st h => fgAuthSimInvSig1Key_prinLen S b P hP k sk hsk rem hst st h
  inv_ext := fun rem hst st h bundle =>
    fgAuthSimInvSig1Key_ext S b P hP k sk hsk rem hst st h bundle
  inv_signed := fun rem hst st h => fgAuthSimInvSig1Key_signed S b P hP k sk hsk rem hst st h
  step := fun q rem hst st _ _ hD hI k1 k2 hC hDC =>
    fgAuthStepCoupling_sig1Key S b P hP k sk hsk q rem hst st hD hI k1 k2 hC hDC

theorem authSig1KeyPerKBound_holds (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b)
    (k : ℕ) : authSig1KeyPerKBound S P b A k :=
  authSig1KeyPerKBound_of_coupling S P hP b A k
    (fun sk hsk => auth1KeySigCoupling S P b hP k sk hsk)

/-- Frozen-game bad-signature hop from `G0_1` (bundle provenance) to `G1` (exact provenance). -/
theorem auth1Key_hop_sigEufCma_frozen_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    |(𝒟[authExpG0_1WithProvFrozen1Key (checkBundleProvenance P) S P A.val].boolBias).toReal -
     (𝒟[authExpG1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A.val].boolBias).toReal| ≤
      (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigReductionAuth1Key S b A) :=
  auth1Key_hop_sigEufCma_frozen_le_of_perK S P b A
    (fun k _ => authSig1KeyPerKBound_holds S P hP b A k)

end Proofs.SignalPqxdh.Security
