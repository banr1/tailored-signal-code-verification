/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyAuthDefs
public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyGlue
public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyRecvOPK
public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyRecvNoOPK
public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyMono
public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyTransfer
public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyCorrAt

/-!
# One-key `G3 → G3.5` authentication hop with imperfect KEM correctness

Combines `authCutoffGlue1Key`, `authRecvOPKδ1Key`, `authRecvNoOPKδ1Key`, `authCorrMono1Key`,
`authCorrTransfer1Key`, and `authCorrAt1Key` into the one-key `G3 → G3.5` hybrid bound
`auth_hop_G3_G3_5_leδ1Key`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.AuthSubHops1to3
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

theorem auth_hop_G3_G3_5_leδ1Key_of_bound (S : Setup)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (δ : ℝ) (hδ : KemDeltaCorrectReal P δ)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) (ε : ℝ)
    (hAny : (𝒟[runAuthFgLatchedSim1Key S P A.1 >>= fun x =>
      pure (badAuthFgAnyLatched P b.q_ro x.2.2)] {true}).toReal ≤ ε) :
    |authFixedAdvG3_1Key S P A.1 - authFixedAdvG3_5_1Key S P A.1| ≤
      2 * ε + 2 * (S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 250 +
        kemDecapsFailureTermReal S δ := by
  have hC := authCutoffGlue1Key S (authRecvOPKδ1Key S) (authRecvNoOPKδ1Key S)
    (authCorrMono1Key S) P hP b A
  have hT := authCorrTransfer1Key S P hP b A
  have hU := prob_hasBadKemCorrRecords_auth_le1Key S (authCorrAt1Key S) P hP δ hδ A.1
  have hTerm : kemDecapsFailureTermReal S δ = 2 * ((S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ) := by
    unfold kemDecapsFailureTermReal; ring
  rw [hTerm]
  linarith

/-- One-key `G3 → G3.5` hybrid bound under `CryptoWellFormedPrimitivesδ`, parameterized by the
`GapDhWithSign` bound `hAny`. -/
theorem auth_hop_G3_G3_5_leδ1Key (S : Setup)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (δ : ℝ) (hδ : KemDeltaCorrectReal P δ)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b)
    (hAny : (𝒟[runAuthFgLatchedSim1Key S P A.1 >>= fun x =>
      pure (badAuthFgAnyLatched P b.q_ro x.2.2)] {true}).toReal ≤
      ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A)) :
    |authFixedAdvG3_1Key S P A.1 - authFixedAdvG3_5_1Key S P A.1| ≤
      2 * ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A) +
      2 * (S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 250 +
      kemDecapsFailureTermReal S δ := by
  have h := auth_hop_G3_G3_5_leδ1Key_of_bound S P hP δ hδ b A _ hAny
  linarith

end Proofs.SignalPqxdh.Security.PqxdhDelta
