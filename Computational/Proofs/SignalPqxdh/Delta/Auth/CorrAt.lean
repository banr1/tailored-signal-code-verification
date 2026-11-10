/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.AuthDefs
import Computational.Proofs.SignalPqxdh.Delta.KeyInd.CorrAt
import VCVio.EvalDist.Monad.Basic

/-!
# PQXDH δ Authentication: Per-Index KEM Correctness Reduction

**Checked by Lean.** Proves `authCorrAt` (`AuthCorrAtStmt`, DEV-PQ21) by instantiating
`badKemCorrProbGenericAt_le_kemCorr` with `shcrChoosePkAuthAt`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

private theorem ac_badKemCorrProbAuthAt_le_kemCorrProb (S : Setup) (P : Primitives)
    (idx : Nat) (A : AuthAdversary S) :
    (𝒟[runAuthShCrSim S P A >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)]
      {true}).toReal ≤
      (𝒟[kemCorrExpProb P (fun pk sk =>
          Prod.fst <$> shcrChoosePkAuthAt S P (idx / S.N_send_tot) (idx % S.N_send_tot) A pk sk)]
        {true}).toReal := by
  unfold shcrChoosePkAuthAt
  have hEq :
      (runAuthShCrSim S P A >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)) =
      (($ᵗ Bool >>= fun secb => pure (AuthState.empty S secb)) >>= fun b0 =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthShCrState S) ProbComp) + pqxdhAuthShCrSimImpl false S P) A.run).run { base :=
            b0 } >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)) := by
    simp [runAuthShCrSim]
  rw [hEq]
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  exact KICorrAt.badKemCorrProbGenericAt_le_kemCorr P
    ($ᵗ Bool >>= fun secb => pure (AuthState.empty S secb))
    AuthState.spkBundles
    (pqxdhAuthShCrSimImpl false S P)
    (pqxdhAuthShCrSimImpl true S P)
    (tryPauseAuthQuery S P)
    idx
    (by
      intro b0 hb0
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hb0
      rcases hb0 with ⟨secb, _, rfl⟩
      rfl)
    (pqxdhAuthShCrSimImpl_clearFalse S P)
    (pqxdhAuthShCrSimImpl_afterGen S P (idx / S.N_send_tot))
    (pqxdhAuthShCrSimImpl_beforeGen S P (idx / S.N_send_tot))
    (pqxdhAuthShCrSimImpl_validStep S P (idx / S.N_send_tot))
    (pqxdhAuthShCrSimImpl_sendStep S P)
    (pqxdhAuthShCrSimImpl_pauseNone S P (idx % S.N_send_tot))
    (pqxdhAuthShCrSimImpl_pauseSome S P (idx / S.N_send_tot) (idx % S.N_send_tot))
    A.run

theorem authCorrAt (S : Setup) : AuthCorrAtStmt S := by
  intro P _hP A idx _hIdx
  exact ⟨fun pk sk =>
      Prod.fst <$> shcrChoosePkAuthAt S P (idx / S.N_send_tot) (idx % S.N_send_tot) A pk sk,
    ac_badKemCorrProbAuthAt_le_kemCorrProb S P idx A⟩

end Proofs.SignalPqxdh.Security.PqxdhDelta
