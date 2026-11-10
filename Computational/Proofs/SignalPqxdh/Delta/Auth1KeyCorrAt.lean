/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.AuthDefs
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd.CorrAt
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Delta.Auth.CorrAt
public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyAuthDefs
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC3b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c4
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopB1

/-!
# One-key authentication: per-index KEM correctness reduction

Proves `authCorrAt1Key` (`AuthCorrAtStmt1Key`), the one-key counterpart of `Delta/Auth/CorrAt.lean`
over `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

private theorem ac_badKemCorrProbAuthAt_le_kemCorrProb1Key (S : Setup) (P : Primitives)
    (idx : Nat) (A : AuthAdversary S) :
    (𝒟[runAuthShCrSim1Key S P A >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)]
      {true}).toReal ≤
      (𝒟[kemCorrExpProb P (fun pk sk =>
          Prod.fst <$> shcrChoosePkAuthAt1Key S P (idx / S.N_send_tot) (idx % S.N_send_tot) A pk sk)]
        {true}).toReal := by
  unfold shcrChoosePkAuthAt1Key
  have hEq :
      (runAuthShCrSim1Key S P A >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)) =
      (($ᵗ Bool >>= fun secb => pure (AuthState.empty S secb)) >>= fun b0 =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthShCrState S) ProbComp) + pqxdhAuthShCrSimImpl1Key false S P) A.run).run { base :=
            b0 } >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)) := by
    simp [runAuthShCrSim1Key]
  rw [hEq]
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  exact KICorrAt.badKemCorrProbGenericAt_le_kemCorr P
    ($ᵗ Bool >>= fun secb => pure (AuthState.empty S secb))
    AuthState.spkBundles
    (pqxdhAuthShCrSimImpl1Key false S P)
    (pqxdhAuthShCrSimImpl1Key true S P)
    (tryPauseAuthQuery1Key S P)
    idx
    (by
      intro b0 hb0
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hb0
      rcases hb0 with ⟨secb, _, rfl⟩
      rfl)
    (pqxdhAuthShCrSimImpl_clearFalse1Key S P)
    (pqxdhAuthShCrSimImpl_afterGen1Key S P (idx / S.N_send_tot))
    (pqxdhAuthShCrSimImpl_beforeGen1Key S P (idx / S.N_send_tot))
    (pqxdhAuthShCrSimImpl_validStep1Key S P (idx / S.N_send_tot))
    (pqxdhAuthShCrSimImpl_sendStep1Key S P)
    (pqxdhAuthShCrSimImpl_pauseNone1Key S P (idx % S.N_send_tot))
    (pqxdhAuthShCrSimImpl_pauseSome1Key S P (idx / S.N_send_tot) (idx % S.N_send_tot))
    A.run

/-- Reduces each flat index of the KEM correctness bad event in `runAuthShCrSim1Key` to
`kemCorrExpProb`. -/
theorem authCorrAt1Key (S : Setup) : AuthCorrAtStmt1Key S := by
  intro P _hP A idx _hIdx
  exact ⟨fun pk sk =>
      Prod.fst <$> shcrChoosePkAuthAt1Key S P (idx / S.N_send_tot) (idx % S.N_send_tot) A pk sk,
    ac_badKemCorrProbAuthAt_le_kemCorrProb1Key S P idx A⟩

end Proofs.SignalPqxdh.Security.PqxdhDelta
