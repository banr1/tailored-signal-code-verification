/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyDefs
import Computational.Proofs.SignalPqxdh.Delta.KeyInd.CorrAt

/-!
# One-Key PQXDH δ Key Indistinguishability: Per-Index KEM Correctness Reduction

**Checked by Lean.** Proves `ki1KeyCorrAt : KI1KeyCorrAtStmt` (DEV-CLI16, DEV-PQ21) on
`runKeyInd1KeyShCrSim` via `KICorrAt.badKemCorrProbGenericAt_le_kemCorr`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

namespace KICorrAt1Key

theorem badKemCorrProbKeyInd1KeyRoAt_le_kemCorrProb (S : Setup) (P : Primitives)
    (idx : Nat) (A : KeyIndAdversary S) :
    (𝒟[runKeyInd1KeyShCrSim S P A >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)]
      {true}).toReal ≤
      (𝒟[kemCorrExpProb P (fun pk sk =>
          Prod.fst <$>
            _root_.Proofs.SignalPqxdh.Security.shcrChoosePkKeyInd1KeyAt S P
              (idx / S.N_send_tot) (idx % S.N_send_tot) A pk sk)]
        {true}).toReal := by
  unfold _root_.Proofs.SignalPqxdh.Security.shcrChoosePkKeyInd1KeyAt
  have hEq :
      (runKeyInd1KeyShCrSim S P A >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)) =
      (($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb)) >>= fun b0 =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndShCrState S) ProbComp) +
            pqxdhKeyInd1KeyShCrCachedImpl false S P) A.run).run { base := b0 } >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)) := by
    unfold runKeyInd1KeyShCrSim
    simp only [bind_assoc, pure_bind]
    refine bind_congr (fun secb => ?_)
    have hSim := CommutesRel.simulateQ_add_unif (cacheShCrAdvKeys S P)
      (pqxdhKeyInd1KeyShCrCachedImpl false S P) (pqxdhKeyInd1KeyShCrImpl false S P)
      (pqxdhKeyInd1KeyShCrCachedImpl_false_commutes_cache S P)
      A.run { base := KeyIndState.empty S secb }
    unfold CommutesRel at hSim
    have hInit : cacheShCrAdvKeys S P { base := KeyIndState.empty S secb } =
        { base := KeyIndState.empty S secb } := rfl
    rw [hInit] at hSim
    rw [hSim, bind_map_left]
    rfl
  rw [hEq]
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  exact KICorrAt.badKemCorrProbGenericAt_le_kemCorr P
    ($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb))
    KeyIndState.spkBundles
    (pqxdhKeyInd1KeyShCrCachedImpl false S P)
    (pqxdhKeyInd1KeyShCrCachedImpl true S P)
    (tryPauseKeyInd1KeyQuery S P)
    idx
    (by
      intro b0 hb0
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hb0
      rcases hb0 with ⟨secb, _, rfl⟩
      rfl)
    (pqxdhKeyInd1KeyShCrCachedImpl_clearFalse S P)
    (pqxdhKeyInd1KeyShCrCachedImpl_afterGen S P (idx / S.N_send_tot))
    (pqxdhKeyInd1KeyShCrCachedImpl_beforeGen S P (idx / S.N_send_tot))
    (pqxdhKeyInd1KeyShCrCachedImpl_validStep S P (idx / S.N_send_tot))
    (pqxdhKeyInd1KeyShCrCachedImpl_sendStep S P)
    (pqxdhKeyInd1KeyShCrCachedImpl_pauseNone S P (idx % S.N_send_tot))
    (pqxdhKeyInd1KeyShCrCachedImpl_pauseSome S P (idx / S.N_send_tot) (idx % S.N_send_tot))
    A.run

end KICorrAt1Key

/-- Reduces one flat index of `hasBadKemCorrRecords` in `runKeyInd1KeyShCrSim` to
    `kemCorrExpProb`. -/
theorem ki1KeyCorrAt (S : Setup) : KI1KeyCorrAtStmt S := by
  intro P _hP A idx _hIdx
  exact ⟨fun pk sk =>
      Prod.fst <$>
        _root_.Proofs.SignalPqxdh.Security.shcrChoosePkKeyInd1KeyAt S P
          (idx / S.N_send_tot) (idx % S.N_send_tot) A pk sk,
    KICorrAt1Key.badKemCorrProbKeyInd1KeyRoAt_le_kemCorrProb S P idx A⟩

end Proofs.SignalPqxdh.Security.PqxdhDelta
