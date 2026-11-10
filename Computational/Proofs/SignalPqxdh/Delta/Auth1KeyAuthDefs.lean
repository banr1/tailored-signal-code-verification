/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyIndDefs
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c3
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c4
public import Computational.Proofs.SignalPqxdh.Security.AuthAssembly
public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmac
public import Computational.Proofs.SignalPqxdh.Delta.AuthDefs
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
# One-key authentication δ hop statements

One-key counterparts of the `Delta/AuthDefs.lean` hop statements and union bound over the
single-scalar identity oracle `pqxdhAuthImpl1KeyG`.
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

/-- One-key `.recvOPK` step coupling on `AuthSendLatchedState` under `CryptoWellFormedPrimitivesδ`
with bad event `badSendδ`. -/
def AuthRecvOPKδStmt1Key (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (maxRo : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
      (s35 s3 : AuthSendLatchedState S),
      AuthSendWinGuardedCoupledInv P s35 s3 →
      isAuthG3Abort P s3.hyb = false →
      s3.hyb.base.hasWonAuth = false →
      badSendδ P maxRo s3 = false →
      s3.adv.advRoLog.length ≤ maxRo →
      s3.adv.respRecs.length ≤ S.N_sess_tot →
      RelProbUpToBad
        (fun y35 y3 =>
          (y35.1 = y3.1 ∧ AuthSendWinGuardedCoupledInv P y35.2 y3.2) ∨
          (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
        (fun y3 => badSendδ P maxRo y3.2)
        ((pqxdhAuthSendLatchedStageImpl1Key .g3_5 S P (.recvOPK k j o msg)).run s35)
        ((pqxdhAuthSendLatchedStageImpl1Key .g3 S P (.recvOPK k j o msg)).run s3)

/-- One-key `.recvNoOPK` step coupling on `AuthSendLatchedState` under
`CryptoWellFormedPrimitivesδ` with bad event `badSendδ`. -/
def AuthRecvNoOPKδStmt1Key (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (maxRo : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
      (s35 s3 : AuthSendLatchedState S),
      AuthSendWinGuardedCoupledInv P s35 s3 →
      isAuthG3Abort P s3.hyb = false →
      s3.hyb.base.hasWonAuth = false →
      badSendδ P maxRo s3 = false →
      s3.adv.advRoLog.length ≤ maxRo →
      s3.adv.respRecs.length ≤ S.N_sess_tot →
      RelProbUpToBad
        (fun y35 y3 =>
          (y35.1 = y3.1 ∧ AuthSendWinGuardedCoupledInv P y35.2 y3.2) ∨
          (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
        (fun y3 => badSendδ P maxRo y3.2)
        ((pqxdhAuthSendLatchedStageImpl1Key .g3_5 S P (.recvNoOPK k j l msg)).run s35)
        ((pqxdhAuthSendLatchedStageImpl1Key .g3 S P (.recvNoOPK k j l msg)).run s3)

/-- Monotonicity of `hasBadAuthKemCorr` along one-key `.g3` send-latched steps. -/
def AuthCorrMonoStmt1Key (S : Setup) : Prop :=
  ∀ (P : Primitives) (q : AuthQuery S) (s : AuthSendLatchedState S),
    hasBadAuthKemCorr P s.hyb = true →
    ∀ y ∈ support ((pqxdhAuthSendLatchedStageImpl1Key .g3 S P q).run s),
      hasBadAuthKemCorr P y.2.hyb = true

/-- One-key `G3 → G3.5` cutoff bound with the `hasBadAuthKemCorr` bad-event term. -/
def AuthCutoffδStmt1Key (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      |authFixedAdvG3_1Key S P A.1 - authFixedAdvG3_5_1Key S P A.1| ≤
        2 * (𝒟[runAuthFgLatchedSim1Key S P A.1 >>= fun x =>
          pure (badAuthFgAnyLatched P b.q_ro x.2.2)] {true}).toReal +
        2 * (S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 250 +
        2 * (𝒟[runAuthSendLatchedSim1Key .g3 S P A.1 >>= fun x =>
          pure (hasBadAuthKemCorr P x.2.2.hyb)] {true}).toReal

/-- Derivation of `AuthCutoffδStmt1Key` from the `.recvOPK`/`.recvNoOPK` couplings and bad-event
monotonicity. -/
def AuthCutoffGlueStmt1Key (S : Setup) : Prop :=
  AuthRecvOPKδStmt1Key S → AuthRecvNoOPKδStmt1Key S → AuthCorrMonoStmt1Key S → AuthCutoffδStmt1Key S

/-- Transfer of `hasBadAuthKemCorr` in `runAuthSendLatchedSim1Key .g3` to `hasBadKemCorrRecords` in
`runAuthShCrSim1Key`. -/
def AuthCorrTransferStmt1Key (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      (𝒟[runAuthSendLatchedSim1Key .g3 S P A.1 >>= fun x =>
          pure (hasBadAuthKemCorr P x.2.2.hyb)] {true}).toReal ≤
        (𝒟[runAuthShCrSim1Key S P A.1 >>= fun x =>
          pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal

/-- Per-index reduction from the KEM correctness bad event in `runAuthShCrSim1Key` to
`kemCorrExpProb`. -/
def AuthCorrAtStmt1Key (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (A : AuthAdversary S) (idx : ℕ), idx < S.N_spk_tot * S.N_send_tot →
      ∃ choosePk : Bytes → Bytes → ProbComp Bytes,
        (𝒟[runAuthShCrSim1Key S P A >>= fun x =>
            pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)]
          {true}).toReal ≤
          (𝒟[kemCorrExpProb P choosePk] {true}).toReal

/-- Union bound of `N_spk_tot * N_send_tot * δ` on `hasBadKemCorrRecords` in `runAuthShCrSim1Key`. -/
theorem prob_hasBadKemCorrRecords_auth_le1Key (S : Setup) (hAt : AuthCorrAtStmt1Key S)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (δ : ℝ) (hδ : KemDeltaCorrectReal P δ)
    (A : AuthAdversary S) :
    (𝒟[runAuthShCrSim1Key S P A >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ := by
  have hU := _root_.SignalPqxdh.Security.toReal_any_range_le_sum (runAuthShCrSim1Key S P A)
    (S.N_spk_tot * S.N_send_tot)
    (fun idx x => hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)
  refine le_trans hU ?_
  calc (∑ k ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
        (𝒟[runAuthShCrSim1Key S P A >>= fun x =>
          pure (hasBadKemCorrRecordsAt S P k x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal)
      ≤ ∑ _k ∈ Finset.range (S.N_spk_tot * S.N_send_tot), δ := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        obtain ⟨choosePk, hC⟩ := hAt P hP A k (Finset.mem_range.mp hk)
        exact le_trans hC (kemCorrExpProb_le P δ hδ choosePk)
    _ = (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end Proofs.SignalPqxdh.Security.PqxdhDelta
