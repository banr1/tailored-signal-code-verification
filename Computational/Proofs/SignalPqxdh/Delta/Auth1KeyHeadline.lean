/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyAssembly
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyStatements
public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdComb

/-!
# Conditional one-key `Auth` headline closure

Defines `Auth1KeyDslFamily` and derives `PqxdhAuth1KeySecureδ` and
`PqxdhCorrectAndSecureWithAuthδ` from costed one-key reductions, the signature hop, and the Gap-DH
bad-event bound.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security Proofs.SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

/-- Costed one-key `Auth` reduction family bundled with its syntactic/semantic bounds and advantage
transfers from the shallow simulators. -/
structure Auth1KeyDslFamily (S : Setup) where
  R : Auth1KeyCostedReductionFamily S
  bounds : Auth1KeyCostedReductionBounds S R
  queryBounds : Auth1KeyReductionQueryBounds S R.eval
  sig_le : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
    GapSigEufCma P P.isValidDhTriple (sigReductionAuth1Key S b A) ≤
      GapSigEufCma P P.isValidDhTriple (R.eval.sig b A)
  gdh_le : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
    GapDhWithSign P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A) ≤
      GapDhWithSign P P.isValidDhTriple P.pow8 (R.eval.gdh b A)
  shcr_le : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
    KemShCr P (shcrReductionAuth1Key S b A) ≤ KemShCr P (R.eval.shcr b A)
  ck_le : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
    PrfChainKey P (prfCkReductionAuthFixed1Key S b A) ≤ PrfChainKey P (R.eval.ck b A)
  mk_le : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
    PrfMsgKeys P (prfMsgKeysReductionAuthFixed1Key S b A) ≤ PrfMsgKeys P (R.eval.mk b A)
  cpa_le : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
    AeadIndCpa P (aeadCpaReductionAuthFixed1Key S b A) ≤ AeadIndCpa P (R.eval.cpa b A)
  int_le : ∀ (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
    PrfHmac P (prfHmacReductionAuth1Key S b A) ≤ PrfHmac P (R.eval.int b A)

/-- One-key signature hop bound against `sigReductionAuth1Key`. -/
def Auth1KeySigHopStmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      |(𝒟[authExpG0_1WithProvFrozen1Key (checkBundleProvenance P) S P A.1].boolBias).toReal -
       (𝒟[authExpG1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A.1].boolBias).toReal|
        ≤ (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigReductionAuth1Key S b A)

/-- Per-principal one-key signature hop bound `authSig1KeyPerKBound`. -/
def Auth1KeySigPerKStmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      ∀ k < S.N_id, authSig1KeyPerKBound S P b A k

theorem auth1KeySigHopStmt_of_perK (S : Setup) (h : Auth1KeySigPerKStmt S) :
    Auth1KeySigHopStmt S := fun P hP b A =>
  auth1Key_hop_sigEufCma_frozen_le_of_perK S P b A (h P hP b A)

/-- Gap-DH bad-event bound for the one-key latched simulator `runAuthFgLatchedSim1Key`. -/
def Auth1KeyGapDhAnyStmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      (𝒟[runAuthFgLatchedSim1Key S P A.1 >>= fun x =>
        pure (badAuthFgAnyLatched P b.q_ro x.2.2)] {true}).toReal ≤
      ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdv4 S b A)

/-- Derives `PqxdhAuth1KeySecureδ S` from an `Auth1KeyDslFamily`, `Auth1KeySigHopStmt`, and
`Auth1KeyGapDhAnyStmt`. -/
theorem pqxdhAuth1KeySecureδ_of (S : Setup) (F : Auth1KeyDslFamily S)
    (hSig : Auth1KeySigHopStmt S) (hAny : Auth1KeyGapDhAnyStmt S) :
    PqxdhAuth1KeySecureδ S :=
  ⟨F.R, F.bounds, F.queryBounds,
    pqxdh_auth1Key_bound_of_sig_h3_costed S F.R
      (fun P hP b A => (hSig P hP b A).trans
        (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (GapSigEufCma_ne_top _ _ _) (F.sig_le P b A)) (Nat.cast_nonneg _))) hAny F.gdh_le F.shcr_le F.ck_le F.mk_le
      F.cpa_le F.int_le⟩

/-- Derives `PqxdhCorrectAndSecureWithAuthδ` from costed one-key `Auth` families and the signature
and Gap-DH hop bounds. -/
theorem pqxdhCorrectAndSecureWithAuthδ_of (F : ∀ S : Setup, Auth1KeyDslFamily S)
    (hSig : ∀ S : Setup, Auth1KeySigHopStmt S)
    (hAny : ∀ S : Setup, Auth1KeyGapDhAnyStmt S) :
    PqxdhCorrectAndSecureWithAuthδ := by
  intro P S
  exact ⟨wellFormedδ_pqxdhCorrect P, pqxdh_key_indδ S,
    pqxdhAuth1KeySecureδ_of S (F S) (hSig S) (hAny S)⟩

theorem pqxdhCorrectAndSecureWithAuthδ_of_perK (F : ∀ S : Setup, Auth1KeyDslFamily S)
    (hPerK : ∀ S : Setup, Auth1KeySigPerKStmt S)
    (hAny : ∀ S : Setup, Auth1KeyGapDhAnyStmt S) :
    PqxdhCorrectAndSecureWithAuthδ :=
  pqxdhCorrectAndSecureWithAuthδ_of F (fun S => auth1KeySigHopStmt_of_perK S (hPerK S)) hAny

theorem auth1KeyGapDhAnyStmt_holds (S : Setup) : Auth1KeyGapDhAnyStmt S := fun P hP b A =>
  prob_badAuthFgAnyLatched_runAuthFgLatchedSim1Key_le_gapDhWithSign S b P hP A

theorem pqxdhCorrectAndSecureWithAuthδ_of_perK' (F : ∀ S : Setup, Auth1KeyDslFamily S)
    (hPerK : ∀ S : Setup, Auth1KeySigPerKStmt S) :
    PqxdhCorrectAndSecureWithAuthδ :=
  pqxdhCorrectAndSecureWithAuthδ_of_perK F hPerK auth1KeyGapDhAnyStmt_holds

end Proofs.SignalPqxdh.Security.PqxdhDelta

#print axioms Proofs.SignalPqxdh.Security.PqxdhDelta.pqxdhAuth1KeySecureδ_of
#print axioms Proofs.SignalPqxdh.Security.PqxdhDelta.pqxdhCorrectAndSecureWithAuthδ_of
#print axioms Proofs.SignalPqxdh.Security.PqxdhDelta.pqxdhCorrectAndSecureWithAuthδ_of_perK
#print axioms Proofs.SignalPqxdh.Security.PqxdhDelta.pqxdhCorrectAndSecureWithAuthδ_of_perK'
