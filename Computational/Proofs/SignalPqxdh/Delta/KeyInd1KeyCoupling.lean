/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyDefs
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyHopG0G3
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyCorrAt
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyStop
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyAtomic
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.HeadlineDelta

/-!
# Costed `ReductionDsl` Assembly for One-Key PQXDH δ Key Indistinguishability

**Checked by Lean.** Packages the atomic `sig` and `shcr` costed reductions with a parameterized
`GapDhWithSign` reduction into `pqxdhKeyInd1KeyCostedFamily` and assembles `PqxdhKeyIndSecureδ`
from syntactic, semantic, `G0 -> G3`, and `G3` reduction obligations.
-/

@[expose] public section

set_option autoImplicit false

open _root_.ReductionDsl
open SignalPqxdh
open SignalPqxdh.Costed (pqSigAndDdhIface)
open SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Computational.Proofs.SignalPqxdh.AtomicLift

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

/-- One-key `G0 -> G3` hop bound for `sigKeyInd1KeyAtomicAdv` and `shcrKeyInd1KeyAtomicAdv`. -/
theorem keyInd1Key_hop_G0_G3_dsl_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    |KeyInd1KeyRoAdvantageReal S P A.1 - keyInd1KeyAdvG3 S P A.1| ≤
      (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigKeyInd1KeyAtomicAdv S b A) +
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrKeyInd1KeyAtomicAdv S b A) +
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  have hSig : GapSigEufCmaReal P P.isValidDhTriple (sigKeyInd1KeyAtomicAdv S b A) =
      GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1Key S b A) :=
    congrArg ENNReal.toReal (GapSigEufCma_sigKeyInd1KeyAtomicAdv P P.isValidDhTriple S b A)
  have hShcr : KemShCrReal P (shcrKeyInd1KeyAtomicAdv S b A) =
      KemShCrReal P (shcrReductionKeyInd1Key S b A) :=
    congrArg ENNReal.toReal (KemShCr_shcrKeyInd1KeyAtomicAdv P S b A)
  rw [hSig, hShcr]
  exact ki1KeyHopG0G3 S P hP b A

/-- One-key `KeyIndCostedReductionFamily S` combining `sigKeyInd1KeyAtomicProg S` and
    `shcrKeyInd1KeyAtomicProg S` with a `CostedReduction` `GapDhWithSign` program `gdhProg`. -/
def pqxdhKeyInd1KeyCostedFamily (S : Setup)
    (gdhProg : QueryBudget → CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S)
      (pqKeyIndCodec S) (.prod (PB 32) (PB 32)) .unit .bool (PB 32)) :
    KeyIndCostedReductionFamily S where
  sig  := sigKeyInd1KeyAtomicProg S
  shcr := shcrKeyInd1KeyAtomicProg S
  gdh  := gdhProg

/-- Syntactic step-cost, query, and block-size bounds for `pqxdhKeyInd1KeyCostedFamily S gdhProg`
    from the syntactic bounds on `gdhProg`. -/
theorem pqxdhKeyInd1KeyCostedBounds_of_gdh (S : Setup)
    (gdhProg : QueryBudget → CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S)
      (pqKeyIndCodec S) (.prod (PB 32) (PB 32)) .unit .bool (PB 32))
    (hGdhCost : ∀ b, (gdhProg b).totalCost b.q_total ≤ _root_.SignalPqxdh.Security.stepCostBudget S b)
    (hGdhSig : ∀ b, (gdhProg b).totalQueries chalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤
      2 * b.q_total)
    (hGdhDdh : ∀ b, (gdhProg b).totalQueries chalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot)
    (hGdhPrim : ∀ b, (gdhProg b).totalQueries chalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b)
    (hGdhBlocks : ∀ b ℓ, GRedBlockBounded S b ℓ (gdhProg b))
    (hSigK : ∀ (b : QueryBudget),
      (sigKeyInd1KeyAtomicProg S b).CostBoundedByKind
        _root_.SignalPqxdh.Security.keyIndQueryKind
        (_root_.SignalPqxdh.Security.keyIndKindCounts b)
        (_root_.SignalPqxdh.Security.stepCostBudgetSplit S b b.q_ro))
    (hShcrK : ∀ (b : QueryBudget),
      (shcrKeyInd1KeyAtomicProg S b).CostBoundedByKind
        _root_.SignalPqxdh.Security.keyIndQueryKind
        (_root_.SignalPqxdh.Security.keyIndKindCounts b)
        (_root_.SignalPqxdh.Security.stepCostBudgetSplit S b b.q_ro))
    (hGdhK : ∀ (b : QueryBudget),
      (gdhProg b).CostBoundedByKind
        _root_.SignalPqxdh.Security.keyIndQueryKind
        (_root_.SignalPqxdh.Security.keyIndKindCounts b)
        (_root_.SignalPqxdh.Security.stepCostBudgetSplit S b b.q_ro)) :
    KeyIndCostedReductionBounds S (pqxdhKeyInd1KeyCostedFamily S gdhProg) where
  ops_sizeHonest  := pqOpsSizeHonest
  samp_sizeHonest := pqSampSizeHonest
  sig_cost        := sigKeyInd1KeyAtomicProg_totalCost_le_stepCostBudget S
  shcr_cost       := shcrKeyInd1KeyAtomicProg_totalCost_le_stepCostBudget S
  gdh_cost        := hGdhCost
  sig_q_sig       := sigKeyInd1KeyAtomicProg_sigQueries_le S
  sig_q_ddh       := sigKeyInd1KeyAtomicProg_ddhQueries_le S
  sig_q_prim      := sigKeyInd1KeyAtomicProg_primQueries_le S
  shcr_q_prim     := shcrKeyInd1KeyAtomicProg_totalPrimQueries_le S
  gdh_q_sig       := hGdhSig
  gdh_q_ddh       := hGdhDdh
  gdh_q_prim      := hGdhPrim
  sig_blocks      := sigKeyInd1KeyAtomicProg_blocks S
  shcr_blocks     := shcrKeyInd1KeyAtomicProg_blocks S
  gdh_blocks      := hGdhBlocks
  sig_costByKind  := hSigK
  shcr_costByKind := hShcrK
  gdh_costByKind  := hGdhK

/-- Semantic query bounds for `(pqxdhKeyInd1KeyCostedFamily S gdhProg).eval`. -/
theorem pqxdhKeyInd1KeyQueryBounds_of_gdh (S : Setup)
    (gdhProg : QueryBudget → CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S)
      (pqKeyIndCodec S) (.prod (PB 32) (PB 32)) .unit .bool (PB 32))
    (hGdhBounded : ∀ b A, ((pqxdhKeyInd1KeyCostedFamily S gdhProg).eval.gdh b A).Bounded) :
    KeyIndReductionQueryBounds S (pqxdhKeyInd1KeyCostedFamily S gdhProg).eval where
  sig_bounded  := sigKeyInd1KeyAtomicAdv_bounded S
  shcr_bounded := shcrKeyInd1KeyAtomicAdv_bounded S
  gdh_bounded  := hGdhBounded

/-- `PqxdhKeyIndReductionBoundStaticδ` for `(pqxdhKeyInd1KeyCostedFamily S gdhProg).eval` from a
    static `G3` bound on `(pqxdhKeyInd1KeyCostedFamily S gdhProg).eval.gdh`. -/
theorem pqxdhKeyInd1KeySecurityStaticδ_of_gdh (S : Setup)
    (gdhProg : QueryBudget → CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S)
      (pqKeyIndCodec S) (.prod (PB 32) (PB 32)) .unit .bool (PB 32))
    (hG3 : KI1KeyG3BoundStmt S (pqxdhKeyInd1KeyCostedFamily S gdhProg).eval.gdh) :
    PqxdhKeyIndReductionBoundStaticδ S (pqxdhKeyInd1KeyCostedFamily S gdhProg).eval := by
  intro P hP δ hδ b A
  have h := pqxdh_1key_key_ind_withδ_of_hops S
    (pqxdhKeyInd1KeyCostedFamily S gdhProg).eval.gdh
    (ki1KeyHopG0G3 S) hG3 P hP δ hδ b A
  have hSig :
      GapSigEufCma P P.isValidDhTriple ((pqxdhKeyInd1KeyCostedFamily S gdhProg).eval.sig b A) =
        GapSigEufCma P P.isValidDhTriple (sigReductionKeyInd1Key S b A) :=
    GapSigEufCma_sigKeyInd1KeyAtomicAdv P P.isValidDhTriple S b A
  have hShcr :
      KemShCr P ((pqxdhKeyInd1KeyCostedFamily S gdhProg).eval.shcr b A) =
        KemShCr P (shcrReductionKeyInd1Key S b A) :=
    KemShCr_shcrKeyInd1KeyAtomicAdv P S b A
  rw [← hSig, ← hShcr] at h
  exact h

/-- Assembles `PqxdhKeyIndSecureδ S` from an activity-bounded costed reduction family and its
    syntactic, semantic, `G0 -> G3`, and `G3` obligations. -/
theorem pqxdhKeyIndSecureδ_of_activeFamily (S : Setup)
    (R : KeyIndCostedReductionFamily S)
    (hCost : KeyIndCostedReductionBounds S R)
    (hQuery : KeyIndReductionQueryBounds S R.eval)
    (hHop : KI1KeyActiveHopG0G3Stmt S R.eval.sig R.eval.shcr)
    (hG3 : KI1KeyActiveG3BoundStmt S R.eval.gdh) :
    PqxdhKeyIndSecureδ S :=
  ⟨R, hCost, hQuery, pqxdh_1key_key_ind_active_withδ_of_hops S R.eval.sig R.eval.shcr R.eval.gdh hHop hG3⟩

end Proofs.SignalPqxdh.Security.PqxdhDelta
