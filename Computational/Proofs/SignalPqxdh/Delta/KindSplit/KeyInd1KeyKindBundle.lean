/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyCoupling -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.AtomicSizeHonest
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveLengths
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveCollisions
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveSigHop
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveSigEval
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShcrHop
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShcrEval
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhHop
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhLegs
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhLeg4Alt
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhUnion
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhEval
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindShcrBounds
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindSigBounds
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindGapDhBounds
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindSigEq
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindShcrEq
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindGapDhEq

/-!
# One-Key PQXDH δ Key-Indistinguishability Kind-Split Bundle

Assembles `KeyIndCostedReductionBounds`, semantic query bounds, and the active-count `G0 → G3`
and `G3` advantage bounds on the per-query-kind reduction family `pqxdhKeyInd1KeyKindCostedSims S`
to establish `PqxdhKeyIndSecureδ S`.
-/

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindBundle

public section

set_option autoImplicit false

open _root_.SignalPqxdh (Setup QueryBudget activeIdCount activeSpkCount activeOpkCount
  activeSendCount activeSendOpkCount GapDhWithSignReal)
open _root_.SignalPqxdh.Security (stepCostBudget stepCostBudgetSplit primQueryBudget
  GRedBlockBounded keyIndQueryKind keyIndKindCounts chalIfaceSigQueryWeight
  chalIfaceDdhQueryWeight chalIfacePrimQueryWeight samplerZeroQueryWeight
  KeyIndCostedReductionBounds KeyIndReductionQueryBounds PqxdhKeyIndReductionBoundδ
  PqxdhKeyIndSecureδ)
open _root_.Computational.Proofs.ReductionDsl.AtomicSizeHonest
  (pqAtomicOps_sizeHonest pqAtomicSamplers_sizeHonest)
open _root_.Proofs.SignalPqxdh.Security.PqxdhDelta (KI1KeyActiveHopG0G3Stmt
  KI1KeyActiveG3BoundStmt KI1KeyG3BoundStmt
  pqxdh_1key_key_ind_active_withδ_of_hops pqxdhKeyIndSecureδ_of_activeFamily)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs
  (pqxdhKeyInd1KeyActiveCostedSims)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs
  (fgKeyInd1KeyGapDhKindAtomicProg pqxdhKeyInd1KeyKindCostedSims)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindShcrBounds
  (shcrKeyInd1KeyKindAtomicProg_cost shcrKeyInd1KeyKindAtomicProg_q_prim
   shcrKeyInd1KeyKindAtomicProg_blocks shcrKeyInd1KeyKindAtomicProg_costByKind
   shcrKeyInd1KeyKindAtomicProg_bounded)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindSigBounds
  (sigKeyInd1KeyKindAtomicProg_totalCost_le sigKeyInd1KeyKindAtomicProg_q_sig
   sigKeyInd1KeyKindAtomicProg_q_ddh sigKeyInd1KeyKindAtomicProg_q_prim
   sigKeyInd1KeyKindAtomicProg_blocks sigKeyInd1KeyKindAtomicProg_costByKind)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindGapDhBounds
  (fgKeyInd1KeyGapDhKindAtomicProg_totalCost_le fgKeyInd1KeyGapDhKindAtomicProg_q_sig
   fgKeyInd1KeyGapDhKindAtomicProg_q_ddh fgKeyInd1KeyGapDhKindAtomicProg_q_prim
   fgKeyInd1KeyGapDhKindAtomicProg_blocks fgKeyInd1KeyGapDhKindAtomicProg_costByKind)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindSigEq
  (gapSigEufCmaReal_keyInd1KeyKind_eq pqxdhKeyInd1KeyKindCostedSims_sig_bounded)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindShcrEq
  (ki1KeyActiveHopG0G3_of_active)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindGapDhEq
  (ki1KeyActiveG3Bound_of_active pqxdhKeyInd1KeyKindCostedSims_gdh_bounded)

theorem pqxdhKeyInd1KeyKindCostedSims_bounds_of_gdh (S : Setup)
    (hGdhCost : ∀ b : QueryBudget,
      (fgKeyInd1KeyGapDhKindAtomicProg S b).totalCost b.q_total ≤ stepCostBudget S b)
    (hGdhSig : ∀ b : QueryBudget,
      (fgKeyInd1KeyGapDhKindAtomicProg S b).totalQueries
        chalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total)
    (hGdhDdh : ∀ b : QueryBudget,
      (fgKeyInd1KeyGapDhKindAtomicProg S b).totalQueries
        chalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
          4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot)
    (hGdhPrim : ∀ b : QueryBudget,
      (fgKeyInd1KeyGapDhKindAtomicProg S b).totalQueries
        chalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b)
    (hGdhBlocks : ∀ (b : QueryBudget) (ℓ : Nat),
      GRedBlockBounded S b ℓ (fgKeyInd1KeyGapDhKindAtomicProg S b))
    (hGdhCostK : ∀ b : QueryBudget,
      (fgKeyInd1KeyGapDhKindAtomicProg S b).CostBoundedByKind keyIndQueryKind (keyIndKindCounts b)
        (stepCostBudgetSplit S b b.q_ro)) :
    KeyIndCostedReductionBounds S (pqxdhKeyInd1KeyKindCostedSims S) where
  ops_sizeHonest  := pqAtomicOps_sizeHonest
  samp_sizeHonest := pqAtomicSamplers_sizeHonest
  sig_cost        := sigKeyInd1KeyKindAtomicProg_totalCost_le S
  shcr_cost       := shcrKeyInd1KeyKindAtomicProg_cost S
  gdh_cost        := hGdhCost
  sig_q_sig       := sigKeyInd1KeyKindAtomicProg_q_sig S
  sig_q_ddh       := sigKeyInd1KeyKindAtomicProg_q_ddh S
  sig_q_prim      := sigKeyInd1KeyKindAtomicProg_q_prim S
  shcr_q_prim     := shcrKeyInd1KeyKindAtomicProg_q_prim S
  gdh_q_sig       := hGdhSig
  gdh_q_ddh       := hGdhDdh
  gdh_q_prim      := hGdhPrim
  sig_blocks      := sigKeyInd1KeyKindAtomicProg_blocks S
  shcr_blocks     := shcrKeyInd1KeyKindAtomicProg_blocks S
  gdh_blocks      := hGdhBlocks
  sig_costByKind  := sigKeyInd1KeyKindAtomicProg_costByKind S
  shcr_costByKind := shcrKeyInd1KeyKindAtomicProg_costByKind S
  gdh_costByKind  := hGdhCostK

/-- Syntactic step-cost, query, block-size, and per-kind step-cost bounds for `pqxdhKeyInd1KeyKindCostedSims S`. -/
theorem pqxdhKeyInd1KeyKindCostedSims_bounds (S : Setup) :
    KeyIndCostedReductionBounds S (pqxdhKeyInd1KeyKindCostedSims S) :=
  pqxdhKeyInd1KeyKindCostedSims_bounds_of_gdh S
    (fgKeyInd1KeyGapDhKindAtomicProg_totalCost_le S)
    (fgKeyInd1KeyGapDhKindAtomicProg_q_sig S)
    (fgKeyInd1KeyGapDhKindAtomicProg_q_ddh S)
    (fgKeyInd1KeyGapDhKindAtomicProg_q_prim S)
    (fgKeyInd1KeyGapDhKindAtomicProg_blocks S)
    (fgKeyInd1KeyGapDhKindAtomicProg_costByKind S)

theorem pqxdhKeyInd1KeyKindCostedSims_queryBounds_of_active (S : Setup)
    (hAct : KeyIndReductionQueryBounds S (pqxdhKeyInd1KeyActiveCostedSims S).eval) :
    KeyIndReductionQueryBounds S (pqxdhKeyInd1KeyKindCostedSims S).eval where
  sig_bounded  := fun b A => pqxdhKeyInd1KeyKindCostedSims_sig_bounded S b A (hAct.sig_bounded b A)
  shcr_bounded := shcrKeyInd1KeyKindAtomicProg_bounded S
  gdh_bounded  := fun b A => pqxdhKeyInd1KeyKindCostedSims_gdh_bounded S b A (hAct.gdh_bounded b A)

/-- Active-count one-key `G0 → G3` hop bound for `(pqxdhKeyInd1KeyKindCostedSims S).eval`. -/
theorem ki1KeyKindActiveHopG0G3 (S : Setup) :
    KI1KeyActiveHopG0G3Stmt S
      (pqxdhKeyInd1KeyKindCostedSims S).eval.sig
      (pqxdhKeyInd1KeyKindCostedSims S).eval.shcr :=
  ki1KeyActiveHopG0G3_of_active S
    (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShcrHop.ki1KeyActiveHopG0G3_of_active_hops S
      (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveCollisions.keyInd1Key_hop_G0_G0_1_active_le S)
      (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveSigHop.keyInd1Key_hop_G0_1_G2_active_le S)
      (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveCollisions.keyInd1Key_hop_G2_G2_1_active_le S)
      (fun P _ b A =>
        Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveSigEval.gapSigEufCmaReal_sigKeyInd1KeyActiveAtomicProg_eq S P b A)
      (fun P _ b A =>
        Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShcrEval.kemShCrReal_shcrKeyInd1KeyActiveAtomicProg_eq S P b A))
    (fun Prim b A => gapSigEufCmaReal_keyInd1KeyKind_eq Prim S b A)

/-- Active-count one-key `G3` `GapDhWithSign` bound for `(pqxdhKeyInd1KeyKindCostedSims S).eval.gdh`. -/
theorem ki1KeyKindActiveGapDhDsl (S : Setup) :
    KI1KeyActiveG3BoundStmt S (pqxdhKeyInd1KeyKindCostedSims S).eval.gdh :=
  ki1KeyActiveG3Bound_of_active S
    (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhUnion.ki1KeyActiveGapDh_of_four_legs S
      (fun P _ b A x hx =>
        let h := Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveLengths.keyIndActiveLengths_of_runKeyIndFgSim1Key S P b A x hx
        ⟨h.principals_le, h.spkBundles_le, h.opkEntries_le, h.sessions_le, h.sessionsOpk_le⟩)
      (fun P hP b A pOrd hpOrd spkOrd hspkOrd =>
        Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhHop.prob_badKeyIndFgDh1OrdAt_1Key_le_gapDhWithSign_active
          S b P hP A pOrd hpOrd spkOrd hspkOrd)
      (fun P hP b A sOrd hsOrd spkOrd hspkOrd =>
        Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhHop.prob_badKeyIndFgDh3OrdAt_1Key_le_gapDhWithSign_active
          S b P hP A sOrd hsOrd spkOrd hspkOrd)
      (fun P hP b A _sOrd hsOrd _pOrd hpOrd =>
        Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhLegs.prob_badKeyIndFgDh2OrdAt_1Key_le_gapDhWithSign_active
          S P hP b A hsOrd hpOrd)
      (fun P hP b A _sOpkOrd hsOrd _opkOrd hoOrd =>
        Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhLeg4Alt.prob_badKeyIndFgDh4OrdAt_1Key_le_gapDhWithSign_active
          S b P hP A hsOrd hoOrd))

theorem ki1KeyKindGapDhDsl (S : Setup) :
    KI1KeyG3BoundStmt S (pqxdhKeyInd1KeyKindCostedSims S).eval.gdh := by
  intro P hP δ hδ b A
  have hAct := ki1KeyKindActiveGapDhDsl S P hP δ hδ b A
  dsimp only at hAct
  refine hAct.trans ?_
  have hGdh_nonneg :
      0 ≤ GapDhWithSignReal P P.isValidDhTriple P.pow8
            ((pqxdhKeyInd1KeyKindCostedSims S).eval.gdh b A) := by
    unfold GapDhWithSignReal
    exact ENNReal.toReal_nonneg
  have hid : (activeIdCount S b.q_on : ℝ) ≤ S.N_id := by
    unfold activeIdCount; exact_mod_cast Nat.min_le_right b.q_on S.N_id
  have hspk : (activeSpkCount S b.q_on : ℝ) ≤ S.N_spk_tot := by
    unfold activeSpkCount; exact_mod_cast Nat.min_le_right b.q_on S.N_spk_tot
  have hopk : (activeOpkCount S b.q_on : ℝ) ≤ S.N_opk_tot := by
    unfold activeOpkCount; exact_mod_cast Nat.min_le_right b.q_on S.N_opk_tot
  have hsend : (activeSendCount S b.q_on : ℝ) ≤ S.N_send_tot := by
    unfold activeSendCount; exact_mod_cast Nat.min_le_right b.q_on S.N_send_tot
  have hsopk : (activeSendOpkCount S b.q_on : ℝ) ≤ S.N_send_opk_tot := by
    unfold activeSendOpkCount; exact_mod_cast Nat.min_le_right b.q_on S.N_send_opk_tot
  have hPoly :
      (activeSpkCount S b.q_on : ℝ) * ((activeIdCount S b.q_on : ℝ) + (activeSendCount S b.q_on : ℝ)) +
        (activeIdCount S b.q_on : ℝ) * (activeSendCount S b.q_on : ℝ) +
        (activeOpkCount S b.q_on : ℝ) * (activeSendOpkCount S b.q_on : ℝ) ≤
      (S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ) := by
    gcongr
  have hMul := mul_le_mul_of_nonneg_right hPoly hGdh_nonneg
  linarith

theorem pqxdhKeyInd1KeyKindCostedSims_securityδ (S : Setup) :
    PqxdhKeyIndReductionBoundδ S (pqxdhKeyInd1KeyKindCostedSims S).eval :=
  pqxdh_1key_key_ind_active_withδ_of_hops S
    (pqxdhKeyInd1KeyKindCostedSims S).eval.sig
    (pqxdhKeyInd1KeyKindCostedSims S).eval.shcr
    (pqxdhKeyInd1KeyKindCostedSims S).eval.gdh
    (ki1KeyKindActiveHopG0G3 S)
    (ki1KeyKindActiveGapDhDsl S)

/-- Establishes `PqxdhKeyIndSecureδ S` via the kind-split reduction family `pqxdhKeyInd1KeyKindCostedSims S`. -/
theorem pqxdhKeyIndSecureδ_of_kindSplit (S : Setup)
    (hActSim : KeyIndReductionQueryBounds S (pqxdhKeyInd1KeyActiveCostedSims S).eval) :
    PqxdhKeyIndSecureδ S :=
  pqxdhKeyIndSecureδ_of_activeFamily S
    (pqxdhKeyInd1KeyKindCostedSims S)
    (pqxdhKeyInd1KeyKindCostedSims_bounds S)
    (pqxdhKeyInd1KeyKindCostedSims_queryBounds_of_active S hActSim)
    (ki1KeyKindActiveHopG0G3 S)
    (ki1KeyKindActiveGapDhDsl S)

end

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindBundle
