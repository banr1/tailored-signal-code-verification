/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Fig8WeightedParts
public import Computational.Proofs.SessionCostedFig8.Bundles
public import Computational.Proofs.SessionCostedFig8.ProgBounds
public import Computational.Proofs.SessionCostedFig8.DFProgSizeBounds
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedReds2

/-!
# Cost Bounds for Shifted Atomic `DeliverForge` Reductions

Compiles the `ShiftedPaper` and `ShiftedDir2Paper` atomic `DeliverForge` reductions and proves
their `GRedBounded` obligations.
-/
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (HooksExcessBounded cInTransitE_excessUB commitEC_excessUB_le compCostW_le_cost_add_excessUB compExcessUB compExcessUB_bind compExcessUB_caseOpt compExcessUB_caseSum compExcessUB_ite compExcessUB_query compExcessUB_ret compExcessUB_sample exprExcessUB exprExcessUB_add exprExcessUB_and exprExcessUB_anyB exprExcessUB_bool exprExcessUB_caseOpt exprExcessUB_cons exprExcessUB_eqN exprExcessUB_foldrB exprExcessUB_fst exprExcessUB_inl exprExcessUB_inr exprExcessUB_ite exprExcessUB_letE exprExcessUB_lt exprExcessUB_nat exprExcessUB_nil exprExcessUB_none exprExcessUB_not exprExcessUB_op exprExcessUB_pair exprExcessUB_snd exprExcessUB_some exprExcessUB_tconst exprExcessUB_tget exprExcessUB_tset exprExcessUB_unit exprExcessUB_v0 exprExcessUB_v1 exprExcessUB_v2 exprExcessUB_v3 exprExcessUB_v4 hooksFSC_excessBounded hooksPRNGC_excessBounded implEC_excessUB_le initFSEStateC_excessUB_le initPRNGEStateC_excessUB_le modeCfgEC_injectFullE_excessUB optNatLit_excessUB pureEngineExprs_excessUB vRecvC_excessUB_le)
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (HooksCostBounded authOutE_cost_le bits_succ_le cCompContainsE_cost_le cGsSetWin_cost cGsSt_cost cInTransitE_cost_le cRecPos_cost cTrivialE_cost_le commitEC_cost_le esAbort_cost esG_cost esH_cost esSetG_cost esSetH_cost hooksFSC_costBounded_linear hooksPRNGC_costBounded implEC_cost_le initFSEStateC_cost_le initPRNGEStateC_cost_le modeCfgEC_injectFullE_cost_le otherE_cost pGet_cost v0_cost v1_cost v2_cost v3_cost v4_cost vRecvC_cost_le)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (bits_le_add_one compCostW_le_of_parts)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW)
open ReductionDsl (CostedReduction Expr atomicFig8Ops atomicFig8Ops_sizeHonest atomicSamplers_sizeHonest ckaTargetIface fig8SmCodecDF fsaeadHeaderIface prngTargetIface)

@[expose] public section

namespace Computational.Proofs.SessionCostedFig8.DFProgBoundsShifted

set_option autoImplicit false


open OracleSpec OracleComp
open _root_.ReductionDsl (Expr Comp CostedReduction AtomicUnifBase atomicFig8Ops
  atomicFig8Ops_sizeHonest atomicSamplers_sizeHonest fig8SmCodecDF
  ckaTargetIface prngTargetIface fsaeadHeaderIface bits reductionSizeBudget)
open _root_.CryptoGames (Party)
open CryptoGames.CKA (DHFun)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey maxForwardJumps)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (ckaOpC ckaSampC
  ckaQueryC prngQueryC fsQueryC)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (compCostW
  compilePureAuxRed_totalCost_le compilePureAuxRed_totalQueries_le)
open Computational.Proofs.ReductionDsl.MacroLift (guardRed_gRedBounded)
open Computational.Proofs.SessionCostedFig8.ProgBounds (ckaOpMacro_cost_le
  compiled_le_ratchetCostBudget dummy_le_ratchetCostBudget)
open Computational.Proofs.SessionCostedFig8.DFProgSizeBounds
  (redCKAAuthDFShiftedPaperGenProg_size_le redPRNGAuthDFShiftedPaperGenProg_size_le
   redFSAuthDFShiftedPaperGenProg_size_le)

section GenericCkaDFWrappers

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
  (idOf : Party → IdentityKey) (lam : Pt)

set_option maxRecDepth 100000 in
theorem compileCkaDFAtomic_gRedBounded_df (B0 : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (CryptoGames.CKA.ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)) .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW (ckaOpC B0) ckaSampC ckaQueryC R.init +
        compCostW (ckaOpC B0) ckaSampC ckaQueryC R.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B0) ckaSampC ckaQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.finish + 600 ≤
        reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compileCkaDFAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam) (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R (ckaOpC B0) ckaSampC ckaQueryC ?_ ?_ ?_ q).trans
      (compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ ?_ ?_)
    · exact ckaOpMacro_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ B0
    · intro s; cases s <;> simp [Bundles.ckaPureAuxBundle, Bundles.ckaSampMacro, ckaSampC,
        Comp.cost, Expr.cost, AtomicUnifBase.cost]
    · intro g; cases g <;> simp [ckaQueryC, Comp.cost, Expr.cost]
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam; simp only [Expr.cost]; omega
    · simp
    · have h1 := Bundles.fig8AdaptQDF_cost ℓ Pt C Dh encPt encT lam
      have h2 := Bundles.fig8AdaptRDF_cost ℓ Pt C Dh encPt encT lam; simp; omega
  · exact dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R (Bundles.ckaOpS B0) Bundles.ckaSampS
      Bundles.ckaQueryS (Bundles.ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0) ?_ ?_).trans ?_
    · intro s; cases s <;> simp [Bundles.ckaPureAuxBundle, Bundles.ckaSampMacro, Bundles.ckaSampS, Comp.size, Expr.size]
    · intro g; cases g <;> simp [Bundles.ckaQueryS, Comp.size, Expr.size]
    · have hs := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have hq := Bundles.fig8AdaptQDF_size ℓ Pt C Dh encPt encT lam
      have hr := Bundles.fig8AdaptRDF_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]; omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s; cases s <;> simp [Bundles.ckaPureAuxBundle, Bundles.ckaSampMacro, Comp.queries]
    · intro g; cases g <;> simp [Comp.queries]

set_option maxRecDepth 100000 in
theorem compilePrngDFAtomic_gRedBounded_df (B0 : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)) .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW (ckaOpC B0) ckaSampC prngQueryC R.init +
        compCostW (ckaOpC B0) ckaSampC prngQueryC R.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B0) ckaSampC prngQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.finish + 600 ≤
        reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compilePrngDFAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam) (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R (ckaOpC B0) ckaSampC prngQueryC ?_ ?_ ?_ q).trans
      (compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ ?_ ?_)
    · exact ckaOpMacro_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ B0
    · intro s; cases s <;> simp [Bundles.prngPureAuxBundle, Bundles.prngSampMacro, ckaSampC,
        Comp.cost, Expr.cost, AtomicUnifBase.cost]
    · intro g; cases g <;> simp [prngQueryC, Comp.cost, Expr.cost]
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam; simp only [Expr.cost]; omega
    · simp
    · have h1 := Bundles.fig8AdaptQDF_cost ℓ Pt C Dh encPt encT lam
      have h2 := Bundles.fig8AdaptRDF_cost ℓ Pt C Dh encPt encT lam; simp; omega
  · exact dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R (Bundles.ckaOpS B0) Bundles.ckaSampS
      Bundles.ckaQueryS (Bundles.ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0) ?_ ?_).trans ?_
    · intro s; cases s <;> simp [Bundles.prngPureAuxBundle, Bundles.prngSampMacro, Bundles.ckaSampS, Comp.size, Expr.size]
    · intro g; cases g <;> simp [Bundles.ckaQueryS, Comp.size, Expr.size]
    · have hs := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have hq := Bundles.fig8AdaptQDF_size ℓ Pt C Dh encPt encT lam
      have hr := Bundles.fig8AdaptRDF_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]; omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s; cases s <;> simp [Bundles.prngPureAuxBundle, Bundles.prngSampMacro, Comp.queries]
    · intro g; cases g <;> simp [Comp.queries]

set_option maxRecDepth 100000 in
theorem compileFsDFAtomic_gRedBounded_df (B0 : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)) .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW (ckaOpC B0) ckaSampC fsQueryC R.init +
        compCostW (ckaOpC B0) ckaSampC fsQueryC R.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B0) ckaSampC fsQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.finish + 600 ≤
        reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compileFsDFAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam) (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R (ckaOpC B0) ckaSampC fsQueryC ?_ ?_ ?_ q).trans
      (compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ ?_ ?_)
    · exact ckaOpMacro_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ B0
    · intro s; cases s <;> simp [Bundles.fsPureAuxBundle, Bundles.fsSampMacro, ckaSampC,
        Comp.cost, Expr.cost, AtomicUnifBase.cost]
    · intro g; cases g <;> simp [fsQueryC, Comp.cost, Expr.cost] <;> omega
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam; simp only [Expr.cost]; omega
    · simp
    · have h1 := Bundles.fig8AdaptQDF_cost ℓ Pt C Dh encPt encT lam
      have h2 := Bundles.fig8AdaptRDF_cost ℓ Pt C Dh encPt encT lam; simp; omega
  · exact dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R (Bundles.ckaOpS B0) Bundles.ckaSampS
      Bundles.ckaQueryS (Bundles.ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0) ?_ ?_).trans ?_
    · intro s; cases s <;> simp [Bundles.fsPureAuxBundle, Bundles.fsSampMacro, Bundles.ckaSampS, Comp.size, Expr.size]
    · intro g; cases g <;> simp [Bundles.ckaQueryS, Comp.size, Expr.size]
    · have hs := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have hq := Bundles.fig8AdaptQDF_size ℓ Pt C Dh encPt encT lam
      have hr := Bundles.fig8AdaptRDF_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]; omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s; cases s <;> simp [Bundles.fsPureAuxBundle, Bundles.fsSampMacro, Comp.queries]
    · intro g; cases g <;> simp [Comp.queries]

end GenericCkaDFWrappers

section ShiftedEngineParts

open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (compCostW_le_of_parts bits_le_add_one)

private lemma bits_le_bits_qep_add3 {x qep : ℕ} (hx : x ≤ qep + 3) :
    _root_.ReductionDsl.bits x ≤ _root_.ReductionDsl.bits qep + 3 := by
  have h1 := bits_succ_le qep; have hm := _root_.ReductionDsl.bits_mono hx
  have h2 : _root_.ReductionDsl.bits (qep + 2) ≤ _root_.ReductionDsl.bits (qep + 1) + 1 :=
    bits_succ_le (qep + 1)
  have h3 : _root_.ReductionDsl.bits (qep + 3) ≤ _root_.ReductionDsl.bits (qep + 2) + 1 :=
    bits_succ_le (qep + 2); omega

private lemma healEpoch_some_sub_le {l t : ℕ} (hl : l ≤ t) :
    CryptoGames.SM.Construction.healEpoch (some (l - 1)) ≤ t + 2 := by
  simp only [CryptoGames.SM.Construction.healEpoch]; omega

private lemma le_fig8AtomicStepBound_linear {q qep k a b : ℕ}
    (hk : k ≤ 200) (ha : a ≤ 100000) (hb : b ≤ 25000000) :
    k * _root_.ReductionDsl.bits qep + a * (q + 1) + b ≤ fig8AtomicStepBound q qep := by
  unfold fig8AtomicStepBound; dsimp only
  have hk' := Nat.mul_le_mul_right (_root_.ReductionDsl.bits qep) hk
  have ha' := Nat.mul_le_mul_right (q + 1) ha
  generalize _root_.ReductionDsl.bits qep = bq at hk' ⊢
  generalize (q + 1) * (3 * bq + 60) = qbq
  generalize (q + 1) * (maxForwardJumps + 1) = B; generalize q + 1 = L at ha' ⊢; omega

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → CryptoGames.SM.Construction.Header T → M → SS × E}
  {fsReceive : RS → CryptoGames.SM.Construction.Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E} {sampKR : ProbComp KR} {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins} {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S_cka" => CryptoGames.CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" => CryptoGames.CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
  fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

private lemma hdrEqE_cost_le {Γ'}
    (c₁ c₂ : Expr OO_cka Γ' (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    (CryptoGames.SM.Engine.hdrEqE c₁ c₂).cost ≤ c₁.cost + c₂.cost + 40 := by
  have hmax11 : max 1 1 = 1 := rfl; have hmax14 : max 1 4 = 4 := rfl
  simp only [CryptoGames.SM.Engine.hdrEqE, CryptoGames.SM.Engine.optTEqE, CryptoGames.CKA.ckaOps, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, hmax11, hmax14, Nat.reduceAdd]; omega

private lemma deliverForgeEC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : _root_.ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : _root_.ReductionDsl.Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep : ℕ)
    (mo : CryptoGames.SM.Construction.Mode) (hhk : HooksCostBounded hk H) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
      (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    (CryptoGames.SM.Engine.deliverForgeEC hk L 3 qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg).cost ≤
      es.cost + arg.cost + 3 * H + 650 * L +
        _root_.ReductionDsl.bits qep + _root_.ReductionDsl.bits mo.tStar + 5010 := by
  have hqep1 := bits_succ_le qep
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let decT : _root_.ReductionDsl.Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool (.prod hdrCtT hdrCtT)) :: Γ'
  let Γ1 : List (_root_.ReductionDsl.Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (_root_.ReductionDsl.Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v1)) (CryptoGames.SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hcc1 := cCompContainsE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (.fst .v1)) (CryptoGames.SM.Engine.cRecPos .v0)
  have hhe1 := hdrEqE_cost_le (Γ' := Γ1) (.fst (.snd (.snd (ReductionDsl.Expr.v1 (O := OO_cka)))))
    (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ1) (CryptoGames.SM.Engine.esH (.fst .v1))
    (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
  have htr := cTrivialE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ2) (CryptoGames.SM.Engine.esG (.fst .v4))
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ2) (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2))
    (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0)
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := modeCfgEC_injectFullE_cost_le (O' := OO_cka) mo (Γ' := Γ2) (.fst (.snd .v0))
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, cRecPos_cost, otherE_cost,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost, v4_cost, Nat.reduceAdd]
    at hit0 hit1 hcc1 hhe1 hvr htr hcm hij
  simp only [CryptoGames.SM.Engine.deliverForgeEC, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.posEpoch, cRecPos_cost, esG_cost, esAbort_cost, esSetH_cost, esSetG_cost, cGsSetWin_cost,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, Nat.reduceAdd]; omega

private lemma cAfterCorrShiftedE_cost_le_cAfterCorrE {O' : _root_.ReductionDsl.Ops S_cka}
    {vpT : _root_.ReductionDsl.Ty S_cka} (L l : ℕ) {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    (CryptoGames.SM.Engine.cAfterCorrShiftedE L l s p).cost ≤
      (CryptoGames.SM.Engine.cAfterCorrE L s p).cost + 36 * _root_.ReductionDsl.bits l + 650 := by
  have hl1 := _root_.ReductionDsl.bits_mono (Nat.sub_le l 1)
  have hb1 : _root_.ReductionDsl.bits 1 = 1 := rfl
  simp only [CryptoGames.SM.Engine.cAfterCorrShiftedE, CryptoGames.SM.Engine.cAfterCorrE, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cLeakE,
    CryptoGames.SM.maxOptE, CryptoGames.SM.maxN, CryptoGames.SM.leN, CryptoGames.SM.boolEq, CryptoGames.SM.otherE, CryptoGames.SM.pGet, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.posSender,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx,
    CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost, hb1, Nat.reduceAdd]; omega

private lemma leakDoomE_cost_le_add {O' : _root_.ReductionDsl.Ops S_cka}
    {vpT : _root_.ReductionDsl.Ty S_cka} (L : ℕ) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (g g₁ g₂ : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) {d : ℕ} (h : g₁.cost ≤ g₂.cost + d) :
    (CryptoGames.SM.Engine.leakDoomE L π g g₁).cost ≤ (CryptoGames.SM.Engine.leakDoomE L π g g₂).cost + d := by
  simp only [CryptoGames.SM.Engine.leakDoomE, ReductionDsl.Expr.cost]; omega

private lemma corrECShifted_cost_le_corrEC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : _root_.ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : _root_.ReductionDsl.Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (L l : ℕ) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO_cka Γ' .bool) :
    (CryptoGames.SM.Engine.corrECShifted hk L l π es p).cost ≤
      (CryptoGames.SM.Engine.corrEC hk L π es p).cost + 72 * _root_.ReductionDsl.bits l + 1300 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let psT := CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (_root_.ReductionDsl.Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) .bool :: Γ'
  let Γ1 : List (_root_.ReductionDsl.Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ0
  have hac0 := cAfterCorrShiftedE_cost_le_cAfterCorrE (O' := OO_cka) (vpT := vpT) L l (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hld := leakDoomE_cost_le_add (O' := OO_cka) (vpT := vpT) L π (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (.fst .v0))
    (CryptoGames.SM.Engine.cAfterCorrShiftedE L l (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0))
    (CryptoGames.SM.Engine.cAfterCorrE L (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)) (Nat.add_assoc _ _ _ ▸ hac0)
  have hac1 := cAfterCorrShiftedE_cost_le_cAfterCorrE (O' := OO_cka) (vpT := vpT) L l (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (.fst .v2)) (.snd .v2)
  simp only [CryptoGames.SM.Engine.corrECShifted, CryptoGames.SM.Engine.corrEC, CryptoGames.SM.orE, CryptoGames.SM.Engine.esMk,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]; omega

private lemma add_eq_both {a1 a2 b1 b2 : ℕ} (ha : a1 = a2) (hb : b1 = b2) :
    a1 + b1 + 1 = a2 + b2 + 1 := by omega
private lemma max_eq_right {a1 a2 b c1 c2 : ℕ} (ha : a1 = a2) (hc : c1 = c2) :
    a1 + max b c1 + 1 = a2 + max b c2 + 1 := by omega
private lemma cEpMgmtE_cost_2_eq_3 {O' : _root_.ReductionDsl.Ops S_cka}
    {vpT : _root_.ReductionDsl.Ty S_cka} {Γ'} (qep : ℕ)
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p bad : Expr O' Γ' .bool) :
    (CryptoGames.SM.Engine.cEpMgmtE 2 qep s p bad).cost = (CryptoGames.SM.Engine.cEpMgmtE 3 qep s p bad).cost := rfl
private lemma cSafeCh_or_cost_2_eq_3 {O' : _root_.ReductionDsl.Ops S_cka}
    {vpT : _root_.ReductionDsl.Ty S_cka} {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p b : Expr O' Γ' .bool) :
    (CryptoGames.SM.orE (.not (CryptoGames.SM.Engine.cSafeChE 2 s p)) b).cost =
      (CryptoGames.SM.orE (.not (CryptoGames.SM.Engine.cSafeChE 3 s p)) b).cost := rfl
private lemma implEC_cost_arith
    {c d e f g h1 h2 i j m tr2 tr3 ch2 ch3 del inj2 inj3 cr0 cr1 cr2 bl bt : ℕ}
    (htr : tr2 = tr3) (hch : ch2 = ch3) (hij : inj2 ≤ inj3 + (bt + 81))
    (hcr0 : cr0 ≤ cr1) (hcr1 : cr1 ≤ cr2 + 72 * bl + 1300) :
    c + (d + max (e + max (f + max
      (g + max (tr2 + h1 + 1) (ch2 + h2 + 1) + 1) (del + i + 1) + 1)
      (inj2 + j + 1) + 1) (cr0 + m + 1) + 1) + 1 ≤
    c + (d + max (e + max (f + max
      (g + max (tr3 + h1 + 1) (ch3 + h2 + 1) + 1) (del + i + 1) + 1)
      (inj3 + j + 1) + 1) (cr2 + m + 1) + 1) + 1 + 72 * bl + bt + 1400 := by omega

private lemma implECShiftedPaperGen_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : _root_.ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : _root_.ReductionDsl.Ty S_cka}
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L l Δ qep maxSkip tStar : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) (π : CryptoGames.SM.Engine.Policy)
    (hbΔ : (b1 = false ∧ Δ = 3) ∨ (b1 = true ∧ Δ = 2)) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    (CryptoGames.SM.Engine.implECShiftedPaperGen b1 hk L l Δ qep maxSkip tStar cfg π es q).cost ≤
      (CryptoGames.SM.Engine.implEC hk L 3 qep maxSkip cfg π es q).cost +
        72 * _root_.ReductionDsl.bits l + _root_.ReductionDsl.bits tStar + 1400 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let smQ := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let Γ_base := .prod (CryptoGames.SM.Engine.esTy vpT hsT) smQ :: Γ'
  let smQ1 := match smQ with | .sum a _ => a | t => t
  let smQ2 := match smQ1 with | .sum a _ => a | t => t
  let smQ3 := match smQ2 with | .sum a _ => a | t => t
  let trQ := match smQ3 with | .sum a _ => a | t => t
  let chQ := match smQ3 with | .sum _ b => b | t => t
  let ijG := .prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E) :: smQ1 :: Γ_base
  have hcr0 := CryptoGames.SM.Engine.corrECShiftedPaper_cost_le hk L l π (Γ' := .bool :: Γ_base) (.fst .v1) .v0
  have hcr1 := corrECShifted_cost_le_corrEC hk L l π (Γ' := .bool :: Γ_base) (.fst .v1) .v0
  rcases hbΔ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hij : (CryptoGames.SM.Engine.injectECGen false hk L 3 qep tStar cfg (Γ' := ijG) (.fst .v2) .v0).cost ≤
        (CryptoGames.SM.Engine.injectEC hk L 3 qep cfg (Γ' := ijG) (.fst .v2) .v0).cost +
          (_root_.ReductionDsl.bits tStar + 81) := Nat.le_add_right _ _
    dsimp only [CryptoGames.SM.Engine.implECShiftedPaperGen, CryptoGames.SM.Engine.implEC, ReductionDsl.Comp.cost]
    with_reducible exact implEC_cost_arith rfl rfl hij hcr0 hcr1
  · let trG := trQ :: smQ3 :: smQ2 :: smQ1 :: Γ_base
    let chG := chQ :: smQ3 :: smQ2 :: smQ1 :: Γ_base
    have htr : (CryptoGames.SM.Engine.transmitEC hk L 2 qep π (Γ' := trG) (.fst .v4) .v0).cost =
        (CryptoGames.SM.Engine.transmitEC hk L 3 qep π (Γ' := trG) (.fst .v4) .v0).cost := by
      dsimp only [CryptoGames.SM.Engine.transmitEC, ReductionDsl.Comp.cost]
      with_reducible apply add_eq_both rfl
      with_reducible apply max_eq_right rfl
      with_reducible apply max_eq_right (cEpMgmtE_cost_2_eq_3 qep _ _ _)
      with_reducible apply max_eq_right rfl
      with_reducible apply add_eq_both rfl
      with_reducible apply max_eq_right rfl
      rfl
    have hch : (CryptoGames.SM.Engine.challEC hk L 2 qep cfg π (Γ' := chG) (.fst .v4) .v0).cost =
        (CryptoGames.SM.Engine.challEC hk L 3 qep cfg π (Γ' := chG) (.fst .v4) .v0).cost := by
      dsimp only [CryptoGames.SM.Engine.challEC, ReductionDsl.Comp.cost]
      with_reducible apply add_eq_both rfl
      with_reducible apply max_eq_right rfl
      with_reducible apply max_eq_right (cEpMgmtE_cost_2_eq_3 qep _ _ _)
      with_reducible apply max_eq_right (cSafeCh_or_cost_2_eq_3 _ _ _)
      with_reducible apply max_eq_right rfl
      with_reducible apply add_eq_both rfl
      with_reducible apply max_eq_right rfl
      rfl
    have hij : (CryptoGames.SM.Engine.injectECGen true hk L 2 qep tStar cfg (Γ' := ijG) (.fst .v2) .v0).cost ≤
        (CryptoGames.SM.Engine.injectEC hk L 3 qep cfg (Γ' := ijG) (.fst .v2) .v0).cost +
          (_root_.ReductionDsl.bits tStar + 81) :=
      CryptoGames.SM.Engine.injectECB1_cost_le_injectEC hk L qep tStar cfg (Γ' := ijG) (.fst .v2) .v0
    dsimp only [CryptoGames.SM.Engine.implECShiftedPaperGen, CryptoGames.SM.Engine.implEC, ReductionDsl.Comp.cost]
    with_reducible exact implEC_cost_arith htr hch hij hcr0 hcr1

private lemma deliverForgeECGen_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : _root_.ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : _root_.ReductionDsl.Ty S_cka}
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L Δ qep tStar : ℕ)
    (mo : CryptoGames.SM.Construction.Mode) (hhk : HooksCostBounded hk H)
    (hbΔ : (b1 = false ∧ Δ = 3) ∨ (b1 = true ∧ Δ = 2)) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
      (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    (CryptoGames.SM.Engine.deliverForgeECGen b1 hk L Δ qep tStar (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg).cost ≤
      es.cost + arg.cost + 3 * H + 650 * L +
        _root_.ReductionDsl.bits qep + _root_.ReductionDsl.bits mo.tStar +
        _root_.ReductionDsl.bits tStar + 5100 := by
  have hdf := deliverForgeEC_cost_le hk H L qep mo hhk es arg
  rcases hbΔ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [CryptoGames.SM.Engine.deliverForgeECGen, Bool.false_eq_true, ↓reduceIte]; omega
  · have hb := CryptoGames.SM.Engine.deliverForgeECB1_cost_le_deliverForgeEC hk L qep tStar
      (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg
    simp only [CryptoGames.SM.Engine.deliverForgeECGen, ↓reduceIte]; omega

private lemma hdrEqE_excessUB_le (B0 : ℕ) {Γ'}
    (c₁ c₂ : Expr OO_cka Γ' (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprExcessUB (ckaOpC B0) (CryptoGames.SM.Engine.hdrEqE c₁ c₂) ≤
      exprExcessUB (ckaOpC B0) c₁ + exprExcessUB (ckaOpC B0) c₂ + 300 := by
  simp only [CryptoGames.SM.Engine.hdrEqE, CryptoGames.SM.Engine.optTEqE, CryptoGames.CKA.ckaOps, ckaOpC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_bool,
    exprExcessUB_eqN, exprExcessUB_and, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
    exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op,
    Nat.add_zero, Nat.zero_add]
  omega

private lemma deliverForgeECGen_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : _root_.ReductionDsl.Iface S_cka (unifSpec + TSpec)} {B0 : ℕ}
    {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : _root_.ReductionDsl.Ty S_cka}
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L Δ qep tStar : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
      (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.deliverForgeECGen b1 hk L Δ qep tStar (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg) ≤
      60 * (exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) arg) +
        2 * Ho + Hr + 500 * L + 2000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let decT : _root_.ReductionDsl.Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool (.prod hdrCtT hdrCtT)) :: Γ'
  let Γ1 : List (_root_.ReductionDsl.Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (_root_.ReductionDsl.Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_excessUB (vpT := vpT) B0 L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_excessUB (vpT := vpT) B0 L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v1)) (CryptoGames.SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hhe1 := hdrEqE_excessUB_le B0 (Γ' := Γ1)
    (.fst (.snd (.snd (ReductionDsl.Expr.v1 (O := OO_cka))))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_excessUB_le hk Ho Hs Hr hhk (Γ' := Γ1)
    (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
  have hcm := commitEC_excessUB_le hk Ho Hs Hr L hhk (Γ' := Γ2)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0)
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := modeCfgEC_injectFullE_excessUB (O' := OO_cka) (ckaOpC B0) mo (Γ' := Γ2) (.fst (.snd .v0))
  simp only [CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.pGet, CryptoGames.SM.otherE, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2,
    exprExcessUB_v4, exprExcessUB_not, exprExcessUB_ite, exprExcessUB_pair,
    exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_letE,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero] at hit0 hit1 hhe1 hvr hcm hij
  cases b1 <;>
    simp only [CryptoGames.SM.Engine.deliverForgeECGen, CryptoGames.SM.Engine.deliverForgeEC, CryptoGames.SM.Engine.deliverForgeECB1,
      Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cTrivialE,
      CryptoGames.SM.Engine.cTrivialB1E, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort,
      CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt,
      CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
      CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
      CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
      CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.healedByE, CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_unit,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_add,
      exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and,
      exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl,
      exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE,
      exprExcessUB_anyB, exprExcessUB_tget, compExcessUB_ret, compExcessUB_bind,
      compExcessUB_ite, compExcessUB_caseOpt, Nat.add_zero, Nat.zero_add,
      Nat.mul_zero] <;>
    omega

private lemma implECShiftedPaperGen_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : _root_.ReductionDsl.Iface S_cka (unifSpec + TSpec)} {B0 : ℕ}
    {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : _root_.ReductionDsl.Ty S_cka}
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L l Δ qep maxSkip tStar : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (hes : exprExcessUB (ckaOpC B0) es = 0) (hq : exprExcessUB (ckaOpC B0) q = 0) :
    compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.implECShiftedPaperGen b1 hk L l Δ qep maxSkip tStar
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es q) ≤
      7 * Ho + 2 * Hs + 2 * Hr + 300 * L + 40000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let trQ : _root_.ReductionDsl.Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : _root_.ReductionDsl.Ty S_cka :=
    .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : _root_.ReductionDsl.Ty S_cka :=
    .prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
  let Γ_base : List (_root_.ReductionDsl.Ty S_cka) := .prod esT smqT :: Γ'
  let Γ_s1 : List (_root_.ReductionDsl.Ty S_cka) := .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γ_base
  let Γ_s2 : List (_root_.ReductionDsl.Ty S_cka) := .sum (.sum trQ chQ) dlQ :: Γ_s1
  let Γ_s3 : List (_root_.ReductionDsl.Ty S_cka) := .sum trQ chQ :: Γ_s2
  have htr : compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.transmitEC hk L Δ qep mo.policy (Γ' := trQ :: Γ_s3) (.fst .v4) .v0) =
    compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.transmitEC hk L 3 qep mo.policy (Γ' := trQ :: Γ_s3) (.fst .v4) .v0) := rfl
  have hch : compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.challEC hk L Δ qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy
        (Γ' := chQ :: Γ_s3) (.fst .v4) .v0) =
    compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.challEC hk L 3 qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy
        (Γ' := chQ :: Γ_s3) (.fst .v4) .v0) := rfl
  have hcr : compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.corrECShiftedPaper hk L l mo.policy (Γ' := .bool :: Γ_base) (.fst .v1) .v0) =
    compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.corrEC hk L mo.policy (Γ' := .bool :: Γ_base) (.fst .v1) .v0) := by
    simp only [CryptoGames.SM.Engine.corrECShiftedPaper, CryptoGames.SM.Engine.corrEC, CryptoGames.SM.Engine.cCorrAllowedPaperE,
      CryptoGames.SM.Engine.cCorrAllowedE, CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cCompInsertE,
      CryptoGames.SM.Engine.cCompSetE, CryptoGames.SM.Engine.cAfterCorrShiftedE,
      CryptoGames.SM.Engine.cAfterCorrE, CryptoGames.SM.Engine.leakDoomE, CryptoGames.SM.Engine.corrDoomE, CryptoGames.SM.Engine.cLeakE,
      CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetAbort,
      CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
      CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
      CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
      CryptoGames.SM.pGet, CryptoGames.SM.pSet,
      CryptoGames.SM.orE, CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.ltOptE, CryptoGames.SM.boolEq,
      CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, optNatLit_excessUB, exprExcessUB_v0, exprExcessUB_v1,
      exprExcessUB_v2, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
      exprExcessUB_add, exprExcessUB_lt, exprExcessUB_eqN,
      exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_cons,
      exprExcessUB_letE, exprExcessUB_anyB, exprExcessUB_foldrB, exprExcessUB_tget, exprExcessUB_tset, compExcessUB_ret,
      compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, Nat.add_zero, Nat.zero_add,
      Nat.mul_zero]
  have hij : compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.injectECGen b1 hk L Δ qep tStar (CryptoGames.SM.Engine.modeCfgEC OO_cka mo)
        (Γ' := dlQ :: Γ_s1) (.fst .v2) .v0) =
    compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.injectEC hk L 3 qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo)
        (Γ' := dlQ :: Γ_s1) (.fst .v2) .v0) := by
    cases b1 <;>
      simp only [CryptoGames.SM.Engine.injectECGen, CryptoGames.SM.Engine.injectEC, CryptoGames.SM.Engine.injectECB1,
        Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.Engine.cSafeInjE, CryptoGames.SM.Engine.cCompContainsE,
        CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.Engine.cTrivialB1E, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
        CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt,
        CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
        CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
        CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
        CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.minN, CryptoGames.SM.healedByE, CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch,
        CryptoGames.SM.posIdx, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3,
        exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat,
        exprExcessUB_none, exprExcessUB_add, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not,
        exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
        exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt,
        exprExcessUB_letE, exprExcessUB_anyB, exprExcessUB_tget, compExcessUB_ret,
        compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, Nat.add_zero, Nat.zero_add,
        Nat.mul_zero]
  have hEq : compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.implECShiftedPaperGen b1 hk L l Δ qep maxSkip tStar
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es q) =
    compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.implEC hk L 3 qep maxSkip (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es q) := by
    simp only [CryptoGames.SM.Engine.implECShiftedPaperGen, CryptoGames.SM.Engine.implEC, compExcessUB_bind,
      compExcessUB_ret, compExcessUB_caseSum, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_v0, htr, hch, hij, hcr]
  rw [hEq]; have hBase := implEC_excessUB_le hk Ho Hs Hr L qep maxSkip mo hhk es q
  rw [hes, hq] at hBase; omega

set_option maxRecDepth 100000 in
private lemma implECDFShiftedPaperGen_compCostW_le_fig8AtomicStepBound
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : _root_.ReductionDsl.Iface S_cka (unifSpec + TSpec)} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : _root_.ReductionDsl.Ty S_cka}
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (q qep l Δ : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hbΔ : (b1 = false ∧ Δ = 3) ∨ (b1 = true ∧ Δ = 2))
    (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ mo.tStar) (hl : l ≤ mo.tStar)
    (hhkC : HooksCostBounded hk
      (let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
       320 * L + 10 * _root_.ReductionDsl.bits qep + B + 2500))
    (hhkE : HooksExcessBounded ((q + 1) * (maxForwardJumps + 1)) ckaSampC qC hk
      (300 * (q + 1) + 250000) 2000000
      (500 * (q + 1) + 40 * ((q + 1) * (maxForwardJumps + 1)) +
        6 * _root_.ReductionDsl.bits ((q + 1) * (maxForwardJumps + 1)) + 5700000)) :
    compCostW (ckaOpC ((q + 1) * (maxForwardJumps + 1))) ckaSampC qC
      (CryptoGames.SM.Engine.implECDFShiftedPaperGen b1 hk (q + 1) l Δ qep maxForwardJumps mo.tStar
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy
        (Γ' := [CryptoGames.SM.Engine.esTy
          (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
          CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1) + 200000 ≤
      fig8AtomicStepBound q qep := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dfqT : _root_.ReductionDsl.Ty S_cka := .prod .bool (.prod hdrCtT hdrCtT)
  let smqDFT := CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
  let H := 320 * L + 10 * _root_.ReductionDsl.bits qep + B + 2500
  let Ho := 300 * L + 250000; let Hs := 2000000
  let Hr := 500 * L + 40 * B + 6 * _root_.ReductionDsl.bits B + 5700000
  let Γ0 : List (_root_.ReductionDsl.Ty S_cka) := .prod esT smqDFT :: [esT, smqDFT]
  have hmfj : maxForwardJumps ≤ 25000 := le_rfl
  have htStar_bits := bits_le_bits_qep_add3 (x := mo.tStar) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add3 (x := mo.tL.getD 0) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add3 (x := l) (qep := qep) (by omega)
  have hbB := bits_le_add_one B
  have hC1_0 := implECShiftedPaperGen_cost_le b1 hk L l Δ qep maxForwardJumps mo.tStar
    (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy hbΔ (Γ' := smqT :: Γ0) (.fst .v1) .v0
  have hC1_1 := implEC_cost_le hk H L qep maxForwardJumps mo hhkC (Γ' := smqT :: Γ0) (.fst .v1) .v0
  simp only [v0_cost, v1_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hC1_1
  have hmul :
      L * (_root_.ReductionDsl.bits (mo.tL.getD 0) + 2 * _root_.ReductionDsl.bits mo.tStar + 40) ≤
        L * (3 * _root_.ReductionDsl.bits qep + 60) := Nat.mul_le_mul_left L (by omega)
  have hE1 := implECShiftedPaperGen_excessUB_le (B0 := B) b1 hk Ho Hs Hr
    L l Δ qep maxForwardJumps mo.tStar mo hhkE (Γ' := smqT :: Γ0) (.fst .v1) .v0 rfl rfl
  have hW1 := compCostW_le_cost_add_excessUB (ckaOpC B) ckaSampC qC
    (CryptoGames.SM.Engine.implECShiftedPaperGen b1 hk L l Δ qep maxForwardJumps mo.tStar
      (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy (Γ' := smqT :: Γ0) (.fst .v1) .v0)
  have hC2 := deliverForgeECGen_cost_le b1 hk H L Δ qep mo.tStar mo hhkC hbΔ
    (Γ' := dfqT :: Γ0) (.fst .v1) .v0
  simp only [v0_cost, v1_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hC2
  have hE2 := deliverForgeECGen_excessUB_le (B0 := B) b1 hk Ho Hs Hr
    L Δ qep mo.tStar mo hhkE (Γ' := dfqT :: Γ0) (.fst .v1) .v0
  simp only [exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_fst] at hE2
  have hW2 := compCostW_le_cost_add_excessUB (ckaOpC B) ckaSampC qC
    (CryptoGames.SM.Engine.deliverForgeECGen b1 hk L Δ qep mo.tStar
      (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) (Γ' := dfqT :: Γ0) (.fst .v1) .v0)
  have hOuter : compCostW (ckaOpC B) ckaSampC qC
      (CryptoGames.SM.Engine.implECDFShiftedPaperGen b1 hk L l Δ qep maxForwardJumps mo.tStar
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy (Γ' := [esT, smqDFT]) .v0 .v1) ≤
      max (compCostW (ckaOpC B) ckaSampC qC
            (CryptoGames.SM.Engine.implECShiftedPaperGen b1 hk L l Δ qep maxForwardJumps mo.tStar
              (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy (Γ' := smqT :: Γ0) (.fst .v1) .v0))
          (compCostW (ckaOpC B) ckaSampC qC
            (CryptoGames.SM.Engine.deliverForgeECGen b1 hk L Δ qep mo.tStar
              (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) (Γ' := dfqT :: Γ0) (.fst .v1) .v0)) + 20 := by
    dsimp only [CryptoGames.SM.Engine.implECDFShiftedPaperGen, compCostW, exprCostW, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]; omega
  unfold fig8AtomicStepBound
  dsimp only [L, B, H, Ho, Hs, Hr] at hOuter hW1 hW2 hC1_0 hC1_1 hE1 hC2 hE2 hmul hbB ⊢
  generalize _root_.ReductionDsl.bits ((q + 1) * (maxForwardJumps + 1)) = bB at hE1 hE2 hbB
  generalize (q + 1) * (maxForwardJumps + 1) = Bv at hOuter hW1 hW2 hC1_0 hC1_1 hE1 hC2 hE2 hbB ⊢
  generalize (q + 1) * (3 * _root_.ReductionDsl.bits qep + 60) = Lbq at hmul ⊢; omega

local notation "hkCKASh" => @CryptoGames.SM.Construction.hooksCKAShiftedC KC Γ CCoins T I KR RSt K SS RS M E
  ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver
  fsSend fsReceive eqT eqI eqM eqE lam defaultE sampKR sampKC sampCCoins sampI sampK
local notation "hkPRNG" => @CryptoGames.SM.Construction.hooksPRNGC KC Γ CCoins T I KR RSt K SS RS M E
  ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver
  fsSend fsReceive eqT eqI eqM eqE lam defaultE sampKR sampKC sampCCoins sampI sampK
local notation "hkFS" => @CryptoGames.SM.Construction.hooksFSC KC Γ CCoins T I KR RSt K SS RS M E
  ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver
  fsSend fsReceive eqT eqI eqM eqE lam defaultE sampKR sampKC sampCCoins sampI sampK
local notation "initCKAShC" =>
  @CryptoGames.SM.Construction.initCKAShiftedEStateC KC Γ CCoins T I KR RSt K SS RS M E
    ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver
    fsSend fsReceive eqT eqI eqM eqE lam defaultE sampKR sampKC sampCCoins sampI sampK
local notation "initPRNGC_" => @CryptoGames.SM.Construction.initPRNGEStateC KC Γ CCoins T I KR RSt K SS RS M E
  ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver
  fsSend fsReceive eqT eqI eqM eqE lam defaultE sampKR sampKC sampCCoins sampI sampK
local notation "initFSC_" => @CryptoGames.SM.Construction.initFSEStateC KC Γ CCoins T I KR RSt K SS RS M E
  ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver
  fsSend fsReceive eqT eqI eqM eqE lam defaultE sampKR sampKC sampCCoins sampI sampK
local notation "redCKAGenP" =>
  @CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperGenProg KC Γ CCoins T I KR RSt K SS RS M E
    ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver
    fsSend fsReceive eqT eqI eqM eqE lam defaultE sampKR sampKC sampCCoins sampI sampK
local notation "redPRNGGenP" =>
  @CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperGenProg KC Γ CCoins T I KR RSt K SS RS M E
    ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver
    fsSend fsReceive eqT eqI eqM eqE lam defaultE sampKR sampKC sampCCoins sampI sampK
local notation "redFSGenP" =>
  @CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg KC Γ CCoins T I KR RSt K SS RS M E
    ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver
    fsSend fsReceive eqT eqI eqM eqE lam defaultE sampKR sampKC sampCCoins sampI sampK

private lemma hooksCKAShiftedC_costBounded (B l tStar : ℕ) :
    HooksCostBounded (hkCKASh B l tStar)
      (5 * _root_.ReductionDsl.bits l + _root_.ReductionDsl.bits tStar + (B + 1) + 530) where
  startSend_le h ctx p t γv σ r := by
    have hl1 := bits_succ_le l; have hb1 : _root_.ReductionDsl.bits 1 = 1 := rfl
    have hl2 : _root_.ReductionDsl.bits (l + 2) ≤ _root_.ReductionDsl.bits (l + 1) + 1 :=
      bits_succ_le (l + 1)
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC, CryptoGames.SM.Construction.ckaShiftedStartSendC,
      CryptoGames.SM.Construction.ckaShiftedSetCache, CryptoGames.SM.Construction.ckaShiftedSetΓPre, CryptoGames.SM.pSet, CryptoGames.SM.leN,
      CryptoGames.CKA.ckaIface, CryptoGames.CKA.ckaSamplers, CryptoGames.CKA.ckaOps, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
      v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, hb1, Nat.reduceAdd]; omega
  startRecv_le h ctx p t γv σ tn := by
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC, CryptoGames.SM.Construction.ckaShiftedStartRecvC,
      CryptoGames.SM.Construction.ckaStartRecvAnsE, CryptoGames.CKA.ckaOps, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
      v0_cost, v1_cost, v2_cost, Nat.reduceAdd]; omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC, CryptoGames.SM.Construction.ckaShiftedFsSendC, CryptoGames.CKA.ckaOps,
      ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]; omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    have hB := _root_.ReductionDsl.bits_le_succ B
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC, CryptoGames.SM.Construction.ckaShiftedFsRecvC, CryptoGames.CKA.ckaOps,
      ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]; omega
  commit_le h ctx p old new := by
    have hl1 := bits_succ_le l; have hb1 : _root_.ReductionDsl.bits 1 = 1 := rfl
    have hl2 : _root_.ReductionDsl.bits (l + 2) ≤ _root_.ReductionDsl.bits (l + 1) + 1 :=
      bits_succ_le (l + 1)
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC, CryptoGames.SM.Construction.ckaShiftedCommitC,
      CryptoGames.SM.Construction.ckaShiftedSetΓPre, CryptoGames.SM.pSet, CryptoGames.SM.isSomeE, CryptoGames.SM.leN, CryptoGames.SM.Engine.vpTcurNat,
      CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpSetΓ, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId, CryptoGames.SM.Engine.vpRoot,
      CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR, CryptoGames.SM.Engine.vpTcur, CryptoGames.CKA.ckaIface, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
      v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, hb1, Nat.reduceAdd]; omega
  reveal_le h ctx p vp := by
    have hb1 : _root_.ReductionDsl.bits 1 = 1 := rfl
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC, CryptoGames.SM.Construction.ckaShiftedRevealC,
      CryptoGames.SM.Engine.realPartyE, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId, CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS,
      CryptoGames.SM.Engine.vpVR, CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat, CryptoGames.SM.leN, CryptoGames.SM.pGet,
      CryptoGames.CKA.ckaIface, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost, hb1, Nat.reduceAdd]; omega

private lemma hooksCKAShiftedC_excessBounded (B0 B l tStar : ℕ) :
    HooksExcessBounded B0 ckaSampC ckaQueryC (hkCKASh B l tStar)
      5000 400000 (20 * B0 + 3 * _root_.ReductionDsl.bits B + 2710000) where
  startSend_le h ctx p t γv σ r := by
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC, CryptoGames.SM.Construction.ckaShiftedStartSendC,
      CryptoGames.SM.Construction.ckaShiftedSetCache, CryptoGames.SM.Construction.ckaShiftedSetΓPre, CryptoGames.SM.pSet, CryptoGames.SM.leN,
      ckaOpC, ckaSampC, ckaQueryC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2,
      exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_unit, exprExcessUB_nat, exprExcessUB_add,
      exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some,
      exprExcessUB_letE, exprExcessUB_op, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_sample, compExcessUB_query, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]; omega
  startRecv_le h ctx p t γv σ tn := by
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC, CryptoGames.SM.Construction.ckaShiftedStartRecvC,
      CryptoGames.SM.Construction.ckaStartRecvAnsE, ckaOpC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_eqN,
      exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_none, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op,
      exprExcessUB_tget, compExcessUB_ret, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]; omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC, CryptoGames.SM.Construction.ckaShiftedFsSendC, ckaOpC,
      exprExcessUB_pair, exprExcessUB_some, exprExcessUB_op, compExcessUB_ret]; omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC, CryptoGames.SM.Construction.ckaShiftedFsRecvC, ckaOpC,
      exprExcessUB_pair, exprExcessUB_some, exprExcessUB_op, compExcessUB_ret]; omega
  commit_le h ctx p old new := by
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC, CryptoGames.SM.Construction.ckaShiftedCommitC,
      CryptoGames.SM.Construction.ckaShiftedSetΓPre, CryptoGames.SM.pSet, CryptoGames.SM.isSomeE, CryptoGames.SM.leN, CryptoGames.SM.Engine.vpSetΓ,
      CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId, CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR,
      CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat, ckaQueryC, exprExcessUB_v0,
      exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_add, exprExcessUB_lt,
      exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some, exprExcessUB_caseOpt,
      exprExcessUB_letE, compExcessUB_ret, compExcessUB_bind, compExcessUB_ite,
      compExcessUB_caseOpt, compExcessUB_query, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]; omega
  reveal_le h ctx p vp := by
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC, CryptoGames.SM.Construction.ckaShiftedRevealC,
      CryptoGames.SM.Engine.realPartyE, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId, CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS,
      CryptoGames.SM.Engine.vpVR, CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat, CryptoGames.SM.leN, CryptoGames.SM.pGet,
      ckaQueryC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2,
      exprExcessUB_nat, exprExcessUB_add, exprExcessUB_lt,
      exprExcessUB_not, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_none, exprExcessUB_some, exprExcessUB_letE,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_query, Nat.add_zero, Nat.zero_add]; omega

private lemma initCKAShiftedEStateC_cost_le (l : ℕ) {Γ'} (bE : Expr OO_cka Γ' .bool) :
    (initCKAShC l bE).cost ≤ bE.cost + 800 := by
  have hb0 : _root_.ReductionDsl.bits 0 = 1 := rfl
  simp only [CryptoGames.SM.Construction.initCKAShiftedEStateC, CryptoGames.SM.Engine.mkPartiesE, CryptoGames.SM.Engine.cGsInitE,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.esMk, CryptoGames.CKA.ckaIface, CryptoGames.CKA.ckaSamplers, CryptoGames.CKA.ckaOps,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost, hb0, Nat.reduceAdd]; omega

private lemma initCKAShiftedEStateC_excessUB_le (B0 l : ℕ) {Γ'} (bE : Expr OO_cka Γ' .bool) :
    compExcessUB (ckaOpC B0) ckaSampC ckaQueryC (initCKAShC l bE) ≤
      exprExcessUB (ckaOpC B0) bE + 3000 := by
  simp only [CryptoGames.SM.Construction.initCKAShiftedEStateC, CryptoGames.SM.Engine.mkPartiesE, CryptoGames.SM.Engine.cGsInitE,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.vpMk, ckaOpC, ckaSampC, ckaQueryC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_letE,
    exprExcessUB_op, exprExcessUB_tconst, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_sample, compExcessUB_query,
    Nat.reduceAdd, Nat.add_zero, Nat.zero_add]; omega

private lemma hooksFSC_zero_costBounded (L B : ℕ) (mo : CryptoGames.SM.Construction.Mode) (j : ℕ) :
    HooksCostBounded (hkFS L B 0 mo j)
      (300 * L + 20 * (j + 1) + 2 * _root_.ReductionDsl.bits mo.tStar +
        2 * _root_.ReductionDsl.bits mo.tH + (B + 1) + 2110) := by
  have h1 : HooksCostBounded (hkFS L B 1 mo j) _ := hooksFSC_costBounded_linear L B mo j
  refine ⟨h1.startSend_le, h1.startRecv_le, fun h ctx p t ss hdr m pair => ?_,
    h1.fsRecv_le, h1.commit_le, h1.reveal_le⟩
  have hsc : ∀ {O' : _root_.ReductionDsl.Ops S_cka} {Γ''}
      (sE : Expr O' Γ'' (CryptoGames.SM.Engine.cGsTy (CryptoGames.SM.Construction.fsVpTy KC Γ CCoins T I KR RSt K SS RS M E))) pE,
      (CryptoGames.SM.Engine.cSafeChE 2 sE pE).cost = (CryptoGames.SM.Engine.cSafeChE 3 sE pE).cost := fun _ _ => rfl
  have hEq : ((hkFS L B 0 mo j).fsSend h ctx p t ss hdr m pair).cost =
      ((hkFS L B 1 mo j).fsSend h ctx p t ss hdr m pair).cost := by
    unfold CryptoGames.SM.Construction.hooksFSC CryptoGames.SM.Construction.fsFsSendC
    dsimp only [ReductionDsl.Comp.cost, ReductionDsl.Expr.cost, Nat.reduceAdd]; rw [hsc]
  rw [hEq]; exact h1.fsSend_le h ctx p t ss hdr m pair

private lemma hooksFSC_zero_excessBounded (B0 L B : ℕ) (mo : CryptoGames.SM.Construction.Mode) (j : ℕ) :
    HooksExcessBounded B0 ckaSampC fsQueryC (hkFS L B 0 mo j)
      (300 * L + 250000) 2000000 (500 * L + 40 * B0 + 6 * _root_.ReductionDsl.bits B + 5700000) := by
  have h1 : HooksExcessBounded B0 ckaSampC fsQueryC (hkFS L B 1 mo j) _ _ _ :=
    hooksFSC_excessBounded B0 L B mo j
  exact ⟨h1.startSend_le, h1.startRecv_le, h1.fsSend_le, h1.fsRecv_le, h1.commit_le, h1.reveal_le⟩

private lemma authOutE_cost_excess_eq {vpT hsT : _root_.ReductionDsl.Ty S_cka}
    (B0 L Δ : ℕ) (π : CryptoGames.SM.Engine.Policy) (hΔ : Δ = 3 ∨ Δ = 2) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy vpT hsT)) :
    (CryptoGames.SM.Engine.authOutE L Δ π es).cost = (CryptoGames.SM.Engine.authOutE L 3 π es).cost ∧
      exprExcessUB (ckaOpC B0) (CryptoGames.SM.Engine.authOutE L Δ π es) =
        exprExcessUB (ckaOpC B0) (CryptoGames.SM.Engine.authOutE L 3 π es) := by
  rcases hΔ with rfl | rfl <;> exact ⟨rfl, rfl⟩

private lemma redCKAAuthDFShiftedPaperGenProg_parts_le (q qep Δcka l tStarH t : ℕ)
    (hbΔ : (decide (Δcka = 0) = false ∧ 2 + Δcka = 3) ∨ (decide (Δcka = 0) = true ∧ 2 + Δcka = 2))
    (ht : t < qep + 2) (hl : l ≤ t) (htH : tStarH ≤ t) :
    let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
    let P := redCKAGenP L B Δcka qep maxForwardJumps l tStarH t
    compCostW (ckaOpC B) ckaSampC ckaQueryC P.init +
        compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC ckaQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P; let mo : CryptoGames.SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have ht_bits := bits_le_bits_qep_add3 (x := t) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add3 (x := l) (qep := qep) (by omega)
  have hl1_bits := bits_le_bits_qep_add3 (x := l - 1) (qep := qep) (by omega)
  have htSH_bits := bits_le_bits_qep_add3 (x := tStarH) (qep := qep) (by omega)
  have hhkC : HooksCostBounded (hkCKASh B l tStarH) (320 * L + 10 * bits qep + B + 2500) :=
    (hooksCKAShiftedC_costBounded B l tStarH).mono (by omega)
  have hhkE : HooksExcessBounded B ckaSampC ckaQueryC (hkCKASh B l tStarH)
      (300 * L + 250000) 2000000 (500 * L + 40 * B + 6 * bits B + 5700000) :=
    (hooksCKAShiftedC_excessBounded B B l tStarH).mono (by omega) (by decide) (by omega)
  have hΔ23 : 2 + Δcka = 3 ∨ 2 + Δcka = 2 := hbΔ.imp And.right And.right
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC ckaQueryC P.init ≤ 4000 := by
      dsimp only [P, CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperGenProg]
      have hiC : (initCKAShC l (Γ' := [.unit]) (.bool false)).cost ≤ _ := initCKAShiftedEStateC_cost_le l (.bool false)
      have hiE : compExcessUB (ckaOpC B) ckaSampC ckaQueryC (initCKAShC l (Γ' := [.unit]) (.bool false)) ≤ _ :=
        initCKAShiftedEStateC_excessUB_le B l (.bool false)
      refine compCostW_le_of_parts (a := 820) (b := 3010) ?_ ?_ (by decide)
      · simp only [Comp.cost, Expr.cost, v0_cost] at hiC ⊢; omega
      · simp only [compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_unit,
          exprExcessUB_v0, exprExcessUB_bool] at hiE ⊢; omega
    have hf : compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish ≤ 2 * bits qep + 100 * (q + 1) + 500 := by
      dsimp only [P, CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperGenProg]
      obtain ⟨hout_eq, hfE_eq⟩ := authOutE_cost_excess_eq B L (2 + Δcka) mo.policy hΔ23
        (Γ' := [CryptoGames.SM.Construction.ckaShiftedEsTy, .bool]) .v0
      have hfC0 := authOutE_cost_le (O' := OO_cka)
        (vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @CryptoGames.SM.Construction.ckaShiftedHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (Γ' := [CryptoGames.SM.Construction.ckaShiftedEsTy, .bool]) .v0
      have hfE0 := (pureEngineExprs_excessUB (ckaOpC B) L 3 0 mo.policy
        (Γ' := [CryptoGames.SM.Construction.ckaShiftedEsTy, .bool])
        (Expr.v0 (O := OO_cka) (t := CryptoGames.SM.Construction.ckaShiftedEsTy))).1
      dsimp only [mo, CryptoGames.SM.Construction.Mode.policy, Option.getD_some] at hout_eq hfC0 hfE0 hfE_eq ⊢
      refine compCostW_le_of_parts (a := 2 * bits qep + 100 * (q + 1) + 500) (b := 0) ?_ ?_ (by omega)
      · simp only [Comp.cost, v0_cost, hout_eq] at hfC0 ⊢; dsimp only [L] at hfC0 ⊢; omega
      · simp only [compExcessUB_ret, hfE_eq, hfE0, exprExcessUB_v0]; exact le_rfl
    refine (Nat.add_le_add (Nat.add_le_add hi hf) le_rfl).trans ((le_of_eq ?_).trans
      (le_fig8AtomicStepBound_linear (k := 2) (a := 100) (b := 104500) (by decide) (by decide) (by decide))); ring
  · dsimp only [P, L, B, CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperGenProg]
    exact implECDFShiftedPaperGen_compCostW_le_fig8AtomicStepBound
      (decide (Δcka = 0)) _ q qep l (2 + Δcka) mo hbΔ ht (by simp [mo]; omega) hl hhkC hhkE

private lemma redPRNGAuthDFShiftedPaperGenProg_parts_le (q qep Δcka l t : ℕ) (authH : Bool)
    (hbΔ : ((!authH) = false ∧ 2 + Δcka = 3) ∨ ((!authH) = true ∧ 2 + Δcka = 2))
    (ht : t < qep + 2) (hl : l ≤ t) :
    let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
    let P := redPRNGGenP L B Δcka qep maxForwardJumps l t authH
    compCostW (ckaOpC B) ckaSampC prngQueryC P.init +
        compCostW (ckaOpC B) ckaSampC prngQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC prngQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P; let moH : CryptoGames.SM.Construction.Mode := ⟨authH, some (l - 1), t⟩
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have ht_bits := bits_le_bits_qep_add3 (x := t) (qep := qep) (by omega)
  have hl1_bits := bits_le_bits_qep_add3 (x := l - 1) (qep := qep) (by omega)
  have htH_le : moH.tH ≤ qep + 3 := by
    have h1 := healEpoch_some_sub_le hl; cases authH <;> simp only [moH, CryptoGames.SM.Construction.Mode.tH] <;> omega
  have htH_bits := bits_le_bits_qep_add3 (x := moH.tH) (qep := qep) htH_le
  have hhkC : HooksCostBounded (hkPRNG B moH) (320 * L + 10 * bits qep + B + 2500) :=
    (hooksPRNGC_costBounded B moH).mono (by dsimp only [moH] at ht_bits htH_bits ⊢; omega)
  have hhkE : HooksExcessBounded B ckaSampC prngQueryC (hkPRNG B moH)
      (300 * L + 250000) 2000000 (500 * L + 40 * B + 6 * bits B + 5700000) :=
    (hooksPRNGC_excessBounded B B moH).mono (by omega) (by decide) (by omega)
  have hΔ23 : 2 + Δcka = 3 ∨ 2 + Δcka = 2 := hbΔ.imp And.right And.right
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC prngQueryC P.init ≤ 5 * bits qep + 5000 := by
      dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperGenProg, CryptoGames.PRFPRNG.prngOps]
      have hiC : (initPRNGC_ moH (Γ' := [.unit]) (.bool false)).cost ≤ _ := initPRNGEStateC_cost_le moH (.bool false)
      have hiE : compExcessUB (ckaOpC B) ckaSampC prngQueryC (initPRNGC_ moH (Γ' := [.unit]) (.bool false)) ≤ _ :=
        initPRNGEStateC_excessUB_le B moH (.bool false)
      refine compCostW_le_of_parts (a := 5 * bits qep + 1000) (b := 3300) ?_ ?_ (by omega)
      · simp only [Comp.cost, Expr.cost, v0_cost] at hiC ⊢; dsimp only [moH] at ht_bits htH_bits hiC; omega
      · simp only [compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_unit,
          exprExcessUB_v0, exprExcessUB_bool] at hiE ⊢; dsimp only [moH] at hiE; omega
    have hf : compCostW (ckaOpC B) ckaSampC prngQueryC P.finish ≤ 2 * bits qep + 100 * (q + 1) + 500 := by
      dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperGenProg, CryptoGames.PRFPRNG.prngOps]
      obtain ⟨hout_eq, hfE_eq⟩ := authOutE_cost_excess_eq B L (2 + Δcka) mo.policy hΔ23
        (Γ' := [CryptoGames.SM.Construction.prngEsTy, .bool]) .v0
      have hfC0 := authOutE_cost_le (O' := OO_cka)
        (vpT := @CryptoGames.SM.Construction.prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @CryptoGames.SM.Construction.prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (Γ' := [CryptoGames.SM.Construction.prngEsTy, .bool]) .v0
      have hfE0 := (pureEngineExprs_excessUB (ckaOpC B) L 3 0 mo.policy
        (Γ' := [CryptoGames.SM.Construction.prngEsTy, .bool])
        (Expr.v0 (O := OO_cka) (t := CryptoGames.SM.Construction.prngEsTy))).1
      dsimp only [mo, CryptoGames.SM.Construction.Mode.policy, Option.getD_some] at hout_eq hfC0 hfE0 hfE_eq ⊢
      refine compCostW_le_of_parts (a := 2 * bits qep + 100 * (q + 1) + 500) (b := 0) ?_ ?_ (by omega)
      · simp only [Comp.cost, v0_cost, hout_eq] at hfC0 ⊢; dsimp only [L] at hfC0 ⊢; omega
      · simp only [compExcessUB_ret, hfE_eq, hfE0, exprExcessUB_v0]; exact le_rfl
    refine (Nat.add_le_add (Nat.add_le_add hi hf) le_rfl).trans ((le_of_eq ?_).trans
      (le_fig8AtomicStepBound_linear (k := 7) (a := 100) (b := 105500) (by decide) (by decide) (by decide))); ring
  · dsimp only [P, L, B, CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperGenProg, CryptoGames.PRFPRNG.prngOps]
    exact implECDFShiftedPaperGen_compCostW_le_fig8AtomicStepBound
      (!authH) _ q qep l (2 + Δcka) mo hbΔ ht (by simp [mo]; omega) hl hhkC hhkE

private lemma redFSAuthDFShiftedPaperGenProg_parts_le (q qep Δcka j l t : ℕ) (authH : Bool)
    (hbΔ : ((!authH) = false ∧ Δcka = 1) ∨ ((!authH) = true ∧ Δcka = 0))
    (ht : t < qep + 2) (hl : l ≤ t) (hj : j < q) :
    let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
    let P := redFSGenP L B Δcka qep maxForwardJumps j l t authH
    compCostW (ckaOpC B) ckaSampC fsQueryC P.init +
        compCostW (ckaOpC B) ckaSampC fsQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC fsQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P; let moH : CryptoGames.SM.Construction.Mode := ⟨authH, some (l - 1), t⟩
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have ht_bits := bits_le_bits_qep_add3 (x := t) (qep := qep) (by omega)
  have htH_le : moH.tH ≤ qep + 3 := by
    have h1 := healEpoch_some_sub_le hl; cases authH <;> simp only [moH, CryptoGames.SM.Construction.Mode.tH] <;> omega
  have htH_bits := bits_le_bits_qep_add3 (x := moH.tH) (qep := qep) htH_le
  have hjL : j + 1 ≤ L := by omega
  have hhkC : HooksCostBounded (hkFS L B Δcka moH j) (320 * L + 10 * bits qep + B + 2500) := by
    have h20 : 20 * (j + 1) ≤ 20 * L := Nat.mul_le_mul_left 20 hjL
    rcases hbΔ with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact (hooksFSC_costBounded_linear L B moH j).mono (by dsimp only [moH] at ht_bits htH_bits ⊢; omega)
    · exact (hooksFSC_zero_costBounded L B moH j).mono (by dsimp only [moH] at ht_bits htH_bits ⊢; omega)
  have hhkE : HooksExcessBounded B ckaSampC fsQueryC (hkFS L B Δcka moH j)
      (300 * L + 250000) 2000000 (500 * L + 40 * B + 6 * bits B + 5700000) := by
    rcases hbΔ with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hooksFSC_excessBounded B L B moH j
    · exact hooksFSC_zero_excessBounded B L B moH j
  have hbΔ' : ((!authH) = false ∧ 2 + Δcka = 3) ∨ ((!authH) = true ∧ 2 + Δcka = 2) := by
    rcases hbΔ with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> [exact Or.inl ⟨h1, rfl⟩; exact Or.inr ⟨h1, rfl⟩]
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC fsQueryC P.init ≤ 4 * bits qep + 500 * (q + 1) + 8000 := by
      dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg, CryptoGames.PRFPRNG.prngOps]
      have hiC : (initFSC_ L moH j (Γ' := [.unit]) (.bool false)).cost ≤ _ := initFSEStateC_cost_le L moH j (.bool false)
      have hiE : compExcessUB (ckaOpC B) ckaSampC fsQueryC (initFSC_ L moH j (Γ' := [.unit]) (.bool false)) ≤ _ :=
        initFSEStateC_excessUB_le B L moH j (.bool false)
      refine compCostW_le_of_parts (a := 4 * bits qep + 220 * L + 2100) (b := 200 * L + 5100) ?_ ?_ (by dsimp only [L]; omega)
      · have h12 : 12 * (j + 1) ≤ 12 * L := Nat.mul_le_mul_left 12 hjL
        simp only [Comp.cost, Expr.cost, v0_cost] at hiC ⊢; dsimp only [moH] at ht_bits htH_bits hiC; omega
      · simp only [compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_unit,
          exprExcessUB_v0, exprExcessUB_bool] at hiE ⊢; dsimp only [moH] at hiE; omega
    have hf : compCostW (ckaOpC B) ckaSampC fsQueryC P.finish ≤ 300 := by
      dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg, CryptoGames.PRFPRNG.prngOps]
      exact compCostW_le_of_parts (a := 10) (b := 210)
        (by simp only [Comp.cost, Expr.cost]; decide)
        (by simp only [compExcessUB_sample, exprExcessUB_unit, ckaSampC]; decide) (by decide)
    refine (Nat.add_le_add (Nat.add_le_add hi hf) le_rfl).trans ((le_of_eq ?_).trans
      (le_fig8AtomicStepBound_linear (k := 4) (a := 500) (b := 108300) (by decide) (by decide) (by decide))); ring
  · dsimp only [P, L, B, CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg, CryptoGames.PRFPRNG.prngOps]
    exact implECDFShiftedPaperGen_compCostW_le_fig8AtomicStepBound
      (!authH) _ q qep l (2 + Δcka) mo hbΔ' ht (by simp [mo]; omega) hl hhkC hhkE

private lemma redCKAAuthDFShiftedPaperGenProg_totalQueries_le (L B Δcka qep maxSkip l tStarH t q : ℕ) :
    (redCKAGenP L B Δcka qep maxSkip l tStarH t).totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 + 2 * q := by
  dsimp only [CostedReduction.totalQueries, CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperGenProg, Comp.queries]
  rw [CryptoGames.SM.Construction.implECDFShiftedPaper_hooksCKAShiftedC_queries]
  simp only [CryptoGames.SM.Construction.initCKAShiftedEStateC, Comp.queries]
  omega

private lemma redPRNGAuthDFShiftedPaperGenProg_totalQueries_le (L B Δcka qep maxSkip l t : ℕ) (authH : Bool) (q : ℕ) :
    (redPRNGGenP L B Δcka qep maxSkip l t authH).totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 + 2 * q := by
  dsimp only [CostedReduction.totalQueries, CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperGenProg, Comp.queries]
  rw [CryptoGames.SM.Construction.initPRNGEStateC_queries, CryptoGames.SM.Construction.implECDFShiftedPaper_hooksPRNGC_queries]
  omega

private lemma redFSAuthDFShiftedPaperGenProg_totalQueries_le (L B Δcka qep maxSkip j l t : ℕ) (authH : Bool) (q : ℕ) :
    (redFSGenP L B Δcka qep maxSkip j l t authH).totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 * q := by
  dsimp only [CostedReduction.totalQueries, CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg, Comp.queries]
  rw [CryptoGames.SM.Construction.initFSEStateC_queries, CryptoGames.SM.Construction.implECDFShiftedPaper_hooksFSC_queries]
  omega

end ShiftedEngineParts

section ShiftedPaperAtomicProgs

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local instance : Inhabited Pt := ⟨0⟩

def redCKAAuthDFShiftedPaperAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q l t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (ckaTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperProg (q + 1) B0 1 qep maxForwardJumps l t)

def redCKAAuthDFShiftedDir2PaperAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q l t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (ckaTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redCKAAuthDFShiftedDir2PaperProg (q + 1) B0 qep maxForwardJumps l t)

def redPRNGAuthDFShiftedPaperAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q l t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (prngTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperProg (q + 1) B0 1 qep maxForwardJumps l t)

def redPRNGAuthDFShiftedDir2PaperAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q l t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (prngTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redPRNGAuthDFShiftedDir2PaperProg (q + 1) B0 qep maxForwardJumps l t)

def redFSAuthDFShiftedPaperAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q j l t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redFSAuthDFShiftedPaperProg (q + 1) B0 1 qep maxForwardJumps j l t)

def redFSAuthDFShiftedDir2PaperAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q j l t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redFSAuthDFShiftedDir2PaperProg (q + 1) B0 qep maxForwardJumps j l t)

theorem redCKAAuthDFShiftedPaperAtomicProg_gRedBounded (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redCKAAuthDFShiftedPaperAtomicProg Dh encPt C ℓ encT idOf lam qep q l t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redCKAAuthDFShiftedPaperAtomicProg]
  exact compileCkaDFAtomic_gRedBounded_df ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
    (redCKAAuthDFShiftedPaperGenProg_parts_le q qep 1 l t t (Or.inl ⟨rfl, rfl⟩) ht hl le_rfl)
    (redCKAAuthDFShiftedPaperGenProg_size_le q qep 1 l t t (Or.inl rfl) ht hl le_rfl hqep)
    (redCKAAuthDFShiftedPaperGenProg_totalQueries_le _ _ _ _ _ _ _ _ _)

theorem redCKAAuthDFShiftedDir2PaperAtomicProg_gRedBounded (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redCKAAuthDFShiftedDir2PaperAtomicProg Dh encPt C ℓ encT idOf lam qep q l t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redCKAAuthDFShiftedDir2PaperAtomicProg]
  exact compileCkaDFAtomic_gRedBounded_df ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
    (redCKAAuthDFShiftedPaperGenProg_parts_le q qep 0 l 0 t (Or.inr ⟨rfl, rfl⟩) ht hl (Nat.zero_le t))
    (redCKAAuthDFShiftedPaperGenProg_size_le q qep 0 l 0 t (Or.inr rfl) ht hl (Nat.zero_le t) hqep)
    (redCKAAuthDFShiftedPaperGenProg_totalQueries_le _ _ _ _ _ _ _ _ _)

theorem redPRNGAuthDFShiftedPaperAtomicProg_gRedBounded (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redPRNGAuthDFShiftedPaperAtomicProg Dh encPt C ℓ encT idOf lam qep q l t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redPRNGAuthDFShiftedPaperAtomicProg]
  exact compilePrngDFAtomic_gRedBounded_df ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
    (redPRNGAuthDFShiftedPaperGenProg_parts_le q qep 1 l t true (Or.inl ⟨rfl, rfl⟩) ht hl)
    (redPRNGAuthDFShiftedPaperGenProg_size_le q qep 1 l t true (Or.inl rfl) ht hl hqep)
    (redPRNGAuthDFShiftedPaperGenProg_totalQueries_le _ _ _ _ _ _ _ _ _)

theorem redPRNGAuthDFShiftedDir2PaperAtomicProg_gRedBounded (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redPRNGAuthDFShiftedDir2PaperAtomicProg Dh encPt C ℓ encT idOf lam qep q l t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redPRNGAuthDFShiftedDir2PaperAtomicProg]
  exact compilePrngDFAtomic_gRedBounded_df ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
    (redPRNGAuthDFShiftedPaperGenProg_parts_le q qep 0 l t false (Or.inr ⟨rfl, rfl⟩) ht hl)
    (redPRNGAuthDFShiftedPaperGenProg_size_le q qep 0 l t false (Or.inr rfl) ht hl hqep)
    (redPRNGAuthDFShiftedPaperGenProg_totalQueries_le _ _ _ _ _ _ _ _ _)

theorem redFSAuthDFShiftedPaperAtomicProg_gRedBounded (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q j l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t) (hj : j < q)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redFSAuthDFShiftedPaperAtomicProg Dh encPt C ℓ encT idOf lam qep q j l t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redFSAuthDFShiftedPaperAtomicProg]
  exact compileFsDFAtomic_gRedBounded_df ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 * q)
    (redFSAuthDFShiftedPaperGenProg_parts_le q qep 1 j l t true (Or.inl ⟨rfl, rfl⟩) ht hl hj)
    (redFSAuthDFShiftedPaperGenProg_size_le q qep 1 j l t true (Or.inl rfl) ht hl hj hqep)
    (redFSAuthDFShiftedPaperGenProg_totalQueries_le _ _ _ _ _ _ _ _ _ _)

theorem redFSAuthDFShiftedDir2PaperAtomicProg_gRedBounded (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q j l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t) (hj : j < q)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redFSAuthDFShiftedDir2PaperAtomicProg Dh encPt C ℓ encT idOf lam qep q j l t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redFSAuthDFShiftedDir2PaperAtomicProg]
  exact compileFsDFAtomic_gRedBounded_df ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 * q)
    (redFSAuthDFShiftedPaperGenProg_parts_le q qep 0 j l t false (Or.inr ⟨rfl, rfl⟩) ht hl hj)
    (redFSAuthDFShiftedPaperGenProg_size_le q qep 0 j l t false (Or.inr rfl) ht hl hj hqep)
    (redFSAuthDFShiftedPaperGenProg_totalQueries_le _ _ _ _ _ _ _ _ _ _)

end ShiftedPaperAtomicProgs

end Computational.Proofs.SessionCostedFig8.DFProgBoundsShifted
