/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Fig8WeightedParts
public import Computational.Proofs.SessionCostedFig8.Bundles
public import Computational.Proofs.SessionCostedFig8.ProgSizeBounds
public import Computational.Proofs.SessionCostedFig8.ProgBounds
import Computational.Proofs.GameHop.ReductionDsl.CostUB

/-!
# Cost Bounds for Atomic `DeliverForge` Reductions

Proves `GRedBounded` within `ratchetCostBudget` for the compiled atomic `DeliverForge` reductions
(`challSimDFAtomicProg`, `redCKAAuthDFAtomicProg`, `redPRNGAuthDFAtomicProg`, and
`redFSAuthDFAtomicProg`).
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.SessionCostedFig8.DFProgBoundsBase

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface Expr Comp CostedReduction bits reductionSizeBudget
  AtomicUnifBase atomicFig8Ops_sizeHonest atomicSamplers_sizeHonest)
open CryptoGames (Party)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (smOpC smSampC smQueryC ckaOpC ckaSampC
  ckaQueryC prngQueryC fsQueryC)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (compCostW compilePureAuxRed_totalCost_le
  compilePureAuxRed_totalQueries_le)
open Computational.Proofs.ReductionDsl.MacroLift (guardRed_gRedBounded)
open Computational.Proofs.SessionCostedFig8.ProgSizeBounds (HooksSizeBounded
  bits_B0_le_ratchetCostBudget bits_four bits_le_ratchetCostBudget_of_le_linear bits_one
  bits_qep_le_ratchetCostBudget bits_three bits_two bits_zero cInTransitE_sizeW_le
  commitEC_sizeW_le compSizeW_bind compSizeW_caseOpt compSizeW_caseSum compSizeW_ite
  compSizeW_query compSizeW_ret compSizeW_sample exprSizeW_add exprSizeW_and exprSizeW_anyB
  exprSizeW_bool exprSizeW_caseOpt exprSizeW_caseSum exprSizeW_cons exprSizeW_eqN
  exprSizeW_findB exprSizeW_foldrB exprSizeW_fst exprSizeW_inl exprSizeW_inr exprSizeW_ite
  exprSizeW_letE exprSizeW_lt exprSizeW_modK exprSizeW_nat exprSizeW_nil exprSizeW_none
  exprSizeW_not exprSizeW_op exprSizeW_pair exprSizeW_snd exprSizeW_some exprSizeW_sub
  exprSizeW_tconst exprSizeW_tget exprSizeW_tset exprSizeW_unit exprSizeW_v0 exprSizeW_v1
  exprSizeW_v2 exprSizeW_v3 exprSizeW_v4 exprSizeW_v5 exprSizeW_var hooksCKAC_sizeBounded
  hooksFSC_sizeBounded hooksPRNGC_sizeBounded implEC_sizeW_le initCKAEStateC_sizeW_le
  initFSEStateC_sizeW_le initPRNGEStateC_sizeW_le modeCfgEC_injectFullE_sizeW
  pureEngineExprs_sizeW_le size_le_ratchetSizeBudget vRecvC_sizeW_le)

section DFWrappers

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : CryptoGames.LibsignalSession.Crypto) (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
  (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)

local notation "Fig8Msg" =>
  CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ
local notation "Fig8Ct" => ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32
local notation "Fig8DDH" => CryptoGames.CKA.DDH.State (BitVec 256) Pt
local notation "Fig8SS" => CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)
local notation "Fig8RS" => CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)
local notation "Fig8SpecDF" => CryptoGames.SM.specDF
  (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt) Fig8Msg (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)
local notation "Fig8CkaCodecDF" => CryptoGames.CKA.ckaSMCodecDF (BitVec 256) Fig8DDH (BitVec 256)
  Pt Pt (BitVec 256) (BitVec 256) (BitVec 256) Fig8SS Fig8RS Fig8Msg Fig8Ct
local notation "Fig8PrngCodecDF" => CryptoGames.PRFPRNG.prngSMCodecDF (BitVec 256) Fig8DDH
  (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256) Fig8SS Fig8RS Fig8Msg Fig8Ct

set_option maxRecDepth 100000 in
theorem compileSmDFAtomic_gRedBounded
    (R : CostedReduction (Bundles.fig8SmOpsShallow ℓ Pt)
      (CryptoGames.SM.smIfaceDF Unit (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt) Unit Fig8Msg
        (BitVec 256) Unit (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) Fig8SpecDF
      (CryptoGames.SM.smCodecDF Unit (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt) Unit Fig8Msg
        (BitVec 256) Unit (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW smOpC smSampC smQueryC R.init + compCostW smOpC smSampC smQueryC R.finish +
      100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW smOpC smSampC smQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS R.init +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS R.handle +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS R.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compileSmDFAtomic ℓ Pt C Dh encPt encT idOf lam R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compileSmDFAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam) (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R smOpC smSampC smQueryC ?_ ?_ ?_ q).trans
      (ProgBounds.compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ (by simp) ?_)
    · intro o; have := Computational.Proofs.ReductionDsl.Fig8Atomic.eqMExpr_cost ℓ Pt C Dh encPt encT lam
      have := Computational.Proofs.ReductionDsl.Fig8Atomic.smEqCtExpr_cost ℓ Pt C Dh encPt encT lam
      have := Computational.Proofs.ReductionDsl.Fig8Atomic.smBlankExpr_cost ℓ Pt C Dh encPt encT lam
      cases o <;> simp only [Bundles.smDFPureAuxBundle, Bundles.smOpMacro, smOpC, Expr.cost] <;> omega
    · intro s; cases s <;> simp [Bundles.smDFPureAuxBundle, Bundles.smDFSampMacro, smSampC, Comp.cost, Expr.cost]
    · intro g; cases g <;> simp [smQueryC, Comp.cost, Expr.cost] <;> omega
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam; simp only [Expr.cost]; omega
    · have := Bundles.fig8AdaptQDF_cost ℓ Pt C Dh encPt encT lam
      have := Bundles.fig8AdaptRDF_cost ℓ Pt C Dh encPt encT lam; simp; omega
  · exact ProgBounds.dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R Bundles.smOpS Bundles.smSampS Bundles.smQueryS
      (Bundles.smOpMacro_size_le ℓ Pt C Dh encPt encT lam) ?_ ?_).trans ?_
    · intro s; cases s <;> simp [Bundles.smDFPureAuxBundle, Bundles.smDFSampMacro, Bundles.smSampS, Comp.size, Expr.size]
    · intro g; cases g <;> simp [Bundles.smQueryS, Comp.size, Expr.size]
    · have := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have := Bundles.fig8AdaptQDF_size ℓ Pt C Dh encPt encT lam
      have := Bundles.fig8AdaptRDF_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]; omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s; cases s <;> simp [Bundles.smDFPureAuxBundle, Bundles.smDFSampMacro, Comp.queries]
    · intro g; cases g <;> simp [Comp.queries]

set_option maxRecDepth 100000 in
theorem compileCkaDFAtomic_gRedBounded (B0 : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.CKA.ckaIface (BitVec 256) Fig8DDH (BitVec 256) Pt Pt (BitVec 256) (BitVec 256)
        (BitVec 256) Fig8SS Fig8RS Fig8Msg Fig8Ct ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256))
        ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))) Fig8SpecDF Fig8CkaCodecDF .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW (ckaOpC B0) ckaSampC ckaQueryC R.init + compCostW (ckaOpC B0) ckaSampC ckaQueryC R.finish +
      100000 ≤ fig8AtomicStepBound q qep ∧ compCostW (ckaOpC B0) ckaSampC ckaQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compileCkaDFAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam) (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R (ckaOpC B0) ckaSampC ckaQueryC
      (ProgBounds.ckaOpMacro_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ B0) ?_ ?_ q).trans
      (ProgBounds.compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ (by simp) ?_)
    · intro s; cases s <;> simp [Bundles.ckaPureAuxBundle, Bundles.ckaSampMacro, ckaSampC, Comp.cost, Expr.cost, AtomicUnifBase.cost]
    · intro g; cases g <;> simp [ckaQueryC, Comp.cost, Expr.cost]
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam; simp only [Expr.cost]; omega
    · have := Bundles.fig8AdaptQDF_cost ℓ Pt C Dh encPt encT lam
      have := Bundles.fig8AdaptRDF_cost ℓ Pt C Dh encPt encT lam; simp; omega
  · exact ProgBounds.dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R (Bundles.ckaOpS B0) Bundles.ckaSampS
      Bundles.ckaQueryS (Bundles.ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0) ?_ ?_).trans ?_
    · intro s; cases s <;> simp [Bundles.ckaPureAuxBundle, Bundles.ckaSampMacro, Bundles.ckaSampS, Comp.size, Expr.size]
    · intro g; cases g <;> simp [Bundles.ckaQueryS, Comp.size, Expr.size]
    · have := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have := Bundles.fig8AdaptQDF_size ℓ Pt C Dh encPt encT lam
      have := Bundles.fig8AdaptRDF_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]; omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s; cases s <;> simp [Bundles.ckaPureAuxBundle, Bundles.ckaSampMacro, Comp.queries]
    · intro g; cases g <;> simp [Comp.queries]

set_option maxRecDepth 100000 in
theorem compilePrngDFAtomic_gRedBounded (B0 : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.PRFPRNG.prngIface (BitVec 256) Fig8DDH (BitVec 256) Pt Pt (BitVec 256)
        (BitVec 256) (BitVec 256) Fig8SS Fig8RS Fig8Msg Fig8Ct ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256))
        ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))) Fig8SpecDF Fig8PrngCodecDF .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW (ckaOpC B0) ckaSampC prngQueryC R.init + compCostW (ckaOpC B0) ckaSampC prngQueryC R.finish +
      100000 ≤ fig8AtomicStepBound q qep ∧ compCostW (ckaOpC B0) ckaSampC prngQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compilePrngDFAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam) (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R (ckaOpC B0) ckaSampC prngQueryC
      (ProgBounds.ckaOpMacro_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ B0) ?_ ?_ q).trans
      (ProgBounds.compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ (by simp) ?_)
    · intro s; cases s <;> simp [Bundles.prngPureAuxBundle, Bundles.prngSampMacro, ckaSampC, Comp.cost, Expr.cost, AtomicUnifBase.cost]
    · intro g; cases g <;> simp [prngQueryC, Comp.cost, Expr.cost]
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam; simp only [Expr.cost]; omega
    · have := Bundles.fig8AdaptQDF_cost ℓ Pt C Dh encPt encT lam
      have := Bundles.fig8AdaptRDF_cost ℓ Pt C Dh encPt encT lam; simp; omega
  · exact ProgBounds.dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R (Bundles.ckaOpS B0) Bundles.ckaSampS
      Bundles.ckaQueryS (Bundles.ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0) ?_ ?_).trans ?_
    · intro s; cases s <;> simp [Bundles.prngPureAuxBundle, Bundles.prngSampMacro, Bundles.ckaSampS, Comp.size, Expr.size]
    · intro g; cases g <;> simp [Bundles.ckaQueryS, Comp.size, Expr.size]
    · have := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have := Bundles.fig8AdaptQDF_size ℓ Pt C Dh encPt encT lam
      have := Bundles.fig8AdaptRDF_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]; omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s; cases s <;> simp [Bundles.prngPureAuxBundle, Bundles.prngSampMacro, Comp.queries]
    · intro g; cases g <;> simp [Comp.queries]

set_option maxRecDepth 100000 in
theorem compileFsDFAtomic_gRedBounded (B0 : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) Fig8DDH (BitVec 256) Pt Pt (BitVec 256)
        (BitVec 256) (BitVec 256) Fig8SS Fig8RS Fig8Msg Fig8Ct ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256))
        ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))) Fig8SpecDF Fig8PrngCodecDF .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW (ckaOpC B0) ckaSampC fsQueryC R.init + compCostW (ckaOpC B0) ckaSampC fsQueryC R.finish +
      100000 ≤ fig8AtomicStepBound q qep ∧ compCostW (ckaOpC B0) ckaSampC fsQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compileFsDFAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam) (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R (ckaOpC B0) ckaSampC fsQueryC
      (ProgBounds.ckaOpMacro_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ B0) ?_ ?_ q).trans
      (ProgBounds.compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ (by simp) ?_)
    · intro s; cases s <;> simp [Bundles.fsPureAuxBundle, Bundles.fsSampMacro, ckaSampC, Comp.cost, Expr.cost, AtomicUnifBase.cost]
    · intro g; cases g <;> simp [fsQueryC, Comp.cost, Expr.cost] <;> omega
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam; simp only [Expr.cost]; omega
    · have := Bundles.fig8AdaptQDF_cost ℓ Pt C Dh encPt encT lam
      have := Bundles.fig8AdaptRDF_cost ℓ Pt C Dh encPt encT lam; simp; omega
  · exact ProgBounds.dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R (Bundles.ckaOpS B0) Bundles.ckaSampS
      Bundles.ckaQueryS (Bundles.ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0) ?_ ?_).trans ?_
    · intro s; cases s <;> simp [Bundles.fsPureAuxBundle, Bundles.fsSampMacro, Bundles.ckaSampS, Comp.size, Expr.size]
    · intro g; cases g <;> simp [Bundles.ckaQueryS, Comp.size, Expr.size]
    · have := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have := Bundles.fig8AdaptQDF_size ℓ Pt C Dh encPt encT lam
      have := Bundles.fig8AdaptRDF_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]; omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s; cases s <;> simp [Bundles.fsPureAuxBundle, Bundles.fsSampMacro, Comp.queries]
    · intro g; cases g <;> simp [Comp.queries]

end DFWrappers

section DFSMParts

open Computational.Proofs.GameHop.ReductionDsl.CostUB (compCost_le_costUB compCostUB exprCostUB)
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (v0_cost v1_cost bits_succ_le)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (compExcessUB exprExcessUB_v0
  exprExcessUB_v1 exprExcessUB_v2 exprExcessUB_v3 exprExcessUB_v4 exprExcessUB_v5 exprExcessUB_v6
  exprExcessUB_v7 exprExcessUB_var exprExcessUB_unit exprExcessUB_bool exprExcessUB_nat
  exprExcessUB_none exprExcessUB_nil exprExcessUB_add exprExcessUB_sub exprExcessUB_mulK
  exprExcessUB_divK exprExcessUB_modK exprExcessUB_lt exprExcessUB_eqN exprExcessUB_not
  exprExcessUB_and exprExcessUB_ite exprExcessUB_pair exprExcessUB_fst exprExcessUB_snd
  exprExcessUB_inl exprExcessUB_inr exprExcessUB_some exprExcessUB_caseOpt exprExcessUB_caseSum
  exprExcessUB_letE exprExcessUB_op exprExcessUB_cons exprExcessUB_len exprExcessUB_take
  exprExcessUB_appendL exprExcessUB_findB exprExcessUB_anyB exprExcessUB_mapB exprExcessUB_foldrB
  exprExcessUB_tconst exprExcessUB_tget exprExcessUB_tset compExcessUB_ret compExcessUB_bind
  compExcessUB_ite compExcessUB_caseOpt compExcessUB_caseSum compExcessUB_sample
  compExcessUB_query)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (compCostW_le_of_parts)

variable {Key St St₂ Msg Coins RCoins C : Type}
  {init : Party → Key → Option St} {send : St → Msg → Coins → Option (St × C)}
  {receive : St → C → RCoins → Option (St × ℕ × ℕ × Msg)}
  {eqMsg : Msg → Msg → Bool} {eqCt : C → C → Bool} {blank : Msg → Msg}
  {injOK : C → Bool} {stOK : Party → St → Bool} {φ : St → Option St₂}
  {stSort : CryptoGames.SM.SMSort}
  {sampKey : ProbComp (Option Key)} {sampCoins : ProbComp (Option Coins)}
  {sampRCoins : ProbComp (Option RCoins)}

local notation "simInitCDF'" => CryptoGames.SM.simInitCDF (init := init) (send := send)
  (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK)
  (stOK := stOK) (φ := φ) (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
  (sampRCoins := sampRCoins)
local notation "simHandleCDF'" => CryptoGames.SM.simHandleCDF (init := init) (send := send)
  (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK)
  (stOK := stOK) (φ := φ) (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
  (sampRCoins := sampRCoins)
local notation "challSimDFProg'" => CryptoGames.SM.challSimDFProg (init := init) (send := send)
  (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK)
  (stOK := stOK) (φ := φ) (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
  (sampRCoins := sampRCoins)

private theorem simInitCDF_cost_le : (simInitCDF').cost ≤ 200 := by
  have hb0 : bits 0 = 1 := rfl
  refine (compCost_le_costUB _).trans ?_
  simp only [CryptoGames.SM.simInitCDF, CryptoGames.SM.mMk, CryptoGames.SM.smIfaceDF,
    CryptoGames.SM.smSamplers, Expr.v0, hb0, dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]; omega

private theorem simInitCDF_excessUB_le : compExcessUB smOpC smSampC smQueryC simInitCDF' ≤ 500 := by
  simp [CryptoGames.SM.simInitCDF, CryptoGames.SM.mMk, smSampC]

private theorem simHandleCDF_cost_le (K qep : ℕ) :
    (simHandleCDF' K 3 qep).cost ≤ 20 * bits qep + 1800 * K + 17000 := by
  refine (compCost_le_costUB _).trans ?_
  simp only [CryptoGames.SM.simHandleCDF, CryptoGames.SM.simTransmitCDF, CryptoGames.SM.simChallCDF,
    CryptoGames.SM.simDeliverCDF, CryptoGames.SM.simInjectCDF, CryptoGames.SM.simCorrCDF,
    CryptoGames.SM.simDeliverForgeCDF, CryptoGames.SM.mEpMgmtE, CryptoGames.SM.mSafeChE,
    CryptoGames.SM.mLeakE, CryptoGames.SM.mRecordE, CryptoGames.SM.mInTransitE,
    CryptoGames.SM.mDeleteE, CryptoGames.SM.mAcceptE, CryptoGames.SM.mChallContainsE,
    CryptoGames.SM.mAfterCorrE, CryptoGames.SM.mMk, CryptoGames.SM.mSt, CryptoGames.SM.mB,
    CryptoGames.SM.mWin, CryptoGames.SM.mEpoch, CryptoGames.SM.mIdx, CryptoGames.SM.mTL,
    CryptoGames.SM.mTrans, CryptoGames.SM.mChall, CryptoGames.SM.mComp, CryptoGames.SM.mMaxAcc,
    CryptoGames.SM.mLeaks, CryptoGames.SM.mCorrs, CryptoGames.SM.recPos, CryptoGames.SM.recCt,
    CryptoGames.SM.isSomeE, CryptoGames.SM.otherE, CryptoGames.SM.pGet, CryptoGames.SM.pSet,
    CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
    CryptoGames.SM.maxOptE, CryptoGames.SM.maxAccSet, CryptoGames.SM.maxAccGet,
    CryptoGames.SM.posEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    CryptoGames.SM.boolEq, CryptoGames.SM.smOps, CryptoGames.SM.smIfaceDF,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, dsl_cost, Nat.reduceAdd]; omega

private theorem simHandleCDF_excessUB_le (K qep : ℕ) :
    compExcessUB smOpC smSampC smQueryC (simHandleCDF' K 3 qep) ≤ 200 * K + 800000 := by
  simp only [CryptoGames.SM.simHandleCDF, CryptoGames.SM.simTransmitCDF, CryptoGames.SM.simChallCDF,
    CryptoGames.SM.simDeliverCDF, CryptoGames.SM.simInjectCDF, CryptoGames.SM.simCorrCDF,
    CryptoGames.SM.simDeliverForgeCDF, CryptoGames.SM.mEpMgmtE, CryptoGames.SM.mSafeChE,
    CryptoGames.SM.mLeakE, CryptoGames.SM.mRecordE, CryptoGames.SM.mInTransitE,
    CryptoGames.SM.mDeleteE, CryptoGames.SM.mAcceptE, CryptoGames.SM.mChallContainsE,
    CryptoGames.SM.mAfterCorrE, CryptoGames.SM.mMk, CryptoGames.SM.mSt, CryptoGames.SM.mB,
    CryptoGames.SM.mWin, CryptoGames.SM.mEpoch, CryptoGames.SM.mIdx, CryptoGames.SM.mTL,
    CryptoGames.SM.mTrans, CryptoGames.SM.mChall, CryptoGames.SM.mComp, CryptoGames.SM.mMaxAcc,
    CryptoGames.SM.mLeaks, CryptoGames.SM.mCorrs, CryptoGames.SM.recPos, CryptoGames.SM.recCt,
    CryptoGames.SM.isSomeE, CryptoGames.SM.otherE, CryptoGames.SM.pGet, CryptoGames.SM.pSet,
    CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
    CryptoGames.SM.maxOptE, CryptoGames.SM.maxAccSet, CryptoGames.SM.maxAccGet,
    CryptoGames.SM.posEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    CryptoGames.SM.boolEq, smOpC, smQueryC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2,
    exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_v5, exprExcessUB_unit, exprExcessUB_bool,
    exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil, exprExcessUB_add, exprExcessUB_modK,
    exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
    exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op, exprExcessUB_cons,
    exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_foldrB, exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    compExcessUB_caseSum, compExcessUB_query, Nat.reduceAdd, Nat.zero_add, Nat.add_zero, Nat.mul_zero]
  omega

private theorem challSimDFProg_parts_le (q qep : ℕ) :
    let P := challSimDFProg' q 3 qep
    compCostW smOpC smSampC smQueryC P.init + compCostW smOpC smSampC smQueryC P.finish +
        100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW smOpC smSampC smQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro P
  have hi : compCostW smOpC smSampC smQueryC P.init ≤ 700 := by
    dsimp only [P, CryptoGames.SM.challSimDFProg]
    exact compCostW_le_of_parts simInitCDF_cost_le simInitCDF_excessUB_le (by omega)
  have hf : compCostW smOpC smSampC smQueryC P.finish ≤ 20 := by
    dsimp only [P, CryptoGames.SM.challSimDFProg]
    exact compCostW_le_of_parts (a := 10) (b := 0) (by simp only [Comp.cost, v1_cost]; decide)
      (by simp only [compExcessUB_ret, exprExcessUB_v1]; decide) (by omega)
  have hh : compCostW smOpC smSampC smQueryC P.handle ≤ 20 * bits qep + 2000 * q + 1017030 := by
    dsimp only [P, CryptoGames.SM.challSimDFProg]
    exact compCostW_le_of_parts (simHandleCDF_cost_le q qep) (simHandleCDF_excessUB_le q qep) (by omega)
  refine ⟨(Nat.add_le_add_right (Nat.add_le_add hi hf) 100000).trans
    (ProgBounds.const_le_fig8AtomicStepBound (by decide)), (Nat.add_le_add_right hh 200000).trans ?_⟩
  exact (le_of_eq (by ring)).trans (ProgBounds.linear_le_fig8AtomicStepBound (k := 20) (a := 2000)
    (b := 1215030) (q := q) (qep := qep) (by decide) (by decide) (by decide))

set_option linter.unusedSimpArgs false in
private theorem simInitCDF_sizeW_le :
    Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS simInitCDF' ≤ 1000 := by
  simp only [CryptoGames.SM.simInitCDF, CryptoGames.SM.mMk, Bundles.smOpS, Bundles.smSampS,
    Bundles.smQueryS, exprSizeW_v0, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_pair, exprSizeW_tconst, compSizeW_ret, compSizeW_bind,
    compSizeW_sample, bits_zero, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
private theorem simHandleCDF_sizeW_le (K qep : ℕ) :
    Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS (simHandleCDF' K 3 qep) ≤
      50 * bits K + 30 * bits qep + 20000 := by
  have hqep1 := bits_succ_le qep
  simp only [CryptoGames.SM.simHandleCDF, CryptoGames.SM.simTransmitCDF, CryptoGames.SM.simChallCDF,
    CryptoGames.SM.simDeliverCDF, CryptoGames.SM.simInjectCDF, CryptoGames.SM.simCorrCDF,
    CryptoGames.SM.simDeliverForgeCDF, CryptoGames.SM.mEpMgmtE, CryptoGames.SM.mSafeChE,
    CryptoGames.SM.mLeakE, CryptoGames.SM.mRecordE, CryptoGames.SM.mInTransitE,
    CryptoGames.SM.mDeleteE, CryptoGames.SM.mAcceptE, CryptoGames.SM.mChallContainsE,
    CryptoGames.SM.mAfterCorrE, CryptoGames.SM.mMk, CryptoGames.SM.mSt, CryptoGames.SM.mB,
    CryptoGames.SM.mWin, CryptoGames.SM.mEpoch, CryptoGames.SM.mIdx, CryptoGames.SM.mTL,
    CryptoGames.SM.mTrans, CryptoGames.SM.mChall, CryptoGames.SM.mComp, CryptoGames.SM.mMaxAcc,
    CryptoGames.SM.mLeaks, CryptoGames.SM.mCorrs, CryptoGames.SM.recPos, CryptoGames.SM.recCt,
    CryptoGames.SM.isSomeE, CryptoGames.SM.otherE, CryptoGames.SM.pGet, CryptoGames.SM.pSet,
    CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
    CryptoGames.SM.maxOptE, CryptoGames.SM.maxAccSet, CryptoGames.SM.maxAccGet,
    CryptoGames.SM.posEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    CryptoGames.SM.boolEq, Bundles.smOpS, Bundles.smSampS, Bundles.smQueryS, exprSizeW_v0,
    exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, exprSizeW_var,
    exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_add,
    exprSizeW_sub, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and,
    exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr,
    exprSizeW_some, exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op,
    exprSizeW_cons, exprSizeW_findB, exprSizeW_anyB, exprSizeW_foldrB, exprSizeW_tconst,
    exprSizeW_tget, exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    compSizeW_caseSum, compSizeW_query, bits_zero, bits_one, bits_two, bits_three, bits_four,
    Nat.reduceAdd]; omega

set_option maxRecDepth 100000 in
private theorem challSimDFProg_size_le (q qep : ℕ) (hqep : qep ≤ 4096 * q + 100000000) :
    let P := challSimDFProg' q 3 qep
    Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.init +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.handle +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro P
  have hi : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.init ≤ 1000 :=
    simInitCDF_sizeW_le
  have hh : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.handle ≤
      50 * bits q + 30 * bits qep + 20000 := simHandleCDF_sizeW_le q qep
  have hf : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.finish ≤ 20 := by
    dsimp only [P, CryptoGames.SM.challSimDFProg]
    simp only [compSizeW_ret, exprSizeW_v1, Nat.reduceAdd]; omega
  have hbq : bits q ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  refine size_le_ratchetSizeBudget (C₀ := 25000) (C₁ := 80) (by decide) (by decide) ?_; omega

end DFSMParts

section DFEngineParts

open CryptoGames.LibsignalSession (maxForwardJumps)
open CryptoGames.SM.Construction (Header healEpoch)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW)
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (HooksCostBounded bits_succ_le
  bits_le_bits_qep_add cInTransitE_cost_le cCompContainsE_cost_le vRecvC_cost_le
  cTrivialE_cost_le commitEC_cost_le modeCfgEC_injectFullE_cost_le esG_cost esH_cost esSetH_cost
  esSetG_cost esAbort_cost pGet_cost cGsSt_cost cGsSetWin_cost cRecPos_cost otherE_cost
  v0_cost v1_cost v2_cost v3_cost v4_cost implEC_cost_le authOutE_cost_le initCKAEStateC_cost_le
  initPRNGEStateC_cost_le initFSEStateC_cost_le hooksCKAC_costBounded hooksPRNGC_costBounded
  hooksFSC_costBounded hooksFSC_costBounded_linear)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (exprExcessUB compExcessUB
  compCostW_le_cost_add_excessUB HooksExcessBounded cInTransitE_excessUB vRecvC_excessUB_le
  commitEC_excessUB_le modeCfgEC_injectFullE_excessUB implEC_excessUB_le pureEngineExprs_excessUB
  hooksCKAC_excessBounded hooksPRNGC_excessBounded hooksFSC_excessBounded
  initCKAEStateC_excessUB_le initPRNGEStateC_excessUB_le initFSEStateC_excessUB_le
  exprExcessUB_v0 exprExcessUB_v1 exprExcessUB_v2 exprExcessUB_v3 exprExcessUB_v4
  exprExcessUB_unit exprExcessUB_bool exprExcessUB_nat exprExcessUB_none exprExcessUB_add
  exprExcessUB_lt exprExcessUB_eqN exprExcessUB_not exprExcessUB_and exprExcessUB_ite
  exprExcessUB_pair exprExcessUB_fst exprExcessUB_snd exprExcessUB_inl exprExcessUB_inr
  exprExcessUB_some exprExcessUB_caseOpt exprExcessUB_letE exprExcessUB_op exprExcessUB_anyB
  exprExcessUB_tget
  compExcessUB_ret compExcessUB_bind compExcessUB_ite compExcessUB_caseOpt compExcessUB_sample)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (compCostW_le_of_parts bits_le_add_one)

private theorem targetsL_getD_le {Δ t : ℕ} {tL : Option ℕ}
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses Δ t) :
    tL.getD 0 ≤ t := by
  simp only [CryptoGames.SM.admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image,
    Finset.mem_range] at htL
  rcases htL with rfl | ⟨l, hl, rfl⟩
  · simp
  · simp only [Option.getD_some]; omega

private theorem healEpoch_le_of_getD_le {t : ℕ} {tL : Option ℕ} (h : tL.getD 0 ≤ t) :
    healEpoch tL ≤ t + 2 := by
  rcases tL with _ | l <;>
    simp only [Option.getD_none, Option.getD_some, healEpoch] at h ⊢ <;> omega

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S_cka" => CryptoGames.CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  CryptoGames.CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "ckaHdrCtT" => CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E

private theorem hdrEqE_cost_le {Γ'} (c₁ c₂ : Expr OO_cka Γ' ckaHdrCtT) :
    (CryptoGames.SM.Engine.hdrEqE c₁ c₂).cost ≤ c₁.cost + c₂.cost + 40 := by
  have hmax11 : max 1 1 = 1 := rfl; have hmax14 : max 1 4 = 4 := rfl
  simp only [CryptoGames.SM.Engine.hdrEqE, CryptoGames.SM.Engine.optTEqE, CryptoGames.CKA.ckaOps,
    Expr.cost, v0_cost, v1_cost, hmax11, hmax14, Nat.reduceAdd]; omega

private theorem deliverForgeEC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep : ℕ)
    (mo : CryptoGames.SM.Construction.Mode) (hhk : HooksCostBounded hk H)
    {Γ'} (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod ckaHdrCtT ckaHdrCtT))) :
    (CryptoGames.SM.Engine.deliverForgeEC hk L 3 qep
      (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg).cost ≤
      es.cost + arg.cost + 3 * H + 650 * L + bits qep + bits mo.tStar + 5010 := by
  have hqep1 := bits_succ_le qep
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool (.prod ckaHdrCtT ckaHdrCtT)) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v1)) (CryptoGames.SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hcc1 := cCompContainsE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (.fst .v1)) (CryptoGames.SM.Engine.cRecPos .v0)
  have hhe1 := hdrEqE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (Γ' := Γ1) (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ1) (CryptoGames.SM.Engine.esH (.fst .v1))
    (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
  have htr := cTrivialE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ2)
    (CryptoGames.SM.Engine.esG (.fst .v4)) (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ2)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0)
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := modeCfgEC_injectFullE_cost_le (O' := OO_cka) mo (Γ' := Γ2) (.fst (.snd .v0))
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, cRecPos_cost, otherE_cost,
    Expr.cost, v0_cost, v1_cost, v2_cost, v4_cost, Nat.reduceAdd] at hit0 hit1 hcc1 hhe1 hvr htr hcm hij
  simp only [CryptoGames.SM.Engine.deliverForgeEC, CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
    CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esMk, CryptoGames.SM.posEpoch, cRecPos_cost,
    esG_cost, esAbort_cost, esSetH_cost, esSetG_cost, cGsSetWin_cost, Comp.cost, Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, Nat.reduceAdd]; omega

private theorem hdrEqE_excessUB (B0 : ℕ) {Γ'} (c₁ c₂ : Expr OO_cka Γ' ckaHdrCtT) :
    exprExcessUB (ckaOpC B0) (CryptoGames.SM.Engine.hdrEqE c₁ c₂) ≤
      exprExcessUB (ckaOpC B0) c₁ + exprExcessUB (ckaOpC B0) c₂ + 20 := by
  simp only [CryptoGames.SM.Engine.hdrEqE, CryptoGames.SM.Engine.optTEqE, ckaOpC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_bool, exprExcessUB_eqN, exprExcessUB_and,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_caseOpt, exprExcessUB_letE,
    exprExcessUB_op, Nat.add_zero, Nat.zero_add]; omega

private theorem deliverForgeEC_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr L qep : ℕ)
    (mo : CryptoGames.SM.Construction.Mode) (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod ckaHdrCtT ckaHdrCtT))) :
    compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.deliverForgeEC hk L 3 qep
      (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg) ≤
      60 * (exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) arg) +
        2 * Ho + Hr + 300 * L + 1000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool (.prod ckaHdrCtT ckaHdrCtT)) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (.fst .v1)) (CryptoGames.SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hhe1 := hdrEqE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) B0 (Γ' := Γ1)
    (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_excessUB_le hk Ho Hs Hr hhk (Γ' := Γ1) (CryptoGames.SM.Engine.esH (.fst .v1))
    (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
  have hcm := commitEC_excessUB_le hk Ho Hs Hr L hhk (Γ' := Γ2)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0)
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := modeCfgEC_injectFullE_excessUB (O' := OO_cka) (ckaOpC B0) mo (Γ' := Γ2) (.fst (.snd .v0))
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.pGet, CryptoGames.SM.otherE, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2,
    exprExcessUB_v4, exprExcessUB_not, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
    exprExcessUB_snd, exprExcessUB_none, exprExcessUB_letE, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
    at hit0 hit1 hhe1 hvr hcm hij
  simp only [CryptoGames.SM.Engine.deliverForgeEC, CryptoGames.SM.Engine.cCompContainsE,
    CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG,
    CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG,
    CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
    CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.healedByE, CryptoGames.SM.pGet,
    CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE, CryptoGames.SM.leN,
    CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch,
    CryptoGames.SM.posIdx, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3,
    exprExcessUB_v4, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
    exprExcessUB_add, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and,
    exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl,
    exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_anyB,
    exprExcessUB_tget,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega

private theorem exprCostW_v0 {S' : Sig} {O' : Ops S'} (opC : O'.Op → ℕ) {t : Ty S'}
    {Γ' : List (Ty S')} : exprCostW opC (.v0 : Expr O' (t :: Γ') t) = 1 := rfl
private theorem exprCostW_v1 {S' : Sig} {O' : Ops S'} (opC : O'.Op → ℕ) {a t : Ty S'}
    {Γ' : List (Ty S')} : exprCostW opC (.v1 : Expr O' (a :: t :: Γ') t) = 1 := rfl

set_option maxRecDepth 100000 in
private theorem implECDF_compCostW_le_fig8AtomicStepBound {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {qC : I'.Tag → ℕ} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (q qep : ℕ)
    (mo : CryptoGames.SM.Construction.Mode) (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hhkC : HooksCostBounded hk (let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
      320 * L + 10 * bits qep + B + 2500))
    (hhkE : HooksExcessBounded ((q + 1) * (maxForwardJumps + 1)) ckaSampC qC hk
      (300 * (q + 1) + 250000) 2000000
      (500 * (q + 1) + 40 * ((q + 1) * (maxForwardJumps + 1)) +
        6 * bits ((q + 1) * (maxForwardJumps + 1)) + 5700000)) :
    compCostW (ckaOpC ((q + 1) * (maxForwardJumps + 1))) ckaSampC qC
      (CryptoGames.SM.Engine.implECDF
        (Γ' := [CryptoGames.SM.Engine.esTy
          (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
          CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
        hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1) + 200000 ≤
      fig8AtomicStepBound q qep := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
  let H := 320 * L + 10 * bits qep + B + 2500
  let Ho := 300 * L + 250000; let Hs := 2000000; let Hr := 500 * L + 40 * B + 6 * bits B + 5700000
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let dfqT : Ty S_cka := .prod .bool (.prod hdrCtT hdrCtT)
  let smqDFT := CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (Ty S_cka) := .prod esT smqDFT :: [esT, smqDFT]
  let Γ_sm : List (Ty S_cka) := smqT :: Γ0; let Γ_df : List (Ty S_cka) := dfqT :: Γ0
  have hmfj : maxForwardJumps = 25000 := rfl
  have htStar_bits := bits_le_bits_qep_add (x := mo.tStar) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := mo.tL.getD 0) (qep := qep) (by omega)
  have hbB := bits_le_add_one B
  have hC_sm := implEC_cost_le hk H L qep maxForwardJumps mo hhkC (Γ' := Γ_sm) (.fst .v1) .v0
  have hE_sm := implEC_excessUB_le hk Ho Hs Hr L qep maxForwardJumps mo hhkE (Γ' := Γ_sm) (.fst .v1) .v0
  have hW_sm := compCostW_le_cost_add_excessUB (ckaOpC B) ckaSampC qC
    (CryptoGames.SM.Engine.implEC hk L 3 qep maxForwardJumps
      (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy (Γ' := Γ_sm) (.fst .v1) .v0)
  have hC_df := deliverForgeEC_cost_le hk H L qep mo hhkC (Γ' := Γ_df) (.fst .v1) .v0
  have hE_df := deliverForgeEC_excessUB_le hk Ho Hs Hr L qep mo hhkE (Γ' := Γ_df) (.fst .v1) .v0
  have hW_df := compCostW_le_cost_add_excessUB (ckaOpC B) ckaSampC qC
    (CryptoGames.SM.Engine.deliverForgeEC hk L 3 qep
      (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) (Γ' := Γ_df) (.fst .v1) .v0)
  simp only [Expr.cost, v0_cost, v1_cost] at hC_sm hC_df
  simp only [exprExcessUB_fst, exprExcessUB_v0, exprExcessUB_v1] at hE_sm hE_df
  have hmul : L * (bits (mo.tL.getD 0) + 2 * bits mo.tStar + 40) ≤ L * (3 * bits qep + 60) :=
    Nat.mul_le_mul_left L (by omega)
  simp only [CryptoGames.SM.Engine.implECDF, compCostW, exprCostW, exprCostW_v0, exprCostW_v1,
    Nat.reduceAdd]
  unfold fig8AtomicStepBound
  dsimp only [L, B, H, Ho, Hs, Hr] at hC_sm hE_sm hW_sm hC_df hE_df hW_df hmul hbB ⊢
  generalize bits ((q + 1) * (maxForwardJumps + 1)) = bB at hE_sm hE_df hbB
  generalize (q + 1) * (maxForwardJumps + 1) = Bv at hC_sm hE_sm hW_sm hC_df hE_df hW_df hbB ⊢
  generalize (q + 1) * (3 * bits qep + 60) = Lbq at hmul ⊢
  omega

private theorem init_finish_le_step {q qep k1 k2 a1 a2 b1 b2 x y : ℕ}
    (hx : x ≤ k1 * bits qep + a1 * (q + 1) + b1) (hy : y ≤ k2 * bits qep + a2 * (q + 1) + b2)
    (hk : k1 + k2 ≤ 200) (ha : a1 + a2 ≤ 15000) (hb : b1 + b2 + 100000 ≤ 25000000) :
    x + y + 100000 ≤ fig8AtomicStepBound q qep := by
  refine (Nat.add_le_add (Nat.add_le_add hx hy) le_rfl).trans
    ((le_of_eq (by ring)).trans (ProgBounds.linear_le_fig8AtomicStepBound hk ha hb))

private theorem hooksCKA_mono_arith {L B bq bt btH : ℕ} (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4) :
    3 * btH + bt + (B + 1) + 1010 ≤ 320 * L + 10 * bq + B + 2500 := by omega
private theorem hooksPRNG_mono_arith {L B bq bt btH : ℕ} (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4) :
    2 * bt + 3 * btH + (B + 1) + 910 ≤ 320 * L + 10 * bq + B + 2500 := by omega
private theorem hooksFS_mono_arith {L B j bq bt btH : ℕ}
    (hj : j + 1 ≤ L) (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4) :
    300 * L + 20 * (j + 1) + 2 * bt + 2 * btH + (B + 1) + 2110 ≤
      320 * L + 10 * bq + B + 2500 := by omega
private theorem authOut_hm {L bq bt btL c : ℕ}
    (ht : bt ≤ bq + 4) (htL : btL ≤ bq + 4) (hc : c ≤ (btL + 3) + bt + 100 * L + 260) :
    c + 0 ≤ 2 * bq + 100 * L + 500 := by omega
private theorem initPRNG_hm {bq bt btH c e : ℕ}
    (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4) (hc : c ≤ 2 * bt + 3 * btH + 930) (he : e ≤ 3300) :
    c + e ≤ 5 * bq + 0 * 1 + 5000 := by omega
private theorem initFS_hm {L j bq bt btH c e : ℕ}
    (hj : j + 1 ≤ L) (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4)
    (hc : c ≤ 200 * L + 12 * (j + 1) + 2 * bt + 2 * btH + 2030) (he : e ≤ 200 * L + 5100) :
    c + e ≤ 4 * bq + 500 * L + 8000 := by omega
private theorem bind_ret_pair_unit_cost_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {Γ' : List (Ty S')} {σ : Ty S'} {c : Comp O' I' Γ' σ} {K M : ℕ}
    (hc : c.cost ≤ K) (hK : K + 5 ≤ M) : (Comp.bind c (Comp.ret (.pair .unit .v0))).cost ≤ M := by
  simp only [Comp.cost, Expr.cost, v0_cost]; omega
private theorem bind_ret_pair_unit_excess_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} (opC : O'.Op → ℕ) (sampC : I'.smp.Samp → ℕ) (qC : I'.Tag → ℕ)
    {Γ' : List (Ty S')} {σ : Ty S'} {c : Comp O' I' Γ' σ} {K M : ℕ}
    (hc : compExcessUB opC sampC qC c ≤ K) (hK : K ≤ M) :
    compExcessUB opC sampC qC (Comp.bind c (Comp.ret (.pair .unit .v0))) ≤ M := by
  simp only [compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_unit, exprExcessUB_v0]; omega
private theorem comp_ret_cost_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {Γ' : List (Ty S')} {τ : Ty S'} {e : Expr O' Γ' τ} {K M : ℕ}
    (he : e.cost ≤ K) (hM : K + 1 ≤ M) : (Comp.ret (I := I') e).cost ≤ M := by
  simp only [Comp.cost]; omega

local notation "redCKAAuthDFProg'" => CryptoGames.SM.Construction.redCKAAuthDFProg
  (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
  (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
  (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
  (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR)
  (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
local notation "redPRNGAuthDFProg'" => CryptoGames.SM.Construction.redPRNGAuthDFProg
  (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
  (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
  (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
  (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR)
  (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
local notation "redFSAuthDFProg'" => CryptoGames.SM.Construction.redFSAuthDFProg
  (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
  (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
  (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
  (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR)
  (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)

private theorem redCKAAuthDFProg_parts_le (q qep t : ℕ) (tL : Option ℕ) {Δ : ℕ}
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses Δ t) :
    let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1); let P := redCKAAuthDFProg' L B 1 qep maxForwardJumps tL t
    compCostW (ckaOpC B) ckaSampC ckaQueryC P.init + compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish +
      100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC ckaQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P; have htL1 := targetsL_getD_le htL; have htL2 := healEpoch_le_of_getD_le htL1
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hhkC := (hooksCKAC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * bits qep + B + 2500) (hooksCKA_mono_arith ht_bits htH_bits)
  have hhkE := (hooksCKAC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B B mo).mono
    (Ho' := 300 * L + 250000) (Hs' := 2000000) (Hr' := 500 * L + 40 * B + 6 * bits B + 5700000) (by omega) (by decide) (by omega)
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC ckaQueryC P.init ≤ 0 * bits qep + 0 * (q + 1) + 2100 := by
      dsimp only [P, CryptoGames.SM.Construction.redCKAAuthDFProg]
      have hiC0 := initCKAEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) mo (Γ' := [.unit]) (.bool false)
      have hiE0 := initCKAEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B mo (Γ' := [.unit]) (.bool false)
      exact compCostW_le_of_parts (a := 520) (b := 1510)
        (bind_ret_pair_unit_cost_le hiC0 (by simp only [Expr.cost]; decide))
        (bind_ret_pair_unit_excess_le _ _ _ hiE0 (by simp only [exprExcessUB_bool]; decide)) (by simp)
    have hf : compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish ≤ 2 * bits qep + 100 * (q + 1) + 500 := by
      dsimp only [P, CryptoGames.SM.Construction.redCKAAuthDFProg]; rw [show (2 : ℕ) + 1 = 3 from rfl]
      have hfC0 := authOutE_cost_le (O' := OO_cka)
        (vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @CryptoGames.SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (Γ' := [CryptoGames.SM.Construction.ckaEsTy, .bool]) .v0
      have hfE0 := (pureEngineExprs_excessUB (ckaOpC B) L 3 0 mo.policy
        (Γ' := [CryptoGames.SM.Construction.ckaEsTy, .bool]) (Expr.v0 (O := OO_cka) (t := CryptoGames.SM.Construction.ckaEsTy))).1
      dsimp only [mo] at hfE0
      exact compCostW_le_of_parts (a := (bits (tL.getD 0) + 3) + bits t + 100 * L + 260) (b := 0)
        (comp_ret_cost_le hfC0 (by simp only [v0_cost]; dsimp only [mo, CryptoGames.SM.Construction.Mode.policy]; omega))
        (by simp only [compExcessUB_ret, hfE0, exprExcessUB_v0]; exact le_rfl) (authOut_hm ht_bits htL_bits le_rfl)
    exact init_finish_le_step hi hf (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, CryptoGames.SM.Construction.redCKAAuthDFProg]
    exact implECDF_compCostW_le_fig8AtomicStepBound _ q qep mo ht htL1 hhkC hhkE

private theorem redPRNGAuthDFProg_parts_le (q qep t : ℕ) (tL : Option ℕ) {Δ : ℕ}
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses Δ t) :
    let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1); let P := redPRNGAuthDFProg' L B 1 qep maxForwardJumps tL t
    compCostW (ckaOpC B) ckaSampC prngQueryC P.init + compCostW (ckaOpC B) ckaSampC prngQueryC P.finish +
      100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC prngQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P; have htL1 := targetsL_getD_le htL; have htL2 := healEpoch_le_of_getD_le htL1
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hhkC := (hooksPRNGC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * bits qep + B + 2500) (hooksPRNG_mono_arith ht_bits htH_bits)
  have hhkE := (hooksPRNGC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B B mo).mono
    (Ho' := 300 * L + 250000) (Hs' := 2000000) (Hr' := 500 * L + 40 * B + 6 * bits B + 5700000) (by omega) (by decide) (by omega)
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC prngQueryC P.init ≤ 5 * bits qep + 0 * (q + 1) + 5000 := by
      dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFProg]
      have hiC0 := initPRNGEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) mo (Γ' := [.unit]) (.bool false)
      have hiE0 := initPRNGEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B mo (Γ' := [.unit]) (.bool false)
      exact compCostW_le_of_parts (a := 2 * bits t + 3 * bits (healEpoch tL) + 930) (b := 3300)
        (bind_ret_pair_unit_cost_le hiC0 (by simp only [Expr.cost]; dsimp only [mo, CryptoGames.SM.Construction.Mode.tH]; omega))
        (bind_ret_pair_unit_excess_le _ _ _ hiE0 (by simp only [exprExcessUB_bool]; decide))
        ((initPRNG_hm ht_bits htH_bits le_rfl le_rfl).trans (by simp))
    have hf : compCostW (ckaOpC B) ckaSampC prngQueryC P.finish ≤ 2 * bits qep + 100 * (q + 1) + 500 := by
      dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFProg]; rw [show (2 : ℕ) + 1 = 3 from rfl]
      have hfC0 := authOutE_cost_le (O' := OO_cka)
        (vpT := @CryptoGames.SM.Construction.prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @CryptoGames.SM.Construction.prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (Γ' := [CryptoGames.SM.Construction.prngEsTy, .bool]) .v0
      have hfE0 := (pureEngineExprs_excessUB (ckaOpC B) L 3 0 mo.policy
        (Γ' := [CryptoGames.SM.Construction.prngEsTy, .bool]) (Expr.v0 (O := OO_cka) (t := CryptoGames.SM.Construction.prngEsTy))).1
      dsimp only [mo] at hfE0
      exact compCostW_le_of_parts (a := (bits (tL.getD 0) + 3) + bits t + 100 * L + 260) (b := 0)
        (comp_ret_cost_le hfC0 (by simp only [v0_cost]; dsimp only [mo, CryptoGames.SM.Construction.Mode.policy]; omega))
        (by simp only [compExcessUB_ret, hfE0, exprExcessUB_v0]; exact le_rfl) (authOut_hm ht_bits htL_bits le_rfl)
    exact init_finish_le_step hi hf (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, CryptoGames.SM.Construction.redPRNGAuthDFProg]
    exact implECDF_compCostW_le_fig8AtomicStepBound _ q qep mo ht htL1 hhkC hhkE

private theorem redFSAuthDFProg_parts_le (q qep j t : ℕ) (tL : Option ℕ) {Δ : ℕ}
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses Δ t) (hj : j < q) :
    let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1); let P := redFSAuthDFProg' L B 1 qep maxForwardJumps j tL t
    compCostW (ckaOpC B) ckaSampC fsQueryC P.init + compCostW (ckaOpC B) ckaSampC fsQueryC P.finish +
      100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC fsQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P; have htL1 := targetsL_getD_le htL; have htL2 := healEpoch_le_of_getD_le htL1
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hjL : j + 1 ≤ L := by omega
  have hhkC := (hooksFSC_costBounded_linear (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B mo j).mono
    (H' := 320 * L + 10 * bits qep + B + 2500) (hooksFS_mono_arith hjL ht_bits htH_bits)
  have hhkE := hooksFSC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B L B mo j
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC fsQueryC P.init ≤ 4 * bits qep + 500 * (q + 1) + 8000 := by
      dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFProg]
      have hiC0 := initFSEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo j (Γ' := [.unit]) (.bool false)
      have hiE0 := initFSEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B L mo j (Γ' := [.unit]) (.bool false)
      exact compCostW_le_of_parts (a := 200 * L + 12 * (j + 1) + 2 * bits t + 2 * bits (healEpoch tL) + 2030)
        (b := 200 * L + 5100)
        (bind_ret_pair_unit_cost_le hiC0 (by simp only [Expr.cost]; dsimp only [mo, CryptoGames.SM.Construction.Mode.tH]; omega))
        (bind_ret_pair_unit_excess_le _ _ _ hiE0 (by simp only [exprExcessUB_bool]; omega))
        (initFS_hm hjL ht_bits htH_bits le_rfl le_rfl)
    have hf : compCostW (ckaOpC B) ckaSampC fsQueryC P.finish ≤ 0 * bits qep + 0 * (q + 1) + 300 := by
      dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFProg]
      exact compCostW_le_of_parts (a := 10) (b := 210) (by simp only [Comp.cost, Expr.cost]; decide)
        (by simp only [compExcessUB_sample, exprExcessUB_unit, ckaSampC]; decide) (by simp)
    exact init_finish_le_step hi hf (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, CryptoGames.SM.Construction.redFSAuthDFProg]
    exact implECDF_compCostW_le_fig8AtomicStepBound _ q qep mo ht htL1 hhkC hhkE

set_option linter.unusedSimpArgs false in
private theorem hdrEqE_sizeW_le (B0 : ℕ) {Γ'} (c₁ c₂ : Expr OO_cka Γ' ckaHdrCtT) :
    Bundles.exprSizeW (Bundles.ckaOpS B0) (CryptoGames.SM.Engine.hdrEqE c₁ c₂) ≤
      Bundles.exprSizeW (Bundles.ckaOpS B0) c₁ + Bundles.exprSizeW (Bundles.ckaOpS B0) c₂ + 400 := by
  simp only [CryptoGames.SM.Engine.hdrEqE, CryptoGames.SM.Engine.optTEqE, CryptoGames.CKA.ckaOps,
    Bundles.ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_eqN,
    exprSizeW_and, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE,
    exprSizeW_op, Nat.reduceAdd]; omega

private theorem modeCfgEC_injectFullE_sizeW_le {O' : Ops S_cka} (opS : O'.Op → ℕ)
    (mo : CryptoGames.SM.Construction.Mode) {Γ'} (e : Expr O' Γ' .nat) :
    Bundles.exprSizeW opS ((CryptoGames.SM.Engine.modeCfgEC O' mo).injectFullE e) ≤
      Bundles.exprSizeW opS e + bits mo.tStar + 1 := by
  rw [modeCfgEC_injectFullE_sizeW]; split_ifs <;> omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
private theorem deliverForgeEC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr L qep : ℕ)
    (mo : CryptoGames.SM.Construction.Mode) (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod ckaHdrCtT ckaHdrCtT))) :
    Bundles.compSizeW (Bundles.ckaOpS B0) sS qS
      (CryptoGames.SM.Engine.deliverForgeEC hk L 3 qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg) ≤
      10 * (Bundles.exprSizeW (Bundles.ckaOpS B0) es + Bundles.exprSizeW (Bundles.ckaOpS B0) arg) +
        2 * Ho + Hr + 20 * bits L + 5 * bits qep + 5 * bits mo.tStar + 10000 := by
  have hqep1 := bits_succ_le qep
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool (.prod ckaHdrCtT ckaHdrCtT)) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (.fst .v1)) (CryptoGames.SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hhe1 := hdrEqE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) B0
    (Γ' := Γ1) (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_sizeW_le hk Ho Hs Hr hhk (Γ' := Γ1) (CryptoGames.SM.Engine.esH (.fst .v1))
    (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
  have hcm := commitEC_sizeW_le hk Ho Hs Hr L hhk (Γ' := Γ2)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := modeCfgEC_injectFullE_sizeW_le (O' := OO_cka) (Bundles.ckaOpS B0) mo (Γ' := Γ2) (.fst (.snd .v0))
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.pGet, CryptoGames.SM.otherE, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
    exprSizeW_v4, exprSizeW_var, exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_none, exprSizeW_letE, Nat.reduceAdd] at hit0 hit1 hhe1 hvr hcm hij
  simp only [CryptoGames.SM.Engine.deliverForgeEC, CryptoGames.SM.Engine.cCompContainsE,
    CryptoGames.SM.Engine.cChallContainsE, CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort,
    CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsMk,
    CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB,
    CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx,
    CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall,
    CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks,
    CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.healedByE,
    CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE,
    CryptoGames.SM.leN, CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender,
    CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, Bundles.ckaOpS, exprSizeW_v0, exprSizeW_v1,
    exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, exprSizeW_var, exprSizeW_unit,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub,
    exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some,
    exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_cons,
    exprSizeW_findB, exprSizeW_anyB, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget,
    exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    compSizeW_caseSum, bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
private theorem implECDF_sizeW_le_ratchet {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (q qep : ℕ)
    (mo : CryptoGames.SM.Construction.Mode) (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hqep : qep ≤ 4096 * q + 100000000)
    (hhk : HooksSizeBounded ((q + 1) * (maxForwardJumps + 1)) sS qS hk
      (80 * bits (ratchetCostBudget q qep) + 15000) 2000 (14 * bits (ratchetCostBudget q qep) + 5000)) :
    Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1))) sS qS
      (CryptoGames.SM.Engine.implECDF (Γ' := [CryptoGames.SM.Engine.esTy
        (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
        CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
        hk (q + 1) (2 + 1) qep maxForwardJumps (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1) ≤
      1000 * bits (ratchetCostBudget q qep) + 250000 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := CryptoGames.SM.Engine.esTy vpT hsT; let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let smqDFT := CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E; let Γ0 : List (Ty S_cka) := .prod esT smqDFT :: [esT, smqDFT]
  let Ho := 80 * bits (ratchetCostBudget q qep) + 15000; let Hr := 14 * bits (ratchetCostBudget q qep) + 5000
  have h_sm := implEC_sizeW_le hk Ho 2000 Hr (q + 1) qep maxForwardJumps mo hhk (Γ' := smqT :: Γ0) (.fst .v1) .v0
  have h_df := deliverForgeEC_sizeW_le hk Ho 2000 Hr (q + 1) qep mo hhk (Γ' := .prod .bool (.prod hdrCtT hdrCtT) :: Γ0) (.fst .v1) .v0
  simp only [exprSizeW_fst, exprSizeW_v0, exprSizeW_v1, exprSizeW_var, Nat.reduceAdd] at h_sm h_df
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  have hbm : bits maxForwardJumps ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by unfold maxForwardJumps; omega)
  have hbtS : bits mo.tStar ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (mo.tL.getD 0) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  dsimp only [Ho, Hr] at h_sm h_df
  simp only [CryptoGames.SM.Engine.implECDF, compSizeW_bind, compSizeW_ret, compSizeW_caseSum,
    exprSizeW_pair, exprSizeW_inl, exprSizeW_inr, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, exprSizeW_var, Nat.reduceAdd]; omega

private theorem bind_ret_pair_unit_sizeW_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {opS : O'.Op → ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {Γ' : List (Ty S')} {σ : Ty S'} {c : Comp O' I' Γ' σ} {K M : ℕ}
    (hc : Bundles.compSizeW opS sS qS c ≤ K) (hM : K + 5 ≤ M) :
    Bundles.compSizeW opS sS qS (Comp.bind c (Comp.ret (.pair .unit .v0))) ≤ M := by
  simp only [compSizeW_bind, compSizeW_ret, exprSizeW_pair, exprSizeW_unit, exprSizeW_v0]; omega

private theorem authOut_ret_sizeW_le {O' : Ops S_cka} {ι : Type} {TSpec : OracleSpec ι}
    {I' : Iface S_cka TSpec} {vpT hsT : Ty S_cka} (opS : O'.Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (q qep : ℕ) (mo : CryptoGames.SM.Construction.Mode) (htStar : mo.tStar < qep + 2)
    (htL : mo.tL.getD 0 ≤ mo.tStar) (hqep : qep ≤ 4096 * q + 100000000) :
    Bundles.compSizeW opS sS qS (Comp.ret (I := I') (Γ := [CryptoGames.SM.Engine.esTy vpT hsT, .bool])
      (CryptoGames.SM.Engine.authOutE (q + 1) (2 + 1) mo.policy .v0)) ≤
      20 * bits (ratchetCostBudget q qep) + 1000 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  have h0 := (pureEngineExprs_sizeW_le opS (q + 1) mo.policy (Γ' := [CryptoGames.SM.Engine.esTy vpT hsT, .bool]) .v0).1
  have hpolL : mo.policy.tL = mo.tL := rfl; have hpolS : mo.policy.tStar = mo.tStar := rfl
  rw [hpolL, hpolS] at h0; simp only [exprSizeW_v0] at h0
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtS : bits mo.tStar ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (mo.tL.getD 0) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  simp only [compSizeW_ret]; omega

private theorem redCKAAuthDFProg_size_le (q qep t : ℕ) (tL : Option ℕ) {Δ : ℕ}
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses Δ t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1); let P := redCKAAuthDFProg' (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; have htL1 := targetsL_getD_le htL; have htL2 := healEpoch_le_of_getD_le htL1
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤ 10000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthDFProg]
    exact bind_ret_pair_unit_sizeW_le (initCKAEStateC_sizeW_le B mo (.bool false)) (by simp only [exprSizeW_bool]; omega)
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      1000 * bits (ratchetCostBudget q qep) + 250000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthDFProg]
    exact implECDF_sizeW_le_ratchet _ q qep mo ht htL1 hqep
      ((hooksCKAC_sizeBounded B B mo).mono (by dsimp [mo] at *; omega) le_rfl (by omega))
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthDFProg]
    exact authOut_ret_sizeW_le _ _ _ q qep mo ht htL1 hqep
  refine size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by decide) (by decide) ?_; omega

private theorem redPRNGAuthDFProg_size_le (q qep t : ℕ) (tL : Option ℕ) {Δ : ℕ}
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses Δ t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1); let P := redPRNGAuthDFProg' (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; have htL1 := targetsL_getD_le htL; have htL2 := healEpoch_le_of_getD_le htL1
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by change healEpoch tL ≤ _; omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤ 10 * bits (ratchetCostBudget q qep) + 7000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFProg]
    refine bind_ret_pair_unit_sizeW_le (initPRNGEStateC_sizeW_le B mo (.bool false)) ?_
    have hmS : mo.tStar = t := rfl; rw [hmS]; simp only [exprSizeW_bool]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤ 1000 * bits (ratchetCostBudget q qep) + 250000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFProg]
    exact implECDF_sizeW_le_ratchet _ q qep mo ht htL1 hqep ((hooksPRNGC_sizeBounded B B mo).mono (by dsimp [mo] at *; omega) le_rfl (by omega))
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤ 20 * bits (ratchetCostBudget q qep) + 1000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFProg]; exact authOut_ret_sizeW_le _ _ _ q qep mo ht htL1 hqep
  refine size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by decide) (by decide) ?_; omega

private theorem redFSAuthDFProg_size_le (q qep j t : ℕ) (tL : Option ℕ) {Δ : ℕ}
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses Δ t) (hj : j < q)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1); let P := redFSAuthDFProg' (q + 1) B 1 qep maxForwardJumps j tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; have htL1 := targetsL_getD_le htL; have htL2 := healEpoch_le_of_getD_le htL1
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbj : bits j ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      45 * bits (ratchetCostBudget q qep) + 15000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFProg]
    refine bind_ret_pair_unit_sizeW_le (initFSEStateC_sizeW_le B (q + 1) mo j (.bool false)) ?_
    have hmS : mo.tStar = t := rfl; rw [hmS]; simp only [exprSizeW_bool]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      1000 * bits (ratchetCostBudget q qep) + 250000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFProg]
    exact implECDF_sizeW_le_ratchet _ q qep mo ht htL1 hqep
      ((hooksFSC_sizeBounded B (q + 1) B mo j).mono (by dsimp [mo] at *; omega) le_rfl (by omega))
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤ 20 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFProg]
    simp only [Bundles.ckaSampS, compSizeW_sample, exprSizeW_unit, Nat.reduceAdd]; omega
  refine size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by decide) (by decide) ?_; omega

end DFEngineParts

section DFConcreteBounds

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

theorem challSimDFAtomicProg_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey) (idOf : Party → CryptoGames.LibsignalSession.IdentityKey)
    (lam : Pt) (qep q : ℕ) (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (Bundles.challSimDFAtomicProg Dh encPt C ℓ encT idOf lam qep q)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep) := by
  dsimp only [Bundles.challSimDFAtomicProg]
  exact compileSmDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ q qep q
    (challSimDFProg_parts_le q qep) (challSimDFProg_size_le q qep hqep)
    (by rw [CryptoGames.SM.challSimDFProg_totalQueries])

theorem redCKAAuthDFAtomicProg_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey) (idOf : Party → CryptoGames.LibsignalSession.IdentityKey)
    (lam : Pt) (qep q t : ℕ) (ht : t < qep + 2) (tL : Option ℕ) {Δ : ℕ}
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses Δ t) (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (Bundles.redCKAAuthDFAtomicProg Dh encPt C ℓ encT idOf lam qep q tL t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.redCKAAuthDFAtomicProg]
  exact compileCkaDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
    (redCKAAuthDFProg_parts_le q qep t tL ht htL) (redCKAAuthDFProg_size_le q qep t tL ht htL hqep)
    (by rw [CryptoGames.SM.Construction.redCKAAuthDFProg_totalQueries]; omega)

theorem redPRNGAuthDFAtomicProg_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey) (idOf : Party → CryptoGames.LibsignalSession.IdentityKey)
    (lam : Pt) (qep q t : ℕ) (ht : t < qep + 2) (tL : Option ℕ) {Δ : ℕ}
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses Δ t) (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (Bundles.redPRNGAuthDFAtomicProg Dh encPt C ℓ encT idOf lam qep q tL t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.redPRNGAuthDFAtomicProg]
  exact compilePrngDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
    (redPRNGAuthDFProg_parts_le q qep t tL ht htL) (redPRNGAuthDFProg_size_le q qep t tL ht htL hqep)
    (by rw [CryptoGames.SM.Construction.redPRNGAuthDFProg_totalQueries]; omega)

theorem redFSAuthDFAtomicProg_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey) (idOf : Party → CryptoGames.LibsignalSession.IdentityKey)
    (lam : Pt) (qep q t : ℕ) (ht : t < qep + 2) (tL : Option ℕ) {Δ : ℕ}
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses Δ t) (j : ℕ) (hj : j < q)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (Bundles.redFSAuthDFAtomicProg Dh encPt C ℓ encT idOf lam qep q j tL t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.redFSAuthDFAtomicProg]
  exact compileFsDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 * q)
    (redFSAuthDFProg_parts_le q qep j t tL ht htL hj) (redFSAuthDFProg_size_le q qep j t tL ht htL hj hqep)
    (by rw [CryptoGames.SM.Construction.redFSAuthDFProg_totalQueries]; omega)

/-- Discharges the `DeliverForge` boundedness conjuncts of `sessionCostedReductionsBounded` at budget `ratchetCostBudget q (qep + 1)`. -/
theorem sessionCostedDFBaseBounds (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey) (idOf : Party → CryptoGames.LibsignalSession.IdentityKey)
    (lam : Pt) (qep q : ℕ) (hqep : qep + 1 ≤ 4096 * q + 100000000 := by omega) :
    let B := ratchetCostBudget q (qep + 1)
    GRedBounded (Bundles.challSimDFAtomicProg Dh encPt C ℓ encT idOf lam (qep + 1) q) (fun _ => 1) (fun _ => 0) q q B ∧
    (∀ t < (qep + 1) + 2, ∀ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      GRedBounded (Bundles.redCKAAuthDFAtomicProg Dh encPt C ℓ encT idOf lam (qep + 1) q tL t)
        (fun _ => 1) (fun _ => 0) q (2 + 2 * q) B) ∧
    (∀ t < (qep + 1) + 2, ∀ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      GRedBounded (Bundles.redPRNGAuthDFAtomicProg Dh encPt C ℓ encT idOf lam (qep + 1) q tL t)
        (fun _ => 1) (fun _ => 0) q (2 + 2 * q) B) ∧
    (∀ t < (qep + 1) + 2, ∀ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t, ∀ j < q,
      GRedBounded (Bundles.redFSAuthDFAtomicProg Dh encPt C ℓ encT idOf lam (qep + 1) q j tL t)
        (fun _ => 1) (fun _ => 0) q (2 * q) B) :=
  ⟨challSimDFAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam (qep + 1) q (by omega),
    fun t ht tL htL => redCKAAuthDFAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam (qep + 1) q t ht tL htL (by omega),
    fun t ht tL htL => redPRNGAuthDFAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam (qep + 1) q t ht tL htL (by omega),
    fun t ht tL htL j hj => redFSAuthDFAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam (qep + 1) q t ht tL htL j hj (by omega)⟩

end DFConcreteBounds

end Computational.Proofs.SessionCostedFig8.DFProgBoundsBase

-- AUTO-BRIDGE BEGIN
namespace Computational.Proofs.SessionCostedFig8
export Computational.Proofs.SessionCostedFig8.DFProgBoundsBase (
  compileSmDFAtomic_gRedBounded
  compileCkaDFAtomic_gRedBounded
  compilePrngDFAtomic_gRedBounded
  compileFsDFAtomic_gRedBounded
  challSimDFAtomicProg_gRedBounded
  redCKAAuthDFAtomicProg_gRedBounded
  redPRNGAuthDFAtomicProg_gRedBounded
  redFSAuthDFAtomicProg_gRedBounded
  sessionCostedDFBaseBounds
)
end Computational.Proofs.SessionCostedFig8
-- AUTO-BRIDGE END
