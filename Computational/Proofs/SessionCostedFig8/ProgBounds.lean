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
import Computational.Proofs.ReductionDsl.Notation
import Computational.Proofs.GameHop.ReductionDsl.CostUB
import Computational.Proofs.GameHop.ReductionDsl.SupportWP
import Computational.Proofs.ReductionDsl.SM.RedCKAPotOK
import Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
import Computational.Proofs.ReductionDsl.SM.RedPRNGPrivQepPotOK
import Computational.Proofs.ReductionDsl.SM.RedFSPotOK

/-!
# Cost Bounds for Atomic Figure 8 Reductions

Proves `GRedBounded` within `ratchetCostBudget` and semantic query bounds for the compiled atomic
Figure 8 reductions of `Bundles.fig8RedsInst`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.SessionCostedFig8.ProgBounds

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface Expr Comp CostedReduction bits reductionSizeBudget
  AtomicUnifBase ckaTargetIface prngTargetIface atomicFig8Ops_sizeHonest atomicSamplers_sizeHonest
  bits_le_succ)
open CryptoGames (Party)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open Computational.Proofs.SessionCostedFig8.QuerySubsumes (QuerySubsumes)
open Computational.Proofs.GameHop.ReductionDsl.CostUB (compCostUB exprCostUB
  compCost_le_costUB exprCost_le_costUB)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_succ_le)
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (HooksCostBounded HooksCostBounded.mono
  hooksCKAC_costBounded hooksPRNGC_costBounded hooksFSC_costBounded_linear
  initCKAEStateC_cost_le initPRNGEStateC_cost_le initFSEStateC_cost_le
  implEC_cost_le vRecvC_cost_le commitEC_cost_le
  cInTransitE_cost_le cCompContainsE_cost_le cTrivialE_cost_le
  fig8StepBound thm1_simHandleC_cost_le
  bits_le_bits_qep_add targetsL_bounds
  v0_cost v1_cost v2_cost v3_cost v4_cost v5_cost v6_cost v7_cost
  otherE_cost isSomeE_cost pGet_cost
  cGsEpoch_cost cGsIdx_cost cGsSt_cost cGsB_cost cRecPos_cost
  esG_cost esH_cost esAbort_cost esSetG_cost esSetH_cost esSetAbort_cost
  cGsSetWin_cost cGsSetStP_cost
  authOutE_cost_le privOutC_cost_le)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (HooksExcessBounded HooksExcessBounded.mono
  hooksCKAC_excessBounded hooksPRNGC_excessBounded hooksFSC_excessBounded
  initCKAEStateC_excessUB_le initPRNGEStateC_excessUB_le initFSEStateC_excessUB_le
  implEC_excessUB_le vSendC_excessUB_le vRecvC_excessUB_le commitEC_excessUB_le
  cInTransitE_excessUB optNatLit_excessUB
  smOpC smSampC smQueryC ckaOpC ckaSampC
  ckaQueryC prngQueryC fsQueryC exprExcessUB compExcessUB compCostW_le_cost_add_excessUB
  privOutC_excessUB_le pureEngineExprs_excessUB
  thm1_simInitC_cost_le thm1_simInitC_excessUB_le thm1_simHandleC_excessUB_le
  compExcessUB_bind compExcessUB_ret compExcessUB_sample compExcessUB_ite
  compExcessUB_caseOpt compExcessUB_caseSum compExcessUB_query
  exprExcessUB_v0 exprExcessUB_v1 exprExcessUB_v2 exprExcessUB_v3 exprExcessUB_v4
  exprExcessUB_v5 exprExcessUB_v6 exprExcessUB_v7 exprExcessUB_var
  exprExcessUB_unit exprExcessUB_bool exprExcessUB_nat exprExcessUB_none exprExcessUB_nil
  exprExcessUB_add exprExcessUB_sub exprExcessUB_mulK exprExcessUB_divK exprExcessUB_modK
  exprExcessUB_lt exprExcessUB_eqN exprExcessUB_not exprExcessUB_and exprExcessUB_ite
  exprExcessUB_pair exprExcessUB_fst exprExcessUB_snd exprExcessUB_inl exprExcessUB_inr
  exprExcessUB_some exprExcessUB_caseOpt exprExcessUB_caseSum exprExcessUB_letE
  exprExcessUB_op exprExcessUB_cons exprExcessUB_len exprExcessUB_take
  exprExcessUB_appendL exprExcessUB_findB exprExcessUB_anyB exprExcessUB_mapB
  exprExcessUB_foldrB exprExcessUB_tconst exprExcessUB_tget exprExcessUB_tset)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound bits_le_add_one
  add_mul_le_ratchetCostBudget_atomic compCostW_le_of_parts
  implEC_compCostW_le_fig8AtomicStepBound
  redCKAAuthProg_parts_le redCKAPrivProg_parts_le redPRNGAuthProg_parts_le
  redPRNGPrivProg_parts_le redFSAuthProg_parts_le redFSPrivProg_parts_le
  redFSPrivCoinProg_parts_le)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW compCostW compilePureAuxRed
  compilePureAuxRed_totalCost_le compilePureAuxRed_totalQueries_le)
open Computational.Proofs.ReductionDsl.MacroLift (toVal dummyRed guardRed guardRed_gRedBounded)
open Computational.Proofs.SessionCostedFig8.ProgSizeBounds (HooksSizeBounded
  bits_B0_le_ratchetCostBudget bits_le_ratchetCostBudget_of_le_linear
  bits_qep_le_ratchetCostBudget bits_zero bits_one bits_two bits_three bits_four
  optNatLit_sizeW vSendC_sizeW_le vRecvC_sizeW_le commitEC_sizeW_le cInTransitE_sizeW_le
  compSizeW_bind compSizeW_ite compSizeW_ret compSizeW_sample
  compSizeW_caseOpt compSizeW_caseSum compSizeW_query
  exprSizeW_v0 exprSizeW_v1 exprSizeW_v2 exprSizeW_v3 exprSizeW_v4
  exprSizeW_v5 exprSizeW_v6 exprSizeW_v7 exprSizeW_var
  exprSizeW_unit exprSizeW_bool exprSizeW_nat exprSizeW_none exprSizeW_nil
  exprSizeW_add exprSizeW_sub exprSizeW_mulK exprSizeW_divK exprSizeW_modK
  exprSizeW_lt exprSizeW_eqN exprSizeW_not exprSizeW_and exprSizeW_ite
  exprSizeW_pair exprSizeW_fst exprSizeW_snd exprSizeW_inl exprSizeW_inr
  exprSizeW_some exprSizeW_caseOpt exprSizeW_caseSum exprSizeW_letE
  exprSizeW_op exprSizeW_cons exprSizeW_len exprSizeW_take
  exprSizeW_appendL exprSizeW_findB exprSizeW_anyB exprSizeW_mapB
  exprSizeW_foldrB exprSizeW_tconst exprSizeW_tget exprSizeW_tset
  hooksCKAC_sizeBounded hooksFSC_sizeBounded hooksPRNGC_sizeBounded implEC_sizeW_le
  initCKAEStateC_sizeW_le initFSEStateC_sizeW_le initPRNGEStateC_sizeW_le privOutC_sizeW_le
  pureEngineExprs_sizeW_le size_le_ratchetSizeBudget thm1_simHandleC_sizeW_le
  thm1_simInitC_sizeW_le)

/-! ## Arithmetic and cost helpers -/

theorem const_le_fig8AtomicStepBound {q qep c : ℕ} (hc : c ≤ 25000000) :
    c ≤ fig8AtomicStepBound q qep := by
  unfold fig8AtomicStepBound
  dsimp only
  omega

theorem linear_le_fig8AtomicStepBound {q qep k a b : ℕ}
    (hk : k ≤ 200) (ha : a ≤ 15000) (hb : b ≤ 25000000) :
    k * bits qep + a * (q + 1) + b ≤ fig8AtomicStepBound q qep := by
  unfold fig8AtomicStepBound
  dsimp only
  have hk' := Nat.mul_le_mul_right (bits qep) hk
  have ha' := Nat.mul_le_mul_right (q + 1) ha
  generalize bits qep = bq at hk' ⊢
  generalize (q + 1) * (q + 1) = qq
  generalize (q + 1) * (3 * bq + 60) = qbq
  generalize (q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1) = B
  generalize q + 1 = L at ha' ⊢
  omega

theorem compiled_totalCost_le_ratchetCostBudget
    {q qep initW handleW finishW ovhI uC ovhH ovhF : ℕ}
    (hIF : initW + finishW + 100000 ≤ fig8AtomicStepBound q qep)
    (hH : handleW + 200000 ≤ fig8AtomicStepBound q qep)
    (hovhIF : ovhI + ovhF ≤ 100000)
    (huC : uC ≤ 200000)
    (hovhH : ovhH ≤ 200000) :
    (initW + ovhI) + q * max uC (handleW + ovhH) + (finishW + ovhF) ≤
      ratchetCostBudget q qep := by
  have h200k : 200000 ≤ fig8AtomicStepBound q qep := const_le_fig8AtomicStepBound (by decide)
  have hmax : max uC (handleW + ovhH) ≤ fig8AtomicStepBound q qep :=
    max_le (huC.trans h200k) (by omega)
  have h1 : (initW + ovhI) + (finishW + ovhF) ≤ fig8AtomicStepBound q qep := by omega
  have h2 :
      (initW + ovhI) + q * max uC (handleW + ovhH) + (finishW + ovhF) =
        ((initW + ovhI) + (finishW + ovhF)) + q * max uC (handleW + ovhH) := by omega
  rw [h2]
  exact add_mul_le_ratchetCostBudget_atomic h1 hmax

theorem compiled_le_ratchetCostBudget {q qep iW hW fW sI aI aQ aR cc aO aOut u : ℕ}
    (hIF : iW + fW + 100000 ≤ fig8AtomicStepBound q qep)
    (hH : hW + 200000 ≤ fig8AtomicStepBound q qep)
    (hs : sI + aI + aO + aOut ≤ 50000) (hu : u ≤ 200000) (hq : aQ + aR + cc ≤ 100000) :
    (iW + sI + aI + 24) + q * max u (hW + aQ + aR + cc + 28) + (fW + aO + aOut + 22) ≤
      ratchetCostBudget q qep := by
  have h200k : 200000 ≤ fig8AtomicStepBound q qep := const_le_fig8AtomicStepBound (by decide)
  have hmax : max u (hW + aQ + aR + cc + 28) ≤ fig8AtomicStepBound q qep :=
    max_le (hu.trans h200k) (by omega)
  have h1 : (iW + sI + aI + 24) + (fW + aO + aOut + 22) ≤ fig8AtomicStepBound q qep := by omega
  have := add_mul_le_ratchetCostBudget_atomic h1 hmax
  omega

theorem dummy_le_ratchetCostBudget {q qep x y z : ℕ} (hxz : x + z ≤ 100000) (hy : y ≤ 200000) :
    x + q * y + z ≤ ratchetCostBudget q qep := by
  have h200k : 200000 ≤ fig8AtomicStepBound q qep := const_le_fig8AtomicStepBound (by decide)
  have := add_mul_le_ratchetCostBudget_atomic (q := q) (qep := qep) (a := x + z) (b := y)
    (by omega) (by omega)
  omega


theorem pureRetRed_isQueryBoundP
    {S : Sig} {O : Ops S} {ι κ : Type} {T₀ : OracleSpec.{0, 0} ι}
    {I : Iface S (unifSpec + T₀)}
    {G : OracleSpec.{0, 0} κ} {C : _root_.ReductionDsl.GameCodec S G}
    {rIn aIn aOut out σ : Ty S}
    (initE : Expr O [rIn] (.prod aIn σ))
    (handleE : Expr O [σ, C.Q] (.prod C.R σ))
    (finishE : Expr O [σ, aOut] out)
    {P : (unifSpec + T₀).Domain → Prop} [DecidablePred P]
    (hFwdU : ∀ n, I.fwdU n = liftM (OracleSpec.query (spec := unifSpec + T₀) (.inl n)))
    (hP : ∀ n, ¬ P (.inl n))
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) (k : ℕ) :
    (({ σ := σ, init := .ret initE, handle := .ret handleE, finish := .ret finishE } :
        CostedReduction O I G C rIn aIn aOut out).eval A x).IsQueryBoundP P k := by
  let R : CostedReduction O I G C rIn aIn aOut out :=
    { σ := σ, init := .ret initE, handle := .ret handleE, finish := .ret finishE }
  suffices hSim : ∀ (oa : OracleComp (unifSpec + G) aOut.denote) (s : σ.denote),
      (((simulateQ R.impl oa).run s) >>= fun bs =>
        pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))).IsQueryBoundP P k by
    change (R.eval A x).IsQueryBoundP P k
    unfold CostedReduction.eval
    simp only [R, Comp.eval, pure_bind]
    exact hSim (A (initE.eval (.cons x .nil)).1) (initE.eval (.cons x .nil)).2
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure b =>
    intro s
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    intro s
    rcases q with n | t
    · have hStep : ((simulateQ R.impl
          (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx)).run s) >>=
            (fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) =
          liftM (OracleSpec.query (spec := unifSpec + T₀) (.inl n)) >>= fun u =>
            (((simulateQ R.impl (mx u)).run s) >>=
              fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) := by
        simp [R, CostedReduction.impl, _root_.ReductionDsl.handlerImpl,
          StateT.run_bind, StateT.run_lift, hFwdU, map_eq_bind_pure_comp, bind_assoc]
      rw [hStep, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (hP n), fun u => by simpa [hP n] using ih u s⟩
    · have hStep : ((simulateQ R.impl
          (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx)).run s) >>=
            (fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) =
          (((simulateQ R.impl
              (mx (C.rdec t (handleE.eval (.cons s (.cons (C.qenc t) .nil))).1))).run
            (handleE.eval (.cons s (.cons (C.qenc t) .nil))).2) >>=
              fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) := by
        simp [R, CostedReduction.impl, _root_.ReductionDsl.handlerImpl, Comp.eval,
          StateT.run_bind, StateT.run_mk, pure_bind]
      rw [hStep]
      exact ih _ _


/-! ## Secure-messaging reductions -/

section SMParts

variable {Key St St₂ Msg Coins RCoins C : Type}
  {init : Party → Key → Option St} {send : St → Msg → Coins → Option (St × C)}
  {receive : St → C → RCoins → Option (St × ℕ × ℕ × Msg)}
  {eqMsg : Msg → Msg → Bool} {eqCt : C → C → Bool} {blank : Msg → Msg}
  {injOK : C → Bool} {stOK : Party → St → Bool} {φ : St → Option St₂}
  {stSort : CryptoGames.SM.SMSort}
  {sampKey : ProbComp (Option Key)} {sampCoins : ProbComp (Option Coins)}
  {sampRCoins : ProbComp (Option RCoins)}

theorem challSimProg_parts_le (q qep : ℕ) :
    let P := CryptoGames.SM.challSimProg (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q 3 qep
    compCostW smOpC smSampC smQueryC P.init + compCostW smOpC smSampC smQueryC P.finish +
        100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW smOpC smSampC smQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro P
  have hi : compCostW smOpC smSampC smQueryC P.init ≤ 700 := by
    dsimp only [P, CryptoGames.SM.challSimProg]
    exact compCostW_le_of_parts thm1_simInitC_cost_le thm1_simInitC_excessUB_le (by omega)
  have hf : compCostW smOpC smSampC smQueryC P.finish ≤ 20 := by
    dsimp only [P, CryptoGames.SM.challSimProg]
    exact compCostW_le_of_parts (a := 10) (b := 0)
      (by simp only [Comp.cost, v1_cost]; decide)
      (by simp only [compExcessUB_ret, exprExcessUB_v1]; decide) (by omega)
  have hh : compCostW smOpC smSampC smQueryC P.handle ≤
      20 * bits qep + 2000 * q + 1017030 := by
    dsimp only [P, CryptoGames.SM.challSimProg]
    have hb0 : bits 0 = 1 := rfl
    refine compCostW_le_of_parts (thm1_simHandleC_cost_le q qep none)
      (thm1_simHandleC_excessUB_le q qep none) ?_
    simp only [Option.getD_none, hb0]
    omega
  refine ⟨(Nat.add_le_add_right (Nat.add_le_add hi hf) 100000).trans
    (const_le_fig8AtomicStepBound (by decide)), ?_⟩
  refine (Nat.add_le_add_right hh 200000).trans ?_
  refine (le_of_eq ?_).trans (linear_le_fig8AtomicStepBound (k := 20) (a := 2000)
    (b := 1215030) (q := q) (qep := qep) (by decide) (by decide) (by decide))
  ring

theorem privRedBProg_parts_le (q qep i : ℕ) (hi_ep : i < qep + 2) :
    let P := CryptoGames.SM.privRedBProg (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q 3 qep i
    compCostW smOpC smSampC smQueryC P.init + compCostW smOpC smSampC smQueryC P.finish +
        100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW smOpC smSampC smQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro P
  have hi : compCostW smOpC smSampC smQueryC P.init ≤ 700 := by
    dsimp only [P, CryptoGames.SM.privRedBProg]
    exact compCostW_le_of_parts thm1_simInitC_cost_le thm1_simInitC_excessUB_le (by omega)
  have hf : compCostW smOpC smSampC smQueryC P.finish ≤ 50 := by
    dsimp only [P, CryptoGames.SM.privRedBProg]
    exact compCostW_le_of_parts (a := 30) (b := 0)
      (by simp only [CryptoGames.SM.boolEq, CryptoGames.SM.mB, Comp.cost, Expr.cost, v0_cost,
        v1_cost, Nat.reduceAdd]; decide)
      (by simp only [CryptoGames.SM.boolEq, CryptoGames.SM.mB, compExcessUB_ret, exprExcessUB_ite,
        exprExcessUB_not, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_v0, exprExcessUB_v1,
        Nat.reduceAdd]; decide)
      (by omega)
  have hh : compCostW smOpC smSampC smQueryC P.handle ≤
      25 * bits qep + 2000 * q + 1017050 := by
    dsimp only [P, CryptoGames.SM.privRedBProg]
    have hbi := bits_le_bits_qep_add (x := i) (qep := qep) (by omega)
    refine compCostW_le_of_parts (thm1_simHandleC_cost_le q qep (some i))
      (thm1_simHandleC_excessUB_le q qep (some i)) ?_
    simp only [Option.getD_some]
    omega
  refine ⟨(Nat.add_le_add_right (Nat.add_le_add hi hf) 100000).trans
    (const_le_fig8AtomicStepBound (by decide)), ?_⟩
  refine (Nat.add_le_add_right hh 200000).trans ?_
  refine (le_of_eq ?_).trans (linear_le_fig8AtomicStepBound (k := 25) (a := 2000)
    (b := 1215050) (q := q) (qep := qep) (by decide) (by decide) (by decide))
  ring

set_option maxRecDepth 100000 in
theorem challSimProg_size_le (q qep : ℕ) (hqep : qep ≤ 4096 * q + 100000000) :
    let P := CryptoGames.SM.challSimProg (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q 3 qep
    Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.init +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.handle +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro P
  have hi : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.init ≤ 1000 :=
    thm1_simInitC_sizeW_le
  have hh : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.handle ≤
      50 * bits q + 30 * bits qep + 20010 := by
    have h0 := thm1_simHandleC_sizeW_le (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q qep none
    simp only [Option.getD_none, bits_zero] at h0
    dsimp only [P, CryptoGames.SM.challSimProg]
    omega
  have hf : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.finish ≤ 20 := by
    dsimp only [P, CryptoGames.SM.challSimProg]
    simp only [compSizeW_ret, exprSizeW_v1, Nat.reduceAdd]; omega
  have hbq : bits q ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  refine size_le_ratchetSizeBudget (C₀ := 25000) (C₁ := 80) (by decide) (by decide) ?_
  omega

set_option maxRecDepth 100000 in
theorem privRedBProg_size_le (q qep i : ℕ) (hi_ep : i < qep + 2)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let P := CryptoGames.SM.privRedBProg (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q 3 qep i
    Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.init +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.handle +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro P
  have hi : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.init ≤ 1000 :=
    thm1_simInitC_sizeW_le
  have hh : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.handle ≤
      50 * bits q + 30 * bits qep + 10 * bits i + 20000 := by
    have h0 := thm1_simHandleC_sizeW_le (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q qep (some i)
    simp only [Option.getD_some] at h0
    dsimp only [P, CryptoGames.SM.privRedBProg]
    omega
  have hf : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.finish ≤ 50 := by
    dsimp only [P, CryptoGames.SM.privRedBProg]
    simp only [CryptoGames.SM.boolEq, CryptoGames.SM.mB, compSizeW_ret, exprSizeW_ite,
      exprSizeW_not, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd]
    omega
  have hbq : bits q ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  have hbi : bits i ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  refine size_le_ratchetSizeBudget (C₀ := 25000) (C₁ := 90) (by decide) (by decide) ?_
  omega

end SMParts

section SMWrapper

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : CryptoGames.LibsignalSession.Crypto) (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
  (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)

set_option maxRecDepth 100000 in
theorem compileSmAtomic_gRedBounded
    (R : CostedReduction (Bundles.fig8SmOpsShallow ℓ Pt)
      (CryptoGames.SM.smIface Unit (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt) Unit
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) Unit (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.SM.smCodec Unit (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt) Unit
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) Unit (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW smOpC smSampC smQueryC R.init + compCostW smOpC smSampC smQueryC R.finish +
        100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW smOpC smSampC smQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS R.init +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS R.handle +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS R.finish + 400 ≤
        reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compileSmAtomic ℓ Pt C Dh encPt encT idOf lam R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compileSmAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R smOpC smSampC smQueryC ?_ ?_ ?_ q).trans
      (compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ ?_ ?_)
    · intro o
      have h1 := Computational.Proofs.ReductionDsl.Fig8Atomic.eqMExpr_cost ℓ Pt C Dh encPt encT lam
      have h2 := Computational.Proofs.ReductionDsl.Fig8Atomic.smEqCtExpr_cost ℓ Pt C Dh encPt encT lam
      have h3 := Computational.Proofs.ReductionDsl.Fig8Atomic.smBlankExpr_cost ℓ Pt C Dh encPt encT lam
      cases o <;> simp only [Bundles.smPureAuxBundle, Bundles.smOpMacro, smOpC, Expr.cost] <;> omega
    · intro s
      cases s <;> simp [Bundles.smPureAuxBundle, Bundles.smSampMacro, smSampC, Comp.cost, Expr.cost]
    · intro g
      cases g <;> simp [smQueryC, Comp.cost, Expr.cost] <;> omega
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam
      simp only [Expr.cost]
      omega
    · simp
    · have h1 := Bundles.fig8AdaptQ_cost ℓ Pt C Dh encPt encT lam
      have h2 := Bundles.fig8AdaptR_cost ℓ Pt C Dh encPt encT lam
      simp
      omega
  · exact dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R Bundles.smOpS Bundles.smSampS Bundles.smQueryS
      (Bundles.smOpMacro_size_le ℓ Pt C Dh encPt encT lam) ?_ ?_).trans ?_
    · intro s
      cases s <;> simp [Bundles.smPureAuxBundle, Bundles.smSampMacro, Bundles.smSampS, Comp.size,
        Expr.size]
    · intro g
      cases g <;> simp [Bundles.smQueryS, Comp.size, Expr.size]
    · have hs := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have hq := Bundles.fig8AdaptQ_size ℓ Pt C Dh encPt encT lam
      have hr := Bundles.fig8AdaptR_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]
      omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s
      cases s <;> simp [Bundles.smPureAuxBundle, Bundles.smSampMacro, Comp.queries]
    · intro g
      cases g <;> simp [Comp.queries]

end SMWrapper

section SMInstance

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

theorem fig8RedsInst_challSim_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).challSim
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileSmAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ q qep q
    (challSimProg_parts_le q qep) (challSimProg_size_le q qep hqep)
    (by rw [CryptoGames.SM.challSimProg_totalQueries])

theorem fig8RedsInst_privRedB_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ) (hi : i < qep + 1) (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).privRedB i)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileSmAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ q qep q
    (privRedBProg_parts_le q qep i (by omega)) (privRedBProg_size_le q qep i (by omega) hqep)
    (by rw [CryptoGames.SM.privRedBProg_totalQueries])

end SMInstance


/-! ## Compiled CKA, PRNG, and FS-AEAD reductions -/

section CkaWrapper

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : CryptoGames.LibsignalSession.Crypto) (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
  (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)

omit [SampleableType Pt] in
theorem ckaOpMacro_cost_le (hℓ : ℓ < 10 ^ 6) (B0 : ℕ) (o : CryptoGames.CKA.CKAOp) :
    (Bundles.ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0 o).cost + 1 ≤ ckaOpC B0 o := by
  have h1 := Computational.Proofs.ReductionDsl.Fig8Atomic.ckaInitAExpr_cost ℓ Pt C Dh encPt encT lam
  have h2 := Computational.Proofs.ReductionDsl.Fig8Atomic.ckaInitBExpr_cost ℓ Pt C Dh encPt encT lam
  have h3 := Computational.Proofs.ReductionDsl.Fig8Atomic.ckaSendExpr_cost ℓ Pt C Dh encPt encT lam
  have h4 := Computational.Proofs.ReductionDsl.Fig8Atomic.ckaRecvExpr_cost ℓ Pt C Dh encPt encT lam
  have h5 := Computational.Proofs.ReductionDsl.Fig8Atomic.prngInitExpr_cost ℓ Pt C Dh encPt encT lam
  have h6 := Computational.Proofs.ReductionDsl.Fig8Atomic.prngUpExpr_cost ℓ Pt C Dh encPt encT lam
  have h7 :=
    Computational.Proofs.ReductionDsl.Fig8Atomic.fsInitSendExpr_cost ℓ Pt C Dh encPt encT lam
  have h8 :=
    Computational.Proofs.ReductionDsl.Fig8Atomic.fsInitRecvExpr_cost ℓ Pt C Dh encPt encT lam
  have h9 := Computational.Proofs.ReductionDsl.Fig8Atomic.fsSendExpr_cost ℓ Pt C Dh encPt encT lam
  have h10 := Computational.Proofs.ReductionDsl.Fig8Atomic.eqPtExpr_cost ℓ Pt C Dh encPt encT lam
  have h11 := Computational.Proofs.ReductionDsl.Fig8Atomic.eqMExpr_cost ℓ Pt C Dh encPt encT lam
  have h12 := Computational.Proofs.ReductionDsl.Fig8Atomic.eqEExpr_cost ℓ Pt C Dh encPt encT lam
  have h13 := Computational.Proofs.ReductionDsl.Fig8Atomic.lamIExpr_cost ℓ Pt C Dh encPt encT lam
  have h14 :=
    Computational.Proofs.ReductionDsl.Fig8Atomic.defaultEExpr_cost ℓ Pt C Dh encPt encT lam
  cases o with
  | fsReceive B' =>
    have h15 :=
      Computational.Proofs.ReductionDsl.Fig8Atomic.fsRecvExpr_cost ℓ Pt C Dh encPt encT lam B0 B'
    simp only [Bundles.ckaOpMacro, ckaOpC]
    omega
  | _ => simp only [Bundles.ckaOpMacro, ckaOpC]; omega

set_option maxRecDepth 100000 in
theorem compileCkaAtomic_gRedBounded (B0 : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.CKA.ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW (ckaOpC B0) ckaSampC ckaQueryC R.init +
        compCostW (ckaOpC B0) ckaSampC ckaQueryC R.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B0) ckaSampC ckaQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.finish + 400 ≤
        reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compileCkaAtomic ℓ Pt C Dh encPt encT idOf lam B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compileCkaAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R (ckaOpC B0) ckaSampC ckaQueryC ?_ ?_ ?_ q).trans
      (compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ ?_ ?_)
    · exact ckaOpMacro_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ B0
    · intro s
      cases s <;> simp [Bundles.ckaPureAuxBundle, Bundles.ckaSampMacro, ckaSampC, Comp.cost,
        Expr.cost, AtomicUnifBase.cost]
    · intro g
      cases g <;> simp [ckaQueryC, Comp.cost, Expr.cost]
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam
      simp only [Expr.cost]
      omega
    · simp
    · have h1 := Bundles.fig8AdaptQ_cost ℓ Pt C Dh encPt encT lam
      have h2 := Bundles.fig8AdaptR_cost ℓ Pt C Dh encPt encT lam
      simp
      omega
  · exact dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R (Bundles.ckaOpS B0) Bundles.ckaSampS
      Bundles.ckaQueryS (Bundles.ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0) ?_ ?_).trans ?_
    · intro s
      cases s <;> simp [Bundles.ckaPureAuxBundle, Bundles.ckaSampMacro, Bundles.ckaSampS,
        Comp.size, Expr.size]
    · intro g
      cases g <;> simp [Bundles.ckaQueryS, Comp.size, Expr.size]
    · have hs := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have hq := Bundles.fig8AdaptQ_size ℓ Pt C Dh encPt encT lam
      have hr := Bundles.fig8AdaptR_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]
      omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s
      cases s <;> simp [Bundles.ckaPureAuxBundle, Bundles.ckaSampMacro, Comp.queries]
    · intro g
      cases g <;> simp [Comp.queries]

set_option maxRecDepth 100000 in
theorem compilePrngAtomic_gRedBounded (B0 : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW (ckaOpC B0) ckaSampC prngQueryC R.init +
        compCostW (ckaOpC B0) ckaSampC prngQueryC R.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B0) ckaSampC prngQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.finish + 400 ≤
        reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compilePrngAtomic ℓ Pt C Dh encPt encT idOf lam B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compilePrngAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R (ckaOpC B0) ckaSampC prngQueryC ?_ ?_ ?_ q).trans
      (compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ ?_ ?_)
    · exact ckaOpMacro_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ B0
    · intro s
      cases s <;> simp [Bundles.prngPureAuxBundle, Bundles.prngSampMacro, ckaSampC, Comp.cost,
        Expr.cost, AtomicUnifBase.cost]
    · intro g
      cases g <;> simp [prngQueryC, Comp.cost, Expr.cost]
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam
      simp only [Expr.cost]
      omega
    · simp
    · have h1 := Bundles.fig8AdaptQ_cost ℓ Pt C Dh encPt encT lam
      have h2 := Bundles.fig8AdaptR_cost ℓ Pt C Dh encPt encT lam
      simp
      omega
  · exact dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R (Bundles.ckaOpS B0) Bundles.ckaSampS
      Bundles.ckaQueryS (Bundles.ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0) ?_ ?_).trans ?_
    · intro s
      cases s <;> simp [Bundles.prngPureAuxBundle, Bundles.prngSampMacro, Bundles.ckaSampS,
        Comp.size, Expr.size]
    · intro g
      cases g <;> simp [Bundles.ckaQueryS, Comp.size, Expr.size]
    · have hs := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have hq := Bundles.fig8AdaptQ_size ℓ Pt C Dh encPt encT lam
      have hr := Bundles.fig8AdaptR_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]
      omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s
      cases s <;> simp [Bundles.prngPureAuxBundle, Bundles.prngSampMacro, Comp.queries]
    · intro g
      cases g <;> simp [Comp.queries]


set_option maxRecDepth 100000 in
theorem compileFsAtomic_gRedBounded (B0 : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW (ckaOpC B0) ckaSampC fsQueryC R.init +
        compCostW (ckaOpC B0) ckaSampC fsQueryC R.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B0) ckaSampC fsQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.finish + 400 ≤
        reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compileFsAtomic ℓ Pt C Dh encPt encT idOf lam B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compileFsAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R (ckaOpC B0) ckaSampC fsQueryC ?_ ?_ ?_ q).trans
      (compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ ?_ ?_)
    · exact ckaOpMacro_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ B0
    · intro s
      cases s <;> simp [Bundles.fsPureAuxBundle, Bundles.fsSampMacro, ckaSampC, Comp.cost,
        Expr.cost, AtomicUnifBase.cost]
    · intro g
      cases g <;> simp [fsQueryC, Comp.cost, Expr.cost] <;> omega
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam
      simp only [Expr.cost]
      omega
    · simp
    · have h1 := Bundles.fig8AdaptQ_cost ℓ Pt C Dh encPt encT lam
      have h2 := Bundles.fig8AdaptR_cost ℓ Pt C Dh encPt encT lam
      simp
      omega
  · exact dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R (Bundles.ckaOpS B0) Bundles.ckaSampS
      Bundles.ckaQueryS (Bundles.ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0) ?_ ?_).trans ?_
    · intro s
      cases s <;> simp [Bundles.fsPureAuxBundle, Bundles.fsSampMacro, Bundles.ckaSampS,
        Comp.size, Expr.size]
    · intro g
      cases g <;> simp [Bundles.ckaQueryS, Comp.size, Expr.size]
    · have hs := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have hq := Bundles.fig8AdaptQ_size ℓ Pt C Dh encPt encT lam
      have hr := Bundles.fig8AdaptR_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]
      omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s
      cases s <;> simp [Bundles.fsPureAuxBundle, Bundles.fsSampMacro, Comp.queries]
    · intro g
      cases g <;> simp [Comp.queries]


private theorem liftP_congr {ι : Type} {T : OracleSpec.{0, 0} ι} {S₁' S₂' : Sig}
    (I₂ : Iface S₂' T) (I₁ : Iface S₁' T) (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    {α : Type} (p : ProbComp α) : I₂.liftP p = I₁.liftP p := by
  unfold Iface.liftP
  rw [funext hFwdU]

private theorem ckaPureAuxBundle_samp_querySubsumes (B0 : ℕ) (s : CryptoGames.CKA.CKASamp)
    (z : ((CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    QuerySubsumes
      (((Bundles.ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (Bundles.fSortCKA ℓ Pt) (Bundles.toDenCKA ℓ Pt) _ z)
          (.cons (idOf .A, idOf .B) .nil)))
      (toVal (Bundles.fSortCKA ℓ Pt) (Bundles.toDenCKA ℓ Pt)
        ((CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
          (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
          (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
            (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
            (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
            (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s with
  | bit | i =>
    apply QuerySubsumes.of_eq
    exact (liftP_congr (ckaTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    exact
      Bundles.querySubsumes_liftP_of_support_subset (ckaTargetIface ℓ Pt)
        (CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
          (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => by simp)

private theorem prngPureAuxBundle_samp_querySubsumes (B0 : ℕ) (s : CryptoGames.CKA.CKASamp)
    (z : ((CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    QuerySubsumes
      (((Bundles.prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (Bundles.fSortCKA ℓ Pt) (Bundles.toDenCKA ℓ Pt) _ z)
          (.cons (idOf .A, idOf .B) .nil)))
      (toVal (Bundles.fSortCKA ℓ Pt) (Bundles.toDenCKA ℓ Pt)
        ((CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
          (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
          (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
            (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
            (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
            (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s with
  | bit | i =>
    apply QuerySubsumes.of_eq
    exact (liftP_congr (prngTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    exact
      Bundles.querySubsumes_liftP_of_support_subset (prngTargetIface ℓ Pt)
        (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
          (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => by simp)

theorem compileCkaAtomic_makesAtMostQueries [Inhabited Pt] (B0 qOut : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.CKA.ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
      (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) Bool)
    (hR : (R.eval (fun _ => A) ()).IsQueryBoundP (· matches .inr _) qOut) :
    CryptoGames.CKA.MakesAtMostQueries
      ((Bundles.compileCkaAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ()) qOut := by
  unfold Bundles.compileCkaAtomic guardRed
  split_ifs with hℓ
  · have hsub := QuerySubsumes.compilePureAuxRed_querySubsumes
      (Bundles.ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (Bundles.ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
      R (Bundles.toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
      (Bundles.fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
      (Bundles.ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
      (ckaPureAuxBundle_samp_querySubsumes ℓ Pt C Dh encPt encT idOf lam B0)
      (fun g z => .of_eq (Bundles.ckaPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
      (fun _ => rfl) (fun _ => rfl)
      (Bundles.fig8AdaptQ_eval_cka ℓ Pt C Dh encPt encT lam)
      (Bundles.fig8AdaptR_eval_cka ℓ Pt C Dh encPt encT lam)
      (fun _ => A) (fun _ => A) id
      (fun _ => .of_eq (id_map A).symm)
      (fun _ => rfl)
      (outEq := id) (fun _ => rfl)
    rw [id_map] at hsub
    exact hsub.isQueryBoundP (fun _ => nofun)
      (CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
        (by rintro (_ | _) <;> rfl) hR)
  · unfold dummyRed
    apply pureRetRed_isQueryBoundP
    · intro; rfl
    · intro _ h; nomatch h

theorem compilePrngAtomic_makesAtMostQueries [Inhabited Pt] (B0 qOut : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
      (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) Bool)
    (hR : (R.eval (fun _ => A) ()).IsQueryBoundP (· matches .inr _) qOut) :
    CryptoGames.PRFPRNG.MakesAtMostQueries
      ((Bundles.compilePrngAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ()) qOut := by
  unfold Bundles.compilePrngAtomic guardRed
  split_ifs with hℓ
  · have hsub := QuerySubsumes.compilePureAuxRed_querySubsumes
      (Bundles.prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (Bundles.ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
      R (Bundles.toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
      (Bundles.fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
      (Bundles.ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
      (prngPureAuxBundle_samp_querySubsumes ℓ Pt C Dh encPt encT idOf lam B0)
      (fun g z => .of_eq (Bundles.prngPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
      (fun _ => rfl) (fun _ => rfl)
      (Bundles.fig8AdaptQ_eval_cka ℓ Pt C Dh encPt encT lam)
      (Bundles.fig8AdaptR_eval_cka ℓ Pt C Dh encPt encT lam)
      (fun _ => A) (fun _ => A) id
      (fun _ => .of_eq (id_map A).symm)
      (fun _ => rfl)
      (outEq := id) (fun _ => rfl)
    rw [id_map] at hsub
    exact hsub.isQueryBoundP (fun _ => nofun)
      (CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
        (by rintro (_ | _) <;> rfl) hR)
  · unfold dummyRed
    apply pureRetRed_isQueryBoundP
    · intro; rfl
    · intro _ h; nomatch h

theorem compileFsAtomic_makesAtMostQueries [Inhabited Pt] (B0 qOut : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
      (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) Bool)
    (hR : CryptoGames.FSAEAD.MakesAtMostQueries (R.eval (fun _ => A) ()) qOut) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((Bundles.compileFsAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ()) qOut := by
  unfold Bundles.compileFsAtomic guardRed
  split_ifs with hℓ
  · have hsub := QuerySubsumes.compilePureAuxRed_querySubsumes
      (Bundles.fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (Bundles.ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
      R (Bundles.toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
      (Bundles.fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
      (Bundles.ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
      (Bundles.fsPureAuxBundle_samp_querySubsumes ℓ Pt C Dh encPt encT idOf lam B0)
      (fun g z => .of_eq (Bundles.fsPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
      (fun _ => rfl) (fun _ => rfl)
      (Bundles.fig8AdaptQ_eval_cka ℓ Pt C Dh encPt encT lam)
      (Bundles.fig8AdaptR_eval_cka ℓ Pt C Dh encPt encT lam)
      (fun _ => A) (fun _ => A) id
      (fun _ => .of_eq (id_map A).symm)
      (fun _ => rfl)
      (outEq := id) (fun _ => rfl)
    rw [id_map] at hsub
    exact hsub.isQueryBoundP (fun _ => nofun)
      (CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
        (by rintro (_ | _) <;> rfl) hR)
  · unfold dummyRed
    apply pureRetRed_isQueryBoundP
    · intro; rfl
    · intro _ h; nomatch h


end CkaWrapper

/-! ## Size bounds and `fig8CostedBounds` instance -/

section EngineSizeParts

open CryptoGames.SM.Construction (Header healEpoch)
open CryptoGames.LibsignalSession (maxForwardJumps)

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS} {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S_cka" => CryptoGames.CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  CryptoGames.CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

private theorem bind_ret_pair_unit_sizeW_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {opS : O'.Op → ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {Γ' : List (Ty S')} {σ : Ty S'} {c : Comp O' I' Γ' σ} {K M : ℕ}
    (hc : Bundles.compSizeW opS sS qS c ≤ K) (hM : K + 5 ≤ M) :
    Bundles.compSizeW opS sS qS (Comp.bind c (Comp.ret (.pair .unit .v0))) ≤ M := by
  simp only [compSizeW_bind, compSizeW_ret, exprSizeW_pair, exprSizeW_unit, exprSizeW_v0]; omega

private theorem samp_bind_ret_pair_unit_sizeW_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {opS : O'.Op → ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {Γ' : List (Ty S')} {s : I'.smp.Samp} {u : Expr O' Γ' (I'.smp.sDom s)}
    {σ : Ty S'} {c : Comp O' I' ((I'.smp.sTy s) :: Γ') σ} {K M : ℕ}
    (hc : Bundles.compSizeW opS sS qS c ≤ K)
    (hM : Bundles.exprSizeW opS u + sS s + K + 6 ≤ M) :
    Bundles.compSizeW opS sS qS
      (Comp.bind (Comp.sample s u) (Comp.bind c (Comp.ret (.pair .unit .v0)))) ≤ M := by
  simp only [compSizeW_bind, compSizeW_sample, compSizeW_ret, exprSizeW_pair, exprSizeW_unit,
    exprSizeW_v0]; omega

private theorem authOut_ret_sizeW_le {O' : Ops S_cka} {ι : Type} {TSpec : OracleSpec ι}
    {I' : Iface S_cka TSpec} {vpT hsT : Ty S_cka}
    (opS : O'.Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (q qep : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hqep : qep ≤ 4096 * q + 100000000) :
    Bundles.compSizeW opS sS qS
      (Comp.ret (I := I') (Γ := [CryptoGames.SM.Engine.esTy vpT hsT, .bool])
        (CryptoGames.SM.Engine.authOutE (q + 1) (2 + 1) mo.policy .v0)) ≤
      20 * bits (ratchetCostBudget q qep) + 1000 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  have h0 := (pureEngineExprs_sizeW_le opS (q + 1) mo.policy
    (Γ' := [CryptoGames.SM.Engine.esTy vpT hsT, .bool]) .v0).1
  have hpolL : mo.policy.tL = mo.tL := rfl
  have hpolS : mo.policy.tStar = mo.tStar := rfl
  rw [hpolL, hpolS] at h0; simp only [exprSizeW_v0] at h0
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtS : bits mo.tStar ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (mo.tL.getD 0) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  simp only [compSizeW_ret]; omega

theorem implEC_sizeW_le_ratchet {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (q qep : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hqep : qep ≤ 4096 * q + 100000000)
    (hhk : HooksSizeBounded ((q + 1) * (maxForwardJumps + 1)) sS qS hk
      (80 * bits (ratchetCostBudget q qep) + 15000) 2000
      (14 * bits (ratchetCostBudget q qep) + 5000)) :
    Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      sS qS
      (CryptoGames.SM.Engine.implEC
        (Γ' := [CryptoGames.SM.Engine.esTy
          (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
          CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E])
        hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1) ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  have h0 := implEC_sizeW_le hk
    (80 * bits (ratchetCostBudget q qep) + 15000) 2000 (14 * bits (ratchetCostBudget q qep) + 5000)
    (q + 1) qep maxForwardJumps mo hhk
    (Γ' := [CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
      CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  simp only [exprSizeW_v0, exprSizeW_v1] at h0
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  have hbm : bits maxForwardJumps ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by unfold maxForwardJumps; omega)
  have hbtS : bits mo.tStar ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (mo.tL.getD 0) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  omega

theorem redCKAAuthProg_size_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redCKAAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤ 10000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthProg]
    refine bind_ret_pair_unit_sizeW_le (initCKAEStateC_sizeW_le B mo (.bool false)) ?_
    simp only [exprSizeW_bool]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksCKAC_sizeBounded B B mo).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 :=
    authOut_ret_sizeW_le _ _ _ q qep mo ht htL1 hqep
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

theorem redCKAPrivProg_size_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redCKAPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, tL, t⟩
  let II := CryptoGames.CKA.ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤ 10000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAPrivProg]
    refine samp_bind_ret_pair_unit_sizeW_le (initCKAEStateC_sizeW_le B mo .v0) ?_
    simp only [Bundles.ckaSampS, exprSizeW_unit, exprSizeW_v0]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAPrivProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksCKAC_sizeBounded B B mo).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAPrivProg]; rw [show (2 : ℕ) + 1 = 3 from rfl]
    refine (privOutC_sizeW_le (O' := OO_cka) (I' := II)
      (vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
      (hsT := @CryptoGames.SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS (q + 1) mo.policy
      (fun {Γ''} => @Comp.sample _ _ _ OO_cka II Γ'' CryptoGames.CKA.CKASamp.bit .unit)
      (Γ' := [CryptoGames.SM.Construction.ckaEsTy, .bool])
      (CryptoGames.SM.Engine.cGsB (CryptoGames.SM.Engine.esG .v0)) .v1 .v0).trans ?_
    have hpolL : mo.policy.tL = tL := rfl; have hpolS : mo.policy.tStar = t := rfl
    rw [hpolL, hpolS]
    simp only [CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.esG, Bundles.ckaSampS,
      compSizeW_sample, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, exprSizeW_unit,
      Nat.reduceAdd]; omega
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

theorem redPRNGAuthProg_size_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redPRNGAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      10 * bits (ratchetCostBudget q qep) + 7000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthProg]
    refine bind_ret_pair_unit_sizeW_le (initPRNGEStateC_sizeW_le B mo (.bool false)) ?_
    have hmS : mo.tStar = t := rfl; rw [hmS]; simp only [exprSizeW_bool]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksPRNGC_sizeBounded B B mo).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 :=
    authOut_ret_sizeW_le _ _ _ q qep mo ht htL1 hqep
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

theorem redPRNGPrivProg_size_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, tL, t⟩
  let II := CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      10 * bits (ratchetCostBudget q qep) + 7000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGPrivProg]
    refine samp_bind_ret_pair_unit_sizeW_le (initPRNGEStateC_sizeW_le B mo .v0) ?_
    have hmS : mo.tStar = t := rfl
    rw [hmS]; simp only [Bundles.ckaSampS, exprSizeW_unit, exprSizeW_v0]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGPrivProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksPRNGC_sizeBounded B B mo).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGPrivProg]; rw [show (2 : ℕ) + 1 = 3 from rfl]
    refine (privOutC_sizeW_le (O' := OO_cka) (I' := II)
      (vpT := @CryptoGames.SM.Construction.prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
      (hsT := @CryptoGames.SM.Construction.prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS (q + 1) mo.policy
      (fun {Γ''} => @Comp.sample _ _ _ OO_cka II Γ'' CryptoGames.CKA.CKASamp.bit .unit)
      (Γ' := [CryptoGames.SM.Construction.prngEsTy, .bool])
      (CryptoGames.SM.Engine.cGsB (CryptoGames.SM.Engine.esG .v0)) .v1 .v0).trans ?_
    have hpolL : mo.policy.tL = tL := rfl; have hpolS : mo.policy.tStar = t := rfl
    rw [hpolL, hpolS]
    simp only [CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.esG, Bundles.ckaSampS,
      compSizeW_sample, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, exprSizeW_unit,
      Nat.reduceAdd]; omega
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

theorem redFSAuthProg_size_le (q qep j t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t) (hj : j < q)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redFSAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps j tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbj : bits j ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      45 * bits (ratchetCostBudget q qep) + 15000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthProg]
    refine bind_ret_pair_unit_sizeW_le (initFSEStateC_sizeW_le B (q + 1) mo j (.bool false)) ?_
    have hmS : mo.tStar = t := rfl; rw [hmS]; simp only [exprSizeW_bool]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksFSC_sizeBounded B (q + 1) B mo j).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤ 20 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthProg]
    simp only [Bundles.ckaSampS, compSizeW_sample, exprSizeW_unit, Nat.reduceAdd]; omega
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

theorem redFSPrivProg_size_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redFSPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, tL, t⟩
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hb0 : bits 0 ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      45 * bits (ratchetCostBudget q qep) + 15000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivProg]
    refine bind_ret_pair_unit_sizeW_le (initFSEStateC_sizeW_le B (q + 1) mo 0 (.bool false)) ?_
    have hmS : mo.tStar = t := rfl; rw [hmS]; simp only [exprSizeW_bool]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksFSC_sizeBounded B (q + 1) B mo 0).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivProg]; rw [show (2 : ℕ) + 1 = 3 from rfl]
    have hpv := (pureEngineExprs_sizeW_le (O' := OO_cka) (Bundles.ckaOpS B)
      (vpT := @CryptoGames.SM.Construction.fsVpTy KC Γ CCoins T I KR RSt K SS RS M E)
      (hsT := @CryptoGames.SM.Construction.fsHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      (q + 1) mo.policy
      (Γ' := [CryptoGames.SM.Construction.fsEsTy KC Γ CCoins T I KR RSt K SS RS M E, .bool]) .v0).2
    have hpolL : mo.policy.tL = tL := rfl; have hpolS : mo.policy.tStar = t := rfl
    rw [hpolL, hpolS] at hpv; dsimp only [mo] at hpv; simp only [exprSizeW_v0] at hpv
    simp only [Bundles.ckaSampS, compSizeW_ite, compSizeW_ret, compSizeW_sample, exprSizeW_v1,
      exprSizeW_unit, Nat.reduceAdd]; omega
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

theorem redFSPrivCoinProg_size_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redFSPrivCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, tL, t⟩
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hb0 : bits 0 ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      45 * bits (ratchetCostBudget q qep) + 15000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivCoinProg]
    refine bind_ret_pair_unit_sizeW_le (initFSEStateC_sizeW_le B (q + 1) mo 0 (.bool false)) ?_
    have hmS : mo.tStar = t := rfl; rw [hmS]; simp only [exprSizeW_bool]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivCoinProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksFSC_sizeBounded B (q + 1) B mo 0).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤ 20 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivCoinProg]
    simp only [Bundles.ckaSampS, compSizeW_sample, exprSizeW_unit, Nat.reduceAdd]; omega
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

end EngineSizeParts

section EngineInstance

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

theorem fig8RedsInst_redCKAAuth_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (t : ℕ) (ht : t < qep + 2) (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAAuth tL t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileCkaAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep _
    (redCKAAuthProg_parts_le q qep t tL ht htL)
    (redCKAAuthProg_size_le q qep t tL ht htL hqep)
    (by rw [CryptoGames.SM.Construction.redCKAAuthProg_totalQueries]; omega)

theorem fig8RedsInst_redPRNGAuth_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (t : ℕ) (ht : t < qep + 2) (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redPRNGAuth tL t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compilePrngAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep _
    (redPRNGAuthProg_parts_le q qep t tL ht htL)
    (redPRNGAuthProg_size_le q qep t tL ht htL hqep)
    (by rw [CryptoGames.SM.Construction.redPRNGAuthProg_totalQueries]; omega)

theorem fig8RedsInst_redFSAuth_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (t : ℕ) (ht : t < qep + 2) (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t) (j : ℕ) (hj : j < q)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSAuth j tL t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileFsAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep _
    (redFSAuthProg_parts_le q qep j t tL ht htL hj)
    (redFSAuthProg_size_le q qep j t tL ht htL hj hqep)
    (by rw [CryptoGames.SM.Construction.redFSAuthProg_totalQueries]; omega)

theorem fig8RedsInst_redCKAPriv_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ) (hi : i < qep + 1) (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) i)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAPriv tL i)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileCkaAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep _
    (redCKAPrivProg_parts_le q qep i tL (by omega) htL)
    (redCKAPrivProg_size_le q qep i tL (by omega) htL hqep)
    (by rw [CryptoGames.SM.Construction.redCKAPrivProg_totalQueries]; omega)

theorem fig8RedsInst_redPRNGPriv_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ) (hi : i < qep + 1) (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) i)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redPRNGPriv tL i)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compilePrngAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep _
    (redPRNGPrivProg_parts_le q qep i tL (by omega) htL)
    (redPRNGPrivProg_size_le q qep i tL (by omega) htL hqep)
    (by rw [CryptoGames.SM.Construction.redPRNGPrivProg_totalQueries]; omega)

theorem fig8RedsInst_redFSPriv_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ) (hi : i < qep + 1) (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) i)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPriv tL i)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileFsAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep _
    (redFSPrivProg_parts_le q qep i tL (by omega) htL)
    (redFSPrivProg_size_le q qep i tL (by omega) htL hqep)
    (by rw [CryptoGames.SM.Construction.redFSPrivProg_totalQueries]; omega)

theorem fig8RedsInst_redFSPrivCoin_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ) (hi : i < qep + 1) (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) i)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPrivCoin tL i)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileFsAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep _
    (redFSPrivCoinProg_parts_le q qep i tL (by omega) htL)
    (redFSPrivCoinProg_size_le q qep i tL (by omega) htL hqep)
    (by rw [CryptoGames.SM.Construction.redFSPrivCoinProg_totalQueries]; omega)

local instance : Inhabited Pt := ⟨0⟩

theorem fig8RedsInst_redCKAAuth_makesAtMostQueries (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.CKA.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAAuth tL t).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  dsimp only [Bundles.fig8RedsInst]
  refine compileCkaAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam _ _ _ A ?_
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (Computational.Proofs.ReductionDsl.SM.RedCKAPotOK.redCKAAuthProg_makesAtMostQueries
      (KC := BitVec 256) (CCoins := BitVec 256) (KR := BitVec 256) (K := BitVec 256)
      (q + 1) ((q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      CryptoGames.LibsignalSession.maxForwardJumps tL t q A hA)

theorem fig8RedsInst_redCKAPriv_makesAtMostQueries (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.CKA.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAPriv tL i).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  dsimp only [Bundles.fig8RedsInst]
  refine compileCkaAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam _ _ _ A ?_
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (Computational.Proofs.ReductionDsl.SM.RedCKAPotOK.redCKAPrivProg_makesAtMostQueries
      (KC := BitVec 256) (CCoins := BitVec 256) (KR := BitVec 256) (K := BitVec 256)
      (q + 1) ((q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      CryptoGames.LibsignalSession.maxForwardJumps tL i q A hA)

theorem fig8RedsInst_redPRNGAuth_makesAtMostQueries (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.PRFPRNG.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redPRNGAuth tL t).eval
        (fun _ => A) ())
      (min (2 + 2 * q) (q + 3)) := by
  dsimp only [Bundles.fig8RedsInst]
  refine compilePrngAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam _ _ _ A ?_
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.redPRNGAuthProg_makesAtMostQueries
      (KC := BitVec 256) (CCoins := BitVec 256) (KR := BitVec 256) (K := BitVec 256)
      (q + 1) ((q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      CryptoGames.LibsignalSession.maxForwardJumps tL t q A hA)

theorem fig8RedsInst_redPRNGPriv_makesAtMostQueries (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.PRFPRNG.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redPRNGPriv tL i).eval
        (fun _ => A) ())
      (min (2 + 2 * q) (min (q + 3) (2 * qep + 2))) := by
  dsimp only [Bundles.fig8RedsInst]
  refine compilePrngAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam _ _ _ A ?_
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (Computational.Proofs.ReductionDsl.SM.RedPRNGPrivQepPotOK.redPRNGPrivProg_makesAtMostQueries
      (KC := BitVec 256) (CCoins := BitVec 256) (KR := BitVec 256) (K := BitVec 256)
      (q + 1) ((q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      CryptoGames.LibsignalSession.maxForwardJumps tL i q A hA)

theorem fig8RedsInst_redFSAuth_makesAtMostQueries (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSAuth j tL t).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  dsimp only [Bundles.fig8RedsInst]
  refine compileFsAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam _ _ _ A ?_
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (Computational.Proofs.ReductionDsl.SM.RedFSPotOK.redFSAuthProg_makesAtMostQueries
      (KC := BitVec 256) (CCoins := BitVec 256) (KR := BitVec 256) (K := BitVec 256)
      (q + 1) ((q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      CryptoGames.LibsignalSession.maxForwardJumps j tL t q A hA)

theorem fig8RedsInst_redFSPriv_makesAtMostQueries (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPriv tL i).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  dsimp only [Bundles.fig8RedsInst]
  refine compileFsAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam _ _ _ A ?_
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (Computational.Proofs.ReductionDsl.SM.RedFSPotOK.redFSPrivProg_makesAtMostQueries
      (KC := BitVec 256) (CCoins := BitVec 256) (KR := BitVec 256) (K := BitVec 256)
      (q + 1) ((q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      CryptoGames.LibsignalSession.maxForwardJumps tL i q A hA)

theorem fig8RedsInst_redFSPrivCoin_makesAtMostQueries (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPrivCoin tL i).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  dsimp only [Bundles.fig8RedsInst]
  refine compileFsAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam _ _ _ A ?_
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (Computational.Proofs.ReductionDsl.SM.RedFSPotOK.redFSPrivCoinProg_makesAtMostQueries
      (KC := BitVec 256) (CCoins := BitVec 256) (KR := BitVec 256) (K := BitVec 256)
      (q + 1) ((q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      CryptoGames.LibsignalSession.maxForwardJumps tL i q A hA)

/-- Discharges `fig8CostedBounds q qep` for `Bundles.fig8RedsInst` when `qep ≤ 4096 * q + 100000000`. -/
theorem fig8RedsInst_bounds (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    CryptoVerification.LibsignalSession.fig8CostedBounds q qep
      (Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q) :=
  ⟨fig8RedsInst_challSim_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q hqep,
    fun i hi => fig8RedsInst_privRedB_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q i hi hqep,
    fun t ht tL htL =>
      fig8RedsInst_redCKAAuth_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q t ht tL htL hqep,
    fun t ht tL htL =>
      fig8RedsInst_redPRNGAuth_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q t ht tL htL hqep,
    fun t ht tL htL j hj =>
      fig8RedsInst_redFSAuth_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q t ht tL htL j hj hqep,
    fun i hi tL htL =>
      fig8RedsInst_redCKAPriv_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q i hi tL htL hqep,
    fun i hi tL htL =>
      fig8RedsInst_redPRNGPriv_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q i hi tL htL hqep,
    fun i hi tL htL =>
      fig8RedsInst_redFSPriv_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q i hi tL htL hqep,
    fun i hi tL htL =>
      fig8RedsInst_redFSPrivCoin_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q i hi tL htL hqep,
    fun t _ tL _ A hA =>
      fig8RedsInst_redCKAAuth_makesAtMostQueries Dh encPt C codec ℓ encT idOf lam qep q tL t A hA,
    fun i _ tL _ A hA =>
      fig8RedsInst_redCKAPriv_makesAtMostQueries Dh encPt C codec ℓ encT idOf lam qep q tL i A hA,
    fun t _ tL _ A hA =>
      fig8RedsInst_redPRNGAuth_makesAtMostQueries Dh encPt C codec ℓ encT idOf lam qep q tL t A hA,
    fun i _ tL _ A hA =>
      fig8RedsInst_redPRNGPriv_makesAtMostQueries Dh encPt C codec ℓ encT idOf lam qep q tL i A hA,
    fun t _ tL _ j _ A hA =>
      fig8RedsInst_redFSAuth_makesAtMostQueries Dh encPt C codec ℓ encT idOf lam qep q j tL t A hA,
    fun i _ tL _ A hA =>
      fig8RedsInst_redFSPriv_makesAtMostQueries Dh encPt C codec ℓ encT idOf lam qep q tL i A hA,
    fun i _ tL _ A hA =>
      fig8RedsInst_redFSPrivCoin_makesAtMostQueries Dh encPt C codec ℓ encT idOf lam qep q tL i A hA⟩

end EngineInstance

end Computational.Proofs.SessionCostedFig8.ProgBounds
