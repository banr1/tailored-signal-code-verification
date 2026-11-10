/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedReds
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperSim
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.QueryTracking.SubSpec
import Computational.Proofs.ReductionDsl.Fig8SourceCosts

/-!
# Paper-Semantics Challenge Simulator Cost Bounds and Shortness Bridges

Cost and query bounds for `challSimDF'PaperProg`, and restricted-query and short-ciphertext
postcondition bridges (`SafePost`) for `redFSAuthDFPaper` and `redFSAuthDFShiftedPaperGen`.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators ENNReal
open ReductionDsl ReductionDsl.Comp OracleSpec OracleComp
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Engine.RedPRNG CryptoGames.SM.Construction
open CryptoGames.SM.Construction.DeliverForge
open Computational.Proofs.ReductionDsl.Fig8SourceCosts
namespace CryptoVerification.LibsignalSession

open ReductionDsl OracleSpec OracleComp CryptoGames CryptoGames.SM CryptoGames.LibsignalSession

section ChallSimDFPaperCost

variable
  {Key St St₂ Msg Coins RCoins C : Type}
  {init : Party → Key → Option St}
  {send : St → Msg → Coins → Option (St × C)}
  {receive : St → C → RCoins → Option (St × ℕ × ℕ × Msg)}
  {eqMsg : Msg → Msg → Bool}
  {eqCt : C → C → Bool}
  {blank : Msg → Msg}
  {injOK : C → Bool}
  {stOK : Party → St → Bool}
  {φ : St → Option St₂}
  {stSort : SM.SMSort}
  {sampKey : ProbComp (Option Key)}
  {sampCoins : ProbComp (Option Coins)}
  {sampRCoins : ProbComp (Option RCoins)}

local notation "S_sm" => SM.smSig Key St St₂ Msg Coins RCoins C
local notation "OO_sm" => SM.smOps init send receive eqMsg eqCt blank injOK stOK φ
local notation "SQ_df" => SM.smQDF Key St St₂ Msg Coins RCoins C

private lemma mCorrAllowedPaperE_cost_le {O' : ReductionDsl.Ops S_sm} (K : ℕ) {Γ}
    (s : ReductionDsl.Expr O' Γ SM.mirrorTy) (p : ReductionDsl.Expr O' Γ .bool) :
    (SM.mCorrAllowedPaperE K s p).cost ≤ s.cost + p.cost + 20 * K + 20 := by
  have hmax34 : max 3 4 = 4 := rfl
  simp only [SM.mCorrAllowedPaperE, SM.mChall, SM.boolEq, SM.posSender, SM.otherE,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, hmax34, Nat.reduceAdd]
  omega

private lemma simTransmitC'DFPaper_cost_le (qep : ℕ) {Γ}
    (s : ReductionDsl.Expr OO_sm Γ SM.mirrorTy)
    (arg : ReductionDsl.Expr OO_sm Γ (.prod .bool (.prod (.base .msg) (.opt (.base .coins))))) :
    (SM.simTransmitC'DFPaper (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) 3 qep s arg).cost ≤
      s.cost + arg.cost + 5 * ReductionDsl.bits qep + 1205 := by
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  let Γ0 : List (ReductionDsl.Ty S_sm) :=
    .prod SM.mirrorTy (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))) :: Γ
  let Γ1 : List (ReductionDsl.Ty S_sm) := .base .ct :: .opt (.base .ct) :: Γ0
  let Γ2 : List (ReductionDsl.Ty S_sm) := SM.mirrorTy :: Γ1
  have hep := mEpMgmtE_cost_le (O' := OO_sm) qep (Γ := Γ1)
    (.fst .v2) (.fst (.snd .v2)) (.bool false)
  have hrec := mRecordE_cost_le (O' := OO_sm) (Γ := Γ2)
    .v0 (.fst (.snd .v3))
    (.pair (.pair (.fst (.snd .v3))
      (.pair (SM.pGet (SM.mEpoch .v0) (.fst (.snd .v3)))
        (.add (SM.pGet (SM.mIdx .v0) (.fst (.snd .v3))) (.nat 1))))
      (.pair (.fst (.snd (.snd .v3))) .v1))
    (.bool false)
  simp only [pGet_cost, mEpoch_cost, mIdx_cost,
    v0_cost, v1_cost, v2_cost, v3_cost, ReductionDsl.Expr.cost, hb1, Nat.reduceAdd] at hep hrec
  simp only [SM.simTransmitC'DFPaper, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, SM.smIfaceDF, Nat.reduceAdd]
  omega
private lemma simChallC'DFPaper_cost_le (qep : ℕ) {Γ}
    (s : ReductionDsl.Expr OO_sm Γ SM.mirrorTy)
    (arg : ReductionDsl.Expr OO_sm Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins)))))) :
    (SM.simChallC'DFPaper (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) 3 qep s arg).cost ≤
      s.cost + arg.cost + 5 * ReductionDsl.bits qep + 1405 := by
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  let Γ0 : List (ReductionDsl.Ty S_sm) :=
    .prod SM.mirrorTy
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))) :: Γ
  let Γ1 : List (ReductionDsl.Ty S_sm) := SM.mirrorTy :: Γ0
  let Γ2 : List (ReductionDsl.Ty S_sm) := .base .ct :: .opt (.base .ct) :: Γ1
  have hep := mEpMgmtE_cost_le (O' := OO_sm) qep (Γ := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.bool false)
  have hsc := mSafeChE_cost_le (O' := OO_sm) (Γ := Γ1) .v0 (.fst (.snd .v1))
  have hrec := mRecordE_cost_le (O' := OO_sm) (Γ := Γ2)
    .v2 (.fst (.snd .v3))
    (.pair (.pair (.fst (.snd .v3))
      (.pair (SM.pGet (SM.mEpoch .v2) (.fst (.snd .v3)))
        (.add (SM.pGet (SM.mIdx .v2) (.fst (.snd .v3))) (.nat 1))))
      (.pair (.ite (SM.mB (.fst .v3)) (.fst (.snd (.snd (.snd .v3)))) (.fst (.snd (.snd .v3))))
        .v0))
    (.bool true)
  simp only [pGet_cost, mEpoch_cost, mIdx_cost, mB_cost,
    v0_cost, v1_cost, v2_cost, v3_cost, ReductionDsl.Expr.cost, hb1, Nat.reduceAdd] at hep hsc hrec
  simp only [SM.simChallC'DFPaper, mB_cost, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, SM.smIfaceDF, Nat.reduceAdd]
  omega

private lemma simDeliverCDF_cost_le (K : ℕ) {Γ}
    (s : ReductionDsl.Expr OO_sm Γ SM.mirrorTy)
    (arg : ReductionDsl.Expr OO_sm Γ (.prod .bool (.base .ct))) :
    (SM.simDeliverCDF (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) K s arg).cost ≤ s.cost + arg.cost + 400 * K + 1000 := by
  let Γ0 : List (ReductionDsl.Ty S_sm) := .prod SM.mirrorTy (.prod .bool (.base .ct)) :: Γ
  let Γ1 : List (ReductionDsl.Ty S_sm) := .prod .nat (.prod .nat (.opt (.base .msg))) ::
    SM.smRrTy Key St St₂ Msg Coins RCoins C :: .opt (SM.smRrTy Key St St₂ Msg Coins RCoins C) :: Γ0
  let Γ2 : List (ReductionDsl.Ty S_sm) := SM.recTy :: Γ1
  have hit := mInTransitE_cost_le (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    K (Γ := Γ1) (.fst .v3) (SM.otherE (.fst (.snd .v3))) (.snd (.snd .v3))
  have hcc := mChallContainsE_cost_le (O' := OO_sm) K (Γ := Γ2) (.fst .v4) (SM.recPos .v0)
  have hacc := mAcceptE_cost_le (O' := OO_sm) K (Γ := Γ2)
    (.fst .v4) (.fst (.snd .v4)) (SM.recPos .v0)
  simp only [otherE_cost, recPos_cost, v0_cost, v3_cost, v4_cost,
    ReductionDsl.Expr.cost, Nat.reduceAdd] at hit hcc hacc
  simp only [SM.simDeliverCDF, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v3_cost, SM.smIfaceDF, Nat.reduceAdd]
  omega

private lemma simInjectCDF_cost_le (K : ℕ) {Γ}
    (s : ReductionDsl.Expr OO_sm Γ SM.mirrorTy)
    (arg : ReductionDsl.Expr OO_sm Γ (.prod .bool (.base .ct))) :
    (SM.simInjectCDF (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) K s arg).cost ≤ s.cost + arg.cost + 250 * K + 900 := by
  let Γ0 : List (ReductionDsl.Ty S_sm) := .prod SM.mirrorTy (.prod .bool (.base .ct)) :: Γ
  let Γ1 : List (ReductionDsl.Ty S_sm) := .prod .nat (.prod .nat (.opt (.base .msg))) ::
    SM.smRrTy Key St St₂ Msg Coins RCoins C :: .opt (SM.smRrTy Key St St₂ Msg Coins RCoins C) :: Γ0
  have hacc := mAcceptE_cost_le (O' := OO_sm) K (Γ := Γ1) (.fst .v3) (.fst (.snd .v3))
    (.pair (SM.otherE (.fst (.snd .v3))) (.pair (.fst .v0) (.fst (.snd .v0))))
  simp only [otherE_cost, v0_cost, v3_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hacc
  simp only [SM.simInjectCDF, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v3_cost, SM.smIfaceDF, Nat.reduceAdd]
  omega

private lemma simCorrCDFPaper_cost_le (K : ℕ) {Γ}
    (s : ReductionDsl.Expr OO_sm Γ SM.mirrorTy) (p : ReductionDsl.Expr OO_sm Γ .bool) :
    (SM.simCorrCDFPaper (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) K s p).cost ≤ s.cost + p.cost + 420 * K + 4100 := by
  let Γ0 : List (ReductionDsl.Ty S_sm) := .prod SM.mirrorTy .bool :: Γ
  let Γ1 : List (ReductionDsl.Ty S_sm) := .opt (.base stSort) :: Γ0
  have hca := mCorrAllowedPaperE_cost_le (O' := OO_sm) K (Γ := Γ0) (.fst .v0) (.snd .v0)
  have hac := mAfterCorrE_cost_le (O' := OO_sm) K (Γ := Γ1) (.fst .v1) (.snd .v1)
  simp only [v0_cost, v1_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hca hac
  simp only [SM.simCorrCDFPaper, isSomeE_cost, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, SM.smIfaceDF, Nat.reduceAdd]
  omega

private lemma simDeliverForgeCDF_cost_le (K : ℕ) {Γ}
    (s : ReductionDsl.Expr OO_sm Γ SM.mirrorTy)
    (arg : ReductionDsl.Expr OO_sm Γ (.prod .bool (.prod (.base .ct) (.base .ct)))) :
    (SM.simDeliverForgeCDF (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) K s arg).cost ≤ s.cost + arg.cost + 250 * K + 900 := by
  let Γ0 : List (ReductionDsl.Ty S_sm) :=
    .prod SM.mirrorTy (.prod .bool (.prod (.base .ct) (.base .ct))) :: Γ
  let Γ1 : List (ReductionDsl.Ty S_sm) := .prod .nat (.prod .nat (.opt (.base .msg))) ::
    SM.smRrTy Key St St₂ Msg Coins RCoins C :: .opt (SM.smRrTy Key St St₂ Msg Coins RCoins C) :: Γ0
  have hacc := mAcceptE_cost_le (O' := OO_sm) K (Γ := Γ1) (.fst .v3) (.fst (.snd .v3))
    (.pair (SM.otherE (.fst (.snd .v3))) (.pair (.fst .v0) (.fst (.snd .v0))))
  simp only [otherE_cost, v0_cost, v3_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hacc
  simp only [SM.simDeliverForgeCDF, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v3_cost, SM.smIfaceDF, Nat.reduceAdd]
  omega

private lemma simHandleC'DFPaper_cost_le (K qep : ℕ) :
    (SM.simHandleC'DFPaper (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K 3 qep).cost ≤ 5 * ReductionDsl.bits qep + 420 * K + 4205 := by
  let trQ : ReductionDsl.Ty S_sm := .prod .bool (.prod (.base .msg) (.opt (.base .coins)))
  let chQ : ReductionDsl.Ty S_sm :=
    .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))
  let dlQ : ReductionDsl.Ty S_sm := .prod .bool (.base .ct)
  let dfQ : ReductionDsl.Ty S_sm := .prod .bool (.prod (.base .ct) (.base .ct))
  let s1 : ReductionDsl.Ty S_sm := .sum (.sum (.sum (.sum trQ chQ) dlQ) dlQ) .bool
  let s2 : ReductionDsl.Ty S_sm := .sum (.sum (.sum trQ chQ) dlQ) dlQ
  let s3 : ReductionDsl.Ty S_sm := .sum (.sum trQ chQ) dlQ
  let s4 : ReductionDsl.Ty S_sm := .sum trQ chQ
  have hb_tr := simTransmitC'DFPaper_cost_le (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
    qep (Γ := trQ :: s4 :: s3 :: s2 :: s1 :: [SM.mirrorTy, SQ_df]) .v5 .v0
  have hb_ch := simChallC'DFPaper_cost_le (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
    qep (Γ := chQ :: s4 :: s3 :: s2 :: s1 :: [SM.mirrorTy, SQ_df]) .v5 .v0
  have hb_dl := simDeliverCDF_cost_le (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
    K (Γ := dlQ :: s3 :: s2 :: s1 :: [SM.mirrorTy, SQ_df]) .v4 .v0
  have hb_ij := simInjectCDF_cost_le (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
    K (Γ := dlQ :: s2 :: s1 :: [SM.mirrorTy, SQ_df]) .v3 .v0
  have hb_cr := simCorrCDFPaper_cost_le (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
    K (Γ := .bool :: s1 :: [SM.mirrorTy, SQ_df]) .v2 .v0
  have hb_df := simDeliverForgeCDF_cost_le (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
    K (Γ := dfQ :: [SM.mirrorTy, SQ_df]) .v1 .v0
  simp only [v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost]
    at hb_tr hb_ch hb_dl hb_ij hb_cr hb_df
  simp only [SM.simHandleC'DFPaper, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, Nat.reduceAdd]
  omega

theorem challSimDF'PaperProg_totalCost_le (q qep : ℕ) :
    (SM.challSimDF'PaperProg (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      q 3 qep).totalCost q ≤
      ratchetCostBudget q qep := by
  have h1 := simHandleC'DFPaper_cost_le (init := init) (send := send) (receive := receive)
    (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
    (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
    q qep
  have hmfj : maxForwardJumps = 25000 := rfl
  rw [SM.challSimDF'PaperProg_totalCost]
  refine add_mul_le_ratchetCostBudget
    (by unfold Computational.Proofs.ReductionDsl.Fig8SourceCosts.fig8StepBound; dsimp only; omega) ?_
  unfold Computational.Proofs.ReductionDsl.Fig8SourceCosts.fig8StepBound
  dsimp only
  omega

end ChallSimDFPaperCost

end CryptoVerification.LibsignalSession
namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Construction.DeliverForge
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC CryptoGames.LibsignalSM.Proofs
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

section ChallSimDFPrimePaper

variable {St Msg Coins C Pub : Type} [DecidableEq C] [DecidableEq Pub]

omit [DecidableEq C] [DecidableEq Pub] in
private lemma queryDF_eq_liftM' (t : (unifSpec + DeliverForge.specDF St Msg Coins C).Domain) :
    (query (spec := unifSpec + DeliverForge.specDF St Msg Coins C) t :
      DeliverForge.AdversaryCompDF St Msg Coins C _) =
      liftM ((unifSpec + DeliverForge.specDF St Msg Coins C).query t) := rfl

private lemma stateT_lift_runDF' {m : Type → Type} [Monad m] {σ α : Type} (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

omit [DecidableEq Pub] in
private lemma isQueryBoundP_simOraclesDF'Paper (Δ qep : ℕ)
    (o : (DeliverForge.specDF St Msg Coins C).Domain) (s : Mirror Msg C) :
    IsQueryBoundP
      ((DeliverForge.simOraclesDF'Paper (St := St) (Coins := Coins) Δ qep o).run s)
      (· matches Sum.inr _) 1 := by
  rcases o with (((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · change IsQueryBoundP ((DeliverForge.simTransmitDF'Paper (St := St) Δ qep (P, msg, r)).run s)
      (· matches Sum.inr _) 1
    unfold DeliverForge.simTransmitDF'Paper DeliverForge.transmitQueryDF
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_runDF', bind_assoc]
    rw [queryDF_eq_liftM', isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res <;> cases s.epMgmt Δ qep P false <;> simp
  · change IsQueryBoundP ((DeliverForge.simChallDF'Paper (St := St) Δ qep (P, m₀, m₁, r)).run s)
      (· matches Sum.inr _) 1
    unfold DeliverForge.simChallDF'Paper DeliverForge.transmitQueryDF
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases s.epMgmt Δ qep P false with
    | none => trivial
    | some s₁ =>
      dsimp only; cases s₁.safeCh Δ P
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure]; trivial
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          stateT_lift_runDF', bind_assoc, pure_bind]
        rw [queryDF_eq_liftM', isQueryBoundP_query_bind_iff]
        refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩; cases res <;> simp
  · change IsQueryBoundP ((DeliverForge.simDeliverDF (St := St) (Coins := Coins) (P, c)).run s)
      (· matches Sum.inr _) 1
    unfold DeliverForge.simDeliverDF DeliverForge.deliverQueryDF
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_runDF', bind_assoc]
    rw [queryDF_eq_liftM', isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res with | none => simp | some rr => cases rr <;> cases s.inTransit P.other c <;> simp
  · change IsQueryBoundP ((DeliverForge.simInjectDF (St := St) (Coins := Coins) (P, c)).run s)
      (· matches Sum.inr _) 1
    unfold DeliverForge.simInjectDF DeliverForge.injectQueryDF
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_runDF', bind_assoc]
    rw [queryDF_eq_liftM', isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res with | none => simp | some rr => cases rr <;> simp
  · change IsQueryBoundP
      ((DeliverForge.simCorrDFPaper (St := St) (Msg := Msg) (Coins := Coins) (C := C) P).run s)
      (· matches Sum.inr _) 1
    unfold DeliverForge.simCorrDFPaper DeliverForge.corrQueryDF
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases s.corrAllowedPaper P
    · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure]; trivial
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        stateT_lift_runDF', bind_assoc, pure_bind]
      rw [queryDF_eq_liftM', isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩; cases res <;> simp
  · change IsQueryBoundP
      ((DeliverForge.simDeliverForgeDF (St := St) (Coins := Coins) (P, c, c')).run s)
      (· matches Sum.inr _) 1
    unfold DeliverForge.simDeliverForgeDF DeliverForge.deliverForgeQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_runDF', bind_assoc]
    rw [queryDF_eq_liftM', isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res with | none => simp | some rr => cases rr <;> simp

omit [DecidableEq Pub] in
theorem challSimDF'Paper_queries (Δ qep : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) {q : ℕ}
    (hq : DeliverForge.MakesAtMostQueriesDF B q) :
    DeliverForge.MakesAtMostQueriesDF (DeliverForge.challSimDF'Paper Δ qep B) q := by
  unfold DeliverForge.MakesAtMostQueriesDF DeliverForge.challSimDF'Paper
  have hb : IsQueryBoundP
      (liftM ($ᵗ Bool : ProbComp Bool) : DeliverForge.AdversaryCompDF St Msg Coins C Bool)
      (· matches Sum.inr _) 0 :=
    IsQueryBoundP.liftComp_subSpec (p := fun _ => False)
      (fun _ => ⟨False.elim, fun h => by nomatch h⟩)
      (ReductionsQueries.isQueryBoundP_false ($ᵗ Bool) 0)
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind hb fun b _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (DeliverForge.simImplDF'Paper (St := St) (Coins := Coins) Δ qep) B).run
        ({ st := fun _ => (), b } : Mirror Msg C))
      (· matches Sum.inr _) q := by
    refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ _
    · rintro (n | o) hp s
      · cases hp
      · exact isQueryBoundP_simOraclesDF'Paper Δ qep o s
    · rintro (n | o) hnp s
      · change IsQueryBoundP
          ((DeliverForge.simCoinsDF (St := St) (Msg := Msg) (Coins := Coins) (C := C) n).run s)
          (· matches Sum.inr _) 0
        unfold DeliverForge.simCoinsDF
        simp only [stateT_lift_runDF']
        rw [queryDF_eq_liftM', isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by rintro ⟨⟩), fun u => by simp⟩
      · exact absurd rfl hnp
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

theorem challSimDF'Paper_equalPub (Δ qep : ℕ) (pubOf : Msg → Pub)
    (B : DeliverForge.AdversaryDF St Msg Coins C) :
    EqualPubChallsDF pubOf (DeliverForge.challSimDF'Paper Δ qep B) := by
  let Q := fun t : (unifSpec + DeliverForge.specDF St Msg Coins C).Domain =>
    unequalPubChallDF (St := St) (Coins := Coins) (C := C) pubOf t = true
  unfold EqualPubChallsDF DeliverForge.challSimDF'Paper
  refine RestrictedReds.SafePost.to_isQueryBoundP (P := fun _ => True) ?_
  refine (RestrictedReds.SafePost.liftComp_unif (fun _ h => by nomatch h) ($ᵗ Bool)).bind
    fun b _ => ?_
  rw [StateT.run'_eq, map_eq_bind_pure_comp]
  have hstep : ∀ t : (unifSpec + DeliverForge.specDF St Msg Coins C).Domain, ¬ (fun _ => False) t →
      RestrictedReds.SafeS Q (fun _ : Mirror Msg C => True) (fun _ _ => True)
        (DeliverForge.simImplDF'Paper (St := St) Δ qep t) := by
    rintro (n | ((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩) _
    · exact RestrictedReds.safeS_lift_query (by simp [Q, unequalPubChallDF])
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simTransmitDF'Paper Δ qep (P, msg, r))
      unfold DeliverForge.simTransmitDF'Paper DeliverForge.transmitQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, unequalPubChallDF]) fun res => ?_
      cases res <;> cases s.epMgmt Δ qep P false
      all_goals first
        | exact RestrictedReds.safeS_pure_true _
        | exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simChallDF'Paper Δ qep (P, m₀, m₁, r))
      unfold DeliverForge.simChallDF'Paper DeliverForge.transmitQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      cases s.epMgmt Δ qep P false with
      | none => exact RestrictedReds.safeS_pure_true _
      | some s₁ =>
        dsimp only; cases s₁.safeCh Δ P
        · exact RestrictedReds.safeS_pure_true _
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          refine RestrictedReds.safeS_bind_query (by simp [Q, unequalPubChallDF]) fun res => ?_
          cases res
          · exact RestrictedReds.safeS_pure_true _
          · exact RestrictedReds.safeS_bind_true
              (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
              fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simDeliverDF (P, c))
      unfold DeliverForge.simDeliverDF DeliverForge.deliverQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, unequalPubChallDF]) fun res => ?_
      cases res with
      | none => exact RestrictedReds.safeS_pure_true _
      | some rr =>
        cases rr <;> cases s.inTransit P.other c
        all_goals first
          | exact RestrictedReds.safeS_pure_true _
          | exact RestrictedReds.safeS_bind_true
              (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
              fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simInjectDF (P, c))
      unfold DeliverForge.simInjectDF DeliverForge.injectQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, unequalPubChallDF]) fun res => ?_
      cases res with
      | none => exact RestrictedReds.safeS_pure_true _
      | some rr =>
        cases rr
        · exact RestrictedReds.safeS_pure_true _
        · exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simCorrDFPaper P)
      unfold DeliverForge.simCorrDFPaper DeliverForge.corrQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      cases s.corrAllowedPaper P
      · exact RestrictedReds.safeS_pure_true _
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine RestrictedReds.safeS_bind_query (by simp [Q, unequalPubChallDF]) fun res => ?_
        cases res
        · exact RestrictedReds.safeS_pure_true _
        · exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simDeliverForgeDF (P, c, c'))
      unfold DeliverForge.simDeliverForgeDF DeliverForge.deliverForgeQuery
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, unequalPubChallDF]) fun res => ?_
      cases res with
      | none => exact RestrictedReds.safeS_pure_true _
      | some rr =>
        cases rr
        · exact RestrictedReds.safeS_pure_true _
        · exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
  exact (RestrictedReds.SafePost.simulateQ_run
    (RestrictedReds.SafePost.true_of_false B) hstep trivial).bind
    fun _ _ => RestrictedReds.SafePost.pure trivial

omit [DecidableEq Pub] in
theorem challSimDF'Paper_sendOk (Δ qep : ℕ) (ok : Msg → Bool)
    (B : DeliverForge.AdversaryDF St Msg Coins C) (hB : SendMsgsOkDF ok B) :
    SendMsgsOkDF ok (DeliverForge.challSimDF'Paper Δ qep B) := by
  let Q := fun t : (unifSpec + DeliverForge.specDF St Msg Coins C).Domain =>
    badSendMsgDF (St := St) (Coins := Coins) (C := C) ok t = true
  unfold SendMsgsOkDF DeliverForge.challSimDF'Paper
  refine RestrictedReds.SafePost.to_isQueryBoundP (P := fun _ => True) ?_
  refine (RestrictedReds.SafePost.liftComp_unif (fun _ h => by nomatch h) ($ᵗ Bool)).bind
    fun b _ => ?_
  rw [StateT.run'_eq, map_eq_bind_pure_comp]
  have hstep : ∀ t, ¬ Q t →
      RestrictedReds.SafeS Q (fun _ : Mirror Msg C => True) (fun _ _ => True)
        (DeliverForge.simImplDF'Paper Δ qep t) := by
    rintro (n | ((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩) hpt
    · exact RestrictedReds.safeS_lift_query (by simp [Q, badSendMsgDF])
    · have hmsg : ok msg = true := by simpa [Q, badSendMsgDF] using hpt
      change RestrictedReds.SafeS Q _ _ (DeliverForge.simTransmitDF'Paper Δ qep (P, msg, r))
      unfold DeliverForge.simTransmitDF'Paper DeliverForge.transmitQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, badSendMsgDF, hmsg]) fun res => ?_
      cases res <;> cases s.epMgmt Δ qep P false
      all_goals first
        | exact RestrictedReds.safeS_pure_true _
        | exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
    · have hm : ok m₀ = true ∧ ok m₁ = true := by
        simpa [Q, badSendMsgDF, Bool.or_eq_true] using hpt
      change RestrictedReds.SafeS Q _ _ (DeliverForge.simChallDF'Paper Δ qep (P, m₀, m₁, r))
      unfold DeliverForge.simChallDF'Paper DeliverForge.transmitQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      cases s.epMgmt Δ qep P false with
      | none => exact RestrictedReds.safeS_pure_true _
      | some s₁ =>
        dsimp only; cases s₁.safeCh Δ P
        · exact RestrictedReds.safeS_pure_true _
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have hmb : ok (if s.b then m₁ else m₀) = true := by
            split_ifs <;> simp [hm.1, hm.2]
          refine RestrictedReds.safeS_bind_query (by simp [Q, badSendMsgDF, hmb]) fun res => ?_
          cases res
          · exact RestrictedReds.safeS_pure_true _
          · exact RestrictedReds.safeS_bind_true
              (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
              fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simDeliverDF (P, c))
      unfold DeliverForge.simDeliverDF DeliverForge.deliverQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, badSendMsgDF]) fun res => ?_
      cases res with
      | none => exact RestrictedReds.safeS_pure_true _
      | some rr =>
        cases rr <;> cases s.inTransit P.other c
        all_goals first
          | exact RestrictedReds.safeS_pure_true _
          | exact RestrictedReds.safeS_bind_true
              (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
              fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simInjectDF (P, c))
      unfold DeliverForge.simInjectDF DeliverForge.injectQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, badSendMsgDF]) fun res => ?_
      cases res with
      | none => exact RestrictedReds.safeS_pure_true _
      | some rr =>
        cases rr
        · exact RestrictedReds.safeS_pure_true _
        · exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simCorrDFPaper P)
      unfold DeliverForge.simCorrDFPaper DeliverForge.corrQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      cases s.corrAllowedPaper P
      · exact RestrictedReds.safeS_pure_true _
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine RestrictedReds.safeS_bind_query (by simp [Q, badSendMsgDF]) fun res => ?_
        cases res
        · exact RestrictedReds.safeS_pure_true _
        · exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simDeliverForgeDF (P, c, c'))
      unfold DeliverForge.simDeliverForgeDF DeliverForge.deliverForgeQuery
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, badSendMsgDF]) fun res => ?_
      cases res with
      | none => exact RestrictedReds.safeS_pure_true _
      | some rr =>
        cases rr
        · exact RestrictedReds.safeS_pure_true _
        · exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
  exact (RestrictedReds.SafePost.simulateQ_run
    (RestrictedReds.SafePost.of_isQueryBoundP hB) hstep trivial).bind
    fun _ _ => RestrictedReds.SafePost.pure trivial

end ChallSimDFPrimePaper

section RedFSAuthDFPaperFsOk

open ReductionsQueries

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E Pub : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [DecidableEq Pub] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K]

private theorem safeS_corrEPaper_of_reveal
    {Q : (RSpec SS RS T M E).Domain → Prop} {mo : Mode}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka j : ℕ) (π : Policy)
    (hrev : ∀ ctx P vp,
      RestrictedReds.SafeS Q
        (RestrictedReds.InvFS (T := T) (Sig := Sig) (K := K) (I := I)
          (SS := SS) (RS := RS) (E := E) mo.tStar)
        (fun _ s => RestrictedReds.InvFS mo.tStar s)
        ((hooksFS cka prng fs Δcka mo j).reveal ctx P vp))
    (P : Party) :
    RestrictedReds.SafeS Q
      (RestrictedReds.InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I)
        (SS := SS) (RS := RS) (M := M) (E := E) mo.tStar)
      (fun _ es => RestrictedReds.InvE mo.tStar es)
      (DeliverForge.corrEPaper (hooksFS cka prng fs Δcka mo j) π P) := by
  unfold DeliverForge.corrEPaper
  refine RestrictedReds.safeS_get_bind fun es hes => ?_
  by_cases h1 : (es.abort || es.g.win || !es.g.corrAllowedPaper P) = true
  · simp only [h1, ↓reduceIte]; exact RestrictedReds.safeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P) = true
    · simp only [h2, ↓reduceIte]
      exact RestrictedReds.safeS_bind_true (RestrictedReds.safeS_abortE (mo := mo))
        fun _ => RestrictedReds.safeS_pure_true none
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      refine RestrictedReds.safeS_bind_true
        (RestrictedReds.safeS_liftH_true (mo := mo) (hrev es.g P (es.g.st P)))
        fun res => ?_
      cases res with
      | none =>
        exact RestrictedReds.safeS_bind_true (RestrictedReds.safeS_abortE (mo := mo))
          fun _ => RestrictedReds.safeS_pure_true none
      | some st =>
        exact RestrictedReds.safeS_bind_true
          (RestrictedReds.safeS_modify_true _ fun _ h => ⟨hes.vp, h.fs⟩)
          fun _ => RestrictedReds.safeS_pure_true (some st)

private theorem safeS_corrEShiftedPaper_of_reveal
    {Q : (RSpec SS RS T M E).Domain → Prop} {mo : Mode}
    (l : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka j : ℕ) (π : Policy)
    (hrev : ∀ ctx P vp,
      RestrictedReds.SafeS Q
        (RestrictedReds.InvFS (T := T) (Sig := Sig) (K := K) (I := I)
          (SS := SS) (RS := RS) (E := E) mo.tStar)
        (fun _ s => RestrictedReds.InvFS mo.tStar s)
        ((hooksFS cka prng fs Δcka mo j).reveal ctx P vp))
    (P : Party) :
    RestrictedReds.SafeS Q
      (RestrictedReds.InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I)
        (SS := SS) (RS := RS) (M := M) (E := E) mo.tStar)
      (fun _ es => RestrictedReds.InvE mo.tStar es)
      (DeliverForge.corrEShiftedPaper l (hooksFS cka prng fs Δcka mo j) π P) := by
  unfold DeliverForge.corrEShiftedPaper
  refine RestrictedReds.safeS_get_bind fun es hes => ?_
  by_cases h1 : (es.abort || es.g.win || !es.g.corrAllowedPaper P) = true
  · simp only [h1, ↓reduceIte]; exact RestrictedReds.safeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 :
        (π.leakDoom es.g (DeliverForge.afterCorrShifted l es.g P) || π.corrDoom es.g P) = true
    · simp only [h2, ↓reduceIte]
      exact RestrictedReds.safeS_bind_true (RestrictedReds.safeS_abortE (mo := mo))
        fun _ => RestrictedReds.safeS_pure_true none
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      refine RestrictedReds.safeS_bind_true
        (RestrictedReds.safeS_liftH_true (mo := mo) (hrev es.g P (es.g.st P)))
        fun res => ?_
      cases res with
      | none =>
        exact RestrictedReds.safeS_bind_true (RestrictedReds.safeS_abortE (mo := mo))
          fun _ => RestrictedReds.safeS_pure_true none
      | some st =>
        exact RestrictedReds.safeS_bind_true
          (RestrictedReds.safeS_modify_true _ fun _ h => ⟨hes.vp, h.fs⟩)
          fun _ => RestrictedReds.safeS_pure_true (some st)

private theorem safeS_transmitE_of_vSend
    {Q : (RSpec SS RS T M E).Domain → Prop} {mo : Mode}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep j : ℕ) (π : Policy)
    (q : Party × M × Option CCoins)
    (hvSend : ∀ ctx P s, RestrictedReds.InvVP mo.tStar s →
      RestrictedReds.SafeS Q
        (RestrictedReds.InvFS (T := T) (Sig := Sig) (K := K) (I := I)
          (SS := SS) (RS := RS) (E := E) mo.tStar)
        (fun res s' => (∀ vp' c, res = some (vp', c) → RestrictedReds.InvVP mo.tStar vp') ∧
          RestrictedReds.InvFS mo.tStar s')
        (vSend (hooksFS cka prng fs Δcka mo j) ctx P s q.2.1 none q.2.2)) :
    RestrictedReds.SafeS Q
      (RestrictedReds.InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I)
        (SS := SS) (RS := RS) (M := M) (E := E) mo.tStar)
      (fun _ es => RestrictedReds.InvE mo.tStar es)
      (transmitE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep π q) := by
  rcases q with ⟨P, m, r⟩; unfold transmitE
  refine RestrictedReds.safeS_get_bind fun es hes => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]; exact RestrictedReds.safeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact RestrictedReds.safeS_pure_true none
    | some s₁ =>
      have hst₁ : ∀ P', RestrictedReds.InvVP mo.tStar (s₁.st P') := by
        rw [RestrictedReds.epMgmt_st (2 + Δcka) qep hep]; exact hes.vp
      by_cases h2 : π.leakDoom es.g s₁ = true
      · simp only [h2, ↓reduceIte]
        exact RestrictedReds.safeS_bind_true (RestrictedReds.safeS_abortE (mo := mo))
          fun _ => RestrictedReds.safeS_pure_true none
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        refine RestrictedReds.safeS_bind_and
          (RestrictedReds.safeS_liftH_and (mo := mo) (hvSend s₁ P (s₁.st P) (hst₁ P)))
          fun res hres => ?_
        rcases res with _ | ⟨st', c⟩
        · exact RestrictedReds.safeS_bind_true (RestrictedReds.safeS_abortE (mo := mo))
            fun _ => RestrictedReds.safeS_pure_true none
        · exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_modify_true _ fun _ h =>
              ⟨RestrictedReds.invVP_record (2 + Δcka) hst₁ P (hres st' c rfl) _ false, h.fs⟩)
            fun _ => RestrictedReds.safeS_pure_true (some c)

private theorem safeS_challE_of_vSend
    {Q : (RSpec SS RS T M E).Domain → Prop} {mo : Mode}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep j : ℕ) (cfg : SM.Config M) (π : Policy)
    (q : Party × M × M × Option CCoins)
    (hvSend : ∀ ctx P s m, RestrictedReds.InvVP mo.tStar s →
      RestrictedReds.SafeS Q
        (RestrictedReds.InvFS (T := T) (Sig := Sig) (K := K) (I := I)
          (SS := SS) (RS := RS) (E := E) mo.tStar)
        (fun res s' => (∀ vp' c, res = some (vp', c) → RestrictedReds.InvVP mo.tStar vp') ∧
          RestrictedReds.InvFS mo.tStar s')
        (vSend (hooksFS cka prng fs Δcka mo j) ctx P s m (some (q.2.1, q.2.2.1)) q.2.2.2)) :
    RestrictedReds.SafeS Q
      (RestrictedReds.InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I)
        (SS := SS) (RS := RS) (M := M) (E := E) mo.tStar)
      (fun _ es => RestrictedReds.InvE mo.tStar es)
      (challE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep cfg π q) := by
  rcases q with ⟨P, m₀, m₁, r⟩; unfold challE
  refine RestrictedReds.safeS_get_bind fun es hes => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]; exact RestrictedReds.safeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact RestrictedReds.safeS_pure_true none
    | some s₁ =>
      have hst₁ : ∀ P', RestrictedReds.InvVP mo.tStar (s₁.st P') := by
        rw [RestrictedReds.epMgmt_st (2 + Δcka) qep hep]; exact hes.vp
      by_cases h2 : (!s₁.safeCh (2 + Δcka) P || !cfg.challAllowedIn (s₁.epoch P)) = true
      · simp only [h2, ↓reduceIte]; exact RestrictedReds.safeS_pure_true none
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : π.leakDoom es.g s₁ = true
        · simp only [h3, ↓reduceIte]
          exact RestrictedReds.safeS_bind_true (RestrictedReds.safeS_abortE (mo := mo))
            fun _ => RestrictedReds.safeS_pure_true none
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          refine RestrictedReds.safeS_bind_and
            (RestrictedReds.safeS_liftH_and (mo := mo) (hvSend s₁ P (s₁.st P) _ (hst₁ P)))
            fun res hres => ?_
          rcases res with _ | ⟨st', c⟩
          · exact RestrictedReds.safeS_bind_true (RestrictedReds.safeS_abortE (mo := mo))
              fun _ => RestrictedReds.safeS_pure_true none
          · exact RestrictedReds.safeS_bind_true
              (RestrictedReds.safeS_modify_true _ fun _ h =>
                ⟨RestrictedReds.invVP_record (2 + Δcka) hst₁ P (hres st' c rfl) _ true, h.fs⟩)
              fun _ => RestrictedReds.safeS_pure_true (some c)

variable [SampleableType KR] [SampleableType KC]

private theorem safeS_deliverE_of_vRecv
    {Q : (RSpec SS RS T M E).Domain → Prop} {mo : Mode}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka j : ℕ) (cfg : SM.Config M)
    (q : Party × (Header T × E))
    (hvRecv : ∀ ctx P s, RestrictedReds.InvVP mo.tStar s → ∀ c rec,
      RestrictedReds.SafeS Q
        (RestrictedReds.InvFS (T := T) (Sig := Sig) (K := K) (I := I)
          (SS := SS) (RS := RS) (E := E) mo.tStar)
        (fun res s' => (∀ vp' t' i' m', res = some (some (vp', t', i', m')) →
          RestrictedReds.InvVP mo.tStar vp') ∧ RestrictedReds.InvFS mo.tStar s')
        (vRecv (hooksFS cka prng fs Δcka mo j) ctx P s c rec)) :
    RestrictedReds.SafeS Q
      (RestrictedReds.InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I)
        (SS := SS) (RS := RS) (M := M) (E := E) mo.tStar)
      (fun _ es => RestrictedReds.InvE mo.tStar es)
      (deliverE (hooksFS cka prng fs Δcka mo j) fs.maxSkip cfg q) := by
  rcases q with ⟨P, c⟩; unfold deliverE
  refine RestrictedReds.safeS_get_bind fun es hes => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]; exact RestrictedReds.safeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.inTransit P.other c with
    | none => exact RestrictedReds.safeS_pure_true none
    | some r =>
      refine RestrictedReds.safeS_bind_and
        (RestrictedReds.safeS_liftH_and (mo := mo)
          (hvRecv es.g P (es.g.st P) (hes.vp P) c (some r)))
        fun res hres => ?_
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · exact RestrictedReds.safeS_bind_true (RestrictedReds.safeS_abortE (mo := mo))
          fun _ => RestrictedReds.safeS_pure_true none
      · by_cases h2 : (cfg.deliverWin && es.g.mustBeCorrect fs.maxSkip P r) = true
        · simp only [h2, ↓reduceIte]
          exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_modify_true _ fun _ h => ⟨h.vp, h.fs⟩)
            fun _ => RestrictedReds.safeS_pure_true (some RecvResult.rejected)
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          exact RestrictedReds.safeS_pure_true (some RecvResult.rejected)
      · refine RestrictedReds.safeS_bind_and
          (RestrictedReds.safeS_commitE cka prng fs Δcka j es.g hes.vp P (es.g.st P)
            st' (hres st' t' i' m' rfl) r.pos)
          fun s₁? hs₁? => ?_
        rcases s₁? with _ | s₁
        · exact RestrictedReds.safeS_pure_true none
        · exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_modify_true _ fun _ h' =>
              ⟨fun P' => by split_ifs <;> exact hs₁? s₁ rfl P', h'.fs⟩)
            fun _ => RestrictedReds.safeS_pure_true _

private theorem safeS_injectE_of_vRecv
    {Q : (RSpec SS RS T M E).Domain → Prop} {mo : Mode} {b1 : Bool} {tStar : ℕ}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep j : ℕ) (cfg : SM.Config M)
    (q : Party × (Header T × E))
    (hvRecv : ∀ ctx P s, RestrictedReds.InvVP mo.tStar s → ∀ c rec,
      RestrictedReds.SafeS Q
        (RestrictedReds.InvFS (T := T) (Sig := Sig) (K := K) (I := I)
          (SS := SS) (RS := RS) (E := E) mo.tStar)
        (fun res s' => (∀ vp' t' i' m', res = some (some (vp', t', i', m')) →
          RestrictedReds.InvVP mo.tStar vp') ∧ RestrictedReds.InvFS mo.tStar s')
        (vRecv (hooksFS cka prng fs Δcka mo j) ctx P s c rec)) :
    RestrictedReds.SafeS Q
      (RestrictedReds.InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I)
        (SS := SS) (RS := RS) (M := M) (E := E) mo.tStar)
      (fun _ es => RestrictedReds.InvE mo.tStar es)
      (injectEGen b1 (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep tStar cfg q) := by
  rcases q with ⟨P, c⟩
  cases b1 <;> [unfold injectEGen injectE; unfold injectEGen DeliverForge.injectEB1]
  all_goals
    dsimp only
    refine RestrictedReds.safeS_get_bind fun es hes => ?_
    split_ifs with h1
    · exact RestrictedReds.safeS_pure_true none
    · refine RestrictedReds.safeS_bind_and
        (RestrictedReds.safeS_liftH_and (mo := mo) (hvRecv es.g P (es.g.st P) (hes.vp P) c none))
        fun res hres => ?_
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · exact RestrictedReds.safeS_bind_true (RestrictedReds.safeS_abortE (mo := mo))
          fun _ => RestrictedReds.safeS_pure_true none
      · exact RestrictedReds.safeS_pure_true (some RecvResult.rejected)
      · by_cases h2 : qep + 1 < t'
        · simp only [h2, ↓reduceIte]
          exact RestrictedReds.safeS_pure_true (some RecvResult.rejected)
        · simp only [h2, ↓reduceIte]
          split_ifs
          · refine RestrictedReds.safeS_bind_and
              (RestrictedReds.safeS_commitE cka prng fs Δcka j es.g hes.vp P (es.g.st P)
                st' (hres st' t' i' m' rfl) ⟨P.other, t', i'⟩)
              fun s₁? hs₁? => ?_
            rcases s₁? with _ | s₁
            · exact RestrictedReds.safeS_pure_true none
            · exact RestrictedReds.safeS_bind_true
                (RestrictedReds.safeS_modify_true _ fun _ h' => ⟨hs₁? s₁ rfl, h'.fs⟩)
                fun _ => RestrictedReds.safeS_pure_true _
          · exact RestrictedReds.safeS_bind_true
              (RestrictedReds.safeS_modify_true _ fun _ h => ⟨h.vp, h.fs⟩)
              fun _ => RestrictedReds.safeS_pure_true (some RecvResult.rejected)
          · exact RestrictedReds.safeS_pure_true (some RecvResult.rejected)

private theorem safeS_deliverForgeE_of_vRecv
    {Q : (RSpec SS RS T M E).Domain → Prop} {mo : Mode} {b1 : Bool} {tStar : ℕ}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep j : ℕ) (cfg : SM.Config M)
    (q : Party × (Header T × E) × (Header T × E))
    (hvRecv : ∀ ctx P s, RestrictedReds.InvVP mo.tStar s → ∀ c rec,
      RestrictedReds.SafeS Q
        (RestrictedReds.InvFS (T := T) (Sig := Sig) (K := K) (I := I)
          (SS := SS) (RS := RS) (E := E) mo.tStar)
        (fun res s' => (∀ vp' t' i' m', res = some (some (vp', t', i', m')) →
          RestrictedReds.InvVP mo.tStar vp') ∧ RestrictedReds.InvFS mo.tStar s')
        (vRecv (hooksFS cka prng fs Δcka mo j) ctx P s c rec)) :
    RestrictedReds.SafeS Q
      (RestrictedReds.InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I)
        (SS := SS) (RS := RS) (M := M) (E := E) mo.tStar)
      (fun _ es => RestrictedReds.InvE mo.tStar es)
      (deliverForgeEGen b1 (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep tStar cfg q) := by
  rcases q with ⟨P, c, c'⟩
  cases b1 <;> [unfold deliverForgeEGen DeliverForge.deliverForgeE;
    unfold deliverForgeEGen DeliverForge.deliverForgeEB1]
  all_goals
    dsimp only
    refine RestrictedReds.safeS_get_bind fun es hes => ?_
    by_cases h1 : (es.abort || es.g.win) = true
    · simp only [h1, ↓reduceIte]; exact RestrictedReds.safeS_pure_true none
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      cases es.g.inTransit P.other c with
      | none => exact RestrictedReds.safeS_pure_true none
      | some r =>
        by_cases h2 :
            ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
        · simp only [h2, ↓reduceIte]; exact RestrictedReds.safeS_pure_true none
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          refine RestrictedReds.safeS_bind_and
            (RestrictedReds.safeS_liftH_and (mo := mo)
              (hvRecv es.g P (es.g.st P) (hes.vp P) c' none))
            fun res hres => ?_
          rcases res with _ | (_ | ⟨st', t', i', m'⟩)
          · exact RestrictedReds.safeS_bind_true (RestrictedReds.safeS_abortE (mo := mo))
              fun _ => RestrictedReds.safeS_pure_true none
          · exact RestrictedReds.safeS_pure_true (some RecvResult.rejected)
          · by_cases h3 : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
            · simp only [h3, ↓reduceIte]
              exact RestrictedReds.safeS_pure_true (some RecvResult.rejected)
            · simp only [h3, Bool.false_eq_true, ↓reduceIte]
              split_ifs
              · refine RestrictedReds.safeS_bind_and
                  (RestrictedReds.safeS_commitE cka prng fs Δcka j es.g hes.vp P (es.g.st P)
                     st' (hres st' t' i' m' rfl) ⟨P.other, t', i'⟩)
                  fun s₁? hs₁? => ?_
                rcases s₁? with _ | s₁
                · exact RestrictedReds.safeS_pure_true none
                · exact RestrictedReds.safeS_bind_true
                    (RestrictedReds.safeS_modify_true _ fun _ h' => ⟨hs₁? s₁ rfl, h'.fs⟩)
                    fun _ => RestrictedReds.safeS_pure_true _
              · exact RestrictedReds.safeS_bind_true
                  (RestrictedReds.safeS_modify_true _ fun _ h => ⟨h.vp, h.fs⟩)
                  fun _ => RestrictedReds.safeS_pure_true (some RecvResult.rejected)
              · exact RestrictedReds.safeS_pure_true (some RecvResult.rejected)

theorem safePost_redFSAuthDFPaper_restricted
    {Q : (RSpec SS RS T M E).Domain → Prop} {pubOf : M → Pub}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j : ℕ)
    (tL : Option ℕ) (tStar : ℕ)
    (hQ : RestrictedReds.ValidQ (SS := SS) (RS := RS) (E := E) Q ⟨true, tL, tStar⟩ pubOf)
    (B : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (heq : EqualPubChallsDF pubOf B) :
    RestrictedReds.SafePost Q (fun _ => True)
      (DeliverForge.redFSAuthDFPaper cka prng fs lam Δcka qep j tL tStar B) := by
  let mo : Mode := ⟨true, tL, tStar⟩
  unfold DeliverForge.redFSAuthDFPaper DeliverForge.engRunDFPaper; dsimp only
  refine RestrictedReds.SafePost.bind (P := fun _ => True) ?_
    fun _ _ => RestrictedReds.safePost_sampleT hQ Bool
  refine (RestrictedReds.safeS_initFS hQ cka prng fs lam j {}
      (RestrictedReds.invFS_empty mo.tStar)).bind fun p hp => ?_
  rcases p with ⟨_ | ⟨vA, vB⟩, h⟩
  · exact RestrictedReds.SafePost.pure trivial
  · rcases hp.1 vA vB rfl with ⟨hvA, hvB⟩
    refine RestrictedReds.SafePost.bind (P := fun r => RestrictedReds.InvE mo.tStar r.2)
      (RestrictedReds.SafePost.simulateQ_run
        (RestrictedReds.SafePost.of_isQueryBoundP heq) (fun q hpt => ?_)
        ⟨fun P => by cases P <;> assumption, hp.2⟩)
      fun _ _ => RestrictedReds.SafePost.pure trivial
    rcases q with u | (t | qdf)
    · exact RestrictedReds.safeS_coinsE hQ u
    · rcases t with ((((q | q) | q) | q) | P)
      · exact RestrictedReds.safeS_transmitE hQ cka prng fs Δcka qep j q
      · exact RestrictedReds.safeS_challE hQ cka prng fs Δcka qep j q
          (by simpa [unequalPubChallDF] using hpt)
      · exact RestrictedReds.safeS_deliverE hQ cka prng fs Δcka j q
      · exact RestrictedReds.safeS_injectE hQ cka prng fs Δcka qep j q
      · exact safeS_corrEPaper_of_reveal cka prng fs Δcka j mo.policy
          (RestrictedReds.safeS_reveal hQ cka prng fs Δcka j) P
    · exact safeS_deliverForgeE_of_vRecv (b1 := false) (tStar := 0)
        cka prng fs Δcka qep j mo.cfg qdf
        fun ctx P s hs => RestrictedReds.safeS_vRecv hQ cka prng fs Δcka j ctx P s hs

theorem safePost_redFSAuthDFPaper_short
    {Q : (RSpec SS RS T M E).Domain → Prop} {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j : ℕ)
    (tL : Option ℕ) (tStar : ℕ)
    (hQ : Proofs.SessionShort.FSAEADRed.ValidQ (SS := SS) (RS := RS) (E := E) Q
      ⟨true, tL, tStar⟩ ok)
    (B : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (hok : SendMsgsOkDF ok B) :
    RestrictedReds.SafePost Q (fun _ => True)
      (DeliverForge.redFSAuthDFPaper cka prng fs lam Δcka qep j tL tStar B) := by
  let mo : Mode := ⟨true, tL, tStar⟩
  unfold DeliverForge.redFSAuthDFPaper DeliverForge.engRunDFPaper; dsimp only
  refine RestrictedReds.SafePost.bind (P := fun _ => True) ?_
    fun _ _ => Proofs.SessionShort.FSAEADRed.safePost_sampleT hQ Bool
  refine (Proofs.SessionShort.FSAEADRed.safeS_initFS hQ cka prng fs lam j {}
      (RestrictedReds.invFS_empty mo.tStar)).bind fun p hp => ?_
  rcases p with ⟨_ | ⟨vA, vB⟩, h⟩
  · exact RestrictedReds.SafePost.pure trivial
  · rcases hp.1 vA vB rfl with ⟨hvA, hvB⟩
    refine RestrictedReds.SafePost.bind (P := fun r => RestrictedReds.InvE mo.tStar r.2)
      (RestrictedReds.SafePost.simulateQ_run
        (RestrictedReds.SafePost.of_isQueryBoundP hok) (fun q hpt => ?_)
        ⟨fun P => by cases P <;> assumption, hp.2⟩)
      fun _ _ => RestrictedReds.SafePost.pure trivial
    rcases q with u | (t | qdf)
    · exact Proofs.SessionShort.FSAEADRed.safeS_coinsE hQ u
    · rcases t with ((((q | q) | q) | q) | P)
      · exact Proofs.SessionShort.FSAEADRed.safeS_transmitE hQ cka prng fs Δcka qep j q
          (by simpa [badSendMsgDF] using hpt)
      · have hok_q : ok q.2.1 = true ∧ ok q.2.2.1 = true := by
          simpa [badSendMsgDF, Bool.or_eq_true] using hpt
        exact Proofs.SessionShort.FSAEADRed.safeS_challE hQ cka prng fs Δcka qep j q
          hok_q.1 hok_q.2
      · exact Proofs.SessionShort.FSAEADRed.safeS_deliverE hQ cka prng fs Δcka j q
      · exact Proofs.SessionShort.FSAEADRed.safeS_injectE hQ cka prng fs Δcka qep j q
      · exact safeS_corrEPaper_of_reveal cka prng fs Δcka j mo.policy
          (Proofs.SessionShort.FSAEADRed.safeS_reveal hQ cka prng fs Δcka j) P
    · exact safeS_deliverForgeE_of_vRecv (b1 := false) (tStar := 0)
        cka prng fs Δcka qep j mo.cfg qdf
        fun ctx P s hs => Proofs.SessionShort.FSAEADRed.safeS_vRecv hQ cka prng fs Δcka j ctx P s hs

theorem safePost_redFSAuthDFShiftedPaperGen_restricted
    {Q : (RSpec SS RS T M E).Domain → Prop} {pubOf : M → Pub}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j l tStar : ℕ) (authH : Bool)
    (hQ : RestrictedReds.ValidQ (SS := SS) (RS := RS) (E := E) Q ⟨authH, some (l - 1), tStar⟩ pubOf)
    (B : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (heq : EqualPubChallsDF pubOf B) :
    RestrictedReds.SafePost Q (fun _ => True)
      (DeliverForge.redFSAuthDFShiftedPaperGen cka prng fs lam Δcka qep j l tStar authH B) := by
  let mo : Mode := ⟨authH, some (l - 1), tStar⟩
  unfold DeliverForge.redFSAuthDFShiftedPaperGen DeliverForge.engRunDFShiftedPaperGen; dsimp only
  refine RestrictedReds.SafePost.bind (P := fun _ => True) ?_
    fun _ _ => RestrictedReds.safePost_sampleT hQ Bool
  refine (RestrictedReds.safeS_initFS hQ cka prng fs lam j {}
      (RestrictedReds.invFS_empty mo.tStar)).bind fun p hp => ?_
  rcases p with ⟨_ | ⟨vA, vB⟩, h⟩
  · exact RestrictedReds.SafePost.pure trivial
  · rcases hp.1 vA vB rfl with ⟨hvA, hvB⟩
    refine RestrictedReds.SafePost.bind (P := fun r => RestrictedReds.InvE mo.tStar r.2)
      (RestrictedReds.SafePost.simulateQ_run
        (RestrictedReds.SafePost.of_isQueryBoundP heq) (fun q hpt => ?_)
        ⟨fun P => by cases P <;> assumption, hp.2⟩)
      fun _ _ => RestrictedReds.SafePost.pure trivial
    rcases q with u | (t | qdf)
    · exact RestrictedReds.safeS_coinsE hQ u
    · rcases t with ((((q | q) | q) | q) | P)
      · exact safeS_transmitE_of_vSend cka prng fs Δcka qep j _ q fun ctx P s hs =>
          RestrictedReds.safeS_vSend hQ cka prng fs Δcka j ctx P s hs q.2.1 none q.2.2
            (by rintro _ _ ⟨⟩)
      · have heq_q : pubOf q.2.1 = pubOf q.2.2.1 := by simpa [unequalPubChallDF] using hpt
        exact safeS_challE_of_vSend cka prng fs Δcka qep j _ _ q fun ctx P s m hs =>
          RestrictedReds.safeS_vSend hQ cka prng fs Δcka j ctx P s hs m (some (q.2.1, q.2.2.1))
            q.2.2.2 (by rintro _ _ ⟨⟩; exact heq_q)
      · exact safeS_deliverE_of_vRecv cka prng fs Δcka j _ q
          fun ctx P s hs => RestrictedReds.safeS_vRecv hQ cka prng fs Δcka j ctx P s hs
      · exact safeS_injectE_of_vRecv cka prng fs Δcka qep j _ q
          fun ctx P s hs => RestrictedReds.safeS_vRecv hQ cka prng fs Δcka j ctx P s hs
      · exact safeS_corrEShiftedPaper_of_reveal l cka prng fs Δcka j _
          (RestrictedReds.safeS_reveal hQ cka prng fs Δcka j) P
    · exact safeS_deliverForgeE_of_vRecv cka prng fs Δcka qep j _ qdf
        fun ctx P s hs => RestrictedReds.safeS_vRecv hQ cka prng fs Δcka j ctx P s hs

theorem safePost_redFSAuthDFShiftedPaperGen_short
    {Q : (RSpec SS RS T M E).Domain → Prop} {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j l tStar : ℕ) (authH : Bool)
    (hQ : Proofs.SessionShort.FSAEADRed.ValidQ (SS := SS) (RS := RS) (E := E)
      Q ⟨authH, some (l - 1), tStar⟩ ok)
    (B : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (hok : SendMsgsOkDF ok B) :
    RestrictedReds.SafePost Q (fun _ => True)
      (DeliverForge.redFSAuthDFShiftedPaperGen cka prng fs lam Δcka qep j l tStar authH B) := by
  let mo : Mode := ⟨authH, some (l - 1), tStar⟩
  unfold DeliverForge.redFSAuthDFShiftedPaperGen DeliverForge.engRunDFShiftedPaperGen; dsimp only
  refine RestrictedReds.SafePost.bind (P := fun _ => True) ?_
    fun _ _ => Proofs.SessionShort.FSAEADRed.safePost_sampleT hQ Bool
  refine (Proofs.SessionShort.FSAEADRed.safeS_initFS hQ cka prng fs lam j {}
      (RestrictedReds.invFS_empty mo.tStar)).bind fun p hp => ?_
  rcases p with ⟨_ | ⟨vA, vB⟩, h⟩
  · exact RestrictedReds.SafePost.pure trivial
  · rcases hp.1 vA vB rfl with ⟨hvA, hvB⟩
    refine RestrictedReds.SafePost.bind (P := fun r => RestrictedReds.InvE mo.tStar r.2)
      (RestrictedReds.SafePost.simulateQ_run
        (RestrictedReds.SafePost.of_isQueryBoundP hok) (fun q hpt => ?_)
        ⟨fun P => by cases P <;> assumption, hp.2⟩)
      fun _ _ => RestrictedReds.SafePost.pure trivial
    rcases q with u | (t | qdf)
    · exact Proofs.SessionShort.FSAEADRed.safeS_coinsE hQ u
    · rcases t with ((((q | q) | q) | q) | P)
      · have hok_q : ok q.2.1 = true := by simpa [badSendMsgDF] using hpt
        exact safeS_transmitE_of_vSend cka prng fs Δcka qep j _ q fun ctx P s hs =>
          Proofs.SessionShort.FSAEADRed.safeS_vSend hQ cka prng fs Δcka j ctx P s hs q.2.1 none
            q.2.2 (fun _ => hok_q) (by rintro _ _ ⟨⟩)
      · have hok_q : ok q.2.1 = true ∧ ok q.2.2.1 = true := by
          simpa [badSendMsgDF, Bool.or_eq_true] using hpt
        exact safeS_challE_of_vSend cka prng fs Δcka qep j _ _ q fun ctx P s m hs =>
          Proofs.SessionShort.FSAEADRed.safeS_vSend hQ cka prng fs Δcka j ctx P s hs m
            (some (q.2.1, q.2.2.1)) q.2.2.2 (by rintro ⟨⟩) (by rintro _ _ ⟨⟩; exact hok_q)
      · exact safeS_deliverE_of_vRecv cka prng fs Δcka j _ q fun ctx P s hs =>
          Proofs.SessionShort.FSAEADRed.safeS_vRecv hQ cka prng fs Δcka j ctx P s hs
      · exact safeS_injectE_of_vRecv cka prng fs Δcka qep j _ q fun ctx P s hs =>
          Proofs.SessionShort.FSAEADRed.safeS_vRecv hQ cka prng fs Δcka j ctx P s hs
      · exact safeS_corrEShiftedPaper_of_reveal l cka prng fs Δcka j _
          (Proofs.SessionShort.FSAEADRed.safeS_reveal hQ cka prng fs Δcka j) P
    · exact safeS_deliverForgeE_of_vRecv cka prng fs Δcka qep j _ qdf
        fun ctx P s hs => Proofs.SessionShort.FSAEADRed.safeS_vRecv hQ cka prng fs Δcka j ctx P s hs

end RedFSAuthDFPaperFsOk

section GuardedShortDF

open GuardedSafe
open CryptoGames.LibsignalSM.Proofs
open CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed
  (FsSendShort FGSafeS FGSafeSTrue fgSafeS_initFS fgSafeS_vSend fgSafeS_vRecv
   fgSafeS_reveal fgSafeS_liftH_true fgSafeS_liftH_and fgSafeS_abortE
   fgSafeS_commitE fgSafeS_coinsE guardedSafePost_sampleT)

local notation "E₀" => ℕ × LibsignalCiphertextWithSalt32

/-- Response invariant requiring every `transmit` or `chall` ciphertext `c` to satisfy
`c.2.2.1.1.length + 8 < 2 ^ 32`. -/
def smDFRespShort {St Msg Coins T : Type} :
    (t : (unifSpec + DeliverForge.specDF St Msg Coins (Header T × E₀)).Domain) →
    (unifSpec + DeliverForge.specDF St Msg Coins (Header T × E₀)).Range t → Prop
  | .inr (.inl o), r =>
      SessionShort.SimAndSM.smRespShort (St := St) (Msg := Msg) (Coins := Coins) (T := T)
        (.inr o) r
  | _, _ => True

/-- Predicate for `deliver`, `inject`, or `deliverForge` queries carrying a wire payload of length
at least `2 ^ 32`. -/
def smDFRecvLong {St Msg Coins T : Type} :
    (unifSpec + DeliverForge.specDF St Msg Coins (Header T × E₀)).Domain → Prop
  | .inr (.inl o) =>
      SessionShort.SimAndSM.smRecvLong (St := St) (Msg := Msg) (Coins := Coins) (T := T)
        (.inr o)
  | .inr (.inr ⟨_, _, c'⟩) => ¬ c'.2.2.1.1.length < 2 ^ 32
  | .inl _ => False

instance instDecidablePredSmDFRecvLong {St Msg Coins T : Type} :
    DecidablePred (smDFRecvLong (St := St) (Msg := Msg) (Coins := Coins) (T := T))
  | .inl _ => isFalse not_false
  | .inr (.inl o) =>
      SessionShort.SimAndSM.instDecidablePredSmRecvLong
        (St := St) (Msg := Msg) (Coins := Coins) (T := T) (.inr o)
  | .inr (.inr ⟨_, _, c'⟩) => inferInstanceAs (Decidable (¬ c'.2.2.1.1.length < 2 ^ 32))

/-- Invariant that under `smDFRespShort`, `A` never queries `deliver`, `inject`, or `deliverForge`
on a wire payload of length at least `2 ^ 32`. -/
def GuardedSMDFShort {St Msg Coins T : Type}
    (A : DeliverForge.AdversaryDF St Msg Coins (Header T × E₀)) : Prop :=
  GuardedSafePost smDFRespShort smDFRecvLong (fun _ => True) A

theorem hQu_smDFRecvLong {St Msg Coins T : Type} (u : ℕ) :
    ¬ smDFRecvLong (St := St) (Msg := Msg) (Coins := Coins) (T := T) (.inl u) :=
  not_false

theorem challSimDF'Paper_guardedSMDFShort {St Msg Coins T : Type} [DecidableEq T]
    (Δ qep : ℕ)
    (B : DeliverForge.AdversaryDF St Msg Coins (Header T × E₀))
    (hB : GuardedSMDFShort B) :
    GuardedSMDFShort (DeliverForge.challSimDF'Paper Δ qep B) := by
  unfold GuardedSMDFShort at hB ⊢
  unfold DeliverForge.challSimDF'Paper
  refine (GuardedSafePost.liftComp_unif hQu_smDFRecvLong ($ᵗ Bool)).bind fun b _ => ?_
  rw [StateT.run'_eq]
  have hsim : GuardedSafePost smDFRespShort smDFRecvLong (fun _ => True)
      ((simulateQ (DeliverForge.simImplDF'Paper Δ qep) B).run
        ({ st := fun _ => (), b } : Mirror Msg (Header T × E₀))) := by
    refine GuardedSafePost.simulateQ_run (I := fun _ => True) hB ?_ trivial
    rintro (n | ((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩) hpt
    · exact guardedSafeS_lift_query (hQu_smDFRecvLong n)
    · change GuardedSafeS _ _ _ _ (DeliverForge.simTransmitDF'Paper Δ qep (P, msg, r))
      unfold DeliverForge.simTransmitDF'Paper DeliverForge.transmitQueryDF
      refine guardedSafeS_get_bind fun s _ => ?_
      refine guardedSafeS_bind_query (Q := smDFRecvLong) not_false fun res hres => ?_
      cases res <;> cases s.epMgmt Δ qep P false
      all_goals first
        | exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
        | exact guardedSafeS_pure _ fun _ _ => ⟨hres, trivial⟩
        | exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
            guardedSafeS_pure _ fun _ _ => ⟨hres, trivial⟩
    · change GuardedSafeS _ _ _ _ (DeliverForge.simChallDF'Paper Δ qep (P, m₀, m₁, r))
      unfold DeliverForge.simChallDF'Paper DeliverForge.transmitQueryDF
      refine guardedSafeS_get_bind fun s _ => ?_
      cases s.epMgmt Δ qep P false with
      | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
      | some s₁ =>
        dsimp only; cases s₁.safeCh Δ P
        · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          refine guardedSafeS_bind_query (Q := smDFRecvLong) not_false fun res hres => ?_
          cases res
          · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
          · exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
              guardedSafeS_pure _ fun _ _ => ⟨hres, trivial⟩
    · change GuardedSafeS _ _ _ _ (DeliverForge.simDeliverDF (P, c))
      unfold DeliverForge.simDeliverDF DeliverForge.deliverQueryDF
      refine guardedSafeS_get_bind fun s _ => ?_
      refine guardedSafeS_bind_query (Q := smDFRecvLong) hpt fun res _ => ?_
      cases res with
      | none => exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
      | some rr =>
        cases rr <;> cases s.inTransit P.other c
        all_goals first
          | exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
          | exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
              guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
    · change GuardedSafeS _ _ _ _ (DeliverForge.simInjectDF (P, c))
      unfold DeliverForge.simInjectDF DeliverForge.injectQueryDF
      refine guardedSafeS_get_bind fun _ _ => ?_
      refine guardedSafeS_bind_query (Q := smDFRecvLong) hpt fun res _ => ?_
      cases res with
      | none => exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
      | some rr =>
        cases rr
        · exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
        · exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
            guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
    · change GuardedSafeS _ _ _ _ (DeliverForge.simCorrDFPaper P)
      unfold DeliverForge.simCorrDFPaper DeliverForge.corrQueryDF
      refine guardedSafeS_get_bind fun s _ => ?_
      cases s.corrAllowedPaper P
      · exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine guardedSafeS_bind_query (Q := smDFRecvLong) not_false fun res _ => ?_
        cases res
        · exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
        · exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
            guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
    · change GuardedSafeS _ _ _ _ (DeliverForge.simDeliverForgeDF (P, c, c'))
      unfold DeliverForge.simDeliverForgeDF DeliverForge.deliverForgeQuery
      refine guardedSafeS_get_bind fun _ _ => ?_
      refine guardedSafeS_bind_query (Q := smDFRecvLong) hpt fun res _ => ?_
      cases res with
      | none => exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
      | some rr =>
        cases rr
        · exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
        · exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
            guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
  exact hsim.map (R := fun _ => True) Prod.fst fun _ _ => trivial

section RedFSGuardedDF

set_option linter.unusedSectionVars false

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

private theorem fgSafeS_corrEPaper
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (π : Policy) (P : Party) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M) (fun _ => True)
      (DeliverForge.corrEPaper (hooksFS cka prng fs Δcka mo j) π P) := by
  unfold DeliverForge.corrEPaper
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win || !es.g.corrAllowedPaper P) = true
  · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P) = true
    · simp only [h2, ↓reduceIte]
      exact guardedSafeS_bind_true fgSafeS_abortE
        fun _ => guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      refine guardedSafeS_bind_true
        (fgSafeS_liftH_true (fgSafeS_reveal cka prng fs Δcka mo j es.g P (es.g.st P)))
        fun res => ?_
      cases res with
      | none =>
        exact guardedSafeS_bind_true fgSafeS_abortE
          fun _ => guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
      | some st =>
        exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
          fun _ => guardedSafeS_pure (some st) fun _ _ => ⟨trivial, trivial⟩

private theorem fgSafeS_corrEShiftedPaper
    (l : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (π : Policy) (P : Party) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M) (fun _ => True)
      (DeliverForge.corrEShiftedPaper l (hooksFS cka prng fs Δcka mo j) π P) := by
  unfold DeliverForge.corrEShiftedPaper
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win || !es.g.corrAllowedPaper P) = true
  · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 :
        (π.leakDoom es.g (DeliverForge.afterCorrShifted l es.g P) || π.corrDoom es.g P) = true
    · simp only [h2, ↓reduceIte]
      exact guardedSafeS_bind_true fgSafeS_abortE
        fun _ => guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      refine guardedSafeS_bind_true
        (fgSafeS_liftH_true (fgSafeS_reveal cka prng fs Δcka mo j es.g P (es.g.st P)))
        fun res => ?_
      cases res with
      | none =>
        exact guardedSafeS_bind_true fgSafeS_abortE
          fun _ => guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
      | some st =>
        exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
          fun _ => guardedSafeS_pure (some st) fun _ _ => ⟨trivial, trivial⟩

private theorem fgSafeS_transmitE_pi {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (Δcka qep : ℕ) (mo : Mode) (j : ℕ) (π : Policy)
    (q : Party × M × Option CCoins) (hok : ok q.2.1 = true) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ c : Header T × E₀, res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
      (transmitE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep π q) := by
  rcases q with ⟨P, m, r⟩
  unfold transmitE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
    | some s₁ =>
      by_cases h2 : π.leakDoom es.g s₁ = true
      · simp only [h2, ↓reduceIte]
        exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
          guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        refine guardedSafeS_bind_and
          (fgSafeS_liftH_and (fgSafeS_vSend cka prng fs hfs Δcka mo j s₁ P (s₁.st P) m none r hok))
          fun res hres => ?_
        rcases res with _ | ⟨st', c⟩
        · exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
            guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
        · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
          refine guardedSafeS_pure (some c) fun _ _ => ⟨?_, trivial⟩
          rintro _ ⟨⟩
          exact hres st' c rfl

private theorem fgSafeS_challE_cfg_pi {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (Δcka qep : ℕ) (mo : Mode) (j : ℕ) (cfg : SM.Config M) (hcm : ∀ t, cfg.challMsg t = none)
    (π : Policy) (q : Party × M × M × Option CCoins)
    (hok₀ : ok q.2.1 = true) (hok₁ : ok q.2.2.1 = true) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ c : Header T × E₀, res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
      (challE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep cfg π q) := by
  rcases q with ⟨P, m₀, m₁, r⟩
  unfold challE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
    | some s₁ =>
      by_cases h2 : (!s₁.safeCh (2 + Δcka) P || !cfg.challAllowedIn (s₁.epoch P)) = true
      · simp only [h2, ↓reduceIte]
        exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : π.leakDoom es.g s₁ = true
        · simp only [h3, ↓reduceIte]
          exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
            guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          have hm : ok ((cfg.challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀)) = true := by
            rw [hcm]
            dsimp only [Option.getD]
            cases es.g.b <;> assumption
          refine guardedSafeS_bind_and
            (fgSafeS_liftH_and (fgSafeS_vSend cka prng fs hfs Δcka mo j s₁ P (s₁.st P) _
              (some (m₀, m₁)) r hm))
            fun res hres => ?_
          rcases res with _ | ⟨st', c⟩
          · exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
              guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
          · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
            refine guardedSafeS_pure (some c) fun _ _ => ⟨?_, trivial⟩
            rintro _ ⟨⟩
            exact hres st' c rfl

private theorem fgSafeS_deliverE_cfg
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (cfg : SM.Config M) (q : Party × (Header T × E₀)) (hc : q.2.2.2.1.1.length < 2 ^ 32) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M) (fun _ => True)
      (deliverE (hooksFS cka prng fs Δcka mo j) fs.maxSkip cfg q) := by
  rcases q with ⟨P, c⟩
  unfold deliverE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.inTransit P.other c with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    | some r =>
      refine guardedSafeS_bind_true
        (fgSafeS_liftH_true (fgSafeS_vRecv cka prng fs Δcka mo j es.g P (es.g.st P) c (some r) hc))
        fun res => ?_
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · exact guardedSafeS_bind_true fgSafeS_abortE
          fun _ => guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
      · by_cases h2 : (cfg.deliverWin && es.g.mustBeCorrect fs.maxSkip P r) = true
        · simp only [h2, ↓reduceIte]
          exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
            fun _ => guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
      · refine guardedSafeS_bind_true
          (fgSafeS_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st' r.pos)
          fun s₁? => ?_
        rcases s₁? with _ | s₁
        · exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
        · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
            fun _ => guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩

private theorem fgSafeS_injectEGen (b1 : Bool) (tStar : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (cfg : SM.Config M) (q : Party × (Header T × E₀)) (hc : q.2.2.2.1.1.length < 2 ^ 32) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M) (fun _ => True)
      (injectEGen b1 (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep tStar cfg q) := by
  rcases q with ⟨P, c⟩
  cases b1 <;> [unfold injectEGen injectE; unfold injectEGen DeliverForge.injectEB1]
  all_goals
    dsimp only
    refine guardedSafeS_get_bind fun es _ => ?_
    split_ifs with h1
    · exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    · refine guardedSafeS_bind_true
        (fgSafeS_liftH_true (fgSafeS_vRecv cka prng fs Δcka mo j es.g P (es.g.st P) c none hc))
        fun res => ?_
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · exact guardedSafeS_bind_true fgSafeS_abortE
          fun _ => guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
      · exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
      · by_cases h2 : qep + 1 < t'
        · simp only [h2, ↓reduceIte]
          exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
        · simp only [h2, ↓reduceIte]
          split_ifs
          · refine guardedSafeS_bind_true
              (fgSafeS_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st' ⟨P.other, t', i'⟩)
              fun s₁? => ?_
            rcases s₁? with _ | s₁
            · exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
            · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                fun _ => guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
          · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
              fun _ => guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
          · exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩

private theorem fgSafeS_deliverForgeEGen (b1 : Bool) (tStar : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (cfg : SM.Config M) (q : Party × (Header T × E₀) × (Header T × E₀))
    (hc' : q.2.2.2.2.1.1.length < 2 ^ 32) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M) (fun _ => True)
      (deliverForgeEGen b1 (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep tStar cfg q) := by
  rcases q with ⟨P, c, c'⟩
  cases b1 <;> [unfold deliverForgeEGen DeliverForge.deliverForgeE;
    unfold deliverForgeEGen DeliverForge.deliverForgeEB1]
  all_goals
    dsimp only
    refine guardedSafeS_get_bind fun es _ => ?_
    by_cases h1 : (es.abort || es.g.win) = true
    · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      cases es.g.inTransit P.other c with
      | none => exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
      | some r =>
        by_cases h2 :
            ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
        · simp only [h2, ↓reduceIte]; exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          refine guardedSafeS_bind_true
            (fgSafeS_liftH_true (fgSafeS_vRecv cka prng fs Δcka mo j es.g P (es.g.st P) c' none hc'))
            fun res => ?_
          rcases res with _ | (_ | ⟨st', t', i', m'⟩)
          · exact guardedSafeS_bind_true fgSafeS_abortE
              fun _ => guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
          · exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
          · by_cases h3 : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
            · simp only [h3, ↓reduceIte]
              exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
            · simp only [h3, Bool.false_eq_true, ↓reduceIte]
              split_ifs
              · refine guardedSafeS_bind_true
                  (fgSafeS_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st' ⟨P.other, t', i'⟩)
                  fun s₁? => ?_
                rcases s₁? with _ | s₁
                · exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
                · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                    fun _ => guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
              · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                  fun _ => guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
              · exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩

theorem guardedFSInjectShort_redFSAuthDFPaper {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (lam : I) (Δcka qep j : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (B : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E₀)
    (hok : SendMsgsOkDF ok B) (hg : GuardedSMDFShort B) :
    GuardedFSInjectShort
      (DeliverForge.redFSAuthDFPaper cka prng fs lam Δcka qep j tL tStar B) := by
  let mo : Mode := ⟨true, tL, tStar⟩
  unfold GuardedFSInjectShort DeliverForge.redFSAuthDFPaper DeliverForge.engRunDFPaper
  dsimp only
  refine GuardedSafePost.bind (P := fun _ => True) ?_ fun _ _ => guardedSafePost_sampleT Bool
  refine (fgSafeS_initFS cka prng fs lam mo j {} trivial).bind fun p _ => ?_
  rcases p with ⟨_ | ⟨vA, vB⟩, h⟩
  · exact GuardedSafePost.pure trivial
  · have hB := hg.and_isQueryBoundP hok
    have hsim : GuardedSafePost fsRespShort fsInjectLong (fun _ => True)
        ((simulateQ (DeliverForge.implEDFPaper (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep
          fs.maxSkip mo.cfg mo.policy) B).run
          { g := { st := fun | .A => vA | .B => vB, b := false }, h, abort := false }) := by
      refine GuardedSafePost.simulateQ_run (I := fun _ => True) hB ?_ trivial
      rintro (u | (t | qdf)) hpt
      · exact fgSafeS_coinsE u
      · rcases t with ((((q | q) | q) | q) | P)
        · have hok_q : ok q.2.1 = true := by
            have hnb : ¬ badSendMsgDF (St := PartyState Γ T Sig SS RS) (Coins := CCoins)
                (C := Header T × E₀) ok (.inr (.inl (.inl (.inl (.inl (.inl q)))))) = true :=
              fun hb => hpt (Or.inr hb)
            simpa [badSendMsgDF] using hnb
          exact fgSafeS_transmitE_pi cka prng fs hfs Δcka qep mo j mo.policy q hok_q
        · have hok_q : ok q.2.1 = true ∧ ok q.2.2.1 = true := by
            have hnb : ¬ badSendMsgDF (St := PartyState Γ T Sig SS RS) (Coins := CCoins)
                (C := Header T × E₀) ok (.inr (.inl (.inl (.inl (.inl (.inr q)))))) = true :=
              fun hb => hpt (Or.inr hb)
            simpa [badSendMsgDF, Bool.or_eq_true] using hnb
          exact fgSafeS_challE_cfg_pi cka prng fs hfs Δcka qep mo j mo.cfg
            (fun _ => rfl) mo.policy q hok_q.1 hok_q.2
        · have hc : q.2.2.2.1.1.length < 2 ^ 32 :=
            Decidable.of_not_not fun hnl => hpt (Or.inl hnl)
          exact fgSafeS_deliverE_cfg cka prng fs Δcka mo j mo.cfg q hc
        · have hc : q.2.2.2.1.1.length < 2 ^ 32 :=
            Decidable.of_not_not fun hnl => hpt (Or.inl hnl)
          exact fgSafeS_injectEGen false 0 cka prng fs Δcka qep mo j mo.cfg q hc
        · exact fgSafeS_corrEPaper cka prng fs Δcka mo j mo.policy P
      · have hc' : qdf.2.2.2.2.1.1.length < 2 ^ 32 :=
          Decidable.of_not_not fun hnl => hpt (Or.inl hnl)
        exact fgSafeS_deliverForgeEGen false 0 cka prng fs Δcka qep mo j mo.cfg qdf hc'
    exact hsim.bind fun _ _ => GuardedSafePost.pure (P := fun _ => True) trivial

theorem guardedFSInjectShort_redFSAuthDFShiftedPaperGen {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (lam : I) (Δcka qep j l tStar : ℕ) (authH : Bool)
    (B : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E₀)
    (hok : SendMsgsOkDF ok B) (hg : GuardedSMDFShort B) :
    GuardedFSInjectShort
      (DeliverForge.redFSAuthDFShiftedPaperGen cka prng fs lam Δcka qep j l tStar authH B) := by
  let mo : Mode := ⟨authH, some (l - 1), tStar⟩
  unfold GuardedFSInjectShort DeliverForge.redFSAuthDFShiftedPaperGen
    DeliverForge.engRunDFShiftedPaperGen
  dsimp only
  refine GuardedSafePost.bind (P := fun _ => True) ?_ fun _ _ => guardedSafePost_sampleT Bool
  refine (fgSafeS_initFS cka prng fs lam mo j {} trivial).bind fun p _ => ?_
  rcases p with ⟨_ | ⟨vA, vB⟩, h⟩
  · exact GuardedSafePost.pure trivial
  · have hB := hg.and_isQueryBoundP hok
    have hsim : GuardedSafePost fsRespShort fsInjectLong (fun _ => True)
        ((simulateQ (DeliverForge.implEDFShiftedPaperGen (!authH) l
          (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip tStar
          (SM.Config.auth tStar) (⟨true, some (l - 1), tStar⟩ : Mode).policy) B).run
          { g := { st := fun | .A => vA | .B => vB, b := false }, h, abort := false }) := by
      refine GuardedSafePost.simulateQ_run (I := fun _ => True) hB ?_ trivial
      rintro (u | (t | qdf)) hpt
      · exact fgSafeS_coinsE u
      · rcases t with ((((q | q) | q) | q) | P)
        · have hok_q : ok q.2.1 = true := by
            have hnb : ¬ badSendMsgDF (St := PartyState Γ T Sig SS RS) (Coins := CCoins)
                (C := Header T × E₀) ok (.inr (.inl (.inl (.inl (.inl (.inl q)))))) = true :=
              fun hb => hpt (Or.inr hb)
            simpa [badSendMsgDF] using hnb
          exact fgSafeS_transmitE_pi cka prng fs hfs Δcka qep mo j _ q hok_q
        · have hok_q : ok q.2.1 = true ∧ ok q.2.2.1 = true := by
            have hnb : ¬ badSendMsgDF (St := PartyState Γ T Sig SS RS) (Coins := CCoins)
                (C := Header T × E₀) ok (.inr (.inl (.inl (.inl (.inl (.inr q)))))) = true :=
              fun hb => hpt (Or.inr hb)
            simpa [badSendMsgDF, Bool.or_eq_true] using hnb
          exact fgSafeS_challE_cfg_pi cka prng fs hfs Δcka qep mo j _
            (fun _ => rfl) _ q hok_q.1 hok_q.2
        · have hc : q.2.2.2.1.1.length < 2 ^ 32 :=
            Decidable.of_not_not fun hnl => hpt (Or.inl hnl)
          exact fgSafeS_deliverE_cfg cka prng fs Δcka mo j _ q hc
        · have hc : q.2.2.2.1.1.length < 2 ^ 32 :=
            Decidable.of_not_not fun hnl => hpt (Or.inl hnl)
          exact fgSafeS_injectEGen (!authH) tStar cka prng fs Δcka qep mo j _ q hc
        · exact fgSafeS_corrEShiftedPaper l cka prng fs Δcka mo j _ P
      · have hc' : qdf.2.2.2.2.1.1.length < 2 ^ 32 :=
          Decidable.of_not_not fun hnl => hpt (Or.inl hnl)
        exact fgSafeS_deliverForgeEGen (!authH) tStar cka prng fs Δcka qep mo j _ qdf hc'
    exact hsim.bind fun _ _ => GuardedSafePost.pure (P := fun _ => True) trivial

end RedFSGuardedDF

end GuardedShortDF

end CryptoVerification.LibsignalSession.HeadlineV1
