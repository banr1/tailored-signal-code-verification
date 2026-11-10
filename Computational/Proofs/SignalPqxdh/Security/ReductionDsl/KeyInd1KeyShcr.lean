/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeySigKem
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndShcrWire
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrEval
import VCVio.EvalDist.Monad.Basic

/-!
# Costed `ReductionDsl` One-Key `KemShCr` Program and Advantage Equivalence

**Checked by Lean.** Defines the two-stage `ReductionDsl` program `shcrKeyInd1KeyProg` for the
one-key `KemShCr` reduction `shcrReductionKeyInd1Key` and proves its syntactic cost, query, and
block-size bounds together with exact `KemShCr` advantage agreement.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open OracleSpec OracleComp RoKem

attribute [simp] bundleV hdrV drKeyV sidV keyIndRenc keyIndQenc

/-! ## One-key `initPrin` branch and `shcrKeyInd1KeyProg` -/

/-- One-key `initPrin u` handler reusing a single 32-byte scalar for both X25519 keys. -/
def initPrin1KeyB (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .ite (eAny K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret (rs rNone (v st))) <|
  bindV sBytes32 fun s0 => bindV (qX25519Base (v s0)) fun ik =>
  .ret (rs (rInitPrin (v ik) (v ik)) (stUpd (v st) (prin := .cons
    (.pair (v u) (peMk (v s0) (v ik) (v s0) (v ik) (.bool false))) (stPrin (v st)))))

@[reducible] def keyIndQueryRestTy : PT :=
  .sum .nat (.sum (.prod .nat .nat) (.sum (.prod .nat (.prod .nat .nat))
  (.sum (.prod .nat (.prod .nat bundleT)) (.sum (.prod .nat (.prod .nat bundleT))
  (.sum (.prod .nat (.prod .nat (.prod .nat hdrT)))
  (.sum (.prod .nat (.prod .nat (.prod .nat hdrT)))
  (.sum sidT (.sum (B 192) (.sum .unit (.sum sidT (.sum (B 32) (.prod .nat .nat))))))))))))

def shcrPostTailC (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (q : Var (keyIndQueryRestTy :: Δ) keyIndQueryRestTy) :
    Comp pqxdhOps pqPrimIface (keyIndQueryRestTy :: Δ) SCS :=
  caseSumV (v q) (fun u => onBase s fun g => corruptB K g u) fun q =>
  caseSumV (v q) (fun x => shcrGenSpkB S K s x) fun q =>
  caseSumV (v q) (fun x => onBase s fun g => genOpkB K g x) fun q =>
  caseSumV (v q) (fun x => shcrInitiateC S K true s x) fun q =>
  caseSumV (v q) (fun x => shcrInitiateC S K false s x) fun q =>
  caseSumV (v q) (fun x => shcrAcceptB S K true s x) fun q =>
  caseSumV (v q) (fun x => shcrAcceptB S K false s x) fun q =>
  caseSumV (v q) (fun sid => onBase s fun g => testB K g sid) fun q =>
  caseSumV (v q) (fun sec => onBase s fun g => roB true K g sec) fun q =>
  caseSumV (v q) (fun _ => onBase s fun g => revealDhB true K g) fun q =>
  caseSumV (v q) (fun sid => onBase s fun g => revealB K g sid) fun q =>
  caseSumV (v q) (fun sk => onBase s fun g => registerB g sk) fun x =>
  onBase s fun g => revealSpkB K g x

def shcr1KeyPostC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ SCS :=
  caseSumV (v q) (fun u => onBase s fun g => initPrin1KeyB K g u) (shcrPostTailC S K s)

theorem shcrPostC_eq_tail (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    shcrPostC (Δ := Δ) S K s q =
      caseSumV (v q) (fun u => onBase s fun g => initPrinB K g u) (shcrPostTailC S K s) :=
  rfl

def shcr1KeyPreC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ (.sum SCS (.prod (B 1568) (.prod pauseTy shcrStTy))) :=
  bindV (pauseCheckC S K s q) fun p =>
  caseOptV (v p) (bindV (shcr1KeyPostC S K s q) fun r => .ret (.inl (v r))) fun d =>
  .ret (.inr (.pair (buPqspkB (.fst (.snd (v d)))) (.pair (v d) (v s))))

/-- Two-stage `ReductionDsl` program for `shcrReductionKeyInd1KeyCore S b` with extraction bound `Q` and state-list bound `K`. -/
def shcrKeyInd1KeyProg (S : Setup) (Q K : Nat) :
    TwoStageCostedReduction pqxdhOps pqPrimIface (keyIndSpec S) (keyIndCodec S)
      (.prod (B 1568) (B 3168)) .unit .bool (B 1568) (.prod (B 32) (B 1568)) (B 1568) where
  σ := shcrStTy
  π := pauseTy
  init := (shcrKeyIndProg S Q K).init
  handlePre := shcr1KeyPreC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  chDone := .ret (scTPk (.var .zero))
  resume := shcrResumeC S K (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₂ := [pauseTy, .prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)]) .zero .zero .zero
  handlePost := shcr1KeyPostC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  finish := shcrExtractC (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, .bool, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, .bool, .prod (B 32) (B 1568)]) Q .zero .zero

abbrev shcrKeyInd1KeyDslProg (S : Setup) (b : QueryBudget) :=
  shcrKeyInd1KeyProg S b.q_total (keyIndLoopBound b)

/-! ## Syntactic cost, query, and block-size bounds -/

theorem initPrin1KeyB_cost_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrin1KeyB (Δ := Δ) K st u).cost ≤ (initPrinB (Δ := Δ) K st u).cost := by
  simp only [initPrin1KeyB, initPrinB, bindV, eAny, natEq,
    stPrin, stSecb, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    stUpd, stMk, peMk, rs, rNone, rInitPrin,
    cost_sBytes32, cost_qX25519Base, cost_qSigPkGen, cost_v, Comp.cost, Expr.cost]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

theorem initPrin1KeyB_queries_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrin1KeyB (Δ := Δ) K st u).queries primW primWS ≤
      (initPrinB (Δ := Δ) K st u).queries primW primWS := by
  simp [initPrin1KeyB, initPrinB, bindV, Comp.queries]

theorem caseSumV_cost_le_left {τ₁ τ₂ τ : PT} {Γ : List PT}
    (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (l₁ l₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (r : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (hl : (l₁ .zero).cost ≤ (l₂ .zero).cost) :
    (caseSumV e l₁ r).cost ≤ (caseSumV e l₂ r).cost := by
  dsimp only [caseSumV, Comp.cost]
  omega

theorem shcr1KeyPostC_cost_le_shcrPostC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcr1KeyPostC (Δ := Δ) S K s q).cost ≤ (shcrPostC (Δ := Δ) S K s q).cost := by
  rw [shcrPostC_eq_tail]
  unfold shcr1KeyPostC
  refine caseSumV_cost_le_left _ _ _ (shcrPostTailC S K s) ?_
  simp only [onBase_cost]
  exact Nat.add_le_add_right (initPrin1KeyB_cost_le K (Γ₁ := keyIndStateTy :: (.nat :: Δ))
    (Γ₂ := .nat :: Δ) (Δ := keyIndStateTy :: (.nat :: Δ)) .zero .zero) 70

theorem shcr1KeyPreC_cost_le_shcrPreC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcr1KeyPreC (Δ := Δ) S K s q).cost ≤ (shcrPreC (Δ := Δ) S K s q).cost := by
  have hPost := shcr1KeyPostC_cost_le_shcrPostC S K (Γ₁ := Γ₁) (Γ₂ := Γ₂)
    (Δ := (.opt pauseTy) :: Δ) s q
  simp only [shcr1KeyPreC, shcrPreC, bindV, caseOptV, Comp.cost]
  omega

theorem shcrKeyInd1KeyProg_totalCost_le_twoKey (S : Setup) (Q K fuel : Nat) :
    (shcrKeyInd1KeyProg S Q K).totalCost fuel ≤ (shcrKeyIndProg S Q K).totalCost fuel := by
  have hInit : (shcrKeyInd1KeyProg S Q K).init.cost = (shcrKeyIndProg S Q K).init.cost := rfl
  have hCh : (shcrKeyInd1KeyProg S Q K).chDone.cost = (shcrKeyIndProg S Q K).chDone.cost := rfl
  have hRes : (shcrKeyInd1KeyProg S Q K).resume.cost = (shcrKeyIndProg S Q K).resume.cost := rfl
  have hFin : (shcrKeyInd1KeyProg S Q K).finish.cost = (shcrKeyIndProg S Q K).finish.cost := rfl
  have hPre : (shcrKeyInd1KeyProg S Q K).handlePre.cost ≤ (shcrKeyIndProg S Q K).handlePre.cost :=
    shcr1KeyPreC_cost_le_shcrPreC S K (Γ₁ := [shcrStTy, keyIndQueryTy])
      (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hPost : (shcrKeyInd1KeyProg S Q K).handlePost.cost ≤ (shcrKeyIndProg S Q K).handlePost.cost :=
    shcr1KeyPostC_cost_le_shcrPostC S K (Γ₁ := [shcrStTy, keyIndQueryTy])
      (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hMax :
      max pqPrimIface.uCost (max (shcrKeyInd1KeyProg S Q K).handlePre.cost
        (shcrKeyInd1KeyProg S Q K).handlePost.cost + (keyIndCodec S).codecCost) ≤
      max pqPrimIface.uCost (max (shcrKeyIndProg S Q K).handlePre.cost
        (shcrKeyIndProg S Q K).handlePost.cost + (keyIndCodec S).codecCost) :=
    max_le (le_max_left _ _)
      (le_trans (Nat.add_le_add_right (max_le (le_trans hPre (le_max_left _ _))
        (le_trans hPost (le_max_right _ _))) _) (le_max_right _ _))
  have hMul := Nat.mul_le_mul_left fuel hMax
  unfold TwoStageCostedReduction.totalCost
  rw [hInit, hCh, hRes, hFin]
  omega

theorem shcrKeyInd1KeyDslProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyDslProg S b).totalCost b.q_total ≤ stepCostBudget S b :=
  (shcrKeyInd1KeyProg_totalCost_le_twoKey S b.q_total (keyIndLoopBound b) b.q_total).trans
    (shcrKeyIndDslProg_totalCost_le S b)

theorem shcrKeyInd1KeyDslProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyDslProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b :=
  (shcrKeyInd1KeyProg_totalCost_le_twoKey S b.q_total (keyIndLoopBound b) b.q_total).trans
    (shcrKeyIndProg_totalCost_le_security_of_le S b (keyIndLoopBound b) le_rfl)

theorem caseSumV_queries_le_left {τ₁ τ₂ τ : PT} {Γ : List PT}
    (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (l₁ l₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (r : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (hl : (l₁ .zero).queries primW primWS ≤ (l₂ .zero).queries primW primWS) :
    (caseSumV e l₁ r).queries primW primWS ≤ (caseSumV e l₂ r).queries primW primWS := by
  dsimp only [caseSumV, Comp.queries]
  omega

theorem shcr1KeyPostC_queries_le_shcrPostC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcr1KeyPostC (Δ := Δ) S K s q).queries primW primWS ≤
      (shcrPostC (Δ := Δ) S K s q).queries primW primWS := by
  rw [shcrPostC_eq_tail]
  unfold shcr1KeyPostC
  refine caseSumV_queries_le_left _ _ _ (shcrPostTailC S K s) ?_
  simp only [onBase_queries]
  exact initPrin1KeyB_queries_le K (Γ₁ := keyIndStateTy :: (.nat :: Δ))
    (Γ₂ := .nat :: Δ) (Δ := keyIndStateTy :: (.nat :: Δ)) .zero .zero

theorem shcr1KeyPreC_queries_le_shcrPreC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcr1KeyPreC (Δ := Δ) S K s q).queries primW primWS ≤
      (shcrPreC (Δ := Δ) S K s q).queries primW primWS := by
  have hPost := shcr1KeyPostC_queries_le_shcrPostC S K (Γ₁ := Γ₁) (Γ₂ := Γ₂)
    (Δ := (.opt pauseTy) :: Δ) s q
  simp only [shcr1KeyPreC, shcrPreC, bindV, caseOptV, Comp.queries]
  omega

theorem shcrKeyInd1KeyProg_totalQueries_le_twoKey (S : Setup) (Q K fuel : Nat) :
    (shcrKeyInd1KeyProg S Q K).totalQueries primW primWS fuel ≤
      (shcrKeyIndProg S Q K).totalQueries primW primWS fuel := by
  have hInit : (shcrKeyInd1KeyProg S Q K).init.queries primW primWS =
      (shcrKeyIndProg S Q K).init.queries primW primWS := rfl
  have hCh : (shcrKeyInd1KeyProg S Q K).chDone.queries primW primWS =
      (shcrKeyIndProg S Q K).chDone.queries primW primWS := rfl
  have hRes : (shcrKeyInd1KeyProg S Q K).resume.queries primW primWS =
      (shcrKeyIndProg S Q K).resume.queries primW primWS := rfl
  have hFin : (shcrKeyInd1KeyProg S Q K).finish.queries primW primWS =
      (shcrKeyIndProg S Q K).finish.queries primW primWS := rfl
  have hPre : (shcrKeyInd1KeyProg S Q K).handlePre.queries primW primWS ≤
      (shcrKeyIndProg S Q K).handlePre.queries primW primWS :=
    shcr1KeyPreC_queries_le_shcrPreC S K (Γ₁ := [shcrStTy, keyIndQueryTy])
      (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hPost : (shcrKeyInd1KeyProg S Q K).handlePost.queries primW primWS ≤
      (shcrKeyIndProg S Q K).handlePost.queries primW primWS :=
    shcr1KeyPostC_queries_le_shcrPostC S K (Γ₁ := [shcrStTy, keyIndQueryTy])
      (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hMax :
      max ((shcrKeyInd1KeyProg S Q K).handlePre.queries primW primWS)
        ((shcrKeyInd1KeyProg S Q K).handlePost.queries primW primWS) ≤
      max ((shcrKeyIndProg S Q K).handlePre.queries primW primWS)
        ((shcrKeyIndProg S Q K).handlePost.queries primW primWS) :=
    max_le (le_trans hPre (le_max_left _ _)) (le_trans hPost (le_max_right _ _))
  have hMul := Nat.mul_le_mul_left fuel hMax
  unfold TwoStageCostedReduction.totalQueries
  rw [hInit, hCh, hRes, hFin]
  omega

theorem shcrKeyInd1KeyDslProg_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyDslProg S b).totalQueries SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      b.q_total ≤ primQueryBudget S b := by
  rw [show SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight = primW from rfl,
    show SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = primWS from rfl]
  exact (shcrKeyInd1KeyProg_totalQueries_le_twoKey S b.q_total (keyIndLoopBound b) b.q_total).trans
    (shcrKeyIndDslProg_totalPrimQueries_le S b)

private theorem securityStepCostBudget_le_legacy (S : Setup) (b : QueryBudget) :
    _root_.SignalPqxdh.Security.stepCostBudget S b ≤
      _root_.SignalPqxdh.LegacyCosted.stepCostBudget S b := by
  refine (security_stepCostBudget_le S b).trans ?_
  unfold stepCostBudget _root_.SignalPqxdh.LegacyCosted.stepCostBudget
  have hEq : 2 ^ 16 * (b.q_total + S.N_dh + S.N_sess_tot + 1) ^ 2 =
      (2 ^ 16 * (b.q_total + 1) * (b.q_total + S.N_dh + S.N_sess_tot + 1) +
        2 ^ 11 * S.N_dh ^ 2 + 2 ^ 8 * S.N_dh * S.N_sess_tot) +
      (2 ^ 16 * (b.q_total + 1) * (S.N_dh + S.N_sess_tot) +
        63488 * S.N_dh ^ 2 + 130816 * S.N_dh * S.N_sess_tot + 65536 * S.N_sess_tot ^ 2) := by ring
  rw [hEq]
  exact Nat.le_add_right _ _

theorem shcrKeyInd1KeyDslProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    SignalPqxdh.LegacyCosted.GRed2BlockBounded S b ℓ (shcrKeyInd1KeyDslProg S b) :=
  _root_.SignalPqxdh.LegacyCosted.gred2BlockBounded_of_totalCost_le
    pqSamplers_sizeHonest
    _root_.SignalPqxdh.LegacyCosted.one_le_pqPrimIface_qCost
    _root_.SignalPqxdh.LegacyCosted.one_le_pqSamplers_sCost
    S b ℓ (shcrKeyInd1KeyDslProg S b)
    ((shcrKeyInd1KeyDslProg_totalCost_le_stepCostBudget S b).trans
      (securityStepCostBudget_le_legacy S b))

theorem initPrin1KeyB_size_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrin1KeyB (Δ := Δ) K st u).size ≤ (initPrinB (Δ := Δ) K st u).size := by
  simp only [initPrin1KeyB, initPrinB, bindV, eAny, natEq,
    stPrin, stSecb, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    stUpd, stMk, peMk, rs, rNone, rInitPrin,
    sBytes32, qX25519Base, qSigPkGen, v, Comp.size, Expr.size]
  omega

theorem caseSumV_size_le_left {τ₁ τ₂ τ : PT} {Γ : List PT}
    (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (l₁ l₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (r : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (hl : (l₁ .zero).size ≤ (l₂ .zero).size) :
    (caseSumV e l₁ r).size ≤ (caseSumV e l₂ r).size := by
  dsimp only [caseSumV, Comp.size]
  omega

theorem shcr1KeyPostC_size_le_shcrPostC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcr1KeyPostC (Δ := Δ) S K s q).size ≤ (shcrPostC (Δ := Δ) S K s q).size := by
  rw [shcrPostC_eq_tail]
  unfold shcr1KeyPostC
  refine caseSumV_size_le_left _ _ _ (shcrPostTailC S K s) ?_
  have h := initPrin1KeyB_size_le K (Γ₁ := keyIndStateTy :: (.nat :: Δ))
    (Γ₂ := .nat :: Δ) (Δ := keyIndStateTy :: (.nat :: Δ)) .zero .zero
  simp only [onBase, bindV, letV, Comp.size]
  omega

theorem shcr1KeyPreC_size_le_shcrPreC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcr1KeyPreC (Δ := Δ) S K s q).size ≤ (shcrPreC (Δ := Δ) S K s q).size := by
  have hPost := shcr1KeyPostC_size_le_shcrPostC S K (Γ₁ := Γ₁) (Γ₂ := Γ₂)
    (Δ := (.opt pauseTy) :: Δ) s q
  simp only [shcr1KeyPreC, shcrPreC, bindV, caseOptV, Comp.size]
  omega

theorem shcrKeyInd1KeyProg_size_le_twoKey (S : Setup) (Q K : Nat) :
    (shcrKeyInd1KeyProg S Q K).size ≤ (shcrKeyIndProg S Q K).size := by
  have hInit : (shcrKeyInd1KeyProg S Q K).init.size = (shcrKeyIndProg S Q K).init.size := rfl
  have hCh : (shcrKeyInd1KeyProg S Q K).chDone.size = (shcrKeyIndProg S Q K).chDone.size := rfl
  have hRes : (shcrKeyInd1KeyProg S Q K).resume.size = (shcrKeyIndProg S Q K).resume.size := rfl
  have hFin : (shcrKeyInd1KeyProg S Q K).finish.size = (shcrKeyIndProg S Q K).finish.size := rfl
  have hPre : (shcrKeyInd1KeyProg S Q K).handlePre.size ≤ (shcrKeyIndProg S Q K).handlePre.size :=
    shcr1KeyPreC_size_le_shcrPreC S K (Γ₁ := [shcrStTy, keyIndQueryTy])
      (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hPost : (shcrKeyInd1KeyProg S Q K).handlePost.size ≤ (shcrKeyIndProg S Q K).handlePost.size :=
    shcr1KeyPostC_size_le_shcrPostC S K (Γ₁ := [shcrStTy, keyIndQueryTy])
      (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  unfold TwoStageCostedReduction.size
  rw [hInit, hCh, hRes, hFin]
  omega

@[simp] private theorem sh_partnerC_size {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) :
    (partnerC (Δ := Δ) s r).size = 211 := by
  simp only [partnerC, bindV, qPow8, getDBytes, optBytesEq, eLet2, eLet, eCaseOpt,
    eqB, litB, v, Comp.size, Expr.size]
  simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
    Ops.sum, Sum.elim_inl]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
private theorem shcrPostC_size_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPostC (Δ := Δ) S K s q).size ≤
      65 * _root_.ReductionDsl.bits K + 30 * _root_.ReductionDsl.bits S.N_dh +
        5 * _root_.ReductionDsl.bits S.N_sess_tot + 12000 := by
  simp (config := { maxSteps := 500000 }) only [shcrPostC, shcrGenSpkB, initGuardE, shcrInitiateC,
    shcrAcceptB, onBase, scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
    initPrinB, corruptB, genSpkB, genOpkB, initSidE, initFinishC, preCheckC, checkSigsC,
    acceptOpkB, acceptNoOpkB, testB, revealB, roB, revealDhB, registerB, revealSpkB,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, checkProvC, sh_partnerC_size, recordRespC, hkdfOrRoC,
    aiIkSk, aiSpkSk, aiOpkSk, aiPqSk, aiReplay, aiHdr, acceptKeysC,
    qK, qJ, qO, qHdr, qKJO,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    stMk, stUpd, peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbMk, sbUpd,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
    seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr,
    seTested, seRevealed, seMk, seUpd,
    reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal, reDrRand,
    reTested, reRevealed, reMk, reUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
    rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rSpkSk,
    isSomeE, isNoneRespE, getDBytes, optFst, optSnd, dhOptNZ, guardE, rs, kyberCheckE, freshE,
    orE, natEq, nat2Eq, nat3Eq, optU32Eq, sidEq, kyberEq, nonZero32,
    buildSecretsE, eLet2, shcrFinE,
    bindV, letV, caseOptV, caseSumV, findMV, anyMV, eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap, v,
    litB, catB, consB, widenB, lenB, eqB, u32OfNat, eqU32,
    sBytes32, sRandom64, sDrKey96,
    qX25519, qX25519Base, qIsCanonical, qPow8, qSigPkGen, qSigSign, qSigVerify,
    qKemKeyGen, qKemEncaps, qKemDecaps, qHkdfDerive96, encEC, encKEM,
    Comp.size, Expr.size, Bool.not_true, ↓reduceIte, Bool.false_eq_true]
  simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
    _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Ops.sum, Sum.elim_inl, Sum.elim_inr]
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hnr := nRecv_le_spk_tot S
  have bNRecv : _root_.ReductionDsl.bits (nRecv S) ≤ _root_.ReductionDsl.bits S.N_dh :=
    _root_.ReductionDsl.bits_mono (by omega)
  have bMin1 : _root_.ReductionDsl.bits (S.N_recv.min S.N_spk_tot) ≤ _root_.ReductionDsl.bits S.N_dh :=
    _root_.ReductionDsl.bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have bMin2 : _root_.ReductionDsl.bits (S.N_opk.min S.N_opk_tot) ≤ _root_.ReductionDsl.bits S.N_dh :=
    _root_.ReductionDsl.bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have bMin3 : _root_.ReductionDsl.bits (S.N_send_opk.min S.N_send_opk_tot) ≤ _root_.ReductionDsl.bits S.N_dh :=
    _root_.ReductionDsl.bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have bMin4 : _root_.ReductionDsl.bits (S.N_send_no_opk.min S.N_send_no_opk_tot) ≤ _root_.ReductionDsl.bits S.N_dh :=
    _root_.ReductionDsl.bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have bId : _root_.ReductionDsl.bits S.N_id ≤ _root_.ReductionDsl.bits S.N_dh :=
    _root_.ReductionDsl.bits_mono (by omega)
  have bSpk : _root_.ReductionDsl.bits S.N_spk_tot ≤ _root_.ReductionDsl.bits S.N_dh :=
    _root_.ReductionDsl.bits_mono (by omega)
  have bOpk : _root_.ReductionDsl.bits S.N_opk_tot ≤ _root_.ReductionDsl.bits S.N_dh :=
    _root_.ReductionDsl.bits_mono (by omega)
  have bSend : _root_.ReductionDsl.bits S.N_send_tot ≤ _root_.ReductionDsl.bits S.N_dh :=
    _root_.ReductionDsl.bits_mono (by omega)
  have bSendO : _root_.ReductionDsl.bits S.N_send_opk_tot ≤ _root_.ReductionDsl.bits S.N_dh :=
    _root_.ReductionDsl.bits_mono (by omega)
  have bSendN : _root_.ReductionDsl.bits S.N_send_no_opk_tot ≤ _root_.ReductionDsl.bits S.N_dh :=
    _root_.ReductionDsl.bits_mono (by omega)
  have hb0 : _root_.ReductionDsl.bits 0 = 1 := by decide
  have hb1 : _root_.ReductionDsl.bits 1 = 1 := by decide
  have hb32 : _root_.ReductionDsl.bits 32 = 6 := by decide
  have : _root_.ReductionDsl.bits (min K S.N_dh) ≤ _root_.ReductionDsl.bits S.N_dh :=
    _root_.ReductionDsl.bits_mono (Nat.min_le_right _ _)
  have : _root_.ReductionDsl.bits (K.min S.N_dh) ≤ _root_.ReductionDsl.bits S.N_dh :=
    _root_.ReductionDsl.bits_mono (Nat.min_le_right _ _)
  have : _root_.ReductionDsl.bits (min K S.N_sess_tot) ≤ _root_.ReductionDsl.bits S.N_sess_tot :=
    _root_.ReductionDsl.bits_mono (Nat.min_le_right _ _)
  have : _root_.ReductionDsl.bits (K.min S.N_sess_tot) ≤ _root_.ReductionDsl.bits S.N_sess_tot :=
    _root_.ReductionDsl.bits_mono (Nat.min_le_right _ _)
  omega

private theorem shcrPreC_size_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPreC (Δ := Δ) S K s q).size ≤
      75 * _root_.ReductionDsl.bits K + 45 * _root_.ReductionDsl.bits S.N_dh +
        10 * _root_.ReductionDsl.bits S.N_sess_tot + 14500 := by
  have hPost := shcrPostC_size_le S K (Γ₁ := Γ₁) (Γ₂ := Γ₂) (Δ := .opt pauseTy :: Δ) s q
  have hPC : (pauseCheckC (Δ := Δ) S K s q).size ≤
      10 * _root_.ReductionDsl.bits K + 15 * _root_.ReductionDsl.bits S.N_dh +
        5 * _root_.ReductionDsl.bits S.N_sess_tot + 2000 := by
    simp only [pauseCheckC, tryPauseC, initGuardE, initSidE, preCheckC, checkSigsC,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, resolveSigPkC,
      scBase, scCnt, scSIdx,
      stPrin, stSpks, stOpks, stSess, stAdv,
      peIkAPk, peIkSignPk, sbSpkPk, oeOpkPk, seSid,
      buIkB, buSpkB, buSpkSig, buOpkB, buPqspkB, buPqspkSig,
      isSomeE,
      orE, natEq, nat2Eq, nat3Eq, sidEq, eLet2,
      bindV, letV, caseOptV, caseSumV, findMV, anyMV, eLet, eCaseOpt, eCaseSum, eFind, eAny, v,
      consB, eqB, qPow8, qSigVerify, encEC, encKEM,
      Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
      Ops.sum, Sum.elim_inl]
    have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
    have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
    have bMin3 : _root_.ReductionDsl.bits (S.N_send_opk.min S.N_send_opk_tot) ≤ _root_.ReductionDsl.bits S.N_dh :=
      _root_.ReductionDsl.bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
    have bMin4 : _root_.ReductionDsl.bits (S.N_send_no_opk.min S.N_send_no_opk_tot) ≤ _root_.ReductionDsl.bits S.N_dh :=
      _root_.ReductionDsl.bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
    have bSendO : _root_.ReductionDsl.bits S.N_send_opk_tot ≤ _root_.ReductionDsl.bits S.N_dh :=
      _root_.ReductionDsl.bits_mono (by omega)
    have : _root_.ReductionDsl.bits (min K S.N_dh) ≤ _root_.ReductionDsl.bits S.N_dh :=
      _root_.ReductionDsl.bits_mono (Nat.min_le_right _ _)
    have : _root_.ReductionDsl.bits (K.min S.N_dh) ≤ _root_.ReductionDsl.bits S.N_dh :=
      _root_.ReductionDsl.bits_mono (Nat.min_le_right _ _)
    omega
  simp only [shcrPreC, bindV, caseOptV, buPqspkB, v, Comp.size, Expr.size]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem shcrKeyIndProg_size_le (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).size ≤
      _root_.ReductionDsl.bits Q + 150 * _root_.ReductionDsl.bits K +
        90 * _root_.ReductionDsl.bits S.N_dh + 25 * _root_.ReductionDsl.bits S.N_sess_tot + 29000 := by
  have hPre : (shcrKeyIndProg S Q K).handlePre.size ≤
      75 * _root_.ReductionDsl.bits K + 45 * _root_.ReductionDsl.bits S.N_dh +
        10 * _root_.ReductionDsl.bits S.N_sess_tot + 14500 :=
    shcrPreC_size_le S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hPost : (shcrKeyIndProg S Q K).handlePost.size ≤
      65 * _root_.ReductionDsl.bits K + 30 * _root_.ReductionDsl.bits S.N_dh +
        5 * _root_.ReductionDsl.bits S.N_sess_tot + 12000 :=
    shcrPostC_size_le S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hInit : (shcrKeyIndProg S Q K).init.size ≤ 100 := by
    dsimp only [shcrKeyIndProg]
    split <;> {
      simp only [emptyStE, stMk, scMk, bindV, v, sBool, sIndex, Comp.size, Expr.size, bits_0]
      omega
    }
  have hRest : (shcrKeyIndProg S Q K).chDone.size +
      (shcrKeyIndProg S Q K).resume.size + (shcrKeyIndProg S Q K).finish.size ≤
      _root_.ReductionDsl.bits Q + 10 * _root_.ReductionDsl.bits K +
        15 * _root_.ReductionDsl.bits S.N_dh + 10 * _root_.ReductionDsl.bits S.N_sess_tot + 1900 := by
    dsimp only [shcrKeyIndProg]
    simp (config := { maxSteps := 500000 }) only [
      shcrResumeC, shcrExtractC, shcrFinE,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd, rrCt,
      initFinishC,
      findHonestC,
      honestPeerC, checkProvC, sh_partnerC_size, hkdfOrRoC,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      stMk, stUpd, peSecIKA0, peIkAPk, peCorrupted,
      sbSpkPk, sbPqspkPk, oeOpkPk,
      seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
      seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seHdr,
      seTested, seRevealed, seMk, seUpd, reDrRand,
      buIkB, buSpkId, buSpkB, buOpkB, buPqspkId, buPqspkB,
      hdMk, rHdr, rInitUnfresh,
      isSomeE, getDBytes, optBytesEq, optFst, optSnd, rs,
      orE, natEq,
      buildSecretsE, eLet2,
      bindV, letV, caseOptV, findMV, anyMV, eLet, eCaseOpt, eFind, eAny, v,
      litB, catB, widenB, eqB,
      sBytes32, sDrKey96,
      qX25519, qX25519Base, qPow8,
      qKemDecaps,
      Comp.size, Expr.size, ↓reduceIte]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
      Ops.sum, Sum.elim_inl]
    have hb0 : _root_.ReductionDsl.bits 0 = 1 := by decide
    have hb1 : _root_.ReductionDsl.bits 1 = 1 := by decide
    have : _root_.ReductionDsl.bits (min K S.N_dh) ≤ _root_.ReductionDsl.bits S.N_dh :=
      _root_.ReductionDsl.bits_mono (Nat.min_le_right _ _)
    have : _root_.ReductionDsl.bits (K.min S.N_dh) ≤ _root_.ReductionDsl.bits S.N_dh :=
      _root_.ReductionDsl.bits_mono (Nat.min_le_right _ _)
    have : _root_.ReductionDsl.bits (min K S.N_sess_tot) ≤ _root_.ReductionDsl.bits S.N_sess_tot :=
      _root_.ReductionDsl.bits_mono (Nat.min_le_right _ _)
    have : _root_.ReductionDsl.bits (K.min S.N_sess_tot) ≤ _root_.ReductionDsl.bits S.N_sess_tot :=
      _root_.ReductionDsl.bits_mono (Nat.min_le_right _ _)
    omega
  unfold _root_.ReductionDsl.TwoStageCostedReduction.size
  omega

theorem shcrKeyIndDslProg_size_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (shcrKeyIndDslProg S b).size ≤
      29000 + 266 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) :=
  shcrKeyIndProg_size_le_stepCostBudget S b (keyIndLoopBound b) le_rfl

theorem shcrKeyInd1KeyDslProg_size_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyDslProg S b).size ≤
      29000 + 266 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) :=
  (shcrKeyInd1KeyProg_size_le_twoKey S b.q_total (keyIndLoopBound b)).trans
    (shcrKeyIndDslProg_size_le_stepCostBudget S b)

/-- Run-local two-stage output block-size bound for `shcrKeyInd1KeyDslProg`. -/
theorem shcrKeyInd1KeyDslProg_blocks_when (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hfit : ∀ u, AllGameQueriesFit ℓ (keyIndCodec S) (A u))
    (x : (Ty.prod (B 1568) (B 3168)).denote)
    (hx : _root_.ReductionDsl.ValFits ℓ (Ty.prod (B 1568) (B 3168)) x)
    (cm : Bytes × Mid (keyIndSpec S) Bool pauseTy.denote shcrStTy.denote Bytes)
    (hcm : cm ∈ supportWhen (SignalPqxdh.LegacyCosted.pqPrimIface.AnswerFits ℓ)
      ((shcrKeyInd1KeyDslProg S b).eval1 A x b.q_total false)) :
    _root_.ReductionDsl.ValFits (SignalPqxdh.LegacyCosted.outputSizeBudget S b ℓ) (B 1568) cm.1 ∧
    ∀ (y : (Ty.prod (B 32) (B 1568)).denote),
      _root_.ReductionDsl.ValFits ℓ (Ty.prod (B 32) (B 1568)) y →
      ∀ z ∈ supportWhen (SignalPqxdh.LegacyCosted.pqPrimIface.AnswerFits ℓ)
        ((shcrKeyInd1KeyDslProg S b).eval2 cm.2 y b.q_total false),
        _root_.ReductionDsl.ValFits (SignalPqxdh.LegacyCosted.outputSizeBudget S b ℓ) (B 1568) z := by
  let R := shcrKeyInd1KeyDslProg S b
  obtain ⟨hcm1, hmid⟩ := R.fits_eval1_when pqO_sizeHonest pqSamplers_sizeHonest ℓ ℓ 0
    (fun _ => trivial) A hfit b.q_total ℓ x hx false cm hcm
  have hCost : R.totalCost b.q_total ≤ _root_.SignalPqxdh.LegacyCosted.stepCostBudget S b :=
    (shcrKeyInd1KeyDslProg_totalCost_le_stepCostBudget S b).trans
      (securityStepCostBudget_le_legacy S b)
  have hNq : R.nq b.q_total ≤ R.totalCost b.q_total :=
    CryptoVerification.E2E.Costed.TwoStageCostedReduction.nq_le_totalCost R b.q_total
  refine ⟨Ty.fits_mono ?_ (B 1568) cm.1 hcm1, fun y hy z hz => ?_⟩
  · unfold _root_.SignalPqxdh.LegacyCosted.outputSizeBudget
    have hMul := Nat.mul_le_mul_right ℓ hNq
    nlinarith
  · have hz' := R.fits_eval2_when pqO_sizeHonest pqSamplers_sizeHonest ℓ ℓ 0
      (fun _ => trivial) cm.2 _ hmid y ℓ hy b.q_total false z hz
    refine Ty.fits_mono ?_ (B 1568) z hz'
    have hPreCost : b.q_total * R.handlePre.cost ≤
        b.q_total * max pqPrimIface.uCost (max R.handlePre.cost R.handlePost.cost + (keyIndCodec S).codecCost) :=
      Nat.mul_le_mul_left _ (le_trans (le_trans (le_max_left _ _) (Nat.le_add_right _ _)) (le_max_right _ _))
    have hPostCost : b.q_total * R.handlePost.cost ≤
        b.q_total * max pqPrimIface.uCost (max R.handlePre.cost R.handlePost.cost + (keyIndCodec S).codecCost) :=
      Nat.mul_le_mul_left _ (le_trans (le_trans (le_max_right _ _) (Nat.le_add_right _ _)) (le_max_right _ _))
    have hResCost : R.resume.cost ≤ max R.chDone.cost R.resume.cost := le_max_right _ _
    have hPreNq : b.q_total * R.handlePre.nq ≤ b.q_total * max R.handlePre.nq R.handlePost.nq :=
      Nat.mul_le_mul_left _ (le_max_left _ _)
    have hPostNq : b.q_total * R.handlePost.nq ≤ b.q_total * max R.handlePre.nq R.handlePost.nq :=
      Nat.mul_le_mul_left _ (le_max_right _ _)
    have hResNq : R.resume.nq ≤ max R.chDone.nq R.resume.nq := le_max_right _ _
    have hC12 : R.init.cost + b.q_total * R.handlePre.cost +
        (R.resume.cost + b.q_total * R.handlePost.cost + R.finish.cost) ≤ 2 * R.totalCost b.q_total := by
      dsimp only [TwoStageCostedReduction.totalCost] at *; omega
    have hN12 : R.init.nq + b.q_total * R.handlePre.nq +
        (R.resume.nq + b.q_total * R.handlePost.nq + R.finish.nq) ≤ 2 * R.nq b.q_total := by
      dsimp only [TwoStageCostedReduction.nq, TwoStageCostedReduction.totalQueries, Comp.nq] at *; omega
    unfold _root_.SignalPqxdh.LegacyCosted.outputSizeBudget
    nlinarith

/-! ## Branch evaluation and invariant preservation -/

theorem initPrin1KeyB_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ keyIndStateTy) (env : Env Δ) (s : KeyIndState S)
    (hs : env.get (Ext.wk st) = keyIndStateToVal s) (hB : KeyIndListsBounded s K)
    (uV : Var Γ₂ .nat) (u : Fin S.N_id) (hu : env.get (Ext.wk uV) = u.val) :
    (initPrin1KeyB K st uV).eval env =
      encRS <$> (pqxdhKeyIndImpl1KeyRoPrim S (.initPrin u)).run s := by
  unfold initPrin1KeyB
  core_simp [hs, hu, List.take_of_length_le, hB.principals_le]
  simp only [pqxdhKeyIndImpl1KeyRoPrim]
  by_cases h : (s.principals.any fun x => x.1 == ↑u) = true
  · simp [h, encRS, keyIndRespToVal, keyIndRenc]
  · simp [h, encRS, keyIndRespToVal, keyIndRenc, liftM, sampleScalar32]

theorem pqxdhKeyIndImpl1KeyRoPrim_hol (S : Setup) (n : Nat) (q : KeyIndQuery S)
    (s : KeyIndState S) (hB : KeyIndListsBounded s n) :
    HoldsOnLeaves (fun x => KeyIndListsBounded x.2 (n + 1))
      ((pqxdhKeyIndImpl1KeyRoPrim S q).run s) := by
  cases q with
  | initPrin u =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hB
    simp only [pqxdhKeyIndImpl1KeyRoPrim]
    khol_simp
    split
    · exact HoldsOnLeaves.pure (by khol_leaf)
    · refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ => ?_
      khol_simp
      exact HoldsOnLeaves.pure (by khol_leaf)
  | _ =>
    simpa [pqxdhKeyIndImpl1KeyRoPrim, StateT.run_bind, StateT.run_get, pure_bind] using
      pqxdhKeyIndImplPrim_hol true S n _ s hB

theorem pqxdhKeyIndShCrPrimImpl1Key_inv (S : Setup) (pk sk : Bytes) (n : ℕ) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (hI : ShInv pk sk n h) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => ShInv pk sk (n + 1) x.2)
      ((pqxdhKeyIndShCrPrimImpl1Key true S q).run h) := by
  cases q with
  | initPrin u =>
    simp only [pqxdhKeyIndShCrPrimImpl1Key, liftShCrBasePrim, StateT.run]
    exact HoldsOnLeaves.bind (pqxdhKeyIndImpl1KeyRoPrim_hol S n (.initPrin u) h.base hI.bnd)
      fun p hp => HoldsOnLeaves.pure ⟨hp, hI.tpk, hI.tsk⟩
  | _ =>
    simpa [pqxdhKeyIndShCrPrimImpl1Key] using pqxdhKeyIndShCrPrimImpl_inv S pk sk n _ h hI

theorem caseSumV_eval_inr {τ₁ τ₂ τ : PT} {Γ : List PT}
    (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (l₁ l₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (r : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (env : Env Γ) {b : τ₂.denote} (hb : e.eval env = .inr b) :
    (caseSumV e l₁ r).eval env = (caseSumV e l₂ r).eval env := by
  simp [caseSumV, Comp.eval, hb]

theorem shcr1KeyPostC_eval (S : Setup) (K n : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sV : Var Γ₁ shcrStTy) (qV : Var Γ₂ keyIndQueryTy) (env : Env Δ) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (sIdx : Nat) (chosen : Bytes)
    (hs : env.get (Ext.wk sV) = shcrStToVal h sIdx chosen)
    (hq : env.get (Ext.wk qV) = keyIndQueryToVal q)
    (hB : KeyIndListsBounded h.base n) (hn : n + 1 ≤ K) :
    (shcr1KeyPostC S K sV qV).eval env =
      encSCS sIdx chosen <$> (pqxdhKeyIndShCrPrimImpl1Key true S q).run h := by
  cases q with
  | initPrin u =>
    have hK : KeyIndListsBounded h.base K := hB.mono (by omega)
    unfold shcr1KeyPostC pqxdhKeyIndShCrPrimImpl1Key
    simp only [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal]
    refine Eq.trans (b := encSCS sIdx chosen <$>
        (liftShCrBasePrim (S := S) (pqxdhKeyIndImpl1KeyRoPrim S (.initPrin u))).run h) ?_ rfl
    exact onBase_eval S _ _ h sIdx chosen (by simpa [Ext.step_wk', Env.get_succ'] using hs) _ _
      (initPrin1KeyB_eval S K _ _ h.base rfl hK _ u rfl)
  | _ =>
    have hEq : (shcr1KeyPostC S K sV qV).eval env = (shcrPostC S K sV qV).eval env := by
      rw [shcrPostC_eq_tail]
      unfold shcr1KeyPostC
      simp [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal]
    rw [hEq, shcrPostC_eval S K n sV qV env _ h sIdx chosen hs hq hB hn]
    rfl

/-! ## Stage 1 and Stage 2 simulation -/

def stepMid1Key (S : Setup) (sIdx : ℕ) (q : KeyIndQuery S) (h : KeyIndShCrState S) :
    OracleComp PrimBaseSpec
      ((KeyIndResponse × KeyIndShCrState S) ⊕ (Bytes × (PauseMid S × KeyIndShCrState S))) := do
  match ← tryPauseMid S sIdx q h with
  | some d => pure (.inr (d.2.1.pqspkB, (d, h)))
  | none => Sum.inl <$> (pqxdhKeyIndShCrPrimImpl1Key true S q).run h

theorem shcr1KeyPreC_eval (S : Setup) (K n : ℕ) (q : KeyIndQuery S) (h : KeyIndShCrState S)
    (sIdx : ℕ) (chosen : Bytes) (hB : KeyIndListsBounded h.base n) (hn : n + 1 ≤ K) :
    (shcr1KeyPreC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).eval
        (.cons (shcrStToVal h sIdx chosen) (.cons (keyIndQueryToVal q) .nil)) =
      Sum.map (encSCS sIdx chosen) (Prod.map id (Prod.map encPause (shcrStToVal · sIdx chosen))) <$>
        stepMid1Key S sIdx q h := by
  have hK : KeyIndListsBounded h.base K := hB.mono (by omega)
  unfold shcr1KeyPreC
  simp only [bindV, caseOptV, Comp.eval]
  rw [pauseCheckC_eval S K _ _ h sIdx chosen rfl hK _ q rfl]
  simp only [stepMid1Key, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | d
  · simp only [Option.map_none, Expr.eval]
    rw [shcr1KeyPostC_eval S K n _ _ _ q h sIdx chosen rfl rfl hB hn]
    simp [map_eq_bind_pure_comp, Expr.eval, v]
  · obtain ⟨sid, bu, k, e⟩ := d
    simp [Expr.eval, v, encPause, shcrStToVal, preKeyBundleToVal]

theorem stepUntilShCr1Key_eq (S : Setup) (sIdx : ℕ) (mx : OracleComp (unifSpec + keyIndSpec S) Bool)
    (h : KeyIndShCrState S) (fuel : ℕ) :
    stepUntilShCrFuelKeyInd1KeyPrim S sIdx mx h fuel =
      Gsh S <$> stepUntilPauseFuel false (stepMid1Key S sIdx) mx fuel h := by
  refine stepUntilPauseFuel_char false (stepMid1Key S sIdx) (Gsh S)
    (fun mx fuel h => stepUntilShCrFuelKeyInd1KeyPrim S sIdx mx h fuel) ?_ ?_ ?_ ?_ mx fuel h
  · intro a fuel s; rfl
  · intro uq k fuel s
    simp only [stepUntilShCrFuelKeyInd1KeyPrim]
    rw [OracleComp.construct_query_bind]
  · intro gq k s
    simp only [stepUntilShCrFuelKeyInd1KeyPrim]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k fuel s
    simp only [stepUntilShCrFuelKeyInd1KeyPrim]
    rw [OracleComp.construct_query_bind]
    dsimp only
    rw [tryPauseMid_shallow, bind_map_left]
    simp only [stepMid1Key, bind_assoc]
    refine bind_congr fun o => ?_
    rcases o with _ | d
    · simp only [Option.map_none, map_eq_bind_pure_comp, bind_assoc]
      rfl
    · simp only [Option.map_some, pure_bind]
      rfl

theorem runWithFuelShCr1Key_eq (S : Setup) (mx : OracleComp (unifSpec + keyIndSpec S) Bool)
    (h : KeyIndShCrState S) (fuel : ℕ) :
    runWithFuelKeyInd1KeyShCrPrim S mx h fuel =
      runWithFuelPrim false (fun q s => (pqxdhKeyIndShCrPrimImpl1Key true S q).run s) mx fuel h := by
  have := runWithFuelPrim_char false (fun q s => (pqxdhKeyIndShCrPrimImpl1Key true S q).run s) id
    (fun mx fuel h => runWithFuelKeyInd1KeyShCrPrim S mx h fuel) (fun _ _ _ => rfl)
    (fun uq k fuel s => by
      simp only [runWithFuelKeyInd1KeyShCrPrim]; rw [OracleComp.construct_query_bind])
    (fun gq k s => by
      simp only [runWithFuelKeyInd1KeyShCrPrim]; rw [OracleComp.construct_query_bind]; rfl)
    (fun gq k fuel s => by
      simp only [runWithFuelKeyInd1KeyShCrPrim]; rw [OracleComp.construct_query_bind]) mx fuel h
  rw [this, id_map]

theorem stepMid1Key_inv (S : Setup) (sIdx : ℕ) (pk sk : Bytes) (n : ℕ) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (hI : ShInv pk sk n h) :
    HoldsOnLeaves (PreStepInvC (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) n)
      (stepMid1Key S sIdx q h) := by
  unfold stepMid1Key
  refine HoldsOnLeaves.bind_const _ fun o => ?_
  rcases o with _ | d
  · exact HoldsOnLeaves.map _ (pqxdhKeyIndShCrPrimImpl1Key_inv S pk sk n q h hI) fun _ hx => hx
  · exact HoldsOnLeaves.pure ⟨rfl, hI⟩

def midRun1Key (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S) (pk sk : Bytes) :
    OracleComp PrimBaseSpec (ℕ × (Option Bytes ×
      RedProg2State (keyIndSpec S) Bool (PauseMid S) (KeyIndShCrState S))) :=
  if S.N_spk_tot * S.N_send_tot = 0 then do
    let secb ← embedUnif ($ᵗ Bool)
    let r ← stepUntilPauseFuel false (stepMid1Key S 0) A.run b.q_total
      (initSh S secb 0 pk sk)
    pure (0, r)
  else do
    let uIdx ← embedUnif (RoKem.sampleIndexRange S.N_id)
    let jIdx ← embedUnif (RoKem.sampleIndexRange S.N_recv)
    let sIdx ← embedUnif (RoKem.sampleIndexRange S.N_send_tot)
    let secb ← embedUnif ($ᵗ Bool)
    let r ← stepUntilPauseFuel false (stepMid1Key S sIdx) A.run b.q_total
      (initSh S secb (uIdx * S.N_recv + jIdx) pk sk)
    pure (sIdx, r)

def midAdv1Key (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S) : KemShCrAdv where
  State := Bytes × Bytes × ℕ × (Option Bytes ×
    RedProg2State (keyIndSpec S) Bool (PauseMid S) (KeyIndShCrState S))
  choosePk := fun pk sk => (fun x => (chosenOf pk x.2.2, (pk, sk, x))) <$> midRun1Key S b A pk sk
  findCollision := fun st => findCollisionKeyInd1KeyPrim S b (toShallow st)
  q_prim := primQueryBudget S b

theorem kemShCrExp_mid1Key_core (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : KeyIndAdversary S) :
    KemShCr P (shcrReductionKeyInd1KeyCore S b A) = KemShCr P (midAdv1Key S b A) := by
  refine SignalPqxdh.Security.ReductionDsl.AuthHs.kemShCr_eq_of_choosePk_spk_send
    P S (shcrReductionKeyInd1KeyCore S b A) (midAdv1Key S b A) toShallow
    (fun bIdx sIdx pk sk => do
      let secb ← embedUnif ($ᵗ Bool)
      let r ← stepUntilPauseFuel false (stepMid1Key S sIdx) A.run b.q_total
        (initSh S secb bIdx pk sk)
      pure (chosenOf pk r.2, (pk, sk, sIdx, r))) ?_ ?_ (fun _ _ _ => rfl)
  · intro pk sk
    simp only [shcrReductionKeyInd1KeyCore, choosePkKeyInd1KeyPrimAt, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Function.comp_def]
    refine bind_congr fun idx => bind_congr fun secb => ?_
    rw [stepUntilShCr1Key_eq, bind_map_left]
    refine bind_congr fun r => ?_
    obtain ⟨c, st⟩ := r
    rcases st with ⟨a, h⟩ | ⟨q, d, h, k⟩ <;> rfl
  · intro pk sk
    simp only [midAdv1Key, midRun1Key]
    split_ifs <;> simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

def stepPreD1Key (S : Setup) (Q K : ℕ) (q : KeyIndQuery S) (st : shcrStTy.denote) :
    OracleComp PrimBaseSpec ((KeyIndResponse × shcrStTy.denote) ⊕
      (Bytes × (pauseTy.denote × shcrStTy.denote))) :=
  (shcrKeyInd1KeyProg S Q K).handlePre.eval (.cons st (.cons (keyIndQueryToVal q) .nil)) >>=
    fun (x : SCS.denote ⊕ (Bytes × (pauseTy.denote × shcrStTy.denote))) => match x with
    | .inl (rVal, st') => pure (.inl (valToKeyIndResp rVal, st'))
    | .inr (ch1Val, (pVal, st')) => pure (.inr (ch1Val, (pVal, st')))

theorem stepPreD1Key_eq (S : Setup) (Q K K' : ℕ) (sIdx : ℕ) (pk sk : Bytes) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (hI : ShInv pk sk K' h) (hK : K' + 1 ≤ K) :
    stepPreD1Key S Q K q (shcrStToVal h sIdx pk) =
      Sum.map (Prod.map id (shcrStToVal · sIdx pk))
        (Prod.map id (Prod.map encPause (shcrStToVal · sIdx pk))) <$> stepMid1Key S sIdx q h := by
  unfold stepPreD1Key
  have hpre : (shcrKeyInd1KeyProg S Q K).handlePre.eval
      (.cons (shcrStToVal h sIdx pk) (.cons (keyIndQueryToVal q) .nil)) = _ :=
    shcr1KeyPreC_eval S K K' q h sIdx pk hI.bnd hK
  rw [hpre, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  erw [bind_assoc]
  refine bind_congr fun x => ?_
  rcases x with ⟨r, h'⟩ | ⟨c, d, h'⟩
  · have hr : valToKeyIndResp (keyIndRespToVal r) = r := keyIndRdec_keyIndRenc r
    simp only [Function.comp_apply, Sum.map_inl, encSCS, Prod.map, id]
    erw [pure_bind]
    simp only [hr]
  · rfl

theorem eval1_1Key_unfold (S : Setup) (Q K : ℕ) (A : KeyIndAdversary S) (pk sk : Bytes)
    (fuel : ℕ) :
    (shcrKeyInd1KeyProg S Q K).eval1 (fun _ => A.run) (pk, sk) fuel false =
    (do
      let (_, st0) ← (shcrKeyInd1KeyProg S Q K).init.eval (.cons (pk, sk) .nil)
      let r : Option Bytes × RedProg2State (keyIndSpec S) Bool pauseTy.denote shcrStTy.denote ←
          stepUntilPauseFuel false (stepPreD1Key S Q K) A.run fuel st0
      match r with
      | (_, .done aOut stFinal) => do
        let v ← (shcrKeyInd1KeyProg S Q K).chDone.eval (.cons stFinal (.cons aOut .nil))
        pure (v, .done aOut stFinal)
      | (c?, .paused gq p stPaused c) =>
        let ch1 := c?.getD pk
        pure (ch1, .paused gq ch1 p stPaused c) :
      OracleComp PrimBaseSpec (Bytes × Mid (keyIndSpec S) Bool pauseTy.denote
        shcrStTy.denote Bytes)) := by
  unfold TwoStageCostedReduction.eval1
  refine bind_congr (m := OracleComp PrimBaseSpec) fun ast0 => ?_
  rcases ast0 with ⟨a, st0⟩
  dsimp only
  rw [GRed2_run1_eq_stepUntilPauseFuel (shcrKeyInd1KeyProg S Q K) false pk A.run fuel st0,
    bind_map_left]
  refine bind_congr2 ?_ fun r => ?_
  · congr 1; funext q st; unfold stepPreD1Key
    refine bind_congr fun x => ?_
    rcases x with ⟨_, _⟩ | ⟨_, _, _⟩ <;> rfl
  rcases r with ⟨c?, ⟨aOut, stFinal⟩ | ⟨gq, p, stPaused, c⟩⟩ <;> rfl

theorem stepRun1Key_bounded (S : Setup) (Q K Ks sIdx : ℕ) (pk sk : Bytes) (A : KeyIndAdversary S)
    (h0 : KeyIndShCrState S) (hI0 : ShInv pk sk 0 h0)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) Ks)
    (hK : Ks + 1 ≤ K) :
    HoldsOnLeaves (Stage1InvC (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) Ks)
        (stepUntilPauseFuel false (stepMid1Key S sIdx) A.run Ks h0) ∧
      stepUntilPauseFuel false (stepPreD1Key S Q K) A.run Ks (shcrStToVal h0 sIdx pk) =
        Prod.map id (RedProg2State.mapSt encPause (shcrStToVal · sIdx pk)) <$>
          stepUntilPauseFuel false (stepMid1Key S sIdx) A.run Ks h0 :=
  stepUntilPauseFuel_map_boundedC false encPause (shcrStToVal · sIdx pk)
    (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) (fun hnm hI => ShInv.mono hnm hI)
    (stepMid1Key S sIdx) (stepPreD1Key S Q K) Ks
    (fun _ q st hn hI => stepPreD1Key_eq S Q K _ sIdx pk sk q st hI (by omega))
    (fun n q st hI => stepMid1Key_inv S sIdx pk sk n q st hI) A.run Ks hA Ks 0 h0 hI0 (by omega)

theorem midRun1Key_inv (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S) (pk sk : Bytes)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total) :
    HoldsOnLeaves
      (fun x => Stage1InvC (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) b.q_total x.2)
      (midRun1Key S b A pk sk) := by
  unfold midRun1Key
  split_ifs
  · refine HoldsOnLeaves.bind_const _ fun secb => ?_
    exact HoldsOnLeaves.bind (stepRun1Key_bounded S b.q_total (b.q_total + 1) b.q_total 0 pk sk A
      (initSh S secb 0 pk sk) (initSh_inv _ _ _ _ _) hA le_rfl).1 fun _ hr => HoldsOnLeaves.pure hr
  · refine HoldsOnLeaves.bind_const _ fun uIdx => HoldsOnLeaves.bind_const _ fun jIdx =>
      HoldsOnLeaves.bind_const _ fun sIdx => HoldsOnLeaves.bind_const _ fun secb => ?_
    exact HoldsOnLeaves.bind (stepRun1Key_bounded S b.q_total (b.q_total + 1) b.q_total sIdx pk sk A
      (initSh S secb (uIdx * S.N_recv + jIdx) pk sk)
      (initSh_inv _ _ _ _ _) hA le_rfl).1 fun _ hr => HoldsOnLeaves.pure hr

theorem shcr1KeyInit_eval (S : Setup) (Q K : ℕ) (pk sk : Bytes) :
    (shcrKeyInd1KeyProg S Q K).init.eval (.cons (pk, sk) .nil) =
      if S.N_spk_tot * S.N_send_tot = 0 then (do
        let secb ← embedUnif ($ᵗ Bool)
        pure ((), shcrStToVal (initSh S secb 0 pk sk) 0 pk))
      else (do
        let uIdx ← embedUnif (RoKem.sampleIndexRange S.N_id)
        let jIdx ← embedUnif (RoKem.sampleIndexRange S.N_recv)
        let sIdx ← embedUnif (RoKem.sampleIndexRange S.N_send_tot)
        let secb ← embedUnif ($ᵗ Bool)
        pure ((), shcrStToVal (initSh S secb (uIdx * S.N_recv + jIdx) pk sk) sIdx pk)) :=
  shcrInit_eval S Q K pk sk

theorem eval1_1Key_eq (S : Setup) (Q K : ℕ) (b : QueryBudget) (A : KeyIndAdversary S)
    (pk sk : Bytes)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total)
    (hK : b.q_total + 1 ≤ K) :
    (shcrKeyInd1KeyProg S Q K).eval1 (fun _ => A.run) (pk, sk) b.q_total false =
    (fun x => (chosenOf pk x.2.2, encMid pk x)) <$> midRun1Key S b A pk sk := by
  have hBody : ∀ bIdx sIdx secb,
      (stepUntilPauseFuel false (stepPreD1Key S Q K) A.run b.q_total
        (shcrStToVal (initSh S secb bIdx pk sk) sIdx pk) >>= fun r =>
        match r with
        | (_, .done aOut stFinal) => do
          let v ← (shcrKeyInd1KeyProg S Q K).chDone.eval (.cons stFinal (.cons aOut .nil))
          pure (v, .done aOut stFinal)
        | (c?, .paused gq p stPaused c) =>
          let ch1 := c?.getD pk
          pure (ch1, .paused gq ch1 p stPaused c)) =
      (stepUntilPauseFuel false (stepMid1Key S sIdx) A.run b.q_total
        (initSh S secb bIdx pk sk) >>= fun r =>
        pure (chosenOf pk r.2, encMid pk (sIdx, r))) := by
    intro bIdx sIdx secb
    obtain ⟨hInv, hEq⟩ := stepRun1Key_bounded S Q K b.q_total sIdx pk sk A
      (initSh S secb bIdx pk sk) (initSh_inv _ _ _ _ _) hA hK
    erw [hEq, bind_map_left]
    refine hInv.bind_congr _ _ fun r hr => ?_
    obtain ⟨c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩ := r
    · obtain ⟨rfl, hI⟩ := hr
      simp [shcrKeyInd1KeyProg, Comp.eval, Expr.eval, shcrStToVal, chosenOf, encMid,
        RedProg2State.mapSt, hI.tpk]
    · obtain ⟨rfl, -⟩ := hr
      rfl
  rw [eval1_1Key_unfold, shcr1KeyInit_eval]
  unfold midRun1Key
  split_ifs <;> simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  · refine bind_congr fun secb => hBody 0 0 secb
  · refine bind_congr fun uIdx => bind_congr fun jIdx => bind_congr fun sIdx =>
      bind_congr fun secb => hBody (uIdx * S.N_recv + jIdx) sIdx secb

/-! ## DSL adversary, semantic bounds, and advantage equality -/

def shcrKeyInd1KeyDslAdvK (S : Setup) (b : QueryBudget) (K : ℕ) (A : KeyIndAdversary S) :
    KemShCrAdv where
  State := Mid (keyIndSpec S) Bool pauseTy.denote shcrStTy.denote Bytes
  choosePk := fun pk sk =>
    (shcrKeyInd1KeyProg S b.q_total K).eval1 (fun _ => A.run) (pk, sk) b.q_total false
  findCollision := fun st ss ct =>
    (shcrKeyInd1KeyProg S b.q_total K).eval2 st (ss, ct) b.q_total false
  q_prim := primQueryBudget S b

/-- `KemShCr` adversary obtained by running `shcrKeyInd1KeyDslProg S b`. -/
def shcrKeyInd1KeyDslAdv (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCrAdv :=
  shcrKeyInd1KeyDslAdvK S b (keyIndLoopBound b) A.1

def stepPostD1Key (S : Setup) (Q K : ℕ) (q : KeyIndQuery S) (st : shcrStTy.denote) :
    OracleComp PrimBaseSpec (KeyIndResponse × shcrStTy.denote) :=
  (shcrKeyInd1KeyProg S Q K).handlePost.eval (.cons st (.cons (keyIndQueryToVal q) .nil)) >>=
    fun (x : SCS.denote) => pure (valToKeyIndResp x.1, x.2)

theorem stepPostD1Key_eq (S : Setup) (Q K Ks sIdx : ℕ) (pk sk chosen : Bytes) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (hI : ShInv pk sk Ks h) (hK : Ks + 1 ≤ K) :
    stepPostD1Key S Q K q (shcrStToVal h sIdx chosen) =
      Prod.map id (shcrStToVal · sIdx chosen) <$> (pqxdhKeyIndShCrPrimImpl1Key true S q).run h := by
  unfold stepPostD1Key
  have hpost : (shcrKeyInd1KeyProg S Q K).handlePost.eval
      (.cons (shcrStToVal h sIdx chosen) (.cons (keyIndQueryToVal q) .nil)) =
      encSCS sIdx chosen <$> (pqxdhKeyIndShCrPrimImpl1Key true S q).run h :=
    shcr1KeyPostC_eval S K Ks (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero _ q h sIdx chosen rfl rfl hI.bnd hK
  rw [hpost, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  erw [bind_assoc]
  refine bind_congr fun x => ?_
  have hr : valToKeyIndResp (keyIndRespToVal x.1) = x.1 := keyIndRdec_keyIndRenc x.1
  simp only [Function.comp_apply, encSCS, Prod.map, id]
  erw [pure_bind]
  simp only [hr]

theorem eval2_1Key_done (S : Setup) (Q K fuel : ℕ) (a : Bool) (st : shcrStTy.denote)
    (ss ct : Bytes) :
    (shcrKeyInd1KeyProg S Q K).eval2 (.done a st) (ss, ct) fuel false =
    (shcrKeyIndProg S Q K).finish.eval (.cons st (.cons a (.cons (ss, ct) .nil))) := by
  simp only [TwoStageCostedReduction.eval2, pure_bind]; rfl

theorem eval2_1Key_paused (S : Setup) (Q K fuel : ℕ) (q : KeyIndQuery S) (ch : Bytes)
    (p : pauseTy.denote) (st : shcrStTy.denote)
    (k : KeyIndResponse → OracleComp (unifSpec + keyIndSpec S) Bool)
    (ss ct : Bytes) :
    (shcrKeyInd1KeyProg S Q K).eval2 (.paused q ch p st k) (ss, ct) fuel false =
    ((shcrKeyIndProg S Q K).resume.eval (.cons st (.cons p (.cons (ss, ct) .nil))) >>=
      fun (x : SCS.denote) => runWithFuelPrim false (stepPostD1Key S Q K)
        (k (valToKeyIndResp x.1)) fuel x.2 >>= fun (y : Bool × shcrStTy.denote) =>
      (shcrKeyIndProg S Q K).finish.eval (.cons y.2 (.cons y.1 (.cons (ss, ct) .nil)))) := by
  simp only [TwoStageCostedReduction.eval2]
  refine bind_congr fun x => ?_
  rw [runFuel_pqPrimIface_eq_runWithFuelPrim]
  rfl

theorem kemShCrExp_dsl1Key_mid (P : Primitives) (S : Setup) (b : QueryBudget) (K : ℕ)
    (A : KeyIndAdversary S)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total)
    (hK : b.q_total + 1 ≤ K) :
    kemShCrExp P (shcrKeyInd1KeyDslAdvK S b K A) = kemShCrExp P (midAdv1Key S b A) := by
  refine kemShCrExp_congr P (midAdv1Key S b A) (shcrKeyInd1KeyDslAdvK S b K A)
    (fun st => Stage1InvC (ShInv st.1 st.2.1) (fun d : PauseMid S => d.2.1.pqspkB)
      b.q_total st.2.2.2)
    (fun st => encMid st.1 st.2.2) ?_ ?_ ?_
  · intro pk sk
    simp only [shcrKeyInd1KeyDslAdvK, midAdv1Key]
    rw [eval1_1Key_eq S b.q_total K b A pk sk hA hK, Functor.map_map]
  · intro pk sk
    simp only [midAdv1Key]
    exact HoldsOnLeaves.map _ (midRun1Key_inv S b A pk sk hA) fun _ hx => hx
  · rintro ⟨pk, sk, sIdx, c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩ ⟨_, hI⟩ ss ct
    · have hI' : ShInv pk sk b.q_total h := hI
      show (shcrKeyInd1KeyProg S b.q_total K).eval2
          (.done a (shcrStToVal h sIdx pk)) (ss, ct) b.q_total false =
        findCollisionKeyInd1KeyPrim S b (pk, sk, pk, .inl (a, h)) ss ct
      erw [eval2_1Key_done, shcrFinish_eval]
      simp only [findCollisionKeyInd1KeyPrim, pure_bind, hI'.tpk, hI'.tsk]
    · obtain ⟨n, r, hIn, hnr, hk⟩ := hI
      show (shcrKeyInd1KeyProg S b.q_total K).eval2
          (.paused q d.2.1.pqspkB (encPause d) (shcrStToVal h sIdx pk) k) (ss, ct) b.q_total
          false =
        findCollisionKeyInd1KeyPrim S b (pk, sk, d.2.1.pqspkB, .inr (toPaused h k d)) ss ct
      erw [eval2_1Key_paused, shcrResume_eval S _ K d h sIdx pk ss ct (hIn.bnd.mono (by omega))]
      erw [bind_map_left]
      simp only [findCollisionKeyInd1KeyPrim, resumePausedKeyInd1KeyPrim, toPaused, bind_assoc]
      refine (postKem_inv S pk sk n d h hIn ss ct).bind_congr _ _ fun p hp => ?_
      obtain ⟨resp, h'⟩ := p
      have hr : valToKeyIndResp (keyIndRespToVal resp) = resp := keyIndRdec_keyIndRenc resp
      dsimp only [encSCS]
      rw [hr]
      obtain ⟨hInvR, hEqR⟩ := runWithFuelPrim_map_bounded false (shcrStToVal · sIdx d.2.1.pqspkB)
        (fun n h => ShInv pk sk n h) (fun hnm hI => ShInv.mono hnm hI)
        (fun q s => (pqxdhKeyIndShCrPrimImpl1Key true S q).run s) (stepPostD1Key S b.q_total K)
        b.q_total (fun q st hI => stepPostD1Key_eq S b.q_total K b.q_total sIdx pk sk _ q st hI hK)
        (fun n q st hI => pqxdhKeyIndShCrPrimImpl1Key_inv S pk sk n q st hI) (k resp) r (hk resp)
        b.q_total (n + 1) h' hp (by omega)
      rw [hEqR, bind_map_left, runWithFuelShCr1Key_eq]
      refine hInvR.bind_congr _ _ fun y hy => ?_
      obtain ⟨a, hf⟩ := y
      dsimp only [Prod.map, id]
      erw [shcrFinish_eval]
      rw [hy.tpk, hy.tsk]

theorem kemShCrExp_shcrKeyInd1KeyDslAdvK_of_queryBound (P : Primitives) (S : Setup) (b : QueryBudget)
    (K : ℕ) (A : KeyIndAdversary S)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total)
    (hK : b.q_total + 1 ≤ K) :
    KemShCr P (shcrKeyInd1KeyDslAdvK S b K A) =
      KemShCr P (shcrReductionKeyInd1KeyCore S b A) := by
  have hDslMid : KemShCr P (shcrKeyInd1KeyDslAdvK S b K A) = KemShCr P (midAdv1Key S b A) := by
    unfold KemShCr
    rw [kemShCrExp_dsl1Key_mid P S b K A hA hK]
  rw [hDslMid, ← kemShCrExp_mid1Key_core]

theorem kemShCrExp_shcrKeyInd1KeyDslAdvK (P : Primitives) (S : Setup) (b : QueryBudget) (K : ℕ)
    (A : BoundedAdv (KeyIndAdversary S) b) (hK : b.q_total + 1 ≤ K) :
    KemShCr P (shcrKeyInd1KeyDslAdvK S b K A.1) =
      KemShCr P (shcrReductionKeyInd1Key S b A) := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total := by
    have h := A.2.2.2.2.1
    convert h using 1; funext q; cases q <;> rfl
  exact kemShCrExp_shcrKeyInd1KeyDslAdvK_of_queryBound P S b K A.1 hA hK

theorem kemShCrExp_shcrKeyInd1KeyDslAdv (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCr P (shcrKeyInd1KeyDslAdv S b A) = KemShCr P (shcrReductionKeyInd1Key S b A) :=
  kemShCrExp_shcrKeyInd1KeyDslAdvK P S b (keyIndLoopBound b) A (by
    change b.q_total + 1 ≤ 2 * b.q_total + 1; omega)

/-- Exact `KemShCr` advantage equality between `shcrKeyInd1KeyDslAdv` and `shcrReductionKeyInd1Key`. -/
theorem KemShCr_shcrKeyInd1KeyDslAdv (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCr P (shcrKeyInd1KeyDslAdv S b A) = KemShCr P (shcrReductionKeyInd1Key S b A) :=
  kemShCrExp_shcrKeyInd1KeyDslAdv P S b A

theorem KemShCrReal_shcrKeyInd1KeyDslAdv (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCrReal P (shcrKeyInd1KeyDslAdv S b A) = KemShCrReal P (shcrReductionKeyInd1Key S b A) :=
  congrArg ENNReal.toReal (KemShCr_shcrKeyInd1KeyDslAdv P S b A)

theorem shcrKeyInd1KeyProg_eval1_primBounded (S : Setup) (Q K fuel : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool) (pk sk : Bytes) :
    ((shcrKeyInd1KeyProg S Q K).eval1 A (pk, sk) fuel false).IsQueryBoundP
      (fun q => SignalPqxdh.isPrimQuery₀ q = true)
      ((shcrKeyInd1KeyProg S Q K).totalQueries primW primWS fuel) :=
  TwoStageCostedReduction.eval1_queryBound (shcrKeyInd1KeyProg S Q K)
    (fun q => SignalPqxdh.isPrimQuery₀ q = true) primW primWS
    (fun _ _ _ => le_rfl)
    (fun n => (isQueryBoundP_query_iff (spec := PrimBaseSpec)
      (fun q => SignalPqxdh.isPrimQuery₀ q = true) (Sum.inl n) 0).2 (fun h => by cases h))
    A (pk, sk) fuel false

theorem shcrKeyInd1KeyProg_eval2_primBounded (S : Setup) (Q K fuel : Nat)
    (m : Mid (keyIndSpec S) Bool pauseTy.denote shcrStTy.denote Bytes) (ss ct : Bytes) :
    ((shcrKeyInd1KeyProg S Q K).eval2 m (ss, ct) fuel false).IsQueryBoundP
      (fun q => SignalPqxdh.isPrimQuery₀ q = true)
      ((shcrKeyInd1KeyProg S Q K).totalQueries primW primWS fuel) :=
  TwoStageCostedReduction.eval2_queryBound (shcrKeyInd1KeyProg S Q K)
    (fun q => SignalPqxdh.isPrimQuery₀ q = true) primW primWS
    (fun _ _ _ => le_rfl)
    (fun n => (isQueryBoundP_query_iff (spec := PrimBaseSpec)
      (fun q => SignalPqxdh.isPrimQuery₀ q = true) (Sum.inl n) 0).2 (fun h => by cases h))
    m (ss, ct) fuel false

/-- Semantic primitive-query bound for `shcrKeyInd1KeyDslAdv`. -/
theorem shcrKeyInd1KeyDslAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (shcrKeyInd1KeyDslAdv S b A).Bounded := by
  have hQ : (shcrKeyInd1KeyDslProg S b).totalQueries primW primWS b.q_total ≤
      primQueryBudget S b :=
    shcrKeyInd1KeyDslProg_totalPrimQueries_le S b
  refine ⟨fun pk sk => ?_, fun st ss ct => ?_⟩
  · exact (shcrKeyInd1KeyProg_eval1_primBounded S b.q_total (keyIndLoopBound b) b.q_total
      (fun _ => A.1.run) pk sk).mono hQ
  · exact (shcrKeyInd1KeyProg_eval2_primBounded S b.q_total (keyIndLoopBound b) b.q_total
      st ss ct).mono hQ

end SignalPqxdh.Security.ReductionDsl.KeyInd
