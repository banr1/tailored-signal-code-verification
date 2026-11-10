/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Fig8WeightedParts -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SizeBudgetBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import

/-!
# Weighted AST Size Bounds for Atomic Figure 8 Reductions

Proves compositional `exprSizeW` and `compSizeW` bounds for the Figure 8 engines, hooks, and atomic
reductions against `reductionSizeBudget`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SessionCostedFig8.ProgSizeBounds

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface Expr Comp CostedReduction bits reductionSizeBudget)
open CryptoGames (Party)
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open Computational.Proofs.SessionCostedFig8.Bundles (exprSizeW compSizeW smOpS smSampS smQueryS
  ckaOpS ckaSampS ckaQueryS)

section SizeSimps

variable {S' : Sig} {O' : Ops S'} {ι : Type} {TSpec : OracleSpec ι} {I' : Iface S' TSpec}
  (opS : O'.Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)

@[simp] theorem exprSizeW_var {Γ t} (v : _root_.ReductionDsl.Var Γ t) : exprSizeW opS (Expr.var (O := O') v) = 1 := rfl
@[simp] theorem exprSizeW_v0 {Γ t} : exprSizeW opS (Expr.v0 (O := O') (Γ := Γ) (t := t)) = 1 := rfl
@[simp] theorem exprSizeW_v1 {Γ t a} : exprSizeW opS (Expr.v1 (O := O') (Γ := Γ) (t := t) (a := a)) = 1 := rfl
@[simp] theorem exprSizeW_v2 {Γ t a b} : exprSizeW opS (Expr.v2 (O := O') (Γ := Γ) (t := t) (a := a) (b := b)) = 1 := rfl
@[simp] theorem exprSizeW_v3 {Γ t a b c} : exprSizeW opS (Expr.v3 (O := O') (Γ := Γ) (t := t) (a := a) (b := b) (c := c)) = 1 := rfl
@[simp] theorem exprSizeW_v4 {Γ t a b c d} : exprSizeW opS (Expr.v4 (O := O') (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d)) = 1 := rfl
@[simp] theorem exprSizeW_v5 {Γ t a b c d e} : exprSizeW opS (Expr.v5 (O := O') (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e)) = 1 := rfl
@[simp] theorem exprSizeW_v6 {Γ t a b c d e f} : exprSizeW opS (Expr.v6 (O := O') (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e) (f := f)) = 1 := rfl
@[simp] theorem exprSizeW_v7 {Γ t a b c d e f g} : exprSizeW opS (Expr.v7 (O := O') (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e) (f := f) (g := g)) = 1 := rfl
@[simp] theorem exprSizeW_unit {Γ} : exprSizeW opS (Expr.unit (O := O') (Γ := Γ)) = 1 := rfl
@[simp] theorem exprSizeW_bool {Γ} (b : Bool) : exprSizeW opS (Expr.bool (O := O') (Γ := Γ) b) = 1 := rfl
@[simp] theorem exprSizeW_nat {Γ} (n : ℕ) : exprSizeW opS (Expr.nat (O := O') (Γ := Γ) n) = bits n := rfl
@[simp] theorem exprSizeW_none {Γ t} : exprSizeW opS (Expr.none (O := O') (Γ := Γ) (t := t)) = 1 := rfl
@[simp] theorem exprSizeW_nil {Γ t} : exprSizeW opS (Expr.nil (O := O') (Γ := Γ) (t := t)) = 1 := rfl
@[simp] theorem exprSizeW_add {Γ} (a b : Expr O' Γ .nat) : exprSizeW opS (.add a b) = exprSizeW opS a + exprSizeW opS b + 1 := rfl
@[simp] theorem exprSizeW_sub {Γ} (a b : Expr O' Γ .nat) : exprSizeW opS (.sub a b) = exprSizeW opS a + exprSizeW opS b + 1 := rfl
@[simp] theorem exprSizeW_mulK {Γ} (k : ℕ) (a : Expr O' Γ .nat) : exprSizeW opS (.mulK k a) = exprSizeW opS a + bits k + 1 := rfl
@[simp] theorem exprSizeW_divK {Γ} (k : ℕ) (a : Expr O' Γ .nat) : exprSizeW opS (.divK k a) = exprSizeW opS a + bits k + 1 := rfl
@[simp] theorem exprSizeW_modK {Γ} (k : ℕ) (a : Expr O' Γ .nat) : exprSizeW opS (.modK k a) = exprSizeW opS a + bits k + 1 := rfl
@[simp] theorem exprSizeW_lt {Γ} (a b : Expr O' Γ .nat) : exprSizeW opS (.lt a b) = exprSizeW opS a + exprSizeW opS b + 1 := rfl
@[simp] theorem exprSizeW_eqN {Γ} (a b : Expr O' Γ .nat) : exprSizeW opS (.eqN a b) = exprSizeW opS a + exprSizeW opS b + 1 := rfl
@[simp] theorem exprSizeW_not {Γ} (a : Expr O' Γ .bool) : exprSizeW opS (.not a) = exprSizeW opS a + 1 := rfl
@[simp] theorem exprSizeW_and {Γ} (a b : Expr O' Γ .bool) : exprSizeW opS (.and a b) = exprSizeW opS a + exprSizeW opS b + 1 := rfl
@[simp] theorem exprSizeW_ite {Γ t} (c : Expr O' Γ .bool) (a b : Expr O' Γ t) : exprSizeW opS (.ite c a b) = exprSizeW opS c + exprSizeW opS a + exprSizeW opS b + 1 := rfl
@[simp] theorem exprSizeW_pair {Γ a b} (x : Expr O' Γ a) (y : Expr O' Γ b) : exprSizeW opS (.pair x y) = exprSizeW opS x + exprSizeW opS y + 1 := rfl
@[simp] theorem exprSizeW_fst {Γ a b} (x : Expr O' Γ (.prod a b)) : exprSizeW opS (.fst x) = exprSizeW opS x + 1 := rfl
@[simp] theorem exprSizeW_snd {Γ a b} (x : Expr O' Γ (.prod a b)) : exprSizeW opS (.snd x) = exprSizeW opS x + 1 := rfl
@[simp] theorem exprSizeW_inl {Γ a b} (x : Expr O' Γ a) : exprSizeW opS (.inl (u := b) x) = exprSizeW opS x + 1 := rfl
@[simp] theorem exprSizeW_inr {Γ a b} (x : Expr O' Γ b) : exprSizeW opS (.inr (t := a) x) = exprSizeW opS x + 1 := rfl
@[simp] theorem exprSizeW_some {Γ a} (x : Expr O' Γ a) : exprSizeW opS (.some x) = exprSizeW opS x + 1 := rfl
@[simp] theorem exprSizeW_caseOpt {Γ a b} (x : Expr O' Γ (.opt a)) (n : Expr O' Γ b) (s : Expr O' (a :: Γ) b) : exprSizeW opS (.caseOpt x n s) = exprSizeW opS x + exprSizeW opS n + exprSizeW opS s + 1 := rfl
@[simp] theorem exprSizeW_caseSum {Γ a b c} (x : Expr O' Γ (.sum a b)) (l : Expr O' (a :: Γ) c) (r : Expr O' (b :: Γ) c) : exprSizeW opS (.caseSum x l r) = exprSizeW opS x + exprSizeW opS l + exprSizeW opS r + 1 := rfl
@[simp] theorem exprSizeW_letE {Γ a b} (x : Expr O' Γ a) (y : Expr O' (a :: Γ) b) : exprSizeW opS (.letE x y) = exprSizeW opS x + exprSizeW opS y + 1 := rfl
@[simp] theorem exprSizeW_op {Γ} (o : O'.Op) (x : Expr O' Γ (O'.dom o)) : exprSizeW opS (.op o x) = exprSizeW opS x + opS o := rfl
@[simp] theorem exprSizeW_cons {Γ a} (x : Expr O' Γ a) (xs : Expr O' Γ (.list a)) : exprSizeW opS (.cons x xs) = exprSizeW opS x + exprSizeW opS xs + 1 := rfl
@[simp] theorem exprSizeW_len {Γ a} (xs : Expr O' Γ (.list a)) : exprSizeW opS (.len xs) = exprSizeW opS xs + 1 := rfl
@[simp] theorem exprSizeW_take {Γ a} (n : Expr O' Γ .nat) (xs : Expr O' Γ (.list a)) : exprSizeW opS (.take n xs) = exprSizeW opS n + exprSizeW opS xs + 1 := rfl
@[simp] theorem exprSizeW_appendL {Γ a} (K : ℕ) (xs ys : Expr O' Γ (.list a)) : exprSizeW opS (.appendL K xs ys) = exprSizeW opS xs + exprSizeW opS ys + bits K + 1 := rfl
@[simp] theorem exprSizeW_findB {Γ a} (K : ℕ) (xs : Expr O' Γ (.list a)) (p : Expr O' (a :: Γ) .bool) : exprSizeW opS (.findB K xs p) = exprSizeW opS xs + exprSizeW opS p + bits K + 1 := rfl
@[simp] theorem exprSizeW_anyB {Γ a} (K : ℕ) (xs : Expr O' Γ (.list a)) (p : Expr O' (a :: Γ) .bool) : exprSizeW opS (.anyB K xs p) = exprSizeW opS xs + exprSizeW opS p + bits K + 1 := rfl
@[simp] theorem exprSizeW_mapB {Γ a b} (K : ℕ) (xs : Expr O' Γ (.list a)) (f : Expr O' (a :: Γ) b) : exprSizeW opS (.mapB K xs f) = exprSizeW opS xs + exprSizeW opS f + bits K + 1 := rfl
@[simp] theorem exprSizeW_foldrB {Γ a b} (K : ℕ) (xs : Expr O' Γ (.list a)) (z : Expr O' Γ b) (f : Expr O' (a :: b :: Γ) b) : exprSizeW opS (.foldrB K xs z f) = exprSizeW opS xs + exprSizeW opS z + exprSizeW opS f + bits K + 1 := rfl
@[simp] theorem exprSizeW_tconst {Γ a} (x : Expr O' Γ a) : exprSizeW opS (.tconst x) = exprSizeW opS x + 1 := rfl
@[simp] theorem exprSizeW_tget {Γ a} (m : Expr O' Γ (.tbl a)) (i : Expr O' Γ .nat) : exprSizeW opS (.tget m i) = exprSizeW opS m + exprSizeW opS i + 1 := rfl
@[simp] theorem exprSizeW_tset {Γ a} (m : Expr O' Γ (.tbl a)) (i : Expr O' Γ .nat) (x : Expr O' Γ a) : exprSizeW opS (.tset m i x) = exprSizeW opS m + exprSizeW opS i + exprSizeW opS x + 1 := rfl

@[simp] theorem compSizeW_ret {Γ t} (e : Expr O' Γ t) : compSizeW opS sS qS (.ret e) = exprSizeW opS e + 1 := rfl
@[simp] theorem compSizeW_bind {Γ t u} (c : Comp O' I' Γ t) (k : Comp O' I' (t :: Γ) u) : compSizeW opS sS qS (.bind c k) = compSizeW opS sS qS c + compSizeW opS sS qS k + 1 := rfl
@[simp] theorem compSizeW_ite {Γ t} (b : Expr O' Γ .bool) (c d : Comp O' I' Γ t) : compSizeW opS sS qS (.ite b c d) = exprSizeW opS b + compSizeW opS sS qS c + compSizeW opS sS qS d + 1 := rfl
@[simp] theorem compSizeW_caseOpt {Γ a t} (b : Expr O' Γ (.opt a)) (c : Comp O' I' Γ t) (d : Comp O' I' (a :: Γ) t) : compSizeW opS sS qS (.caseOpt b c d) = exprSizeW opS b + compSizeW opS sS qS c + compSizeW opS sS qS d + 1 := rfl
@[simp] theorem compSizeW_caseSum {Γ a b t} (e : Expr O' Γ (.sum a b)) (c : Comp O' I' (a :: Γ) t) (d : Comp O' I' (b :: Γ) t) : compSizeW opS sS qS (.caseSum e c d) = exprSizeW opS e + compSizeW opS sS qS c + compSizeW opS sS qS d + 1 := rfl
@[simp] theorem compSizeW_sample {Γ} (s : I'.smp.Samp) (e : Expr O' Γ (I'.smp.sDom s)) : compSizeW opS sS qS (.sample s e) = exprSizeW opS e + sS s := rfl
@[simp] theorem compSizeW_query {Γ} (g : I'.Tag) (e : Expr O' Γ (I'.dom g)) : compSizeW opS sS qS (.query g e) = exprSizeW opS e + qS g := rfl
@[simp] theorem compSizeW_iter {Γ t} (n : ℕ) (e : Expr O' Γ t) (body : Comp O' I' (t :: Γ) t) : compSizeW opS sS qS (.iter n e body) = exprSizeW opS e + compSizeW opS sS qS body + bits n + 1 := rfl
@[simp] theorem compSizeW_findM {Γ a} (n : ℕ) (e : Expr O' Γ (.list a)) (body : Comp O' I' (a :: Γ) .bool) : compSizeW opS sS qS (.findM n e body) = exprSizeW opS e + compSizeW opS sS qS body + bits n + 1 := rfl
@[simp] theorem compSizeW_anyM {Γ a} (n : ℕ) (e : Expr O' Γ (.list a)) (body : Comp O' I' (a :: Γ) .bool) : compSizeW opS sS qS (.anyM n e body) = exprSizeW opS e + compSizeW opS sS qS body + bits n + 1 := rfl
@[simp] theorem compSizeW_mapM {Γ a b} (n : ℕ) (e : Expr O' Γ (.list a)) (body : Comp O' I' (a :: Γ) b) : compSizeW opS sS qS (.mapM n e body) = exprSizeW opS e + compSizeW opS sS qS body + bits n + 1 := rfl
@[simp] theorem compSizeW_consumeFirstM {Γ a} (K : ℕ) (l : Expr O' Γ (.list a)) (p : Comp O' I' (a :: Γ) .bool) (mk : Expr O' (a :: Γ) a) : compSizeW opS sS qS (.consumeFirstM K l p mk) = exprSizeW opS l + compSizeW opS sS qS p + exprSizeW opS mk + bits K + 1 := rfl
@[simp] theorem compSizeW_foldM {Γ a b} (K : ℕ) (l : Expr O' Γ (.list a)) (z : Expr O' Γ b) (f : Comp O' I' (a :: b :: Γ) b) : compSizeW opS sS qS (.foldM K l z f) = exprSizeW opS l + exprSizeW opS z + compSizeW opS sS qS f + bits K + 1 := rfl

end SizeSimps

section BudgetBridge

open CryptoGames.LibsignalSession (maxForwardJumps)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge
  (bits_mono bits_pos bits_succ_le size_le_budget_of_log_cost)

theorem bits_le_succ_nat : ∀ k, bits k ≤ k + 1
  | 0 => by decide
  | k + 1 => by have := bits_succ_le k; have := bits_le_succ_nat k; omega

theorem bits_le_ratchetCostBudget_of_le_linear {x q qep : ℕ}
    (hx : x ≤ 4096 * q + 102400000) :
    bits x ≤ bits (ratchetCostBudget q qep) := by
  apply bits_mono
  unfold ratchetCostBudget maxForwardJumps
  have hbq : 1 ≤ bits qep := bits_pos qep
  have hsq : q + 1 ≤ (q + 1) ^ 2 := by nlinarith
  have hprod : 25001 * (q + 1) ≤ (q + 1) ^ 2 * (25000 + bits qep) := by nlinarith
  nlinarith

theorem bits_qep_le_ratchetCostBudget {q qep : ℕ}
    (hqep : qep ≤ 4096 * q + 100000000) :
    bits qep ≤ bits (ratchetCostBudget q qep) :=
  bits_le_ratchetCostBudget_of_le_linear (by omega)

theorem bits_B0_le_ratchetCostBudget (q qep : ℕ) :
    bits ((q + 1) * (maxForwardJumps + 1)) ≤ bits (ratchetCostBudget q qep) := by
  apply bits_mono
  unfold ratchetCostBudget maxForwardJumps
  have hbq : 1 ≤ bits qep := bits_pos qep
  have hsq : q + 1 ≤ (q + 1) ^ 2 := by nlinarith
  have hprod : (q + 1) * 25001 ≤ (q + 1) ^ 2 * (25000 + bits qep) := by nlinarith
  nlinarith

theorem size_le_ratchetSizeBudget {sz C₀ C₁ q qep : ℕ}
    (h₀ : C₀ ≤ 2 ^ 22) (h₁ : C₁ ≤ 2 ^ 11)
    (h : sz ≤ C₀ + C₁ * bits (ratchetCostBudget q qep)) :
    sz ≤ reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) :=
  size_le_budget_of_log_cost h₀ h₁ h

end BudgetBridge

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

theorem bits_zero : bits 0 = 1 := rfl
theorem bits_one : bits 1 = 1 := rfl
theorem bits_two : bits 2 = 2 := rfl
theorem bits_three : bits 3 = 2 := rfl
theorem bits_four : bits 4 = 3 := rfl

section Thm1SizeHelpers

open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_succ_le)

variable {Key St St₂ Msg Coins RCoins C : Type}
  {init : Party → Key → Option St} {send : St → Msg → Coins → Option (St × C)}
  {receive : St → C → RCoins → Option (St × ℕ × ℕ × Msg)}
  {eqMsg : Msg → Msg → Bool} {eqCt : C → C → Bool} {blank : Msg → Msg}
  {injOK : C → Bool} {stOK : Party → St → Bool} {φ : St → Option St₂}
  {stSort : CryptoGames.SM.SMSort}
  {sampKey : ProbComp (Option Key)} {sampCoins : ProbComp (Option Coins)}
  {sampRCoins : ProbComp (Option RCoins)}

theorem thm1_simInitC_sizeW_le :
    compSizeW smOpS smSampS smQueryS
      (CryptoGames.SM.simInitC (init := init) (send := send) (receive := receive)
        (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
        (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
        (sampRCoins := sampRCoins)) ≤ 1000 := by
  simp only [CryptoGames.SM.simInitC, CryptoGames.SM.mMk, smOpS, smSampS, smQueryS,
    exprSizeW_v0, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_pair, exprSizeW_tconst,
    compSizeW_ret, compSizeW_bind, compSizeW_sample, bits_zero, Nat.reduceAdd]
  omega

theorem thm1_simHandleC_sizeW_le (K qep : ℕ) (realEpoch : Option ℕ) :
    compSizeW smOpS smSampS smQueryS
      (CryptoGames.SM.simHandleC (init := init) (send := send) (receive := receive)
        (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
        (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K 3 qep realEpoch) ≤
      50 * bits K + 30 * bits qep + 10 * bits (realEpoch.getD 0) + 20000 := by
  have hqep1 := bits_succ_le qep
  have hre1 := bits_succ_le (realEpoch.getD 0)
  cases realEpoch <;>
  · simp only [CryptoGames.SM.simHandleC, CryptoGames.SM.simTransmitC, CryptoGames.SM.simChallC,
      CryptoGames.SM.simSendC, CryptoGames.SM.simDeliverC, CryptoGames.SM.simInjectC,
      CryptoGames.SM.simCorrC, CryptoGames.SM.mEpMgmtE, CryptoGames.SM.mSafeChE,
      CryptoGames.SM.mLeakE, CryptoGames.SM.mRecordE, CryptoGames.SM.mInTransitE,
      CryptoGames.SM.mDeleteE, CryptoGames.SM.mAcceptE, CryptoGames.SM.mChallContainsE,
      CryptoGames.SM.mAfterCorrE, CryptoGames.SM.mMk, CryptoGames.SM.mSt, CryptoGames.SM.mB,
      CryptoGames.SM.mWin, CryptoGames.SM.mEpoch, CryptoGames.SM.mIdx, CryptoGames.SM.mTL,
      CryptoGames.SM.mTrans, CryptoGames.SM.mChall, CryptoGames.SM.mComp, CryptoGames.SM.mMaxAcc,
      CryptoGames.SM.mLeaks, CryptoGames.SM.mCorrs, CryptoGames.SM.recPos, CryptoGames.SM.recCt,
      CryptoGames.SM.isSomeE, CryptoGames.SM.otherE, CryptoGames.SM.pGet, CryptoGames.SM.pSet,
      CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
      CryptoGames.SM.maxOptE, CryptoGames.SM.maxAccSet, CryptoGames.SM.maxAccGet,
      CryptoGames.SM.posEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch,
      CryptoGames.SM.posIdx, CryptoGames.SM.boolEq, Option.getD_none, Option.getD_some,
      smOpS, smSampS, smQueryS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
      exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_mulK, exprSizeW_divK,
      exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some,
      exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_cons,
      exprSizeW_len, exprSizeW_take, exprSizeW_appendL, exprSizeW_findB, exprSizeW_anyB,
      exprSizeW_mapB, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset,
      compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
      compSizeW_sample, compSizeW_query,
      bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
    omega

end Thm1SizeHelpers

section EngineSizeHelpers

open CryptoGames.SM.Construction (Header)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_succ_le)

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS} {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}

local notation "S_cka" => CryptoGames.CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  CryptoGames.CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

theorem optNatLit_sizeW {S' : Sig} {O' : Ops S'} (opS : O'.Op → ℕ) {Γ'} (o : Option ℕ) :
    exprSizeW opS (CryptoGames.SM.Engine.optNatLit (O' := O') (Γ' := Γ') o) =
      if o.isSome then bits (o.getD 0) + 1 else 1 := by cases o <;> rfl

theorem modeCfgEC_challOKE_sizeW {O' : Ops S_cka} (opS : O'.Op → ℕ)
    (mo : CryptoGames.SM.Construction.Mode) {Γ'} (e : Expr O' Γ' .nat) :
    exprSizeW opS ((CryptoGames.SM.Engine.modeCfgEC O' mo).challOKE e) =
      if mo.auth then 1 else exprSizeW opS e + bits mo.tStar + 1 := by
  cases h : mo.auth <;> simp [CryptoGames.SM.Engine.modeCfgEC, h]

theorem modeCfgEC_injectFullE_sizeW {O' : Ops S_cka} (opS : O'.Op → ℕ)
    (mo : CryptoGames.SM.Construction.Mode) {Γ'} (e : Expr O' Γ' .nat) :
    exprSizeW opS ((CryptoGames.SM.Engine.modeCfgEC O' mo).injectFullE e) =
      if mo.auth then exprSizeW opS e + bits mo.tStar + 1 else 1 := by
  cases h : mo.auth <;> simp [CryptoGames.SM.Engine.modeCfgEC, h]

theorem modeCfgEC_challMsgE_sizeW {O' : Ops S_cka} (opS : O'.Op → ℕ)
    (mo : CryptoGames.SM.Construction.Mode) {Γ'} (ep : Expr O' Γ' .nat) (b : Expr O' Γ' .bool)
    (m0 m1 : Expr O' Γ' (.base .msg)) :
    exprSizeW opS ((CryptoGames.SM.Engine.modeCfgEC O' mo).challMsgE ep b m0 m1) =
      exprSizeW opS b + exprSizeW opS m1 + exprSizeW opS m0 + 1 := rfl

theorem corrDoomE_sizeW_le {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka}
    (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (g : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    exprSizeW opS (CryptoGames.SM.Engine.corrDoomE π g p) ≤
      exprSizeW opS g + exprSizeW opS p + bits (π.tL.getD 0) + 2 * bits π.tStar + 80 := by
  cases h : π.auth <;>
  · simp only [CryptoGames.SM.Engine.corrDoomE, h, Bool.false_eq_true, ↓reduceIte,
      CryptoGames.SM.boolEq, CryptoGames.SM.ltOptE,
      CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.pGet, CryptoGames.SM.Engine.cGsEpoch,
      optNatLit_sizeW, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_bool,
      exprSizeW_nat, exprSizeW_lt, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE, Nat.reduceAdd]
    (try split_ifs) <;> omega

structure HooksSizeBounded {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} (B0 : ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr : ℕ) : Prop where
  startSend_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ' (CryptoGames.SM.Engine.cGsTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool) (t : Expr OO_cka Γ' .nat) (γv : Expr OO_cka Γ' γvT)
      (σ : Expr OO_cka Γ' svT) (r : Expr OO_cka Γ' (.opt (.base .ccoins))),
      compSizeW (ckaOpS B0) sS qS (hk.startSend h ctx p t γv σ r) ≤
        4 * (exprSizeW (ckaOpS B0) h + exprSizeW (ckaOpS B0) ctx + exprSizeW (ckaOpS B0) p +
          exprSizeW (ckaOpS B0) t + exprSizeW (ckaOpS B0) γv + exprSizeW (ckaOpS B0) σ +
          exprSizeW (ckaOpS B0) r) + Ho
  startRecv_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ' (CryptoGames.SM.Engine.cGsTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool) (t : Expr OO_cka Γ' .nat) (γv : Expr OO_cka Γ' γvT)
      (σ : Expr OO_cka Γ' svT) (tn : Expr OO_cka Γ' (.base .t)),
      compSizeW (ckaOpS B0) sS qS (hk.startRecv h ctx p t γv σ tn) ≤
        4 * (exprSizeW (ckaOpS B0) h + exprSizeW (ckaOpS B0) ctx + exprSizeW (ckaOpS B0) p +
          exprSizeW (ckaOpS B0) t + exprSizeW (ckaOpS B0) γv + exprSizeW (ckaOpS B0) σ +
          exprSizeW (ckaOpS B0) tn) + Ho
  fsSend_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ' (CryptoGames.SM.Engine.cGsTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool) (t : Expr OO_cka Γ' .nat) (ss : Expr OO_cka Γ' ssvT)
      (hdr : Expr OO_cka Γ' (CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
      (m : Expr OO_cka Γ' (.base .msg)) (pair : Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg)))),
      compSizeW (ckaOpS B0) sS qS (hk.fsSend h ctx p t ss hdr m pair) ≤
        4 * (exprSizeW (ckaOpS B0) h + exprSizeW (ckaOpS B0) ctx + exprSizeW (ckaOpS B0) p +
          exprSizeW (ckaOpS B0) t + exprSizeW (ckaOpS B0) ss + exprSizeW (ckaOpS B0) hdr +
          exprSizeW (ckaOpS B0) m + exprSizeW (ckaOpS B0) pair) + Hs
  fsRecv_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ' (CryptoGames.SM.Engine.cGsTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool) (t : Expr OO_cka Γ' .nat) (rs : Expr OO_cka Γ' rsvT)
      (hdr : Expr OO_cka Γ' (CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
      (e : Expr OO_cka Γ' (.base .ct)) (rec_ : Expr OO_cka Γ' (.opt CryptoGames.SM.Engine.cRecTy)),
      compSizeW (ckaOpS B0) sS qS (hk.fsRecv h ctx p t rs hdr e rec_) ≤
        4 * (exprSizeW (ckaOpS B0) h + exprSizeW (ckaOpS B0) ctx + exprSizeW (ckaOpS B0) p +
          exprSizeW (ckaOpS B0) t + exprSizeW (ckaOpS B0) rs + exprSizeW (ckaOpS B0) hdr +
          exprSizeW (ckaOpS B0) e + exprSizeW (ckaOpS B0) rec_) + Hr
  commit_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ' (CryptoGames.SM.Engine.cGsTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool)
      (old new : Expr OO_cka Γ' (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)),
      compSizeW (ckaOpS B0) sS qS (hk.commit h ctx p old new) ≤
        4 * (exprSizeW (ckaOpS B0) h + exprSizeW (ckaOpS B0) ctx + exprSizeW (ckaOpS B0) p +
          exprSizeW (ckaOpS B0) old + exprSizeW (ckaOpS B0) new) + Ho
  reveal_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ' (CryptoGames.SM.Engine.cGsTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool)
      (vp : Expr OO_cka Γ' (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)),
      compSizeW (ckaOpS B0) sS qS (hk.reveal h ctx p vp) ≤
        4 * (exprSizeW (ckaOpS B0) h + exprSizeW (ckaOpS B0) ctx + exprSizeW (ckaOpS B0) p +
          exprSizeW (ckaOpS B0) vp) + Ho

theorem HooksSizeBounded.mono {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    {hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT}
    {Ho Hs Hr Ho' Hs' Hr' : ℕ}
    (h : HooksSizeBounded B0 sS qS hk Ho Hs Hr) (hHo : Ho ≤ Ho') (hHs : Hs ≤ Hs') (hHr : Hr ≤ Hr') :
    HooksSizeBounded B0 sS qS hk Ho' Hs' Hr' where
  startSend_le hE ctx p t γv σ r := (h.startSend_le hE ctx p t γv σ r).trans (by omega)
  startRecv_le hE ctx p t γv σ tn := (h.startRecv_le hE ctx p t γv σ tn).trans (by omega)
  fsSend_le hE ctx p t ss hdr m pair := (h.fsSend_le hE ctx p t ss hdr m pair).trans (by omega)
  fsRecv_le hE ctx p t rs hdr e rec_ := (h.fsRecv_le hE ctx p t rs hdr e rec_).trans (by omega)
  commit_le hE ctx p old new := (h.commit_le hE ctx p old new).trans (by omega)
  reveal_le hE ctx p vp := (h.reveal_le hE ctx p vp).trans (by omega)

theorem cInTransitE_sizeW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (CryptoGames.SM.Engine.cGsTy vpT))
    (qParty : Expr OO_cka Γ' .bool)
    (c : Expr OO_cka Γ' (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprSizeW (ckaOpS B0) (CryptoGames.SM.Engine.cInTransitE L s qParty c) ≤
      exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) qParty +
        exprSizeW (ckaOpS B0) c + bits L + 1000 := by
  simp only [CryptoGames.SM.Engine.cInTransitE, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.Engine.cRecCt,
    CryptoGames.SM.Engine.hdrCtEqE, CryptoGames.SM.Engine.optTEqE,
    CryptoGames.SM.posSender, CryptoGames.SM.boolEq, ckaOpS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_var, exprSizeW_bool, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op,
    exprSizeW_findB, Nat.reduceAdd]
  omega

theorem pureEngineExprs_sizeW_le {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT hsT : Ty S_cka}
    (L : ℕ) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr O' Γ' (CryptoGames.SM.Engine.esTy vpT hsT)) :
    exprSizeW opS (CryptoGames.SM.Engine.authOutE L 3 π es) ≤
      exprSizeW opS es + 10 * bits L + 5 * bits (π.tL.getD 0) + 5 * bits π.tStar + 400 ∧
    exprSizeW opS (CryptoGames.SM.Engine.privValidE L 3 π es) ≤
      exprSizeW opS es + 10 * bits L + 5 * bits (π.tL.getD 0) + 5 * bits π.tStar + 400 := by
  constructor <;>
  · simp only [CryptoGames.SM.Engine.authOutE, CryptoGames.SM.Engine.privValidE,
      CryptoGames.SM.Engine.cAuthOKE, CryptoGames.SM.Engine.cCanonE,
      CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE,
      CryptoGames.SM.ltOptE, CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esG,
      CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
      optNatLit_sizeW,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
      exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_add, exprSizeW_sub, exprSizeW_modK,
      exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE,
      exprSizeW_anyB, exprSizeW_foldrB, bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
    split_ifs <;> omega

theorem privOutC_sizeW_le {O' : Ops S_cka} {ι : Type} {TSpec : OracleSpec ι}
    {I' : Iface S_cka TSpec} {vpT hsT : Ty S_cka}
    (opS : O'.Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (L : ℕ) (π : CryptoGames.SM.Engine.Policy)
    (drawBit : ∀ {Γ''}, Comp O' I' Γ'' .bool)
    {Γ'} (b b' : Expr O' Γ' .bool) (es : Expr O' Γ' (CryptoGames.SM.Engine.esTy vpT hsT)) :
    compSizeW opS sS qS (CryptoGames.SM.Engine.privOutC L 3 π drawBit b b' es) ≤
      exprSizeW opS es + exprSizeW opS b + 2 * exprSizeW opS b' +
        compSizeW opS sS qS (drawBit (Γ'' := Γ')) +
        10 * bits L + 5 * bits (π.tL.getD 0) + 5 * bits π.tStar + 420 := by
  have hpv := (pureEngineExprs_sizeW_le opS L π es).2
  simp only [CryptoGames.SM.Engine.privOutC, CryptoGames.SM.boolEq, compSizeW_ite, compSizeW_ret,
    exprSizeW_ite, exprSizeW_not, Nat.reduceAdd]
  omega

theorem vSendC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr : ℕ)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (h : Expr OO_cka Γ' hsT)
    (ctx : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.cGsTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO_cka Γ' .bool)
    (s : Expr OO_cka Γ' (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (m : Expr OO_cka Γ' (.base .msg))
    (pair : Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (r : Expr OO_cka Γ' (.opt (.base .ccoins))) :
    compSizeW (ckaOpS B0) sS qS (CryptoGames.SM.Engine.vSendC hk h ctx p s m pair r) ≤
      6 * (exprSizeW (ckaOpS B0) h + exprSizeW (ckaOpS B0) ctx + exprSizeW (ckaOpS B0) p +
        exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) m + exprSizeW (ckaOpS B0) pair +
        exprSizeW (ckaOpS B0) r) + Ho + Hs + 1000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ0 : List (Ty S_cka) :=
    .prod hsT (.prod (CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.opt (.base .ccoins))))) ::
      .prod hsT (.prod (CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.prod (.base .msg)
        (.prod (.opt (.prod (.base .msg) (.base .msg))) (.opt (.base .ccoins))))))) :: Γ'
  let Γ1 : List (Ty S_cka) :=
    ssvT :: vpT :: .prod (.opt vpT) hsT ::
      .prod hsT (.prod (CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.prod (.base .msg)
        (.prod (.opt (.prod (.base .msg) (.base .msg))) (.opt (.base .ccoins))))))) :: Γ'
  have hss := hhk.startSend_le (Γ' := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.add (CryptoGames.SM.Engine.vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
    (CryptoGames.SM.Engine.vpΓ (.fst (.snd (.snd (.snd .v0)))))
    (CryptoGames.SM.Engine.vpRoot (.fst (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd .v0))))
  have hfs := hhk.fsSend_le (Γ' := Γ1)
    (.snd .v2) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (CryptoGames.SM.Engine.vpTcurNat .v1) .v0
    (.pair (CryptoGames.SM.Engine.vpTcurNat .v1) (CryptoGames.SM.Engine.vpTcur .v1))
    (.fst (.snd (.snd (.snd (.snd .v3)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
  simp only [CryptoGames.SM.Engine.vpTcurNat, CryptoGames.SM.Engine.vpTcur,
    CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpRoot,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
    exprSizeW_nat, exprSizeW_add, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    bits_one, Nat.reduceAdd] at hss hfs
  simp only [CryptoGames.SM.Engine.vSendC, CryptoGames.SM.Engine.vSendStep1C,
    CryptoGames.SM.sendsInE, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId,
    CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR, CryptoGames.SM.Engine.vpTcur,
    CryptoGames.SM.Engine.vpTcurNat, CryptoGames.SM.Engine.vpSetVS, CryptoGames.SM.Engine.vpΓ,
    CryptoGames.SM.Engine.vpRoot, ckaOpS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_add,
    exprSizeW_eqN, exprSizeW_modK, exprSizeW_lt, exprSizeW_and, exprSizeW_not, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_some,
    exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op, exprSizeW_tget, exprSizeW_tset,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    bits_zero, bits_one, bits_two, Nat.reduceAdd]
  omega

theorem vRecvC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr : ℕ)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (h : Expr OO_cka Γ' hsT)
    (ctx : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.cGsTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO_cka Γ' .bool)
    (s : Expr OO_cka Γ' (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (c : Expr OO_cka Γ' (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))
    (rec_ : Expr OO_cka Γ' (.opt CryptoGames.SM.Engine.cRecTy)) :
    compSizeW (ckaOpS B0) sS qS (CryptoGames.SM.Engine.vRecvC hk h ctx p s c rec_) ≤
      6 * (exprSizeW (ckaOpS B0) h + exprSizeW (ckaOpS B0) ctx + exprSizeW (ckaOpS B0) p +
        exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) c + exprSizeW (ckaOpS B0) rec_) +
        Ho + Hr + 800 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (Ty S_cka) :=
    .base .t :: .prod hsT (.prod (CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT hdrCtT))) ::
      .prod hsT (.prod (CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT
        (.prod hdrCtT (.opt CryptoGames.SM.Engine.cRecTy))))) :: Γ'
  let Γ1 : List (Ty S_cka) :=
    rsvT :: vpT :: .opt vpT :: .prod (.opt (.opt vpT)) hsT ::
      .prod hsT (.prod (CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT
        (.prod hdrCtT (.opt CryptoGames.SM.Engine.cRecTy))))) :: Γ'
  have hsr := hhk.startRecv_le (Γ' := Γ0)
    (.fst .v1) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
    (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
    (CryptoGames.SM.Engine.vpΓ (.fst (.snd (.snd (.snd .v1)))))
    (CryptoGames.SM.Engine.vpRoot (.fst (.snd (.snd (.snd .v1))))) .v0
  have hfr := hhk.fsRecv_le (Γ' := Γ1)
    (.snd .v3) (.fst (.snd .v4)) (.fst (.snd (.snd .v4)))
    (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v4))))))) .v0
    (.fst (.fst (.snd (.snd (.snd (.snd .v4))))))
    (.snd (.fst (.snd (.snd (.snd (.snd .v4))))))
    (.snd (.snd (.snd (.snd (.snd .v4)))))
  simp only [CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpRoot,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
    exprSizeW_fst, exprSizeW_snd, Nat.reduceAdd] at hsr hfr
  simp only [CryptoGames.SM.Engine.vRecvC, CryptoGames.SM.Engine.vRecvStep1C,
    CryptoGames.SM.orE, CryptoGames.SM.sendsInE, CryptoGames.SM.Engine.vpMk,
    CryptoGames.SM.Engine.vpId, CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR,
    CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat, CryptoGames.SM.Engine.vpSetVR,
    CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpRoot,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_v5, exprSizeW_v6, exprSizeW_v7, exprSizeW_var,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_add, exprSizeW_lt, exprSizeW_eqN, exprSizeW_modK,
    exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_none, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_tget,
    exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    bits_zero, bits_one, bits_two, Nat.reduceAdd]
  omega

theorem commitEC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr L : ℕ)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (s : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.cGsTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO_cka Γ' .bool)
    (old new : Expr OO_cka Γ'
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (pos : Expr OO_cka Γ' CryptoGames.SM.posTy) :
    compSizeW (ckaOpS B0) sS qS (CryptoGames.SM.Engine.commitEC hk L es s p old new pos) ≤
      6 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) p +
        exprSizeW (ckaOpS B0) old + exprSizeW (ckaOpS B0) new +
        exprSizeW (ckaOpS B0) pos) + Ho + 5 * bits L + 1000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ0 : List (Ty S_cka) :=
    .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod (CryptoGames.SM.Engine.cGsTy vpT)
      (.prod .bool (.prod vpT vpT))) :: Γ'
  have hcm := hhk.commit_le (Γ' := Γ0)
    (CryptoGames.SM.Engine.esH (.fst .v0)) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
  simp only [CryptoGames.SM.Engine.esH, exprSizeW_v0, exprSizeW_var, exprSizeW_fst, exprSizeW_snd,
    Nat.reduceAdd] at hcm
  simp only [CryptoGames.SM.Engine.commitEC, CryptoGames.SM.Engine.cAcceptE,
    CryptoGames.SM.Engine.cDeleteE, CryptoGames.SM.Engine.cCompDeleteE,
    CryptoGames.SM.Engine.cCompSetE, CryptoGames.SM.Engine.cGsSetStP,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG,
    CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
    CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    CryptoGames.SM.pSet, CryptoGames.SM.pGet, CryptoGames.SM.maxAccSet, CryptoGames.SM.maxAccGet,
    CryptoGames.SM.maxN, CryptoGames.SM.leN, CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_add, exprSizeW_lt, exprSizeW_eqN,
    exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_none, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_nil,
    exprSizeW_cons, exprSizeW_letE, exprSizeW_foldrB, exprSizeW_tget, exprSizeW_tset,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    bits_zero, bits_one, bits_two, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
private theorem transmitEC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L qep : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins))))) :
    compSizeW (ckaOpS B0) sS qS
      (CryptoGames.SM.Engine.transmitEC hk L 3 qep mo.policy es arg) ≤
      6 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) arg) +
        Ho + Hs + 3 * bits L + 4 * bits qep +
        3 * bits (mo.tL.getD 0) + 5 * bits mo.tStar + 3000 := by
  have hpol_tL : mo.policy.tL = mo.tL := rfl
  have hpol_tStar : mo.policy.tStar = mo.tStar := rfl
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  have hvs := vSendC_sizeW_le hk Ho Hs Hr hhk
    (Γ' := CryptoGames.SM.Engine.cGsTy vpT :: .prod esT trQ :: Γ')
    (CryptoGames.SM.Engine.esH (.fst .v1)) .v0 (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst (.snd .v1)))
    (.fst (.snd (.snd .v1))) .none (.snd (.snd (.snd .v1)))
  simp only [CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.pGet,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_none, exprSizeW_letE, Nat.reduceAdd] at hvs
  simp only [CryptoGames.SM.Engine.transmitEC, CryptoGames.SM.Engine.cEpMgmtE,
    CryptoGames.SM.Engine.cSafeChE, CryptoGames.SM.Engine.cLeakE,
    CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cRecordE,
    CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE,
    CryptoGames.SM.Engine.leakDoomE, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort,
    CryptoGames.SM.Engine.esSetAbort, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    optNatLit_sizeW, hpol_tL, hpol_tStar, CryptoGames.SM.sendsInE,
    CryptoGames.SM.healedByE, CryptoGames.SM.pGet, CryptoGames.SM.pSet, CryptoGames.SM.orE,
    CryptoGames.SM.isSomeE, CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.maxOptE,
    CryptoGames.SM.ltOptE, CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender,
    CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, ckaOpS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3,
    exprSizeW_v4, exprSizeW_v5, exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub,
    exprSizeW_mulK, exprSizeW_divK, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not,
    exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl,
    exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE,
    exprSizeW_op, exprSizeW_cons, exprSizeW_len, exprSizeW_take, exprSizeW_appendL,
    exprSizeW_findB, exprSizeW_anyB, exprSizeW_mapB, exprSizeW_foldrB, exprSizeW_tconst,
    exprSizeW_tget, exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    compSizeW_caseSum, bits_zero, bits_one, bits_two, bits_three, bits_four,
    Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd]
  (try split_ifs) <;> omega

set_option linter.unusedSimpArgs false in
private theorem challEC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L qep : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ'
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins)))))) :
    compSizeW (ckaOpS B0) sS qS
      (CryptoGames.SM.Engine.challEC hk L 3 qep
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es arg) ≤
      6 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) arg) +
        Ho + Hs + 3 * bits L + 4 * bits qep +
        3 * bits (mo.tL.getD 0) + 6 * bits mo.tStar + 3000 := by
  have hpol_tL : mo.policy.tL = mo.tL := rfl
  have hpol_tStar : mo.policy.tStar = mo.tStar := rfl
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  have hvs := vSendC_sizeW_le hk Ho Hs Hr hhk
    (Γ' := CryptoGames.SM.Engine.cGsTy vpT :: .prod esT chQ :: Γ')
    (CryptoGames.SM.Engine.esH (.fst .v1)) .v0 (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst (.snd .v1)))
    ((CryptoGames.SM.Engine.modeCfgEC OO_cka mo).challMsgE
      (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v0) (.fst (.snd .v1)))
      (CryptoGames.SM.Engine.cGsB (CryptoGames.SM.Engine.esG (.fst .v1)))
      (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
    (.some (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))))
    (.snd (.snd (.snd (.snd .v1))))
  simp only [modeCfgEC_challMsgE_sizeW, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsB,
    CryptoGames.SM.pGet, exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_ite, exprSizeW_pair,
    exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_letE, Nat.reduceAdd] at hvs
  simp only [CryptoGames.SM.Engine.challEC, CryptoGames.SM.Engine.cEpMgmtE,
    CryptoGames.SM.Engine.cSafeChE, CryptoGames.SM.Engine.cLeakE,
    CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cRecordE,
    CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE,
    CryptoGames.SM.Engine.leakDoomE, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort,
    CryptoGames.SM.Engine.esSetAbort, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    modeCfgEC_challMsgE_sizeW, modeCfgEC_challOKE_sizeW, optNatLit_sizeW, hpol_tL, hpol_tStar,
    CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE, CryptoGames.SM.pGet, CryptoGames.SM.pSet,
    CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
    CryptoGames.SM.maxOptE, CryptoGames.SM.ltOptE, CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, ckaOpS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
    exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_mulK, exprSizeW_divK,
    exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some,
    exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_cons,
    exprSizeW_len, exprSizeW_take, exprSizeW_appendL, exprSizeW_findB, exprSizeW_anyB,
    exprSizeW_mapB, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
    bits_zero, bits_one, bits_two, bits_three, bits_four, Bool.false_eq_true, ↓reduceIte,
    Nat.reduceAdd]
  (try split_ifs) <;> omega

set_option linter.unusedSimpArgs false in
private theorem deliverEC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L maxSkip : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    compSizeW (ckaOpS B0) sS qS
      (CryptoGames.SM.Engine.deliverEC hk L maxSkip
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg) ≤
      6 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) arg) +
        2 * Ho + Hr + 9 * bits L + 5 * bits maxSkip + 6000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_dl0 : List (Ty S_cka) := .prod esT dlQ :: Γ'
  have hit := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_dl0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0)))
    (.snd (.snd .v0))
  have hvr := vRecvC_sizeW_le hk Ho Hs Hr hhk (Γ' := CryptoGames.SM.Engine.cRecTy :: Γ_dl0)
    (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd .v1)) (.some .v0)
  have hcm := commitEC_sizeW_le hk Ho Hs Hr L hhk
    (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: CryptoGames.SM.Engine.cRecTy :: Γ_dl0)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (CryptoGames.SM.Engine.cRecPos .v3)
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.pGet,
    CryptoGames.SM.otherE, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_var, exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_some, exprSizeW_letE, Nat.reduceAdd] at hit hvr hcm
  simp only [CryptoGames.SM.Engine.deliverEC, CryptoGames.SM.Engine.cCompContainsE,
    CryptoGames.SM.Engine.cChallContainsE, CryptoGames.SM.Engine.cMustBeCorrectE,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.Engine.cRecMsg, CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.otherE,
    CryptoGames.SM.leN, CryptoGames.SM.maxAccGet, CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, ckaOpS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
    exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_mulK, exprSizeW_divK,
    exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some,
    exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_cons,
    exprSizeW_len, exprSizeW_take, exprSizeW_appendL, exprSizeW_findB, exprSizeW_anyB,
    exprSizeW_mapB, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
    bits_zero, bits_one, bits_two, bits_three, bits_four, Bool.false_eq_true, ↓reduceIte,
    Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
private theorem injectEC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L qep : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    compSizeW (ckaOpS B0) sS qS
      (CryptoGames.SM.Engine.injectEC hk L 3 qep
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg) ≤
      6 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) arg) +
        2 * Ho + Hr + 8 * bits L + 4 * bits qep + 3 * bits mo.tStar + 6000 := by
  have hqep1 := bits_succ_le qep
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_ij0 : List (Ty S_cka) := .prod esT dlQ :: Γ'
  have hit := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_ij0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0)))
    (.snd (.snd .v0))
  have hvr := vRecvC_sizeW_le hk Ho Hs Hr hhk (Γ' := Γ_ij0)
    (CryptoGames.SM.Engine.esH (.fst .v0)) (CryptoGames.SM.Engine.esG (.fst .v0)) (.fst (.snd .v0))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v0))) (.fst (.snd .v0)))
    (.snd (.snd .v0)) .none
  have hcm := commitEC_sizeW_le hk Ho Hs Hr L hhk
    (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ_ij0)
    (CryptoGames.SM.Engine.esSetH (.fst .v3) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v3)) (.fst (.snd .v3))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v3))) (.fst (.snd .v3)))
    (.fst .v0) (.pair (CryptoGames.SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.pGet, CryptoGames.SM.otherE,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
    exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none,
    exprSizeW_letE, Nat.reduceAdd] at hit hvr hcm
  simp only [CryptoGames.SM.Engine.injectEC, CryptoGames.SM.Engine.cSafeInjE,
    CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cTrivialE,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    modeCfgEC_injectFullE_sizeW, optNatLit_sizeW, CryptoGames.SM.healedByE, CryptoGames.SM.pGet,
    CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE, CryptoGames.SM.leN,
    CryptoGames.SM.minN, CryptoGames.SM.ltOptE, CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, ckaOpS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
    exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_mulK, exprSizeW_divK,
    exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some,
    exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_cons,
    exprSizeW_len, exprSizeW_take, exprSizeW_appendL, exprSizeW_findB, exprSizeW_anyB,
    exprSizeW_mapB, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
    bits_zero, bits_one, bits_two, bits_three, bits_four, Bool.false_eq_true, ↓reduceIte,
    Nat.reduceAdd]
  (try split_ifs) <;> omega

set_option linter.unusedSimpArgs false in
private theorem corrEC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO_cka Γ' .bool) :
    compSizeW (ckaOpS B0) sS qS
      (CryptoGames.SM.Engine.corrEC hk L mo.policy es p) ≤
      6 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) p) +
        Ho + 57 * bits L + 10 * bits (mo.tL.getD 0) + 8 * bits mo.tStar + 11500 := by
  have hpol_tL : mo.policy.tL = mo.tL := rfl
  have hpol_tStar : mo.policy.tStar = mo.tStar := rfl
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let Γ_cr0 : List (Ty S_cka) := .prod esT .bool :: Γ'
  have hcd := corrDoomE_sizeW_le (O' := OO_cka) (ckaOpS B0) mo.policy (Γ' := Γ_cr0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hrv := hhk.reveal_le (Γ' := Γ_cr0)
    (CryptoGames.SM.Engine.esH (.fst .v0)) (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v0))) (.snd .v0))
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.pGet, hpol_tL, hpol_tStar,
    exprSizeW_v0, exprSizeW_var, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_letE, Nat.reduceAdd] at hcd hrv
  simp only [CryptoGames.SM.Engine.corrEC, CryptoGames.SM.Engine.cLeakE,
    CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cCorrAllowedE,
    CryptoGames.SM.Engine.cAfterCorrE, CryptoGames.SM.Engine.cCompInsertE,
    CryptoGames.SM.Engine.cCompSetE, CryptoGames.SM.Engine.leakDoomE,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetAbort, CryptoGames.SM.Engine.cGsMk,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
    CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    CryptoGames.SM.Engine.cRecPos, optNatLit_sizeW, hpol_tL, hpol_tStar, CryptoGames.SM.pGet,
    CryptoGames.SM.pSet, CryptoGames.SM.orE, CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
    CryptoGames.SM.maxOptE, CryptoGames.SM.ltOptE, CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, ckaOpS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
    exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_mulK, exprSizeW_divK,
    exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some,
    exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_cons,
    exprSizeW_len, exprSizeW_take, exprSizeW_appendL, exprSizeW_findB, exprSizeW_anyB,
    exprSizeW_mapB, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
    bits_zero, bits_one, bits_two, bits_three, bits_four, Bool.false_eq_true, ↓reduceIte,
    Nat.reduceAdd]
  (try split_ifs) <;> omega

set_option linter.unusedSimpArgs false in
theorem implEC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L qep maxSkip : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    compSizeW (ckaOpS B0) sS qS
      (CryptoGames.SM.Engine.implEC hk L 3 qep maxSkip
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es q) ≤
      60 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) q) +
        7 * Ho + 2 * Hs + 2 * Hr + 80 * bits L + 20 * bits qep + 10 * bits maxSkip +
        20 * bits (mo.tL.getD 0) + 25 * bits mo.tStar + 30000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let Γ_base : List (Ty S_cka) := .prod esT smqT :: Γ'
  let Γ_cr : List (Ty S_cka) := .bool :: Γ_base
  let Γ_s1 : List (Ty S_cka) := .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γ_base
  let Γ_ij : List (Ty S_cka) := dlQ :: Γ_s1
  let Γ_s2 : List (Ty S_cka) := .sum (.sum trQ chQ) dlQ :: Γ_s1
  let Γ_dl : List (Ty S_cka) := dlQ :: Γ_s2
  let Γ_s3 : List (Ty S_cka) := .sum trQ chQ :: Γ_s2
  let Γ_tr : List (Ty S_cka) := trQ :: Γ_s3
  let Γ_ch : List (Ty S_cka) := chQ :: Γ_s3
  have h_tr := transmitEC_sizeW_le hk Ho Hs Hr L qep mo hhk (Γ' := Γ_tr) (.fst .v4) .v0
  have h_ch := challEC_sizeW_le hk Ho Hs Hr L qep mo hhk (Γ' := Γ_ch) (.fst .v4) .v0
  have h_dl := deliverEC_sizeW_le hk Ho Hs Hr L maxSkip mo hhk (Γ' := Γ_dl) (.fst .v3) .v0
  have h_ij := injectEC_sizeW_le hk Ho Hs Hr L qep mo hhk (Γ' := Γ_ij) (.fst .v2) .v0
  have h_cr := corrEC_sizeW_le hk Ho Hs Hr L mo hhk (Γ' := Γ_cr) (.fst .v1) .v0
  simp only [exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_var, exprSizeW_fst, Nat.reduceAdd] at h_tr h_ch h_dl h_ij h_cr
  simp only [CryptoGames.SM.Engine.implEC,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_var,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr,
    compSizeW_ret, compSizeW_bind, compSizeW_caseSum, Nat.reduceAdd]
  omega

section HooksCKAAndPRNGSize

variable {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

theorem hooksCKAC_sizeBounded (B0 B : ℕ) (mo : CryptoGames.SM.Construction.Mode) :
    HooksSizeBounded B0 ckaSampS ckaQueryS
      (CryptoGames.SM.Construction.hooksCKAC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 mo)
      (5 * bits mo.tH + 5 * bits mo.tStar + 5000) 2000 (3 * bits B0 + 2 * bits B + 2000) where
  startSend_le h ctx p t γv σ r := by
    have htH1 := bits_succ_le mo.tH
    simp only [CryptoGames.SM.Construction.hooksCKAC, CryptoGames.SM.Construction.ckaStartSendC,
      CryptoGames.SM.leN, ckaOpS, ckaSampS, ckaQueryS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
      exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, exprSizeW_v6, exprSizeW_v7, exprSizeW_var,
      exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not,
      exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op, exprSizeW_tget,
      exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
      compSizeW_sample, compSizeW_query, bits_zero, bits_one, Nat.reduceAdd]
    omega
  startRecv_le h ctx p t γv σ tn := by
    simp only [CryptoGames.SM.Construction.hooksCKAC, CryptoGames.SM.Construction.ckaStartRecvC,
      CryptoGames.SM.Construction.ckaStartRecvAnsE, ckaOpS, exprSizeW_v0, exprSizeW_v1,
      exprSizeW_v2, exprSizeW_v3, exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_eqN,
      exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op, exprSizeW_tget,
      compSizeW_ret, Nat.reduceAdd]
    omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [CryptoGames.SM.Construction.hooksCKAC, CryptoGames.SM.Construction.ckaFsSendC,
      ckaOpS, exprSizeW_pair, exprSizeW_some, exprSizeW_op, compSizeW_ret, Nat.reduceAdd]
    omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    simp only [CryptoGames.SM.Construction.hooksCKAC, CryptoGames.SM.Construction.ckaFsRecvC,
      ckaOpS, exprSizeW_pair, exprSizeW_some, exprSizeW_op, compSizeW_ret, Nat.reduceAdd]
    omega
  commit_le h ctx p old new := by
    have htH1 := bits_succ_le mo.tH
    simp only [CryptoGames.SM.Construction.hooksCKAC, CryptoGames.SM.Construction.ckaCommitC,
      CryptoGames.SM.isSomeE, CryptoGames.SM.leN, CryptoGames.SM.Engine.vpSetΓ,
      CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId, CryptoGames.SM.Engine.vpRoot,
      CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR, CryptoGames.SM.Engine.vpΓ,
      CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat, ckaQueryS, exprSizeW_v0,
      exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var, exprSizeW_bool,
      exprSizeW_nat, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_some,
      exprSizeW_caseOpt, exprSizeW_letE, compSizeW_ret, compSizeW_bind, compSizeW_ite,
      compSizeW_caseOpt, compSizeW_query, bits_zero, bits_one, Nat.reduceAdd]
    omega
  reveal_le h ctx p vp := by
    simp only [CryptoGames.SM.Construction.hooksCKAC, CryptoGames.SM.Construction.ckaRevealC,
      CryptoGames.SM.Engine.realPartyE, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId,
      CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR,
      CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat,
      ckaQueryS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
      exprSizeW_nat, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_some,
      exprSizeW_caseOpt, exprSizeW_letE, compSizeW_ret, compSizeW_bind, compSizeW_caseOpt,
      compSizeW_query, bits_zero, Nat.reduceAdd]
    omega

theorem hooksPRNGC_sizeBounded (B0 B : ℕ) (mo : CryptoGames.SM.Construction.Mode) :
    HooksSizeBounded B0 ckaSampS ckaQueryS
      (CryptoGames.SM.Construction.hooksPRNGC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo)
      (5 * bits mo.tH + 5 * bits mo.tStar + 3000) 2000 (3 * bits B0 + 2 * bits B + 2000) where
  startSend_le h ctx p t γv σ r := by
    simp only [CryptoGames.SM.Construction.hooksPRNGC, CryptoGames.SM.Construction.prngStartSendC,
      CryptoGames.SM.Construction.rootPRNGC, CryptoGames.SM.Construction.prngProcessCorrC,
      ckaOpS, ckaSampS, ckaQueryS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3,
      exprSizeW_v4, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_lt,
      exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_none, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE,
      exprSizeW_op, exprSizeW_tget, exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite,
      compSizeW_caseOpt, compSizeW_sample, compSizeW_query, bits_zero, Nat.reduceAdd]
    omega
  startRecv_le h ctx p t γv σ tn := by
    simp only [CryptoGames.SM.Construction.hooksPRNGC, CryptoGames.SM.Construction.prngStartRecvC,
      ckaOpS, ckaQueryS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
      exprSizeW_bool, exprSizeW_nat, exprSizeW_eqN, exprSizeW_and, exprSizeW_ite, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_some, exprSizeW_caseOpt,
      exprSizeW_letE, exprSizeW_op, exprSizeW_tget, compSizeW_ret, compSizeW_bind, compSizeW_ite,
      compSizeW_caseOpt, compSizeW_query, Nat.reduceAdd]
    omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [CryptoGames.SM.Construction.hooksPRNGC, CryptoGames.SM.Construction.prngFsSendC,
      ckaOpS, exprSizeW_pair, exprSizeW_some, exprSizeW_op, compSizeW_ret, Nat.reduceAdd]
    omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    simp only [CryptoGames.SM.Construction.hooksPRNGC, CryptoGames.SM.Construction.prngFsRecvC,
      ckaOpS, exprSizeW_pair, exprSizeW_some, exprSizeW_op, compSizeW_ret, Nat.reduceAdd]
    omega
  commit_le h ctx p old new := by
    simp only [CryptoGames.SM.Construction.hooksPRNGC, CryptoGames.SM.Construction.prngCommitC,
      exprSizeW_pair, exprSizeW_some, compSizeW_ret, Nat.reduceAdd]
    omega
  reveal_le h ctx p vp := by
    simp only [CryptoGames.SM.Construction.hooksPRNGC, CryptoGames.SM.Construction.prngRevealC,
      CryptoGames.SM.Engine.realPartyE, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId,
      CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR,
      CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_nat, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_some, exprSizeW_caseOpt,
      exprSizeW_letE, compSizeW_ret, compSizeW_bind, compSizeW_caseOpt, bits_zero, Nat.reduceAdd]
    omega

theorem initCKAEStateC_sizeW_le (B0 : ℕ) (mo : CryptoGames.SM.Construction.Mode) {Γ'}
    (bE : Expr OO_cka Γ' .bool) :
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS
      (CryptoGames.SM.Construction.initCKAEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo bE) ≤ exprSizeW (ckaOpS B0) bE + 8000 := by
  simp only [CryptoGames.SM.Construction.initCKAEStateC, CryptoGames.SM.Engine.mkPartiesE,
    CryptoGames.SM.Engine.cGsInitE, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.Engine.vpMk, ckaOpS, ckaSampS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
    exprSizeW_v3, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
    exprSizeW_nil, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_letE,
    exprSizeW_op, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset, compSizeW_ret, compSizeW_bind,
    compSizeW_ite, compSizeW_sample, bits_zero, Nat.reduceAdd]
  omega

theorem initPRNGEStateC_sizeW_le (B0 : ℕ) (mo : CryptoGames.SM.Construction.Mode) {Γ'}
    (bE : Expr OO_cka Γ' .bool) :
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS
      (CryptoGames.SM.Construction.initPRNGEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo bE) ≤
      exprSizeW (ckaOpS B0) bE + 5 * bits mo.tH + 5 * bits mo.tStar + 5200 := by
  simp only [CryptoGames.SM.Construction.initPRNGEStateC, CryptoGames.SM.Construction.rootPRNGC,
    CryptoGames.SM.Construction.prngProcessCorrC, CryptoGames.SM.Construction.abortedPartiesE,
    CryptoGames.SM.Engine.mkPartiesE, CryptoGames.SM.Engine.cGsInitE, CryptoGames.SM.Engine.cGsMk,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.vpMk, ckaOpS, ckaSampS, ckaQueryS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
    exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not,
    exprSizeW_and, exprSizeW_ite, exprSizeW_none, exprSizeW_nil, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op,
    exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite,
    compSizeW_caseOpt, compSizeW_sample, compSizeW_query, bits_zero, Nat.reduceAdd]
  omega

end HooksCKAAndPRNGSize

section HooksFSCSize

variable {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "hsTy_fs" => CryptoGames.SM.Construction.fsHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "vpTy_fs" => CryptoGames.SM.Construction.fsVpTy KC Γ CCoins T I KR RSt K SS RS M E

theorem lookupFC_sizeW_le (B0 L : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' hsTy_fs) (ikE : Expr OO_cka Γ' (.base .i)) :
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS
      (CryptoGames.SM.Construction.lookupFC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L hE ikE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ikE + bits L + 450 := by
  simp only [CryptoGames.SM.Construction.lookupFC, CryptoGames.SM.Construction.tableLookupE,
    CryptoGames.SM.Construction.fsHsSetTable, CryptoGames.SM.Construction.fsHsMk,
    CryptoGames.SM.Construction.fsHsCache, CryptoGames.SM.Construction.fsHsTable,
    CryptoGames.SM.Construction.fsHsSessions, CryptoGames.SM.Construction.fsHsTrans,
    CryptoGames.SM.Construction.fsHsCount, CryptoGames.SM.Construction.fsHsSCorr,
    CryptoGames.SM.Construction.fsHsExt, ckaOpS, ckaSampS, ckaQueryS, exprSizeW_v0, exprSizeW_v1,
    exprSizeW_v2, exprSizeW_v3, exprSizeW_var, exprSizeW_unit, exprSizeW_none, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_caseOpt,
    exprSizeW_letE, exprSizeW_op, exprSizeW_cons, exprSizeW_foldrB, compSizeW_ret, compSizeW_bind,
    compSizeW_caseOpt, compSizeW_sample, Nat.reduceAdd]
  omega

theorem isExtE_sizeW_le (B0 L j : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' hsTy_fs) (ikE : Expr OO_cka Γ' (.base .i)) :
    exprSizeW (ckaOpS B0) (CryptoGames.SM.Construction.isExtE L j hE ikE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ikE + 4 * bits L + 2 * bits j + 800 := by
  simp only [CryptoGames.SM.Construction.isExtE, CryptoGames.SM.Construction.sessionsMemE,
    CryptoGames.SM.Construction.sessionsIdxOfE, CryptoGames.SM.Construction.sessionsLenE,
    CryptoGames.SM.Construction.sessionsAppendOneE, CryptoGames.SM.Construction.fsHsSetSessions,
    CryptoGames.SM.Construction.fsHsMk, CryptoGames.SM.Construction.fsHsCache,
    CryptoGames.SM.Construction.fsHsTable, CryptoGames.SM.Construction.fsHsSessions,
    CryptoGames.SM.Construction.fsHsTrans, CryptoGames.SM.Construction.fsHsCount,
    CryptoGames.SM.Construction.fsHsSCorr, CryptoGames.SM.Construction.fsHsExt, CryptoGames.SM.orE,
    ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_nil, exprSizeW_add, exprSizeW_eqN, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_letE, exprSizeW_op, exprSizeW_cons, exprSizeW_foldrB, bits_zero,
    bits_one, Nat.reduceAdd]
  omega

theorem extOfE_sizeW_le (B0 L j : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' hsTy_fs) (sidE : Expr OO_cka Γ' (.opt (.base .i))) :
    exprSizeW (ckaOpS B0) (CryptoGames.SM.Construction.extOfE L j hE sidE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) sidE + 4 * bits L + 2 * bits j + 850 := by
  have hie := isExtE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) B0 L j (Γ' := .base .i :: .prod hsTy_fs (.opt (.base .i)) :: Γ')
    (.fst .v1) .v0
  simp only [exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_fst, Nat.reduceAdd] at hie
  simp only [CryptoGames.SM.Construction.extOfE, exprSizeW_v0, exprSizeW_var, exprSizeW_bool,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE, Nat.reduceAdd]
  omega

theorem rootFSC_sizeW_le (B0 L : ℕ) (mo : CryptoGames.SM.Construction.Mode) {Γ'}
    (hE : Expr OO_cka Γ' hsTy_fs) (tE : Expr OO_cka Γ' .nat)
    (ikE : Expr OO_cka Γ' (.base .i)) (σE : Expr OO_cka Γ' (.base .sig)) :
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS
      (CryptoGames.SM.Construction.rootFSC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo hE tE ikE σE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) ikE +
        exprSizeW (ckaOpS B0) σE + bits L + 3 * bits mo.tStar + 3 * bits mo.tH + 3200 := by
  have hlk := lookupFC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L
    (Γ' := .prod hsTy_fs (.prod .nat (.prod (.base .i) (.base .sig))) :: Γ')
    (.fst .v0) (.fst (.snd (.snd .v0)))
  simp only [exprSizeW_v0, exprSizeW_var, exprSizeW_fst, exprSizeW_snd, Nat.reduceAdd] at hlk
  simp only [CryptoGames.SM.Construction.rootFSC, ckaOpS, ckaSampS, ckaQueryS, exprSizeW_v0,
    exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_lt, exprSizeW_eqN, exprSizeW_and, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_some, exprSizeW_op, compSizeW_ret, compSizeW_bind, compSizeW_ite,
    compSizeW_sample, Nat.reduceAdd]
  omega

theorem fsTransFindE_sizeW_le (B0 L : ℕ) {Γ'}
    (trE : Expr OO_cka Γ'
      (.list (CryptoGames.SM.Construction.fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (hcE : Expr OO_cka Γ' (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprSizeW (ckaOpS B0) (CryptoGames.SM.Construction.fsTransFindE L trE hcE) ≤
      exprSizeW (ckaOpS B0) trE + exprSizeW (ckaOpS B0) hcE + bits L + 700 := by
  simp only [CryptoGames.SM.Construction.fsTransFindE, CryptoGames.SM.Engine.hdrCtEqE,
    CryptoGames.SM.Engine.optTEqE, ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var,
    exprSizeW_bool, exprSizeW_eqN, exprSizeW_and, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op, exprSizeW_findB, Nat.reduceAdd]
  omega

theorem rangeListC_sizeW {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} (opS : O'.Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (L : ℕ) {Γ' : List (Ty S')} :
    compSizeW opS sS qS
      (CryptoGames.SM.Construction.rangeListC (O' := O') (I' := I') L (Γ' := Γ')) =
      bits L + 19 := by
  simp only [CryptoGames.SM.Construction.rangeListC, exprSizeW_v0, exprSizeW_var, exprSizeW_nat,
    exprSizeW_nil, exprSizeW_add, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_cons,
    compSizeW_ret, compSizeW_bind, compSizeW_iter, bits_zero, bits_one, Nat.reduceAdd]
  omega

theorem unliftVRE_sizeW_le (opS : (OO_cka).Op → ℕ) (L : ℕ) {Γ'}
    (vRE : Expr OO_cka Γ' (.tbl (.opt (.opt (.base .rs)))))
    (rsExtE : Expr OO_cka Γ' (.opt (.base .rs)))
    (rngE : Expr OO_cka Γ' (.list .nat)) :
    exprSizeW opS (CryptoGames.SM.Construction.unliftVRE (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) L vRE rsExtE rngE) ≤
      exprSizeW opS vRE + exprSizeW opS rsExtE + exprSizeW opS rngE + bits L + 100 := by
  simp only [CryptoGames.SM.Construction.unliftVRE, CryptoGames.SM.Construction.unliftEntryE,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_none, exprSizeW_pair,
    exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE,
    exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset, Nat.reduceAdd]
  omega

theorem hooksFSC_sizeBounded (B0 L B : ℕ) (mo : CryptoGames.SM.Construction.Mode) (j : ℕ) :
    HooksSizeBounded B0 ckaSampS ckaQueryS
      (CryptoGames.SM.Construction.hooksFSC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B 1 mo j)
      (40 * bits L + 20 * bits j + 6 * bits mo.tStar + 6 * bits mo.tH + 14000) 2000
      (6 * bits B0 + 4 * bits B + 4 * bits L + 5000) where
  startSend_le {Γ'} hE ctxE pE tE γE σE rE := by
    let Γ0 : List (Ty S_cka) := .base .ccoins :: .prod hsTy_fs (.prod .nat (.prod (.base .γ)
      (.prod (.base .sig) (.opt (.base .ccoins))))) :: Γ'
    let Γ1 : List (Ty S_cka) := .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) hsTy_fs :: Γ0
    have hrt := rootFSC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
      (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR)
      (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B0 L mo
      (Γ' := Γ0) (.fst .v1) (.fst (.snd .v1))
      (.snd (.snd (Expr.op (O := OO_cka) CryptoGames.CKA.CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1))))
    have hext := extOfE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
      (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) B0 L j (Γ' := Γ1)
      (.snd .v0) (.snd (.snd (.fst .v0)))
    simp only [ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_op, Nat.reduceAdd] at hrt hext
    simp only [CryptoGames.SM.Construction.hooksFSC, CryptoGames.SM.Construction.fsStartSendC,
      CryptoGames.SM.Construction.fsHsSetCache, CryptoGames.SM.Construction.fsHsMk,
      CryptoGames.SM.Construction.fsHsCache, CryptoGames.SM.Construction.fsHsTable,
      CryptoGames.SM.Construction.fsHsSessions, CryptoGames.SM.Construction.fsHsTrans,
      CryptoGames.SM.Construction.fsHsCount, CryptoGames.SM.Construction.fsHsSCorr,
      CryptoGames.SM.Construction.fsHsExt, ckaOpS, ckaSampS, ckaQueryS, exprSizeW_v0, exprSizeW_v1,
      exprSizeW_v2, exprSizeW_var, exprSizeW_unit, exprSizeW_none, exprSizeW_ite, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_op, exprSizeW_tset, compSizeW_ret,
      compSizeW_bind, compSizeW_caseOpt, compSizeW_sample, Nat.reduceAdd]; omega
  startRecv_le {Γ'} hE ctxE pE tE γE σE tnE := by
    let Γ0 : List (Ty S_cka) := .prod hsTy_fs (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.base .t)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .prod (.base .k) hsTy_fs :: Γ0
    have hlk := lookupFC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
      (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR)
      (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B0 L (Γ' := Γ0)
      (.fst .v0) (.snd (Expr.op (O := OO_cka) CryptoGames.CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))))
    have hie := isExtE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
      (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) B0 L j (Γ' := Γ1)
      (.snd .v0) (.snd (Expr.op (O := OO_cka) CryptoGames.CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))
    simp only [ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_op, Nat.reduceAdd] at hlk hie
    simp only [CryptoGames.SM.Construction.hooksFSC, CryptoGames.SM.Construction.fsStartRecvC,
      CryptoGames.SM.Construction.fsHsCache, ckaOpS, ckaSampS, ckaQueryS, exprSizeW_v0,
      exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_eqN, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_op, exprSizeW_tget, compSizeW_ret,
      compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, Nat.reduceAdd]; omega
  fsSend_le hE ctxE pE tE ssvE hdrE mE pairE := by
    simp only [CryptoGames.SM.Construction.hooksFSC, CryptoGames.SM.Construction.fsFsSendC,
      CryptoGames.SM.Engine.cSafeChE, CryptoGames.SM.Construction.fsHsSetSCorr,
      CryptoGames.SM.Construction.fsHsSetCountTrans, CryptoGames.SM.Construction.fsHsSetExt,
      CryptoGames.SM.Construction.fsHsMk, CryptoGames.SM.Construction.fsHsCache,
      CryptoGames.SM.Construction.fsHsTable, CryptoGames.SM.Construction.fsHsSessions,
      CryptoGames.SM.Construction.fsHsTrans, CryptoGames.SM.Construction.fsHsCount,
      CryptoGames.SM.Construction.fsHsSCorr, CryptoGames.SM.Construction.fsHsExt,
      CryptoGames.SM.healedByE, CryptoGames.SM.leN, CryptoGames.SM.pGet,
      CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsEpoch, ckaOpS, ckaSampS, ckaQueryS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var, exprSizeW_unit,
      exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_add, exprSizeW_lt, exprSizeW_not,
      exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some,
      exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op, exprSizeW_cons, compSizeW_ret, compSizeW_bind,
      compSizeW_ite, compSizeW_caseOpt, compSizeW_query, bits_one, bits_three, Nat.reduceAdd]; omega
  fsRecv_le {Γ'} hE ctxE pE tE rsvE hdrE eE recE := by
    let hdrT := CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
    let Γ0 : List (Ty S_cka) := .prod hsTy_fs (.prod (.opt (.base .rs)) (.prod hdrT
      (.prod (.base .ct) (.opt CryptoGames.SM.Engine.cRecTy)))) :: Γ'
    let rrT : Ty S_cka := .sum .unit (.prod .nat (.opt (.base .msg)))
    let Γ1 : List (Ty S_cka) := .prod .nat (.opt (.base .msg)) :: rrT :: .opt rrT :: Γ0
    have htf0 := fsTransFindE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
      (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ0)
      (CryptoGames.SM.Construction.fsHsTrans (.fst .v0)) (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))))
    have htf3 := fsTransFindE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
      (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
      (CryptoGames.SM.Construction.fsHsTrans (.fst .v3)) (.pair (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3)))))
    simp only [CryptoGames.SM.Construction.fsHsTrans, exprSizeW_v0, exprSizeW_v3, exprSizeW_var,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, Nat.reduceAdd] at htf0 htf3
    simp only [CryptoGames.SM.Construction.hooksFSC, CryptoGames.SM.Construction.fsFsRecvC,
      CryptoGames.SM.Construction.fsTransFilterE, CryptoGames.SM.Construction.fsHsSetTrans,
      CryptoGames.SM.Construction.fsHsSetExt, CryptoGames.SM.Construction.fsHsMk,
      CryptoGames.SM.Construction.fsHsCache, CryptoGames.SM.Construction.fsHsTable,
      CryptoGames.SM.Construction.fsHsSessions, CryptoGames.SM.Construction.fsHsTrans,
      CryptoGames.SM.Construction.fsHsCount, CryptoGames.SM.Construction.fsHsSCorr,
      CryptoGames.SM.Construction.fsHsExt, CryptoGames.SM.Engine.cRecMsg, ckaOpS, ckaSampS,
      ckaQueryS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
      exprSizeW_none, exprSizeW_nil, exprSizeW_eqN, exprSizeW_not, exprSizeW_ite, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE,
      exprSizeW_op, exprSizeW_cons, exprSizeW_foldrB, compSizeW_ret, compSizeW_bind,
      compSizeW_caseOpt, compSizeW_caseSum, compSizeW_query, Nat.reduceAdd]; omega
  commit_le hE ctxE pE old new := by
    simp only [CryptoGames.SM.Construction.hooksFSC, CryptoGames.SM.Construction.fsCommitC,
      exprSizeW_pair, exprSizeW_some, compSizeW_ret, Nat.reduceAdd]; omega
  reveal_le {Γ'} hE ctxE pE vpE := by
    let Γ0 : List (Ty S_cka) := .prod hsTy_fs vpTy_fs :: Γ'
    let Γ2 : List (Ty S_cka) := .opt (.base .ss) :: .prod (.opt (.opt (.base .ss))) hsTy_fs :: Γ0
    let Γ4 : List (Ty S_cka) := .opt (.base .rs) :: .prod (.opt (.opt (.base .rs))) hsTy_fs :: Γ2
    let Γ5 : List (Ty S_cka) := .list .nat :: Γ4
    have huv := unliftVRE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
      (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (ckaOpS B0) L
      (Γ' := Γ5) (CryptoGames.SM.Engine.vpVR (.snd .v5)) .v1 .v0
    simp only [CryptoGames.SM.Engine.vpVR, exprSizeW_v0, exprSizeW_v1, exprSizeW_v5, exprSizeW_var,
      exprSizeW_fst, exprSizeW_snd, Nat.reduceAdd] at huv
    simp only [CryptoGames.SM.Construction.hooksFSC, CryptoGames.SM.Construction.fsRevealC,
      CryptoGames.SM.Construction.fsHsSetSCorr, CryptoGames.SM.Construction.fsHsSetExt,
      CryptoGames.SM.Construction.fsHsMk, CryptoGames.SM.Construction.fsHsCache,
      CryptoGames.SM.Construction.fsHsTable, CryptoGames.SM.Construction.fsHsSessions,
      CryptoGames.SM.Construction.fsHsTrans, CryptoGames.SM.Construction.fsHsCount,
      CryptoGames.SM.Construction.fsHsSCorr, CryptoGames.SM.Construction.fsHsExt,
      CryptoGames.SM.Engine.realPartyE, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId,
      CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR,
      CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat,
      rangeListC_sizeW, ckaOpS, ckaSampS, ckaQueryS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
      exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, exprSizeW_var, exprSizeW_unit, exprSizeW_bool,
      exprSizeW_nat, exprSizeW_none, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_caseOpt,
      exprSizeW_letE, exprSizeW_tget, compSizeW_ret, compSizeW_bind, compSizeW_ite,
      compSizeW_caseOpt, compSizeW_query, bits_zero, Nat.reduceAdd]; omega

theorem initFSEStateC_sizeW_le (B0 L : ℕ) (mo : CryptoGames.SM.Construction.Mode) (j : ℕ) {Γ'}
    (bE : Expr OO_cka Γ' .bool) :
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS
      (CryptoGames.SM.Construction.initFSEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo j bE) ≤
      exprSizeW (ckaOpS B0) bE + 22 * bits L + 10 * bits j + 4 * bits mo.tStar + 4 * bits mo.tH + 12000 := by
  let Γ0 : List (Ty S_cka) := .base .kc :: .base .kr :: .bool :: Γ'
  let Γ1 : List (Ty S_cka) := .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) hsTy_fs :: Γ0
  have hrt := rootFSC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR)
    (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B0 L mo
    (Γ' := Γ0) CryptoGames.SM.Construction.fsHsEmptyE (.nat 0)
    (Expr.op (O := OO_cka) CryptoGames.CKA.CKAOp.lamI .unit)
    (Expr.op (O := OO_cka) CryptoGames.CKA.CKAOp.prngInit .v1)
  have hext := extOfE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) B0 L j (Γ' := Γ1)
    (.snd .v0) (.snd (.snd (.fst .v0)))
  simp only [CryptoGames.SM.Construction.fsHsEmptyE, CryptoGames.SM.Construction.fsHsMk, ckaOpS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_op,
    exprSizeW_tconst, bits_zero, Nat.reduceAdd] at hrt hext
  simp only [CryptoGames.SM.Construction.initFSEStateC, CryptoGames.SM.Engine.mkPartiesE,
    CryptoGames.SM.Engine.cGsInitE, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Construction.fsHsEmptyE,
    CryptoGames.SM.Construction.fsHsMk, ckaOpS, ckaSampS, ckaQueryS, exprSizeW_v0, exprSizeW_v1,
    exprSizeW_v2, exprSizeW_v3, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_some, exprSizeW_letE, exprSizeW_op, exprSizeW_tconst, exprSizeW_tset, compSizeW_ret,
    compSizeW_bind, compSizeW_sample, bits_zero, Nat.reduceAdd]; omega

end HooksFSCSize

end EngineSizeHelpers

end Computational.Proofs.SessionCostedFig8.ProgSizeBounds
