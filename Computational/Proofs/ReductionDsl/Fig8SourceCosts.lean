/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSessionStatements
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound
public import Computational.Proofs.ReductionDsl.PureAuxMacroLift
public import Computational.Proofs.ReductionDsl.SM.RedCKA
public import Computational.Proofs.ReductionDsl.SM.RedFS
public import Computational.Proofs.ReductionDsl.SM.RedPRNG
public import Computational.Proofs.ReductionDsl.SM.Theorem1
public import Computational.Proofs.SessionCostedBase
import Computational.Proofs.GameHop.ReductionDsl.CostUB

/-!
# Source AST cost bounds for Figure 8 `ReductionDsl` programs

Logarithmic `bits`-aware source `.cost` bounds (`fig8StepBound`) for `SM.simHandleC`,
`SM.Engine.implEC`, `hooksCKAC`, `hooksPRNGC`, `hooksFSC`, and their initializers and finalizers.
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst
  LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction SM.Engine
  CKA AEADScheme MACScheme WireAEAD FSAEAD ReductionDsl
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open Computational.Proofs.GameHop.ReductionDsl.CostUB
open Computational.Proofs.ReductionDsl.PureAuxMacroLift

namespace Computational.Proofs.ReductionDsl.Fig8SourceCosts


section Thm1CostHelpers

variable {Key St St₂ Msg Coins RCoins C : Type}
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
local notation "SIface_sm" =>
  SM.smIface Key St St₂ Msg Coins RCoins C stSort sampKey sampCoins sampRCoins
local notation "SQ_sm" => SM.smQ Key St St₂ Msg Coins RCoins C

lemma v0_cost {S' : ReductionDsl.Sig} {O' : ReductionDsl.Ops S'} {t : ReductionDsl.Ty S'} {Γ} :
    (ReductionDsl.Expr.v0 (O := O') (t := t) (Γ := Γ)).cost = 1 := rfl

lemma v1_cost {S' : ReductionDsl.Sig} {O' : ReductionDsl.Ops S'} {t a : ReductionDsl.Ty S'} {Γ} :
    (ReductionDsl.Expr.v1 (O := O') (t := t) (a := a) (Γ := Γ)).cost = 1 := rfl

lemma v2_cost {S' : ReductionDsl.Sig} {O' : ReductionDsl.Ops S'} {t a b : ReductionDsl.Ty S'} {Γ} :
    (ReductionDsl.Expr.v2 (O := O') (t := t) (a := a) (b := b) (Γ := Γ)).cost = 1 := rfl

lemma v3_cost {S' : ReductionDsl.Sig} {O' : ReductionDsl.Ops S'}
    {t a b c : ReductionDsl.Ty S'} {Γ} :
    (ReductionDsl.Expr.v3 (O := O') (t := t) (a := a) (b := b) (c := c) (Γ := Γ)).cost = 1 := rfl

lemma v4_cost {S' : ReductionDsl.Sig} {O' : ReductionDsl.Ops S'}
    {t a b c d : ReductionDsl.Ty S'} {Γ} :
    (ReductionDsl.Expr.v4 (O := O') (t := t) (a := a) (b := b) (c := c) (d := d) (Γ := Γ)).cost =
      1 := rfl

lemma v5_cost {S' : ReductionDsl.Sig} {O' : ReductionDsl.Ops S'}
    {t a b c d e : ReductionDsl.Ty S'} {Γ} :
    (ReductionDsl.Expr.v5 (O := O') (t := t) (a := a) (b := b) (c := c) (d := d) (e := e)
      (Γ := Γ)).cost = 1 := rfl

lemma v6_cost {S' : ReductionDsl.Sig} {O' : ReductionDsl.Ops S'}
    {t a b c d e f : ReductionDsl.Ty S'} {Γ} :
    (ReductionDsl.Expr.v6 (O := O') (t := t) (a := a) (b := b) (c := c) (d := d) (e := e) (f := f)
      (Γ := Γ)).cost = 1 := rfl

lemma v7_cost {S' : ReductionDsl.Sig} {O' : ReductionDsl.Ops S'}
    {t a b c d e f g : ReductionDsl.Ty S'} {Γ} :
    (ReductionDsl.Expr.v7 (O := O') (t := t) (a := a) (b := b) (c := c) (d := d) (e := e) (f := f)
      (g := g) (Γ := Γ)).cost = 1 := rfl

lemma otherE_cost {S' : ReductionDsl.Sig} {O' : ReductionDsl.Ops S'} {Γ}
    (p : ReductionDsl.Expr O' Γ .bool) :
    (SM.otherE p).cost = p.cost + 1 := rfl

lemma isSomeE_cost {S' : ReductionDsl.Sig} {O' : ReductionDsl.Ops S'} {Γ t}
    (e : ReductionDsl.Expr O' Γ (.opt t)) :
    (SM.isSomeE e).cost = e.cost + 2 := by
  simp [SM.isSomeE, ReductionDsl.Expr.cost]

lemma pGet_cost {S' : ReductionDsl.Sig} {O' : ReductionDsl.Ops S'} {Γ t}
    (m : ReductionDsl.Expr O' Γ (.prod t t)) (p : ReductionDsl.Expr O' Γ .bool) :
    (SM.pGet m p).cost = m.cost + p.cost + 8 := by
  simp [SM.pGet, ReductionDsl.Expr.cost, ReductionDsl.Expr.v0]

lemma mEpoch_cost {O' : ReductionDsl.Ops S_sm} {Γ}
    (s : ReductionDsl.Expr O' Γ SM.mirrorTy) :
    (SM.mEpoch s).cost = s.cost + 4 := rfl

lemma mIdx_cost {O' : ReductionDsl.Ops S_sm} {Γ}
    (s : ReductionDsl.Expr O' Γ SM.mirrorTy) :
    (SM.mIdx s).cost = s.cost + 5 := rfl

lemma recPos_cost {O' : ReductionDsl.Ops S_sm} {Γ}
    (r : ReductionDsl.Expr O' Γ SM.recTy) :
    (SM.recPos r).cost = r.cost + 1 := rfl

lemma mSafeChE_cost_le {O' : ReductionDsl.Ops S_sm} {Γ}
    (s : ReductionDsl.Expr O' Γ SM.mirrorTy) (p : ReductionDsl.Expr O' Γ .bool) :
    (SM.mSafeChE 3 s p).cost ≤ s.cost + p.cost + 80 := by
  have hb3 : ReductionDsl.bits 3 = 2 := rfl
  simp only [SM.mSafeChE, SM.healedByE, SM.leN, SM.pGet,
    SM.mTL, SM.mEpoch, ReductionDsl.Expr.cost, ReductionDsl.Expr.v0,
    ReductionDsl.Expr.v1, hb3, Nat.reduceAdd]
  omega

lemma mLeakE_cost_le {O' : ReductionDsl.Ops S_sm} {Γ}
    (s : ReductionDsl.Expr O' Γ SM.mirrorTy) (l : ReductionDsl.Expr O' Γ .nat) :
    (SM.mLeakE s l).cost ≤ s.cost + l.cost + 250 := by
  simp only [SM.mLeakE, SM.mMk, SM.maxOptE, SM.maxN, SM.leN,
    SM.mSt, SM.mB, SM.mWin, SM.mEpoch, SM.mIdx,
    SM.mTL, SM.mTrans, SM.mChall, SM.mComp,
    SM.mMaxAcc, SM.mLeaks, SM.mCorrs,
    ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, Nat.reduceAdd]
  omega

lemma bits_succ_le (n : ℕ) : ReductionDsl.bits (n + 1) ≤ ReductionDsl.bits n + 1 := by
  have hadd := ReductionDsl.bits_add n 1
  have h1 : ReductionDsl.bits 1 = 1 := rfl
  have hb := ReductionDsl.one_le_bits n
  omega

lemma bits_le_bits_qep_add {x qep : ℕ} (h : x ≤ qep + 7) :
    ReductionDsl.bits x ≤ ReductionDsl.bits qep + 4 := by
  have hm := ReductionDsl.bits_mono h
  have hadd := ReductionDsl.bits_add qep 7
  have h7 : ReductionDsl.bits 7 = 3 := by
    dsimp only [ReductionDsl.bits]
    have hge : 2 ≤ Nat.log 2 7 := (Nat.le_log_iff_pow_le (by omega) (by omega)).2 (by norm_num)
    have hlt : Nat.log 2 7 < 3 := Nat.log_lt_of_lt_pow (by omega) (by norm_num)
    omega
  have hb := ReductionDsl.one_le_bits qep
  omega

lemma mEpMgmtE_cost_le {O' : ReductionDsl.Ops S_sm} (qep : ℕ) {Γ}
    (s : ReductionDsl.Expr O' Γ SM.mirrorTy)
    (p bad : ReductionDsl.Expr O' Γ .bool) :
    (SM.mEpMgmtE 3 qep s p bad).cost ≤
      s.cost + p.cost + bad.cost + 5 * ReductionDsl.bits qep + 705 := by
  have hb0 : ReductionDsl.bits 0 = 1 := rfl
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  have hb2 : ReductionDsl.bits 2 = 2 := rfl
  let Γ0 : List (ReductionDsl.Ty S_sm) := .prod SM.mirrorTy (.prod .bool .bool) :: Γ
  have hsc := mSafeChE_cost_le (O' := O') (Γ := Γ0) (.fst .v0) (.fst (.snd .v0))
  have hlk := mLeakE_cost_le (O' := O') (Γ := Γ0) (.fst .v0)
    (.add (SM.pGet (SM.mEpoch (.fst .v0)) (.fst (.snd .v0))) (.nat 1))
  simp only [pGet_cost, mEpoch_cost, v0_cost, ReductionDsl.Expr.cost, hb1, Nat.reduceAdd] at hsc hlk
  simp only [SM.mEpMgmtE, SM.mMk, SM.sendsInE, SM.pSet,
    SM.mSt, SM.mB, SM.mWin, SM.mIdx,
    SM.mTL, SM.mTrans, SM.mChall, SM.mComp,
    SM.mMaxAcc, SM.mLeaks, SM.mCorrs,
    pGet_cost, mEpoch_cost, v0_cost, v1_cost,
    ReductionDsl.Expr.cost, hb0, hb1, hb2, Nat.reduceAdd]
  omega

lemma mRecordE_cost_le {O' : ReductionDsl.Ops S_sm} {Γ}
    (s : ReductionDsl.Expr O' Γ SM.mirrorTy)
    (p : ReductionDsl.Expr O' Γ .bool) (r : ReductionDsl.Expr O' Γ SM.recTy)
    (isChall : ReductionDsl.Expr O' Γ .bool) :
    (SM.mRecordE 3 s p r isChall).cost ≤
      s.cost + p.cost + r.cost + isChall.cost + 350 := by
  let Γ0 : List (ReductionDsl.Ty S_sm) :=
    .prod SM.mirrorTy (.prod .bool (.prod SM.recTy .bool)) :: Γ
  have hsc := mSafeChE_cost_le (O' := O') (Γ := Γ0) (.fst .v0) (.fst (.snd .v0))
  simp only [v0_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hsc
  simp only [SM.mRecordE, SM.mMk, SM.pSet,
    SM.recPos, SM.posIdx,
    SM.mSt, SM.mB, SM.mWin, SM.mEpoch, SM.mIdx,
    SM.mTL, SM.mTrans, SM.mChall, SM.mComp,
    SM.mMaxAcc, SM.mLeaks, SM.mCorrs,
    ReductionDsl.Expr.cost, v0_cost, Nat.reduceAdd]
  omega

lemma mB_cost {O' : ReductionDsl.Ops S_sm} {Γ}
    (s : ReductionDsl.Expr O' Γ SM.mirrorTy) :
    (SM.mB s).cost = s.cost + 2 := rfl

lemma mInTransitE_cost_le (K : ℕ) {Γ}
    (s : ReductionDsl.Expr OO_sm Γ SM.mirrorTy)
    (qParty : ReductionDsl.Expr OO_sm Γ .bool) (c : ReductionDsl.Expr OO_sm Γ (.base .ct)) :
    (SM.mInTransitE K s qParty c).cost ≤ s.cost + qParty.cost + c.cost + 40 * K + 60 := by
  have hmax34 : max 3 4 = 4 := rfl
  simp only [SM.mInTransitE, SM.mTrans, SM.recPos, SM.recCt, SM.posSender, SM.boolEq,
    ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
    SM.smOps, hmax34, Nat.reduceAdd]
  omega

lemma mDeleteE_cost_le {O' : ReductionDsl.Ops S_sm} (K : ℕ) {Γ}
    (s : ReductionDsl.Expr O' Γ SM.mirrorTy)
    (pos : ReductionDsl.Expr O' Γ SM.posTy) :
    (SM.mDeleteE K s pos).cost ≤ s.cost + pos.cost + 240 * K + 250 := by
  have hmax34 : max 3 4 = 4 := rfl
  have hmax31 : max 3 1 = 3 := rfl
  simp only [SM.mDeleteE, SM.mMk, SM.recPos,
    SM.posEq, SM.boolEq, SM.posSender, SM.posEpoch, SM.posIdx,
    SM.mSt, SM.mB, SM.mWin, SM.mEpoch, SM.mIdx,
    SM.mTL, SM.mTrans, SM.mChall, SM.mComp,
    SM.mMaxAcc, SM.mLeaks, SM.mCorrs,
    ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
    hmax34, hmax31, Nat.reduceAdd]
  omega

lemma mAcceptE_cost_le {O' : ReductionDsl.Ops S_sm} (K : ℕ) {Γ}
    (s : ReductionDsl.Expr O' Γ SM.mirrorTy)
    (p : ReductionDsl.Expr O' Γ .bool) (pos : ReductionDsl.Expr O' Γ SM.posTy) :
    (SM.mAcceptE K s p pos).cost ≤
      s.cost + p.cost + 2 * pos.cost + 240 * K + 800 := by
  have hdel := mDeleteE_cost_le (O' := O') K s pos
  simp only [SM.mAcceptE, SM.mMk, SM.pSet, SM.pGet,
    SM.maxAccSet, SM.maxAccGet, SM.maxN, SM.leN, SM.posEpoch, SM.posIdx,
    SM.mSt, SM.mB, SM.mWin, SM.mEpoch, SM.mIdx,
    SM.mTL, SM.mTrans, SM.mChall, SM.mComp,
    SM.mMaxAcc, SM.mLeaks, SM.mCorrs,
    ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, Nat.reduceAdd]
  omega

lemma mChallContainsE_cost_le {O' : ReductionDsl.Ops S_sm} (K : ℕ) {Γ}
    (s : ReductionDsl.Expr O' Γ SM.mirrorTy)
    (pos : ReductionDsl.Expr O' Γ SM.posTy) :
    (SM.mChallContainsE K s pos).cost ≤ s.cost + pos.cost + 70 * K + 50 := by
  have hmax34 : max 3 4 = 4 := rfl
  simp only [SM.mChallContainsE, SM.mChall, SM.posEq, SM.boolEq,
    SM.posSender, SM.posEpoch, SM.posIdx,
    ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, hmax34, Nat.reduceAdd]
  omega

lemma mAfterCorrE_cost_le {O' : ReductionDsl.Ops S_sm} (K : ℕ) {Γ}
    (s : ReductionDsl.Expr O' Γ SM.mirrorTy)
    (p : ReductionDsl.Expr O' Γ .bool) :
    (SM.mAfterCorrE K s p).cost ≤ s.cost + p.cost + 400 * K + 4000 := by
  have hmax34 : max 3 4 = 4 := rfl
  have hmax41 : max 4 1 = 4 := rfl
  simp only [SM.mAfterCorrE, SM.mMk, SM.mLeakE,
    SM.maxOptE, SM.maxN, SM.leN, SM.boolEq, SM.otherE, SM.pGet,
    SM.recPos, SM.posSender,
    SM.mSt, SM.mB, SM.mWin, SM.mEpoch, SM.mIdx,
    SM.mTL, SM.mTrans, SM.mChall, SM.mComp,
    SM.mMaxAcc, SM.mLeaks, SM.mCorrs,
    ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
    hmax34, hmax41, Nat.reduceAdd]
  omega

lemma thm1_simHandleC_cost_le (K qep : ℕ) (realEpoch : Option ℕ) :
    (SM.simHandleC (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K 3 qep realEpoch).cost ≤
      20 * ReductionDsl.bits qep + 5 * ReductionDsl.bits (realEpoch.getD 0) + 1800 * K + 17025 := by
  refine (compCost_le_costUB _).trans ?_
  cases realEpoch with
  | none =>
    have hb0 : ReductionDsl.bits 0 = 1 := rfl
    simp only [SM.simHandleC, SM.simTransmitC, SM.simChallC, SM.simSendC,
      SM.simDeliverC, SM.simInjectC, SM.simCorrC,
      SM.mEpMgmtE, SM.mSafeChE, SM.mLeakE, SM.mRecordE, SM.mInTransitE,
      SM.mDeleteE, SM.mAcceptE, SM.mChallContainsE, SM.mAfterCorrE,
      SM.mMk, SM.mSt, SM.mB, SM.mWin, SM.mEpoch, SM.mIdx, SM.mTL, SM.mTrans, SM.mChall,
      SM.mComp, SM.mMaxAcc, SM.mLeaks, SM.mCorrs, SM.recPos, SM.recCt,
      SM.isSomeE, SM.otherE, SM.pGet, SM.pSet, SM.sendsInE, SM.healedByE,
      SM.leN, SM.maxN, SM.maxOptE, SM.maxAccSet, SM.maxAccGet,
      SM.posEq, SM.posSender, SM.posEpoch, SM.posIdx, SM.boolEq,
      SM.smOps, SM.smIface, Option.getD_none, hb0,
      ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
      ReductionDsl.Expr.v3, ReductionDsl.Expr.v4,
      dsl_cost, Nat.reduceAdd]
    omega
  | some i =>
    simp only [SM.simHandleC, SM.simTransmitC, SM.simChallC, SM.simSendC,
      SM.simDeliverC, SM.simInjectC, SM.simCorrC,
      SM.mEpMgmtE, SM.mSafeChE, SM.mLeakE, SM.mRecordE, SM.mInTransitE,
      SM.mDeleteE, SM.mAcceptE, SM.mChallContainsE, SM.mAfterCorrE,
      SM.mMk, SM.mSt, SM.mB, SM.mWin, SM.mEpoch, SM.mIdx, SM.mTL, SM.mTrans, SM.mChall,
      SM.mComp, SM.mMaxAcc, SM.mLeaks, SM.mCorrs, SM.recPos, SM.recCt,
      SM.isSomeE, SM.otherE, SM.pGet, SM.pSet, SM.sendsInE, SM.healedByE,
      SM.leN, SM.maxN, SM.maxOptE, SM.maxAccSet, SM.maxAccGet,
      SM.posEq, SM.posSender, SM.posEpoch, SM.posIdx, SM.boolEq,
      SM.smOps, SM.smIface, Option.getD_some,
      ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
      ReductionDsl.Expr.v3, ReductionDsl.Expr.v4,
      dsl_cost, Nat.reduceAdd]
    omega

end Thm1CostHelpers

/-! ## Static cost bounds for `SM.Engine.implEC` -/

section EngineCostHelpers

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}

local notation "S_cka" => CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

private lemma optNatLit_cost_le {S' : ReductionDsl.Sig} {O' : ReductionDsl.Ops S'} {Γ'}
    (o : Option ℕ) :
    (SM.Engine.optNatLit (O' := O') (Γ' := Γ') o).cost ≤ ReductionDsl.bits (o.getD 0) + 3 := by
  cases o with
  | none =>
    have hb0 : ReductionDsl.bits 0 = 1 := rfl
    simp [SM.Engine.optNatLit, ReductionDsl.Expr.cost, hb0]
  | some n =>
    simp only [SM.Engine.optNatLit, ReductionDsl.Expr.cost, Option.getD_some]
    omega

lemma cGsEpoch_cost {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT)) :
    (SM.Engine.cGsEpoch s).cost = s.cost + 4 := rfl

lemma cGsIdx_cost {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT)) :
    (SM.Engine.cGsIdx s).cost = s.cost + 5 := rfl

lemma cGsSt_cost {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT)) :
    (SM.Engine.cGsSt s).cost = s.cost + 1 := rfl

lemma cRecPos_cost {O' : ReductionDsl.Ops S_cka} {Γ'}
    (r : ReductionDsl.Expr O' Γ' SM.Engine.cRecTy) :
    (SM.Engine.cRecPos r).cost = r.cost + 1 := rfl

lemma esG_cost {O' : ReductionDsl.Ops S_cka} {vpT hsT : ReductionDsl.Ty S_cka} {Γ'}
    (es : ReductionDsl.Expr O' Γ' (SM.Engine.esTy vpT hsT)) :
    (SM.Engine.esG es).cost = es.cost + 1 := rfl

lemma esH_cost {O' : ReductionDsl.Ops S_cka} {vpT hsT : ReductionDsl.Ty S_cka} {Γ'}
    (es : ReductionDsl.Expr O' Γ' (SM.Engine.esTy vpT hsT)) :
    (SM.Engine.esH es).cost = es.cost + 2 := rfl

lemma esAbort_cost {O' : ReductionDsl.Ops S_cka} {vpT hsT : ReductionDsl.Ty S_cka} {Γ'}
    (es : ReductionDsl.Expr O' Γ' (SM.Engine.esTy vpT hsT)) :
    (SM.Engine.esAbort es).cost = es.cost + 2 := rfl

private lemma cSafeChE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT)) (p : ReductionDsl.Expr O' Γ' .bool) :
    (SM.Engine.cSafeChE 3 s p).cost ≤ s.cost + p.cost + 80 := by
  have hb3 : ReductionDsl.bits 3 = 2 := rfl
  simp only [SM.Engine.cSafeChE, SM.healedByE, SM.leN, SM.pGet,
    SM.Engine.cGsTL, SM.Engine.cGsEpoch, ReductionDsl.Expr.cost, ReductionDsl.Expr.v0,
    ReductionDsl.Expr.v1, hb3, Nat.reduceAdd]
  omega

private lemma cSafeInjE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT)) :
    (SM.Engine.cSafeInjE 3 s).cost ≤ s.cost + 80 := by
  have hb3 : ReductionDsl.bits 3 = 2 := rfl
  simp only [SM.Engine.cSafeInjE, SM.healedByE, SM.leN, SM.minN,
    SM.Engine.cGsTL, SM.Engine.cGsEpoch, ReductionDsl.Expr.cost, ReductionDsl.Expr.v0,
    ReductionDsl.Expr.v1, hb3, Nat.reduceAdd]
  omega

private lemma cLeakE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT)) (l : ReductionDsl.Expr O' Γ' .nat) :
    (SM.Engine.cLeakE s l).cost ≤ s.cost + l.cost + 250 := by
  simp only [SM.Engine.cLeakE, SM.Engine.cGsMk, SM.maxOptE, SM.maxN, SM.leN,
    SM.Engine.cGsSt, SM.Engine.cGsB, SM.Engine.cGsWin, SM.Engine.cGsEpoch, SM.Engine.cGsIdx,
    SM.Engine.cGsTL, SM.Engine.cGsTrans, SM.Engine.cGsChall, SM.Engine.cGsComp,
    SM.Engine.cGsMaxAcc, SM.Engine.cGsLeaks, SM.Engine.cGsCorrs,
    ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, Nat.reduceAdd]
  omega

private lemma cEpMgmtE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (qep : ℕ) {Γ'} (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT))
    (p bad : ReductionDsl.Expr O' Γ' .bool) :
    (SM.Engine.cEpMgmtE 3 qep s p bad).cost ≤
      s.cost + p.cost + bad.cost + 5 * ReductionDsl.bits qep + 705 := by
  have hb0 : ReductionDsl.bits 0 = 1 := rfl
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  have hb2 : ReductionDsl.bits 2 = 2 := rfl
  let Γ0 : List (ReductionDsl.Ty S_cka) := .prod (SM.Engine.cGsTy vpT) (.prod .bool .bool) :: Γ'
  have hsc := cSafeChE_cost_le (O' := O') (vpT := vpT) (Γ' := Γ0) (.fst .v0) (.fst (.snd .v0))
  have hlk := cLeakE_cost_le (O' := O') (vpT := vpT) (Γ' := Γ0) (.fst .v0)
    (.add (SM.pGet (SM.Engine.cGsEpoch (.fst .v0)) (.fst (.snd .v0))) (.nat 1))
  simp only [pGet_cost, cGsEpoch_cost, v0_cost, ReductionDsl.Expr.cost, hb1, Nat.reduceAdd] at hsc hlk
  simp only [SM.Engine.cEpMgmtE, SM.Engine.cGsMk, SM.sendsInE, SM.pSet,
    SM.Engine.cGsSt, SM.Engine.cGsB, SM.Engine.cGsWin, SM.Engine.cGsIdx,
    SM.Engine.cGsTL, SM.Engine.cGsTrans, SM.Engine.cGsChall, SM.Engine.cGsComp,
    SM.Engine.cGsMaxAcc, SM.Engine.cGsLeaks, SM.Engine.cGsCorrs,
    pGet_cost, cGsEpoch_cost, v0_cost, v1_cost,
    ReductionDsl.Expr.cost, hb0, hb1, hb2, Nat.reduceAdd]
  omega

lemma cCompContainsE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L : ℕ) {Γ'} (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT))
    (pos : ReductionDsl.Expr O' Γ' SM.posTy) :
    (SM.Engine.cCompContainsE L s pos).cost ≤ s.cost + pos.cost + 200 := by
  simp only [SM.Engine.cCompContainsE, SM.Engine.cGsComp, SM.pGet,
    SM.posSender, SM.posEpoch, SM.posIdx,
    ReductionDsl.Expr.cost, v0_cost, Nat.reduceAdd]
  omega

private lemma cRecordE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L : ℕ) {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT))
    (p : ReductionDsl.Expr O' Γ' .bool) (st' : ReductionDsl.Expr O' Γ' vpT)
    (r : ReductionDsl.Expr O' Γ' SM.Engine.cRecTy) (isChall : ReductionDsl.Expr O' Γ' .bool) :
    (SM.Engine.cRecordE L 3 s p st' r isChall).cost ≤
      s.cost + p.cost + st'.cost + r.cost + isChall.cost + 700 := by
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod (SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.prod SM.Engine.cRecTy .bool))) :: Γ'
  have hsc := cSafeChE_cost_le (O' := O') (vpT := vpT) (Γ' := Γ0) (.fst .v0) (.fst (.snd .v0))
  simp only [v0_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hsc
  simp only [SM.Engine.cRecordE, SM.Engine.cGsMk, SM.pSet, SM.pGet,
    SM.Engine.cCompInsertE, SM.Engine.cCompSetE,
    SM.Engine.cRecPos, SM.posSender, SM.posEpoch, SM.posIdx,
    SM.Engine.cGsSt, SM.Engine.cGsB, SM.Engine.cGsWin, SM.Engine.cGsEpoch, SM.Engine.cGsIdx,
    SM.Engine.cGsTL, SM.Engine.cGsTrans, SM.Engine.cGsChall, SM.Engine.cGsComp,
    SM.Engine.cGsMaxAcc, SM.Engine.cGsLeaks, SM.Engine.cGsCorrs,
    ReductionDsl.Expr.cost, v0_cost, Nat.reduceAdd]
  omega

lemma cInTransitE_cost_le {vpT : ReductionDsl.Ty S_cka} (L : ℕ) {Γ'}
    (s : ReductionDsl.Expr OO_cka Γ' (SM.Engine.cGsTy vpT))
    (qParty : ReductionDsl.Expr OO_cka Γ' .bool)
    (c : ReductionDsl.Expr OO_cka Γ' (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Engine.cInTransitE L s qParty c).cost ≤ s.cost + qParty.cost + c.cost + 65 * L + 60 := by
  have hmax34 : max 3 4 = 4 := rfl
  have hmax11 : max 1 1 = 1 := rfl
  have hmax14 : max 1 4 = 4 := rfl
  have hmax47 : max 4 7 = 7 := rfl
  simp only [SM.Engine.cInTransitE, SM.Engine.cGsTrans, SM.Engine.cRecPos, SM.Engine.cRecCt,
    SM.Engine.hdrCtEqE, SM.Engine.optTEqE, SM.posSender, SM.boolEq,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, CKA.ckaOps,
    hmax34, hmax11, hmax14, hmax47, Nat.reduceAdd]
  omega

private lemma cDeleteE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L : ℕ) {Γ'} (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT))
    (pos : ReductionDsl.Expr O' Γ' SM.posTy) :
    (SM.Engine.cDeleteE L s pos).cost ≤ s.cost + pos.cost + 240 * L + 650 := by
  have hmax34 : max 3 4 = 4 := rfl
  have hmax31 : max 3 1 = 3 := rfl
  simp only [SM.Engine.cDeleteE, SM.Engine.cGsMk, SM.Engine.cRecPos,
    SM.Engine.cCompDeleteE, SM.Engine.cCompSetE, SM.pSet, SM.pGet,
    SM.posEq, SM.boolEq, SM.posSender, SM.posEpoch, SM.posIdx,
    SM.Engine.cGsSt, SM.Engine.cGsB, SM.Engine.cGsWin, SM.Engine.cGsEpoch, SM.Engine.cGsIdx,
    SM.Engine.cGsTL, SM.Engine.cGsTrans, SM.Engine.cGsChall, SM.Engine.cGsComp,
    SM.Engine.cGsMaxAcc, SM.Engine.cGsLeaks, SM.Engine.cGsCorrs,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost,
    hmax34, hmax31, Nat.reduceAdd]
  omega

private lemma cAcceptE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L : ℕ) {Γ'} (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT))
    (p : ReductionDsl.Expr O' Γ' .bool) (st' : ReductionDsl.Expr O' Γ' vpT)
    (pos : ReductionDsl.Expr O' Γ' SM.posTy) :
    (SM.Engine.cAcceptE L s p st' pos).cost ≤
      s.cost + p.cost + st'.cost + 2 * pos.cost + 240 * L + 1200 := by
  have hdel := cDeleteE_cost_le (O' := O') (vpT := vpT) L s pos
  simp only [SM.Engine.cAcceptE, SM.Engine.cGsMk, SM.pSet, SM.pGet,
    SM.maxAccSet, SM.maxAccGet, SM.maxN, SM.leN, SM.posEpoch, SM.posIdx,
    SM.Engine.cGsSt, SM.Engine.cGsB, SM.Engine.cGsWin, SM.Engine.cGsEpoch, SM.Engine.cGsIdx,
    SM.Engine.cGsTL, SM.Engine.cGsTrans, SM.Engine.cGsChall, SM.Engine.cGsComp,
    SM.Engine.cGsMaxAcc, SM.Engine.cGsLeaks, SM.Engine.cGsCorrs,
    ReductionDsl.Expr.cost, v0_cost, Nat.reduceAdd]
  omega

private lemma cChallContainsE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L : ℕ) {Γ'} (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT))
    (pos : ReductionDsl.Expr O' Γ' SM.posTy) :
    (SM.Engine.cChallContainsE L s pos).cost ≤ s.cost + pos.cost + 70 * L + 50 := by
  have hmax34 : max 3 4 = 4 := rfl
  simp only [SM.Engine.cChallContainsE, SM.Engine.cGsChall, SM.posEq, SM.boolEq,
    SM.posSender, SM.posEpoch, SM.posIdx,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, hmax34, Nat.reduceAdd]
  omega

private lemma cMustBeCorrectE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L maxSkip : ℕ) {Γ'} (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT))
    (p : ReductionDsl.Expr O' Γ' .bool) (r : ReductionDsl.Expr O' Γ' SM.Engine.cRecTy) :
    (SM.Engine.cMustBeCorrectE L maxSkip s p r).cost ≤
      s.cost + p.cost + r.cost + (maxSkip + 1) + 400 := by
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  have hms := ReductionDsl.bits_le_succ maxSkip
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod (SM.Engine.cGsTy vpT) (.prod .bool SM.Engine.cRecTy) :: Γ'
  have hcc := cCompContainsE_cost_le (O' := O') (vpT := vpT) L (Γ' := Γ0)
    (.fst .v0) (SM.Engine.cRecPos (.snd (.snd .v0)))
  simp only [cRecPos_cost, v0_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hcc
  simp only [SM.Engine.cMustBeCorrectE, SM.leN, SM.maxAccGet, SM.pGet,
    SM.Engine.cGsMaxAcc, cRecPos_cost, SM.posIdx, SM.posEpoch,
    ReductionDsl.Expr.cost, v0_cost, hb1, Nat.reduceAdd]
  omega

lemma cTrivialE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L : ℕ) {Γ'} (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT))
    (pos : ReductionDsl.Expr O' Γ' SM.posTy) :
    (SM.Engine.cTrivialE L 3 s pos).cost ≤ s.cost + pos.cost + 150 * L + 350 := by
  have hb3 : ReductionDsl.bits 3 = 2 := rfl
  have hmax34 : max 3 4 = 4 := rfl
  let Γ0 : List (ReductionDsl.Ty S_cka) := .prod (SM.Engine.cGsTy vpT) SM.posTy :: Γ'
  have hcc := cCompContainsE_cost_le (O' := O') (vpT := vpT) L (Γ' := Γ0) (.fst .v0) (.snd .v0)
  simp only [v0_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hcc
  simp only [SM.Engine.cTrivialE, SM.orE, SM.healedByE, SM.leN,
    SM.Engine.cGsTrans, SM.Engine.cGsTL, SM.Engine.cRecPos, SM.posEq, SM.boolEq,
    SM.posSender, SM.posEpoch, SM.posIdx,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, hb3, hmax34, Nat.reduceAdd]
  omega

private lemma cCorrAllowedE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L : ℕ) {Γ'} (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT))
    (p : ReductionDsl.Expr O' Γ' .bool) :
    (SM.Engine.cCorrAllowedE L s p).cost ≤
      s.cost + p.cost + 300 * L + 150 := by
  have hmax34 : max 3 4 = 4 := rfl
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    SM.Engine.cRecTy :: .prod (SM.Engine.cGsTy vpT) .bool :: Γ'
  have hcc := cCompContainsE_cost_le (O' := O') (vpT := vpT) L (Γ' := Γ0)
    (.fst .v1) (SM.Engine.cRecPos .v0)
  simp only [cRecPos_cost, v0_cost, v1_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hcc
  have hbody : 8 + ((SM.Engine.cCompContainsE L (O' := O') (vpT := vpT) (Γ' := Γ0)
      (.fst .v1) (SM.Engine.cRecPos .v0)).cost + 1) + 1 + 1 ≤ 215 := by omega
  have hmul := Nat.mul_le_mul_left L hbody
  simp only [SM.Engine.cCorrAllowedE, SM.Engine.cGsChall, SM.Engine.cGsTrans,
    SM.posSender, SM.boolEq, SM.otherE,
    cRecPos_cost, v0_cost, v1_cost, ReductionDsl.Expr.cost, hmax34, Nat.reduceAdd]
  omega

private lemma cAfterCorrE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L : ℕ) {Γ'} (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT))
    (p : ReductionDsl.Expr O' Γ' .bool) :
    (SM.Engine.cAfterCorrE L s p).cost ≤ s.cost + p.cost + 5500 * L + 4000 := by
  have hmax22 : max 2 2 = 2 := rfl
  have hmax214 : max 2 14 = 14 := rfl
  have hmax33 : max 3 3 = 3 := rfl
  have hmax34 : max 3 4 = 4 := rfl
  have hmax77 : max 7 7 = 7 := rfl
  have hmax393 : max 393 1 = 393 := rfl
  simp only [SM.Engine.cAfterCorrE, SM.Engine.cGsMk, SM.Engine.cLeakE,
    SM.Engine.cCompInsertE, SM.Engine.cCompSetE, SM.pSet, SM.pGet,
    SM.maxOptE, SM.maxN, SM.leN, SM.boolEq, SM.otherE,
    SM.Engine.cRecPos, SM.posSender, SM.posEpoch, SM.posIdx,
    SM.Engine.cGsSt, SM.Engine.cGsB, SM.Engine.cGsWin, SM.Engine.cGsEpoch, SM.Engine.cGsIdx,
    SM.Engine.cGsTL, SM.Engine.cGsTrans, SM.Engine.cGsChall, SM.Engine.cGsComp,
    SM.Engine.cGsMaxAcc, SM.Engine.cGsLeaks, SM.Engine.cGsCorrs,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost,
    hmax22, hmax214, hmax33, hmax34, hmax77, hmax393, Nat.reduceAdd]
  omega

private lemma cCanonE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L : ℕ) {Γ'} (tStar : ReductionDsl.Expr O' Γ' .nat)
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT)) :
    (SM.Engine.cCanonE L tStar s).cost ≤ tStar.cost + s.cost + 50 * L + 50 := by
  have hmax22 : max 2 2 = 2 := rfl
  have hmax214 : max 2 14 = 14 := rfl
  have hmax161 : max 16 1 = 16 := rfl
  simp only [SM.Engine.cCanonE, SM.Engine.cGsLeaks, SM.maxN, SM.leN,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost,
    hmax22, hmax214, hmax161, Nat.reduceAdd]
  omega

private lemma cAuthOKE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L : ℕ) {Γ'} (tLStar : ReductionDsl.Expr O' Γ' (.opt .nat))
    (tStar : ReductionDsl.Expr O' Γ' .nat)
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT)) :
    (SM.Engine.cAuthOKE L 3 tLStar tStar s).cost ≤
      tLStar.cost + tStar.cost + s.cost + 100 * L + 200 := by
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  have hb2 : ReductionDsl.bits 2 = 2 := rfl
  have hb3 : ReductionDsl.bits 3 = 2 := rfl
  have hmax14 : max 1 4 = 4 := rfl
  have hmax78 : max 7 8 = 8 := rfl
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod (.opt .nat) (.prod .nat (SM.Engine.cGsTy vpT)) :: Γ'
  have hcan := cCanonE_cost_le (O' := O') (vpT := vpT) L (Γ' := Γ0)
    (.fst (.snd .v0)) (.snd (.snd .v0))
  simp only [v0_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hcan
  simp only [SM.Engine.cAuthOKE, SM.validGuessE, SM.healedByE, SM.optNatEqE,
    SM.ltOptE, SM.leN, SM.boolEq, SM.receiverOfE,
    SM.Engine.cGsLeaks, SM.Engine.cGsCorrs,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, hb1, hb2, hb3, hmax14, hmax78, Nat.reduceAdd]
  omega

private lemma leakDoomE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L : ℕ) (π : SM.Engine.Policy) {Γ'}
    (g g' : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT)) :
    (SM.Engine.leakDoomE L π g g').cost ≤
      g.cost + g'.cost +
        L * (ReductionDsl.bits (π.tL.getD 0) + 2 * ReductionDsl.bits π.tStar + 40) +
        2 * ReductionDsl.bits π.tStar + 105 := by
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod (SM.Engine.cGsTy vpT) (SM.Engine.cGsTy vpT) :: Γ'
  have hopt := optNatLit_cost_le (O' := O') (Γ' := .nat :: Γ0) π.tL
  have hmax14 : max 1 4 = 4 := rfl
  have hmax33 : max 3 3 = 3 := rfl
  simp only [SM.Engine.leakDoomE, SM.orE, SM.ltOptE, SM.leN, SM.pGet,
    SM.Engine.cGsLeaks, SM.Engine.cGsEpoch,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, hmax14, hmax33, Nat.reduceAdd]
  have hbody1 :
      (SM.Engine.optNatLit (O' := O') (Γ' := .nat :: Γ0) π.tL).cost + 1 + 1 + 7 + 1 +
        (1 + ReductionDsl.bits π.tStar + 1) + 1 + 1 ≤
        ReductionDsl.bits (π.tL.getD 0) + ReductionDsl.bits π.tStar + 20 := by omega
  have hbody2 : 1 + ReductionDsl.bits π.tStar + 1 + 1 + 1 ≤
      ReductionDsl.bits π.tStar + 10 := by omega
  have hmul1 := Nat.mul_le_mul_left L hbody1
  have hmul2 := Nat.mul_le_mul_left L hbody2
  have hmul3 :
      L * (ReductionDsl.bits (π.tL.getD 0) + ReductionDsl.bits π.tStar + 20) +
        L * (ReductionDsl.bits π.tStar + 10) ≤
      L * (ReductionDsl.bits (π.tL.getD 0) + 2 * ReductionDsl.bits π.tStar + 40) := by
    have hring :
        L * (ReductionDsl.bits (π.tL.getD 0) + ReductionDsl.bits π.tStar + 20) +
          L * (ReductionDsl.bits π.tStar + 10) =
        L * (ReductionDsl.bits (π.tL.getD 0) + 2 * ReductionDsl.bits π.tStar + 30) := by ring
    rw [hring]
    exact Nat.mul_le_mul_left L (by omega)
  omega

private lemma corrDoomE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (π : SM.Engine.Policy) {Γ'}
    (g : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT))
    (p : ReductionDsl.Expr O' Γ' .bool) :
    (SM.Engine.corrDoomE π g p).cost ≤
      g.cost + p.cost + (ReductionDsl.bits (π.tL.getD 0) + 3) +
        2 * ReductionDsl.bits π.tStar + 105 := by
  have hopt := optNatLit_cost_le (O' := O') (Γ' := .prod (SM.Engine.cGsTy vpT) .bool :: Γ') π.tL
  cases hAuth : π.auth <;>
  · simp only [SM.Engine.corrDoomE, hAuth, ↓reduceIte, Bool.false_eq_true,
      SM.boolEq, SM.ltOptE, SM.leN, SM.maxN, pGet_cost, cGsEpoch_cost,
      ReductionDsl.Expr.cost, v0_cost, v1_cost, Nat.reduceAdd]
    omega

lemma authOutE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT hsT : ReductionDsl.Ty S_cka}
    (L : ℕ) (π : SM.Engine.Policy) {Γ'}
    (es : ReductionDsl.Expr O' Γ' (SM.Engine.esTy vpT hsT)) :
    (SM.Engine.authOutE L 3 π es).cost ≤
      es.cost + (ReductionDsl.bits (π.tL.getD 0) + 3) +
        ReductionDsl.bits π.tStar + 100 * L + 255 := by
  let Γ0 : List (ReductionDsl.Ty S_cka) := SM.Engine.esTy vpT hsT :: Γ'
  have hopt := optNatLit_cost_le (O' := O') (Γ' := Γ0) π.tL
  have hauth := cAuthOKE_cost_le (O' := O') (vpT := vpT) L (Γ' := Γ0)
    (SM.Engine.optNatLit π.tL) (.nat π.tStar) (SM.Engine.esG .v0)
  simp only [esG_cost, v0_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hauth
  simp only [SM.Engine.authOutE, SM.Engine.esAbort, SM.Engine.cGsWin, esG_cost,
    ReductionDsl.Expr.cost, v0_cost, Nat.reduceAdd]
  omega

lemma privValidE_cost_le {O' : ReductionDsl.Ops S_cka} {vpT hsT : ReductionDsl.Ty S_cka}
    (L : ℕ) (π : SM.Engine.Policy) {Γ'}
    (es : ReductionDsl.Expr O' Γ' (SM.Engine.esTy vpT hsT)) :
    (SM.Engine.privValidE L 3 π es).cost ≤
      es.cost + 2 * (ReductionDsl.bits (π.tL.getD 0) + 3) +
        2 * ReductionDsl.bits π.tStar + 50 * L + 205 := by
  have hb3 : ReductionDsl.bits 3 = 2 := rfl
  let Γ0 : List (ReductionDsl.Ty S_cka) := SM.Engine.esTy vpT hsT :: Γ'
  have hopt := optNatLit_cost_le (O' := O') (Γ' := Γ0) π.tL
  have hcan := cCanonE_cost_le (O' := O') (vpT := vpT) L (Γ' := Γ0)
    (.nat π.tStar) (SM.Engine.esG .v0)
  simp only [esG_cost, v0_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hcan
  simp only [SM.Engine.privValidE, SM.validGuessE, SM.healedByE, SM.optNatEqE,
    SM.leN, SM.Engine.esAbort,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, hb3, Nat.reduceAdd]
  omega

lemma privOutC_cost_le {O' : ReductionDsl.Ops S_cka} {ι : Type} {TSpec : OracleSpec ι}
    {I' : ReductionDsl.Iface S_cka TSpec} {vpT hsT : ReductionDsl.Ty S_cka}
    (L : ℕ) (π : SM.Engine.Policy)
    (drawBit : ∀ {Γ''}, ReductionDsl.Comp O' I' Γ'' .bool)
    {Γ'} (b b' : ReductionDsl.Expr O' Γ' .bool)
    (es : ReductionDsl.Expr O' Γ' (SM.Engine.esTy vpT hsT)) :
    (SM.Engine.privOutC L 3 π drawBit b b' es).cost ≤
      es.cost + 3 * b.cost + 3 * b'.cost + (drawBit (Γ'' := Γ')).cost +
        2 * (ReductionDsl.bits (π.tL.getD 0) + 3) + 2 * ReductionDsl.bits π.tStar + 50 * L + 225 := by
  have hpv := privValidE_cost_le (O' := O') (vpT := vpT) (hsT := hsT) L π es
  simp only [SM.Engine.privOutC, SM.boolEq, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]
  omega

private lemma vpId_cost {O' : ReductionDsl.Ops S_cka} {γvT svT ssvT vrT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.vpTy γvT svT ssvT vrT)) :
    (SM.Engine.vpId s).cost = s.cost + 1 := rfl

private lemma vpRoot_cost {O' : ReductionDsl.Ops S_cka} {γvT svT ssvT vrT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.vpTy γvT svT ssvT vrT)) :
    (SM.Engine.vpRoot s).cost = s.cost + 2 := rfl

private lemma vpVS_cost {O' : ReductionDsl.Ops S_cka} {γvT svT ssvT vrT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.vpTy γvT svT ssvT vrT)) :
    (SM.Engine.vpVS s).cost = s.cost + 3 := rfl

private lemma vpVR_cost {O' : ReductionDsl.Ops S_cka} {γvT svT ssvT vrT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.vpTy γvT svT ssvT vrT)) :
    (SM.Engine.vpVR s).cost = s.cost + 4 := rfl

private lemma vpΓ_cost {O' : ReductionDsl.Ops S_cka} {γvT svT ssvT vrT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.vpTy γvT svT ssvT vrT)) :
    (SM.Engine.vpΓ s).cost = s.cost + 5 := rfl

private lemma vpTcur_cost {O' : ReductionDsl.Ops S_cka} {γvT svT ssvT vrT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.vpTy γvT svT ssvT vrT)) :
    (SM.Engine.vpTcur s).cost = s.cost + 6 := rfl

private lemma vpTcurNat_cost {O' : ReductionDsl.Ops S_cka}
    {γvT svT ssvT vrT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.vpTy γvT svT ssvT vrT)) :
    (SM.Engine.vpTcurNat s).cost = s.cost + 6 := rfl

private lemma vpMk_cost {O' : ReductionDsl.Ops S_cka} {γvT svT ssvT vrT : ReductionDsl.Ty S_cka} {Γ'}
    (id : ReductionDsl.Expr O' Γ' .bool) (root : ReductionDsl.Expr O' Γ' svT)
    (vS : ReductionDsl.Expr O' Γ' (.opt ssvT)) (vR : ReductionDsl.Expr O' Γ' vrT)
    (γ : ReductionDsl.Expr O' Γ' γvT) (curCkaMsg : ReductionDsl.Expr O' Γ' (.opt (.base .t)))
    (tcur : ReductionDsl.Expr O' Γ' .nat) :
    (SM.Engine.vpMk id root vS vR γ curCkaMsg tcur).cost =
      id.cost + (root.cost + (vS.cost + (vR.cost +
        (γ.cost + (curCkaMsg.cost + tcur.cost + 1) + 1) + 1) + 1) + 1) + 1 := rfl

private lemma vpSetVS_cost {O' : ReductionDsl.Ops S_cka} {γvT svT ssvT vrT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.vpTy γvT svT ssvT vrT))
    (vS : ReductionDsl.Expr O' Γ' (.opt ssvT)) :
    (SM.Engine.vpSetVS s vS).cost = (s.cost + vS.cost + 1) + 44 + 1 := rfl

private lemma vpSetVR_cost {O' : ReductionDsl.Ops S_cka} {γvT svT ssvT vrT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.vpTy γvT svT ssvT vrT))
    (vR : ReductionDsl.Expr O' Γ' vrT) :
    (SM.Engine.vpSetVR s vR).cost = (s.cost + vR.cost + 1) + 43 + 1 := rfl

lemma esSetG_cost {O' : ReductionDsl.Ops S_cka} {vpT hsT : ReductionDsl.Ty S_cka} {Γ'}
    (es : ReductionDsl.Expr O' Γ' (SM.Engine.esTy vpT hsT))
    (g : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT)) :
    (SM.Engine.esSetG es g).cost = (es.cost + g.cost + 1) + 12 + 1 := rfl

lemma esSetH_cost {O' : ReductionDsl.Ops S_cka} {vpT hsT : ReductionDsl.Ty S_cka} {Γ'}
    (es : ReductionDsl.Expr O' Γ' (SM.Engine.esTy vpT hsT))
    (h : ReductionDsl.Expr O' Γ' hsT) :
    (SM.Engine.esSetH es h).cost = (es.cost + h.cost + 1) + 11 + 1 := rfl

lemma esSetAbort_cost {O' : ReductionDsl.Ops S_cka} {vpT hsT : ReductionDsl.Ty S_cka} {Γ'}
    (es : ReductionDsl.Expr O' Γ' (SM.Engine.esTy vpT hsT))
    (abort : ReductionDsl.Expr O' Γ' .bool) :
    (SM.Engine.esSetAbort es abort).cost = (es.cost + abort.cost + 1) + 11 + 1 := rfl

lemma cGsSetWin_cost {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT)) (w : ReductionDsl.Expr O' Γ' .bool) :
    (SM.Engine.cGsSetWin s w).cost = s.cost + w.cost + 111 := by
  simp only [SM.Engine.cGsSetWin, SM.Engine.cGsMk,
    SM.Engine.cGsSt, SM.Engine.cGsB, SM.Engine.cGsEpoch, SM.Engine.cGsIdx,
    SM.Engine.cGsTL, SM.Engine.cGsTrans, SM.Engine.cGsChall, SM.Engine.cGsComp,
    SM.Engine.cGsMaxAcc, SM.Engine.cGsLeaks, SM.Engine.cGsCorrs,
    ReductionDsl.Expr.cost, v0_cost, Nat.reduceAdd]

lemma cGsSetStP_cost {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT))
    (p : ReductionDsl.Expr O' Γ' .bool) (st' : ReductionDsl.Expr O' Γ' vpT) :
    (SM.Engine.cGsSetStP s p st').cost = s.cost + p.cost + st'.cost + 135 := by
  have hmax77 : max 7 7 = 7 := rfl
  simp only [SM.Engine.cGsSetStP, SM.Engine.cGsMk, SM.pSet,
    SM.Engine.cGsSt, SM.Engine.cGsB, SM.Engine.cGsWin, SM.Engine.cGsEpoch, SM.Engine.cGsIdx,
    SM.Engine.cGsTL, SM.Engine.cGsTrans, SM.Engine.cGsChall, SM.Engine.cGsComp,
    SM.Engine.cGsMaxAcc, SM.Engine.cGsLeaks, SM.Engine.cGsCorrs,
    ReductionDsl.Expr.cost, v0_cost, hmax77, Nat.reduceAdd]
  omega

private lemma realPartyE_cost_le {O' : ReductionDsl.Ops S_cka}
    {γvT svT ssvT vrT : ReductionDsl.Ty S_cka} {Γ'}
    (vp : ReductionDsl.Expr O' Γ' (SM.Engine.vpTy γvT svT ssvT vrT))
    (γ : ReductionDsl.Expr O' Γ' (.base .γ)) (σ : ReductionDsl.Expr O' Γ' (.base .sig))
    (vS : ReductionDsl.Expr O' Γ' (.opt (.base .ss)))
    (vR : ReductionDsl.Expr O' Γ' (.tbl (.opt (.base .rs)))) :
    (SM.Engine.realPartyE vp γ σ vS vR).cost ≤
      vp.cost + γ.cost + σ.cost + vS.cost + vR.cost + 60 := by
  simp only [SM.Engine.realPartyE, vpMk_cost, vpId_cost, vpTcur_cost, vpTcurNat_cost,
    ReductionDsl.Expr.cost, v0_cost, Nat.reduceAdd]
  omega

private lemma modeCfgEC_challOKE_cost_le {O' : ReductionDsl.Ops S_cka} (mo : SM.Construction.Mode)
    {Γ'} (e : ReductionDsl.Expr O' Γ' .nat) :
    ((SM.Engine.modeCfgEC O' mo).challOKE e).cost ≤ e.cost + ReductionDsl.bits mo.tStar + 6 := by
  cases h : mo.auth <;>
  · simp only [SM.Engine.modeCfgEC, h, ↓reduceIte, Bool.false_eq_true, ReductionDsl.Expr.cost]
    omega

lemma modeCfgEC_injectFullE_cost_le {O' : ReductionDsl.Ops S_cka} (mo : SM.Construction.Mode)
    {Γ'} (e : ReductionDsl.Expr O' Γ' .nat) :
    ((SM.Engine.modeCfgEC O' mo).injectFullE e).cost ≤ e.cost + ReductionDsl.bits mo.tStar + 6 := by
  cases h : mo.auth <;>
  · simp only [SM.Engine.modeCfgEC, h, ↓reduceIte, Bool.false_eq_true, ReductionDsl.Expr.cost]
    omega

structure HooksCostBounded {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H : ℕ) : Prop where
  startSend_le : ∀ {Γ'} (h : ReductionDsl.Expr OO_cka Γ' hsT)
      (ctx : ReductionDsl.Expr OO_cka Γ'
        (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : ReductionDsl.Expr OO_cka Γ' .bool)
      (t : ReductionDsl.Expr OO_cka Γ' .nat)
      (γv : ReductionDsl.Expr OO_cka Γ' γvT)
      (σ : ReductionDsl.Expr OO_cka Γ' svT)
      (r : ReductionDsl.Expr OO_cka Γ' (.opt (.base .ccoins))),
      (hk.startSend h ctx p t γv σ r).cost ≤
        2 * (h.cost + ctx.cost + p.cost + t.cost + γv.cost + σ.cost + r.cost) + H
  startRecv_le : ∀ {Γ'} (h : ReductionDsl.Expr OO_cka Γ' hsT)
      (ctx : ReductionDsl.Expr OO_cka Γ'
        (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : ReductionDsl.Expr OO_cka Γ' .bool)
      (t : ReductionDsl.Expr OO_cka Γ' .nat)
      (γv : ReductionDsl.Expr OO_cka Γ' γvT)
      (σ : ReductionDsl.Expr OO_cka Γ' svT)
      (tn : ReductionDsl.Expr OO_cka Γ' (.base .t)),
      (hk.startRecv h ctx p t γv σ tn).cost ≤
        2 * (h.cost + ctx.cost + p.cost + t.cost + γv.cost + σ.cost + tn.cost) + H
  fsSend_le : ∀ {Γ'} (h : ReductionDsl.Expr OO_cka Γ' hsT)
      (ctx : ReductionDsl.Expr OO_cka Γ'
        (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : ReductionDsl.Expr OO_cka Γ' .bool)
      (t : ReductionDsl.Expr OO_cka Γ' .nat)
      (ss : ReductionDsl.Expr OO_cka Γ' ssvT)
      (hdr : ReductionDsl.Expr OO_cka Γ' (CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
      (m : ReductionDsl.Expr OO_cka Γ' (.base .msg))
      (pair : ReductionDsl.Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg)))),
      (hk.fsSend h ctx p t ss hdr m pair).cost ≤
        2 * (h.cost + ctx.cost + p.cost + t.cost + ss.cost + hdr.cost + m.cost + pair.cost) + H
  fsRecv_le : ∀ {Γ'} (h : ReductionDsl.Expr OO_cka Γ' hsT)
      (ctx : ReductionDsl.Expr OO_cka Γ'
        (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : ReductionDsl.Expr OO_cka Γ' .bool)
      (t : ReductionDsl.Expr OO_cka Γ' .nat)
      (rs : ReductionDsl.Expr OO_cka Γ' rsvT)
      (hdr : ReductionDsl.Expr OO_cka Γ' (CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
      (e : ReductionDsl.Expr OO_cka Γ' (.base .ct))
      (rec_ : ReductionDsl.Expr OO_cka Γ' (.opt SM.Engine.cRecTy)),
      (hk.fsRecv h ctx p t rs hdr e rec_).cost ≤
        2 * (h.cost + ctx.cost + p.cost + t.cost + rs.cost + hdr.cost + e.cost + rec_.cost) + H
  commit_le : ∀ {Γ'} (h : ReductionDsl.Expr OO_cka Γ' hsT)
      (ctx : ReductionDsl.Expr OO_cka Γ'
        (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : ReductionDsl.Expr OO_cka Γ' .bool)
      (old new : ReductionDsl.Expr OO_cka Γ'
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)),
      (hk.commit h ctx p old new).cost ≤
        2 * (h.cost + ctx.cost + p.cost + old.cost + new.cost) + H
  reveal_le : ∀ {Γ'} (h : ReductionDsl.Expr OO_cka Γ' hsT)
      (ctx : ReductionDsl.Expr OO_cka Γ'
        (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : ReductionDsl.Expr OO_cka Γ' .bool)
      (vp : ReductionDsl.Expr OO_cka Γ'
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)),
      (hk.reveal h ctx p vp).cost ≤
        2 * (h.cost + ctx.cost + p.cost + vp.cost) + H

private lemma vSendStep1C_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H : ℕ)
    (hhk : HooksCostBounded hk H)
    {Γ'} (h : ReductionDsl.Expr OO_cka Γ' hsT)
    (ctx : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : ReductionDsl.Expr OO_cka Γ' .bool)
    (s : ReductionDsl.Expr OO_cka Γ'
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (r : ReductionDsl.Expr OO_cka Γ' (.opt (.base .ccoins))) :
    (SM.Engine.vSendStep1C hk h ctx p s r).cost ≤
      h.cost + ctx.cost + p.cost + s.cost + r.cost + H + 250 := by
  have hb0 : ReductionDsl.bits 0 = 1 := rfl
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  have hb2 : ReductionDsl.bits 2 = 2 := rfl
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod hsT (.prod (SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.opt (.base .ccoins))))) :: Γ'
  have hss := hhk.startSend_le (Γ' := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.add (SM.Engine.vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
    (SM.Engine.vpΓ (.fst (.snd (.snd (.snd .v0)))))
    (SM.Engine.vpRoot (.fst (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd .v0))))
  simp only [vpTcurNat_cost, vpΓ_cost, vpRoot_cost, v0_cost, ReductionDsl.Expr.cost,
    hb1, Nat.reduceAdd] at hss
  simp only [SM.Engine.vSendStep1C, SM.sendsInE, vpMk_cost, vpId_cost, vpVR_cost, vpTcurNat_cost,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost,
    hb0, hb1, hb2, Nat.reduceAdd]
  omega

private lemma vSendC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H : ℕ)
    (hhk : HooksCostBounded hk H)
    {Γ'} (h : ReductionDsl.Expr OO_cka Γ' hsT)
    (ctx : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : ReductionDsl.Expr OO_cka Γ' .bool)
    (s : ReductionDsl.Expr OO_cka Γ'
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (m : ReductionDsl.Expr OO_cka Γ' (.base .msg))
    (pair : ReductionDsl.Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (r : ReductionDsl.Expr OO_cka Γ' (.opt (.base .ccoins))) :
    (SM.Engine.vSendC hk h ctx p s m pair r).cost ≤
      h.cost + ctx.cost + p.cost + s.cost + m.cost + pair.cost + r.cost + 2 * H + 600 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod hsT (.prod (SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.prod (.base .msg)
      (.prod (.opt (.prod (.base .msg) (.base .msg))) (.opt (.base .ccoins))))))) :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) :=
    ssvT :: vpT :: .prod (.opt vpT) hsT :: Γ0
  have hs1 := vSendStep1C_cost_le hk H hhk (Γ' := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  have hfs := hhk.fsSend_le (Γ' := Γ1)
    (.snd .v2) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (SM.Engine.vpTcurNat .v1) .v0
    (.pair (SM.Engine.vpTcurNat .v1) (SM.Engine.vpTcur .v1))
    (.fst (.snd (.snd (.snd (.snd .v3)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
  simp only [vpTcurNat_cost, vpTcur_cost, v0_cost, v1_cost, v2_cost, v3_cost,
    ReductionDsl.Expr.cost, Nat.reduceAdd] at hs1 hfs
  simp only [SM.Engine.vSendC, vpVS_cost, vpTcurNat_cost, vpTcur_cost, vpSetVS_cost,
    CKA.ckaOps, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v3_cost, Nat.reduceAdd]
  omega

private lemma vRecvStep1C_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H : ℕ)
    (hhk : HooksCostBounded hk H)
    {Γ'} (h : ReductionDsl.Expr OO_cka Γ' hsT)
    (ctx : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : ReductionDsl.Expr OO_cka Γ' .bool)
    (s : ReductionDsl.Expr OO_cka Γ'
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (c : ReductionDsl.Expr OO_cka Γ' (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Engine.vRecvStep1C hk h ctx p s c).cost ≤
      h.cost + ctx.cost + p.cost + s.cost + c.cost + H + 450 := by
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod hsT (.prod (SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT hdrCtT))) :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) := .base .t :: Γ0
  have hsr := hhk.startRecv_le (Γ' := Γ1)
    (.fst .v1) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
    (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
    (SM.Engine.vpΓ (.fst (.snd (.snd (.snd .v1)))))
    (SM.Engine.vpRoot (.fst (.snd (.snd (.snd .v1)))))
    .v0
  simp only [vpΓ_cost, vpRoot_cost, v0_cost, v1_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hsr
  simp only [SM.Engine.vRecvStep1C, vpMk_cost, vpId_cost, vpVS_cost, vpVR_cost, vpTcur_cost,
    vpTcurNat_cost, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, v4_cost, hb1, Nat.reduceAdd]
  omega

lemma cGsB_cost {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka} {Γ'}
    (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT)) :
    (SM.Engine.cGsB s).cost = s.cost + 2 := rfl

private lemma modeCfgEC_challMsgE_cost {O' : ReductionDsl.Ops S_cka} (mo : SM.Construction.Mode)
    {Γ'} (ep : ReductionDsl.Expr O' Γ' .nat) (b : ReductionDsl.Expr O' Γ' .bool)
    (m0 m1 : ReductionDsl.Expr O' Γ' (.base .msg)) :
    ((SM.Engine.modeCfgEC O' mo).challMsgE ep b m0 m1).cost =
      b.cost + max m1.cost m0.cost + 1 := rfl

lemma vRecvC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H : ℕ)
    (hhk : HooksCostBounded hk H)
    {Γ'} (h : ReductionDsl.Expr OO_cka Γ' hsT)
    (ctx : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : ReductionDsl.Expr OO_cka Γ' .bool)
    (s : ReductionDsl.Expr OO_cka Γ'
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (c : ReductionDsl.Expr OO_cka Γ' (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))
    (rec_ : ReductionDsl.Expr OO_cka Γ' (.opt SM.Engine.cRecTy)) :
    (SM.Engine.vRecvC hk h ctx p s c rec_).cost ≤
      h.cost + ctx.cost + p.cost + s.cost + c.cost + rec_.cost + 2 * H + 1000 := by
  have hb0 : ReductionDsl.bits 0 = 1 := rfl
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  have hb2 : ReductionDsl.bits 2 = 2 := rfl
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod hsT (.prod (SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT
      (.prod hdrCtT (.opt SM.Engine.cRecTy))))) :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) :=
    rsvT :: vpT :: .opt vpT :: .prod (.opt (.opt vpT)) hsT :: Γ0
  have hstep := vRecvStep1C_cost_le hk H hhk (Γ' := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.fst (.snd (.snd (.snd (.snd .v0)))))
  have hfr := hhk.fsRecv_le (Γ' := Γ1)
    (.snd .v3) (.fst (.snd .v4)) (.fst (.snd (.snd .v4)))
    (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v4)))))))
    .v0
    (.fst (.fst (.snd (.snd (.snd (.snd .v4))))))
    (.snd (.fst (.snd (.snd (.snd (.snd .v4))))))
    (.snd (.snd (.snd (.snd (.snd .v4)))))
  simp only [v0_cost, v3_cost, v4_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hstep hfr
  simp only [SM.Engine.vRecvC, SM.orE, SM.sendsInE, vpId_cost, vpTcurNat_cost, vpVR_cost,
    vpSetVR_cost, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v7_cost,
    hb0, hb1, hb2, Nat.reduceAdd]
  omega

lemma commitEC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L : ℕ)
    (hhk : HooksCostBounded hk H)
    {Γ'} (es : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (s : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : ReductionDsl.Expr OO_cka Γ' .bool)
    (old new : ReductionDsl.Expr OO_cka Γ'
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (pos : ReductionDsl.Expr OO_cka Γ' SM.posTy) :
    (SM.Engine.commitEC hk L es s p old new pos).cost ≤
      es.cost + s.cost + 2 * p.cost + old.cost + 2 * new.cost + 2 * pos.cost +
        H + 240 * L + 1500 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod (SM.Engine.esTy vpT hsT) (.prod (SM.Engine.cGsTy vpT)
      (.prod .bool (.prod vpT vpT))) :: Γ'
  have hacc := cAcceptE_cost_le (O' := OO_cka) (vpT := vpT) L s p new pos
  have hcm := hhk.commit_le (Γ' := Γ0)
    (SM.Engine.esH (.fst .v0)) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
  simp only [esH_cost, v0_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hcm
  simp only [SM.Engine.commitEC, SM.Engine.esMk, esG_cost, esAbort_cost, cGsSetStP_cost,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost,
    Nat.reduceAdd]
  omega

private lemma transmitEC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep : ℕ)
    (π : SM.Engine.Policy) (hhk : HooksCostBounded hk H)
    {Γ'} (es : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : ReductionDsl.Expr OO_cka Γ' (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins))))) :
    (SM.Engine.transmitEC hk L 3 qep π es arg).cost ≤
      es.cost + arg.cost + 2 * H + 70 * L +
        L * (ReductionDsl.bits (π.tL.getD 0) + 2 * ReductionDsl.bits π.tStar + 40) +
        2 * ReductionDsl.bits π.tStar + 5 * ReductionDsl.bits qep + 2520 := by
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod (SM.Engine.esTy vpT hsT) (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))) :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) := SM.Engine.cGsTy vpT :: Γ0
  let Γ2 : List (ReductionDsl.Ty S_cka) :=
    .prod vpT hdrCtT :: .prod (.opt (.prod vpT hdrCtT)) hsT :: Γ1
  have hep := cEpMgmtE_cost_le (O' := OO_cka) (vpT := vpT) qep (Γ' := Γ0)
    (SM.Engine.esG (.fst .v0)) (.fst (.snd .v0)) (SM.isSomeE (.snd (.snd (.snd .v0))))
  have hld := leakDoomE_cost_le (O' := OO_cka) (vpT := vpT) L π (Γ' := Γ1)
    (SM.Engine.esG (.fst .v1)) .v0
  have hvs := vSendC_cost_le hk H hhk (Γ' := Γ1)
    (SM.Engine.esH (.fst .v1)) .v0 (.fst (.snd .v1))
    (SM.pGet (SM.Engine.cGsSt .v0) (.fst (.snd .v1)))
    (.fst (.snd (.snd .v1))) .none (.snd (.snd (.snd .v1)))
  have hrec := cRecordE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ2)
    .v2 (.fst (.snd .v3)) (.fst .v0)
    (.pair (.pair (.fst (.snd .v3)) (.pair (SM.pGet (SM.Engine.cGsEpoch .v2) (.fst (.snd .v3)))
        (.add (SM.pGet (SM.Engine.cGsIdx .v2) (.fst (.snd .v3))) (.nat 1))))
      (.pair (.fst (.snd (.snd .v3))) (.snd .v0)))
    (.bool false)
  simp only [esG_cost, esH_cost, pGet_cost, cGsSt_cost, cGsEpoch_cost, cGsIdx_cost, isSomeE_cost,
    v0_cost, v1_cost, v2_cost, v3_cost, ReductionDsl.Expr.cost, hb1, Nat.reduceAdd] at hep hld hvs hrec
  simp only [SM.Engine.transmitEC, SM.orE, SM.Engine.cGsWin, SM.Engine.esMk,
    esG_cost, esAbort_cost, esSetAbort_cost,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, Nat.reduceAdd]
  omega

private lemma challEC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep : ℕ)
    (mo : SM.Construction.Mode) (π : SM.Engine.Policy) (hhk : HooksCostBounded hk H)
    {Γ'} (es : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : ReductionDsl.Expr OO_cka Γ'
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins)))))) :
    (SM.Engine.challEC hk L 3 qep (SM.Engine.modeCfgEC OO_cka mo) π es arg).cost ≤
      es.cost + arg.cost + 2 * H + 70 * L +
        L * (ReductionDsl.bits (π.tL.getD 0) + 2 * ReductionDsl.bits π.tStar + 40) +
        2 * ReductionDsl.bits π.tStar + ReductionDsl.bits mo.tStar +
        5 * ReductionDsl.bits qep + 2720 := by
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod (SM.Engine.esTy vpT hsT)
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))) :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) := SM.Engine.cGsTy vpT :: Γ0
  let Γ2 : List (ReductionDsl.Ty S_cka) :=
    .prod vpT hdrCtT :: .prod (.opt (.prod vpT hdrCtT)) hsT :: Γ1
  have hep := cEpMgmtE_cost_le (O' := OO_cka) (vpT := vpT) qep (Γ' := Γ0)
    (SM.Engine.esG (.fst .v0)) (.fst (.snd .v0)) (SM.isSomeE (.snd (.snd (.snd (.snd .v0)))))
  have hsc := cSafeChE_cost_le (O' := OO_cka) (vpT := vpT) (Γ' := Γ1) .v0 (.fst (.snd .v1))
  have hok := modeCfgEC_challOKE_cost_le (O' := OO_cka) mo (Γ' := Γ1)
    (SM.pGet (SM.Engine.cGsEpoch .v0) (.fst (.snd .v1)))
  have hld := leakDoomE_cost_le (O' := OO_cka) (vpT := vpT) L π (Γ' := Γ1)
    (SM.Engine.esG (.fst .v1)) .v0
  have hvs := vSendC_cost_le hk H hhk (Γ' := Γ1)
    (SM.Engine.esH (.fst .v1)) .v0 (.fst (.snd .v1))
    (SM.pGet (SM.Engine.cGsSt .v0) (.fst (.snd .v1)))
    ((SM.Engine.modeCfgEC OO_cka mo).challMsgE
      (SM.pGet (SM.Engine.cGsEpoch .v0) (.fst (.snd .v1)))
      (SM.Engine.cGsB (SM.Engine.esG (.fst .v1)))
      (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
    (.some (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))))
    (.snd (.snd (.snd (.snd .v1))))
  have hrec := cRecordE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ2)
    .v2 (.fst (.snd .v3)) (.fst .v0)
    (.pair (.pair (.fst (.snd .v3)) (.pair (SM.pGet (SM.Engine.cGsEpoch .v2) (.fst (.snd .v3)))
        (.add (SM.pGet (SM.Engine.cGsIdx .v2) (.fst (.snd .v3))) (.nat 1))))
      (.pair ((SM.Engine.modeCfgEC OO_cka mo).challMsgE
        (SM.pGet (SM.Engine.cGsEpoch .v2) (.fst (.snd .v3)))
        (SM.Engine.cGsB (SM.Engine.esG (.fst .v3)))
        (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3))))) (.snd .v0)))
    (.bool true)
  simp only [modeCfgEC_challMsgE_cost, cGsB_cost, esG_cost, esH_cost, pGet_cost, cGsSt_cost,
    cGsEpoch_cost, cGsIdx_cost, isSomeE_cost, v0_cost, v1_cost, v2_cost, v3_cost,
    ReductionDsl.Expr.cost, hb1, Nat.reduceAdd] at hep hsc hok hld hvs hrec
  simp only [SM.Engine.challEC, SM.orE, SM.Engine.cGsWin, SM.Engine.esMk,
    esG_cost, esAbort_cost, esSetAbort_cost,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, Nat.reduceAdd]
  omega

private lemma deliverEC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L maxSkip : ℕ)
    (cfg : SM.Engine.ConfigEC OO_cka) (hhk : HooksCostBounded hk H)
    {Γ'} (es : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : ReductionDsl.Expr OO_cka Γ'
      (.prod .bool (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    (SM.Engine.deliverEC hk L maxSkip cfg es arg).cost ≤
      es.cost + arg.cost + 3 * H + 600 * L + (maxSkip + 1) + 4600 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let decT : ReductionDsl.Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod (SM.Engine.esTy vpT hsT) (.prod .bool hdrCtT) :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) := SM.Engine.cRecTy :: Γ0
  let Γ2 : List (ReductionDsl.Ty S_cka) :=
    .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  let Γ3 : List (ReductionDsl.Ty S_cka) := decT :: Γ2
  let Γ4 : List (ReductionDsl.Ty S_cka) :=
    SM.Engine.cGsTy vpT ::
      .prod (.opt (SM.Engine.cGsTy vpT)) (SM.Engine.esTy vpT hsT) :: Γ3
  have hit := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0)
    (SM.Engine.esG (O' := OO_cka) (.fst .v0)) (SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ1)
    (SM.Engine.esH (.fst .v1)) (SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd .v1)) (.some .v0)
  have hmb3 := cMustBeCorrectE_cost_le (O' := OO_cka) (vpT := vpT) L maxSkip (Γ' := Γ2)
    (SM.Engine.esG (.fst .v3)) (.fst (.snd .v3)) .v2
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ3)
    (SM.Engine.esSetH (.fst .v4) (.snd .v2)) (SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (SM.Engine.cRecPos .v3)
  have hmb6 := cMustBeCorrectE_cost_le (O' := OO_cka) (vpT := vpT) L maxSkip (Γ' := Γ4)
    (SM.Engine.esG (.fst .v6)) (.fst (.snd .v6)) .v5
  have hcc6 := cChallContainsE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ4)
    (SM.Engine.esG (.fst .v6)) (SM.Engine.cRecPos .v5)
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, cRecPos_cost, otherE_cost,
    ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost, v6_cost,
    Nat.reduceAdd] at hit hvr hmb3 hcm hmb6 hcc6
  simp only [SM.Engine.deliverEC, SM.orE, SM.Engine.cGsWin, SM.Engine.esMk,
    SM.Engine.cRecMsg, SM.posEpoch, SM.posIdx, cRecPos_cost,
    esG_cost, esAbort_cost, esSetG_cost, cGsSetWin_cost, CKA.ckaOps,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, v5_cost,
    Nat.reduceAdd]
  omega

private lemma injectEC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep : ℕ)
    (mo : SM.Construction.Mode) (hhk : HooksCostBounded hk H)
    {Γ'} (es : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : ReductionDsl.Expr OO_cka Γ'
      (.prod .bool (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    (SM.Engine.injectEC hk L 3 qep (SM.Engine.modeCfgEC OO_cka mo) es arg).cost ≤
      es.cost + arg.cost + 3 * H + 600 * L +
        ReductionDsl.bits qep + ReductionDsl.bits mo.tStar + 4210 := by
  have hqep1 := bits_succ_le qep
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let decT : ReductionDsl.Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod (SM.Engine.esTy vpT hsT) (.prod .bool hdrCtT) :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) :=
    decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ0
  have hit := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0)
    (SM.Engine.esG (O' := OO_cka) (.fst .v0)) (SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hsi := cSafeInjE_cost_le (O' := OO_cka) (vpT := vpT) (Γ' := Γ0)
    (SM.Engine.esG (.fst .v0))
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ0)
    (SM.Engine.esH (.fst .v0)) (SM.Engine.esG (.fst .v0)) (.fst (.snd .v0))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v0))) (.fst (.snd .v0)))
    (.snd (.snd .v0)) .none
  have htr := cTrivialE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ1)
    (SM.Engine.esG (.fst .v3))
    (.pair (SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ1)
    (SM.Engine.esSetH (.fst .v3) (.snd .v2)) (SM.Engine.esG (.fst .v3)) (.fst (.snd .v3))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v3))) (.fst (.snd .v3)))
    (.fst .v0)
    (.pair (SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := modeCfgEC_injectFullE_cost_le (O' := OO_cka) mo (Γ' := Γ1) (.fst (.snd .v0))
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, otherE_cost,
    ReductionDsl.Expr.cost,
    v0_cost, v2_cost, v3_cost, Nat.reduceAdd] at hit hsi hvr htr hcm hij
  simp only [SM.Engine.injectEC, SM.orE, SM.isSomeE, SM.Engine.cGsWin, SM.Engine.esMk,
    esG_cost, esAbort_cost, esSetH_cost, esSetG_cost, cGsSetWin_cost,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, Nat.reduceAdd]
  omega

private lemma corrEC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L : ℕ)
    (π : SM.Engine.Policy) (hhk : HooksCostBounded hk H)
    {Γ'} (es : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : ReductionDsl.Expr OO_cka Γ' .bool) :
    (SM.Engine.corrEC hk L π es p).cost ≤
      es.cost + p.cost + H + 18000 * L +
        L * (ReductionDsl.bits (π.tL.getD 0) + 2 * ReductionDsl.bits π.tStar + 40) +
        (ReductionDsl.bits (π.tL.getD 0) + 3) +
        4 * ReductionDsl.bits π.tStar + 15020 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let psT := CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (ReductionDsl.Ty S_cka) := .prod (SM.Engine.esTy vpT hsT) .bool :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ0
  have hca := cCorrAllowedE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ0)
    (SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hac0 := cAfterCorrE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ0)
    (SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hld := leakDoomE_cost_le (O' := OO_cka) (vpT := vpT) L π (Γ' := Γ0)
    (SM.Engine.esG (.fst .v0)) (SM.Engine.cAfterCorrE L (SM.Engine.esG (.fst .v0)) (.snd .v0))
  have hcd := corrDoomE_cost_le (O' := OO_cka) (vpT := vpT) π (Γ' := Γ0)
    (SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hrv := hhk.reveal_le (Γ' := Γ0)
    (SM.Engine.esH (.fst .v0)) (SM.Engine.esG (.fst .v0)) (.snd .v0)
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v0))) (.snd .v0))
  have hac1 := cAfterCorrE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ1)
    (SM.Engine.esG (.fst .v2)) (.snd .v2)
  simp only [esG_cost, esH_cost, pGet_cost, cGsSt_cost, v0_cost, v2_cost,
    ReductionDsl.Expr.cost, Nat.reduceAdd] at hca hac0 hld hcd hrv hac1
  simp only [SM.Engine.corrEC, SM.orE, SM.Engine.cGsWin, SM.Engine.esMk,
    esG_cost, esAbort_cost, esSetAbort_cost,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, Nat.reduceAdd]
  omega

lemma implEC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep maxSkip : ℕ)
    (mo : SM.Construction.Mode) (hhk : HooksCostBounded hk H)
    {Γ'} (es : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : ReductionDsl.Expr OO_cka Γ' (CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Engine.implEC hk L 3 qep maxSkip (SM.Engine.modeCfgEC OO_cka mo) mo.policy es q).cost ≤
      es.cost + q.cost + 3 * H + 18000 * L +
        L * (ReductionDsl.bits (mo.tL.getD 0) + 2 * ReductionDsl.bits mo.tStar + 40) +
        (ReductionDsl.bits (mo.tL.getD 0) + 3) +
        5 * ReductionDsl.bits mo.tStar + 5 * ReductionDsl.bits qep + (maxSkip + 1) + 18050 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := SM.Engine.esTy vpT hsT
  let smqT := CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let trQ : ReductionDsl.Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : ReductionDsl.Ty S_cka := .prod .bool
    (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : ReductionDsl.Ty S_cka := .prod .bool hdrCtT
  let Γ0 : List (ReductionDsl.Ty S_cka) := .prod esT smqT :: Γ'
  let Γ_cr : List (ReductionDsl.Ty S_cka) := .bool :: Γ0
  let Γ_s1 : List (ReductionDsl.Ty S_cka) :=
    .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γ0
  let Γ_ij : List (ReductionDsl.Ty S_cka) := dlQ :: Γ_s1
  let Γ_s2 : List (ReductionDsl.Ty S_cka) := .sum (.sum trQ chQ) dlQ :: Γ_s1
  let Γ_dl : List (ReductionDsl.Ty S_cka) := dlQ :: Γ_s2
  let Γ_s3 : List (ReductionDsl.Ty S_cka) := .sum trQ chQ :: Γ_s2
  let Γ_tr : List (ReductionDsl.Ty S_cka) := trQ :: Γ_s3
  let Γ_ch : List (ReductionDsl.Ty S_cka) := chQ :: Γ_s3
  have htr := transmitEC_cost_le hk H L qep mo.policy hhk (Γ' := Γ_tr) (.fst .v4) .v0
  have hch := challEC_cost_le hk H L qep mo mo.policy hhk (Γ' := Γ_ch) (.fst .v4) .v0
  have hdl := deliverEC_cost_le hk H L maxSkip (SM.Engine.modeCfgEC OO_cka mo) hhk
    (Γ' := Γ_dl) (.fst .v3) .v0
  have hij := injectEC_cost_le hk H L qep mo hhk (Γ' := Γ_ij) (.fst .v2) .v0
  have hcr := corrEC_cost_le hk H L mo.policy hhk (Γ' := Γ_cr) (.fst .v1) .v0
  have hpol_tL : mo.policy.tL = mo.tL := rfl
  have hpol_tStar : mo.policy.tStar = mo.tStar := rfl
  simp only [hpol_tL, hpol_tStar, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost,
    ReductionDsl.Expr.cost, Nat.reduceAdd] at htr hch hdl hij hcr
  simp only [SM.Engine.implEC, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, Nat.reduceAdd]
  omega

private lemma cost_bind_ret_le_costUB {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ι : Type} {T : OracleSpec ι} {I : ReductionDsl.Iface S T}
    {Γ : List (ReductionDsl.Ty S)} {t u : ReductionDsl.Ty S}
    (e : ReductionDsl.Expr O Γ t) (k : ReductionDsl.Comp O I (t :: Γ) u) :
    (ReductionDsl.Comp.bind (.ret e) k).cost ≤ e.cost + compCostUB k + 2 := by
  have hk := compCost_le_costUB k
  simp only [ReductionDsl.Comp.cost]; omega

private lemma ret_pair_letE_cost_le_costUB {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ι : Type} {T : OracleSpec ι} {I : ReductionDsl.Iface S T}
    {Γ : List (ReductionDsl.Ty S)} {t u v : ReductionDsl.Ty S}
    (e : ReductionDsl.Expr O Γ t) (k : ReductionDsl.Expr O (t :: Γ) u)
    (r : ReductionDsl.Expr O Γ v) :
    (ReductionDsl.Comp.ret (I := I) (.pair (.letE e k) r)).cost ≤
      e.cost + r.cost + exprCostUB k + 3 := by
  have hk := exprCost_le_costUB k
  simp only [ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]; omega

section HooksCKACCost

variable
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

lemma hooksCKAC_costBounded (B : ℕ) (mo : SM.Construction.Mode) :
    HooksCostBounded
      (SM.Construction.hooksCKAC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 mo)
      (3 * ReductionDsl.bits mo.tH + ReductionDsl.bits mo.tStar + (B + 1) + 1010) where
  startSend_le h ctx p t γv σ r := by
    have htH1 := bits_succ_le mo.tH
    dsimp only [SM.Construction.hooksCKAC, SM.Construction.ckaStartSendC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [SM.leN, CKA.ckaIface, CKA.ckaSamplers, CKA.ckaOps,
      ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
      ReductionDsl.Expr.v2, ReductionDsl.Expr.v3, ReductionDsl.Expr.v4,
      dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]
    omega
  startRecv_le h ctx p t γv σ tn := by
    dsimp only [SM.Construction.hooksCKAC, SM.Construction.ckaStartRecvC,
      SM.Construction.ckaStartRecvAnsE]
    refine (ret_pair_letE_cost_le_costUB _ _ _).trans ?_
    simp only [CKA.ckaOps, ReductionDsl.Expr.cost,
      ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
      dsl_cost, exprCostUB, Nat.reduceAdd]
    omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [SM.Construction.hooksCKAC, SM.Construction.ckaFsSendC, CKA.ckaOps,
      ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]
    omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    have hB := ReductionDsl.bits_le_succ B
    simp only [SM.Construction.hooksCKAC, SM.Construction.ckaFsRecvC, CKA.ckaOps,
      ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]
    omega
  commit_le h ctx p old new := by
    have htH1 := bits_succ_le mo.tH
    dsimp only [SM.Construction.hooksCKAC, SM.Construction.ckaCommitC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [SM.isSomeE, SM.leN, SM.Engine.vpSetΓ, SM.Engine.vpMk,
      SM.Engine.vpId, SM.Engine.vpRoot, SM.Engine.vpVS, SM.Engine.vpVR,
      SM.Engine.vpΓ, SM.Engine.vpTcur, SM.Engine.vpTcurNat, CKA.ckaIface,
      ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
      ReductionDsl.Expr.v2, ReductionDsl.Expr.v3, ReductionDsl.Expr.v4,
      dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]
    omega
  reveal_le h ctx p vp := by
    dsimp only [SM.Construction.hooksCKAC, SM.Construction.ckaRevealC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [SM.Engine.realPartyE, SM.Engine.vpMk,
      SM.Engine.vpId, SM.Engine.vpRoot, SM.Engine.vpVS, SM.Engine.vpVR,
      SM.Engine.vpΓ, SM.Engine.vpTcur, SM.Engine.vpTcurNat, CKA.ckaIface,
      ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
      ReductionDsl.Expr.v2, dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]
    omega

end HooksCKACCost

section HooksPRNGCCost

variable
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

lemma hooksPRNGC_costBounded (B : ℕ) (mo : SM.Construction.Mode) :
    HooksCostBounded
      (SM.Construction.hooksPRNGC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo)
      (2 * ReductionDsl.bits mo.tStar + 3 * ReductionDsl.bits mo.tH + (B + 1) + 910) where
  startSend_le h ctx p t γv σ r := by
    dsimp only [SM.Construction.hooksPRNGC, SM.Construction.prngStartSendC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [SM.Construction.rootPRNGC, SM.Construction.prngProcessCorrC,
      PRFPRNG.prngIface, PRFPRNG.prngSamplers, PRFPRNG.prngOps, CKA.ckaSamplers, CKA.ckaOps,
      ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
      ReductionDsl.Expr.v2, ReductionDsl.Expr.v3,
      dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]
    omega
  startRecv_le h ctx p t γv σ tn := by
    dsimp only [SM.Construction.hooksPRNGC, SM.Construction.prngStartRecvC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [PRFPRNG.prngOps, CKA.ckaOps,
      ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
      ReductionDsl.Expr.v2, dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]
    omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [SM.Construction.hooksPRNGC, SM.Construction.prngFsSendC, PRFPRNG.prngOps,
      CKA.ckaOps, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]
    omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    have hB := ReductionDsl.bits_le_succ B
    simp only [SM.Construction.hooksPRNGC, SM.Construction.prngFsRecvC, PRFPRNG.prngOps,
      CKA.ckaOps, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]
    omega
  commit_le h ctx p old new := by
    simp only [SM.Construction.hooksPRNGC, SM.Construction.prngCommitC,
      ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]
    omega
  reveal_le h ctx p vp := by
    dsimp only [SM.Construction.hooksPRNGC, SM.Construction.prngRevealC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [SM.Engine.realPartyE, SM.Engine.vpMk,
      SM.Engine.vpId, SM.Engine.vpRoot, SM.Engine.vpVS, SM.Engine.vpVR,
      SM.Engine.vpΓ, SM.Engine.vpTcur, SM.Engine.vpTcurNat,
      ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
      dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]
    omega

lemma initPRNGEStateC_cost_le (mo : SM.Construction.Mode) {Γ'}
    (bE : ReductionDsl.Expr OO_cka Γ' .bool) :
    (SM.Construction.initPRNGEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) mo bE).cost ≤
      bE.cost + 2 * ReductionDsl.bits mo.tStar + 3 * ReductionDsl.bits mo.tH + 910 := by
  have hb0 : ReductionDsl.bits 0 = 1 := rfl
  dsimp only [SM.Construction.initPRNGEStateC]
  refine (cost_bind_ret_le_costUB _ _).trans ?_
  simp only [SM.Construction.rootPRNGC, SM.Construction.prngProcessCorrC,
    SM.Construction.abortedPartiesE, SM.Engine.mkPartiesE, SM.Engine.cGsInitE,
    SM.Engine.cGsMk, SM.Engine.esMk, SM.Engine.vpMk,
    PRFPRNG.prngIface, PRFPRNG.prngSamplers, PRFPRNG.prngOps,
    CKA.ckaSamplers, CKA.ckaOps,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2, ReductionDsl.Expr.v3,
    hb0, dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]
  omega

end HooksPRNGCCost

section HooksFSCCost

variable
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

local notation "hsTy_fs" => SM.Construction.fsHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "vpTy_fs" => SM.Construction.fsVpTy KC Γ CCoins T I KR RSt K SS RS M E

private lemma fsHsCache_cost {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs) :
    (SM.Construction.fsHsCache h).cost = h.cost + 1 := rfl

private lemma fsHsTable_cost {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs) :
    (SM.Construction.fsHsTable h).cost = h.cost + 2 := rfl

private lemma fsHsSessions_cost {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs) :
    (SM.Construction.fsHsSessions h).cost = h.cost + 3 := rfl

private lemma fsHsTrans_cost {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs) :
    (SM.Construction.fsHsTrans h).cost = h.cost + 4 := rfl

private lemma fsHsCount_cost {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs) :
    (SM.Construction.fsHsCount h).cost = h.cost + 5 := rfl

private lemma fsHsSCorr_cost {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs) :
    (SM.Construction.fsHsSCorr h).cost = h.cost + 6 := rfl

private lemma fsHsExt_cost {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs) :
    (SM.Construction.fsHsExt h).cost = h.cost + 6 := rfl

private lemma fsHsSetCache_cost_le {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs)
    (c : ReductionDsl.Expr O' Γ'
      (.tbl (.opt (SM.Construction.fsCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    (SM.Construction.fsHsSetCache h c).cost ≤ 6 * h.cost + c.cost + 40 := by
  simp only [SM.Construction.fsHsSetCache, SM.Construction.fsHsMk,
    fsHsTable_cost, fsHsSessions_cost, fsHsTrans_cost, fsHsCount_cost,
    fsHsSCorr_cost, fsHsExt_cost, ReductionDsl.Expr.cost]
  omega

private lemma fsHsSetTable_cost_le {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs)
    (tbl : ReductionDsl.Expr O' Γ'
      (.list (SM.Construction.fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    (SM.Construction.fsHsSetTable h tbl).cost ≤ 6 * h.cost + tbl.cost + 40 := by
  simp only [SM.Construction.fsHsSetTable, SM.Construction.fsHsMk,
    fsHsCache_cost, fsHsSessions_cost, fsHsTrans_cost, fsHsCount_cost,
    fsHsSCorr_cost, fsHsExt_cost, ReductionDsl.Expr.cost]
  omega

private lemma fsHsSetSessions_cost_le {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs)
    (ses : ReductionDsl.Expr O' Γ' (.list (.base .i))) :
    (SM.Construction.fsHsSetSessions h ses).cost ≤ 6 * h.cost + ses.cost + 40 := by
  simp only [SM.Construction.fsHsSetSessions, SM.Construction.fsHsMk,
    fsHsCache_cost, fsHsTable_cost, fsHsTrans_cost, fsHsCount_cost,
    fsHsSCorr_cost, fsHsExt_cost, ReductionDsl.Expr.cost]
  omega

private lemma fsHsSetTrans_cost_le {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs)
    (tr : ReductionDsl.Expr O' Γ'
      (.list (SM.Construction.fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    (SM.Construction.fsHsSetTrans h tr).cost ≤ 6 * h.cost + tr.cost + 40 := by
  simp only [SM.Construction.fsHsSetTrans, SM.Construction.fsHsMk,
    fsHsCache_cost, fsHsTable_cost, fsHsSessions_cost, fsHsCount_cost,
    fsHsSCorr_cost, fsHsExt_cost, ReductionDsl.Expr.cost]
  omega

private lemma fsHsSetCountTrans_cost_le {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs)
    (cnt : ReductionDsl.Expr O' Γ' .nat)
    (tr : ReductionDsl.Expr O' Γ'
      (.list (SM.Construction.fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    (SM.Construction.fsHsSetCountTrans h cnt tr).cost ≤ 5 * h.cost + cnt.cost + tr.cost + 40 := by
  simp only [SM.Construction.fsHsSetCountTrans, SM.Construction.fsHsMk,
    fsHsCache_cost, fsHsTable_cost, fsHsSessions_cost,
    fsHsSCorr_cost, fsHsExt_cost, ReductionDsl.Expr.cost]
  omega

private lemma fsHsSetSCorr_cost_le {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs)
    (sc : ReductionDsl.Expr O' Γ' .bool) :
    (SM.Construction.fsHsSetSCorr h sc).cost ≤ 6 * h.cost + sc.cost + 40 := by
  simp only [SM.Construction.fsHsSetSCorr, SM.Construction.fsHsMk,
    fsHsCache_cost, fsHsTable_cost, fsHsSessions_cost, fsHsTrans_cost,
    fsHsCount_cost, fsHsExt_cost, ReductionDsl.Expr.cost]
  omega

private lemma fsHsSetExt_cost_le {O' : ReductionDsl.Ops S_cka} {Γ'}
    (h : ReductionDsl.Expr O' Γ' hsTy_fs)
    (ex : ReductionDsl.Expr O' Γ' (SM.Construction.fsExtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Construction.fsHsSetExt h ex).cost ≤ 6 * h.cost + ex.cost + 40 := by
  simp only [SM.Construction.fsHsSetExt, SM.Construction.fsHsMk,
    fsHsCache_cost, fsHsTable_cost, fsHsSessions_cost, fsHsTrans_cost,
    fsHsCount_cost, fsHsSCorr_cost, ReductionDsl.Expr.cost]
  omega

private lemma tableLookupE_cost_le (L : ℕ) {Γ'}
    (tblE : ReductionDsl.Expr OO_cka Γ'
      (.list (SM.Construction.fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (ikE : ReductionDsl.Expr OO_cka Γ' (.base .i)) :
    (SM.Construction.tableLookupE L tblE ikE).cost ≤ tblE.cost + ikE.cost + 12 * L + 10 := by
  have hmax31 : max 3 1 = 3 := rfl
  simp only [SM.Construction.tableLookupE, PRFPRNG.prngOps, CKA.ckaOps,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost, hmax31, Nat.reduceAdd]
  omega

private lemma lookupFC_cost_le (L : ℕ) {Γ'}
    (hE : ReductionDsl.Expr OO_cka Γ' hsTy_fs)
    (ikE : ReductionDsl.Expr OO_cka Γ' (.base .i)) :
    (SM.Construction.lookupFC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L hE ikE).cost ≤
      hE.cost + ikE.cost + 12 * L + 100 := by
  let Γ0 : List (ReductionDsl.Ty S_cka) := .prod hsTy_fs (.base .i) :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) := .base .k :: Γ0
  have htl := tableLookupE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) L (Γ' := Γ0)
    (SM.Construction.fsHsTable (.fst .v0)) (.snd .v0)
  have hst := fsHsSetTable_cost_le (O' := OO_cka) (Γ' := Γ1) (.fst .v1)
    (.cons (.pair (.snd .v1) .v0) (SM.Construction.fsHsTable (.fst .v1)))
  simp only [fsHsTable_cost, v0_cost, v1_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at htl hst
  simp only [SM.Construction.lookupFC, PRFPRNG.fsaeadHeaderAdIface,
    PRFPRNG.prngSamplers, CKA.ckaSamplers,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost, v0_cost, v1_cost, Nat.reduceAdd]
  omega

private lemma isExtE_cost_le (L j : ℕ) {Γ'}
    (hE : ReductionDsl.Expr OO_cka Γ' hsTy_fs)
    (ikE : ReductionDsl.Expr OO_cka Γ' (.base .i)) :
    (SM.Construction.isExtE L j hE ikE).cost ≤
      hE.cost + ikE.cost + 30 * L + 2 * (j + 1) + 120 := by
  have hb0 : ReductionDsl.bits 0 = 1 := rfl
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  have hmax11 : max 1 1 = 1 := rfl
  have hmax13 : max 1 3 = 3 := rfl
  have hj := ReductionDsl.bits_le_succ j
  let Γ0 : List (ReductionDsl.Ty S_cka) := .prod hsTy_fs (.base .i) :: Γ'
  have hss := fsHsSetSessions_cost_le (O' := OO_cka) (Γ' := Γ0) (.fst .v0)
    (SM.Construction.sessionsAppendOneE L (SM.Construction.fsHsSessions (.fst .v0)) (.snd .v0))
  simp only [SM.Construction.sessionsAppendOneE, fsHsSessions_cost, v0_cost, v1_cost,
    ReductionDsl.Expr.cost, Nat.reduceAdd] at hss
  simp only [SM.Construction.isExtE, SM.Construction.sessionsMemE,
    SM.Construction.sessionsIdxOfE, SM.Construction.sessionsLenE,
    SM.Construction.sessionsAppendOneE,
    SM.orE, PRFPRNG.prngOps, CKA.ckaOps, fsHsSessions_cost,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost,
    hb0, hb1, hmax11, hmax13, Nat.reduceAdd]
  omega

private lemma extOfE_cost_le (L j : ℕ) {Γ'}
    (hE : ReductionDsl.Expr OO_cka Γ' hsTy_fs)
    (sidE : ReductionDsl.Expr OO_cka Γ' (.opt (.base .i))) :
    (SM.Construction.extOfE L j hE sidE).cost ≤
      hE.cost + sidE.cost + 30 * L + 2 * (j + 1) + 130 := by
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .base .i :: .prod hsTy_fs (.opt (.base .i)) :: Γ'
  have hie := isExtE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) L j (Γ' := Γ0) (.fst .v1) .v0
  simp only [v0_cost, v1_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hie
  simp only [SM.Construction.extOfE, ReductionDsl.Expr.cost, v0_cost, Nat.reduceAdd]
  omega

private lemma rootFSC_cost_le (L : ℕ) (mo : SM.Construction.Mode) {Γ'}
    (hE : ReductionDsl.Expr OO_cka Γ' hsTy_fs)
    (tE : ReductionDsl.Expr OO_cka Γ' .nat)
    (ikE : ReductionDsl.Expr OO_cka Γ' (.base .i))
    (σE : ReductionDsl.Expr OO_cka Γ' (.base .sig)) :
    (SM.Construction.rootFSC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L mo hE tE ikE σE).cost ≤
      hE.cost + tE.cost + ikE.cost + σE.cost +
        12 * L + 2 * ReductionDsl.bits mo.tStar + 2 * ReductionDsl.bits mo.tH + 260 := by
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod hsTy_fs (.prod .nat (.prod (.base .i) (.base .sig))) :: Γ'
  have hlk := lookupFC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L (Γ' := Γ0)
    (.fst .v0) (.fst (.snd (.snd .v0)))
  simp only [v0_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at hlk
  simp only [SM.Construction.rootFSC, PRFPRNG.fsaeadHeaderAdIface,
    PRFPRNG.prngSamplers, PRFPRNG.prngOps, CKA.ckaSamplers, CKA.ckaOps,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, Nat.reduceAdd]
  omega

private lemma fsStartSendC_cost_le (L : ℕ) (mo : SM.Construction.Mode) (j : ℕ) {Γ'}
    (hE : ReductionDsl.Expr OO_cka Γ' hsTy_fs)
    (ctxE : ReductionDsl.Expr OO_cka Γ' (SM.Engine.cGsTy vpTy_fs))
    (pE : ReductionDsl.Expr OO_cka Γ' .bool)
    (tE : ReductionDsl.Expr OO_cka Γ' .nat)
    (γE : ReductionDsl.Expr OO_cka Γ' (.base .γ))
    (σE : ReductionDsl.Expr OO_cka Γ' (.base .sig))
    (rE : ReductionDsl.Expr OO_cka Γ' (.opt (.base .ccoins))) :
    (SM.Construction.fsStartSendC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L mo j hE ctxE pE tE γE σE rE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + γE.cost + σE.cost + rE.cost) +
        300 * L + 20 * (j + 1) + 2 * ReductionDsl.bits mo.tStar +
        2 * ReductionDsl.bits mo.tH + 2110 := by
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .base .ccoins :: .prod hsTy_fs (.prod .nat (.prod (.base .γ)
      (.prod (.base .sig) (.opt (.base .ccoins))))) :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) :=
    .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) hsTy_fs :: Γ0
  have hrt := rootFSC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo (Γ' := Γ0)
    (.fst .v1) (.fst (.snd .v1))
    (.snd (.snd (ReductionDsl.Expr.op (O := OO_cka) CKA.CKAOp.ckaSend
      (.pair (.fst (.snd (.snd .v1))) .v0))))
    (.fst (.snd (.snd (.snd .v1))))
  have hext := extOfE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    L j (Γ' := Γ1) (.snd .v0) (.snd (.snd (.fst .v0)))
  have hsc := fsHsSetCache_cost_le (O' := OO_cka) (Γ' := Γ1)
    (.snd (SM.Construction.extOfE L j (.snd .v0) (.snd (.snd (.fst .v0)))))
    (.tset (SM.Construction.fsHsCache
        (.snd (SM.Construction.extOfE L j (.snd .v0) (.snd (.snd (.fst .v0))))))
      (.fst (.snd .v2))
      (.some (.pair
        (.fst (.snd (ReductionDsl.Expr.op (O := OO_cka) CKA.CKAOp.ckaSend
          (.pair (.fst (.snd (.snd .v2))) .v1))))
        (.pair (.fst (.fst .v0))
          (.pair (.fst (.snd (.fst .v0)))
            (.fst (SM.Construction.extOfE L j (.snd .v0) (.snd (.snd (.fst .v0))))))))))
  simp only [PRFPRNG.prngOps, CKA.ckaOps, fsHsCache_cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, Nat.reduceAdd] at hrt hext hsc
  simp only [SM.Construction.fsStartSendC, PRFPRNG.fsaeadHeaderAdIface,
    PRFPRNG.prngSamplers, PRFPRNG.prngOps, CKA.ckaSamplers, CKA.ckaOps,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, Nat.reduceAdd]
  omega

private lemma fsStartRecvC_cost_le (L : ℕ) (mo : SM.Construction.Mode) (j : ℕ) {Γ'}
    (hE : ReductionDsl.Expr OO_cka Γ' hsTy_fs)
    (ctxE : ReductionDsl.Expr OO_cka Γ' (SM.Engine.cGsTy vpTy_fs))
    (pE : ReductionDsl.Expr OO_cka Γ' .bool)
    (tE : ReductionDsl.Expr OO_cka Γ' .nat)
    (γE : ReductionDsl.Expr OO_cka Γ' (.base .γ))
    (σE : ReductionDsl.Expr OO_cka Γ' (.base .sig))
    (tnE : ReductionDsl.Expr OO_cka Γ' (.base .t)) :
    (SM.Construction.fsStartRecvC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L mo j hE ctxE pE tE γE σE tnE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + γE.cost + σE.cost + tnE.cost) +
        100 * L + 6 * (j + 1) + ReductionDsl.bits mo.tStar + 910 := by
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod hsTy_fs (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.base .t)))) :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) := .prod (.base .k) hsTy_fs :: Γ0
  have hlk := lookupFC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L (Γ' := Γ0)
    (.fst .v0)
    (.snd (ReductionDsl.Expr.op (O := OO_cka) CKA.CKAOp.ckaReceive
      (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))))
  have hie := isExtE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) L j (Γ' := Γ1) (.snd .v0)
    (.snd (ReductionDsl.Expr.op (O := OO_cka) CKA.CKAOp.ckaReceive
      (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))
  simp only [PRFPRNG.prngOps, CKA.ckaOps, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, Nat.reduceAdd] at hlk hie
  simp only [SM.Construction.fsStartRecvC, PRFPRNG.prngOps, CKA.ckaOps, fsHsCache_cost,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, Nat.reduceAdd]
  omega

private lemma fsFsSendC_cost_le {Γ'}
    (hE : ReductionDsl.Expr OO_cka Γ' hsTy_fs)
    (ctxE : ReductionDsl.Expr OO_cka Γ' (SM.Engine.cGsTy vpTy_fs))
    (pE : ReductionDsl.Expr OO_cka Γ' .bool)
    (tE : ReductionDsl.Expr OO_cka Γ' .nat)
    (ssvE : ReductionDsl.Expr OO_cka Γ' (.opt (.base .ss)))
    (hdrE : ReductionDsl.Expr OO_cka Γ' (CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (mE : ReductionDsl.Expr OO_cka Γ' (.base .msg))
    (pairE : ReductionDsl.Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    (SM.Construction.fsFsSendC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      1 hE ctxE pE tE ssvE hdrE mE pairE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + ssvE.cost +
        hdrE.cost + mE.cost + pairE.cost) + 500 := by
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  let hdrT := CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod hsTy_fs (.prod (SM.Engine.cGsTy vpTy_fs) (.prod .bool (.prod (.opt (.base .ss))
      (.prod hdrT (.prod (.base .msg) (.opt (.prod (.base .msg) (.base .msg)))))))) :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) := .base .ss :: .opt (.base .ss) :: Γ0
  let Γ2 : List (ReductionDsl.Ty S_cka) :=
    .base .ct :: .opt (.base .ct) :: .prod .bool hsTy_fs :: Γ0
  let Γ3 : List (ReductionDsl.Ty S_cka) := .prod (.base .ss) (.base .rs) :: Γ0
  have hsc := cSafeChE_cost_le (O' := OO_cka) (vpT := vpTy_fs) (Γ' := Γ0)
    (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
  have hssc := fsHsSetSCorr_cost_le (O' := OO_cka) (Γ' := Γ1) (.fst .v2) (.bool true)
  have hsct := fsHsSetCountTrans_cost_le (O' := OO_cka) (Γ' := Γ2) (.snd .v2)
    (.add (SM.Construction.fsHsCount (.snd .v2)) (.nat 1))
    (.cons (.pair (.add (SM.Construction.fsHsCount (.snd .v2)) (.nat 1))
      (.pair (.fst (.snd (.snd (.snd (.snd .v3))))) .v0))
      (SM.Construction.fsHsTrans (.snd .v2)))
  have hse := fsHsSetExt_cost_le (O' := OO_cka) (Γ' := Γ3) (.fst .v1)
    (.some (.pair (.fst (ReductionDsl.Expr.op (O := OO_cka) CKA.CKAOp.fsSend
      (.pair (.fst .v0) (.pair (.fst (.snd (.snd (.snd (.snd .v1)))))
        (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))))))) (.snd .v0)))
  simp only [fsHsCount_cost, fsHsTrans_cost, CKA.ckaOps,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, hb1,
    Nat.reduceAdd] at hsc hssc hsct hse
  simp only [SM.Construction.fsFsSendC, PRFPRNG.fsaeadHeaderAdIface,
    PRFPRNG.prngOps, CKA.ckaOps, fsHsExt_cost, fsHsSCorr_cost,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, Nat.reduceAdd]
  omega

private lemma fsTransFindE_cost_le (L : ℕ) {Γ'}
    (trE : ReductionDsl.Expr OO_cka Γ'
      (.list (SM.Construction.fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (hcE : ReductionDsl.Expr OO_cka Γ' (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Construction.fsTransFindE L trE hcE).cost ≤ trE.cost + hcE.cost + 55 * L + 20 := by
  have hmax11 : max 1 1 = 1 := rfl
  have hmax14 : max 1 4 = 4 := rfl
  have hmax47 : max 4 7 = 7 := rfl
  simp only [SM.Construction.fsTransFindE, SM.Engine.hdrCtEqE, SM.Engine.optTEqE,
    PRFPRNG.prngOps, CKA.ckaOps, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, hmax11, hmax14, hmax47, Nat.reduceAdd]
  omega

private lemma fsTransFilterE_cost_le (L : ℕ) {Γ'}
    (trE : ReductionDsl.Expr OO_cka Γ'
      (.list (SM.Construction.fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (dropE : ReductionDsl.Expr OO_cka Γ' .nat) :
    (SM.Construction.fsTransFilterE L trE dropE).cost ≤ trE.cost + dropE.cost + 15 * L + 15 := by
  have hmax31 : max 3 1 = 3 := rfl
  simp only [SM.Construction.fsTransFilterE, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, hmax31, Nat.reduceAdd]
  omega

private lemma fsFsRecvC_cost_le (L B : ℕ) {Γ'}
    (hE : ReductionDsl.Expr OO_cka Γ' hsTy_fs)
    (ctxE : ReductionDsl.Expr OO_cka Γ' (SM.Engine.cGsTy vpTy_fs))
    (pE : ReductionDsl.Expr OO_cka Γ' .bool)
    (tE : ReductionDsl.Expr OO_cka Γ' .nat)
    (rsvE : ReductionDsl.Expr OO_cka Γ' (.opt (.base .rs)))
    (hdrE : ReductionDsl.Expr OO_cka Γ' (CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (eE : ReductionDsl.Expr OO_cka Γ' (.base .ct))
    (recE : ReductionDsl.Expr OO_cka Γ' (.opt SM.Engine.cRecTy)) :
    (SM.Construction.fsFsRecvC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B hE ctxE pE tE rsvE hdrE eE recE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + rsvE.cost +
        hdrE.cost + eE.cost + recE.cost) + 150 * L + (B + 1) + 500 := by
  have hB := ReductionDsl.bits_le_succ B
  let hdrT := CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod hsTy_fs (.prod (.opt (.base .rs)) (.prod hdrT
      (.prod (.base .ct) (.opt SM.Engine.cRecTy)))) :: Γ'
  let rrT : ReductionDsl.Ty S_cka := .sum .unit (.prod .nat (.opt (.base .msg)))
  let Γ1 : List (ReductionDsl.Ty S_cka) :=
    .prod .nat (.opt (.base .msg)) :: rrT :: .opt rrT :: Γ0
  let Γ2 : List (ReductionDsl.Ty S_cka) :=
    .prod (.base .rs) (.prod .nat (.base .msg)) :: .prod (.base .ss) (.base .rs) :: Γ0
  have htf0 := fsTransFindE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) L (Γ' := Γ0)
    (SM.Construction.fsHsTrans (.fst .v0))
    (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))))
  have htf3 := fsTransFindE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) L (Γ' := Γ1)
    (SM.Construction.fsHsTrans (.fst .v3))
    (.pair (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3)))))
  have hflt := fsTransFilterE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) L (Γ' := Γ1)
    (SM.Construction.fsHsTrans (.fst .v3))
    (.caseOpt (SM.Construction.fsTransFindE L (SM.Construction.fsHsTrans (.fst .v3))
      (.pair (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3)))))) (.fst .v0) (.fst .v0))
  have hst := fsHsSetTrans_cost_le (O' := OO_cka) (Γ' := Γ1) (.fst .v3)
    (SM.Construction.fsTransFilterE L (SM.Construction.fsHsTrans (.fst .v3))
      (.caseOpt (SM.Construction.fsTransFindE L (SM.Construction.fsHsTrans (.fst .v3))
        (.pair (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3)))))) (.fst .v0) (.fst .v0)))
  have hse := fsHsSetExt_cost_le (O' := OO_cka) (Γ' := Γ2) (.fst .v2)
    (.some (.pair (.fst .v1) (.fst .v0)))
  simp only [fsHsTrans_cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, Nat.reduceAdd] at htf0 htf3 hflt hst hse
  simp only [SM.Construction.fsFsRecvC, PRFPRNG.fsaeadHeaderAdIface, SM.Engine.cRecMsg,
    PRFPRNG.prngOps, CKA.ckaOps, fsHsExt_cost,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, Nat.reduceAdd]
  omega

@[simp] private lemma rangeListC_cost {S' : ReductionDsl.Sig} {O' : ReductionDsl.Ops S'}
    {ι : Type} {spec : OracleSpec ι} {I' : ReductionDsl.Iface S' spec}
    (L : ℕ) {Γ' : List (ReductionDsl.Ty S')} :
    (SM.Construction.rangeListC (O' := O') (I' := I') L (Γ' := Γ')).cost = 12 * L + 8 := by
  have hb0 : ReductionDsl.bits 0 = 1 := rfl
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  simp only [SM.Construction.rangeListC, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, hb0, hb1, Nat.reduceAdd]
  ring

private lemma unliftVRE_cost_le (L : ℕ) {Γ'}
    (vRE : ReductionDsl.Expr OO_cka Γ' (.tbl (.opt (.opt (.base .rs)))))
    (rsExtE : ReductionDsl.Expr OO_cka Γ' (.opt (.base .rs)))
    (rngE : ReductionDsl.Expr OO_cka Γ' (.list .nat)) :
    (SM.Construction.unliftVRE L vRE rsExtE rngE).cost ≤
      vRE.cost + rsExtE.cost + rngE.cost + 216 * L + 10 := by
  have hmax22 : max 2 2 = 2 := rfl
  have hmax14 : max 1 4 = 4 := rfl
  simp only [SM.Construction.unliftVRE, SM.Construction.unliftEntryE,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost, hmax22, hmax14, Nat.reduceAdd]
  omega

private lemma fsRevealC_cost_le (L : ℕ) (mo : SM.Construction.Mode) {Γ'}
    (hE : ReductionDsl.Expr OO_cka Γ' hsTy_fs)
    (ctxE : ReductionDsl.Expr OO_cka Γ' (SM.Engine.cGsTy vpTy_fs))
    (pE : ReductionDsl.Expr OO_cka Γ' .bool)
    (vpE : ReductionDsl.Expr OO_cka Γ' vpTy_fs) :
    (SM.Construction.fsRevealC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L mo hE ctxE pE vpE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + vpE.cost) +
        228 * L + ReductionDsl.bits mo.tStar + 830 := by
  let Γ0 : List (ReductionDsl.Ty S_cka) := .prod hsTy_fs vpTy_fs :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) :=
    .base .ss :: .opt (.base .ss) :: .opt (.base .ss) :: Γ0
  let Γ2 : List (ReductionDsl.Ty S_cka) :=
    .opt (.base .ss) :: .prod (.opt (.opt (.base .ss))) hsTy_fs :: Γ0
  let Γ3 : List (ReductionDsl.Ty S_cka) :=
    .prod (.base .ss) (.base .rs) :: .opt (.prod (.base .ss) (.base .rs)) ::
      .opt (.base .rs) :: Γ2
  let Γ4 : List (ReductionDsl.Ty S_cka) :=
    .opt (.base .rs) :: .prod (.opt (.opt (.base .rs))) hsTy_fs :: Γ2
  let Γ5 : List (ReductionDsl.Ty S_cka) := .list .nat :: Γ4
  have hssc := fsHsSetSCorr_cost_le (O' := OO_cka) (Γ' := Γ1) (.fst .v3) (.bool true)
  have hse := fsHsSetExt_cost_le (O' := OO_cka) (Γ' := Γ3) (.snd .v4) (.some .v0)
  have huv := unliftVRE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) L (Γ' := Γ5)
    (SM.Engine.vpVR (.snd .v5)) .v1 .v0
  have hrp := realPartyE_cost_le (O' := OO_cka) (Γ' := Γ5)
    (.snd .v5) (SM.Engine.vpΓ (.snd .v5)) (SM.Engine.vpRoot (.snd .v5)) .v3
    (SM.Construction.unliftVRE L (SM.Engine.vpVR (.snd .v5)) .v1 .v0)
  simp only [vpVR_cost, vpΓ_cost, vpRoot_cost, v0_cost, v1_cost, v3_cost, v4_cost, v5_cost,
    ReductionDsl.Expr.cost, Nat.reduceAdd] at hssc hse huv hrp
  simp only [SM.Construction.fsRevealC, PRFPRNG.fsaeadHeaderAdIface,
    vpVS_cost, vpVR_cost, fsHsExt_cost, rangeListC_cost,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, Nat.reduceAdd]
  omega

lemma hooksFSC_costBounded_linear (L B : ℕ) (mo : SM.Construction.Mode) (j : ℕ) :
    HooksCostBounded
      (SM.Construction.hooksFSC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B 1 mo j)
      (300 * L + 20 * (j + 1) + 2 * ReductionDsl.bits mo.tStar +
        2 * ReductionDsl.bits mo.tH + (B + 1) + 2110) where
  startSend_le h ctx p t γv σ r :=
    (fsStartSendC_cost_le (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo j h ctx p t γv σ r).trans
      (by omega)
  startRecv_le h ctx p t γv σ tn :=
    (fsStartRecvC_cost_le (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo j h ctx p t γv σ tn).trans
      (by omega)
  fsSend_le h ctx p t ss hdr m pair :=
    (fsFsSendC_cost_le (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) h ctx p t ss hdr m pair).trans
      (by omega)
  fsRecv_le h ctx p t rs hdr e rec_ :=
    (fsFsRecvC_cost_le (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B h ctx p t rs hdr e rec_).trans (by omega)
  commit_le h ctx p old new := by
    simp only [SM.Construction.hooksFSC, SM.Construction.fsCommitC,
      ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]
    omega
  reveal_le h ctx p vp :=
    (fsRevealC_cost_le (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo h ctx p vp).trans
      (by omega)

lemma hooksFSC_costBounded (L B : ℕ) (mo : SM.Construction.Mode) (j : ℕ) :
    HooksCostBounded
      (SM.Construction.hooksFSC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B 1 mo j)
      (L * L + 300 * L + 20 * (j + 1) + 2 * ReductionDsl.bits mo.tStar +
        2 * ReductionDsl.bits mo.tH + (B + 1) + 2110) where
  startSend_le h ctx p t γv σ r :=
    ((hooksFSC_costBounded_linear L B mo j).startSend_le h ctx p t γv σ r).trans (by omega)
  startRecv_le h ctx p t γv σ tn :=
    ((hooksFSC_costBounded_linear L B mo j).startRecv_le h ctx p t γv σ tn).trans (by omega)
  fsSend_le h ctx p t ss hdr m pair :=
    ((hooksFSC_costBounded_linear L B mo j).fsSend_le h ctx p t ss hdr m pair).trans (by omega)
  fsRecv_le h ctx p t rs hdr e rec_ :=
    ((hooksFSC_costBounded_linear L B mo j).fsRecv_le h ctx p t rs hdr e rec_).trans (by omega)
  commit_le h ctx p old new :=
    ((hooksFSC_costBounded_linear L B mo j).commit_le h ctx p old new).trans (by omega)
  reveal_le h ctx p vp :=
    ((hooksFSC_costBounded_linear L B mo j).reveal_le h ctx p vp).trans (by omega)

lemma initFSEStateC_cost_le (L : ℕ) (mo : SM.Construction.Mode) (j : ℕ) {Γ'}
    (bE : ReductionDsl.Expr OO_cka Γ' .bool) :
    (SM.Construction.initFSEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo j bE).cost ≤
      bE.cost + 200 * L + 12 * (j + 1) +
        2 * ReductionDsl.bits mo.tStar + 2 * ReductionDsl.bits mo.tH + 2010 := by
  have hb0 : ReductionDsl.bits 0 = 1 := rfl
  let Γ0 : List (ReductionDsl.Ty S_cka) := .base .kc :: .base .kr :: .bool :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) :=
    .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) hsTy_fs :: Γ0
  have hrt := rootFSC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo (Γ' := Γ0)
    SM.Construction.fsHsEmptyE (.nat 0)
    (ReductionDsl.Expr.op (O := OO_cka) CKA.CKAOp.lamI .unit)
    (ReductionDsl.Expr.op (O := OO_cka) CKA.CKAOp.prngInit .v1)
  have hext := extOfE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    L j (Γ' := Γ1) (.snd .v0) (.snd (.snd (.fst .v0)))
  simp only [SM.Construction.fsHsEmptyE, SM.Construction.fsHsMk,
    PRFPRNG.prngOps, CKA.ckaOps, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, hb0, Nat.reduceAdd] at hrt hext
  simp only [SM.Construction.initFSEStateC, SM.Engine.mkPartiesE,
    SM.Engine.cGsInitE, SM.Engine.cGsMk, SM.Engine.esMk, vpMk_cost,
    SM.Construction.fsHsEmptyE, SM.Construction.fsHsMk,
    PRFPRNG.fsaeadHeaderAdIface, PRFPRNG.prngSamplers, PRFPRNG.prngOps,
    CKA.ckaSamplers, CKA.ckaOps, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v3_cost, hb0, Nat.reduceAdd]
  omega

end HooksFSCCost

lemma targetsL_bounds {t : ℕ} {tL : Option ℕ} (htL : tL ∈ admissibleLastLeakGuesses (2 + 1) t) :
    tL.getD 0 ≤ t ∧ healEpoch tL ≤ t := by
  simp only [admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at htL
  rcases htL with rfl | ⟨l, hl, rfl⟩
  · simp [healEpoch]
  · simp only [Option.getD_some, healEpoch]
    omega

abbrev fig8StepBound (q qep : ℕ) : ℕ :=
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  20000 * L + L * (3 * ReductionDsl.bits qep + 60) + 3 * B +
    200 * ReductionDsl.bits qep + 350000

lemma fig8_poly_le_ratchetCostBudget (q qep : ℕ) :
    (q + 1) * fig8StepBound q qep ≤ ratchetCostBudget q qep := by
  unfold ratchetCostBudget fig8StepBound
  dsimp only
  set M := maxForwardJumps + ReductionDsl.bits qep
  set L := q + 1
  set B := (q + 1) * (maxForwardJumps + 1)
  have hmfj : maxForwardJumps = 25000 := rfl
  have hbq : 1 ≤ ReductionDsl.bits qep := ReductionDsl.one_le_bits qep
  have hL_pos : 1 ≤ L := by omega
  have hM_lb : 25001 ≤ M := by omega
  have hm_le : maxForwardJumps + 1 ≤ M := by omega
  have hB_le : B ≤ L * M := Nat.mul_le_mul_left L hm_le
  have h20000L : 20000 * L ≤ L * M := by
    calc 20000 * L = L * 20000 := Nat.mul_comm _ _
      _ ≤ L * M := Nat.mul_le_mul_left L (by omega)
  have h3b : 3 * ReductionDsl.bits qep + 60 ≤ 4 * M := by omega
  have hL3b : L * (3 * ReductionDsl.bits qep + 60) ≤ 4 * (L * M) :=
    (Nat.mul_le_mul_left L h3b).trans_eq (by ring)
  have hb_LM : ReductionDsl.bits qep ≤ L * M := by
    calc ReductionDsl.bits qep ≤ M := by omega
      _ = 1 * M := (Nat.one_mul M).symm
      _ ≤ L * M := Nat.mul_le_mul_right M hL_pos
  have h1_LM : 25001 ≤ L * M := by
    calc 25001 = 1 * 25001 := (Nat.one_mul _).symm
      _ ≤ L * M := Nat.mul_le_mul hL_pos hM_lb
  have hsum :
      20000 * L + L * (3 * ReductionDsl.bits qep + 60) + 3 * B +
        200 * ReductionDsl.bits qep + 350000 ≤
        2 ^ 12 * (L * M) := by
    omega
  calc (q + 1) * (20000 * L + L * (3 * ReductionDsl.bits qep + 60) +
          3 * B + 200 * ReductionDsl.bits qep + 350000)
      ≤ (q + 1) * (2 ^ 12 * (L * M)) := Nat.mul_le_mul_left (q + 1) hsum
    _ = 2 ^ 12 * (q + 1) ^ 2 * M := by
      change (q + 1) * (2 ^ 12 * ((q + 1) * M)) = 2 ^ 12 * (q + 1) ^ 2 * M
      ring

lemma add_mul_le_ratchetCostBudget {q qep a b : ℕ}
    (ha : a ≤ fig8StepBound q qep) (hb : b ≤ fig8StepBound q qep) :
    a + q * b ≤ ratchetCostBudget q qep := by
  have hmul : q * b ≤ q * fig8StepBound q qep := Nat.mul_le_mul_left q hb
  have hring : (q + 1) * fig8StepBound q qep = q * fig8StepBound q qep + fig8StepBound q qep := by
    rw [Nat.add_mul, Nat.one_mul]
  have h1 : a + q * b ≤ (q + 1) * fig8StepBound q qep := by omega
  exact h1.trans (fig8_poly_le_ratchetCostBudget q qep)

lemma HooksCostBounded.mono {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    {hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT} {H H' : ℕ}
    (h : H ≤ H') (hhk : HooksCostBounded hk H) : HooksCostBounded hk H' where
  startSend_le hE ctx p t γv σ r := (hhk.startSend_le hE ctx p t γv σ r).trans (by omega)
  startRecv_le hE ctx p t γv σ tn := (hhk.startRecv_le hE ctx p t γv σ tn).trans (by omega)
  fsSend_le hE ctx p t ss hdr m pair := (hhk.fsSend_le hE ctx p t ss hdr m pair).trans (by omega)
  fsRecv_le hE ctx p t rs hdr e rec_ := (hhk.fsRecv_le hE ctx p t rs hdr e rec_).trans (by omega)
  commit_le hE ctx p old new := (hhk.commit_le hE ctx p old new).trans (by omega)
  reveal_le hE ctx p vp := (hhk.reveal_le hE ctx p vp).trans (by omega)

lemma implEC_step_le_fig8StepBound {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (q qep : ℕ)
    (mo : SM.Construction.Mode)
    (htStar : mo.tStar < qep + 2)
    (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hhk : HooksCostBounded hk
      (let L := q + 1
       let B := (q + 1) * (maxForwardJumps + 1)
       320 * L + 10 * ReductionDsl.bits qep + B + 2500)) :
    (SM.Engine.implEC
      (Γ' := [SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
        CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E])
      hk (q + 1) 3 qep maxForwardJumps
      (SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1).cost + 12 ≤
      fig8StepBound q qep := by
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  have hmfj : maxForwardJumps = 25000 := rfl
  have htStar_bits := bits_le_bits_qep_add (x := mo.tStar) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := mo.tL.getD 0) (qep := qep) (by omega)
  have himpl := implEC_cost_le hk
    (320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    L qep maxForwardJumps mo hhk
    (Γ' := [SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
      CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  simp only [v0_cost, v1_cost] at himpl
  have hmul :
      L * (ReductionDsl.bits (mo.tL.getD 0) + 2 * ReductionDsl.bits mo.tStar + 40) ≤
        L * (3 * ReductionDsl.bits qep + 60) :=
    Nat.mul_le_mul_left L (by omega)
  dsimp only [L, B, fig8StepBound] at himpl hmul ⊢
  omega


lemma initCKAEStateC_cost_le
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (mo : SM.Construction.Mode) {Γ'} (bE : ReductionDsl.Expr OO_cka Γ' .bool) :
    (SM.Construction.initCKAEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) mo bE).cost ≤ bE.cost + 500 := by
  have hb0 : ReductionDsl.bits 0 = 1 := rfl
  dsimp only [SM.Construction.initCKAEStateC]
  refine (cost_bind_ret_le_costUB _ _).trans ?_
  simp only [SM.Engine.mkPartiesE, SM.Engine.cGsInitE, SM.Engine.cGsMk,
    SM.Engine.esMk, SM.Engine.vpMk, CKA.ckaOps,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
    hb0, dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]
  omega

end EngineCostHelpers

end Computational.Proofs.ReductionDsl.Fig8SourceCosts
