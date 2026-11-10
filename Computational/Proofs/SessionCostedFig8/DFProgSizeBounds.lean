/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperSim -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedReds2 -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.ProgSizeBounds -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Weighted AST Size Bounds for `DeliverForge` Reductions

Proves compositional `exprSizeW` and `compSizeW` bounds for the paper-semantics and shifted
`DeliverForge` engines, hooks, and reductions against `reductionSizeBudget`.
-/

public section

namespace Computational.Proofs.SessionCostedFig8.DFProgSizeBounds

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open CryptoGames.LibsignalSession (maxForwardJumps)
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open _root_.ReductionDsl (Sig Ops Ty Expr Comp Iface bits reductionSizeBudget)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_succ_le)
open Computational.Proofs.SessionCostedFig8.Bundles
  (exprSizeW compSizeW smOpS smSampS smQueryS ckaOpS ckaSampS ckaQueryS)
open Computational.Proofs.SessionCostedFig8.ProgSizeBounds
  (exprSizeW_var exprSizeW_v0 exprSizeW_v1 exprSizeW_v2 exprSizeW_v3 exprSizeW_v4
   exprSizeW_v5 exprSizeW_v6 exprSizeW_v7 exprSizeW_unit exprSizeW_bool exprSizeW_nat
   exprSizeW_none exprSizeW_nil exprSizeW_add exprSizeW_sub exprSizeW_mulK exprSizeW_divK
   exprSizeW_modK exprSizeW_lt exprSizeW_eqN exprSizeW_not exprSizeW_and exprSizeW_ite
   exprSizeW_pair exprSizeW_fst exprSizeW_snd exprSizeW_inl exprSizeW_inr exprSizeW_some
   exprSizeW_caseOpt exprSizeW_caseSum exprSizeW_letE exprSizeW_op exprSizeW_cons
   exprSizeW_len exprSizeW_take exprSizeW_appendL exprSizeW_findB exprSizeW_anyB
   exprSizeW_mapB exprSizeW_foldrB exprSizeW_tconst exprSizeW_tget exprSizeW_tset
   compSizeW_ret compSizeW_bind compSizeW_ite compSizeW_caseOpt compSizeW_caseSum
   compSizeW_sample compSizeW_query compSizeW_iter compSizeW_findM compSizeW_anyM
   compSizeW_mapM compSizeW_consumeFirstM compSizeW_foldM
   bits_zero bits_one bits_two bits_three bits_four
   bits_le_ratchetCostBudget_of_le_linear bits_qep_le_ratchetCostBudget
   bits_B0_le_ratchetCostBudget size_le_ratchetSizeBudget
   optNatLit_sizeW modeCfgEC_challOKE_sizeW modeCfgEC_injectFullE_sizeW modeCfgEC_challMsgE_sizeW
   corrDoomE_sizeW_le HooksSizeBounded HooksSizeBounded.mono cInTransitE_sizeW_le
   pureEngineExprs_sizeW_le vRecvC_sizeW_le commitEC_sizeW_le implEC_sizeW_le
   hooksCKAC_sizeBounded hooksPRNGC_sizeBounded initCKAEStateC_sizeW_le initPRNGEStateC_sizeW_le
   hooksFSC_sizeBounded initFSEStateC_sizeW_le)

/-! ## Paper challenge simulator -/

section ChallSimDFPaperSize

variable {Key St St₂ Msg Coins RCoins C : Type}
  {init : Party → Key → Option St} {send : St → Msg → Coins → Option (St × C)}
  {receive : St → C → RCoins → Option (St × ℕ × ℕ × Msg)}
  {eqMsg : Msg → Msg → Bool} {eqCt : C → C → Bool} {blank : Msg → Msg}
  {injOK : C → Bool} {stOK : Party → St → Bool} {φ : St → Option St₂}
  {stSort : CryptoGames.SM.SMSort} {sampKey : ProbComp (Option Key)}
  {sampCoins : ProbComp (Option Coins)} {sampRCoins : ProbComp (Option RCoins)}

theorem df_simInitCDF_sizeW_le :
    compSizeW smOpS smSampS smQueryS
      (CryptoGames.SM.simInitCDF (init := init) (send := send) (receive := receive)
        (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
        (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
        (sampRCoins := sampRCoins)) ≤ 1000 := by
  simp only [CryptoGames.SM.simInitCDF, CryptoGames.SM.mMk, smSampS,
    compSizeW_bind, compSizeW_sample, compSizeW_ret, exprSizeW_pair, exprSizeW_unit,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_tconst,
    exprSizeW_v0, bits_zero, Nat.reduceAdd]; omega

theorem df_simHandleC'DFPaper_sizeW_le (K qep : ℕ) :
    compSizeW smOpS smSampS smQueryS
      (CryptoGames.SM.simHandleC'DFPaper (init := init) (send := send) (receive := receive)
        (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
        (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
        (sampRCoins := sampRCoins) K 3 qep) ≤ 50 * bits K + 30 * bits qep + 30000 := by
  have hqep1 : bits (qep + 1) ≤ bits qep + 1 := bits_succ_le qep
  simp only [CryptoGames.SM.simHandleC'DFPaper, CryptoGames.SM.simTransmitC'DFPaper,
    CryptoGames.SM.simChallC'DFPaper, CryptoGames.SM.simDeliverCDF, CryptoGames.SM.simInjectCDF,
    CryptoGames.SM.simCorrCDFPaper, CryptoGames.SM.simDeliverForgeCDF, CryptoGames.SM.mEpMgmtE,
    CryptoGames.SM.mSafeChE, CryptoGames.SM.mLeakE,
    CryptoGames.SM.mRecordE, CryptoGames.SM.mInTransitE, CryptoGames.SM.mDeleteE,
    CryptoGames.SM.mAcceptE, CryptoGames.SM.mChallContainsE, CryptoGames.SM.mCorrAllowedPaperE,
    CryptoGames.SM.mAfterCorrE, CryptoGames.SM.mMk, CryptoGames.SM.mSt, CryptoGames.SM.mB,
    CryptoGames.SM.mWin, CryptoGames.SM.mEpoch, CryptoGames.SM.mIdx, CryptoGames.SM.mTL,
    CryptoGames.SM.mTrans, CryptoGames.SM.mChall, CryptoGames.SM.mComp, CryptoGames.SM.mMaxAcc,
    CryptoGames.SM.mLeaks, CryptoGames.SM.mCorrs, CryptoGames.SM.recPos, CryptoGames.SM.recCt,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, CryptoGames.SM.posEq,
    CryptoGames.SM.pGet, CryptoGames.SM.pSet, CryptoGames.SM.maxAccGet, CryptoGames.SM.maxAccSet,
    CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE, CryptoGames.SM.maxOptE, CryptoGames.SM.leN,
    CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
    CryptoGames.SM.otherE, CryptoGames.SM.isSomeE, smOpS, smQueryS,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
    compSizeW_query, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
    exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, exprSizeW_unit,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_add,
    exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not,
    exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl,
    exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE,
    exprSizeW_op, exprSizeW_cons, exprSizeW_findB, exprSizeW_anyB, exprSizeW_foldrB,
    exprSizeW_tget, exprSizeW_tset, bits_zero, bits_one, bits_two, bits_three,
    Nat.reduceAdd]; omega

set_option maxRecDepth 100000 in
theorem challSimDF'PaperProg_size_le (q qep : ℕ) (hqep : qep ≤ 4096 * q + 100000000) :
    let P := CryptoGames.SM.challSimDF'PaperProg (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q 3 qep
    compSizeW smOpS smSampS smQueryS P.init + compSizeW smOpS smSampS smQueryS P.handle +
      compSizeW smOpS smSampS smQueryS P.finish + 600 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro P
  have hI : compSizeW smOpS smSampS smQueryS P.init ≤ 1000 := df_simInitCDF_sizeW_le
  have hH : compSizeW smOpS smSampS smQueryS P.handle ≤ 50 * bits q + 30 * bits qep + 30000 :=
    df_simHandleC'DFPaper_sizeW_le q qep
  have hF : compSizeW smOpS smSampS smQueryS P.finish ≤ 10 := by
    simp [P, CryptoGames.SM.challSimDF'PaperProg, compSizeW_ret, exprSizeW_v1]
  have hbq : bits q ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  exact size_le_ratchetSizeBudget (C₀ := 32000) (C₁ := 80) (by omega) (by omega) (by omega)

end ChallSimDFPaperSize

/-! ## Engine and hook size bounds -/

section DFEngineSizeHelpers

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
local notation "OO_cka" =>
  CryptoGames.CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

private theorem healedByE_sizeW_2_eq_3 {S' : Sig} {O' : Ops S'} (opS : O'.Op → ℕ) {Γ'}
    (tL : Expr O' Γ' (.opt .nat)) (t : Expr O' Γ' .nat) :
    exprSizeW opS (CryptoGames.SM.healedByE tL 2 t) =
      exprSizeW opS (CryptoGames.SM.healedByE tL 3 t) := by
  simp only [CryptoGames.SM.healedByE, CryptoGames.SM.leN, exprSizeW_letE, exprSizeW_pair,
    exprSizeW_caseOpt, exprSizeW_fst, exprSizeW_snd, exprSizeW_bool, exprSizeW_not,
    exprSizeW_lt, exprSizeW_add, exprSizeW_nat, exprSizeW_v0, exprSizeW_v1, bits_two, bits_three]

private theorem cSafeChE_sizeW_2_eq_3 {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka} {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    exprSizeW opS (CryptoGames.SM.Engine.cSafeChE 2 s p) =
      exprSizeW opS (CryptoGames.SM.Engine.cSafeChE 3 s p) := by
  simp only [CryptoGames.SM.Engine.cSafeChE, exprSizeW_letE, exprSizeW_pair, healedByE_sizeW_2_eq_3]

private theorem cSafeInjE_sizeW_2_eq_3 {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka} {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) :
    exprSizeW opS (CryptoGames.SM.Engine.cSafeInjE 2 s) =
      exprSizeW opS (CryptoGames.SM.Engine.cSafeInjE 3 s) := by
  simp only [CryptoGames.SM.Engine.cSafeInjE, exprSizeW_letE, healedByE_sizeW_2_eq_3]

private theorem cEpMgmtE_sizeW_2_eq_3 {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka} {Γ'}
    (qep : ℕ) (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p bad : Expr O' Γ' .bool) :
    exprSizeW opS (CryptoGames.SM.Engine.cEpMgmtE 2 qep s p bad) =
      exprSizeW opS (CryptoGames.SM.Engine.cEpMgmtE 3 qep s p bad) := by
  simp only [CryptoGames.SM.Engine.cEpMgmtE, exprSizeW_letE, exprSizeW_pair, exprSizeW_ite,
    exprSizeW_and, exprSizeW_not, cSafeChE_sizeW_2_eq_3]

private theorem cRecordE_sizeW_2_eq_3 {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka} {Γ'}
    (L : ℕ) (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool)
    (st' : Expr O' Γ' vpT) (r : Expr O' Γ' CryptoGames.SM.Engine.cRecTy) (isChall : Expr O' Γ' .bool) :
    exprSizeW opS (CryptoGames.SM.Engine.cRecordE L 2 s p st' r isChall) =
      exprSizeW opS (CryptoGames.SM.Engine.cRecordE L 3 s p st' r isChall) := by
  simp only [CryptoGames.SM.Engine.cRecordE, CryptoGames.SM.Engine.cGsMk,
    exprSizeW_letE, exprSizeW_pair, exprSizeW_ite, cSafeChE_sizeW_2_eq_3]

private theorem cTrivialE_sizeW_2_eq_3 {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka} {Γ'}
    (L : ℕ) (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (pos : Expr O' Γ' CryptoGames.SM.posTy) :
    exprSizeW opS (CryptoGames.SM.Engine.cTrivialE L 2 s pos) =
      exprSizeW opS (CryptoGames.SM.Engine.cTrivialE L 3 s pos) := by
  simp only [CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.orE, exprSizeW_letE, exprSizeW_pair,
    exprSizeW_ite, exprSizeW_bool, exprSizeW_and, exprSizeW_not, healedByE_sizeW_2_eq_3]

private theorem authOutE_sizeW_2_eq_3 {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT hsT : Ty S_cka} {Γ'}
    (L : ℕ) (π : CryptoGames.SM.Engine.Policy) (es : Expr O' Γ' (CryptoGames.SM.Engine.esTy vpT hsT)) :
    exprSizeW opS (CryptoGames.SM.Engine.authOutE L 2 π es) =
      exprSizeW opS (CryptoGames.SM.Engine.authOutE L 3 π es) := by
  simp only [CryptoGames.SM.Engine.authOutE, CryptoGames.SM.Engine.cAuthOKE,
    CryptoGames.SM.validGuessE, exprSizeW_letE, exprSizeW_pair, exprSizeW_and, healedByE_sizeW_2_eq_3]

private theorem authOutE_sizeW_le_gen {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT hsT : Ty S_cka}
    (L Δ : ℕ) (hΔ : Δ = 3 ∨ Δ = 2) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr O' Γ' (CryptoGames.SM.Engine.esTy vpT hsT)) :
    exprSizeW opS (CryptoGames.SM.Engine.authOutE L Δ π es) ≤
      exprSizeW opS es + 10 * bits L + 5 * bits (π.tL.getD 0) + 5 * bits π.tStar + 400 := by
  rcases hΔ with rfl | rfl
  · exact (pureEngineExprs_sizeW_le opS L π es).1
  · rw [authOutE_sizeW_2_eq_3]; exact (pureEngineExprs_sizeW_le opS L π es).1

private theorem transmitEC_sizeW_2_eq_3 {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opS : (OO_cka).Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L qep : ℕ) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins))))) :
    compSizeW opS sS qS (CryptoGames.SM.Engine.transmitEC hk L 2 qep π es arg) =
      compSizeW opS sS qS (CryptoGames.SM.Engine.transmitEC hk L 3 qep π es arg) := by
  simp only [CryptoGames.SM.Engine.transmitEC, compSizeW_bind, compSizeW_ret, compSizeW_ite,
    compSizeW_caseOpt, exprSizeW_pair, exprSizeW_some, CryptoGames.SM.Engine.esMk,
    cEpMgmtE_sizeW_2_eq_3, cRecordE_sizeW_2_eq_3]

private theorem challEC_sizeW_2_eq_3 {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opS : (OO_cka).Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L qep : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins)))))) :
    compSizeW opS sS qS (CryptoGames.SM.Engine.challEC hk L 2 qep cfg π es arg) =
      compSizeW opS sS qS (CryptoGames.SM.Engine.challEC hk L 3 qep cfg π es arg) := by
  simp only [CryptoGames.SM.Engine.challEC, compSizeW_bind, compSizeW_ret, compSizeW_ite,
    compSizeW_caseOpt, exprSizeW_pair, exprSizeW_some, CryptoGames.SM.orE, exprSizeW_ite,
    exprSizeW_bool, exprSizeW_not, CryptoGames.SM.Engine.esMk, cEpMgmtE_sizeW_2_eq_3,
    cSafeChE_sizeW_2_eq_3, cRecordE_sizeW_2_eq_3]

private theorem injectEC_sizeW_2_eq_3 {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opS : (OO_cka).Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L qep : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    compSizeW opS sS qS (CryptoGames.SM.Engine.injectEC hk L 2 qep cfg es arg) =
      compSizeW opS sS qS (CryptoGames.SM.Engine.injectEC hk L 3 qep cfg es arg) := by
  simp only [CryptoGames.SM.Engine.injectEC, compSizeW_bind, compSizeW_ret, compSizeW_ite,
    compSizeW_caseOpt, exprSizeW_pair, CryptoGames.SM.orE, exprSizeW_ite, exprSizeW_bool,
    exprSizeW_not, cSafeInjE_sizeW_2_eq_3, cTrivialE_sizeW_2_eq_3]

set_option linter.unusedSimpArgs false in
theorem hdrEqE_sizeW_le (B0 : ℕ) {Γ'}
    (c₁ c₂ : Expr OO_cka Γ' (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprSizeW (ckaOpS B0) (CryptoGames.SM.Engine.hdrEqE c₁ c₂) ≤
      exprSizeW (ckaOpS B0) c₁ + exprSizeW (ckaOpS B0) c₂ + 400 := by
  simp only [CryptoGames.SM.Engine.hdrEqE, CryptoGames.SM.Engine.optTEqE, CryptoGames.CKA.ckaOps,
    ckaOpS, exprSizeW_letE, exprSizeW_pair, exprSizeW_and, exprSizeW_eqN, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_bool, exprSizeW_op, exprSizeW_v0, exprSizeW_v1,
    exprSizeW_var, Nat.reduceAdd]; omega

private theorem cTrivialE_sizeW_le {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka}
    (L Δ : ℕ) (hΔ : Δ = 3 ∨ Δ = 2) {Γ'} (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT))
    (pos : Expr O' Γ' CryptoGames.SM.posTy) :
    exprSizeW opS (CryptoGames.SM.Engine.cTrivialE L Δ s pos) ≤
      exprSizeW opS s + exprSizeW opS pos + 2 * bits L + 200 := by
  rcases hΔ with rfl | rfl <;>
    · simp only [CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.Engine.cCompContainsE,
        CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsTL,
        CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.healedByE, CryptoGames.SM.pGet,
        CryptoGames.SM.posEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch,
        CryptoGames.SM.posIdx, CryptoGames.SM.boolEq, CryptoGames.SM.leN, CryptoGames.SM.orE,
        exprSizeW_letE, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_ite, exprSizeW_bool,
        exprSizeW_not, exprSizeW_and, exprSizeW_anyB, exprSizeW_caseOpt, exprSizeW_add,
        exprSizeW_lt, exprSizeW_eqN, exprSizeW_nat, exprSizeW_tget, exprSizeW_v0, exprSizeW_v1,
        bits_two, bits_three, Nat.reduceAdd]; omega

private theorem cTrivialB1E_sizeW_le_cTrivialE {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka}
    (L tStar : ℕ) {Γ'} (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT))
    (pos : Expr O' Γ' CryptoGames.SM.posTy) :
    exprSizeW opS (CryptoGames.SM.Engine.cTrivialB1E L tStar s pos) ≤
      exprSizeW opS (CryptoGames.SM.Engine.cTrivialE L 3 s pos) +
        4 * exprSizeW opS s + 2 * exprSizeW opS pos + bits tStar + 60 := by
  simp only [CryptoGames.SM.Engine.cTrivialB1E, CryptoGames.SM.orE, CryptoGames.SM.posEpoch,
    CryptoGames.SM.leN, CryptoGames.SM.Engine.cGsEpoch, cTrivialE_sizeW_2_eq_3, exprSizeW_ite,
    exprSizeW_bool, exprSizeW_and, exprSizeW_not, exprSizeW_eqN, exprSizeW_lt, exprSizeW_nat,
    exprSizeW_fst, exprSizeW_snd]; omega

private theorem injectECB1_sizeW_le_injectEC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opS : (OO_cka).Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L qep tStar : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    compSizeW opS sS qS (CryptoGames.SM.Engine.injectECB1 hk L qep tStar cfg es arg) ≤
      compSizeW opS sS qS (CryptoGames.SM.Engine.injectEC hk L 3 qep cfg es arg) + bits tStar + 150 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let dlQ : Ty S_cka := .prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ3 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: .prod esT dlQ :: Γ'
  have htr := cTrivialB1E_sizeW_le_cTrivialE opS L tStar (Γ' := Γ3)
    (CryptoGames.SM.Engine.esG (.fst .v3))
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hs0 : exprSizeW opS (CryptoGames.SM.Engine.esG (Γ' := Γ3) (.fst .v3)) ≤ 10 := by
    simp only [CryptoGames.SM.Engine.esG, exprSizeW_fst, exprSizeW_v3, Nat.reduceAdd]; omega
  have hpos : exprSizeW opS (Expr.pair (O := OO_cka) (Γ := Γ3)
      (CryptoGames.SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))) ≤ 20 := by
    simp only [CryptoGames.SM.otherE, exprSizeW_pair, exprSizeW_not, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_v0, exprSizeW_v3, Nat.reduceAdd]; omega
  simp only [CryptoGames.SM.Engine.injectECB1, CryptoGames.SM.Engine.injectEC, compSizeW_bind,
    compSizeW_ret, compSizeW_ite, compSizeW_caseOpt, exprSizeW_pair, CryptoGames.SM.orE,
    exprSizeW_ite, exprSizeW_bool, exprSizeW_not, cSafeInjE_sizeW_2_eq_3]; omega

private theorem injectECGen_sizeW_le_injectEC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opS : (OO_cka).Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L Δ qep tStar : ℕ) (hΔ : Δ = 3 ∨ Δ = 2) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    compSizeW opS sS qS (CryptoGames.SM.Engine.injectECGen b1 hk L Δ qep tStar cfg es arg) ≤
      compSizeW opS sS qS (CryptoGames.SM.Engine.injectEC hk L 3 qep cfg es arg) + bits tStar + 150 := by
  cases b1 <;> simp only [CryptoGames.SM.Engine.injectECGen, Bool.false_eq_true, ↓reduceIte]
  · rcases hΔ with rfl | rfl
    · omega
    · rw [injectEC_sizeW_2_eq_3]; omega
  · exact injectECB1_sizeW_le_injectEC opS sS qS hk L qep tStar cfg es arg

set_option linter.unusedSimpArgs false in
theorem deliverForgeEC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L qep : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ'
      (.prod .bool (.prod (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
        (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    compSizeW (ckaOpS B0) sS qS
      (CryptoGames.SM.Engine.deliverForgeEC hk L 3 qep
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg) ≤
      60 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) arg) +
        2 * Ho + Hr + 20 * bits L + 5 * bits qep + 5 * bits mo.tStar + 9500 := by
  have hqep1 : bits (qep + 1) ≤ bits qep + 1 := bits_succ_le qep
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dfQ : Ty S_cka := .prod .bool (.prod hdrCtT hdrCtT)
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) := .prod esT dfQ :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ4 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit1 := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0)))
    (.fst (.snd (.snd .v0)))
  have hit2 := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (.fst .v1)) (CryptoGames.SM.otherE (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1)))
  have hhdr := hdrEqE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 (Γ' := Γ1)
    (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_sizeW_le hk Ho Hs Hr hhk (Γ' := Γ1)
    (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1))
    (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1)))
      (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
  have hcm := commitEC_sizeW_le hk Ho Hs Hr L hhk (Γ' := Γ4)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2))
    (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4)))
      (.fst (.snd .v4)))
    (.fst .v0)
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v4)))
      (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.pGet, CryptoGames.SM.otherE, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
    exprSizeW_v3, exprSizeW_v4, exprSizeW_var, exprSizeW_not, exprSizeW_ite, exprSizeW_pair,
    exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_some, exprSizeW_letE, Nat.reduceAdd]
    at hit1 hit2 hhdr hvr hcm
  simp only [CryptoGames.SM.Engine.deliverForgeEC, CryptoGames.SM.Engine.cCompContainsE,
    CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG,
    CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG,
    CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
    CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    CryptoGames.SM.Engine.cRecPos, modeCfgEC_injectFullE_sizeW, CryptoGames.SM.healedByE,
    CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE,
    CryptoGames.SM.leN, CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender,
    CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
    exprSizeW_v3, exprSizeW_v4, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_add, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and,
    exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr,
    exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_anyB, exprSizeW_tget,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, bits_zero, bits_one, bits_two,
    bits_three, Nat.reduceAdd]
  split_ifs <;> omega

private theorem deliverForgeEC_sizeW_2_eq_3 {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opS : (OO_cka).Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L qep : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) {Γ'}
    (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ'
      (.prod .bool (.prod (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
        (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    compSizeW opS sS qS (CryptoGames.SM.Engine.deliverForgeEC hk L 2 qep cfg es arg) =
      compSizeW opS sS qS (CryptoGames.SM.Engine.deliverForgeEC hk L 3 qep cfg es arg) := by
  simp only [CryptoGames.SM.Engine.deliverForgeEC, compSizeW_bind, compSizeW_ret, compSizeW_ite,
    compSizeW_caseOpt, exprSizeW_pair, cTrivialE_sizeW_2_eq_3]

private theorem deliverForgeECB1_sizeW_le_deliverForgeEC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opS : (OO_cka).Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L qep tStar : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) {Γ'}
    (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ'
      (.prod .bool (.prod (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
        (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    compSizeW opS sS qS (CryptoGames.SM.Engine.deliverForgeECB1 hk L qep tStar cfg es arg) ≤
      compSizeW opS sS qS (CryptoGames.SM.Engine.deliverForgeEC hk L 3 qep cfg es arg) +
        bits tStar + 150 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dfQ : Ty S_cka := .prod .bool (.prod hdrCtT hdrCtT)
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ4 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT ::
    CryptoGames.SM.Engine.cRecTy :: .prod esT dfQ :: Γ'
  have htr := cTrivialB1E_sizeW_le_cTrivialE opS L tStar (Γ' := Γ4)
    (CryptoGames.SM.Engine.esG (.fst .v4))
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v4)))
      (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hs0 : exprSizeW opS (CryptoGames.SM.Engine.esG (Γ' := Γ4) (.fst .v4)) ≤ 10 := by
    simp only [CryptoGames.SM.Engine.esG, exprSizeW_fst, exprSizeW_v4, Nat.reduceAdd]; omega
  have hpos : exprSizeW opS (Expr.pair (O := OO_cka) (Γ := Γ4)
      (CryptoGames.SM.otherE (.fst (.snd .v4)))
      (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))) ≤ 20 := by
    simp only [CryptoGames.SM.otherE, exprSizeW_pair, exprSizeW_not, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_v0, exprSizeW_v4, Nat.reduceAdd]; omega
  simp only [CryptoGames.SM.Engine.deliverForgeECB1, CryptoGames.SM.Engine.deliverForgeEC,
    compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt, exprSizeW_pair]
  omega

theorem deliverForgeECGen_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L Δ qep tStar : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hΔ : Δ = 3 ∨ Δ = 2) (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ'
      (.prod .bool (.prod (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
        (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    compSizeW (ckaOpS B0) sS qS
      (CryptoGames.SM.Engine.deliverForgeECGen b1 hk L Δ qep tStar
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg) ≤
      60 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) arg) +
        2 * Ho + Hr + 20 * bits L + 5 * bits qep + 5 * bits mo.tStar + 5 * bits tStar + 10000 := by
  have hdf := deliverForgeEC_sizeW_le hk Ho Hs Hr L qep mo hhk es arg
  cases b1
  · simp only [CryptoGames.SM.Engine.deliverForgeECGen, Bool.false_eq_true, ↓reduceIte]
    rcases hΔ with rfl | rfl
    · omega
    · rw [deliverForgeEC_sizeW_2_eq_3]; omega
  · simp only [CryptoGames.SM.Engine.deliverForgeECGen, ↓reduceIte]
    have hb1 := deliverForgeECB1_sizeW_le_deliverForgeEC (ckaOpS B0) sS qS hk L qep tStar
      (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg
    omega

private theorem cCorrAllowedPaperE_sizeW_le {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka}
    (L : ℕ) {Γ'} (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    exprSizeW opS (CryptoGames.SM.Engine.cCorrAllowedPaperE L s p) ≤
      exprSizeW opS (CryptoGames.SM.Engine.cCorrAllowedE L s p) := by
  simp only [CryptoGames.SM.Engine.cCorrAllowedPaperE, CryptoGames.SM.Engine.cCorrAllowedE,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.boolEq, CryptoGames.SM.posSender,
    CryptoGames.SM.otherE, exprSizeW_letE, exprSizeW_pair, exprSizeW_not, exprSizeW_and,
    exprSizeW_anyB, exprSizeW_ite, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd]; omega

private theorem corrECPaper_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opS : (OO_cka).Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L : ℕ) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO_cka Γ' .bool) :
    compSizeW opS sS qS (CryptoGames.SM.Engine.corrECPaper hk L π es p) ≤
      compSizeW opS sS qS (CryptoGames.SM.Engine.corrEC hk L π es p) := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  have hca := cCorrAllowedPaperE_sizeW_le opS L (Γ' := .prod esT .bool :: Γ')
    (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
  simp only [CryptoGames.SM.Engine.corrECPaper, CryptoGames.SM.Engine.corrEC, CryptoGames.SM.orE,
    compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt, exprSizeW_pair, exprSizeW_ite,
    exprSizeW_bool, exprSizeW_not]; omega

private theorem implECPaper_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opS : (OO_cka).Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L Δ qep maxSkip : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    compSizeW opS sS qS (CryptoGames.SM.Engine.implECPaper hk L Δ qep maxSkip cfg π es q) ≤
      compSizeW opS sS qS (CryptoGames.SM.Engine.implEC hk L Δ qep maxSkip cfg π es q) := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  have hcr := corrECPaper_sizeW_le opS sS qS hk L π (Γ' := .bool :: .prod esT smqT :: Γ') (.fst .v1) .v0
  simp only [CryptoGames.SM.Engine.implECPaper, CryptoGames.SM.Engine.implEC,
    compSizeW_bind, compSizeW_ret, compSizeW_caseSum, exprSizeW_pair]; omega

theorem implECDFPaper_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L qep maxSkip : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    compSizeW (ckaOpS B0) sS qS
      (CryptoGames.SM.Engine.implECDFPaper hk L 3 qep maxSkip
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es q) ≤
      60 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) q) +
        9 * Ho + 2 * Hs + 3 * Hr + 100 * bits L + 25 * bits qep + 10 * bits maxSkip +
        20 * bits (mo.tL.getD 0) + 30 * bits mo.tStar + 42000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let smqdfT := CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let dfQ : Ty S_cka := .prod .bool (.prod (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
    (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))
  have hp := implECPaper_sizeW_le (ckaOpS B0) sS qS hk L 3 qep maxSkip
    (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy (Γ' := smqT :: .prod esT smqdfT :: Γ') (.fst .v1) .v0
  have him := implEC_sizeW_le hk Ho Hs Hr L qep maxSkip mo hhk (Γ' := smqT :: .prod esT smqdfT :: Γ') (.fst .v1) .v0
  have hdf := deliverForgeEC_sizeW_le hk Ho Hs Hr L qep mo hhk (Γ' := dfQ :: .prod esT smqdfT :: Γ') (.fst .v1) .v0
  simp only [exprSizeW_fst, exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd] at him hdf
  simp only [CryptoGames.SM.Engine.implECDFPaper, compSizeW_bind, compSizeW_ret, compSizeW_caseSum,
    exprSizeW_pair, exprSizeW_inl, exprSizeW_inr, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0,
    Nat.reduceAdd]; omega

private theorem cAfterCorrShiftedE_sizeW_le_cAfterCorrE {O' : Ops S_cka} (opS : O'.Op → ℕ)
    {vpT : Ty S_cka} (L l : ℕ) {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    exprSizeW opS (CryptoGames.SM.Engine.cAfterCorrShiftedE L l s p) ≤
      exprSizeW opS (CryptoGames.SM.Engine.cAfterCorrE L s p) + (40 * bits l + 1000) := by
  have hl1 := bits_mono (Nat.sub_le l 1)
  simp only [CryptoGames.SM.Engine.cAfterCorrShiftedE, CryptoGames.SM.Engine.cAfterCorrE,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cLeakE,
    CryptoGames.SM.maxOptE, CryptoGames.SM.maxN, CryptoGames.SM.leN,
    CryptoGames.SM.boolEq, CryptoGames.SM.otherE, CryptoGames.SM.pGet,
    CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.posSender,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
    CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    exprSizeW_letE, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_ite,
    exprSizeW_not, exprSizeW_and, exprSizeW_lt, exprSizeW_eqN, exprSizeW_add, exprSizeW_nat,
    exprSizeW_some, exprSizeW_caseOpt, exprSizeW_cons, exprSizeW_foldrB,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, bits_one,
    Nat.reduceAdd]
  omega

private theorem leakDoomE_sizeW_le_add {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka}
    (L : ℕ) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (g s₁ s₂ : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) {d : ℕ}
    (hs : exprSizeW opS s₁ ≤ exprSizeW opS s₂ + d) :
    exprSizeW opS (CryptoGames.SM.Engine.leakDoomE L π g s₁) ≤
      exprSizeW opS (CryptoGames.SM.Engine.leakDoomE L π g s₂) + d := by
  simp only [CryptoGames.SM.Engine.leakDoomE, exprSizeW_letE, exprSizeW_pair]
  omega

private theorem corrECShiftedPaper_sizeW_le_corrEC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opS : (OO_cka).Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L l : ℕ) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO_cka Γ' .bool) :
    compSizeW opS sS qS (CryptoGames.SM.Engine.corrECShiftedPaper hk L l π es p) ≤
      compSizeW opS sS qS (CryptoGames.SM.Engine.corrEC hk L π es p) + 80 * bits l + 2500 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let Γ0 : List (Ty S_cka) := .prod esT .bool :: Γ'
  let psT := CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ2 : List (Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ0
  have hca := cCorrAllowedPaperE_sizeW_le opS L (Γ' := Γ0) (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hac0 := cAfterCorrShiftedE_sizeW_le_cAfterCorrE opS L l (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hld := leakDoomE_sizeW_le_add opS L π (Γ' := Γ0) (CryptoGames.SM.Engine.esG (.fst .v0)) _ _ hac0
  have hac2 := cAfterCorrShiftedE_sizeW_le_cAfterCorrE opS L l (Γ' := Γ2)
    (CryptoGames.SM.Engine.esG (.fst .v2)) (.snd .v2)
  simp only [CryptoGames.SM.Engine.corrECShiftedPaper, CryptoGames.SM.Engine.corrEC,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.orE, compSizeW_bind, compSizeW_ret, compSizeW_ite,
    compSizeW_caseOpt, exprSizeW_pair, exprSizeW_some, exprSizeW_ite, exprSizeW_bool,
    exprSizeW_not]; omega

private theorem implECShiftedPaperGen_sizeW_le_implEC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opS : (OO_cka).Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L l Δ qep maxSkip tStar : ℕ) (hΔ : Δ = 3 ∨ Δ = 2)
    (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    compSizeW opS sS qS
      (CryptoGames.SM.Engine.implECShiftedPaperGen b1 hk L l Δ qep maxSkip tStar cfg π es q) ≤
      compSizeW opS sS qS (CryptoGames.SM.Engine.implEC hk L 3 qep maxSkip cfg π es q) +
        80 * bits l + bits tStar + 3000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
  let Γ_base : List (Ty S_cka) := .prod esT smqT :: Γ'
  let Γ_s1 : List (Ty S_cka) := .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γ_base
  have hij := injectECGen_sizeW_le_injectEC opS sS qS b1 hk L Δ qep tStar hΔ cfg
    (Γ' := dlQ :: Γ_s1) (.fst .v2) .v0
  have hcr := corrECShiftedPaper_sizeW_le_corrEC opS sS qS hk L l π (Γ' := .bool :: Γ_base) (.fst .v1) .v0
  rcases hΔ with rfl | rfl
  · simp only [CryptoGames.SM.Engine.implECShiftedPaperGen, CryptoGames.SM.Engine.implEC,
      compSizeW_bind, compSizeW_ret, compSizeW_caseSum, exprSizeW_pair]; omega
  · simp only [CryptoGames.SM.Engine.implECShiftedPaperGen, CryptoGames.SM.Engine.implEC,
      compSizeW_bind, compSizeW_ret, compSizeW_caseSum, exprSizeW_pair,
      transmitEC_sizeW_2_eq_3, challEC_sizeW_2_eq_3]; omega

theorem implECDFShiftedPaperGen_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L l Δ qep maxSkip tStar : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hΔ : Δ = 3 ∨ Δ = 2) (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    compSizeW (ckaOpS B0) sS qS
      (CryptoGames.SM.Engine.implECDFShiftedPaperGen b1 hk L l Δ qep maxSkip tStar
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es q) ≤
      60 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) q) +
        9 * Ho + 2 * Hs + 3 * Hr + 100 * bits L + 80 * bits l + 25 * bits qep +
        10 * bits maxSkip + 20 * bits (mo.tL.getD 0) + 30 * bits mo.tStar +
        6 * bits tStar + 46000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let smqdfT := CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dfQ : Ty S_cka := .prod .bool (.prod hdrCtT hdrCtT)
  have hs := implECShiftedPaperGen_sizeW_le_implEC (ckaOpS B0) sS qS b1 hk L l Δ qep maxSkip
    tStar hΔ (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy
    (Γ' := smqT :: .prod esT smqdfT :: Γ') (.fst .v1) .v0
  have him := implEC_sizeW_le hk Ho Hs Hr L qep maxSkip mo hhk
    (Γ' := smqT :: .prod esT smqdfT :: Γ') (.fst .v1) .v0
  have hdf := deliverForgeECGen_sizeW_le b1 hk Ho Hs Hr L Δ qep tStar mo hΔ hhk
    (Γ' := dfQ :: .prod esT smqdfT :: Γ') (.fst .v1) .v0
  simp only [exprSizeW_fst, exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd] at him hdf
  simp only [CryptoGames.SM.Engine.implECDFShiftedPaperGen, compSizeW_bind, compSizeW_ret,
    compSizeW_caseSum, exprSizeW_pair, exprSizeW_inl, exprSizeW_inr, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_v0, Nat.reduceAdd]
  omega

theorem hooksCKAShiftedC_sizeBounded (B0 B l tStar : ℕ) :
    HooksSizeBounded B0 ckaSampS ckaQueryS
      (CryptoGames.SM.Construction.hooksCKAShiftedC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B l tStar)
      (10 * bits l + 5 * bits tStar + 6000) 2000 (3 * bits B0 + 2 * bits B + 2000) where
  startSend_le h ctx p t γv σ r := by
    have hl1 := bits_succ_le l
    have hl2 : bits (l + 2) ≤ bits (l + 1) + 1 := bits_succ_le (l + 1)
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC,
      CryptoGames.SM.Construction.ckaShiftedStartSendC,
      CryptoGames.SM.Construction.ckaShiftedSetCache,
      CryptoGames.SM.Construction.ckaShiftedSetΓPre,
      CryptoGames.SM.pSet, CryptoGames.SM.leN,
      ckaOpS, ckaSampS, ckaQueryS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
      exprSizeW_unit, exprSizeW_nat,
      exprSizeW_add, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not,
      exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_some,
      exprSizeW_letE, exprSizeW_op, exprSizeW_tset,
      compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_sample,
      compSizeW_query, bits_one, Nat.reduceAdd]
    omega
  startRecv_le h ctx p t γv σ tn := by
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC,
      CryptoGames.SM.Construction.ckaShiftedStartRecvC,
      CryptoGames.SM.Construction.ckaStartRecvAnsE, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_bool,
      exprSizeW_nat, exprSizeW_eqN, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_none, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE,
      exprSizeW_op, exprSizeW_tget, compSizeW_ret, Nat.reduceAdd]
    omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC,
      CryptoGames.SM.Construction.ckaShiftedFsSendC, ckaOpS,
      exprSizeW_pair, exprSizeW_some, exprSizeW_op, compSizeW_ret]
    omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC,
      CryptoGames.SM.Construction.ckaShiftedFsRecvC, ckaOpS,
      exprSizeW_pair, exprSizeW_some, exprSizeW_op, compSizeW_ret]
    omega
  commit_le h ctx p old new := by
    have hl1 := bits_succ_le l
    have hl2 : bits (l + 2) ≤ bits (l + 1) + 1 := bits_succ_le (l + 1)
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC,
      CryptoGames.SM.Construction.ckaShiftedCommitC,
      CryptoGames.SM.Construction.ckaShiftedSetΓPre,
      CryptoGames.SM.pSet, CryptoGames.SM.isSomeE, CryptoGames.SM.leN,
      CryptoGames.SM.Engine.vpSetΓ, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId,
      CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR,
      CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat,
      ckaQueryS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
      exprSizeW_bool, exprSizeW_nat, exprSizeW_add, exprSizeW_lt,
      exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_none, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE,
      compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_query,
      bits_one, Nat.reduceAdd]
    omega
  reveal_le h ctx p vp := by
    simp only [CryptoGames.SM.Construction.hooksCKAShiftedC,
      CryptoGames.SM.Construction.ckaShiftedRevealC,
      CryptoGames.SM.Engine.realPartyE, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId,
      CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR,
      CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat,
      CryptoGames.SM.leN, CryptoGames.SM.pGet, ckaQueryS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
      exprSizeW_nat, exprSizeW_add, exprSizeW_lt, exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_none, exprSizeW_some, exprSizeW_letE,
      compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_query,
      bits_one, Nat.reduceAdd]
    omega

theorem initCKAShiftedEStateC_sizeW_le (B0 l : ℕ) {Γ'} (bE : Expr OO_cka Γ' .bool) :
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS
      (CryptoGames.SM.Construction.initCKAShiftedEStateC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) l bE) ≤
      exprSizeW (ckaOpS B0) bE + 9000 := by
  simp only [CryptoGames.SM.Construction.initCKAShiftedEStateC,
    CryptoGames.SM.Engine.mkPartiesE, CryptoGames.SM.Engine.cGsInitE,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.vpMk,
    ckaOpS, ckaSampS, ckaQueryS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_unit,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_some, exprSizeW_letE, exprSizeW_op, exprSizeW_tconst,
    exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_sample,
    compSizeW_query, bits_zero, Nat.reduceAdd]
  omega

theorem hooksFSC_zero_sizeBounded (B0 L B : ℕ) (mo : CryptoGames.SM.Construction.Mode) (j : ℕ) :
    HooksSizeBounded B0 ckaSampS ckaQueryS
      (CryptoGames.SM.Construction.hooksFSC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B 0 mo j)
      (40 * bits L + 20 * bits j + 6 * bits mo.tStar + 6 * bits mo.tH + 14000) 2000
      (6 * bits B0 + 4 * bits B + 4 * bits L + 5000) where
  startSend_le hE ctxE pE tE γE σE rE :=
    (hooksFSC_sizeBounded B0 L B mo j).startSend_le hE ctxE pE tE γE σE rE
  startRecv_le hE ctxE pE tE γE σE tnE :=
    (hooksFSC_sizeBounded B0 L B mo j).startRecv_le hE ctxE pE tE γE σE tnE
  fsSend_le hE ctxE pE tE ssvE hdrE mE pairE := by
    simp only [CryptoGames.SM.Construction.hooksFSC, CryptoGames.SM.Construction.fsFsSendC,
      CryptoGames.SM.Engine.cSafeChE, CryptoGames.SM.Construction.fsHsSetSCorr,
      CryptoGames.SM.Construction.fsHsSetCountTrans, CryptoGames.SM.Construction.fsHsSetExt,
      CryptoGames.SM.Construction.fsHsMk, CryptoGames.SM.Construction.fsHsCache,
      CryptoGames.SM.Construction.fsHsTable, CryptoGames.SM.Construction.fsHsSessions,
      CryptoGames.SM.Construction.fsHsTrans, CryptoGames.SM.Construction.fsHsCount,
      CryptoGames.SM.Construction.fsHsSCorr, CryptoGames.SM.Construction.fsHsExt,
      CryptoGames.SM.healedByE, CryptoGames.SM.leN, CryptoGames.SM.pGet,
      CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsEpoch, ckaOpS, ckaQueryS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_unit,
      exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_add, exprSizeW_lt, exprSizeW_not,
      exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some,
      exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op, exprSizeW_cons, compSizeW_ret, compSizeW_bind,
      compSizeW_ite, compSizeW_caseOpt, compSizeW_query, bits_one, bits_two, Nat.reduceAdd]
    omega
  fsRecv_le hE ctxE pE tE rsvE hdrE eE recE :=
    (hooksFSC_sizeBounded B0 L B mo j).fsRecv_le hE ctxE pE tE rsvE hdrE eE recE
  commit_le hE ctxE pE old new :=
    (hooksFSC_sizeBounded B0 L B mo j).commit_le hE ctxE pE old new
  reveal_le hE ctxE pE vpE :=
    (hooksFSC_sizeBounded B0 L B mo j).reveal_le hE ctxE pE vpE

private theorem hooksFSC_gen_sizeBounded (B0 L B Δcka : ℕ) (hΔ : Δcka = 1 ∨ Δcka = 0)
    (mo : CryptoGames.SM.Construction.Mode) (j : ℕ) :
    HooksSizeBounded B0 ckaSampS ckaQueryS
      (CryptoGames.SM.Construction.hooksFSC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j)
      (40 * bits L + 20 * bits j + 6 * bits mo.tStar + 6 * bits mo.tH + 14000) 2000
      (6 * bits B0 + 4 * bits B + 4 * bits L + 5000) := by
  rcases hΔ with rfl | rfl
  · exact hooksFSC_sizeBounded B0 L B mo j
  · exact hooksFSC_zero_sizeBounded B0 L B mo j

/-! ## Top-level reduction size bounds -/

private theorem healEpoch_le_add_three {tL : Option ℕ} {t : ℕ} (h : tL.getD 0 ≤ t) :
    CryptoGames.SM.Construction.healEpoch tL ≤ t + 3 := by
  cases tL <;> simp [CryptoGames.SM.Construction.healEpoch] at h ⊢; omega

private theorem bind_ret_pair_unit_sizeW_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {opS : O'.Op → ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {Γ' : List (Ty S')} {σ : Ty S'} {c : Comp O' I' Γ' σ} {K M : ℕ}
    (hc : compSizeW opS sS qS c ≤ K) (hM : K + 5 ≤ M) :
    compSizeW opS sS qS (Comp.bind c (Comp.ret (.pair .unit .v0))) ≤ M := by
  simp only [compSizeW_bind, compSizeW_ret, exprSizeW_pair, exprSizeW_unit, exprSizeW_v0]
  omega

private theorem authOut_ret_gen_sizeW_le {O' : Ops S_cka} {ι : Type} {TSpec : OracleSpec ι}
    {I' : Iface S_cka TSpec} {vpT hsT : Ty S_cka}
    (opS : O'.Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (q qep Δ : ℕ) (hΔ : Δ = 3 ∨ Δ = 2) (mo : CryptoGames.SM.Construction.Mode)
    (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hqep : qep ≤ 4096 * q + 100000000) :
    compSizeW opS sS qS
      (Comp.ret (I := I') (Γ := [CryptoGames.SM.Engine.esTy vpT hsT, .bool])
        (CryptoGames.SM.Engine.authOutE (q + 1) Δ mo.policy .v0)) ≤
      20 * bits (ratchetCostBudget q qep) + 1000 := by
  have h0 := authOutE_sizeW_le_gen opS (q + 1) Δ hΔ mo.policy
    (Γ' := [CryptoGames.SM.Engine.esTy vpT hsT, .bool]) .v0
  have hpolL : mo.policy.tL = mo.tL := rfl
  have hpolS : mo.policy.tStar = mo.tStar := rfl
  rw [hpolL, hpolS] at h0
  simp only [exprSizeW_v0] at h0
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtS : bits mo.tStar ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (mo.tL.getD 0) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  simp only [compSizeW_ret]
  omega

private theorem implECDFPaper_sizeW_le_ratchet {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (q qep : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hqep : qep ≤ 4096 * q + 100000000)
    (hhk : HooksSizeBounded ((q + 1) * (maxForwardJumps + 1)) sS qS hk
      (80 * bits (ratchetCostBudget q qep) + 15000) 2000
      (14 * bits (ratchetCostBudget q qep) + 5000)) :
    compSizeW (ckaOpS ((q + 1) * (maxForwardJumps + 1))) sS qS
      (CryptoGames.SM.Engine.implECDFPaper
        (Γ' := [CryptoGames.SM.Engine.esTy
          (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
          CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
        hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1) ≤
      1050 * bits (ratchetCostBudget q qep) + 250000 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  have h0 := implECDFPaper_sizeW_le hk (80 * bits (ratchetCostBudget q qep) + 15000) 2000
    (14 * bits (ratchetCostBudget q qep) + 5000) (q + 1) qep maxForwardJumps mo hhk
    (Γ' := [CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
      CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  simp only [exprSizeW_v0, exprSizeW_v1] at h0
  have hbL := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := q + 1) (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  have hbm : bits maxForwardJumps ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by unfold maxForwardJumps; omega)
  have hbtS := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := mo.tStar) (by omega)
  have hbtL := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := mo.tL.getD 0) (by omega)
  omega

private theorem implECDFShiftedPaperGen_sizeW_le_ratchet {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (q qep l Δ tStar : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hΔ : Δ = 3 ∨ Δ = 2) (htStar : tStar < qep + 2) (hl : l ≤ tStar)
    (hmoS : mo.tStar ≤ tStar) (hmoL : mo.tL.getD 0 ≤ tStar) (hqep : qep ≤ 4096 * q + 100000000)
    (hhk : HooksSizeBounded ((q + 1) * (maxForwardJumps + 1)) sS qS hk
      (80 * bits (ratchetCostBudget q qep) + 15000) 2000
      (14 * bits (ratchetCostBudget q qep) + 5000)) :
    compSizeW (ckaOpS ((q + 1) * (maxForwardJumps + 1))) sS qS
      (CryptoGames.SM.Engine.implECDFShiftedPaperGen
        (Γ' := [CryptoGames.SM.Engine.esTy
          (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
          CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
        b1 hk (q + 1) l Δ qep maxForwardJumps tStar
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1) ≤
      1050 * bits (ratchetCostBudget q qep) + 250000 := by
  have h0 := implECDFShiftedPaperGen_sizeW_le b1 hk (80 * bits (ratchetCostBudget q qep) + 15000) 2000
    (14 * bits (ratchetCostBudget q qep) + 5000) (q + 1) l Δ qep maxForwardJumps tStar mo hΔ hhk
    (Γ' := [CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
      CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  simp only [exprSizeW_v0, exprSizeW_v1] at h0
  have hbL := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := q + 1) (by omega)
  have hbl := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := l) (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  have hbm : bits maxForwardJumps ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by unfold maxForwardJumps; omega)
  have hbt := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := tStar) (by omega)
  have hbtS := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := mo.tStar) (by omega)
  have hbtL := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := mo.tL.getD 0) (by omega)
  omega

theorem redCKAAuthDFShiftedPaperGenProg_size_le
    (q qep Δcka l tStarH t : ℕ) (hΔ : 2 + Δcka = 3 ∨ 2 + Δcka = 2)
    (ht : t < qep + 2) (hl : l ≤ t) (htH : tStarH ≤ t) (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperGenProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
      (sampK := sampK) (q + 1) B Δcka qep maxForwardJumps l tStarH t
    compSizeW (ckaOpS B) ckaSampS ckaQueryS P.init +
      compSizeW (ckaOpS B) ckaSampS ckaQueryS P.handle +
      compSizeW (ckaOpS B) ckaSampS ckaQueryS P.finish + 600 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have hbl := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := l) (by omega)
  have hbtH := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := tStarH) (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have htL : mo.tL.getD 0 ≤ t := by dsimp [mo]; omega
  have hi : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.init ≤ 10000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperGenProg]
    refine bind_ret_pair_unit_sizeW_le (initCKAShiftedEStateC_sizeW_le B l (.bool false)) ?_
    simp only [exprSizeW_bool]; omega
  have hh : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.handle ≤
      1050 * bits (ratchetCostBudget q qep) + 250000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperGenProg]
    exact implECDFShiftedPaperGen_sizeW_le_ratchet _ _ q qep l (2 + Δcka) t mo hΔ ht hl le_rfl
      htL hqep ((hooksCKAShiftedC_sizeBounded B B l tStarH).mono (by omega) le_rfl (by omega))
  have hf : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 :=
    authOut_ret_gen_sizeW_le _ _ _ q qep (2 + Δcka) hΔ mo ht htL hqep
  exact size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by omega) (by omega) (by omega)

theorem redPRNGAuthDFShiftedPaperGenProg_size_le
    (q qep Δcka l t : ℕ) (authH : Bool) (hΔ : 2 + Δcka = 3 ∨ 2 + Δcka = 2)
    (ht : t < qep + 2) (hl : l ≤ t) (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperGenProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
      (sampK := sampK) (q + 1) B Δcka qep maxForwardJumps l t authH
    compSizeW (ckaOpS B) ckaSampS ckaQueryS P.init +
      compSizeW (ckaOpS B) ckaSampS ckaQueryS P.handle +
      compSizeW (ckaOpS B) ckaSampS ckaQueryS P.finish + 600 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  let moH : CryptoGames.SM.Construction.Mode := ⟨authH, some (l - 1), t⟩
  have hbt := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := t) (by omega)
  have hheal : CryptoGames.SM.Construction.healEpoch (some (l - 1)) ≤ t + 3 := healEpoch_le_add_three (by simp; omega)
  have hbtH : bits moH.tH ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (x := CryptoGames.SM.Construction.healEpoch (some (l - 1))) (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have htL : mo.tL.getD 0 ≤ t := by dsimp [mo]; omega
  have hi : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.init ≤
      20 * bits (ratchetCostBudget q qep) + 8000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperGenProg]
    refine bind_ret_pair_unit_sizeW_le (initPRNGEStateC_sizeW_le B moH (.bool false)) ?_
    simp only [exprSizeW_bool]; dsimp [moH] at *; omega
  have hh : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.handle ≤
      1050 * bits (ratchetCostBudget q qep) + 250000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperGenProg]
    exact implECDFShiftedPaperGen_sizeW_le_ratchet _ _ q qep l (2 + Δcka) t mo hΔ ht hl le_rfl
      htL hqep ((hooksPRNGC_sizeBounded B B moH).mono (by dsimp [moH] at *; omega) le_rfl (by omega))
  have hf : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 :=
    authOut_ret_gen_sizeW_le _ _ _ q qep (2 + Δcka) hΔ mo ht htL hqep
  exact size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by omega) (by omega) (by omega)

theorem redFSAuthDFShiftedPaperGenProg_size_le
    (q qep Δcka j l t : ℕ) (authH : Bool) (hΔ : Δcka = 1 ∨ Δcka = 0)
    (ht : t < qep + 2) (hl : l ≤ t) (hj : j < q) (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
      (sampK := sampK) (q + 1) B Δcka qep maxForwardJumps j l t authH
    compSizeW (ckaOpS B) ckaSampS ckaQueryS P.init +
      compSizeW (ckaOpS B) ckaSampS ckaQueryS P.handle +
      compSizeW (ckaOpS B) ckaSampS ckaQueryS P.finish + 600 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  let moH : CryptoGames.SM.Construction.Mode := ⟨authH, some (l - 1), t⟩
  have hΔ2 : 2 + Δcka = 3 ∨ 2 + Δcka = 2 := by omega
  have hbL := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := q + 1) (by omega)
  have hbj := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := j) (by omega)
  have hbt := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := t) (by omega)
  have hheal : CryptoGames.SM.Construction.healEpoch (some (l - 1)) ≤ t + 3 := healEpoch_le_add_three (by simp; omega)
  have hbtH : bits moH.tH ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (x := CryptoGames.SM.Construction.healEpoch (some (l - 1))) (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have htL : mo.tL.getD 0 ≤ t := by dsimp [mo]; omega
  have hi : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.init ≤
      45 * bits (ratchetCostBudget q qep) + 15000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg]
    refine bind_ret_pair_unit_sizeW_le (initFSEStateC_sizeW_le B (q + 1) moH j (.bool false)) ?_
    simp only [exprSizeW_bool]; dsimp [moH] at *; omega
  have hh : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.handle ≤
      1050 * bits (ratchetCostBudget q qep) + 250000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg]
    exact implECDFShiftedPaperGen_sizeW_le_ratchet _ _ q qep l (2 + Δcka) t mo hΔ2 ht hl le_rfl
      htL hqep ((hooksFSC_gen_sizeBounded B (q + 1) B Δcka hΔ moH j).mono
        (by dsimp [moH] at *; omega) le_rfl (by omega))
  have hf : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.finish ≤ 100 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg]
    simp only [compSizeW_sample, exprSizeW_unit, ckaSampS]; omega
  exact size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by omega) (by omega) (by omega)

theorem redCKAAuthDFPaperProg_size_le
    (q qep t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redCKAAuthDFPaperProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
      (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    compSizeW (ckaOpS B) ckaSampS ckaQueryS P.init +
      compSizeW (ckaOpS B) ckaSampS ckaQueryS P.handle +
      compSizeW (ckaOpS B) ckaSampS ckaQueryS P.finish + 600 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have hbt := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := t) (by omega)
  have hheal : CryptoGames.SM.Construction.healEpoch tL ≤ t + 3 := healEpoch_le_add_three htL
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (x := CryptoGames.SM.Construction.healEpoch tL) (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.init ≤ 10000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthDFPaperProg]
    refine bind_ret_pair_unit_sizeW_le (initCKAEStateC_sizeW_le B mo (.bool false)) ?_
    simp only [exprSizeW_bool]; omega
  have hh : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.handle ≤
      1050 * bits (ratchetCostBudget q qep) + 250000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthDFPaperProg]
    exact implECDFPaper_sizeW_le_ratchet _ q qep mo ht htL hqep
      ((hooksCKAC_sizeBounded B B mo).mono (by dsimp [mo] at *; omega) le_rfl (by omega))
  have hf : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 :=
    authOut_ret_gen_sizeW_le _ _ _ q qep (2 + 1) (Or.inl rfl) mo ht htL hqep
  exact size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by omega) (by omega) (by omega)

theorem redPRNGAuthDFPaperProg_size_le
    (q qep t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redPRNGAuthDFPaperProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
      (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    compSizeW (ckaOpS B) ckaSampS ckaQueryS P.init +
      compSizeW (ckaOpS B) ckaSampS ckaQueryS P.handle +
      compSizeW (ckaOpS B) ckaSampS ckaQueryS P.finish + 600 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have hbt := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := t) (by omega)
  have hheal : CryptoGames.SM.Construction.healEpoch tL ≤ t + 3 := healEpoch_le_add_three htL
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (x := CryptoGames.SM.Construction.healEpoch tL) (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.init ≤
      20 * bits (ratchetCostBudget q qep) + 8000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFPaperProg]
    refine bind_ret_pair_unit_sizeW_le (initPRNGEStateC_sizeW_le B mo (.bool false)) ?_
    simp only [exprSizeW_bool]; dsimp [mo] at *; omega
  have hh : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.handle ≤
      1050 * bits (ratchetCostBudget q qep) + 250000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFPaperProg]
    exact implECDFPaper_sizeW_le_ratchet _ q qep mo ht htL hqep
      ((hooksPRNGC_sizeBounded B B mo).mono (by dsimp [mo] at *; omega) le_rfl (by omega))
  have hf : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 :=
    authOut_ret_gen_sizeW_le _ _ _ q qep (2 + 1) (Or.inl rfl) mo ht htL hqep
  exact size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by omega) (by omega) (by omega)

theorem redFSAuthDFPaperProg_size_le
    (q qep j t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) (hj : j < q)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redFSAuthDFPaperProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
      (sampK := sampK) (q + 1) B 1 qep maxForwardJumps j tL t
    compSizeW (ckaOpS B) ckaSampS ckaQueryS P.init +
      compSizeW (ckaOpS B) ckaSampS ckaQueryS P.handle +
      compSizeW (ckaOpS B) ckaSampS ckaQueryS P.finish + 600 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have hbL := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := q + 1) (by omega)
  have hbj := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := j) (by omega)
  have hbt := bits_le_ratchetCostBudget_of_le_linear (q := q) (qep := qep) (x := t) (by omega)
  have hheal : CryptoGames.SM.Construction.healEpoch tL ≤ t + 3 := healEpoch_le_add_three htL
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (x := CryptoGames.SM.Construction.healEpoch tL) (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.init ≤
      45 * bits (ratchetCostBudget q qep) + 15000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFPaperProg]
    refine bind_ret_pair_unit_sizeW_le (initFSEStateC_sizeW_le B (q + 1) mo j (.bool false)) ?_
    simp only [exprSizeW_bool]; dsimp [mo] at *; omega
  have hh : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.handle ≤
      1050 * bits (ratchetCostBudget q qep) + 250000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFPaperProg]
    exact implECDFPaper_sizeW_le_ratchet _ q qep mo ht htL hqep
      ((hooksFSC_sizeBounded B (q + 1) B mo j).mono (by dsimp [mo] at *; omega) le_rfl (by omega))
  have hf : compSizeW (ckaOpS B) ckaSampS ckaQueryS P.finish ≤ 100 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthDFPaperProg]
    simp only [compSizeW_sample, exprSizeW_unit, ckaSampS]; omega
  exact size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by omega) (by omega) (by omega)

end DFEngineSizeHelpers

end Computational.Proofs.SessionCostedFig8.DFProgSizeBounds
