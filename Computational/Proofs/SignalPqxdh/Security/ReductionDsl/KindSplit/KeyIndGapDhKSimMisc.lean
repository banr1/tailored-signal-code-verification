/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Bound
public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCore
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKem
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigProg
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs

/-!
# `init` and `finish` Simulation for Shadow-Indexed `KeyInd` Gap-DH

Proves `init` forgetful simulation and initial invariants along with `finish` CDH and forgery
extraction simulation for `sigKeyInd1KeyKindAtomicProg`, `gdhShadowFinish2Atomic`, and
`fgKeyInd1KeyGapDhKindAtomicProg`.
-/

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimMisc

set_option autoImplicit false

public section

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Var Expr Comp Env Iface pqAtomicSig pqAtomicOps pqKeyIndCodec)
open _root_.SignalPqxdh (
  Bytes Setup QueryBudget KeyIndQuery
  activeIdCount activeSpkCount activeOpkCount activeSendCount activeSendOpkCount
)
open _root_.SignalPqxdh.Costed (PB pqSigAndDdhIface)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqGapDhIface B U32 sidT)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  PT Ext v letV bindV caseOptV caseSumV eMap eFind eAny findMV mapMV foldMV
  gPrim liftBase qPow8 qX25519 ddhQ eCaseOpt eqB litB slice32
  keyIndStateTy keyIndQueryTy keyIndRespTy keyIndSessionEntryTy keyIndRespEntryTy spkBundleEntryTy
  paramsTy params2Ty simTy gdhStateTy gdhState2Ty
  paU paV paUp paPrinFlag paPrinIdx paDhFlag paEphIdx paSpkIdx paOpkMode paOpkIdx paMode paMk
  pa2U pa2V pa2Up pa2PrinTarget pa2SpkTarget pa2OpkMode pa2OpkTarget pa2Mode pa2Mk
  smBase smFgL smRaw smLog smPows smUpd emptySimE
  stPrin stSpks stOpks stSess stResps stAdv stUpd
  corruptB testB revealB revealSpkB
  wrapBase2 wrapSim2 initPrinGdh2B genSpkGdh2B genOpkGdh2B registerGdhB gdhHandle2
  logFindC logFind2C spkPowsC lookupFromPowsE initDh1CandC respDh1CandC
  findMapStepC findMapStep2C extractMode0C extractMode0_2C gdhFinish gdhFinish2
  chooseArm2C bernoulliRatioGdhC
  sig1KeyStTy s1Fg s1Base s1Target s1Pk s1Forgery s1Mk s1Upd sig1KeyTargetGenSpkB
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (
  liftGdhComp liftGdhComp_eval liftGdhToSign_pure liftGdhToSign_bind mem_support_liftGdhToSign
  twoVarRen pullEnv_twoVarRen renameComp renameComp_eval
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  avlEmptyE dfltB192E dfltDrKeyE
)
open Computational.Proofs.ReductionDsl.StepSim (bumpPred bind_congr_support)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  AtomicIface embedTy embedVal projVal embedEnv
  mapComp mapComp_eval liftKeyIndHandle liftKeyIndHandle_eval liftKeyInd1Stage
  tlGapDhKeyInd tlSigDdhKeyInd
)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  sig1KeyActiveStTy gdh1KeyActiveStateTy saTP saInner
  sigKeyInd1KeyActiveDslProg sigKeyInd1KeyActiveAtomicProg
  initParams1KeyActiveC fgKeyInd1KeyGapDhActiveDslProg fgKeyInd1KeyGapDhActiveAtomicProg
  fgActiveTotalIndexCount
)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (
  sig1KeyActiveKindStTy gdh1KeyActiveKindStateTy
  sig1KeyKindBaseInit sig1KeyKindBaseFinish initParams1KeyKindC gdh1KeyKindBaseInit
  sig1KeyKindInitC sig1KeyKindFinishC gdh1KeyKindInitC
  sig1KeyKindHandleC gdh1KeyKindHandleC gdh1KeyKindFinishC
  sigKeyInd1KeyKindAtomicProg fgKeyInd1KeyGapDhKindAtomicProg
  sig1KeyKindBaseInit_unsupported sig1KeyKindBaseFinish_unsupported
  initParams1KeyKindC_unsupported gdh1KeyKindBaseInit_unsupported
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  keyIndSentinel dispatchKeyIndQ runAt2
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase (
  keyIndSimPred keyIndSimBounds
  fixSent fixSent_keyIndSentinel fixSent_of_lt_N_dh beq_fixSent_of_le_mOn mem_support_sIndex_lt
  stPrinList stSpksList stOpksList stSessList stRespsList stAdvList
  BaseOnlineLenInv take_min_eq_of_length_le
  dispatchKeyIndQ_eval runAt2_eval
  corruptB_min_eq testB_min_eq revealB_min_eq revealSpkB_min_eq initPrin1KeyB_min_eq
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (
  KeyIndKFuels keyIndKFuelsOfBudget
  fgShadowAtomicTy emptyFgShadowE gdhShadowState2AtomicTy forgetGdhShadow2
  GdhAtomicLift gdhLift1Key liftGdhAtomic
  extractMode0KC gdhFinishK extractMode0_2KC gdhFinish2K
  gdhShadowHandle2Atomic gdhShadowFinish2Atomic
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase (
  GdhAtomicLiftValid gdhLift1Key_valid
  fixParamsSent fixSig1KeyActiveSent forgetSig1KeyActiveK
  fixGdh1KeyActiveSent forgetGdh1KeyActiveK
  GdhSimInv GdhSimInv_emptySim Gdh2SimInv Sig1KeyActiveSimInv Gdh1KeyActiveSimInv
  KeyIndStepSim
)

section InitAndFinish

set_option allowUnsafeReducibility true
attribute [local implicit_reducible]
  _root_.SignalPqxdh.LegacyCosted.pqChalIface
  _root_.SignalPqxdh.LegacyCosted.pqPrimIface
  _root_.SignalPqxdh.LegacyCosted.pqGapDhIface
  _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
  _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle
  _root_.SignalPqxdh.sigAndDdhSpec
  _root_.SignalPqxdh.sigOracleSpec
  _root_.SignalPqxdh.gapDhOracleSpec
  _root_.SignalPqxdh.LegacyCosted.gapDhDdhOracle
  sigKeyInd1KeyKindAtomicProg
  fgKeyInd1KeyGapDhKindAtomicProg
  sigKeyInd1KeyActiveAtomicProg
  fgKeyInd1KeyGapDhActiveAtomicProg
  sigKeyInd1KeyActiveDslProg
  fgKeyInd1KeyGapDhActiveDslProg
  _root_.ReductionDsl.CostedReduction.σ
  Env.get

private theorem mem_support_embedPrim {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {mx : OracleComp _root_.SignalPqxdh.PrimBaseSpec α} {a : α}
    (h : a ∈ support (_root_.SignalPqxdh.Security.embedPrim (spec := spec) mx)) :
    a ∈ support mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simpa [_root_.SignalPqxdh.Security.embedPrim] using h
  | query_bind t mx ih =>
    change a ∈ support
      (liftM (OracleSpec.query (spec := _root_.SignalPqxdh.PrimBaseSpec + spec) (Sum.inl t)) >>=
        fun u => _root_.SignalPqxdh.Security.embedPrim (spec := spec) (mx u)) at h
    rw [mem_support_bind_iff] at h
    obtain ⟨u, _, h⟩ := h
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ih u h⟩

private theorem mem_support_fgEmbedPrim {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {mx : OracleComp _root_.SignalPqxdh.PrimBaseSpec α} {a : α}
    (h : a ∈ support (_root_.SignalPqxdh.Security.FgGapDh.embedPrim (spec := spec) mx)) :
    a ∈ support mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simpa [_root_.SignalPqxdh.Security.FgGapDh.embedPrim] using h
  | query_bind t mx ih =>
    change a ∈ support
      (liftM (OracleSpec.query (spec := _root_.SignalPqxdh.PrimBaseSpec + spec) (Sum.inl t)) >>=
        fun u => _root_.SignalPqxdh.Security.FgGapDh.embedPrim (spec := spec) (mx u)) at h
    rw [mem_support_bind_iff] at h
    obtain ⟨u, _, h⟩ := h
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ih u h⟩

private theorem fixSent_zero (S : Setup) (b : QueryBudget) : fixSent S b 0 = 0 := by
  unfold fixSent keyIndSentinel
  split_ifs with h
  · omega
  · rfl

private theorem activeIdCount_le_N_dh (S : Setup) (q : ℕ) : activeIdCount S q ≤ S.N_dh := by
  simp only [activeIdCount, Setup.N_dh]; omega

private theorem activeSpkCount_le_N_dh (S : Setup) (q : ℕ) : activeSpkCount S q ≤ S.N_dh := by
  simp only [activeSpkCount, Setup.N_dh]; omega

private theorem activeOpkCount_le_N_dh (S : Setup) (q : ℕ) : activeOpkCount S q ≤ S.N_dh := by
  simp only [activeOpkCount, Setup.N_dh]; omega

private theorem activeSendCount_le_N_dh (S : Setup) (q : ℕ) : activeSendCount S q ≤ S.N_dh := by
  simp only [activeSendCount, Setup.N_dh]; omega

private theorem activeSendOpkCount_le_N_dh (S : Setup) (q : ℕ) :
    activeSendOpkCount S q ≤ S.N_dh := by
  simp only [activeSendOpkCount, Setup.N_dh, Setup.N_send_tot]; omega

private theorem sigActive_init_unsupported (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).init.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 :=
  rfl

private theorem sigActive_finish_unsupported (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).finish.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 :=
  rfl

private theorem embedVal_unit_prod {τ : PT} (r : (Ty.prod .unit τ).denote) :
    embedVal (.prod .unit τ) r = (r.1, embedVal τ r.2) := rfl

/-- `StepSim.ForgetSim.hInit` for `sigKeyInd1KeyKindAtomicProg` vs `sigKeyInd1KeyActiveAtomicProg`. -/
theorem sigKeyInd1KeyKindAtomicProg_hInit (S : Setup) (b : QueryBudget) (pk : (PB 32).denote) :
    Prod.map id (forgetSig1KeyActiveK S b) <$>
      (sigKeyInd1KeyKindAtomicProg S b).init.eval (.cons pk .nil) =
      (sigKeyInd1KeyActiveAtomicProg S b).init.eval (.cons pk .nil) ∧
    ∀ as' ∈ support ((sigKeyInd1KeyKindAtomicProg S b).init.eval (.cons pk .nil)),
      Sig1KeyActiveSimInv S b 0 as'.2 := by
  have hEnv :
      (Env.cons pk .nil : Env [PB 32]) =
        embedEnv (.cons (projVal (B 32) pk) .nil : Env [B 32]) := by
    simp [embedEnv, AtomicLift.embedVal_projVal]
  have hEvalK :
      (sigKeyInd1KeyKindAtomicProg S b).init.eval (.cons pk .nil) =
        (fun r => (r.1, (embedVal sig1KeyActiveStTy r.2, (emptyFgShadowE (Γ := [])).eval .nil))) <$>
          (sig1KeyKindBaseInit S b).eval (.cons (projVal (B 32) pk) .nil) := by
    simp only [sigKeyInd1KeyKindAtomicProg, sig1KeyKindInitC, Comp.eval, hEnv]
    rw [mapComp_eval tlSigDdhKeyInd (sig1KeyKindBaseInit S b) (sig1KeyKindBaseInit_unsupported S b)]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
      embedVal_unit_prod, emptyFgShadowE, avlEmptyE, dfltB192E, dfltDrKeyE,
      KeyIndGapDhK.dfltFgRoValE, Expr.eval, Env.get]
  have hEvalOld :
      (sigKeyInd1KeyActiveAtomicProg S b).init.eval (.cons pk .nil) =
        embedVal (.prod .unit sig1KeyActiveStTy) <$>
          (sigKeyInd1KeyActiveDslProg S b).init.eval (.cons (projVal (B 32) pk) .nil) := by
    simp only [sigKeyInd1KeyActiveAtomicProg, liftKeyInd1Stage, hEnv]
    exact mapComp_eval tlSigDdhKeyInd (sigKeyInd1KeyActiveDslProg S b).init
      (sigActive_init_unsupported S b) _
  rw [hEvalK, hEvalOld]
  constructor
  · simp only [map_eq_bind_pure_comp, Function.comp_def,
      sig1KeyKindBaseInit, sigKeyInd1KeyActiveDslProg, bindV, Comp.eval, bind_assoc, pure_bind]
    refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun k hk => ?_
    refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun secb _ => ?_
    by_cases hZero : activeIdCount S b.q_on = 0
    · simp [hZero, forgetSig1KeyActiveK, fixSig1KeyActiveSent, fixSent_keyIndSentinel,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v, embedVal, Expr.eval]
    · have hkLt : k < S.N_dh := by
        have hpos : 0 < activeIdCount S b.q_on := Nat.pos_of_ne_zero hZero
        have hkId : k < activeIdCount S b.q_on := by
          refine mem_support_sIndex_lt (activeIdCount S b.q_on) hpos (.cons (projVal (B 32) pk) .nil) ?_
          exact mem_support_embedPrim
            (by simpa [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim,
              _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.eval] using hk)
        exact Nat.lt_of_lt_of_le hkId (activeIdCount_le_N_dh S b.q_on)
      simp [hZero, forgetSig1KeyActiveK, fixSig1KeyActiveSent, fixSent_of_lt_N_dh hkLt,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v, embedVal, Expr.eval]
  · intro as' has'
    rw [map_eq_bind_pure_comp, mem_support_bind_iff] at has'
    obtain ⟨r, hr, has'⟩ := has'
    rw [Function.comp_apply, mem_support_pure_iff] at has'
    subst has'
    simp only [sig1KeyKindBaseInit, bindV, Comp.eval, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨k, _, secb, _, rfl⟩ := hr
    exact GdhSimInv_emptySim S b secb

private def fixParamsSentLeg (S : Setup) (b : QueryBudget) (pa : paramsTy.denote) : paramsTy.denote :=
  let (u, (vPk, (up, (prinFlag, (prinIdx, (dhFlag, (ephIdx, (spkIdx, (opkMode, (opkIdx, mode)))))))))) := pa
  (u, (vPk, (up, (prinFlag, (fixSent S b prinIdx,
    (dhFlag, (fixSent S b ephIdx, (fixSent S b spkIdx, (opkMode, (fixSent S b opkIdx, mode))))))))))

private theorem embedVal_fixParamsSentLeg (S : Setup) (b : QueryBudget) (pa : paramsTy.denote) :
    embedVal paramsTy (fixParamsSentLeg S b pa) = fixParamsSent S b (embedVal paramsTy pa) := by
  rcases pa with ⟨u, vPk, up, prinFlag, prinIdx, dhFlag, ephIdx, spkIdx, opkMode, opkIdx, mode⟩
  rfl

private theorem chooseArm2C_map_eval {Γ₁ Δ : List PT} {τ₁ τ₂ : PT} [Ext Γ₁ Δ]
    (f : τ₁.denote → τ₂.denote) (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ₁)
    (d1 d2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ₂)
    (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'] (ρ : Env Δ'), f <$> (c1 (Δ' := Δ')).eval ρ = (d1 (Δ' := Δ')).eval ρ)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'] (ρ : Env Δ'), f <$> (c2 (Δ' := Δ')).eval ρ = (d2 (Δ' := Δ')).eval ρ)
    (ρ : Env Δ) :
    f <$> (chooseArm2C (Γ₁ := Γ₁) w1 w2 c1 c2).eval ρ =
      (chooseArm2C (Γ₁ := Γ₁) w1 w2 d1 d2).eval ρ := by
  unfold chooseArm2C
  split_ifs
  · exact h2 ρ
  · exact h1 ρ
  · simp only [bindV, Comp.eval, map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
    refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun b _ => ?_
    let bT : (Ty.bool : PT).denote := true
    let bF : (Ty.bool : PT).denote := false
    cases b
    · have h := h2 (.cons bF ρ)
      simpa [-bind_pure_comp, Comp.eval, Expr.eval, Env.get, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        map_eq_bind_pure_comp, Function.comp_def] using h
    · have h := h1 (.cons bT ρ)
      simpa [-bind_pure_comp, Comp.eval, Expr.eval, Env.get, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        map_eq_bind_pure_comp, Function.comp_def] using h

private theorem initParams1KeyKindC_legacy_sim (S : Setup) (b : QueryBudget) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (B 32) (B 32))) (env : Env Δ) :
    fixParamsSentLeg S b <$> (initParams1KeyKindC S b uv).eval env =
      (initParams1KeyActiveC S b uv).eval env := by
  unfold initParams1KeyKindC initParams1KeyActiveC
  dsimp only
  by_cases hTot : fgActiveTotalIndexCount S b.q_on = 0
  · simp [hTot, Comp.eval, paMk, fixParamsSentLeg, fixSent_keyIndSentinel, Expr.eval]
  · simp only [hTot, ↓reduceIte]
    refine chooseArm2C_map_eval (fixParamsSentLeg S b) _ _ _ _ _ _
      (fun {_} [_] ρ => chooseArm2C_map_eval (fixParamsSentLeg S b) _ _ _ _ _ _ ?_ ?_ ρ)
      (fun {_} [_] ρ => chooseArm2C_map_eval (fixParamsSentLeg S b) _ _ _ _ _ _ ?_ ?_ ρ) env
    · intro Δ' _ ρ
      by_cases hnA : activeIdCount S b.q_on * activeSpkCount S b.q_on = 0
      · simp [hnA, Comp.eval, paMk, fixParamsSentLeg, fixSent_keyIndSentinel, fixSent_zero, Expr.eval]
      · have hPos1 : 0 < activeIdCount S b.q_on := Nat.pos_of_ne_zero (fun h => hnA (by simp [h]))
        have hPos2 : 0 < activeSpkCount S b.q_on := Nat.pos_of_ne_zero (fun h => hnA (by simp [h]))
        simp only [hnA, ↓reduceIte, bindV, Comp.eval, map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
        refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun pOrd hP => ?_
        refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun spkOrd hSpk => ?_
        have hP' : pOrd ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sIndex (activeIdCount S b.q_on)).eval ρ) :=
          mem_support_fgEmbedPrim (by simpa [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.eval] using hP)
        have hSpk' : spkOrd ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sIndex (activeSpkCount S b.q_on)).eval (.cons pOrd ρ)) :=
          mem_support_fgEmbedPrim (by simpa [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.eval] using hSpk)
        have hLt1 := Nat.lt_of_lt_of_le (mem_support_sIndex_lt _ hPos1 _ hP') (activeIdCount_le_N_dh S b.q_on)
        have hLt2 := Nat.lt_of_lt_of_le (mem_support_sIndex_lt _ hPos2 _ hSpk') (activeSpkCount_le_N_dh S b.q_on)
        simp [paMk, v, fixParamsSentLeg, fixSent_keyIndSentinel, fixSent_of_lt_N_dh hLt1,
          fixSent_of_lt_N_dh hLt2, Expr.eval]
    · intro Δ' _ ρ
      by_cases hnC : activeSendCount S b.q_on * activeSpkCount S b.q_on = 0
      · simp [hnC, Comp.eval, paMk, fixParamsSentLeg, fixSent_keyIndSentinel, fixSent_zero, Expr.eval]
      · have hPos1 : 0 < activeSendCount S b.q_on := Nat.pos_of_ne_zero (fun h => hnC (by simp [h]))
        have hPos2 : 0 < activeSpkCount S b.q_on := Nat.pos_of_ne_zero (fun h => hnC (by simp [h]))
        simp only [hnC, ↓reduceIte, bindV, Comp.eval, map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
        refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun ephOrd hEph => ?_
        refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun spkOrd hSpk => ?_
        have hEph' : ephOrd ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sIndex (activeSendCount S b.q_on)).eval ρ) :=
          mem_support_fgEmbedPrim (by simpa [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.eval] using hEph)
        have hSpk' : spkOrd ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sIndex (activeSpkCount S b.q_on)).eval (.cons ephOrd ρ)) :=
          mem_support_fgEmbedPrim (by simpa [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.eval] using hSpk)
        have hLt1 := Nat.lt_of_lt_of_le (mem_support_sIndex_lt _ hPos1 _ hEph') (activeSendCount_le_N_dh S b.q_on)
        have hLt2 := Nat.lt_of_lt_of_le (mem_support_sIndex_lt _ hPos2 _ hSpk') (activeSpkCount_le_N_dh S b.q_on)
        simp [paMk, v, fixParamsSentLeg, fixSent_keyIndSentinel, fixSent_of_lt_N_dh hLt1,
          fixSent_of_lt_N_dh hLt2, Expr.eval]
    · intro Δ' _ ρ
      by_cases hnB : activeSendCount S b.q_on * activeIdCount S b.q_on = 0
      · simp [hnB, Comp.eval, paMk, fixParamsSentLeg, fixSent_keyIndSentinel, fixSent_zero, Expr.eval]
      · have hPos1 : 0 < activeSendCount S b.q_on := Nat.pos_of_ne_zero (fun h => hnB (by simp [h]))
        have hPos2 : 0 < activeIdCount S b.q_on := Nat.pos_of_ne_zero (fun h => hnB (by simp [h]))
        simp only [hnB, ↓reduceIte, bindV, Comp.eval, map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
        refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun ephOrd hEph => ?_
        refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun pOrd hP => ?_
        have hEph' : ephOrd ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sIndex (activeSendCount S b.q_on)).eval ρ) :=
          mem_support_fgEmbedPrim (by simpa [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.eval] using hEph)
        have hP' : pOrd ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sIndex (activeIdCount S b.q_on)).eval (.cons ephOrd ρ)) :=
          mem_support_fgEmbedPrim (by simpa [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.eval] using hP)
        have hLt1 := Nat.lt_of_lt_of_le (mem_support_sIndex_lt _ hPos1 _ hEph') (activeSendCount_le_N_dh S b.q_on)
        have hLt2 := Nat.lt_of_lt_of_le (mem_support_sIndex_lt _ hPos2 _ hP') (activeIdCount_le_N_dh S b.q_on)
        simp [paMk, v, fixParamsSentLeg, fixSent_keyIndSentinel, fixSent_of_lt_N_dh hLt1,
          fixSent_of_lt_N_dh hLt2, Expr.eval]
    · intro Δ' _ ρ
      by_cases hnD : activeSendOpkCount S b.q_on * activeOpkCount S b.q_on = 0
      · simp [hnD, Comp.eval, paMk, fixParamsSentLeg, fixSent_keyIndSentinel, fixSent_zero, Expr.eval]
      · have hPos1 : 0 < activeSendOpkCount S b.q_on := Nat.pos_of_ne_zero (fun h => hnD (by simp [h]))
        have hPos2 : 0 < activeOpkCount S b.q_on := Nat.pos_of_ne_zero (fun h => hnD (by simp [h]))
        simp only [hnD, ↓reduceIte, bindV, Comp.eval, map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
        refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun ephOrd hEph => ?_
        refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun opkOrd hOpk => ?_
        have hEph' : ephOrd ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sIndex (activeSendOpkCount S b.q_on)).eval ρ) :=
          mem_support_fgEmbedPrim (by simpa [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.eval] using hEph)
        have hOpk' : opkOrd ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sIndex (activeOpkCount S b.q_on)).eval (.cons ephOrd ρ)) :=
          mem_support_fgEmbedPrim (by simpa [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.eval] using hOpk)
        have hLt1 := Nat.lt_of_lt_of_le (mem_support_sIndex_lt _ hPos1 _ hEph') (activeSendOpkCount_le_N_dh S b.q_on)
        have hLt2 := Nat.lt_of_lt_of_le (mem_support_sIndex_lt _ hPos2 _ hOpk') (activeOpkCount_le_N_dh S b.q_on)
        simp [paMk, v, fixParamsSentLeg, fixSent_keyIndSentinel, fixSent_of_lt_N_dh hLt1,
          fixSent_of_lt_N_dh hLt2, Expr.eval]

private theorem chooseArm2C_unsup_local {Γ₁ Δ : List PT} {α : PT} [Ext Γ₁ Δ] (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' α)
    (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  have hb : ∀ {Δ' : List PT}, (bernoulliRatioGdhC (Δ := Δ') w1 w2).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
    intro Δ'; unfold bernoulliRatioGdhC
    split_ifs <;> simp [bindV, Comp.queries, gPrim, liftBase, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sIndex]
  unfold chooseArm2C; split_ifs <;> simp [bindV, Comp.queries, hb, h1, h2]

private theorem initParams1KeyActiveC_unsupported (S : Setup) (b : QueryBudget)
    {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))) :
    (initParams1KeyActiveC S b (Δ := Δ) uv).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  have hArm : ∀ {Δ' : List PT} (n : Nat),
      (gPrim (Γ := Δ') (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sIndex n)).queries
        tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := fun _ => rfl
  unfold initParams1KeyActiveC; dsimp only
  by_cases htot : fgActiveTotalIndexCount S b.q_on = 0
  · simp [htot, Comp.queries]
  · simp only [htot, ↓reduceIte]
    exact chooseArm2C_unsup_local _ _ _ _
      (fun {_} [_] => chooseArm2C_unsup_local _ _ _ _
        (fun {_} [_] => by split_ifs <;> simp [bindV, Comp.queries, hArm])
        (fun {_} [_] => by split_ifs <;> simp [bindV, Comp.queries, hArm]))
      (fun {_} [_] => chooseArm2C_unsup_local _ _ _ _
        (fun {_} [_] => by split_ifs <;> simp [bindV, Comp.queries, hArm])
        (fun {_} [_] => by split_ifs <;> simp [bindV, Comp.queries, hArm]))

private theorem gdhActive_init_unsupported (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  have h1 := initParams1KeyActiveC_unsupported S b
    (Γ₁ := [.prod (B 32) (B 32), .prod (B 32) (B 32)])
    (Δ := [.prod (B 32) (B 32), .prod (B 32) (B 32)]) .zero
  simp only [fgKeyInd1KeyGapDhActiveDslProg, letV, bindV, Comp.queries,
    KeyIndGapDhKSimBase.liftGdhComp_unsupported_keyInd, h1]
  rfl

/-- Forgetful simulation for `initParams1KeyKindC` vs `initParams1KeyActiveC` under `fixParamsSent`. -/
theorem initParams1KeyKindC_sim (S : Setup) (b : QueryBudget) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (B 32) (B 32))) (env : Env Δ) :
    fixParamsSent S b <$>
      (mapComp tlGapDhKeyInd (initParams1KeyKindC S b uv)).eval (embedEnv env) =
    (mapComp tlGapDhKeyInd (initParams1KeyActiveC S b uv)).eval (embedEnv env) := by
  rw [mapComp_eval tlGapDhKeyInd (initParams1KeyKindC S b uv) (initParams1KeyKindC_unsupported S b uv),
      mapComp_eval tlGapDhKeyInd (initParams1KeyActiveC S b uv)
        (initParams1KeyActiveC_unsupported S b uv),
      ← initParams1KeyKindC_legacy_sim S b uv env]
  simp [Functor.map_map, embedVal_fixParamsSentLeg]

/-- `StepSim.ForgetSim.hInit` for `fgKeyInd1KeyGapDhKindAtomicProg` vs
    `fgKeyInd1KeyGapDhActiveAtomicProg`. -/
theorem fgKeyInd1KeyGapDhKindAtomicProg_hInit (S : Setup) (b : QueryBudget)
    (uv : (Ty.prod (PB 32) (PB 32)).denote) :
    Prod.map id (forgetGdh1KeyActiveK S b) <$>
      (fgKeyInd1KeyGapDhKindAtomicProg S b).init.eval (.cons uv .nil) =
      (fgKeyInd1KeyGapDhActiveAtomicProg S b).init.eval (.cons uv .nil) ∧
    ∀ as' ∈ support ((fgKeyInd1KeyGapDhKindAtomicProg S b).init.eval (.cons uv .nil)),
      Gdh1KeyActiveSimInv S b 0 as'.2 := by
  have hEnv :
      (Env.cons uv .nil : Env [.prod (PB 32) (PB 32)]) =
        embedEnv (.cons (projVal (.prod (B 32) (B 32)) uv) .nil : Env [.prod (B 32) (B 32)]) := by
    simp [embedEnv, AtomicLift.embedVal_projVal]
  have hEvalK :
      (fgKeyInd1KeyGapDhKindAtomicProg S b).init.eval (.cons uv .nil) =
        (fun r => (r.1, (embedVal gdh1KeyActiveStateTy r.2, (emptyFgShadowE (Γ := [])).eval .nil))) <$>
          (gdh1KeyKindBaseInit S b).eval (.cons (projVal (.prod (B 32) (B 32)) uv) .nil) := by
    simp only [fgKeyInd1KeyGapDhKindAtomicProg, gdh1KeyKindInitC, Comp.eval, hEnv]
    rw [mapComp_eval tlSigDdhKeyInd (gdh1KeyKindBaseInit S b) (gdh1KeyKindBaseInit_unsupported S b)]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
      embedVal_unit_prod, emptyFgShadowE, avlEmptyE, dfltB192E, dfltDrKeyE,
      KeyIndGapDhK.dfltFgRoValE, Expr.eval, Env.get]
  have hEvalOld :
      (fgKeyInd1KeyGapDhActiveAtomicProg S b).init.eval (.cons uv .nil) =
        embedVal (.prod .unit gdh1KeyActiveStateTy) <$>
          (fgKeyInd1KeyGapDhActiveDslProg S b).init.eval
            (.cons (projVal (.prod (B 32) (B 32)) uv) .nil) := by
    simp only [fgKeyInd1KeyGapDhActiveAtomicProg, liftKeyInd1Stage, hEnv]
    exact mapComp_eval tlSigDdhKeyInd (fgKeyInd1KeyGapDhActiveDslProg S b).init
      (gdhActive_init_unsupported S b) _
  rw [hEvalK, hEvalOld]
  constructor
  · simp only [gdh1KeyKindBaseInit, fgKeyInd1KeyGapDhActiveDslProg,
      letV, bindV, v, Comp.eval, Expr.eval, Env.get,
      liftGdhComp_eval, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    have hSim := initParams1KeyKindC_legacy_sim S b
      (Γ₁ := [.prod (B 32) (B 32), .prod (B 32) (B 32)])
      (Δ := [.prod (B 32) (B 32), .prod (B 32) (B 32)]) .zero
      (.cons (projVal (.prod (B 32) (B 32)) uv) (.cons (projVal (.prod (B 32) (B 32)) uv) .nil))
    simp only [Prod.mk.eta]
    rw [← hSim]
    simp [-bind_pure_comp, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
      liftGdhToSign_bind, liftGdhToSign_pure,
      forgetGdh1KeyActiveK, fixGdh1KeyActiveSent, fixParamsSent, fixParamsSentLeg, embedVal,
      emptySimE, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smMk,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.emptyStE,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk, Expr.eval]
  · intro as' has'
    rw [map_eq_bind_pure_comp, mem_support_bind_iff] at has'
    obtain ⟨r, hr, has'⟩ := has'
    rw [Function.comp_apply, mem_support_pure_iff] at has'
    subst has'
    simp only [gdh1KeyKindBaseInit, letV, bindV, Comp.eval,
      liftGdhComp_eval, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, rfl, pa, _, secb, _, rfl⟩ := hr
    exact ⟨GdhSimInv_emptySim S b secb, Nat.zero_le _⟩

/-- `StepSim.ForgetSim.hFinish` for `sigKeyInd1KeyKindAtomicProg` vs
    `sigKeyInd1KeyActiveAtomicProg`. -/
theorem sigKeyInd1KeyKindAtomicProg_hFinish (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (s' : (sigKeyInd1KeyKindAtomicProg S b).σ.denote) (aOut : Bool)
    (_hB : ∀ j, c j ≤ keyIndSimBounds b j) (_hInv : Sig1KeyActiveSimInv S b c s') :
    (sigKeyInd1KeyKindAtomicProg S b).finish.eval (.cons s' (.cons aOut .nil)) =
      (sigKeyInd1KeyActiveAtomicProg S b).finish.eval
        (.cons (forgetSig1KeyActiveK S b s') (.cons aOut .nil)) := by
  simp only [sigKeyInd1KeyKindAtomicProg, sig1KeyKindFinishC, runAt2_eval,
    sigKeyInd1KeyActiveAtomicProg, liftKeyInd1Stage,
    Expr.eval, Env.get]
  have hEnv1 :
      (Env.cons s'.1 (.cons aOut .nil) : Env [embedTy sig1KeyActiveStTy, .bool]) =
        embedEnv (.cons (projVal sig1KeyActiveStTy s'.1) (.cons aOut .nil) :
          Env [sig1KeyActiveStTy, .bool]) := by
    simp only [embedEnv, AtomicLift.embedVal_projVal]; rfl
  have hEnv2 :
      (Env.cons (forgetSig1KeyActiveK S b s') (.cons aOut .nil) :
          Env [embedTy sig1KeyActiveStTy, .bool]) =
        embedEnv (.cons (projVal sig1KeyActiveStTy (forgetSig1KeyActiveK S b s'))
          (.cons aOut .nil) : Env [sig1KeyActiveStTy, .bool]) := by
    simp only [embedEnv, AtomicLift.embedVal_projVal]; rfl
  rw [hEnv1, hEnv2,
    mapComp_eval tlSigDdhKeyInd sig1KeyKindBaseFinish sig1KeyKindBaseFinish_unsupported,
    mapComp_eval tlSigDdhKeyInd (sigKeyInd1KeyActiveDslProg S b).finish
      (sigActive_finish_unsupported S b)]
  rcases s' with ⟨⟨tp?, ⟨sm, ⟨ord, ⟨pk, ⟨budget, forgery⟩⟩⟩⟩⟩, fgSh⟩
  rfl

private theorem mapMV_length_eq {Γ : List PT} {a b : PT} (M : ℕ)
    (l : Expr pqxdhOps Γ (.list a)) (f : Comp pqxdhOps pqGapDhIface (a :: Γ) b) (ρ : Env Γ)
    {ys : List b.denote} (hys : ys ∈ support ((Comp.mapM M l f).eval ρ)) :
    ys.length = ((l.eval ρ).take M).length := by
  simp only [Comp.eval] at hys
  generalize (l.eval ρ).take M = xs at hys
  induction xs generalizing ys with
  | nil =>
    simp only [ReductionDsl.mapML, mem_support_pure_iff] at hys
    subst hys; rfl
  | cons x xs ih =>
    simp only [ReductionDsl.mapML, mem_support_bind_iff, mem_support_pure_iff] at hys
    obtain ⟨y, _, ys', hys', rfl⟩ := hys
    simp [ih hys']

private theorem logFindC_eq_of_le (K₁ K₂ off : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (ρ : Env Δ)
    (hLog : ((smLog (v sm)).eval ρ).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (logFindC K₁ off pa sm).eval ρ = (logFindC K₂ off pa sm).eval ρ := by
  have hMap :
      (eMap K₁ (smLog (v sm)) fun sec => _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.slice32 off (v sec)).eval ρ =
      (eMap K₂ (smLog (v sm)) fun sec => _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.slice32 off (v sec)).eval ρ := by
    simp only [eMap, Expr.eval, List.take_of_length_le hLog,
      List.take_of_length_le (Nat.le_trans hLog hLe)]
  have hCandLen :
      ((eMap K₂ (smLog (v sm)) fun sec =>
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.slice32 off (v sec)).eval ρ).length ≤ K₁ := by
    simp only [eMap, Expr.eval, List.length_map, List.length_take]
    omega
  unfold logFindC
  simp only [bindV, findMV, Comp.eval, hMap, List.take_of_length_le hCandLen,
    List.take_of_length_le (Nat.le_trans hCandLen hLe)]

private theorem logFind2C_eq_of_le (K₁ K₂ off : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (ρ : Env Δ)
    (hLog : ((smLog (v sm)).eval ρ).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (logFind2C K₁ off pa sm).eval ρ = (logFind2C K₂ off pa sm).eval ρ := by
  have hMap :
      (eMap K₁ (smLog (v sm)) fun sec => _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.slice32 off (v sec)).eval ρ =
      (eMap K₂ (smLog (v sm)) fun sec => _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.slice32 off (v sec)).eval ρ := by
    simp only [eMap, Expr.eval, List.take_of_length_le hLog,
      List.take_of_length_le (Nat.le_trans hLog hLe)]
  have hCandLen :
      ((eMap K₂ (smLog (v sm)) fun sec =>
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.slice32 off (v sec)).eval ρ).length ≤ K₁ := by
    simp only [eMap, Expr.eval, List.length_map, List.length_take]
    omega
  unfold logFind2C
  simp only [bindV, findMV, Comp.eval, hMap, List.take_of_length_le hCandLen,
    List.take_of_length_le (Nat.le_trans hCandLen hLe)]

private theorem extractMode0KC_eq (S : Setup) (f : KeyIndKFuels) (K : ℕ)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (ρ : Env Δ)
    (hOnLe : f.kOn ≤ K) (hOffLe : f.kOff ≤ K)
    (hLog : ((smLog (v sm)).eval ρ).length ≤ f.kOff)
    (hPows : ((smPows (v sm)).eval ρ).length ≤ f.kOn)
    (hSpks : ((stSpks (smBase (v sm))).eval ρ).length ≤ f.kOn)
    (hSess : ((stSess (smBase (v sm))).eval ρ).length ≤ f.kOn)
    (hResps : ((stResps (smBase (v sm))).eval ρ).length ≤ f.kOn) :
    (extractMode0KC S f pa sm).eval ρ = (extractMode0C S K pa sm).eval ρ := by
  unfold extractMode0KC extractMode0C
  have hMap :
      (eMap f.kOff (smLog (v sm)) fun sec => _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.slice32 32 (v sec)).eval ρ =
      (eMap K (smLog (v sm)) fun sec => _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.slice32 32 (v sec)).eval ρ := by
    simp only [eMap, Expr.eval, List.take_of_length_le hLog,
      List.take_of_length_le (Nat.le_trans hLog hOffLe)]
  have hCandLen :
      ((eMap K (smLog (v sm)) fun sec =>
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.slice32 32 (v sec)).eval ρ).length ≤ f.kOff := by
    simp only [eMap, Expr.eval, List.length_map, List.length_take]; omega
  simp only [bindV, caseOptV, letV, Comp.eval]
  have hFind :
      (findMV f.kOff (eMap f.kOff (smLog (v sm)) fun sec =>
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.slice32 32 (v sec))
          fun z => _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.ddhQ (paU (v pa)) (paV (v pa)) (v z)).eval ρ =
      (findMV K (eMap K (smLog (v sm)) fun sec =>
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.slice32 32 (v sec))
          fun z => _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.ddhQ (paU (v pa)) (paV (v pa)) (v z)).eval ρ := by
    simp only [findMV, Comp.eval, hMap, List.take_of_length_le hCandLen,
      List.take_of_length_le (Nat.le_trans hCandLen hOffLe)]
  rw [hFind]
  refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun f1 _ => ?_
  cases f1 with
  | some z => rfl
  | none =>
    let noneOpt : (Ty.opt (B 32)).denote := none
    have hSpks' : ((stSpks (smBase (v sm))).eval (.cons noneOpt ρ)).length ≤ f.kOn := by
      simpa [smBase, stSpks, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        Expr.eval, Env.get] using hSpks
    have hSpkPows :
        (spkPowsC S f.kOn (stSpks (smBase (v sm)))).eval (.cons noneOpt ρ) =
        (spkPowsC S K (stSpks (smBase (v sm)))).eval (.cons noneOpt ρ) := by
      simp only [spkPowsC, mapMV, Comp.eval]
      rw [take_min_eq_of_length_le _ hSpks' hOnLe]
    rw [hSpkPows]
    refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun spkPows hMemSpk => ?_
    have hSpkPowsLen : spkPows.length ≤ f.kOn := by
      have hEq := mapMV_length_eq (min K S.N_dh) _ _ (.cons noneOpt ρ) hMemSpk
      rw [hEq, List.length_take]
      exact Nat.le_trans (Nat.min_le_right _ _) hSpks'
    simp only [Expr.eval, pure_bind]
    have hFold1 :
        (foldMV (min f.kOn S.N_dh) (stSess (smBase (v sm))) .none fun s acc =>
            findMapStepC pa acc
              (initDh1CandC S f.kOn
                (.zero : Var (.list (.prod (B 32) (B 32)) :: .opt (B 32) :: Δ) (.list (.prod (B 32) (B 32))))
                (.zero : Var (.list (.prod (B 32) (B 32)) :: .list (.prod (B 32) (B 32)) :: .opt (B 32) :: Δ)
                  (.list (.prod (B 32) (B 32))))
                s)).eval
          (.cons ((smPows (v sm)).eval (.cons spkPows (.cons noneOpt ρ))) (.cons spkPows (.cons noneOpt ρ))) =
        (foldMV (min K S.N_dh) (stSess (smBase (v sm))) .none fun s acc =>
            findMapStepC pa acc
              (initDh1CandC S K
                (.zero : Var (.list (.prod (B 32) (B 32)) :: .opt (B 32) :: Δ) (.list (.prod (B 32) (B 32))))
                (.zero : Var (.list (.prod (B 32) (B 32)) :: .list (.prod (B 32) (B 32)) :: .opt (B 32) :: Δ)
                  (.list (.prod (B 32) (B 32))))
                s)).eval
          (.cons ((smPows (v sm)).eval (.cons spkPows (.cons noneOpt ρ))) (.cons spkPows (.cons noneOpt ρ))) := by
      simp only [foldMV, Comp.eval, Expr.eval]
      rw [take_min_eq_of_length_le _ (by simpa [smBase, stSess, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', Expr.eval, Env.get] using hSess) hOnLe]
      refine congrArg (fun f => _root_.ReductionDsl.foldML f _ _) (funext fun s => funext fun acc => ?_)
      cases acc with
      | some _ => rfl
      | none =>
        simp only [findMapStepC, caseOptV, bindV, initDh1CandC, lookupFromPowsE, eFind, Comp.eval, bind_assoc]
        refine bind_congr_support _ _ _ fun wSpk _ => ?_
        have h1 := take_min_eq_of_length_le (N := S.N_dh) _ hSpkPowsLen hOnLe
        have h2 := List.take_of_length_le hPows
        have h3 := List.take_of_length_le (Nat.le_trans hPows hOnLe)
        simp only [smPows, v, Expr.eval] at h2 h3
        simp only [gPrim, liftBase, qX25519, eCaseOpt, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', v, smPows, Comp.eval, Expr.eval]
        rw [h1, h2, h3]
    rw [hFold1]
    refine bind_congr_support _ _ _ fun f2 _ => ?_
    cases f2 with
    | some z => rfl
    | none =>
      simp only [foldMV, Comp.eval, Expr.eval]
      rw [take_min_eq_of_length_le _ (by simpa [smBase, stResps, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', Expr.eval, Env.get] using hResps) hOnLe]
      refine congrArg (fun m : OracleComp _ _ => m >>= _)
        (congrArg (fun f => _root_.ReductionDsl.foldML f _ _) (funext fun r => funext fun acc => ?_))
      cases acc with
      | some _ => rfl
      | none =>
        simp only [findMapStepC, caseOptV, bindV, respDh1CandC, eFind, Comp.eval]
        have hSpksTake := take_min_eq_of_length_le (N := S.N_dh) _ hSpks hOnLe
        simp only [smBase, v, Expr.eval] at hSpksTake
        simp only [gPrim, liftBase, qX25519, eCaseOpt, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', v, smBase, Comp.eval, Expr.eval]
        rw [hSpksTake]

private theorem extractMode0_2KC_eq (S : Setup) (f : KeyIndKFuels) (K : ℕ)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (ρ : Env Δ)
    (hOnLe : f.kOn ≤ K) (hOffLe : f.kOff ≤ K)
    (hLog : ((smLog (v sm)).eval ρ).length ≤ f.kOff)
    (hPows : ((smPows (v sm)).eval ρ).length ≤ f.kOn)
    (hSpks : ((stSpks (smBase (v sm))).eval ρ).length ≤ f.kOn)
    (hSess : ((stSess (smBase (v sm))).eval ρ).length ≤ f.kOn)
    (hResps : ((stResps (smBase (v sm))).eval ρ).length ≤ f.kOn) :
    (extractMode0_2KC S f pa sm).eval ρ = (extractMode0_2C S K pa sm).eval ρ := by
  unfold extractMode0_2KC extractMode0_2C
  have hMap : (eMap f.kOff (smLog (v sm)) fun sec => slice32 32 (v sec)).eval ρ =
      (eMap K (smLog (v sm)) fun sec => slice32 32 (v sec)).eval ρ := by
    simp only [eMap, Expr.eval, List.take_of_length_le hLog, List.take_of_length_le (Nat.le_trans hLog hOffLe)]
  have hCandLen : ((eMap K (smLog (v sm)) fun sec => slice32 32 (v sec)).eval ρ).length ≤ f.kOff := by
    simp only [eMap, Expr.eval, List.length_map, List.length_take]; omega
  simp only [bindV, caseOptV, letV, Comp.eval]
  have hFind :
      (findMV f.kOff (eMap f.kOff (smLog (v sm)) fun sec => slice32 32 (v sec))
          fun z => ddhQ (pa2U (v pa)) (pa2V (v pa)) (v z)).eval ρ =
      (findMV K (eMap K (smLog (v sm)) fun sec => slice32 32 (v sec))
          fun z => ddhQ (pa2U (v pa)) (pa2V (v pa)) (v z)).eval ρ := by
    simp only [findMV, Comp.eval, hMap, List.take_of_length_le hCandLen,
      List.take_of_length_le (Nat.le_trans hCandLen hOffLe)]
  rw [hFind]
  refine bind_congr_support _ _ _ fun f1 _ => ?_
  cases f1 with
  | some z => rfl
  | none =>
    let noneOpt : (Ty.opt (B 32)).denote := none
    have hSpks' : ((stSpks (smBase (v sm))).eval (.cons noneOpt ρ)).length ≤ f.kOn := by
      simpa [smBase, stSpks, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', Expr.eval, Env.get] using hSpks
    have hSpkPows : (spkPowsC S f.kOn (stSpks (smBase (v sm)))).eval (.cons noneOpt ρ) =
        (spkPowsC S K (stSpks (smBase (v sm)))).eval (.cons noneOpt ρ) := by
      simp only [spkPowsC, mapMV, Comp.eval]; rw [take_min_eq_of_length_le _ hSpks' hOnLe]
    rw [hSpkPows]
    refine bind_congr_support _ _ _ fun spkPows hMemSpk => ?_
    have hSpkPowsLen : spkPows.length ≤ f.kOn := by
      rw [mapMV_length_eq (min K S.N_dh) _ _ (.cons noneOpt ρ) hMemSpk, List.length_take]
      exact Nat.le_trans (Nat.min_le_right _ _) hSpks'
    simp only [Expr.eval, pure_bind]
    have hFold1 :
        (foldMV (min f.kOn S.N_dh) (stSess (smBase (v sm))) .none fun s acc => findMapStep2C pa acc
            (initDh1CandC S f.kOn (.zero : Var (.list (.prod (B 32) (B 32)) :: .opt (B 32) :: Δ) _)
              (.zero : Var (.list (.prod (B 32) (B 32)) :: .list (.prod (B 32) (B 32)) :: .opt (B 32) :: Δ) _) s)).eval
          (.cons ((smPows (v sm)).eval (.cons spkPows (.cons noneOpt ρ))) (.cons spkPows (.cons noneOpt ρ))) =
        (foldMV (min K S.N_dh) (stSess (smBase (v sm))) .none fun s acc => findMapStep2C pa acc
            (initDh1CandC S K (.zero : Var (.list (.prod (B 32) (B 32)) :: .opt (B 32) :: Δ) _)
              (.zero : Var (.list (.prod (B 32) (B 32)) :: .list (.prod (B 32) (B 32)) :: .opt (B 32) :: Δ) _) s)).eval
          (.cons ((smPows (v sm)).eval (.cons spkPows (.cons noneOpt ρ))) (.cons spkPows (.cons noneOpt ρ))) := by
      simp only [foldMV, Comp.eval, Expr.eval]
      rw [take_min_eq_of_length_le _ (by simpa [smBase, stSess, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', Expr.eval, Env.get] using hSess) hOnLe]
      refine congrArg (fun f => _root_.ReductionDsl.foldML f _ _) (funext fun s => funext fun acc => ?_)
      cases acc with
      | some _ => rfl
      | none =>
        simp only [findMapStep2C, caseOptV, bindV, initDh1CandC, lookupFromPowsE, eFind, Comp.eval, bind_assoc]
        refine bind_congr_support _ _ _ fun wSpk _ => ?_
        have h1 := take_min_eq_of_length_le (N := S.N_dh) _ hSpkPowsLen hOnLe
        have h2 := List.take_of_length_le hPows
        have h3 := List.take_of_length_le (Nat.le_trans hPows hOnLe)
        simp only [smPows, v, Expr.eval] at h2 h3
        simp only [gPrim, liftBase, qX25519, eCaseOpt, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', v, smPows, Comp.eval, Expr.eval]
        rw [h1, h2, h3]
    rw [hFold1]
    refine bind_congr_support _ _ _ fun f2 _ => ?_
    cases f2 with
    | some z => rfl
    | none =>
      simp only [foldMV, Comp.eval, Expr.eval]
      rw [take_min_eq_of_length_le _ (by simpa [smBase, stResps, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', Expr.eval, Env.get] using hResps) hOnLe]
      refine congrArg (fun m : OracleComp _ _ => m >>= _)
        (congrArg (fun f => _root_.ReductionDsl.foldML f _ _) (funext fun r => funext fun acc => ?_))
      cases acc with
      | some _ => rfl
      | none =>
        simp only [findMapStep2C, caseOptV, bindV, respDh1CandC, eFind, Comp.eval]
        have hSpksTake := take_min_eq_of_length_le (N := S.N_dh) _ hSpks hOnLe
        simp only [smBase, v, Expr.eval] at hSpksTake
        simp only [gPrim, liftBase, qX25519, eCaseOpt, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', v, smBase, Comp.eval, Expr.eval]
        rw [hSpksTake]

private theorem gdhFinishK_unsupported (S : Setup) (f : KeyIndKFuels) :
    (gdhFinishK S f).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [-sup_of_le_left, -sup_of_le_right, gdhFinishK, extractMode0KC, logFindC, spkPowsC, findMapStepC,
    initDh1CandC, respDh1CandC, letV, bindV, caseOptV, findMV, mapMV, foldMV, ddhQ, gPrim, liftBase, qPow8,
    qX25519, Comp.queries, tlGapDhKeyInd, AtomicLift.keyIndUnsupportedPrimW]

private theorem gdhFinish_unsupported (S : Setup) (K : ℕ) :
    (gdhFinish S K).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [-sup_of_le_left, -sup_of_le_right, gdhFinish, extractMode0C, logFindC, spkPowsC, findMapStepC,
    initDh1CandC, respDh1CandC, letV, bindV, caseOptV, findMV, mapMV, foldMV, ddhQ, gPrim, liftBase, qPow8,
    qX25519, Comp.queries, tlGapDhKeyInd, AtomicLift.keyIndUnsupportedPrimW]

private theorem gdhFinish2K_unsupported (S : Setup) (f : KeyIndKFuels) :
    (gdhFinish2K S f).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [-sup_of_le_left, -sup_of_le_right, gdhFinish2K, extractMode0_2KC, logFind2C, spkPowsC, findMapStep2C,
    initDh1CandC, respDh1CandC, letV, bindV, caseOptV, findMV, mapMV, foldMV, ddhQ, gPrim, liftBase, qPow8,
    qX25519, Comp.queries, tlGapDhKeyInd, AtomicLift.keyIndUnsupportedPrimW]

private theorem gdhFinish2_unsupported (S : Setup) (K : ℕ) :
    (gdhFinish2 S K).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [-sup_of_le_left, -sup_of_le_right, gdhFinish2, extractMode0_2C, logFind2C, spkPowsC, findMapStep2C,
    initDh1CandC, respDh1CandC, letV, bindV, caseOptV, findMV, mapMV, foldMV, ddhQ, gPrim, liftBase, qPow8,
    qX25519, Comp.queries, tlGapDhKeyInd, AtomicLift.keyIndUnsupportedPrimW]

private theorem gdhFinishK_eq (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (pa : paramsTy.denote) (sm : simTy.denote) (sh : fgShadowAtomicTy.denote) (aOut : Bool)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hInv : GdhSimInv S b c (embedVal simTy sm, sh)) :
    (gdhFinishK S (keyIndKFuelsOfBudget S b)).eval (.cons (pa, sm) (.cons aOut .nil)) =
      (gdhFinish S b.q_total).eval (.cons (pa, sm) (.cons aOut .nil)) := by
  set f := keyIndKFuelsOfBudget S b
  have hOnLe : f.kOn ≤ b.q_total := Nat.min_le_right _ _
  have hOffLe : f.kOff ≤ b.q_total := Nat.min_le_right _ _
  have hBase : BaseOnlineLenInv c sm.1 := by
    have h := hInv.online_len
    have hEq : (embedVal simTy sm).1 = embedVal keyIndStateTy sm.1 := rfl
    rw [hEq, AtomicLift.projVal_embedVal] at h
    exact h
  have h0 : c 0 ≤ f.kOn := hB 0
  have hLog : sm.2.2.2.1.length ≤ f.kOff := by
    have h := hInv.smLog_length_le_kOff hB
    have hEq : (embedVal simTy sm).2.2.2.1 = sm.2.2.2.1.map (embedVal (B 192)) := rfl
    rw [hEq, List.length_map] at h; exact h
  have hPows : sm.2.2.2.2.length ≤ f.kOn := by
    have h := hInv.smPows_length_le_kOn hB
    have hEq : (embedVal simTy sm).2.2.2.2 = sm.2.2.2.2.map (embedVal (.prod (B 32) (B 32))) := rfl
    rw [hEq, List.length_map] at h; exact h
  have hSpks : sm.1.2.2.1.length ≤ f.kOn := Nat.le_trans hBase.spks_le h0
  have hSess : sm.1.2.2.2.2.1.length ≤ f.kOn := Nat.le_trans hBase.sess_le h0
  have hResps : sm.1.2.2.2.2.2.1.length ≤ f.kOn := Nat.le_trans hBase.resps_le h0
  let aOutT : (Ty.bool : PT).denote := aOut
  let stT : gdhStateTy.denote := (pa, sm)
  have hLogE :
      ((smLog (v (.zero : Var [simTy, paramsTy, gdhStateTy, .bool] simTy))).eval
        (.cons sm (.cons pa (.cons stT (.cons aOutT .nil))))).length ≤ f.kOff := by
    simpa [smLog, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', Expr.eval, Env.get] using hLog
  unfold gdhFinishK gdhFinish
  simp only [letV, Comp.eval, Expr.eval, Env.get, pure_bind,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq, paMode, v,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk']
  split_ifs
  · exact extractMode0KC_eq S f b.q_total
      (Γ₁ := [paramsTy, gdhStateTy, .bool]) (Γ₂ := [simTy, paramsTy, gdhStateTy, .bool])
      .zero .zero _ hOnLe hOffLe hLogE
      (by simpa [smPows, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', Expr.eval, Env.get] using hPows)
      (by simpa [smBase, stSpks, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', Expr.eval, Env.get] using hSpks)
      (by simpa [smBase, stSess, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', Expr.eval, Env.get] using hSess)
      (by simpa [smBase, stResps, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', Expr.eval, Env.get] using hResps)
  · exact logFindC_eq_of_le f.kOff b.q_total 96
      (Γ₁ := [paramsTy, gdhStateTy, .bool]) (Γ₂ := [simTy, paramsTy, gdhStateTy, .bool])
      .zero .zero _ hLogE hOffLe
  · exact logFindC_eq_of_le f.kOff b.q_total 64
      (Γ₁ := [paramsTy, gdhStateTy, .bool]) (Γ₂ := [simTy, paramsTy, gdhStateTy, .bool])
      .zero .zero _ hLogE hOffLe
  · exact logFindC_eq_of_le f.kOff b.q_total 128
      (Γ₁ := [paramsTy, gdhStateTy, .bool]) (Γ₂ := [simTy, paramsTy, gdhStateTy, .bool])
      .zero .zero _ hLogE hOffLe

private theorem gdhFinish2K_eq (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (pa : params2Ty.denote) (sm : simTy.denote) (sh : fgShadowAtomicTy.denote) (aOut : Bool)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hInv : GdhSimInv S b c (embedVal simTy sm, sh)) :
    (gdhFinish2K S (keyIndKFuelsOfBudget S b)).eval (.cons (pa, sm) (.cons aOut .nil)) =
      (gdhFinish2 S b.q_total).eval (.cons (pa, sm) (.cons aOut .nil)) := by
  set f := keyIndKFuelsOfBudget S b
  have hOnLe : f.kOn ≤ b.q_total := Nat.min_le_right _ _
  have hOffLe : f.kOff ≤ b.q_total := Nat.min_le_right _ _
  have hBase : BaseOnlineLenInv c sm.1 := by
    have h := hInv.online_len
    have hEq : (embedVal simTy sm).1 = embedVal keyIndStateTy sm.1 := rfl
    rw [hEq, AtomicLift.projVal_embedVal] at h
    exact h
  have h0 : c 0 ≤ f.kOn := hB 0
  have hLog : sm.2.2.2.1.length ≤ f.kOff := by
    have h := hInv.smLog_length_le_kOff hB
    have hEq : (embedVal simTy sm).2.2.2.1 = sm.2.2.2.1.map (embedVal (B 192)) := rfl
    rw [hEq, List.length_map] at h; exact h
  have hPows : sm.2.2.2.2.length ≤ f.kOn := by
    have h := hInv.smPows_length_le_kOn hB
    have hEq : (embedVal simTy sm).2.2.2.2 = sm.2.2.2.2.map (embedVal (.prod (B 32) (B 32))) := rfl
    rw [hEq, List.length_map] at h; exact h
  have hSpks : sm.1.2.2.1.length ≤ f.kOn := Nat.le_trans hBase.spks_le h0
  have hSess : sm.1.2.2.2.2.1.length ≤ f.kOn := Nat.le_trans hBase.sess_le h0
  have hResps : sm.1.2.2.2.2.2.1.length ≤ f.kOn := Nat.le_trans hBase.resps_le h0
  let aOutT : (Ty.bool : PT).denote := aOut
  let st2T : gdhState2Ty.denote := (pa, sm)
  have hLogE :
      ((smLog (v (.zero : Var [simTy, params2Ty, gdhState2Ty, .bool] simTy))).eval
        (.cons sm (.cons pa (.cons st2T (.cons aOutT .nil))))).length ≤ f.kOff := by
    simpa [smLog, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', Expr.eval, Env.get] using hLog
  unfold gdhFinish2K gdhFinish2
  simp only [letV, Comp.eval, Expr.eval, Env.get, pure_bind,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq, pa2Mode, v,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk']
  split_ifs
  · exact extractMode0_2KC_eq S f b.q_total
      (Γ₁ := [params2Ty, gdhState2Ty, .bool]) (Γ₂ := [simTy, params2Ty, gdhState2Ty, .bool])
      .zero .zero _ hOnLe hOffLe hLogE
      (by simpa [smPows, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', Expr.eval, Env.get] using hPows)
      (by simpa [smBase, stSpks, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', Expr.eval, Env.get] using hSpks)
      (by simpa [smBase, stSess, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', Expr.eval, Env.get] using hSess)
      (by simpa [smBase, stResps, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', Expr.eval, Env.get] using hResps)
  · exact logFind2C_eq_of_le f.kOff b.q_total 96
      (Γ₁ := [params2Ty, gdhState2Ty, .bool]) (Γ₂ := [simTy, params2Ty, gdhState2Ty, .bool])
      .zero .zero _ hLogE hOffLe
  · exact logFind2C_eq_of_le f.kOff b.q_total 64
      (Γ₁ := [params2Ty, gdhState2Ty, .bool]) (Γ₂ := [simTy, params2Ty, gdhState2Ty, .bool])
      .zero .zero _ hLogE hOffLe
  · exact logFind2C_eq_of_le f.kOff b.q_total 128
      (Γ₁ := [params2Ty, gdhState2Ty, .bool]) (Γ₂ := [simTy, params2Ty, gdhState2Ty, .bool])
      .zero .zero _ hLogE hOffLe

private theorem logFindC_congr_uv (K off : ℕ)
    (u vPk : (B 32).denote) (rest1 rest2 : _)
    (sm : simTy.denote) (aOut : (Ty.bool : PT).denote) :
    (logFindC (Δ := [simTy, paramsTy, gdhStateTy, .bool]) K off
      (.zero : Var [paramsTy, gdhStateTy, .bool] paramsTy)
      (.zero : Var [simTy, paramsTy, gdhStateTy, .bool] simTy)).eval
        (.cons sm (.cons (u, vPk, rest1) (.cons ((u, vPk, rest1), sm) (.cons aOut .nil)))) =
    (logFindC (Δ := [simTy, paramsTy, gdhStateTy, .bool]) K off
      (.zero : Var [paramsTy, gdhStateTy, .bool] paramsTy)
      (.zero : Var [simTy, paramsTy, gdhStateTy, .bool] simTy)).eval
        (.cons sm (.cons (u, vPk, rest2) (.cons ((u, vPk, rest2), sm) (.cons aOut .nil)))) := by
  unfold logFindC
  simp only [bindV, findMV, Comp.eval, smLog, v,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk']
  refine congrArg₂ Bind.bind ?_ (funext fun found => ?_)
  · apply congrArg₂ _root_.ReductionDsl.findML
    · funext z
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.ddhQ, paU, paV,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        Comp.eval, Expr.eval]
    · simp only [eMap, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.slice32,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.takeKB,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.dropB,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero']
  · cases found <;> rfl

private theorem findMapStepC_congr {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (acc : Var Γ₂ (.opt (B 32)))
    (cand : Comp pqxdhOps pqGapDhIface Δ (B 32)) (ρ₁ ρ₂ : Env Δ)
    (hAcc : (v acc).eval ρ₁ = (v acc).eval ρ₂)
    (hU : (paU (v pa)).eval ρ₁ = (paU (v pa)).eval ρ₂)
    (hV : (paV (v pa)).eval ρ₁ = (paV (v pa)).eval ρ₂)
    (hCand : cand.eval ρ₁ = cand.eval ρ₂) :
    (findMapStepC pa acc cand).eval ρ₁ = (findMapStepC pa acc cand).eval ρ₂ := by
  have hU' : ∀ z : (B 32).denote,
      (paU (v pa : Expr pqxdhOps (B 32 :: Δ) paramsTy)).eval (.cons z ρ₁) =
        (paU (v pa : Expr pqxdhOps (B 32 :: Δ) paramsTy)).eval (.cons z ρ₂) := fun _ => hU
  have hV' : ∀ z : (B 32).denote,
      (paV (v pa : Expr pqxdhOps (B 32 :: Δ) paramsTy)).eval (.cons z ρ₁) =
        (paV (v pa : Expr pqxdhOps (B 32 :: Δ) paramsTy)).eval (.cons z ρ₂) := fun _ => hV
  unfold findMapStepC
  simp only [caseOptV, bindV, Comp.eval, hAcc]
  cases (v acc).eval ρ₂ with
  | some _ => exact congrArg pure hAcc
  | none =>
    rw [hCand]
    refine congrArg₂ Bind.bind rfl (funext fun z => ?_)
    have hDdh :
        (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.ddhQ
          (paU (v pa)) (paV (v pa)) (v (.zero : Var (B 32 :: Δ) (B 32)))).eval (.cons z ρ₁) =
        (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.ddhQ
          (paU (v pa)) (paV (v pa)) (v (.zero : Var (B 32 :: Δ) (B 32)))).eval (.cons z ρ₂) := by
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.ddhQ, Comp.eval, Expr.eval]
      rw [hU' z, hV' z]; rfl
    rw [hDdh]
    refine congrArg₂ Bind.bind rfl (funext fun ok => ?_)
    cases ok <;> rfl

private theorem initDh1CandC_congr (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (spkPows : Var Γ₁ (.list (.prod (B 32) (B 32))))
    (advPows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    (s : Var Δ keyIndSessionEntryTy) (ρ₁ ρ₂ : Env Δ)
    (hSpk : (v spkPows).eval ρ₁ = (v spkPows).eval ρ₂)
    (hAdv : (v advPows).eval ρ₁ = (v advPows).eval ρ₂)
    (hS : (v s).eval ρ₁ = (v s).eval ρ₂) :
    (initDh1CandC S K spkPows advPows s).eval ρ₁ = (initDh1CandC S K spkPows advPows s).eval ρ₂ := by
  simp only [v, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk'] at hSpk hAdv hS
  unfold initDh1CandC
  simp only [bindV, gPrim, liftBase, qPow8, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sePeerSpk,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', v, Comp.eval, Expr.eval]
  rw [hS]
  refine congrArg₂ Bind.bind rfl (funext fun wSpk => ?_)
  simp only [lookupFromPowsE, eFind, eCaseOpt, eqB, litB, liftBase, qX25519,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.seHdr,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.hdIkAPk,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero', v, Comp.eval, Expr.eval]
  rw [hSpk, hAdv, hS]

private theorem respDh1CandC_congr (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (spks : Var Γ₁ (.list (.prod (.prod .nat .nat) spkBundleEntryTy)))
    (r : Var Γ₂ keyIndRespEntryTy) (ρ₁ ρ₂ : Env Δ)
    (hSpks : (v spks).eval ρ₁ = (v spks).eval ρ₂)
    (hR : (v r).eval ρ₁ = (v r).eval ρ₂) :
    (respDh1CandC S K spks r).eval ρ₁ = (respDh1CandC S K spks r).eval ρ₂ := by
  simp only [v, Expr.eval] at hSpks hR
  unfold respDh1CandC
  simp only [gPrim, liftBase, qX25519, Comp.eval]
  refine congrArg (fun p => pqGapDhIface.dec (.inl .x25519) p <$>
    liftM (OracleSpec.query (pqGapDhIface.enc (.inl .x25519) p))) ?_
  simp only [eCaseOpt, eFind, litB, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sbSpkSk,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat2Eq, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.respBundleKeyE, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.reSid,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseSum, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero', v, Expr.eval, hSpks, hR]; rfl

private theorem extractMode0C_congr_uv (S : Setup) (K : ℕ)
    (u vPk : (B 32).denote) (rest1 rest2 : _)
    (sm : simTy.denote) (aOut : (Ty.bool : PT).denote) :
    (extractMode0C (Δ := [simTy, paramsTy, gdhStateTy, .bool]) S K
      (.zero : Var [paramsTy, gdhStateTy, .bool] paramsTy)
      (.zero : Var [simTy, paramsTy, gdhStateTy, .bool] simTy)).eval
        (.cons sm (.cons (u, vPk, rest1) (.cons ((u, vPk, rest1), sm) (.cons aOut .nil)))) =
    (extractMode0C (Δ := [simTy, paramsTy, gdhStateTy, .bool]) S K
      (.zero : Var [paramsTy, gdhStateTy, .bool] paramsTy)
      (.zero : Var [simTy, paramsTy, gdhStateTy, .bool] simTy)).eval
        (.cons sm (.cons (u, vPk, rest2) (.cons ((u, vPk, rest2), sm) (.cons aOut .nil)))) := by
  unfold extractMode0C
  simp only [bindV, caseOptV, letV, findMV, eMap, Comp.eval, Expr.eval, pure_bind, smLog, v,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk']
  refine congrArg₂ Bind.bind ?_ (funext fun f1 => ?_)
  · apply congrArg₂ _root_.ReductionDsl.findML
    · funext z
      simp only [ddhQ, paU, paV, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Comp.eval, Expr.eval]
    · rfl
  cases f1 with
  | some _ => rfl
  | none =>
    simp only [spkPowsC, mapMV, Comp.eval, Expr.eval, stSpks, smBase, v,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ']
    refine congrArg₂ Bind.bind ?_ (funext fun spkPows => ?_)
    · apply congrArg₂ _root_.ReductionDsl.mapML
      · funext sb
        simp only [bindV, gPrim, liftBase, qPow8,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sbSpkPk, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sbSpkSk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
          Comp.eval, Expr.eval]
      · rfl
    simp only [foldMV, Comp.eval, Expr.eval, smPows, stSess,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ']
    refine congrArg₂ Bind.bind ?_ (funext fun f2 => ?_)
    · apply congrArg (fun f => _root_.ReductionDsl.foldML f _ _)
      funext s acc
      exact findMapStepC_congr _ _ _ _ _
        (by simp only [v, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero'])
        (by simp only [paU, v, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero'])
        (by simp only [paV, v, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero'])
        (initDh1CandC_congr S K _ _ _ _ _
          (by simp only [v, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero'])
          (by simp only [v, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero'])
          (by simp only [v, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero']))
    cases f2 with
    | some _ => rfl
    | none =>
      refine congrArg₂ Bind.bind ?_ (funext fun f3 => ?_)
      · apply congrArg (fun f => _root_.ReductionDsl.foldML f _ _)
        funext r acc
        exact findMapStepC_congr _ _ _ _ _
          (by simp only [v, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero'])
          (by simp only [paU, v, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero'])
          (by simp only [paV, v, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero'])
          (respDh1CandC_congr S K _ _ _ _
            (by simp only [v, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero'])
            (by simp only [v, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero']))
      cases f3 <;> rfl

private theorem gdhFinish_fixParamsSentLeg_eq (S : Setup) (b : QueryBudget) (K : ℕ)
    (pa : paramsTy.denote) (sm : simTy.denote) (aOut : Bool) :
    (gdhFinish S K).eval (.cons (fixParamsSentLeg S b pa, sm) (.cons aOut .nil)) =
      (gdhFinish S K).eval (.cons (pa, sm) (.cons aOut .nil)) := by
  have hMode : (fixParamsSentLeg S b pa).2.2.2.2.2.2.2.2.2.2 = pa.2.2.2.2.2.2.2.2.2.2 := by
    rcases pa with ⟨_, _, _, _, _, _, _, _, _, _, _⟩; rfl
  have hEq : ∃ u vPk r1 r2, fixParamsSentLeg S b pa = (u, vPk, r1) ∧ pa = (u, vPk, r2) := by
    rcases pa with ⟨u, vPk, up, pF, pI, dF, eI, sI, oM, oI, md⟩
    exact ⟨u, vPk, _, _, rfl, rfl⟩
  unfold gdhFinish
  simp only [letV, Comp.eval, Expr.eval, Env.get, pure_bind,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq, paMode, v,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk', _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk']
  rw [hMode]
  rcases hEq with ⟨u, vPk, r1, r2, h1, h2⟩
  rw [h1, h2]
  split_ifs
  · exact extractMode0C_congr_uv S K u vPk r1 r2 sm aOut
  · exact logFindC_congr_uv K 96 u vPk r1 r2 sm aOut
  · exact logFindC_congr_uv K 64 u vPk r1 r2 sm aOut
  · exact logFindC_congr_uv K 128 u vPk r1 r2 sm aOut

/-- `finish` fuel-identity simulation for tuple-keyed `gdhShadowFinish2Atomic` vs `gdhFinish2`. -/
theorem gdhShadowFinish2Atomic_sim {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A}
    {evalGdh : ∀ {α : Type}, OracleComp _root_.SignalPqxdh.Security.FgGapDh.GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh)
    (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (s' : gdhShadowState2AtomicTy.denote) (aOut : Bool)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j) (hInv : Gdh2SimInv S b c s') :
    (gdhShadowFinish2Atomic gl S (keyIndKFuelsOfBudget S b)).eval (.cons s' (.cons aOut .nil)) =
      (runAt2 .v0 .v1 (liftGdhAtomic gl (gdhFinish2 S b.q_total))).eval
        (.cons (forgetGdhShadow2 s') (.cons aOut .nil)) := by
  simp only [gdhShadowFinish2Atomic, forgetGdhShadow2, runAt2_eval,
    Expr.eval, _root_.ReductionDsl.Expr.v0, _root_.ReductionDsl.Expr.v1, Env.get]
  have hEnv :
      (Env.cons s'.1 (.cons aOut .nil) : Env [embedTy gdhState2Ty, .bool]) =
        embedEnv (.cons (projVal gdhState2Ty s'.1) (.cons aOut .nil) :
          Env [gdhState2Ty, .bool]) := by
    simp only [embedEnv, AtomicLift.embedVal_projVal]; rfl
  rw [hEnv,
      hgl.liftGdhAtomic_eval _ (gdhFinish2K_unsupported S _) _,
      hgl.liftGdhAtomic_eval _ (gdhFinish2_unsupported S b.q_total) _]
  have hInv' : GdhSimInv S b c (embedVal simTy (projVal gdhState2Ty s'.1).2, s'.2) := by
    rw [show (projVal gdhState2Ty s'.1).2 = projVal simTy s'.1.2 from rfl, AtomicLift.embedVal_projVal]
    exact hInv
  rw [gdhFinish2K_eq S b c (projVal gdhState2Ty s'.1).1 (projVal gdhState2Ty s'.1).2 s'.2 aOut hB hInv']

/-- `StepSim.ForgetSim.hFinish` for `fgKeyInd1KeyGapDhKindAtomicProg` vs
    `fgKeyInd1KeyGapDhActiveAtomicProg`. -/
theorem fgKeyInd1KeyGapDhKindAtomicProg_hFinish (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (s' : (fgKeyInd1KeyGapDhKindAtomicProg S b).σ.denote) (aOut : Bool)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j) (hInv : Gdh1KeyActiveSimInv S b c s') :
    (fgKeyInd1KeyGapDhKindAtomicProg S b).finish.eval (.cons s' (.cons aOut .nil)) =
      (fgKeyInd1KeyGapDhActiveAtomicProg S b).finish.eval
        (.cons (forgetGdh1KeyActiveK S b s') (.cons aOut .nil)) := by
  simp only [fgKeyInd1KeyGapDhKindAtomicProg, gdh1KeyKindFinishC, runAt2_eval,
    Expr.eval, _root_.ReductionDsl.Expr.v0, _root_.ReductionDsl.Expr.v1, Env.get]
  have hEnvK :
      (Env.cons s'.1.1.1 (.cons aOut .nil) : Env [embedTy gdhStateTy, .bool]) =
        embedEnv (.cons (projVal gdhStateTy s'.1.1.1) (.cons aOut .nil) :
          Env [gdhStateTy, .bool]) := by
    simp only [embedEnv, AtomicLift.embedVal_projVal]; rfl
  rw [hEnvK, gdhLift1Key_valid.liftGdhAtomic_eval _ (gdhFinishK_unsupported S _) _]
  have hActiveUnsup :
      (fgKeyInd1KeyGapDhActiveDslProg S b).finish.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
    have h1 := KeyIndGapDhKSimBase.liftGdhComp_unsupported_keyInd (gdhFinish S b.q_total)
    rw [gdhFinish_unsupported] at h1
    have hRen : ∀ {Γ Δ : List PT} {τ : PT} (ρ : _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.Ren Γ Δ)
        (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface Γ τ),
        (renameComp ρ c).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) =
          c.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) := by
      intro Γ Δ τ ρ c; induction c generalizing Δ <;> simp_all [renameComp, Comp.queries]
    simp [fgKeyInd1KeyGapDhActiveDslProg,
      Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.gdh1KeyActiveFinish, letV,
      Comp.queries, hRen, h1]
  have hEnvOld :
      (Env.cons (forgetGdh1KeyActiveK S b s') (.cons aOut .nil) :
          Env [embedTy gdh1KeyActiveStateTy, .bool]) =
        embedEnv (.cons (projVal gdh1KeyActiveStateTy (forgetGdh1KeyActiveK S b s'))
          (.cons aOut .nil) : Env [gdh1KeyActiveStateTy, .bool]) := by
    simp only [embedEnv, AtomicLift.embedVal_projVal]; rfl
  simp only [fgKeyInd1KeyGapDhActiveAtomicProg, liftKeyInd1Stage]
  rw [hEnvOld, mapComp_eval tlSigDdhKeyInd _ hActiveUnsup _]
  simp only [fgKeyInd1KeyGapDhActiveDslProg,
    Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.gdh1KeyActiveFinish,
    letV, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
    Comp.eval, Expr.eval, Env.get, pure_bind, renameComp_eval, pullEnv_twoVarRen, liftGdhComp_eval]
  have hProjForget :
      (projVal gdh1KeyActiveStateTy (forgetGdh1KeyActiveK S b s')).1.1 =
        (fixParamsSentLeg S b (projVal paramsTy s'.1.1.1.1), projVal simTy s'.1.1.1.2) := by
    rcases s' with ⟨⟨⟨⟨paA, smA⟩, sigB⟩, rest⟩, sh⟩
    have hPa : projVal paramsTy (fixParamsSent S b paA) = fixParamsSentLeg S b (projVal paramsTy paA) := by
      conv_lhs => rw [← AtomicLift.embedVal_projVal paramsTy paA]
      rw [← embedVal_fixParamsSentLeg, AtomicLift.projVal_embedVal]
    change (projVal paramsTy (fixParamsSent S b paA), projVal simTy smA) =
      (fixParamsSentLeg S b (projVal paramsTy paA), projVal simTy smA)
    rw [hPa]
  rw [hProjForget, gdhFinish_fixParamsSentLeg_eq]
  have hInv' : GdhSimInv S b c (embedVal simTy (projVal simTy s'.1.1.1.2), s'.2) := by
    simpa [AtomicLift.embedVal_projVal] using hInv.sim_inv
  have hStEq : projVal gdhStateTy s'.1.1.1 = (projVal paramsTy s'.1.1.1.1, projVal simTy s'.1.1.1.2) := rfl
  rw [hStEq, gdhFinishK_eq S b c (projVal paramsTy s'.1.1.1.1) (projVal simTy s'.1.1.1.2) s'.2 aOut hB hInv']

end InitAndFinish

end

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimMisc
