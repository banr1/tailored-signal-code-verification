/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhStepInit
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure
import VCVio.CryptoFoundations.SecExp.Measure

/-!
# Active `GapDhWithSign` Parameter Sampler Evaluation Equivalence

Proves unsupported-query vanishing, evaluation equivalence, distributional equivalence against
flat-index decoding, and `GapDhWithSign` advantage equality for `initParams1KeyActiveC` and
`fgKeyInd1KeyGapDhActiveAtomicProg`.
-/

set_option autoImplicit false

open OracleSpec OracleComp Function
open scoped ENNReal
open ReductionDsl (Ty Var Env Expr Comp CostedReduction handlerImpl)
open SignalPqxdh (Setup Bytes QueryBudget KeyIndQuery KeyIndResponse KeyIndAdversary
  BoundedAdv Primitives GapDhWithSignAdv GapDhWithSign GapDhWithSignReal gapDhWithSignExp
  PrimBaseSpec primBaseImpl primSpec sigAndDdhSpec sampleScalar32
  activeIdCount activeSpkCount activeOpkCount activeSendCount activeSendOpkCount
  gdhQueryBudget gdhPrimQueryBudget keyIndSpec)
open SignalPqxdh.Costed (PB pqAtomicOps pqKeyIndCodec)
open SignalPqxdh.LegacyCosted (pqSig B pqxdhOps pqPrimIface pqGapDhIface pqSigAndDdhIface
  sigAndDdhOracle keyIndCodec)
open SignalPqxdh.Security (embedUnif embedPrim)
open SignalPqxdh.Security.FgGapDh (GdhSimSpec FgKeyIndSimState unifGdh sampleIndexRange)
open SignalPqxdh.Security.FgGapDh1Key (GdhSignSimSpec FgKeyInd1KeySimState liftGdhToSign
  unifGdhSign runWithGdhSignStep)
open SignalPqxdh.Security.ReductionDsl.KeyInd (PT Ext v letV letV_eval bindV
  sBool sBool_eval sIndex sIndex_eval liftBase
  paramsTy keyIndRespTy
  paMk emptySimE gPrim
  bernoulliRatioGdhC chooseArm2C
  keyIndRespToVal
  Env.get_zero' Env.get_succ' Ext.step_wk' Ext.refl_wk')
open scoped SignalPqxdh.Security.ReductionDsl.KeyInd
open scoped SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (emptySimE_eval
  letV_queries bindV_queries
  gPrim_eval FgGapDh_embedPrim_eq FgGapDh_embedUnif_eq)
open SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (sim1KeyStateToVal
  liftGdhComp liftGdhComp_eval liftGdhToSign_bind liftGdhToSign_pure
  liftGdhToSign_query_inl)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (activeSigBudget
  fgActiveTotalIndexCount gdh1KeyActiveStateTy gdh1KeyActiveHandle gdh1KeyActiveFinish
  initParams1KeyActiveC fgKeyInd1KeyGapDhActiveDslProg fgKeyInd1KeyGapDhActiveAtomicProg)
open Computational.Proofs.SignalPqxdh.AtomicLift (liftKeyInd1Stage liftKeyInd1Stage_eval
  tlGapDhKeyInd tlSigDdhKeyInd keyIndUnsupportedPrimW embedVal)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow (FgActiveParams
  activeParamsDh1 activeParamsDh3 activeParamsDh2 activeParamsDh4
  activeParamsZero activeParamsFlat activeParamsFlat_eq_zero activeParamsFlat_mode_lt4
  activeParamsFlat_dh1 activeParamsFlat_dh3 activeParamsFlat_dh2 activeParamsFlat_dh4
  FgKeyInd1KeyActiveSimState fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveFinish
  fgKeyInd1KeyActiveRunWithParams fgKeyInd1KeyGapDhActiveRunAtFlat fgKeyInd1KeyGapDhActiveAdv4)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveInitEval

public section

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle
end

/-! ## Initialization unsupported-query vanishing -/

section Unsupported

private def zPrimW : pqPrimIface.Tag → ℕ := keyIndUnsupportedPrimW
private def zPrimWS : pqPrimIface.smp.Samp → ℕ := fun _ => 0
private def zGapDhW : pqGapDhIface.Tag → ℕ := tlGapDhKeyInd.unsupportedW
private def zGapDhWS : pqGapDhIface.smp.Samp → ℕ := fun _ => 0
private def zSigDdhW : pqSigAndDdhIface.Tag → ℕ := tlSigDdhKeyInd.unsupportedW
private def zSigDdhWS : pqSigAndDdhIface.smp.Samp → ℕ := fun _ => 0

@[simp] private theorem sBool_unsup {Γ : List PT} : (sBool (Γ := Γ)).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem sIndex_unsup (N : ℕ) {Γ : List PT} : (sIndex N (Γ := Γ)).queries zPrimW zPrimWS = 0 := rfl
@[simp] private theorem gPrim_unsup {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).queries zGapDhW zGapDhWS = c.queries zPrimW zPrimWS := by
  unfold gPrim; induction c with | query _ _ => rfl | sample _ _ => rfl | _ => simp_all [liftBase, Comp.queries]
@[simp] private theorem liftGdhComp_unsupported {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ τ) :
    (liftGdhComp c).queries zSigDdhW zSigDdhWS = c.queries zGapDhW zGapDhWS := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.queries]
@[simp] private theorem letV_u {Γ : List PT} {a b : PT} (e : Expr pqxdhOps Γ a)
    (k : Var (a :: Γ) a → Comp pqxdhOps pqSigAndDdhIface (a :: Γ) b) :
    (letV e k).queries zSigDdhW zSigDdhWS = (k .zero).queries zSigDdhW zSigDdhWS :=
  letV_queries zSigDdhW zSigDdhWS e k
@[simp] private theorem bindV_u {Γ : List PT} {a b : PT} (c : Comp pqxdhOps pqSigAndDdhIface Γ a)
    (k : Var (a :: Γ) a → Comp pqxdhOps pqSigAndDdhIface (a :: Γ) b) :
    (bindV c k).queries zSigDdhW zSigDdhWS = c.queries zSigDdhW zSigDdhWS + (k .zero).queries zSigDdhW zSigDdhWS :=
  bindV_queries zSigDdhW zSigDdhWS c k
@[simp] private theorem bindV_gdh_u {Γ : List PT} {a b : PT} (c : Comp pqxdhOps pqGapDhIface Γ a)
    (k : Var (a :: Γ) a → Comp pqxdhOps pqGapDhIface (a :: Γ) b) :
    (bindV c k).queries zGapDhW zGapDhWS = c.queries zGapDhW zGapDhWS + (k .zero).queries zGapDhW zGapDhWS :=
  bindV_queries zGapDhW zGapDhWS c k

@[simp] private theorem bernoulliRatioGdhC_unsup {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).queries zGapDhW zGapDhWS = 0 := by
  unfold bernoulliRatioGdhC
  split_ifs <;> simp [Comp.queries]

private theorem chooseArm2C_unsup {Γ₁ Δ : List PT} {α : PT} [Ext Γ₁ Δ] (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' α)
    (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).queries zGapDhW zGapDhWS = 0)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).queries zGapDhW zGapDhWS = 0) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).queries zGapDhW zGapDhWS = 0 := by
  unfold chooseArm2C
  split_ifs <;> simp [Comp.queries, h1, h2]

@[simp] private theorem initParams1KeyActiveC_unsup (S : Setup) (b : QueryBudget)
    {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))) :
    (initParams1KeyActiveC S b (Δ := Δ) uv).queries zGapDhW zGapDhWS = 0 := by
  unfold initParams1KeyActiveC
  dsimp only
  by_cases htot : fgActiveTotalIndexCount S b.q_on = 0
  · simp [htot, Comp.queries]
  · simp only [htot, ↓reduceIte]
    exact chooseArm2C_unsup _ _ _ _
      (fun {_} [_] => chooseArm2C_unsup _ _ _ _
        (fun {_} [_] => by split_ifs <;> simp [Comp.queries])
        (fun {_} [_] => by split_ifs <;> simp [Comp.queries]))
      (fun {_} [_] => chooseArm2C_unsup _ _ _ _
        (fun {_} [_] => by split_ifs <;> simp [Comp.queries])
        (fun {_} [_] => by split_ifs <;> simp [Comp.queries]))

theorem gdhActive_init_unsupported_1278 (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) =
      0 := by
  change (fgKeyInd1KeyGapDhActiveDslProg S b).init.queries zSigDdhW zSigDdhWS = 0
  simp [fgKeyInd1KeyGapDhActiveDslProg, Comp.queries]

end Unsupported

/-! ## Shallow parameter samplers and evaluation equivalence -/

@[expose] def paramsToVal (pa : FgActiveParams) : paramsTy.denote :=
  (pa.U, (pa.V, (pa.Up, (pa.prinFlag, (pa.prinIdx, (pa.dhFlag,
    (pa.ephIdx, (pa.spkIdx, (pa.opkMode, (pa.opkIdx, pa.mode))))))))))

@[expose] def sim1KeyActiveStateToVal {S : Setup} (pa : FgActiveParams)
    (stA : FgKeyInd1KeyActiveSimState S) : gdh1KeyActiveStateTy.denote :=
  (sim1KeyStateToVal (paramsToVal pa) stA.st1, (stA.resolvedPrin?, stA.sendOpkCnt))

@[expose] def encGdh1KeyActiveRS {S : Setup} (pa : FgActiveParams)
    (p : KeyIndResponse × FgKeyInd1KeyActiveSimState S) :
    (Ty.prod keyIndRespTy gdh1KeyActiveStateTy).denote :=
  (keyIndRespToVal p.1, sim1KeyActiveStateToVal pa p.2)

private noncomputable def bernoulliRatioProb (A B : Nat) : ProbComp Bool :=
  if A = 0 then pure false
  else if B = 0 then pure true
  else if A ≤ B then do
    let x ← sampleIndexRange (A + B)
    let y1 ← sampleIndexRange A
    let y2 ← sampleIndexRange A
    pure (decide (x < y1 + y2 + 1))
  else do
    let x ← sampleIndexRange (A + B)
    let y1 ← sampleIndexRange B
    let y2 ← sampleIndexRange B
    pure (!decide (x < y1 + y2 + 1))

private noncomputable def chooseArm2Prob {α : Type} (w1 w2 : Nat)
    (p1 p2 : ProbComp α) : ProbComp α :=
  if w1 = 0 then p2
  else if w2 = 0 then p1
  else do
    let sel ← bernoulliRatioProb w1 w2
    if sel = true then p1 else p2

private noncomputable def samplePairProb {α : Type} (M N : Nat) (dflt : α)
    (mk : Nat → Nat → α) : ProbComp α :=
  if M * N = 0 then pure dflt
  else do
    let i ← sampleIndexRange M
    let j ← sampleIndexRange N
    pure (mk i j)

private noncomputable def initParams1KeyActiveProb (S : Setup) (b : QueryBudget)
    (U V : Bytes) : ProbComp FgActiveParams :=
  let n_id := activeIdCount S b.q_on
  let n_spk := activeSpkCount S b.q_on
  let n_opk := activeOpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let n_send_opk := activeSendOpkCount S b.q_on
  let nA := n_id * n_spk
  let nC := n_send * n_spk
  let nB := n_send * n_id
  let nD := n_send_opk * n_opk
  if fgActiveTotalIndexCount S b.q_on = 0 then
    pure (activeParamsZero b U V)
  else
    chooseArm2Prob (nA + nC) (nB + nD)
      (chooseArm2Prob nA nC
        (samplePairProb n_id n_spk (activeParamsDh1 b U V 0 0) (activeParamsDh1 b U V))
        (samplePairProb n_send n_spk (activeParamsDh3 b U V 0 0) (activeParamsDh3 b U V)))
      (chooseArm2Prob nB nD
        (samplePairProb n_send n_id (activeParamsDh2 b U V 0 0) (activeParamsDh2 b U V))
        (samplePairProb n_send_opk n_opk (activeParamsDh4 b U V 0 0) (activeParamsDh4 b U V)))

private theorem fgEmbedPrim_bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (m : OracleComp PrimBaseSpec α) (k : α → OracleComp PrimBaseSpec β) :
    SignalPqxdh.Security.FgGapDh.embedPrim (spec := spec) (m >>= k) =
      (SignalPqxdh.Security.FgGapDh.embedPrim (spec := spec) m >>=
        fun a => SignalPqxdh.Security.FgGapDh.embedPrim (spec := spec) (k a)) := by
  rw [FgGapDh_embedPrim_eq]
  induction m using OracleComp.inductionOn with
  | pure _ => rfl
  | query_bind q cont ih =>
    simp only [bind_assoc, embedPrim, OracleComp.construct_query_bind]
    exact bind_congr ih

private theorem embedPrim_embedUnif_eq_unifGdh {α : Type} (m : ProbComp α) :
    embedPrim (embedUnif m) = unifGdh m := by
  rw [← FgGapDh_embedPrim_eq, ← FgGapDh_embedUnif_eq]; rfl

private theorem unifGdh_pure {α : Type} (x : α) :
    unifGdh (pure x : ProbComp α) = pure x := by
  simp [unifGdh, FgGapDh_embedUnif_eq, embedUnif, embedPrim]

private theorem unifGdh_bind {α β : Type} (m : ProbComp α) (f : α → ProbComp β) :
    unifGdh (m >>= f) = (unifGdh m >>= fun x => unifGdh (f x)) := by
  unfold unifGdh
  rw [FgGapDh_embedUnif_eq]
  unfold embedUnif
  rw [liftComp_bind, fgEmbedPrim_bind]
  simp only [FgGapDh_embedUnif_eq, embedUnif]

private theorem bernoulliRatioGdhC_eval {Δ : List PT} (A B : Nat) (env : Env Δ) :
    (bernoulliRatioGdhC A B).eval env = unifGdh (bernoulliRatioProb A B) := by
  unfold bernoulliRatioGdhC bernoulliRatioProb
  by_cases hA : A = 0
  · simp [hA, Comp.eval, Expr.eval, unifGdh_pure]
  · by_cases hB : B = 0
    · simp [hA, hB, Comp.eval, Expr.eval, unifGdh_pure]
    · by_cases hAB : A ≤ B <;>
      · simp only [hA, hB, hAB, ↓reduceIte, bindV, gPrim_eval, sIndex_eval, Comp.eval,
          embedPrim_embedUnif_eq_unifGdh, unifGdh_bind, unifGdh_pure]
        refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => ?_
        simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', Env.get_zero']

private theorem chooseArm2C_eval {Γ₁ : List PT} (uv : Var Γ₁ (.prod (B 32) (B 32)))
    (U V : Bytes) {α : PT} (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' α)
    (p1 p2 : ProbComp α.denote)
    (hc1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'] (env' : Env Δ'),
      env'.get (Ext.wk uv) = (U, V) → (c1 (Δ' := Δ')).eval env' = unifGdh p1)
    (hc2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'] (env' : Env Δ'),
      env'.get (Ext.wk uv) = (U, V) → (c2 (Δ' := Δ')).eval env' = unifGdh p2)
    {Δ : List PT} [Ext Γ₁ Δ] (env : Env Δ)
    (huv : env.get (Ext.wk uv) = (U, V)) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).eval env =
      unifGdh (chooseArm2Prob w1 w2 p1 p2) := by
  unfold chooseArm2C chooseArm2Prob
  by_cases hw1 : w1 = 0
  · simp [hw1, hc2 env huv]
  · by_cases hw2 : w2 = 0
    · simp [hw1, hw2, hc1 env huv]
    · simp only [hw1, hw2, ↓reduceIte, bindV, Comp.eval, bernoulliRatioGdhC_eval, unifGdh_bind]
      refine bind_congr fun sel => ?_
      have huv' : (Env.cons sel env).get (Ext.wk (Δ := .bool :: Δ) uv) = (U, V) := by
        simpa [Ext.step_wk', Env.get_succ'] using huv
      have hsel : (v (Δ := .bool :: Δ) (.zero : Var (.bool :: Δ) .bool)).eval (.cons sel env) = sel := by
        simp [v, Expr.eval, Ext.refl_wk', Env.get_zero']
      cases sel <;> simp [hsel, hc1 (.cons _ env) huv', hc2 (.cons _ env) huv']

private theorem initParams1KeyActiveC_eval (S : Setup) (b : QueryBudget)
    {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32)))
    (env : Env Δ) (U V : Bytes) (huv : env.get (Ext.wk uv) = (U, V)) :
    (initParams1KeyActiveC S b (Δ := Δ) uv).eval env =
      unifGdh (paramsToVal <$> initParams1KeyActiveProb S b U V) := by
  have hMapChoose : ∀ (w1 w2 : Nat) (q1 q2 : ProbComp FgActiveParams),
      (paramsToVal <$> chooseArm2Prob w1 w2 q1 q2) =
        chooseArm2Prob w1 w2 (paramsToVal <$> q1) (paramsToVal <$> q2) := by
    intro w1 w2 q1 q2
    unfold chooseArm2Prob
    split_ifs with h1 h2
    · rfl
    · rfl
    · simp only [map_eq_bind_pure_comp, bind_assoc]
      refine bind_congr fun sel => ?_
      cases sel <;> rfl
  have hMapPair : ∀ (M N : Nat) (dflt : FgActiveParams) (mk : Nat → Nat → FgActiveParams),
      (paramsToVal <$> samplePairProb M N dflt mk) =
        samplePairProb M N (paramsToVal dflt) (fun i j => paramsToVal (mk i j)) := by
    intro M N dflt mk
    unfold samplePairProb
    split_ifs <;> simp [map_eq_bind_pure_comp, bind_assoc]
  unfold initParams1KeyActiveC initParams1KeyActiveProb
  dsimp only
  by_cases htot : fgActiveTotalIndexCount S b.q_on = 0
  · simp [htot, v, Comp.eval, Expr.eval, huv, paMk, paramsToVal, activeParamsZero, unifGdh_pure]
  · simp only [htot, ↓reduceIte, hMapChoose, hMapPair]
    refine chooseArm2C_eval uv U V _ _ _ _ _ _
      (fun env' huv' => chooseArm2C_eval uv U V _ _ _ _ _ _
        (fun env'' huv'' => ?_) (fun env'' huv'' => ?_) env' huv')
      (fun env' huv' => chooseArm2C_eval uv U V _ _ _ _ _ _
        (fun env'' huv'' => ?_) (fun env'' huv'' => ?_) env' huv')
      env huv
    · unfold samplePairProb
      by_cases h0 : activeIdCount S b.q_on * activeSpkCount S b.q_on = 0
      · simp [h0, v, Comp.eval, Expr.eval, huv'', paMk, paramsToVal, activeParamsDh1, unifGdh_pure]
      · simp only [h0, ↓reduceIte, bindV, gPrim_eval, sIndex_eval, Comp.eval,
          embedPrim_embedUnif_eq_unifGdh, unifGdh_bind, unifGdh_pure]
        refine bind_congr fun pOrd => bind_congr fun spkOrd => ?_
        simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', Env.get_zero',
          huv'', paMk, paramsToVal, activeParamsDh1]
    · unfold samplePairProb
      by_cases h0 : activeSendCount S b.q_on * activeSpkCount S b.q_on = 0
      · simp [h0, v, Comp.eval, Expr.eval, huv'', paMk, paramsToVal, activeParamsDh3, unifGdh_pure]
      · simp only [h0, ↓reduceIte, bindV, gPrim_eval, sIndex_eval, Comp.eval,
          embedPrim_embedUnif_eq_unifGdh, unifGdh_bind, unifGdh_pure]
        refine bind_congr fun ephOrd => bind_congr fun spkOrd => ?_
        simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', Env.get_zero',
          huv'', paMk, paramsToVal, activeParamsDh3]
    · unfold samplePairProb
      by_cases h0 : activeSendCount S b.q_on * activeIdCount S b.q_on = 0
      · simp [h0, v, Comp.eval, Expr.eval, huv'', paMk, paramsToVal, activeParamsDh2, unifGdh_pure]
      · simp only [h0, ↓reduceIte, bindV, gPrim_eval, sIndex_eval, Comp.eval,
          embedPrim_embedUnif_eq_unifGdh, unifGdh_bind, unifGdh_pure]
        refine bind_congr fun ephOrd => bind_congr fun pOrd => ?_
        simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', Env.get_zero',
          huv'', paMk, paramsToVal, activeParamsDh2]
    · unfold samplePairProb
      by_cases h0 : activeSendOpkCount S b.q_on * activeOpkCount S b.q_on = 0
      · simp [h0, v, Comp.eval, Expr.eval, huv'', paMk, paramsToVal, activeParamsDh4, unifGdh_pure]
      · simp only [h0, ↓reduceIte, bindV, gPrim_eval, sIndex_eval, Comp.eval,
          embedPrim_embedUnif_eq_unifGdh, unifGdh_bind, unifGdh_pure]
        refine bind_congr fun ephOrd => bind_congr fun opkOrd => ?_
        simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', Env.get_zero',
          huv'', paMk, paramsToVal, activeParamsDh4]

/-! ## Distributional equivalence with flat-index decoding -/

section DistHelpers

private theorem simulateQ_unifGdhSign {α : Type}
    (primImpl0 : QueryImpl primSpec ProbComp)
    (chalImpl : QueryImpl sigAndDdhSpec ProbComp) (mx : ProbComp α) :
    simulateQ ((QueryImpl.ofLift unifSpec ProbComp + primImpl0) + chalImpl) (unifGdhSign mx) = mx := by
  unfold unifGdhSign unifGdh
  rw [FgGapDh_embedUnif_eq, FgGapDh_embedPrim_eq]
  unfold embedUnif
  induction mx using OracleComp.inductionOn with
  | pure a =>
    simp [embedPrim, liftGdhToSign_pure]
  | query_bind k cont ih =>
    rw [liftComp_bind, liftComp_query]
    change simulateQ ((QueryImpl.ofLift unifSpec ProbComp + primImpl0) + chalImpl)
        (liftGdhToSign (embedPrim
          ((id <$> liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl k))) >>=
            fun u => (cont u).liftComp PrimBaseSpec))) = _
    rw [id_map]
    simp only [embedPrim, OracleComp.construct_query_bind]
    change simulateQ ((QueryImpl.ofLift unifSpec ProbComp + primImpl0) + chalImpl)
        (liftGdhToSign
          (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inl k))) >>=
            fun u => embedPrim ((cont u).liftComp PrimBaseSpec))) = _
    rw [liftGdhToSign_bind, liftGdhToSign_query_inl, simulateQ_bind]
    simp
    exact bind_congr ih

private theorem evalDist_sampleIndexRange_bind {β : Type} [MeasurableSpace β]
    [DiscreteMeasurableSpace β] {N : ℕ} (hN : 0 < N)
    (g : ℕ → ProbComp β) (z : β) :
    𝒟[sampleIndexRange N >>= g] {z} =
      ∑ k ∈ Finset.range N, 𝒟[g k] {z} * (N : ℝ≥0∞)⁻¹ := by
  have _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  simp only [sampleIndexRange, hN, ↓reduceDIte, bind_assoc, pure_bind]
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton z)
      (Measurable.of_discrete).aemeasurable,
    MeasureTheory.lintegral_fintype]
  simp_rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun k => 𝒟[g k] {z} * (N : ℝ≥0∞)⁻¹) N

private theorem mul_evalDist_sampleIndexRange {β : Type} [MeasurableSpace β]
    [DiscreteMeasurableSpace β] {N : ℕ} (hN : 0 < N)
    (f : ℕ → ProbComp β) (z : β) :
    (N : ℝ≥0∞) * 𝒟[sampleIndexRange N >>= f] {z} =
      ∑ i ∈ Finset.range N, 𝒟[f i] {z} := by
  have hN0 : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hNtop : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  rw [evalDist_sampleIndexRange_bind hN, ← Finset.sum_mul,
    ← mul_assoc, mul_comm (N : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel hN0 hNtop, mul_one]

private theorem sum_range_mul_div_mod_ennreal' (M N : ℕ) (g : ℕ → ℕ → ℝ≥0∞) :
    ∑ k ∈ Finset.range (M * N), g (k / N) (k % N) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N, g i j := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_one_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hPos : 0 < N := by omega
    rw [Nat.add_comm (m * N) j, Nat.add_mul_div_right j m hPos, Nat.div_eq_of_lt hj,
      Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

private theorem sum_range_lt_split' (c K : ℕ) (hc : c ≤ K) (a b : ℝ≥0∞) :
    (∑ y ∈ Finset.range K, if y < c then a else b) =
      (c : ℝ≥0∞) * a + ((K - c : ℕ) : ℝ≥0∞) * b := by
  have hK : K = c + (K - c) := (Nat.add_sub_of_le hc).symm
  conv_lhs => rw [hK]
  rw [Finset.sum_range_add]
  congr 1
  · trans (∑ _y ∈ Finset.range c, a)
    · refine Finset.sum_congr rfl fun y hy => ?_
      simp [Finset.mem_range.mp hy]
    · simp
  · trans (∑ _y ∈ Finset.range (K - c), b)
    · refine Finset.sum_congr rfl fun y _ => ?_
      have hge : ¬ (c + y < c) := by omega
      simp [hge]
    · simp

private theorem sum_range_odd' (m : ℕ) :
    ∑ x ∈ Finset.range m, (2 * x + 1) = m * m := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

private theorem sum_range_sq_add_one (m : ℕ) :
    (∑ y1 ∈ Finset.range m, ∑ y2 ∈ Finset.range m, (y1 + y2 + 1)) = m * m * m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    simp_rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib, ih]
    have hCombine : (∑ x ∈ Finset.range k, (x + k + 1)) + ∑ x ∈ Finset.range k, (k + x + 1) =
        (∑ x ∈ Finset.range k, (2 * x + 1)) + ∑ _x ∈ Finset.range k, (2 * k + 1) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      omega
    have h1 := sum_range_odd' k
    have h2 : ∑ _x ∈ Finset.range k, (2 * k + 1) = k * (2 * k + 1) := by simp
    nlinarith

private theorem sum_range_sq_sub_add_one (m K : ℕ) (h : m + m ≤ K) :
    (∑ y1 ∈ Finset.range m, ∑ y2 ∈ Finset.range m, (K - (y1 + y2 + 1))) = m * m * (K - m) := by
  have hAdd : (∑ y1 ∈ Finset.range m, ∑ y2 ∈ Finset.range m, (K - (y1 + y2 + 1))) +
      (∑ y1 ∈ Finset.range m, ∑ y2 ∈ Finset.range m, (y1 + y2 + 1)) = m * m * K := by
    rw [← Finset.sum_add_distrib]
    trans (∑ _y1 ∈ Finset.range m, m * K)
    · refine Finset.sum_congr rfl fun y1 hy1 => ?_
      rw [← Finset.sum_add_distrib]
      have hy1' : y1 < m := Finset.mem_range.mp hy1
      trans (∑ _y2 ∈ Finset.range m, K)
      · refine Finset.sum_congr rfl fun y2 hy2 => ?_
        have hy2' : y2 < m := Finset.mem_range.mp hy2
        omega
      · simp
    · simp [Nat.mul_assoc]
  rw [sum_range_sq_add_one] at hAdd
  have hmK : m ≤ K := by omega
  zify [hmK] at hAdd ⊢
  nlinarith

private theorem evalDist_bernoulliCube_scaled {β : Type} [MeasurableSpace β]
    [DiscreteMeasurableSpace β] {M K : ℕ} (hM : 0 < M) (hMK : M + M ≤ K)
    (pT pF : ProbComp β) (z : β) :
    (K : ℝ≥0∞) * 𝒟[sampleIndexRange K >>= fun x =>
        sampleIndexRange M >>= fun y1 => sampleIndexRange M >>= fun y2 =>
          if decide (x < y1 + y2 + 1) = true then pT else pF] {z} =
      (M : ℝ≥0∞) * 𝒟[pT] {z} + ((K - M : ℕ) : ℝ≥0∞) * 𝒟[pF] {z} := by
  have hK : 0 < K := by omega
  have hM0 : (M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
  have hMtop : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top M
  rw [mul_evalDist_sampleIndexRange hK]
  have hInner : ∀ x ∈ Finset.range K,
      𝒟[sampleIndexRange M >>= fun y1 => sampleIndexRange M >>= fun y2 =>
          if decide (x < y1 + y2 + 1) = true then pT else pF] {z} =
        ∑ y1 ∈ Finset.range M,
          (∑ y2 ∈ Finset.range M,
            (if x < y1 + y2 + 1 then 𝒟[pT] {z} else 𝒟[pF] {z}) * (M : ℝ≥0∞)⁻¹) *
            (M : ℝ≥0∞)⁻¹ := by
    intro x _
    rw [evalDist_sampleIndexRange_bind hM]
    refine Finset.sum_congr rfl fun y1 _ => congrArg (· * (M : ℝ≥0∞)⁻¹) ?_
    rw [evalDist_sampleIndexRange_bind hM]
    refine Finset.sum_congr rfl fun y2 _ => ?_
    by_cases hlt : x < y1 + y2 + 1 <;> simp [hlt]
  rw [Finset.sum_congr rfl hInner, Finset.sum_comm]
  have hSwap2 : (∑ y1 ∈ Finset.range M, ∑ x ∈ Finset.range K,
      (∑ y2 ∈ Finset.range M,
        (if x < y1 + y2 + 1 then 𝒟[pT] {z} else 𝒟[pF] {z}) * (M : ℝ≥0∞)⁻¹) *
        (M : ℝ≥0∞)⁻¹) =
      ∑ y1 ∈ Finset.range M,
        (∑ y2 ∈ Finset.range M,
          (((y1 + y2 + 1 : ℕ) : ℝ≥0∞) * 𝒟[pT] {z} +
            ((K - (y1 + y2 + 1) : ℕ) : ℝ≥0∞) * 𝒟[pF] {z}) * (M : ℝ≥0∞)⁻¹) *
          (M : ℝ≥0∞)⁻¹ := by
    refine Finset.sum_congr rfl fun y1 hy1 => ?_
    have hy1' : y1 < M := Finset.mem_range.mp hy1
    simp_rw [← Finset.sum_mul]
    congr 1; congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y2 hy2 => ?_
    have hy2' : y2 < M := Finset.mem_range.mp hy2
    exact sum_range_lt_split' (y1 + y2 + 1) K (by omega) _ _
  rw [hSwap2]
  simp_rw [← Finset.sum_mul]
  have hSplit : (∑ y1 ∈ Finset.range M, ∑ y2 ∈ Finset.range M,
      (((y1 + y2 + 1 : ℕ) : ℝ≥0∞) * 𝒟[pT] {z} +
        ((K - (y1 + y2 + 1) : ℕ) : ℝ≥0∞) * 𝒟[pF] {z})) =
      ((M * M * M : ℕ) : ℝ≥0∞) * 𝒟[pT] {z} +
        ((M * M * (K - M) : ℕ) : ℝ≥0∞) * 𝒟[pF] {z} := by
    simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Nat.cast_sum]
    rw [sum_range_sq_add_one M, sum_range_sq_sub_add_one M K hMK]
  rw [hSplit]
  have hCancel : ∀ c : ℝ≥0∞,
      ((M : ℝ≥0∞) * (M : ℝ≥0∞) * c) * (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞)⁻¹ = c := by
    intro c
    rw [mul_comm ((M : ℝ≥0∞) * (M : ℝ≥0∞)) c, mul_assoc c,
      mul_assoc (M : ℝ≥0∞) (M : ℝ≥0∞) (M : ℝ≥0∞)⁻¹,
      ENNReal.mul_inv_cancel hM0 hMtop, mul_one, mul_assoc c,
      ENNReal.mul_inv_cancel hM0 hMtop, mul_one]
  simp only [Nat.cast_mul, add_mul]
  have hL : (M : ℝ≥0∞) * (M : ℝ≥0∞) * (M : ℝ≥0∞) * 𝒟[pT] {z} *
      (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞)⁻¹ = (M : ℝ≥0∞) * 𝒟[pT] {z} := by
    rw [mul_assoc ((M : ℝ≥0∞) * (M : ℝ≥0∞)) (M : ℝ≥0∞) (𝒟[pT] {z})]
    exact hCancel _
  have hR : (M : ℝ≥0∞) * (M : ℝ≥0∞) * ((K - M : ℕ) : ℝ≥0∞) * 𝒟[pF] {z} *
      (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞)⁻¹ = ((K - M : ℕ) : ℝ≥0∞) * 𝒟[pF] {z} := by
    rw [mul_assoc ((M : ℝ≥0∞) * (M : ℝ≥0∞)) (((K - M : ℕ) : ℝ≥0∞)) (𝒟[pF] {z})]
    exact hCancel _
  rw [hL, hR]

private theorem evalDist_bernoulliRatioProb_scaled {β : Type} [MeasurableSpace β]
    [DiscreteMeasurableSpace β] {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (pT pF : ProbComp β) (z : β) :
    ((A + B : ℕ) : ℝ≥0∞) * 𝒟[bernoulliRatioProb A B >>= fun u =>
        if u = true then pT else pF] {z} =
      (A : ℝ≥0∞) * 𝒟[pT] {z} + (B : ℝ≥0∞) * 𝒟[pF] {z} := by
  have hA0 : A ≠ 0 := Nat.ne_of_gt hA
  have hB0 : B ≠ 0 := Nat.ne_of_gt hB
  unfold bernoulliRatioProb
  simp only [hA0, hB0, ↓reduceIte]
  by_cases hAB : A ≤ B
  · simp only [hAB, ↓reduceIte, bind_assoc, pure_bind]
    rw [evalDist_bernoulliCube_scaled hA (by omega), Nat.add_sub_cancel_left]
  · simp only [hAB, ↓reduceIte, bind_assoc, pure_bind]
    have hRew : (sampleIndexRange (A + B) >>= fun x =>
        sampleIndexRange B >>= fun y1 => sampleIndexRange B >>= fun y2 =>
          if (!decide (x < y1 + y2 + 1)) = true then pT else pF) =
        (sampleIndexRange (A + B) >>= fun x =>
          sampleIndexRange B >>= fun y1 => sampleIndexRange B >>= fun y2 =>
            if decide (x < y1 + y2 + 1) = true then pF else pT) := by
      refine bind_congr fun x => bind_congr fun y1 => bind_congr fun y2 => ?_
      cases decide (x < y1 + y2 + 1) <;> rfl
    rw [hRew, evalDist_bernoulliCube_scaled hB (by omega), Nat.add_sub_cancel_right, add_comm]

private theorem evalDist_chooseArm2Prob_scaled {α β : Type} [MeasurableSpace β]
    [DiscreteMeasurableSpace β] (w1 w2 : ℕ)
    (p1 p2 : ProbComp α) (g : α → ProbComp β) (z : β) :
    ((w1 + w2 : ℕ) : ℝ≥0∞) * 𝒟[chooseArm2Prob w1 w2 p1 p2 >>= g] {z} =
      (w1 : ℝ≥0∞) * 𝒟[p1 >>= g] {z} + (w2 : ℝ≥0∞) * 𝒟[p2 >>= g] {z} := by
  unfold chooseArm2Prob
  by_cases hw1 : w1 = 0
  · simp [hw1]
  · by_cases hw2 : w2 = 0
    · simp [hw1, hw2]
    · simp only [hw1, hw2, ↓reduceIte, bind_assoc]
      have hBind : (bernoulliRatioProb w1 w2 >>= fun sel =>
          (if sel = true then p1 else p2) >>= g) =
          (bernoulliRatioProb w1 w2 >>= fun sel =>
            if sel = true then (p1 >>= g) else (p2 >>= g)) := by
        refine bind_congr fun sel => ?_
        cases sel <;> rfl
      rw [hBind]
      exact evalDist_bernoulliRatioProb_scaled (Nat.pos_of_ne_zero hw1) (Nat.pos_of_ne_zero hw2)
        (p1 >>= g) (p2 >>= g) z

private theorem evalDist_samplePairProb_scaled {α β : Type} [MeasurableSpace β]
    [DiscreteMeasurableSpace β] (M N : ℕ) (dflt : α)
    (mk : ℕ → ℕ → α) (g : α → ProbComp β) (z : β) :
    ((M * N : ℕ) : ℝ≥0∞) * 𝒟[samplePairProb M N dflt mk >>= g] {z} =
      ∑ k ∈ Finset.range (M * N), 𝒟[g (mk (k / N) (k % N))] {z} := by
  unfold samplePairProb
  by_cases h0 : M * N = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte, bind_assoc, pure_bind]
    have hPos : 0 < M * N := Nat.pos_of_ne_zero h0
    have hM : 0 < M := Nat.pos_of_mul_pos_right hPos
    have hN : 0 < N := Nat.pos_of_mul_pos_left hPos
    rw [Nat.cast_mul, mul_comm (M : ℝ≥0∞) (N : ℝ≥0∞), mul_assoc,
      mul_evalDist_sampleIndexRange hM, Finset.mul_sum]
    simp_rw [mul_evalDist_sampleIndexRange hN]
    exact (sum_range_mul_div_mod_ennreal' M N (fun i j => 𝒟[g (mk i j)] {z})).symm

private theorem evalDist_initParams1KeyActiveProb_bind {β : Type} [MeasurableSpace β]
    [DiscreteMeasurableSpace β] (S : Setup) (b : QueryBudget)
    (U V : Bytes) (g : FgActiveParams → ProbComp β) (z : β) :
    𝒟[initParams1KeyActiveProb S b U V >>= g] {z} =
      𝒟[sampleIndexRange (fgActiveTotalIndexCount S b.q_on) >>= fun idx =>
          g (activeParamsFlat S b U V idx)] {z} := by
  by_cases htot : fgActiveTotalIndexCount S b.q_on = 0
  · simp [initParams1KeyActiveProb, htot, sampleIndexRange, activeParamsFlat_eq_zero S b U V 0 htot]
  · have hPos : 0 < fgActiveTotalIndexCount S b.q_on := Nat.pos_of_ne_zero htot
    have hTot0 : (fgActiveTotalIndexCount S b.q_on : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr htot
    have hTotTop : (fgActiveTotalIndexCount S b.q_on : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [← ENNReal.mul_right_inj hTot0 hTotTop]
    rw [mul_evalDist_sampleIndexRange hPos]
    unfold initParams1KeyActiveProb
    simp only [htot, ↓reduceIte]
    let n_id := activeIdCount S b.q_on
    let n_spk := activeSpkCount S b.q_on
    let n_opk := activeOpkCount S b.q_on
    let n_send := activeSendCount S b.q_on
    let n_send_opk := activeSendOpkCount S b.q_on
    let nA := n_id * n_spk
    let nC := n_send * n_spk
    let nB := n_send * n_id
    let nD := n_send_opk * n_opk
    have hTotEq : fgActiveTotalIndexCount S b.q_on = (nA + nC) + (nB + nD) := by
      dsimp only [fgActiveTotalIndexCount, nA, nC, nB, nD, n_id, n_spk, n_opk, n_send, n_send_opk]
      omega
    conv_lhs => rw [hTotEq]
    rw [evalDist_chooseArm2Prob_scaled (nA + nC) (nB + nD),
      evalDist_chooseArm2Prob_scaled nA nC,
      evalDist_chooseArm2Prob_scaled nB nD,
      evalDist_samplePairProb_scaled n_id n_spk,
      evalDist_samplePairProb_scaled n_send n_spk,
      evalDist_samplePairProb_scaled n_send n_id,
      evalDist_samplePairProb_scaled n_send_opk n_opk]
    have hTotEq4 : fgActiveTotalIndexCount S b.q_on = nA + nC + nB + nD := by
      dsimp only [fgActiveTotalIndexCount, nA, nC, nB, nD, n_id, n_spk, n_opk, n_send, n_send_opk]
    rw [hTotEq4, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
    have hSumA : (∑ k ∈ Finset.range nA, 𝒟[g (activeParamsDh1 b U V (k / n_spk) (k % n_spk))] {z}) =
        ∑ idx ∈ Finset.range nA, 𝒟[g (activeParamsFlat S b U V idx)] {z} := by
      refine Finset.sum_congr rfl fun idx hidx => ?_
      rw [activeParamsFlat_dh1 S b U V idx (Finset.mem_range.mp hidx)]
    have hSumC : (∑ k ∈ Finset.range nC, 𝒟[g (activeParamsDh3 b U V (k / n_spk) (k % n_spk))] {z}) =
        ∑ k ∈ Finset.range nC, 𝒟[g (activeParamsFlat S b U V (nA + k))] {z} := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < nC := Finset.mem_range.mp hk
      have h1 : ¬ (nA + k < nA) := by omega
      have h2 : nA + k < nA + nC := by omega
      have hd := activeParamsFlat_dh3 S b U V (nA + k) h1 h2
      dsimp only at hd
      rw [Nat.add_sub_cancel_left] at hd
      rw [hd]
    have hSumB : (∑ k ∈ Finset.range nB, 𝒟[g (activeParamsDh2 b U V (k / n_id) (k % n_id))] {z}) =
        ∑ k ∈ Finset.range nB, 𝒟[g (activeParamsFlat S b U V (nA + nC + k))] {z} := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < nB := Finset.mem_range.mp hk
      have h2 : ¬ (nA + nC + k < nA + nC) := by omega
      have h3 : nA + nC + k < nA + nC + nB := by omega
      have hd := activeParamsFlat_dh2 S b U V (nA + nC + k) h2 h3
      dsimp only at hd
      rw [Nat.add_sub_cancel_left] at hd
      rw [hd]
    have hSumD : (∑ k ∈ Finset.range nD, 𝒟[g (activeParamsDh4 b U V (k / n_opk) (k % n_opk))] {z}) =
        ∑ k ∈ Finset.range nD, 𝒟[g (activeParamsFlat S b U V (nA + nC + nB + k))] {z} := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < nD := Finset.mem_range.mp hk
      have h3 : ¬ (nA + nC + nB + k < nA + nC + nB) := by omega
      have h4 : nA + nC + nB + k < fgActiveTotalIndexCount S b.q_on := by omega
      have hd := activeParamsFlat_dh4 S b U V (nA + nC + nB + k) h3 h4
      dsimp only at hd
      rw [Nat.add_sub_cancel_left] at hd
      rw [hd]
    rw [hSumA, hSumC, hSumB, hSumD]
    ac_rfl

end DistHelpers

/-! ## End-to-end `GapDhWithSign` advantage equality -/

@[expose] def runFrom1KeyActive (S : Setup) (K : Nat)
    (A : OracleComp (unifSpec + keyIndSpec S) Bool)
    (x0 : gdh1KeyActiveStateTy.denote) : OracleComp GdhSignSimSpec Bytes := do
  let (out, s') ← (simulateQ (handlerImpl (C := keyIndCodec S) (gdh1KeyActiveHandle S K)) A).run x0
  (gdh1KeyActiveFinish S K).eval (.cons s' (.cons out .nil))

private theorem fgKeyInd1KeyGapDhActiveDslProg_1278_eval_runFrom (S : Setup) (b : QueryBudget)
    (A : OracleComp (unifSpec + keyIndSpec S) Bool) (U V : Bytes) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).eval (fun _ => A) (U, V) =
      (do
        let pa ← unifGdhSign (initParams1KeyActiveProb S b U V)
        let secb ← unifGdhSign ($ᵗ Bool)
        runFrom1KeyActive S b.q_total A
          (sim1KeyActiveStateToVal pa (FgKeyInd1KeyActiveSimState.empty S b secb))) := by
  simp only [CostedReduction.eval, fgKeyInd1KeyGapDhActiveDslProg,
    letV_eval, bindV, Comp.eval, liftGdhComp_eval, gPrim_eval, sBool_eval,
    emptySimE_eval (S := S), v, Expr.eval, Env.get_zero', Env.get_succ',
    Ext.step_wk', Ext.refl_wk', bind_assoc, pure_bind]
  rw [initParams1KeyActiveC_eval S b .zero _ U V rfl]
  simp only [CostedReduction.impl, runFrom1KeyActive, map_eq_bind_pure_comp, Function.comp_def,
    unifGdh_bind, unifGdh_pure, liftGdhToSign_bind, liftGdhToSign_pure,
    sim1KeyActiveStateToVal, sim1KeyStateToVal,
    FgKeyInd1KeyActiveSimState.empty, FgKeyInd1KeySimState.empty,
    bind_assoc, pure_bind]
  simp only [unifGdhSign, unifGdh, FgGapDh_embedPrim_eq, FgGapDh_embedUnif_eq]
  rfl

private theorem fgKeyInd1KeyGapDhActiveDslProg_1278_simulateQ_bind_evalDist_eq
    {β : Type} [MeasurableSpace β] [DiscreteMeasurableSpace β] [Countable β]
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes)
    (primImpl0 : QueryImpl primSpec ProbComp) (chalImpl : QueryImpl sigAndDdhSpec ProbComp)
    (k : Bytes → ProbComp β)
    (hRunFrom : ∀ (pa : FgActiveParams),
      (pa.mode = 0 ∨ pa.mode = 1 ∨ pa.mode = 2 ∨ pa.mode = 3) →
      ∀ (secb : Bool),
        runFrom1KeyActive S b.q_total A.1.run
          (sim1KeyActiveStateToVal pa (FgKeyInd1KeyActiveSimState.empty S b secb)) =
        (do
          let (_, finalSt) ← runWithGdhSignStep (fgKeyInd1KeyActiveStep pa S b.q_total) A.1.run
            (FgKeyInd1KeyActiveSimState.empty S b secb)
          fgKeyInd1KeyActiveFinish pa S b.q_total finalSt)) :
    𝒟[simulateQ ((QueryImpl.ofLift unifSpec ProbComp + primImpl0) + chalImpl)
        ((fgKeyInd1KeyGapDhActiveDslProg S b).eval (fun _ => A.1.run) (U, V)) >>= k] =
      𝒟[simulateQ ((QueryImpl.ofLift unifSpec ProbComp + primImpl0) + chalImpl)
        ((fgKeyInd1KeyGapDhActiveAdv4 S b A).run U V) >>= k] := by
  let impl := (QueryImpl.ofLift unifSpec ProbComp + primImpl0) + chalImpl
  let g (pa : FgActiveParams) : ProbComp β :=
    ($ᵗ Bool) >>= fun secb =>
      simulateQ impl
        (runFrom1KeyActive S b.q_total A.1.run
          (sim1KeyActiveStateToVal pa (FgKeyInd1KeyActiveSimState.empty S b secb))) >>= k
  have hDsl : (simulateQ impl
        ((fgKeyInd1KeyGapDhActiveDslProg S b).eval (fun _ => A.1.run) (U, V)) >>= k) =
      (initParams1KeyActiveProb S b U V >>= g) := by
    rw [fgKeyInd1KeyGapDhActiveDslProg_1278_eval_runFrom S b A.1.run U V]
    rw [simulateQ_bind, simulateQ_unifGdhSign, bind_assoc]
    refine bind_congr fun pa => ?_
    rw [simulateQ_bind, simulateQ_unifGdhSign, bind_assoc]
  have hSh : (simulateQ impl ((fgKeyInd1KeyGapDhActiveAdv4 S b A).run U V) >>= k) =
      (sampleIndexRange (fgActiveTotalIndexCount S b.q_on) >>= fun idx =>
        g (activeParamsFlat S b U V idx)) := by
    unfold fgKeyInd1KeyGapDhActiveAdv4 fgKeyInd1KeyGapDhActiveRunAtFlat
      fgKeyInd1KeyActiveRunWithParams
    dsimp only
    rw [simulateQ_bind, simulateQ_unifGdhSign, bind_assoc]
    refine bind_congr fun idx => ?_
    rw [simulateQ_bind, simulateQ_unifGdhSign, bind_assoc]
    refine bind_congr fun secb => congrArg (· >>= k) (congrArg (simulateQ impl) ?_)
    exact (hRunFrom (activeParamsFlat S b U V idx)
      (activeParamsFlat_mode_lt4 S b U V idx) secb).symm
  rw [hDsl, hSh]
  exact MeasureTheory.Measure.ext_of_singleton
    (evalDist_initParams1KeyActiveProb_bind S b U V g)

private theorem gapDhWithSign_of_simulateQ_bind_evalDist_eq
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (adv1 adv2 : GapDhWithSignAdv)
    (hRun : ∀ (U V : Bytes) (primImpl0 : QueryImpl primSpec ProbComp)
        (chalImpl : QueryImpl sigAndDdhSpec ProbComp) (k : Bytes → ProbComp Bool),
      𝒟[simulateQ ((QueryImpl.ofLift unifSpec ProbComp + primImpl0) + chalImpl) (adv1.run U V) >>= k] =
        𝒟[simulateQ ((QueryImpl.ofLift unifSpec ProbComp + primImpl0) + chalImpl) (adv2.run U V) >>= k]) :
    GapDhWithSign P isValidDhTriple pow8 adv1 = GapDhWithSign P isValidDhTriple pow8 adv2 := by
  have hExp : 𝒟[gapDhWithSignExp P isValidDhTriple pow8 adv1] =
      𝒟[gapDhWithSignExp P isValidDhTriple pow8 adv2] := by
    unfold gapDhWithSignExp primBaseImpl
    refine OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ fun u _ => ?_
    refine OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ fun v _ => ?_
    exact hRun _ _ _ _ _
  simp only [GapDhWithSign, hExp]

private theorem gapDhWithSignReal_of_gapDhWithSign_eq
    (P : Primitives) (adv1 adv2 : GapDhWithSignAdv)
    (hEq : GapDhWithSign P P.isValidDhTriple P.pow8 adv1 =
      GapDhWithSign P P.isValidDhTriple P.pow8 adv2) :
    GapDhWithSignReal P P.isValidDhTriple P.pow8 adv1 =
      GapDhWithSignReal P P.isValidDhTriple P.pow8 adv2 := by
  simp only [GapDhWithSignReal, hEq]

theorem fgKeyInd1KeyGapDhActiveAtomicProg_1278_eval_eq (S : Setup) (b : QueryBudget)
    (hHandle : (fgKeyInd1KeyGapDhActiveDslProg S b).handle.queries
      tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0)
    (hFinish : (fgKeyInd1KeyGapDhActiveDslProg S b).finish.queries
      tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0)
    (adv : Unit → OracleComp (unifSpec + keyIndSpec S) Bool) (U V : Bytes) :
    (fgKeyInd1KeyGapDhActiveAtomicProg S b).eval adv (U, V) =
      (fgKeyInd1KeyGapDhActiveDslProg S b).eval adv (U, V) := by
  have h := liftKeyInd1Stage_eval tlSigDdhKeyInd S (fgKeyInd1KeyGapDhActiveDslProg S b)
    (gdhActive_init_unsupported_1278 S b) hHandle hFinish adv (U, V)
  have hId : embedVal (B 32) = id := rfl
  rw [hId, id_map] at h
  exact h

theorem gapDhWithSign_fgKeyInd1KeyGapDhActiveAtomicProg_1278_eq
    (S : Setup) (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (hHandle : (fgKeyInd1KeyGapDhActiveDslProg S b).handle.queries
      tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0)
    (hFinish : (fgKeyInd1KeyGapDhActiveDslProg S b).finish.queries
      tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0)
    (hRunFrom : ∀ (pa : FgActiveParams),
      (pa.mode = 0 ∨ pa.mode = 1 ∨ pa.mode = 2 ∨ pa.mode = 3) →
      ∀ (secb : Bool),
        runFrom1KeyActive S b.q_total A.1.run
          (sim1KeyActiveStateToVal pa (FgKeyInd1KeyActiveSimState.empty S b secb)) =
        (do
          let (_, finalSt) ← runWithGdhSignStep (fgKeyInd1KeyActiveStep pa S b.q_total) A.1.run
            (FgKeyInd1KeyActiveSimState.empty S b secb)
          fgKeyInd1KeyActiveFinish pa S b.q_total finalSt)) :
    GapDhWithSign P isValidDhTriple pow8
      { run := fun U V => (fgKeyInd1KeyGapDhActiveAtomicProg S b).eval (fun _ => A.1.run) (U, V)
        q_ddh := gdhQueryBudget S b
        q_sig := 2 * min S.N_spk_tot S.N_recv
        q_prim := gdhPrimQueryBudget S b } =
    GapDhWithSign P isValidDhTriple pow8
      (fgKeyInd1KeyGapDhActiveAdv4 S b A) := by
  refine gapDhWithSign_of_simulateQ_bind_evalDist_eq P isValidDhTriple pow8 _ _ ?_
  intro U V primImpl0 chalImpl k
  dsimp only
  rw [fgKeyInd1KeyGapDhActiveAtomicProg_1278_eval_eq S b hHandle hFinish (fun _ => A.1.run) U V]
  exact fgKeyInd1KeyGapDhActiveDslProg_1278_simulateQ_bind_evalDist_eq
    S b A U V primImpl0 chalImpl k hRunFrom

/-- Real-valued `GapDhWithSignReal` advantage equality between
    `fgKeyInd1KeyGapDhActiveAtomicProg` and `fgKeyInd1KeyGapDhActiveAdv4`. -/
theorem gapDhWithSignReal_fgKeyInd1KeyGapDhActiveAtomicProg_1278_eq
    (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (hHandle : (fgKeyInd1KeyGapDhActiveDslProg S b).handle.queries
      tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0)
    (hFinish : (fgKeyInd1KeyGapDhActiveDslProg S b).finish.queries
      tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0)
    (hRunFrom : ∀ (pa : FgActiveParams),
      (pa.mode = 0 ∨ pa.mode = 1 ∨ pa.mode = 2 ∨ pa.mode = 3) →
      ∀ (secb : Bool),
        runFrom1KeyActive S b.q_total A.1.run
          (sim1KeyActiveStateToVal pa (FgKeyInd1KeyActiveSimState.empty S b secb)) =
        (do
          let (_, finalSt) ← runWithGdhSignStep (fgKeyInd1KeyActiveStep pa S b.q_total) A.1.run
            (FgKeyInd1KeyActiveSimState.empty S b secb)
          fgKeyInd1KeyActiveFinish pa S b.q_total finalSt)) :
    GapDhWithSignReal P P.isValidDhTriple P.pow8
      { run := fun U V => (fgKeyInd1KeyGapDhActiveAtomicProg S b).eval (fun _ => A.1.run) (U, V)
        q_ddh := gdhQueryBudget S b
        q_sig := 2 * min S.N_spk_tot S.N_recv
        q_prim := gdhPrimQueryBudget S b } =
    GapDhWithSignReal P P.isValidDhTriple P.pow8
      (fgKeyInd1KeyGapDhActiveAdv4 S b A) :=
  gapDhWithSignReal_of_gapDhWithSign_eq P _ _
    (gapDhWithSign_fgKeyInd1KeyGapDhActiveAtomicProg_1278_eq S P P.isValidDhTriple P.pow8
      b A hHandle hFinish hRunFrom)

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveInitEval
