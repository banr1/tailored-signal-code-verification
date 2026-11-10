/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhEval
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Query Transfer and Distributional Equivalence for `fgKeyInd1KeyGapDh2Prog`

Transfers `ddh`, `prim`, and `sig` query bounds from `fgKeyInd1KeyGapDhProg` to
`fgKeyInd1KeyGapDh2Prog` and proves that `fgKeyInd1KeyGapDh2Prog` and `fgKeyInd1KeyGapDhAdv4`
induce the same output distribution in `gapDhWithSignExp`.
-/

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh2Eval

public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open OracleSpec OracleComp
open _root_.ReductionDsl (Var Env Expr Comp Ty CostedReduction handlerImpl)
open _root_.SignalPqxdh (Setup Bytes Primitives QueryBudget BoundedAdv KeyIndAdversary KeyIndQuery
  KeyIndResponse keyIndSpec GapDhWithSignAdv gapDhWithSignExp gdhQueryBudget gdhPrimQueryBudget
  primBaseImpl sigAndDdhSpec PrimQuery SigQuery DdhQuery)
open _root_.SignalPqxdh.LegacyCosted (B keyIndCodec keyIndQenc pqxdhOps pqGapDhIface
  pqSigAndDdhIface sigAndDdhOracle gapDhDdhOracle)
open _root_.SignalPqxdh.Security (fgTotalIndexCount embedPrim)
open _root_.SignalPqxdh.Security.FgGapDh (GdhSimSpec sampleIndexRange unifGdh embedUnif)
open _root_.SignalPqxdh.Security.FgGapDh1Key (GdhSignSimSpec liftGdhToSign unifGdhSign
  FgKeyInd1KeySimState fgKeyInd1KeyGapDhAdv4)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (PT Ext v bindV letV letV_eval caseOptV
  caseSumV gPrim sIndex sIndex_eval sBool sBool_eval emptySimE keyIndQueryTy keyIndRespTy
  keyIndStateTy simTy simStateToVal paramsTy params2Ty ephTargetTy spkTargetTy opkTargetTy
  pa2Mk paUp paV paPrinFlag paPrinIdx paSpkIdx spkFlatIdxE mulRight pa2V pa2Up pa2PrinTarget
  pa2SpkTarget params2ToFlat bernoulliRatioGdhC chooseArm2C samplePrin2C sampleSpkPair2C
  sampleOpkTriple2C sampleSendOpkTarget2C sampleSendNoOpkTarget2C sampleSendTarget2C
  natEq natEq_eval nat2Eq eAny eFind eCaseOpt stPrin stSpks smBase
  litB consB peMk peIkAPk sbMk buMk u32OfNat encEC encKEM rNone rInitPrin rBundle
  stUpd stMk stSecb stOpks stResps stUsedO stUsedN stSess stAdv stRo stKyb
  smUpd smMk smFgL smRaw smLog smPows
  fgKeyInd1KeyGapDhProg fgKeyInd1KeyGapDh2Prog)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (paramsDhVal paramsOpkVal gPrim_eval
  emptySimE_eval FgGapDh_embedPrim_eq FgGapDh_embedUnif_eq InBoundsParams2 gdhHandle2_eval_map_eq
  gdhFinish2_eval_eq)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (gdh1KeyStateTy gdh1KeyState2Ty
  sim1KeyStateToVal callGdhHandle callGdhHandle2 initPrin1KeyB initPrin1Key2B genSpk1KeyB
  genSpk1Key2B gdh1KeyHandle gdh1KeyHandle2 gdh1KeyFinish gdh1KeyFinish2 initParams1Key2C
  initAdv4_1Key2Base initAdv4_1Key2 liftGdhComp renameComp twoVarRen sigChalQ_dsl_eval
  liftGdhComp_eval renameComp_eval pullEnv_twoVarRen liftGdhToSign_bind liftGdhToSign_pure
  liftGdhToSign_map liftGdhToSign_query_inl mem_support_liftGdhToSign runFrom1Key
  params1KeyIkVal params1KeyFlatVal fgKeyInd1KeyGapDhRunAtFlatComp
  fgKeyInd1KeyGapDhProg_eval_runFrom1Key fgKeyInd1KeyGapDhProg_eval_eq_of_queryBound
  fgKeyInd1KeyGapDhProg_eval_eq)

set_option allowUnsafeReducibility true
attribute [local implicit_reducible] sigAndDdhOracle gapDhDdhOracle Env.get Ext.wk

/-! ## Support-Wise Query Bounds and Uniform Helpers -/

private theorem isQueryBoundP_of_bind_mem_support {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {α β : Type} {m : OracleComp spec α} {f : α → OracleComp spec β}
    {p : ι → Prop} [DecidablePred p] {B : Nat} (h : IsQueryBoundP (m >>= f) p B) :
    ∀ x ∈ support m, IsQueryBoundP (f x) p B := by
  induction m using OracleComp.inductionOn generalizing B with
  | pure a =>
    intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
    simpa only [pure_bind] using h
  | query_bind q k ih =>
    intro x hx; rw [bind_assoc, isQueryBoundP_query_bind_iff] at h; rw [mem_support_bind_iff] at hx
    rcases hx with ⟨u, _, hxu⟩; by_cases hp : p q
    · simp only [hp, ↓reduceIte] at h; exact (ih u (h.2 u) x hxu).mono (Nat.sub_le B 1)
    · simp only [hp, ↓reduceIte] at h; exact ih u (h.2 u) x hxu

private theorem isQueryBoundP_bind_of_zero_mem_support {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {α β : Type} {m : OracleComp spec α} {f : α → OracleComp spec β}
    {p : ι → Prop} [DecidablePred p] {B : Nat}
    (hm : IsQueryBoundP m p 0) (hf : ∀ x ∈ support m, IsQueryBoundP (f x) p B) :
    IsQueryBoundP (m >>= f) p B := by
  induction m using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using hf a (by simp)
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hm; rcases hm with ⟨hFirst, hCont⟩
    have hnp : ¬ p q := hFirst.elim id fun hlt => by omega
    simp only [hnp, ↓reduceIte] at hCont; rw [bind_assoc, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl hnp, fun u => ?_⟩; simp only [hnp, ↓reduceIte]
    exact ih u (hCont u) fun x hx => hf x (by rw [mem_support_bind_iff]; exact ⟨u, mem_support_query q u, hx⟩)

private theorem unifGdh_pure {α : Type} (a : α) : unifGdh (pure a : ProbComp α) = pure a := rfl

private theorem unifGdh_bind {α β : Type} (m : ProbComp α) (k : α → ProbComp β) :
    unifGdh (m >>= k) = (unifGdh m >>= fun x => unifGdh (k x)) := by
  induction m using OracleComp.inductionOn with
  | pure _ => rfl
  | query_bind q r ih =>
    change (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inl q))) >>= fun u => unifGdh (r u >>= k)) =
      (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inl q))) >>= fun u => unifGdh (r u)) >>=
        fun x => unifGdh (k x)
    rw [bind_assoc]; congr 1; funext u; exact ih u

private theorem unifGdh_map {α β : Type} (f : α → β) (m : ProbComp α) : unifGdh (f <$> m) = f <$> unifGdh m := by
  simp only [map_eq_bind_pure_comp, unifGdh_bind, Function.comp_def, unifGdh_pure]

private theorem liftGdhToSign_unifGdh {α : Type} (m : ProbComp α) :
    liftGdhToSign (unifGdh m) = unifGdhSign m := rfl

private theorem unifGdhSign_query_bind_eq {α : Type} (n : ℕ) (k : Fin (n + 1) → ProbComp α) :
    unifGdhSign (liftM (OracleSpec.query (spec := unifSpec) n) >>= k) =
      (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl (Sum.inl n))) >>= fun u => unifGdhSign (k u)) := by
  change liftGdhToSign (unifGdh (liftM (OracleSpec.query (spec := unifSpec) n) >>= k)) = _; rw [unifGdh_bind]
  have hq : unifGdh (liftM (OracleSpec.query (spec := unifSpec) n)) =
      liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inl n))) := by
    unfold unifGdh embedUnif _root_.SignalPqxdh.Security.FgGapDh.embedPrim; rw [liftComp_query]
    exact bind_pure (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inl n))))
  rw [hq, liftGdhToSign_bind, liftGdhToSign_query_inl]; rfl

private theorem mem_support_unifGdhSign_iff {α : Type} {mx : ProbComp α} {x : α} :
    x ∈ support (unifGdhSign mx) ↔ x ∈ support mx := by
  induction mx using OracleComp.inductionOn with
  | pure _ => rfl
  | query_bind n k ih =>
    rw [unifGdhSign_query_bind_eq, mem_support_bind_iff, mem_support_bind_iff]
    exact ⟨fun ⟨u, _, hu⟩ => ⟨u, mem_support_query n u, (ih u).mp hu⟩,
      fun ⟨u, _, hu⟩ => ⟨u, mem_support_query _ u, (ih u).mpr hu⟩⟩

private theorem unifGdhSign_isQueryBoundP_zero {α : Type} (mx : ProbComp α)
    (p : ((ℕ ⊕ PrimQuery) ⊕ (SigQuery ⊕ DdhQuery)) → Prop) [DecidablePred p]
    (hpUnif : ∀ n : ℕ, ¬ p (Sum.inl (Sum.inl n))) : IsQueryBoundP (unifGdhSign mx) p 0 := by
  induction mx using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure p a 0
  | query_bind n k ih =>
    rw [unifGdhSign_query_bind_eq, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (hpUnif n), fun u => ?_⟩; simp only [hpUnif n, ↓reduceIte]; exact ih u

/-! ## Parameter Tree Distributional Equivalence -/

private def bernoulliRatioGdhProb (A B : Nat) : ProbComp Bool :=
  if A = 0 then pure false else if B = 0 then pure true
  else if A ≤ B then do
    let x ← sampleIndexRange (A + B); let y1 ← sampleIndexRange A; let y2 ← sampleIndexRange A
    return decide (x < y1 + y2 + 1)
  else do
    let x ← sampleIndexRange (A + B); let y1 ← sampleIndexRange B; let y2 ← sampleIndexRange B
    return !decide (x < y1 + y2 + 1)

private def chooseArm2Prob {α : Type} (w1 w2 : Nat) (c1 c2 : ProbComp α) : ProbComp α :=
  if w1 = 0 then c2 else if w2 = 0 then c1 else do let b ← bernoulliRatioGdhProb w1 w2; if b then c1 else c2

private def samplePrin2Prob (S : Setup) : ProbComp (Option Nat) :=
  if S.N_id = 0 then pure none else do let u ← sampleIndexRange S.N_id; return some u

private def sampleSpkPair2Prob (S : Setup) : ProbComp (Option (Nat × Nat)) :=
  if S.N_spk_tot = 0 then pure none
  else do let u ← sampleIndexRange S.N_id; let j ← sampleIndexRange S.N_recv; return some (u, j)

private def sampleOpkTriple2Prob (S : Setup) : ProbComp (Option (Nat × (Nat × Nat))) :=
  if S.N_opk_tot = 0 then pure none else do
    let u ← sampleIndexRange S.N_id; let j ← sampleIndexRange S.N_recv; let o ← sampleIndexRange S.N_opk
    return some (u, (j, o))

private def sampleSendOpkTarget2Prob (S : Setup) : ProbComp (Option (Bool × (Nat × Nat))) :=
  if S.N_send_opk_tot = 0 then pure none
  else do let u ← sampleIndexRange S.N_id; let i ← sampleIndexRange S.N_send_opk; return some (true, (u, i))

private def sampleSendNoOpkTarget2Prob (S : Setup) : ProbComp (Option (Bool × (Nat × Nat))) :=
  if S.N_send_no_opk_tot = 0 then pure none
  else do let u ← sampleIndexRange S.N_id; let i ← sampleIndexRange S.N_send_no_opk; return some (false, (u, i))

private def sampleSendTarget2Prob (S : Setup) : ProbComp (Option (Bool × (Nat × Nat))) :=
  if S.N_send_tot = 0 then pure none
  else chooseArm2Prob S.N_send_opk_tot S.N_send_no_opk_tot (sampleSendOpkTarget2Prob S) (sampleSendNoOpkTarget2Prob S)

private def initParams1Key2Prob (S : Setup) (U V : Bytes) : ProbComp params2Ty.denote :=
  if fgTotalIndexCount S = 0 then
    pure (U, (V, (U, (none, (false, (some (true, (0, 0)), (none, (true, (some (0, (0, 0)), 3)))))))))
  else
    let nA := S.N_id * S.N_spk_tot
    let nC := S.N_send_tot * S.N_spk_tot
    let nB := S.N_send_tot * S.N_id
    let nD := S.N_send_opk_tot * S.N_opk_tot
    chooseArm2Prob (nA + nC) (nB + nD)
      (chooseArm2Prob nA nC
        (do let pt ← samplePrin2Prob S; let st ← sampleSpkPair2Prob S
            return (U, (V, (U, (pt, (true, (none, (st, (false, (none, 0))))))))))
        (do let et ← sampleSendTarget2Prob S; let st ← sampleSpkPair2Prob S
            return (U, (V, (U, (none, (false, (et, (st, (false, (none, 1)))))))))))
      (chooseArm2Prob nB nD
        (do let et ← sampleSendTarget2Prob S; let pt ← samplePrin2Prob S
            return (V, (U, (U, (pt, (false, (et, (none, (false, (none, 2))))))))))
        (do let et ← sampleSendOpkTarget2Prob S; let ot ← sampleOpkTriple2Prob S
            return (U, (V, (U, (none, (false, (et, (none, (true, (ot, 3)))))))))))

private theorem gPrim_sIndex_eval_unifGdh {Γ : List PT} (N : Nat) (env : Env Γ) :
    (gPrim (Γ := Γ) (sIndex N)).eval env = unifGdh (sampleIndexRange N) := by
  simp [gPrim, sIndex_eval, unifGdh, FgGapDh_embedPrim_eq, FgGapDh_embedUnif_eq]

private theorem bernoulliRatioGdhC_eval {Δ : List PT} (A B : Nat) (env : Env Δ) :
    (bernoulliRatioGdhC (Δ := Δ) A B).eval env = unifGdh (bernoulliRatioGdhProb A B) := by
  unfold bernoulliRatioGdhC bernoulliRatioGdhProb; split_ifs
  · simp only [Comp.eval, Expr.eval, unifGdh_pure]
  · simp only [Comp.eval, Expr.eval, unifGdh_pure]
  · simp only [bindV, Comp.eval, gPrim_sIndex_eval_unifGdh, v, Expr.eval, Env.get, Ext.wk,
      unifGdh_bind, unifGdh_pure]
  · simp only [bindV, Comp.eval, gPrim_sIndex_eval_unifGdh, v, Expr.eval, Env.get, Ext.wk,
      unifGdh_bind, unifGdh_pure]

private theorem chooseArm2C_eval {Γ₁ Δ : List PT} {α : PT} [Ext Γ₁ Δ] (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' α)
    (p1 p2 : ProbComp α.denote) (env : Env Δ) (h1 : c1.eval env = unifGdh p1)
    (h1b : ∀ b : Ty.bool.denote, (c1 (Δ' := .bool :: Δ)).eval (.cons b env) = unifGdh p1)
    (h2 : c2.eval env = unifGdh p2)
    (h2b : ∀ b : Ty.bool.denote, (c2 (Δ' := .bool :: Δ)).eval (.cons b env) = unifGdh p2) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).eval env = unifGdh (chooseArm2Prob w1 w2 p1 p2) := by
  unfold chooseArm2C chooseArm2Prob; split_ifs
  · exact h2
  · exact h1
  · simp only [bindV, Comp.eval, bernoulliRatioGdhC_eval, unifGdh_bind]
    refine _root_.bind_congr fun b => ?_; cases b <;> simp [v, Expr.eval, Ext.wk, h1b, h2b]

private theorem samplePrin2C_eval (S : Setup) {Δ : List PT} (env : Env Δ) :
    (samplePrin2C S (Δ := Δ)).eval env = unifGdh (samplePrin2Prob S) := by
  unfold samplePrin2C samplePrin2Prob; split_ifs
  · simp only [Comp.eval, Expr.eval, unifGdh_pure]
  · simp only [bindV, Comp.eval, gPrim_sIndex_eval_unifGdh, v, Expr.eval, Env.get, Ext.wk,
      unifGdh_bind, unifGdh_pure]

private theorem sampleSpkPair2C_eval (S : Setup) {Δ : List PT} (env : Env Δ) :
    (sampleSpkPair2C S (Δ := Δ)).eval env = unifGdh (sampleSpkPair2Prob S) := by
  unfold sampleSpkPair2C sampleSpkPair2Prob; split_ifs
  · simp only [Comp.eval, Expr.eval, unifGdh_pure]
  · simp only [bindV, Comp.eval, gPrim_sIndex_eval_unifGdh, v, Expr.eval, Env.get, Ext.wk,
      unifGdh_bind, unifGdh_pure]

private theorem sampleOpkTriple2C_eval (S : Setup) {Δ : List PT} (env : Env Δ) :
    (sampleOpkTriple2C S (Δ := Δ)).eval env = unifGdh (sampleOpkTriple2Prob S) := by
  unfold sampleOpkTriple2C sampleOpkTriple2Prob; split_ifs
  · simp only [Comp.eval, Expr.eval, unifGdh_pure]
  · simp only [bindV, Comp.eval, gPrim_sIndex_eval_unifGdh, v, Expr.eval, Env.get, Ext.wk,
      unifGdh_bind, unifGdh_pure]

private theorem sampleSendOpkTarget2C_eval (S : Setup) {Δ : List PT} (env : Env Δ) :
    (sampleSendOpkTarget2C S (Δ := Δ)).eval env = unifGdh (sampleSendOpkTarget2Prob S) := by
  unfold sampleSendOpkTarget2C sampleSendOpkTarget2Prob; split_ifs
  · simp only [Comp.eval, Expr.eval, unifGdh_pure]
  · simp only [bindV, Comp.eval, gPrim_sIndex_eval_unifGdh, v, Expr.eval, Env.get, Ext.wk,
      unifGdh_bind, unifGdh_pure]

private theorem sampleSendNoOpkTarget2C_eval (S : Setup) {Δ : List PT} (env : Env Δ) :
    (sampleSendNoOpkTarget2C S (Δ := Δ)).eval env = unifGdh (sampleSendNoOpkTarget2Prob S) := by
  unfold sampleSendNoOpkTarget2C sampleSendNoOpkTarget2Prob; split_ifs
  · simp only [Comp.eval, Expr.eval, unifGdh_pure]
  · simp only [bindV, Comp.eval, gPrim_sIndex_eval_unifGdh, v, Expr.eval, Env.get, Ext.wk,
      unifGdh_bind, unifGdh_pure]

private theorem sampleSendTarget2C_eval (S : Setup) {Δ : List PT} (env : Env Δ) :
    (sampleSendTarget2C S (Δ := Δ)).eval env = unifGdh (sampleSendTarget2Prob S) := by
  unfold sampleSendTarget2C sampleSendTarget2Prob; split_ifs
  · simp [Comp.eval, Expr.eval, unifGdh_pure]
  · exact chooseArm2C_eval _ _ _ _ _ _ env
      (sampleSendOpkTarget2C_eval S env) (fun b => sampleSendOpkTarget2C_eval S (.cons b env))
      (sampleSendNoOpkTarget2C_eval S env) (fun b => sampleSendNoOpkTarget2C_eval S (.cons b env))

private theorem initParams1Key2C_eval (S : Setup) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (B 32) (B 32))) (env : Env Δ) :
    (initParams1Key2C S (Δ := Δ) uv).eval env =
      unifGdh (initParams1Key2Prob S (env.get (Ext.wk uv)).1 (env.get (Ext.wk uv)).2) := by
  unfold initParams1Key2C initParams1Key2Prob; split_ifs
  · simp [pa2Mk, v, Comp.eval, Expr.eval, unifGdh_pure]
  · refine chooseArm2C_eval _ _ _ _ _ _ env ?_ (fun b1 => ?_) ?_ (fun b1 => ?_) <;>
      refine chooseArm2C_eval _ _ _ _ _ _ _ ?_ (fun b2 => ?_) ?_ (fun b2 => ?_) <;>
      simp [bindV, pa2Mk, v, Comp.eval, Expr.eval, samplePrin2C_eval, sampleSpkPair2C_eval,
        sampleSendTarget2C_eval, sampleSendOpkTarget2C_eval, sampleOpkTriple2C_eval,
        Ext.wk, unifGdh_bind, unifGdh_map]

private theorem mem_support_sampleIndexRange_lt {N k : Nat} (hN : N ≠ 0)
    (hk : k ∈ support (sampleIndexRange N)) : k < N := by
  have hPos : 0 < N := Nat.pos_of_ne_zero hN
  simp only [sampleIndexRange, hPos, ↓reduceDIte, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hk
  obtain ⟨i, _, rfl⟩ := hk; exact i.isLt

private theorem mem_support_chooseArm2Prob {α : Type} {w1 w2 : Nat} {c1 c2 : ProbComp α} {x : α}
    (hx : x ∈ support (chooseArm2Prob w1 w2 c1 c2)) : x ∈ support c1 ∨ x ∈ support c2 := by
  unfold chooseArm2Prob at hx; split_ifs at hx
  · exact Or.inr hx
  · exact Or.inl hx
  · rw [mem_support_bind_iff] at hx; obtain ⟨b, _, hbx⟩ := hx; cases b; exacts [Or.inr hbx, Or.inl hbx]

private theorem mem_support_initParams1Key2Prob_inBounds (S : Setup) (U V : Bytes)
    {pa2 : params2Ty.denote} (hpa : pa2 ∈ support (initParams1Key2Prob S U V)) :
    InBoundsParams2 S pa2 := by
  have hPrin : ∀ {pt}, pt ∈ support (samplePrin2Prob S) → ∀ u, pt = some u → u < S.N_id := by
    intro pt hpt u hu; unfold samplePrin2Prob at hpt; split_ifs at hpt with hId
    · simp at hpt; subst hpt; cases hu
    · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hpt
      obtain ⟨v, hv, rfl⟩ := hpt; cases hu; exact mem_support_sampleIndexRange_lt hId hv
  have hSpk : ∀ {st}, st ∈ support (sampleSpkPair2Prob S) →
      ∀ u j, st = some (u, j) → u < S.N_id ∧ j < S.N_recv := by
    intro st hst u j huj; unfold sampleSpkPair2Prob at hst; split_ifs at hst with hS0
    · simp at hst; subst hst; cases huj
    · have hPos : 0 < S.N_id * S.N_recv := Nat.pos_of_ne_zero hS0
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hst
      obtain ⟨u', hu', j', hj', rfl⟩ := hst; cases huj
      exact ⟨mem_support_sampleIndexRange_lt (Nat.ne_of_gt (Nat.pos_of_mul_pos_right hPos)) hu',
        mem_support_sampleIndexRange_lt (Nat.ne_of_gt (Nat.pos_of_mul_pos_left hPos)) hj'⟩
  have hOpk : ∀ {ot}, ot ∈ support (sampleOpkTriple2Prob S) →
      ∀ u j o, ot = some (u, (j, o)) → u < S.N_id ∧ j < S.N_recv ∧ o < S.N_opk := by
    intro ot hot u j o hujo; unfold sampleOpkTriple2Prob at hot; split_ifs at hot with hO0
    · simp at hot; subst hot; cases hujo
    · have hPos : 0 < (S.N_id * S.N_recv) * S.N_opk := Nat.pos_of_ne_zero hO0
      have hSpkPos : 0 < S.N_id * S.N_recv := Nat.pos_of_mul_pos_right hPos
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hot
      obtain ⟨u', hu', j', hj', o', ho', rfl⟩ := hot; cases hujo
      exact ⟨mem_support_sampleIndexRange_lt (Nat.ne_of_gt (Nat.pos_of_mul_pos_right hSpkPos)) hu',
        mem_support_sampleIndexRange_lt (Nat.ne_of_gt (Nat.pos_of_mul_pos_left hSpkPos)) hj',
        mem_support_sampleIndexRange_lt (Nat.ne_of_gt (Nat.pos_of_mul_pos_left hPos)) ho'⟩
  have hSendOpk : ∀ {et}, et ∈ support (sampleSendOpkTarget2Prob S) →
      ∀ b u i, et = some (b, (u, i)) →
        u < S.N_id ∧ (if b then i < S.N_send_opk else i < S.N_send_no_opk) := by
    intro et het b u i hbui; unfold sampleSendOpkTarget2Prob at het; split_ifs at het with hSO0
    · simp at het; subst het; cases hbui
    · have hPos : 0 < S.N_id * S.N_send_opk := Nat.pos_of_ne_zero hSO0
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at het
      obtain ⟨u', hu', i', hi', rfl⟩ := het; cases hbui
      exact ⟨mem_support_sampleIndexRange_lt (Nat.ne_of_gt (Nat.pos_of_mul_pos_right hPos)) hu',
        mem_support_sampleIndexRange_lt (Nat.ne_of_gt (Nat.pos_of_mul_pos_left hPos)) hi'⟩
  have hSendNoOpk : ∀ {et}, et ∈ support (sampleSendNoOpkTarget2Prob S) →
      ∀ b u i, et = some (b, (u, i)) →
        u < S.N_id ∧ (if b then i < S.N_send_opk else i < S.N_send_no_opk) := by
    intro et het b u i hbui; unfold sampleSendNoOpkTarget2Prob at het; split_ifs at het with hSN0
    · simp at het; subst het; cases hbui
    · have hPos : 0 < S.N_id * S.N_send_no_opk := Nat.pos_of_ne_zero hSN0
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at het
      obtain ⟨u', hu', i', hi', rfl⟩ := het; cases hbui
      exact ⟨mem_support_sampleIndexRange_lt (Nat.ne_of_gt (Nat.pos_of_mul_pos_right hPos)) hu',
        mem_support_sampleIndexRange_lt (Nat.ne_of_gt (Nat.pos_of_mul_pos_left hPos)) hi'⟩
  have hSend : ∀ {et}, et ∈ support (sampleSendTarget2Prob S) →
      ∀ b u i, et = some (b, (u, i)) →
        u < S.N_id ∧ (if b then i < S.N_send_opk else i < S.N_send_no_opk) := by
    intro et het b u i hbui; unfold sampleSendTarget2Prob at het; split_ifs at het
    · simp at het; subst het; cases hbui
    · exact (mem_support_chooseArm2Prob het).elim (fun h1 => hSendOpk h1 b u i hbui)
        (fun h2 => hSendNoOpk h2 b u i hbui)
  unfold initParams1Key2Prob at hpa; split_ifs at hpa with hTot0
  · exact Or.inl hTot0
  · right
    rcases mem_support_chooseArm2Prob hpa with hAC | hBD
    · rcases mem_support_chooseArm2Prob hAC with hA | hC
      · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hA
        obtain ⟨pt, hpt, st, hst, rfl⟩ := hA
        exact ⟨hPrin hpt, (fun _ _ _ h => by cases h), hSpk hst, (fun _ _ _ h => by cases h)⟩
      · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hC
        obtain ⟨et, het, st, hst, rfl⟩ := hC
        exact ⟨(fun _ h => by cases h), hSend het, hSpk hst, (fun _ _ _ h => by cases h)⟩
    · rcases mem_support_chooseArm2Prob hBD with hB | hD
      · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hB
        obtain ⟨et, het, pt, hpt, rfl⟩ := hB
        exact ⟨hPrin hpt, hSend het, (fun _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hD
        obtain ⟨et, het, ot, hot, rfl⟩ := hD
        exact ⟨(fun _ h => by cases h), hSendOpk het, (fun _ _ h => by cases h), hOpk hot⟩

private theorem k1g_evalDist_sampleIndexRange_bind_singleton {N : ℕ} (hN : 0 < N)
    (g : ℕ → ProbComp Bool) (z : Bool) :
    𝒟[sampleIndexRange N >>= g] {z} = ∑ k ∈ Finset.range N, 𝒟[g k] {z} * (N : ℝ≥0∞)⁻¹ := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩; let : MeasurableSpace (Fin N) := ⊤
  simp only [sampleIndexRange, hN, ↓reduceDIte, bind_assoc, pure_bind]
  rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply (MeasurableSet.singleton z)
    (Measurable.of_discrete).aemeasurable, MeasureTheory.lintegral_fintype]
  simp_rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun k => 𝒟[g k] {z} * (N : ℝ≥0∞)⁻¹) N

private theorem k1g_mul_evalDist_sampleIndexRange {N : ℕ} (hN : 0 < N) (f : ℕ → ProbComp Bool) (z : Bool) :
    (N : ℝ≥0∞) * 𝒟[sampleIndexRange N >>= f] {z} = ∑ i ∈ Finset.range N, 𝒟[f i] {z} := by
  have hN0 : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [k1g_evalDist_sampleIndexRange_bind_singleton hN, ← Finset.sum_mul, ← mul_assoc,
    mul_comm (N : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel hN0 (ENNReal.natCast_ne_top N), mul_one]

private theorem k1g_sum_range_mul_div_mod_ennreal (M N : ℕ) (g : ℕ → ℕ → ℝ≥0∞) :
    ∑ k ∈ Finset.range (M * N), g (k / N) (k % N) = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N, g i j := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_one_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]; congr 1
    refine Finset.sum_congr rfl fun j hj => ?_; rw [Finset.mem_range] at hj; have hPos : 0 < N := by omega
    rw [Nat.add_comm (m * N) j, Nat.add_mul_div_right j m hPos, Nat.div_eq_of_lt hj,
      Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

private theorem k1g_sum_range_lt_split (c K : ℕ) (hc : c ≤ K) (a b : ℝ≥0∞) :
    (∑ y ∈ Finset.range K, if y < c then a else b) = (c : ℝ≥0∞) * a + ((K - c : ℕ) : ℝ≥0∞) * b := by
  conv_lhs => rw [show K = c + (K - c) from (Nat.add_sub_of_le hc).symm]
  rw [Finset.sum_range_add]; congr 1
  · rw [Finset.sum_congr rfl (g := fun _ => a) (fun y hy => by simp [Finset.mem_range.mp hy])]
    simp
  · rw [Finset.sum_congr rfl (g := fun _ => b) (fun y _ => by simp [show ¬ (c + y < c) by omega])]
    simp

private theorem k1g_sum_range_odd (m : ℕ) : ∑ x ∈ Finset.range m, (2 * x + 1) = m * m := by
  induction m with | zero => simp | succ k ih => rw [Finset.sum_range_succ, ih]; ring

private theorem k1g_sum_range_sq_add_one (m : ℕ) :
    (∑ y1 ∈ Finset.range m, ∑ y2 ∈ Finset.range m, (y1 + y2 + 1)) = m * m * m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]; simp_rw [Finset.sum_range_succ]; rw [Finset.sum_add_distrib, ih]
    have hCombine : (∑ x ∈ Finset.range k, (x + k + 1)) + ∑ x ∈ Finset.range k, (k + x + 1) =
        (∑ x ∈ Finset.range k, (2 * x + 1)) + ∑ _x ∈ Finset.range k, (2 * k + 1) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun x _ => by omega
    have h1 := k1g_sum_range_odd k
    have h2 : ∑ _x ∈ Finset.range k, (2 * k + 1) = k * (2 * k + 1) := by simp
    nlinarith

private theorem k1g_sum_range_sq_sub_add_one (m K : ℕ) (h : m + m ≤ K) :
    (∑ y1 ∈ Finset.range m, ∑ y2 ∈ Finset.range m, (K - (y1 + y2 + 1))) = m * m * (K - m) := by
  have hAdd : (∑ y1 ∈ Finset.range m, ∑ y2 ∈ Finset.range m, (K - (y1 + y2 + 1))) +
      (∑ y1 ∈ Finset.range m, ∑ y2 ∈ Finset.range m, (y1 + y2 + 1)) = m * m * K := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (g := fun _ => m * K) fun y1 hy1 => by
      rw [← Finset.sum_add_distrib]
      have hy1' : y1 < m := Finset.mem_range.mp hy1
      rw [Finset.sum_congr rfl (g := fun _ => K) fun y2 hy2 => by
        have := Finset.mem_range.mp hy2; omega]
      simp]
    simp [Nat.mul_assoc]
  rw [k1g_sum_range_sq_add_one] at hAdd
  rw [Nat.mul_sub_left_distrib]
  omega

private theorem k1g_evalDist_bernoulliCube_scaled {M K : ℕ} (hM : 0 < M) (hMK : M + M ≤ K)
    (pT pF : ProbComp Bool) (z : Bool) :
    (K : ℝ≥0∞) * 𝒟[sampleIndexRange K >>= fun x => sampleIndexRange M >>= fun y1 =>
        sampleIndexRange M >>= fun y2 => if decide (x < y1 + y2 + 1) = true then pT else pF] {z} =
      (M : ℝ≥0∞) * 𝒟[pT] {z} + ((K - M : ℕ) : ℝ≥0∞) * 𝒟[pF] {z} := by
  have hK : 0 < K := by omega
  have hM0 : (M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
  have hMtop : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top M
  rw [k1g_mul_evalDist_sampleIndexRange hK]
  have hInner : ∀ x ∈ Finset.range K,
      𝒟[sampleIndexRange M >>= fun y1 => sampleIndexRange M >>= fun y2 =>
          if decide (x < y1 + y2 + 1) = true then pT else pF] {z} =
        ∑ y1 ∈ Finset.range M, (∑ y2 ∈ Finset.range M,
          (if x < y1 + y2 + 1 then 𝒟[pT] {z} else 𝒟[pF] {z}) * (M : ℝ≥0∞)⁻¹) * (M : ℝ≥0∞)⁻¹ := fun x _ => by
    rw [k1g_evalDist_sampleIndexRange_bind_singleton hM]
    refine Finset.sum_congr rfl fun y1 _ => congrArg (· * (M : ℝ≥0∞)⁻¹) ?_
    rw [k1g_evalDist_sampleIndexRange_bind_singleton hM]
    exact Finset.sum_congr rfl fun y2 _ => by by_cases hlt : x < y1 + y2 + 1 <;> simp [hlt]
  rw [Finset.sum_congr rfl hInner, Finset.sum_comm]
  have hSwap2 : (∑ y1 ∈ Finset.range M, ∑ x ∈ Finset.range K,
      (∑ y2 ∈ Finset.range M, (if x < y1 + y2 + 1 then 𝒟[pT] {z} else 𝒟[pF] {z}) * (M : ℝ≥0∞)⁻¹) * (M : ℝ≥0∞)⁻¹) =
      ∑ y1 ∈ Finset.range M, (∑ y2 ∈ Finset.range M,
        (((y1 + y2 + 1 : ℕ) : ℝ≥0∞) * 𝒟[pT] {z} + ((K - (y1 + y2 + 1) : ℕ) : ℝ≥0∞) * 𝒟[pF] {z}) *
          (M : ℝ≥0∞)⁻¹) * (M : ℝ≥0∞)⁻¹ := Finset.sum_congr rfl fun y1 hy1 => by
    have hy1' : y1 < M := Finset.mem_range.mp hy1; simp_rw [← Finset.sum_mul]
    refine congrArg (· * (M : ℝ≥0∞)⁻¹) (congrArg (· * (M : ℝ≥0∞)⁻¹) ?_); rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y2 hy2 => by
      have := Finset.mem_range.mp hy2; exact k1g_sum_range_lt_split (y1 + y2 + 1) K (by omega) _ _
  rw [hSwap2]; simp_rw [← Finset.sum_mul]
  have hSplit : (∑ y1 ∈ Finset.range M, ∑ y2 ∈ Finset.range M,
      (((y1 + y2 + 1 : ℕ) : ℝ≥0∞) * 𝒟[pT] {z} + ((K - (y1 + y2 + 1) : ℕ) : ℝ≥0∞) * 𝒟[pF] {z})) =
      ((M * M * M : ℕ) : ℝ≥0∞) * 𝒟[pT] {z} + ((M * M * (K - M) : ℕ) : ℝ≥0∞) * 𝒟[pF] {z} := by
    simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Nat.cast_sum]
    rw [k1g_sum_range_sq_add_one M, k1g_sum_range_sq_sub_add_one M K hMK]
  rw [hSplit]
  have hCancel : ∀ c : ℝ≥0∞, ((M : ℝ≥0∞) * (M : ℝ≥0∞) * c) * (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞)⁻¹ = c := fun c => by
    rw [mul_comm ((M : ℝ≥0∞) * (M : ℝ≥0∞)) c, mul_assoc c, mul_assoc (M : ℝ≥0∞) (M : ℝ≥0∞) (M : ℝ≥0∞)⁻¹,
      ENNReal.mul_inv_cancel hM0 hMtop, mul_one, mul_assoc c, ENNReal.mul_inv_cancel hM0 hMtop, mul_one]
  simp only [Nat.cast_mul, add_mul]
  rw [mul_assoc ((M : ℝ≥0∞) * (M : ℝ≥0∞)) (M : ℝ≥0∞) (𝒟[pT] {z}), hCancel,
    mul_assoc ((M : ℝ≥0∞) * (M : ℝ≥0∞)) (((K - M : ℕ) : ℝ≥0∞)) (𝒟[pF] {z}), hCancel]

private theorem k1g_evalDist_bernoulliRatioGdhProb_scaled {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (pT pF : ProbComp Bool) (z : Bool) :
    ((A + B : ℕ) : ℝ≥0∞) * 𝒟[bernoulliRatioGdhProb A B >>= fun u => if u = true then pT else pF] {z} =
      (A : ℝ≥0∞) * 𝒟[pT] {z} + (B : ℝ≥0∞) * 𝒟[pF] {z} := by
  unfold bernoulliRatioGdhProb; simp only [Nat.ne_of_gt hA, Nat.ne_of_gt hB, ↓reduceIte]
  by_cases hAB : A ≤ B
  · simp only [hAB, ↓reduceIte, bind_assoc, pure_bind]
    rw [k1g_evalDist_bernoulliCube_scaled hA (by omega), Nat.add_sub_cancel_left]
  · simp only [hAB, ↓reduceIte, bind_assoc, pure_bind]
    have hRew : (sampleIndexRange (A + B) >>= fun x => sampleIndexRange B >>= fun y1 =>
        sampleIndexRange B >>= fun y2 => if (!decide (x < y1 + y2 + 1)) = true then pT else pF) =
        (sampleIndexRange (A + B) >>= fun x => sampleIndexRange B >>= fun y1 =>
          sampleIndexRange B >>= fun y2 => if decide (x < y1 + y2 + 1) = true then pF else pT) :=
      _root_.bind_congr fun x => _root_.bind_congr fun y1 => _root_.bind_congr fun y2 => by
        cases decide (x < y1 + y2 + 1) <;> rfl
    rw [hRew, k1g_evalDist_bernoulliCube_scaled hB (by omega), Nat.add_sub_cancel_right, add_comm]

private theorem k1g_evalDist_chooseArm2Prob_bind_scaled {α : Type} (w1 w2 : ℕ)
    (c1 c2 : ProbComp α) (k : α → ProbComp Bool) (z : Bool) :
    ((w1 + w2 : ℕ) : ℝ≥0∞) * 𝒟[chooseArm2Prob w1 w2 c1 c2 >>= k] {z} =
      (w1 : ℝ≥0∞) * 𝒟[c1 >>= k] {z} + (w2 : ℝ≥0∞) * 𝒟[c2 >>= k] {z} := by
  unfold chooseArm2Prob; split_ifs with hw1 hw2
  · subst hw1; simp
  · subst hw2; simp
  · have hBind : ((bernoulliRatioGdhProb w1 w2 >>= fun b => if b = true then c1 else c2) >>= k) =
        (bernoulliRatioGdhProb w1 w2 >>= fun b => if b = true then c1 >>= k else c2 >>= k) := by
      rw [bind_assoc]; exact _root_.bind_congr fun b => by cases b <;> rfl
    exact (congrArg (fun m => ((w1 + w2 : ℕ) : ℝ≥0∞) * 𝒟[m] {z}) hBind).trans
      (k1g_evalDist_bernoulliRatioGdhProb_scaled (Nat.pos_of_ne_zero hw1) (Nat.pos_of_ne_zero hw2) (c1 >>= k) (c2 >>= k) z)

private def sendTarget2OfFlat (S : Setup) (tIdx : Nat) : Option (Bool × (Nat × Nat)) :=
  if tIdx < S.N_send_opk_tot then some (true, (tIdx / S.N_send_opk, tIdx % S.N_send_opk))
  else let r := tIdx - S.N_send_opk_tot; some (false, (r / S.N_send_no_opk, r % S.N_send_no_opk))

private theorem eiRaw_sendTarget2OfFlat (S : Setup) {tIdx : Nat} (ht : tIdx < S.N_send_tot) :
    (match sendTarget2OfFlat S tIdx with
      | none => S.N_send_tot
      | some (true, (u, i)) => u * Nat.min S.N_send_opk S.N_send_opk_tot + i
      | some (false, (u, i)) => S.N_send_opk_tot + (u * Nat.min S.N_send_no_opk S.N_send_no_opk_tot + i)) = tIdx := by
  have hSendEq : S.N_send_tot = S.N_id * S.N_send_opk + S.N_id * S.N_send_no_opk := rfl
  have hIdPos : 0 < S.N_id := by by_contra h0; rw [hSendEq, show S.N_id = 0 by omega] at ht; simp at ht
  unfold sendTarget2OfFlat; split_ifs with hlt
  · have hMin : Nat.min S.N_send_opk S.N_send_opk_tot = S.N_send_opk :=
      Nat.min_eq_left (by simpa [Setup.N_send_opk_tot] using Nat.mul_le_mul_right S.N_send_opk hIdPos)
    dsimp only; rw [hMin, Nat.mul_comm _ S.N_send_opk, Nat.div_add_mod]
  · have hMin : Nat.min S.N_send_no_opk S.N_send_no_opk_tot = S.N_send_no_opk :=
      Nat.min_eq_left (by simpa [Setup.N_send_no_opk_tot] using Nat.mul_le_mul_right S.N_send_no_opk hIdPos)
    dsimp only; rw [hMin, Nat.mul_comm _ S.N_send_no_opk, Nat.div_add_mod]
    exact Nat.add_sub_of_le (Nat.le_of_not_lt hlt)

private theorem k1g_evalDist_sampleSendOpkTarget2Prob_scaled (S : Setup)
    (k : Option (Bool × (Nat × Nat)) → ProbComp Bool) (z : Bool) :
    (S.N_send_opk_tot : ℝ≥0∞) * 𝒟[sampleSendOpkTarget2Prob S >>= k] {z} =
      ∑ t ∈ Finset.range S.N_send_opk_tot, 𝒟[k (some (true, (t / S.N_send_opk, t % S.N_send_opk)))] {z} := by
  unfold sampleSendOpkTarget2Prob; by_cases h0 : S.N_send_opk_tot = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte, bind_assoc, pure_bind]
    have hPos : 0 < S.N_id * S.N_send_opk := Nat.pos_of_ne_zero h0
    change ((S.N_id * S.N_send_opk : ℕ) : ℝ≥0∞) * _ = ∑ t ∈ Finset.range (S.N_id * S.N_send_opk), _
    rw [Nat.cast_mul, mul_comm (S.N_id : ℝ≥0∞), mul_assoc,
      k1g_mul_evalDist_sampleIndexRange (Nat.pos_of_mul_pos_right hPos), Finset.mul_sum]
    simp_rw [k1g_mul_evalDist_sampleIndexRange (Nat.pos_of_mul_pos_left hPos)]
    exact (k1g_sum_range_mul_div_mod_ennreal S.N_id S.N_send_opk _).symm

private theorem k1g_evalDist_sampleSendNoOpkTarget2Prob_scaled (S : Setup)
    (k : Option (Bool × (Nat × Nat)) → ProbComp Bool) (z : Bool) :
    (S.N_send_no_opk_tot : ℝ≥0∞) * 𝒟[sampleSendNoOpkTarget2Prob S >>= k] {z} =
      ∑ r ∈ Finset.range S.N_send_no_opk_tot, 𝒟[k (some (false, (r / S.N_send_no_opk, r % S.N_send_no_opk)))] {z} := by
  unfold sampleSendNoOpkTarget2Prob; by_cases h0 : S.N_send_no_opk_tot = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte, bind_assoc, pure_bind]
    have hPos : 0 < S.N_id * S.N_send_no_opk := Nat.pos_of_ne_zero h0
    change ((S.N_id * S.N_send_no_opk : ℕ) : ℝ≥0∞) * _ = ∑ r ∈ Finset.range (S.N_id * S.N_send_no_opk), _
    rw [Nat.cast_mul, mul_comm (S.N_id : ℝ≥0∞), mul_assoc,
      k1g_mul_evalDist_sampleIndexRange (Nat.pos_of_mul_pos_right hPos), Finset.mul_sum]
    simp_rw [k1g_mul_evalDist_sampleIndexRange (Nat.pos_of_mul_pos_left hPos)]
    exact (k1g_sum_range_mul_div_mod_ennreal S.N_id S.N_send_no_opk _).symm

private theorem k1g_evalDist_sampleSendTarget2Prob_scaled (S : Setup)
    (k : Option (Bool × (Nat × Nat)) → ProbComp Bool) (z : Bool) :
    (S.N_send_tot : ℝ≥0∞) * 𝒟[sampleSendTarget2Prob S >>= k] {z} =
      ∑ tIdx ∈ Finset.range S.N_send_tot, 𝒟[k (sendTarget2OfFlat S tIdx)] {z} := by
  unfold sampleSendTarget2Prob; by_cases h0 : S.N_send_tot = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]; have hTotEq : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
    rw [hTotEq, k1g_evalDist_chooseArm2Prob_bind_scaled, Finset.sum_range_add,
      k1g_evalDist_sampleSendOpkTarget2Prob_scaled, k1g_evalDist_sampleSendNoOpkTarget2Prob_scaled]
    congr 1
    · exact Finset.sum_congr rfl fun t ht => by simp [sendTarget2OfFlat, Finset.mem_range.mp ht]
    · exact Finset.sum_congr rfl fun r _ => by simp [sendTarget2OfFlat, show ¬ (S.N_send_opk_tot + r < S.N_send_opk_tot) by omega]

private theorem k1g_evalDist_samplePrin2Prob_scaled (S : Setup)
    (k : Option Nat → ProbComp Bool) (z : Bool) :
    (S.N_id : ℝ≥0∞) * 𝒟[samplePrin2Prob S >>= k] {z} =
      ∑ u ∈ Finset.range S.N_id, 𝒟[k (some u)] {z} := by
  unfold samplePrin2Prob; by_cases h0 : S.N_id = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte, bind_assoc, pure_bind]
    exact k1g_mul_evalDist_sampleIndexRange (Nat.pos_of_ne_zero h0) (fun u => k (some u)) z

private theorem k1g_evalDist_sampleSpkPair2Prob_scaled (S : Setup)
    (k : Option (Nat × Nat) → ProbComp Bool) (z : Bool) :
    (S.N_spk_tot : ℝ≥0∞) * 𝒟[sampleSpkPair2Prob S >>= k] {z} =
      ∑ sIdx ∈ Finset.range S.N_spk_tot,
        𝒟[k (some (sIdx / S.N_recv, sIdx % S.N_recv))] {z} := by
  unfold sampleSpkPair2Prob; by_cases h0 : S.N_spk_tot = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte, bind_assoc, pure_bind]
    have hPos : 0 < S.N_id * S.N_recv := Nat.pos_of_ne_zero h0
    change ((S.N_id * S.N_recv : ℕ) : ℝ≥0∞) * _ = ∑ sIdx ∈ Finset.range (S.N_id * S.N_recv), _
    rw [Nat.cast_mul, mul_comm (S.N_id : ℝ≥0∞), mul_assoc,
      k1g_mul_evalDist_sampleIndexRange (Nat.pos_of_mul_pos_right hPos), Finset.mul_sum]
    simp_rw [k1g_mul_evalDist_sampleIndexRange (Nat.pos_of_mul_pos_left hPos)]
    exact (k1g_sum_range_mul_div_mod_ennreal S.N_id S.N_recv _).symm

private theorem k1g_evalDist_sampleOpkTriple2Prob_scaled (S : Setup)
    (k : Option (Nat × (Nat × Nat)) → ProbComp Bool) (z : Bool) :
    (S.N_opk_tot : ℝ≥0∞) * 𝒟[sampleOpkTriple2Prob S >>= k] {z} =
      ∑ oIdx ∈ Finset.range S.N_opk_tot,
        𝒟[k (some ((oIdx / S.N_opk) / S.N_recv, ((oIdx / S.N_opk) % S.N_recv, oIdx % S.N_opk)))] {z} := by
  unfold sampleOpkTriple2Prob; by_cases h0 : S.N_opk_tot = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte, bind_assoc, pure_bind]
    have hPos : 0 < (S.N_id * S.N_recv) * S.N_opk := Nat.pos_of_ne_zero h0
    have hSpkPos : 0 < S.N_id * S.N_recv := Nat.pos_of_mul_pos_right hPos
    change (((S.N_id * S.N_recv) * S.N_opk : ℕ) : ℝ≥0∞) * _ =
      ∑ oIdx ∈ Finset.range ((S.N_id * S.N_recv) * S.N_opk), _
    rw [k1g_sum_range_mul_div_mod_ennreal (S.N_id * S.N_recv) S.N_opk
      (fun sIdx o => 𝒟[k (some (sIdx / S.N_recv, (sIdx % S.N_recv, o)))] {z})]
    simp_rw [k1g_sum_range_mul_div_mod_ennreal S.N_id S.N_recv
      (fun u j => ∑ o ∈ Finset.range S.N_opk, 𝒟[k (some (u, (j, o)))] {z})]
    have hRearr : (((S.N_id * S.N_recv) * S.N_opk : ℕ) : ℝ≥0∞) *
        𝒟[sampleIndexRange S.N_id >>= fun u => sampleIndexRange S.N_recv >>= fun j =>
          sampleIndexRange S.N_opk >>= fun o => k (some (u, (j, o)))] {z} =
        ((S.N_recv : ℝ≥0∞) * (S.N_opk : ℝ≥0∞)) * ((S.N_id : ℝ≥0∞) *
          𝒟[sampleIndexRange S.N_id >>= fun u => sampleIndexRange S.N_recv >>= fun j =>
            sampleIndexRange S.N_opk >>= fun o => k (some (u, (j, o)))] {z}) := by
      push_cast; ring
    rw [hRearr, k1g_mul_evalDist_sampleIndexRange (Nat.pos_of_mul_pos_right hSpkPos), Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_comm (S.N_recv : ℝ≥0∞) (S.N_opk : ℝ≥0∞), mul_assoc,
      k1g_mul_evalDist_sampleIndexRange (Nat.pos_of_mul_pos_left hSpkPos), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ =>
      k1g_mul_evalDist_sampleIndexRange (Nat.pos_of_mul_pos_left hPos) (fun o => k (some (u, (j, o)))) z

private theorem evalDist_initParams1Key2Prob_map_bind (S : Setup) (U V : Bytes)
    (g : paramsTy.denote → ProbComp Bool) (z : Bool) :
    𝒟[initParams1Key2Prob S U V >>= fun pa2 => g (params2ToFlat S pa2)] {z} =
      𝒟[sampleIndexRange (fgTotalIndexCount S) >>= fun idx => g (params1KeyFlatVal S U V idx)] {z} := by
  let g2 : params2Ty.denote → ProbComp Bool := fun pa2 => g (params2ToFlat S pa2)
  change 𝒟[initParams1Key2Prob S U V >>= g2] {z} = _
  unfold initParams1Key2Prob; by_cases hTot0 : fgTotalIndexCount S = 0
  · simp only [hTot0, ↓reduceIte, sampleIndexRange, lt_self_iff_false, ↓reduceDIte, pure_bind]
    have hSplit : S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
        S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot = 0 := hTot0
    exact congrArg (fun p => 𝒟[g p] {z}) (by
      simp [params2ToFlat, params1KeyFlatVal, paramsOpkVal,
        show S.N_id * S.N_spk_tot = 0 by omega, show S.N_send_tot * S.N_spk_tot = 0 by omega,
        show S.N_send_tot * S.N_id = 0 by omega])
  · simp only [hTot0, ↓reduceIte]
    let nA := S.N_id * S.N_spk_tot
    let nC := S.N_send_tot * S.N_spk_tot
    let nB := S.N_send_tot * S.N_id
    let nD := S.N_send_opk_tot * S.N_opk_tot
    have hTotDef : fgTotalIndexCount S = (nA + nC) + (nB + nD) := by
      change S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
        S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot = _; omega
    refine (ENNReal.mul_right_inj (Nat.cast_ne_zero.mpr hTot0) (ENNReal.natCast_ne_top _)).mp ?_
    rw [k1g_mul_evalDist_sampleIndexRange (Nat.pos_of_ne_zero hTot0)]
    conv_lhs => arg 1; rw [hTotDef]
    rw [k1g_evalDist_chooseArm2Prob_bind_scaled, k1g_evalDist_chooseArm2Prob_bind_scaled,
      k1g_evalDist_chooseArm2Prob_bind_scaled]
    have hArmA : (nA : ℝ≥0∞) * 𝒟[(do
        let pt ← samplePrin2Prob S; let st ← sampleSpkPair2Prob S
        return (U, (V, (U, (pt, (true, (none, (st, (false, (none, 0)))))))))) >>= g2] {z} =
        ∑ idx ∈ Finset.range nA, 𝒟[g (params1KeyFlatVal S U V idx)] {z} := by
      dsimp only [nA]; simp only [bind_assoc, pure_bind]
      rw [Nat.cast_mul, mul_comm (S.N_id : ℝ≥0∞), mul_assoc,
        k1g_evalDist_samplePrin2Prob_scaled, Finset.mul_sum]
      simp_rw [k1g_evalDist_sampleSpkPair2Prob_scaled]
      have hRhs : (∑ idx ∈ Finset.range (S.N_id * S.N_spk_tot), 𝒟[g (params1KeyFlatVal S U V idx)] {z}) =
          ∑ idx ∈ Finset.range (S.N_id * S.N_spk_tot),
            𝒟[g (paramsDhVal S true (idx / S.N_spk_tot) (idx % S.N_spk_tot) U V)] {z} :=
        Finset.sum_congr rfl fun idx hidx => by simp [params1KeyFlatVal, Finset.mem_range.mp hidx]
      rw [hRhs, k1g_sum_range_mul_div_mod_ennreal S.N_id S.N_spk_tot
        (fun u sIdx => 𝒟[g (paramsDhVal S true u sIdx U V)] {z})]
      refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun sIdx _ =>
        congrArg (fun p => 𝒟[g p] {z}) ?_
      have hIdPos : 0 < S.N_id := by have := Finset.mem_range.mp hu; omega
      have hMin : Nat.min S.N_recv S.N_spk_tot = S.N_recv :=
        Nat.min_eq_left (by simpa [Setup.N_spk_tot] using Nat.mul_le_mul_right S.N_recv hIdPos)
      simp [params2ToFlat, paramsDhVal, hMin, Nat.mul_comm _ S.N_recv, Nat.div_add_mod]
    have hArmC : (nC : ℝ≥0∞) * 𝒟[(do
        let et ← sampleSendTarget2Prob S; let st ← sampleSpkPair2Prob S
        return (U, (V, (U, (none, (false, (et, (st, (false, (none, 1)))))))))) >>= g2] {z} =
        ∑ r ∈ Finset.range nC, 𝒟[g (params1KeyFlatVal S U V (nA + r))] {z} := by
      dsimp only [nC]; simp only [bind_assoc, pure_bind]
      rw [Nat.cast_mul, mul_comm (S.N_send_tot : ℝ≥0∞), mul_assoc,
        k1g_evalDist_sampleSendTarget2Prob_scaled, Finset.mul_sum]
      simp_rw [k1g_evalDist_sampleSpkPair2Prob_scaled]
      have hRhs : (∑ r ∈ Finset.range (S.N_send_tot * S.N_spk_tot),
          𝒟[g (params1KeyFlatVal S U V (nA + r))] {z}) =
          ∑ r ∈ Finset.range (S.N_send_tot * S.N_spk_tot),
            𝒟[g (paramsDhVal S false (r / S.N_spk_tot) (r % S.N_spk_tot) U V)] {z} :=
        Finset.sum_congr rfl fun r hr => by
          have hlt := Finset.mem_range.mp hr
          have hge : ¬ (nA + r < nA) := by omega
          have hlt2 : nA + r < nA + S.N_send_tot * S.N_spk_tot := by omega
          dsimp only [nA] at hge hlt2 ⊢; simp [params1KeyFlatVal, hge, hlt2]
      rw [hRhs, k1g_sum_range_mul_div_mod_ennreal S.N_send_tot S.N_spk_tot
        (fun tIdx sIdx => 𝒟[g (paramsDhVal S false tIdx sIdx U V)] {z})]
      refine Finset.sum_congr rfl fun tIdx ht => Finset.sum_congr rfl fun sIdx hs =>
        congrArg (fun p => 𝒟[g p] {z}) ?_
      have hs' : sIdx < S.N_id * S.N_recv := Finset.mem_range.mp hs
      have hIdPos : 0 < S.N_id := by by_contra h0; rw [show S.N_id = 0 by omega] at hs'; simp at hs'
      have hMin : Nat.min S.N_recv S.N_spk_tot = S.N_recv :=
        Nat.min_eq_left (by simpa [Setup.N_spk_tot] using Nat.mul_le_mul_right S.N_recv hIdPos)
      simp [params2ToFlat, paramsDhVal, hMin, Nat.mul_comm _ S.N_recv, Nat.div_add_mod]
      exact eiRaw_sendTarget2OfFlat S (Finset.mem_range.mp ht)
    have hArmB : (nB : ℝ≥0∞) * 𝒟[(do
        let et ← sampleSendTarget2Prob S; let pt ← samplePrin2Prob S
        return (V, (U, (U, (pt, (false, (et, (none, (false, (none, 2)))))))))) >>= g2] {z} =
        ∑ r ∈ Finset.range nB, 𝒟[g (params1KeyFlatVal S U V ((nA + nC) + r))] {z} := by
      dsimp only [nB]; simp only [bind_assoc, pure_bind]
      rw [Nat.cast_mul, mul_comm (S.N_send_tot : ℝ≥0∞), mul_assoc,
        k1g_evalDist_sampleSendTarget2Prob_scaled, Finset.mul_sum]
      simp_rw [k1g_evalDist_samplePrin2Prob_scaled]
      have hRhs : (∑ r ∈ Finset.range (S.N_send_tot * S.N_id),
          𝒟[g (params1KeyFlatVal S U V ((nA + nC) + r))] {z}) =
          ∑ r ∈ Finset.range (S.N_send_tot * S.N_id),
            𝒟[g (params1KeyIkVal S (r / S.N_id) (r % S.N_id) U V)] {z} :=
        Finset.sum_congr rfl fun r hr => by
          have hlt := Finset.mem_range.mp hr
          have hge1 : ¬ ((nA + nC) + r < nA) := by omega
          have hge2 : ¬ ((nA + nC) + r < nA + nC) := by omega
          have hlt3 : (nA + nC) + r < nA + nC + S.N_send_tot * S.N_id := by omega
          dsimp only [nA, nC] at hge1 hge2 hlt3 ⊢; simp [params1KeyFlatVal, hge1, hge2, hlt3]
      rw [hRhs, k1g_sum_range_mul_div_mod_ennreal S.N_send_tot S.N_id
        (fun tIdx pIdx => 𝒟[g (params1KeyIkVal S tIdx pIdx U V)] {z})]
      refine Finset.sum_congr rfl fun tIdx ht => Finset.sum_congr rfl fun pIdx _ =>
        congrArg (fun p => 𝒟[g p] {z}) ?_
      simp [params2ToFlat, params1KeyIkVal]; exact eiRaw_sendTarget2OfFlat S (Finset.mem_range.mp ht)
    have hArmD : (nD : ℝ≥0∞) * 𝒟[(do
        let et ← sampleSendOpkTarget2Prob S; let ot ← sampleOpkTriple2Prob S
        return (U, (V, (U, (none, (false, (et, (none, (true, (ot, 3)))))))))) >>= g2] {z} =
        ∑ r ∈ Finset.range nD, 𝒟[g (params1KeyFlatVal S U V ((nA + nC) + (nB + r)))] {z} := by
      dsimp only [nD]; simp only [bind_assoc, pure_bind]
      rw [Nat.cast_mul, mul_comm (S.N_send_opk_tot : ℝ≥0∞), mul_assoc,
        k1g_evalDist_sampleSendOpkTarget2Prob_scaled, Finset.mul_sum]
      simp_rw [k1g_evalDist_sampleOpkTriple2Prob_scaled]
      have hRhs : (∑ r ∈ Finset.range (S.N_send_opk_tot * S.N_opk_tot),
          𝒟[g (params1KeyFlatVal S U V ((nA + nC) + (nB + r)))] {z}) =
          ∑ r ∈ Finset.range (S.N_send_opk_tot * S.N_opk_tot),
            𝒟[g (paramsOpkVal S (r / S.N_opk_tot) (r % S.N_opk_tot) U V)] {z} :=
        Finset.sum_congr rfl fun r _ => by
          have hge1 : ¬ ((nA + nC) + (nB + r) < nA) := by omega
          have hge2 : ¬ ((nA + nC) + (nB + r) < nA + nC) := by omega
          have hge3 : ¬ ((nA + nC) + (nB + r) < nA + nC + nB) := by omega
          have hSub : ((nA + nC) + (nB + r)) - (nA + nC + nB) = r := by omega
          dsimp only [nA, nC, nB] at hge1 hge2 hge3 hSub ⊢; simp [params1KeyFlatVal, hge1, hge2, hge3, hSub]
      rw [hRhs, k1g_sum_range_mul_div_mod_ennreal S.N_send_opk_tot S.N_opk_tot
        (fun tIdx oIdx => 𝒟[g (paramsOpkVal S tIdx oIdx U V)] {z})]
      refine Finset.sum_congr rfl fun tIdx _ => Finset.sum_congr rfl fun oIdx ho =>
        congrArg (fun p => 𝒟[g p] {z}) ?_
      have ho' : oIdx < (S.N_id * S.N_recv) * S.N_opk := Finset.mem_range.mp ho
      have hSpkPos : 0 < S.N_id * S.N_recv := by
        by_contra h0; rw [show S.N_id * S.N_recv = 0 by omega] at ho'; simp at ho'
      have hIdPos : 0 < S.N_id := Nat.pos_of_mul_pos_right hSpkPos
      have hMinS : Nat.min S.N_send_opk S.N_send_opk_tot = S.N_send_opk :=
        Nat.min_eq_left (by simpa [Setup.N_send_opk_tot] using Nat.mul_le_mul_right S.N_send_opk hIdPos)
      have hMinR : Nat.min S.N_recv S.N_spk_tot = S.N_recv :=
        Nat.min_eq_left (by simpa [Setup.N_spk_tot] using Nat.mul_le_mul_right S.N_recv hIdPos)
      have hMinO : Nat.min S.N_opk S.N_opk_tot = S.N_opk :=
        Nat.min_eq_left (by simpa [Setup.N_opk_tot, Setup.N_spk_tot] using Nat.mul_le_mul_right S.N_opk hSpkPos)
      simp [params2ToFlat, paramsOpkVal, hMinS, hMinR, hMinO,
        Nat.mul_comm _ S.N_send_opk, Nat.mul_comm _ S.N_recv, Nat.mul_comm _ S.N_opk, Nat.div_add_mod]
    rw [hArmA, hArmC, hArmB, hArmD, hTotDef, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]

private theorem evalDist_initParams1Key2Prob_map_bind_measure (S : Setup) (U V : Bytes)
    (g : paramsTy.denote → ProbComp Bool) :
    𝒟[initParams1Key2Prob S U V >>= fun pa2 => g (params2ToFlat S pa2)] =
      𝒟[sampleIndexRange (fgTotalIndexCount S) >>= fun idx => g (params1KeyFlatVal S U V idx)] :=
  MeasureTheory.Measure.ext_of_singleton (evalDist_initParams1Key2Prob_map_bind S U V g)

private theorem exists_flat_of_mem_support_initParams1Key2Prob (S : Setup) (U V : Bytes)
    {pa2 : params2Ty.denote} (hpa : pa2 ∈ support (initParams1Key2Prob S U V)) :
    ∃ idx ∈ support (sampleIndexRange (fgTotalIndexCount S)),
      params2ToFlat S pa2 = params1KeyFlatVal S U V idx := by
  classical
  let P : paramsTy.denote → Prop := fun pa =>
    ∃ idx ∈ support (sampleIndexRange (fgTotalIndexCount S)), pa = params1KeyFlatVal S U V idx
  let g : paramsTy.denote → ProbComp Bool := fun pa => pure (decide (P pa))
  have hNoFalseR : false ∉ support (sampleIndexRange (fgTotalIndexCount S) >>=
      fun idx => g (params1KeyFlatVal S U V idx)) := by
    rw [mem_support_bind_iff]; rintro ⟨idx, hIdx, hF⟩
    have hP : P (params1KeyFlatVal S U V idx) := ⟨idx, hIdx, rfl⟩; simp [g, hP] at hF
  have hZeroR : ¬ (0 < 𝒟[sampleIndexRange (fgTotalIndexCount S) >>=
      fun idx => g (params1KeyFlatVal S U V idx)] {false}) :=
    mt (mem_support_iff_evalDist_singleton_pos _ false).mpr hNoFalseR
  rw [← evalDist_initParams1Key2Prob_map_bind S U V g false] at hZeroR
  have hNoFalseL : false ∉ support (initParams1Key2Prob S U V >>= fun pa2' => g (params2ToFlat S pa2')) :=
    mt (mem_support_iff_evalDist_singleton_pos _ false).mp hZeroR
  by_contra hNotP; apply hNoFalseL; rw [mem_support_bind_iff]; exact ⟨pa2, hpa, by simp [g]; exact hNotP⟩

private theorem simulateQ_primBaseImpl_unifGdhSign_bind {α β : Type} (P : Primitives)
    (rest : QueryImpl sigAndDdhSpec ProbComp) (m : ProbComp α) (f : α → OracleComp GdhSignSimSpec β) :
    simulateQ (primBaseImpl P + rest) (unifGdhSign m >>= f) =
      (m >>= fun a => simulateQ (primBaseImpl P + rest) (f a)) := by
  induction m using OracleComp.inductionOn with
  | pure a => change simulateQ (primBaseImpl P + rest) (pure a >>= f) = _; simp only [pure_bind]
  | query_bind q r ih =>
    change simulateQ (primBaseImpl P + rest)
        ((liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl (Sum.inl q))) >>= fun u => unifGdhSign (r u)) >>= f) =
      (liftM (OracleSpec.query q) >>= fun u => r u) >>= fun a => simulateQ (primBaseImpl P + rest) (f a)
    rw [bind_assoc, simulateQ_bind, simulateQ_query, bind_assoc]
    change (liftM (OracleSpec.query q) >>= fun u => simulateQ (primBaseImpl P + rest) (unifGdhSign (r u) >>= f)) = _
    congr 1; funext u; exact ih u

private theorem probComp_bind_congr_support {α β : Type} (m : ProbComp α)
    (f₁ f₂ : α → ProbComp β) (h : ∀ x ∈ support m, f₁ x = f₂ x) : (m >>= f₁) = (m >>= f₂) := by
  induction m using OracleComp.inductionOn with
  | pure a => change (pure a >>= f₁) = (pure a >>= f₂); simp only [pure_bind]; exact h a (by simp)
  | query_bind q r ih =>
    change ((liftM (OracleSpec.query q) >>= r) >>= f₁) = ((liftM (OracleSpec.query q) >>= r) >>= f₂)
    rw [bind_assoc, bind_assoc]; congr 1; funext u; refine ih u fun x hx => h x ?_
    change x ∈ support (liftM (OracleSpec.query q) >>= r); rw [mem_support_bind_iff]; exact ⟨u, by simp, hx⟩

private theorem evalDist_simulateQ_primBaseImpl_of_run_eq_param
    (P : Primitives) (S : Setup) (U V : Bytes) (rest : QueryImpl sigAndDdhSpec ProbComp)
    (kFinal : Bytes → ProbComp Bool) (m2 m1 : OracleComp GdhSignSimSpec Bytes)
    (run2 : params2Ty.denote → OracleComp GdhSignSimSpec Bytes)
    (run1 : paramsTy.denote → OracleComp GdhSignSimSpec Bytes)
    (hRun2 : m2 = (unifGdhSign (initParams1Key2Prob S U V) >>= run2))
    (hRun1 : m1 = (unifGdhSign (sampleIndexRange (fgTotalIndexCount S)) >>=
      fun idx => run1 (params1KeyFlatVal S U V idx)))
    (hAgree : ∀ pa2, InBoundsParams2 S pa2 → run2 pa2 = run1 (params2ToFlat S pa2)) :
    𝒟[simulateQ (primBaseImpl P + rest) m2 >>= kFinal] = 𝒟[simulateQ (primBaseImpl P + rest) m1 >>= kFinal] := by
  rw [hRun2, hRun1, simulateQ_primBaseImpl_unifGdhSign_bind, simulateQ_primBaseImpl_unifGdhSign_bind,
    bind_assoc, bind_assoc]
  let g : paramsTy.denote → ProbComp Bool := fun pa => simulateQ (primBaseImpl P + rest) (run1 pa) >>= kFinal
  rw [probComp_bind_congr_support (initParams1Key2Prob S U V) _ (fun pa2 => g (params2ToFlat S pa2))
    fun pa2 hMem => by dsimp only [g]; rw [hAgree pa2 (mem_support_initParams1Key2Prob_inBounds S U V hMem)]]
  exact evalDist_initParams1Key2Prob_map_bind_measure S U V g

private theorem evalDist_gapDhWithSignExp_of_run_eq_param
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (A2 A1 : GapDhWithSignAdv)
    (run2 : Bytes → Bytes → params2Ty.denote → OracleComp GdhSignSimSpec Bytes)
    (run1 : Bytes → Bytes → paramsTy.denote → OracleComp GdhSignSimSpec Bytes)
    (hRun2 : ∀ U V, A2.run U V = (unifGdhSign (initParams1Key2Prob S U V) >>= run2 U V))
    (hRun1 : ∀ U V, A1.run U V =
      (unifGdhSign (sampleIndexRange (fgTotalIndexCount S)) >>= fun idx => run1 U V (params1KeyFlatVal S U V idx)))
    (hAgree : ∀ U V pa2, InBoundsParams2 S pa2 → run2 U V pa2 = run1 U V (params2ToFlat S pa2)) :
    𝒟[gapDhWithSignExp P isValidDhTriple pow8 A2] = 𝒟[gapDhWithSignExp P isValidDhTriple pow8 A1] := by
  let : MeasurableSpace Bytes := ⊤; unfold gapDhWithSignExp
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]; congr 1; funext u
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]; congr 1; funext v; dsimp only
  exact evalDist_simulateQ_primBaseImpl_of_run_eq_param P S (P.x25519Base u) (P.x25519Base v) _ _ _ _
    (run2 (P.x25519Base u) (P.x25519Base v)) (run1 (P.x25519Base u) (P.x25519Base v))
    (hRun2 (P.x25519Base u) (P.x25519Base v)) (hRun1 (P.x25519Base u) (P.x25519Base v))
    (hAgree (P.x25519Base u) (P.x25519Base v))

/-! ## State Projection Homomorphism -/

private def sigSlack (S : Setup) (K : Nat) : Nat := min S.N_spk_tot S.N_recv - min K (min S.N_spk_tot S.N_recv)

private def mapState1Key2 (S : Setup) (K : Nat) (s2 : gdh1KeyState2Ty.denote) : gdh1KeyStateTy.denote :=
  ((params2ToFlat S s2.1.1, s2.1.2), s2.2 + sigSlack S K)

private def Inv1Key2 (S : Setup) (K k : Nat) (s2 : gdh1KeyState2Ty.denote) : Prop :=
  InBoundsParams2 S s2.1.1 ∧ (sigSlack S K = 0 ∨ k ≤ s2.2)

private theorem Inv1Key2_mono {S : Setup} {K k : Nat} {s2 : gdh1KeyState2Ty.denote}
    (h : Inv1Key2 S K (k + 1) s2) : Inv1Key2 S K k s2 := ⟨h.1, h.2.imp id fun _ => by omega⟩

private theorem Inv1Key2_init {S : Setup} (K : Nat) {pa2 : params2Ty.denote}
    (hB : InBoundsParams2 S pa2) (sm : simTy.denote) :
    Inv1Key2 S K K ((pa2, sm), min K (min S.N_spk_tot S.N_recv)) := by
  refine ⟨hB, ?_⟩; unfold sigSlack; by_cases hle : min S.N_spk_tot S.N_recv ≤ K <;> [left; right] <;> omega

private theorem mapState1Key2_init (S : Setup) (K : Nat) (pa2 : params2Ty.denote) (secb : Bool) :
    mapState1Key2 S K ((pa2, simStateToVal (FgKeyInd1KeySimState.empty S secb).sim),
        min K (min S.N_spk_tot S.N_recv)) =
      sim1KeyStateToVal (params2ToFlat S pa2) (FgKeyInd1KeySimState.empty S secb) := by
  unfold mapState1Key2 sim1KeyStateToVal FgKeyInd1KeySimState.empty
  refine Prod.ext rfl ?_
  change min K (min S.N_spk_tot S.N_recv) + sigSlack S K = min S.N_spk_tot S.N_recv
  unfold sigSlack
  omega

private theorem nat_mul_add_eq_iff {N u₁ j₁ u₂ j₂ : ℕ} (hj₁ : j₁ < N) (hj₂ : j₂ < N) :
    u₁ * N + j₁ = u₂ * N + j₂ ↔ u₁ = u₂ ∧ j₁ = j₂ := by
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
  have hu : u₁ = u₂ := by
    rcases lt_trichotomy u₁ u₂ with hlt | rfl | hgt
    · have := Nat.mul_le_mul_right N hlt; nlinarith
    · rfl
    · have := Nat.mul_le_mul_right N hgt; nlinarith
  subst hu; exact ⟨rfl, by omega⟩

private theorem spkTarget_match_eq (S : Setup) (pa2 : params2Ty.denote)
    (hB : InBoundsParams2 S pa2) (u : Fin S.N_id) (j : Fin S.N_recv) :
    (match pa2.2.2.2.2.2.2.1 with | none => false | some sp => decide (u.val = sp.1) && decide (j.val = sp.2)) =
      decide (Nat.min S.N_recv S.N_spk_tot * u.val + j.val = (params2ToFlat S pa2).2.2.2.2.2.2.2.1) := by
  simp only [Nat.mul_comm (Nat.min S.N_recv S.N_spk_tot) u.val]
  have hIdPos : 0 < S.N_id := Nat.pos_of_ne_zero (by have := u.isLt; omega)
  have hSpkPos : 0 < S.N_spk_tot := Nat.mul_pos hIdPos (Nat.pos_of_ne_zero (by have := j.isLt; omega))
  have hTotNe : fgTotalIndexCount S ≠ 0 := by unfold fgTotalIndexCount; have := Nat.mul_pos hIdPos hSpkPos; omega
  have hMinR : Nat.min S.N_recv S.N_spk_tot = S.N_recv :=
    Nat.min_eq_left (by unfold Setup.N_spk_tot; nlinarith [u.isLt])
  rcases pa2 with ⟨U, V, Up, pt, df, et, st, om, ot, md⟩; have hSt := (hB.resolve_left hTotNe).2.2.1
  cases st with
  | none =>
    have hlt : u.val * S.N_recv + j.val < S.N_spk_tot := by
      unfold Setup.N_spk_tot; have := Nat.mul_le_mul_right S.N_recv u.isLt; nlinarith [j.isLt]
    simp only [params2ToFlat, hMinR, Nat.ne_of_lt hlt, decide_false]
  | some sp =>
    rcases sp with ⟨uT, jT⟩; obtain ⟨_, hjT⟩ := hSt uT jT rfl; simp only [params2ToFlat, hMinR]
    by_cases hEq : u.val = uT ∧ j.val = jT
    · rcases hEq with ⟨rfl, rfl⟩; simp
    · have hNe : u.val * S.N_recv + j.val ≠ uT * S.N_recv + jT := fun h => hEq ((nat_mul_add_eq_iff j.isLt hjT).mp h)
      simp only [hNe, decide_false, Bool.and_eq_false_iff, decide_eq_false_iff_not]; tauto

private theorem callGdhHandle2_eval_map_eq (S : Setup) (K k : Nat) {Δ : List PT}
    (st2 : Var Δ gdh1KeyState2Ty) (q2 : Var Δ keyIndQueryTy) (env2 : Env Δ)
    {Δ' : List PT} (st1 : Var Δ' gdh1KeyStateTy) (q1 : Var Δ' keyIndQueryTy) (env1 : Env Δ')
    (s2 : gdh1KeyState2Ty.denote) (gq : KeyIndQuery S) (hInv : Inv1Key2 S K (k + 1) s2)
    (hs2 : env2.get st2 = s2) (hq2 : env2.get q2 = (keyIndCodec S).qenc gq)
    (hs1 : env1.get st1 = mapState1Key2 S K s2) (hq1 : env1.get q1 = (keyIndCodec S).qenc gq) :
    (fun r : keyIndRespTy.denote × gdh1KeyState2Ty.denote => (r.1, mapState1Key2 S K r.2)) <$>
        (callGdhHandle2 S K st2 q2).eval env2 = (callGdhHandle S K st1 q1).eval env1 ∧
    ∀ r ∈ support ((callGdhHandle2 S K st2 q2).eval env2), Inv1Key2 S K k r.2 := by
  rcases s2 with ⟨⟨pa2, sm⟩, sigB2⟩; obtain ⟨hMap, hSup⟩ := gdhHandle2_eval_map_eq S K pa2 hInv.1 sm gq
  unfold callGdhHandle2 callGdhHandle
  simp only [letV_eval, bindV, Comp.eval, v, Expr.eval, Env.get, Ext.wk,
    renameComp_eval, pullEnv_twoVarRen, liftGdhComp_eval, hs2, hq2, hs1, hq1, mapState1Key2]
  constructor
  · have hL := congrArg liftGdhToSign hMap; rw [liftGdhToSign_map] at hL; rw [← hL]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
  · intro r hr; rw [mem_support_bind_iff] at hr; rcases hr with ⟨res, hres, hrEq⟩
    simp only [support_pure, Set.mem_singleton_iff] at hrEq; subst hrEq
    have hpa : res.2.1 = pa2 := hSup res (mem_support_liftGdhToSign hres)
    exact ⟨by dsimp only; rw [hpa]; exact hInv.1, hInv.2.imp id fun _ => by dsimp only; omega⟩

private theorem initPrin1Key2B_eval_map_eq (S : Setup) (K k : Nat)
    (s2 : gdh1KeyState2Ty.denote) (u : Fin S.N_id) (hInv : Inv1Key2 S K (k + 1) s2) :
    let env2 : Env [.nat, gdh1KeyState2Ty, keyIndQueryTy] :=
      .cons u.val (.cons s2 (.cons ((keyIndCodec S).qenc (.initPrin u)) .nil))
    let env1 : Env [.nat, gdh1KeyStateTy, keyIndQueryTy] :=
      .cons u.val (.cons (mapState1Key2 S K s2) (.cons ((keyIndCodec S).qenc (.initPrin u)) .nil))
    (fun r : keyIndRespTy.denote × gdh1KeyState2Ty.denote => (r.1, mapState1Key2 S K r.2)) <$>
        (initPrin1Key2B K (Γ₁ := [gdh1KeyState2Ty, keyIndQueryTy])
          (Γ₂ := [.nat, gdh1KeyState2Ty, keyIndQueryTy]) .zero .zero).eval env2 =
      (initPrin1KeyB K (Γ₁ := [gdh1KeyStateTy, keyIndQueryTy])
        (Γ₂ := [.nat, gdh1KeyStateTy, keyIndQueryTy]) .zero .zero).eval env1 ∧
    ∀ r ∈ support ((initPrin1Key2B K (Γ₁ := [gdh1KeyState2Ty, keyIndQueryTy])
        (Γ₂ := [.nat, gdh1KeyState2Ty, keyIndQueryTy]) .zero .zero).eval env2),
      Inv1Key2 S K k r.2 := by
  rcases s2 with ⟨⟨pa2, sm⟩, sigB2⟩; dsimp only; unfold initPrin1Key2B initPrin1KeyB
  simp only [letV_eval, bindV, Comp.eval, smBase, v, Expr.eval, Env.get, Ext.wk, mapState1Key2]
  let qEnc : keyIndQueryTy.denote := (keyIndCodec S).qenc (.initPrin u)
  let e2 : Env [keyIndStateTy, simTy, params2Ty, .nat, gdh1KeyState2Ty, keyIndQueryTy] :=
    Env.cons sm.1 (.cons sm (.cons pa2 (.cons u.val (.cons ((pa2, sm), sigB2) (.cons qEnc .nil)))))
  let e1 : Env [keyIndStateTy, simTy, paramsTy, .nat, gdh1KeyStateTy, keyIndQueryTy] :=
    Env.cons sm.1 (.cons sm (.cons (params2ToFlat S pa2)
      (.cons u.val (.cons ((params2ToFlat S pa2, sm), sigB2 + sigSlack S K) (.cons qEnc .nil)))))
  have hcAny : (eAny K (stPrin (.var .zero)) fun p =>
      natEq (.fst (.var p)) (.var (.succ (.succ (.succ (.succ .zero)))))).eval e2 =
      (eAny K (stPrin (.var .zero)) fun p =>
        natEq (.fst (.var p)) (.var (.succ (.succ (.succ (.succ .zero)))))).eval e1 := rfl
  dsimp only [e2, e1, qEnc] at hcAny
  change _ ∧ _; rw [← hcAny]
  cases (eAny K (stPrin (.var .zero)) fun p =>
      natEq (.fst (.var p)) (.var (.succ (.succ (.succ (.succ .zero)))))).eval
      (Env.cons (t := keyIndStateTy) sm.1
        (Env.cons (t := simTy) sm
          (Env.cons (t := params2Ty) pa2
            (Env.cons (t := .nat) u.val
              (Env.cons (t := gdh1KeyState2Ty) ((pa2, sm), sigB2)
                (Env.cons (t := keyIndQueryTy) ((keyIndCodec S).qenc (.initPrin u)) .nil))))))
  · have hPT : (eCaseOpt (pa2PrinTarget (.var (.succ (.succ .zero)))) (.bool false) fun uT =>
        natEq (.var (.succ (.succ (.succ (.succ .zero))))) (.var uT)).eval e2 =
        (Expr.and (paPrinFlag (.var (.succ (.succ .zero))))
          (natEq (.var (.succ (.succ (.succ .zero)))) (paPrinIdx (.var (.succ (.succ .zero)))))).eval e1 := by
      simp only [e2, e1, eCaseOpt, pa2PrinTarget, paPrinFlag, paPrinIdx, natEq_eval, Expr.eval,
        Env.get]
      rcases pa2 with ⟨_, _, _, _ | uT, _, _, _, _, _, _⟩ <;> simp [params2ToFlat]
    dsimp only [e2, e1, qEnc] at hPT
    have hUp : pa2.2.2.1 = (params2ToFlat S pa2).2.2.1 := by rcases pa2 with ⟨_, _, _, _, _, _, _, _, _, _⟩; rfl
    simp only [Bool.false_eq_true, ↓reduceIte, hPT, liftGdhComp_eval, gPrim_eval,
      map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine ⟨_root_.bind_congr fun sk0 => _root_.bind_congr fun pk0 => by
      simp [pa2Up, paUp, litB, peMk, rInitPrin, stUpd, stMk, smUpd, smMk, smFgL, smRaw, smLog, smPows,
        stSecb, stPrin, stSpks, stOpks, stResps, stUsedO, stUsedN, stSess, stAdv, stRo, stKyb,
        Expr.eval, hUp], fun r hr => ?_⟩
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, _, _, rfl⟩; exact Inv1Key2_mono hInv
  · simp only [↓reduceIte, map_pure, support_pure, Set.mem_singleton_iff]
    exact ⟨by simp [rNone, Expr.eval], fun _ hr => hr ▸ Inv1Key2_mono hInv⟩

private theorem genSpk1Key2B_eval_map_eq (S : Setup) (K k : Nat)
    (s2 : gdh1KeyState2Ty.denote) (u : Fin S.N_id) (j : Fin S.N_recv)
    {T1 T2 : PT} (r1Val : T1.denote) (r2Val : T2.denote)
    (hInv : Inv1Key2 S K (k + 1) s2) :
    let qEnc : keyIndQueryTy.denote := (keyIndCodec S).qenc (.genSPK u j)
    let env2 : Env [.prod .nat .nat, T2, T1, gdh1KeyState2Ty, keyIndQueryTy] :=
      Env.cons (u.val, j.val) (.cons r2Val (.cons r1Val (.cons s2 (.cons qEnc .nil))))
    let env1 : Env [.prod .nat .nat, T2, T1, gdh1KeyStateTy, keyIndQueryTy] :=
      Env.cons (u.val, j.val) (.cons r2Val (.cons r1Val (.cons (mapState1Key2 S K s2) (.cons qEnc .nil))))
    (fun r : keyIndRespTy.denote × gdh1KeyState2Ty.denote => (r.1, mapState1Key2 S K r.2)) <$>
        (genSpk1Key2B S K (.succ (.succ (.succ .zero))) (.succ (.succ (.succ (.succ .zero)))) .zero).eval env2 =
      (genSpk1KeyB S K (.succ (.succ (.succ .zero))) (.succ (.succ (.succ (.succ .zero)))) .zero).eval env1 ∧
    ∀ r ∈ support ((genSpk1Key2B S K (.succ (.succ (.succ .zero)))
        (.succ (.succ (.succ (.succ .zero)))) .zero).eval env2), Inv1Key2 S K k r.2 := by
  dsimp only; unfold genSpk1Key2B genSpk1KeyB
  set qEnc : keyIndQueryTy.denote := (keyIndCodec S).qenc (.genSPK u j) with hqEnc
  let Δ2 : List PT := [.prod .nat .nat, T2, T1, gdh1KeyState2Ty, keyIndQueryTy]
  let Δ1 : List PT := [.prod .nat .nat, T2, T1, gdh1KeyStateTy, keyIndQueryTy]
  let base2 : Env Δ2 := Env.cons (u.val, j.val) (.cons r2Val (.cons r1Val (.cons s2 (.cons qEnc .nil))))
  let base1 : Env Δ1 := Env.cons (u.val, j.val) (.cons r2Val (.cons r1Val (.cons (mapState1Key2 S K s2) (.cons qEnc .nil))))
  let st2 : Var Δ2 gdh1KeyState2Ty := .succ (.succ (.succ .zero))
  let x2 : Var Δ2 (.prod .nat .nat) := .zero
  let st1 : Var Δ1 gdh1KeyStateTy := .succ (.succ (.succ .zero))
  let x1 : Var Δ1 (.prod .nat .nat) := .zero
  have hOuter : (eCaseOpt (pa2PrinTarget (.fst (.fst (v st2))))
      (.bool false) fun uT => natEq (.fst (v x2)) (v uT)).eval base2 =
      (Expr.and (paPrinFlag (.fst (.fst (v st1))))
        (natEq (.fst (v x1)) (paPrinIdx (.fst (.fst (v st1)))))).eval base1 := by
    rcases s2 with ⟨⟨pa2, sm⟩, sigB2⟩
    simp only [base2, base1, st2, x2, st1, x1, eCaseOpt, pa2PrinTarget, paPrinFlag, paPrinIdx,
      natEq_eval, v, Expr.eval, Env.get, Ext.wk, mapState1Key2]
    rcases pa2 with ⟨_, _, _, _ | uT, _, _, _, _, _, _⟩ <;> simp [params2ToFlat]
  dsimp only [st2, x2, base2, st1, x1, base1] at hOuter
  simp only [Comp.eval]; rw [hOuter]
  by_cases hT : (Expr.and (paPrinFlag (.fst (.fst (v st1))))
      (natEq (.fst (v x1)) (paPrinIdx (.fst (.fst (v st1)))))).eval base1 = true
  · clear_value qEnc; clear hqEnc
    dsimp only [st1, x1, base1] at hT
    simp only [hT, ↓reduceIte]; rcases s2 with ⟨⟨pa2, sm⟩, sigB2⟩
    simp only [letV_eval, caseOptV, bindV, Comp.eval, smBase, v, Expr.eval, Env.get, Ext.wk, mapState1Key2]
    let mid2 : Env [.nat, keyIndStateTy, simTy, params2Ty, .prod .nat .nat, T2, T1, gdh1KeyState2Ty, keyIndQueryTy] :=
      Env.cons sigB2 (.cons sm.1 (.cons sm (.cons pa2 base2)))
    let mid1 : Env [.nat, keyIndStateTy, simTy, paramsTy, .prod .nat .nat, T2, T1, gdh1KeyStateTy, keyIndQueryTy] :=
      Env.cons (sigB2 + sigSlack S K) (.cons sm.1 (.cons sm (.cons (params2ToFlat S pa2) base1)))
    have hAnyEq : (eAny K (stSpks (.var (.succ .zero))) fun p =>
        nat2Eq (.fst (.var p)) (.var (.succ (.succ (.succ (.succ (.succ .zero))))))).eval mid2 =
        (eAny K (stSpks (.var (.succ .zero))) fun p =>
          nat2Eq (.fst (.var p)) (.var (.succ (.succ (.succ (.succ (.succ .zero))))))).eval mid1 := rfl
    dsimp only [mid2, mid1, base2, base1, mapState1Key2] at hAnyEq
    rw [← hAnyEq]
    cases (eAny K (stSpks (.var (.succ .zero))) fun p =>
        nat2Eq (.fst (.var p)) (.var (.succ (.succ (.succ (.succ (.succ .zero))))))).eval
        (Env.cons (t := .nat) sigB2
          (Env.cons (t := keyIndStateTy) sm.1
            (Env.cons (t := simTy) sm
              (Env.cons (t := params2Ty) pa2
                (Env.cons (t := .prod .nat .nat) (u.val, j.val)
                  (Env.cons (t := T2) r2Val
                    (Env.cons (t := T1) r1Val
                      (Env.cons (t := gdh1KeyState2Ty) ((pa2, sm), sigB2)
                        (Env.cons (t := keyIndQueryTy) qEnc .nil)))))))))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hFindEq : (eFind K (stPrin (.var (.succ .zero))) fun p =>
          natEq (.fst (.var p)) (.fst (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))).eval mid2 =
          (eFind K (stPrin (.var (.succ .zero))) fun p =>
            natEq (.fst (.var p)) (.fst (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))).eval mid1 := rfl
      dsimp only [mid2, mid1, base2, base1, mapState1Key2] at hFindEq
      rw [← hFindEq]
      cases (eFind K (stPrin (.var (.succ .zero))) fun p =>
          natEq (.fst (.var p)) (.fst (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))).eval
          (Env.cons (t := .nat) sigB2
            (Env.cons (t := keyIndStateTy) sm.1
              (Env.cons (t := simTy) sm
                (Env.cons (t := params2Ty) pa2
                  (Env.cons (t := .prod .nat .nat) (u.val, j.val)
                    (Env.cons (t := T2) r2Val
                      (Env.cons (t := T1) r1Val
                        (Env.cons (t := gdh1KeyState2Ty) ((pa2, sm), sigB2)
                          (Env.cons (t := keyIndQueryTy) qEnc .nil))))))))) with
      | none =>
        simp only [map_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨by simp [rNone, Expr.eval], fun _ hr => hr ▸ Inv1Key2_mono hInv⟩
      | some ue =>
        simp only [natEq, Expr.eval, Env.get]
        have hSigZero : decide (sigB2 = 0) = decide (sigB2 + sigSlack S K = 0) := by
          rcases hInv.2 with hSl0 | hLe
          · rw [hSl0, Nat.add_zero]
          · dsimp only at hLe
            have hPos : sigB2 ≠ 0 := fun h0 => Nat.not_succ_le_zero k (h0 ▸ hLe)
            simp [hPos]
        rw [hSigZero]
        by_cases hZ : decide (sigB2 + sigSlack S K = 0) = true
        · simp only [hZ, ↓reduceIte, map_pure, support_pure, Set.mem_singleton_iff]
          have hSl0 : sigSlack S K = 0 :=
            Nat.eq_zero_of_add_eq_zero_left (of_decide_eq_true hZ)
          exact ⟨by simp [rNone, Expr.eval], fun _ hr => by subst hr; exact ⟨hInv.1, Or.inl hSl0⟩⟩
        · simp only [hZ, Bool.false_eq_true, ↓reduceIte]
          have hBeq : ∀ a b : Nat, (a == b) = decide (a = b) := fun a b => by
            cases h : (a == b) <;> simp_all
          have hSpkT : (eCaseOpt (pa2SpkTarget (.var (.succ (.succ (.succ (.succ .zero)))))) (.bool false)
              fun sp => nat2Eq (.var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))) (.var sp)).eval
              (.cons ue mid2) =
              (natEq
                (spkFlatIdxE S
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))
                  (.snd (.var (.succ (.succ (.succ (.succ (.succ .zero))))))))
                (paSpkIdx (.var (.succ (.succ (.succ (.succ .zero))))))).eval (.cons ue mid1) := by
            simp only [mid2, mid1, base2, base1, eCaseOpt, pa2SpkTarget, paSpkIdx, spkFlatIdxE, mulRight,
              nat2Eq, natEq_eval, Expr.eval, Env.get, hBeq]
            have hM := spkTarget_match_eq S pa2 hInv.1 u j
            rcases pa2 with ⟨_, _, _, _, _, _, _ | sp, _, _, _⟩ <;> exact hM
          dsimp only [mid2, mid1, base2, base1, mapState1Key2] at hSpkT
          have hV : pa2.2.1 = (params2ToFlat S pa2).2.1 := by rcases pa2 with ⟨_, _, _, _, _, _, _, _, _, _⟩; rfl
          rw [hSpkT]
          simp only [liftGdhComp_eval, gPrim_eval, sigChalQ_dsl_eval]
          constructor
          · simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
            refine _root_.bind_congr fun spkSkRaw => _root_.bind_congr fun spkPkRaw => ?_
            simp only [pa2V, paV, litB, encEC, consB, Expr.eval, Env.get, hV]
            refine _root_.bind_congr fun _ => _root_.bind_congr fun _ =>
              _root_.bind_congr fun _ => ?_
            simp only [encKEM, consB, Expr.eval]
            refine _root_.bind_congr fun _ => ?_
            have hSub : (sigB2 : Nat) - 1 + sigSlack S K = (sigB2 : Nat) + sigSlack S K - 1 := by
              rcases hInv.2 with hSl0 | hLe
              · rw [hSl0, Nat.add_zero, Nat.add_zero]
              · dsimp only at hLe
                exact (Nat.sub_add_comm (Nat.le_trans (Nat.le_add_left 1 k) hLe)).symm
            simp [u32OfNat, sbMk, buMk, peIkAPk, rBundle,
              stUpd, stMk, smUpd, smMk, smFgL, smRaw, smLog, smPows,
              stSecb, stPrin, stSpks, stOpks, stResps, stUsedO, stUsedN, stSess, stAdv,
              stRo, stKyb, Expr.eval, hSub]
            rfl
          · intro r hr
            simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
            rcases hr with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
            exact ⟨hInv.1, hInv.2.imp id fun _ => by dsimp only; omega⟩
    · simp only [↓reduceIte, map_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨by simp [rNone, Expr.eval], fun _ hr => hr ▸ Inv1Key2_mono hInv⟩
  · dsimp only [st1, x1, base1] at hT
    simp only [hT, Bool.false_eq_true, ↓reduceIte]
    exact callGdhHandle2_eval_map_eq S K k st2 (.succ (.succ (.succ (.succ .zero)))) base2
      st1 (.succ (.succ (.succ (.succ .zero)))) base1 s2 (.genSPK u j) hInv rfl hqEnc rfl hqEnc

private theorem gdh1KeyHandle2_eval_map_eq (S : Setup) (K k : Nat)
    (s2 : gdh1KeyState2Ty.denote) (gq : KeyIndQuery S) (hInv : Inv1Key2 S K (k + 1) s2) :
    (fun r : keyIndRespTy.denote × gdh1KeyState2Ty.denote => (r.1, mapState1Key2 S K r.2)) <$>
        (gdh1KeyHandle2 S K).eval (.cons s2 (.cons ((keyIndCodec S).qenc gq) .nil)) =
      (gdh1KeyHandle S K).eval (.cons (mapState1Key2 S K s2) (.cons ((keyIndCodec S).qenc gq) .nil)) ∧
    ∀ r ∈ support ((gdh1KeyHandle2 S K).eval (.cons s2 (.cons ((keyIndCodec S).qenc gq) .nil))),
      Inv1Key2 S K k r.2 := by
  cases gq with
  | initPrin u =>
    simpa only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk] using initPrin1Key2B_eval_map_eq S K k s2 u hInv
  | genSPK u j =>
    simpa only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk] using genSpk1Key2B_eval_map_eq S K k s2 u j _ _ hInv
  | corruptIK u =>
    simp only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk]
    exact callGdhHandle2_eval_map_eq S K k _ _ _ _ _ _ s2 (.corruptIK u) hInv rfl rfl rfl rfl
  | genOPK u j o =>
    simp only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk]
    exact callGdhHandle2_eval_map_eq S K k _ _ _ _ _ _ s2 (.genOPK u j o) hInv rfl rfl rfl rfl
  | initiateOPK u i bdl =>
    simp only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk]
    exact callGdhHandle2_eval_map_eq S K k _ _ _ _ _ _ s2 (.initiateOPK u i bdl) hInv rfl rfl rfl rfl
  | initiateNoOPK u i bdl =>
    simp only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk]
    exact callGdhHandle2_eval_map_eq S K k _ _ _ _ _ _ s2 (.initiateNoOPK u i bdl) hInv rfl rfl rfl rfl
  | acceptOPK u j o hdr =>
    simp only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk]
    exact callGdhHandle2_eval_map_eq S K k _ _ _ _ _ _ s2 (.acceptOPK u j o hdr) hInv rfl rfl rfl rfl
  | acceptNoOPK u j l hdr =>
    simp only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk]
    exact callGdhHandle2_eval_map_eq S K k _ _ _ _ _ _ s2 (.acceptNoOPK u j l hdr) hInv rfl rfl rfl rfl
  | testSession sid =>
    simp only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk]
    exact callGdhHandle2_eval_map_eq S K k _ _ _ _ _ _ s2 (.testSession sid) hInv rfl rfl rfl rfl
  | roQuery sec =>
    simp only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk]
    exact callGdhHandle2_eval_map_eq S K k _ _ _ _ _ _ s2 (.roQuery sec) hInv rfl rfl rfl rfl
  | revealDhSecrets =>
    simp only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk]
    exact callGdhHandle2_eval_map_eq S K k _ _ _ _ _ _ s2 .revealDhSecrets hInv rfl rfl rfl rfl
  | revealSessionKey sid =>
    simp only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk]
    exact callGdhHandle2_eval_map_eq S K k _ _ _ _ _ _ s2 (.revealSessionKey sid) hInv rfl rfl rfl rfl
  | registerKey sk =>
    simp only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk]
    exact callGdhHandle2_eval_map_eq S K k _ _ _ _ _ _ s2 (.registerKey sk) hInv rfl rfl rfl rfl
  | revealSpkSk u j =>
    simp only [gdh1KeyHandle2, gdh1KeyHandle, keyIndCodec, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get, Ext.wk]
    exact callGdhHandle2_eval_map_eq S K k _ _ _ _ _ _ s2 (.revealSpkSk u j) hInv rfl rfl rfl rfl

private theorem gdh1KeyFinish2_eval_eq (S : Setup) (K : Nat) (s2 : gdh1KeyState2Ty.denote) (b : Bool) :
    (gdh1KeyFinish2 S K).eval (.cons s2 (.cons b .nil)) =
      (gdh1KeyFinish S K).eval (.cons (mapState1Key2 S K s2) (.cons b .nil)) := by
  rcases s2 with ⟨⟨pa2, sm⟩, sigB2⟩
  simp only [gdh1KeyFinish2, gdh1KeyFinish, mapState1Key2, letV_eval, renameComp_eval,
    pullEnv_twoVarRen, liftGdhComp_eval, v, Expr.eval, Env.get, Ext.wk, gdhFinish2_eval_eq S K pa2 sm b]

private def runFrom1Key2 (S : Setup) (K : Nat) (A : OracleComp (unifSpec + keyIndSpec S) Bool)
    (x0 : gdh1KeyState2Ty.denote) : OracleComp GdhSignSimSpec Bytes := do
  let (b, s') ← (simulateQ (handlerImpl (C := keyIndCodec S) (gdh1KeyHandle2 S K)) A).run x0
  (gdh1KeyFinish2 S K).eval (.cons s' (.cons b .nil))

private theorem simulateQ_gdh1KeyHandle2_bind_eq {α : Type} (S : Setup) (K : Nat)
    (mx : OracleComp (unifSpec + keyIndSpec S) α) (qRem : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) qRem)
    (s2 : gdh1KeyState2Ty.denote) (hInv : Inv1Key2 S K qRem s2)
    (f2 : α × gdh1KeyState2Ty.denote → OracleComp GdhSignSimSpec Bytes)
    (f1 : α × gdh1KeyStateTy.denote → OracleComp GdhSignSimSpec Bytes)
    (hf : ∀ a s2', f2 (a, s2') = f1 (a, mapState1Key2 S K s2')) :
    ((simulateQ (handlerImpl (C := keyIndCodec S) (gdh1KeyHandle2 S K)) mx).run s2 >>= f2) =
      ((simulateQ (handlerImpl (C := keyIndCodec S) (gdh1KeyHandle S K)) mx).run (mapState1Key2 S K s2) >>= f1) := by
  induction mx using OracleComp.inductionOn generalizing qRem s2 with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact hf a s2
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hMx; rcases q with uq | gq
    · rcases hMx with ⟨_, hCont⟩
      simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte] at hCont
      rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
      change (((pqSigAndDdhIface.fwdU uq >>= fun u => pure (u, s2)) >>= fun x =>
          (simulateQ (handlerImpl (C := keyIndCodec S) (gdh1KeyHandle2 S K)) (k x.1)).run x.2) >>= f2) =
        (((pqSigAndDdhIface.fwdU uq >>= fun u => pure (u, mapState1Key2 S K s2)) >>= fun x =>
          (simulateQ (handlerImpl (C := keyIndCodec S) (gdh1KeyHandle S K)) (k x.1)).run x.2) >>= f1)
      simp only [bind_assoc, pure_bind]; exact _root_.bind_congr fun u => ih u qRem (hCont u) s2 hInv
    · rcases hMx with ⟨hFirst, hCont⟩
      have hPos : 0 < qRem := hFirst.elim (fun hAbs => absurd rfl hAbs) id
      obtain ⟨n, rfl⟩ : ∃ n, qRem = n + 1 := ⟨qRem - 1, by omega⟩
      simp only [Sum.isRight_inr, ↓reduceIte, Nat.add_sub_cancel] at hCont
      obtain ⟨hStep, hPres⟩ := gdh1KeyHandle2_eval_map_eq S K n s2 gq hInv
      rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
      change (((do let p ← (gdh1KeyHandle2 S K).eval (.cons s2 (.cons ((keyIndCodec S).qenc gq) .nil))
                   pure ((keyIndCodec S).rdec gq p.1, p.2)) >>= fun x =>
          (simulateQ (handlerImpl (C := keyIndCodec S) (gdh1KeyHandle2 S K)) (k x.1)).run x.2) >>= f2) =
        (((do let p ← (gdh1KeyHandle S K).eval (.cons (mapState1Key2 S K s2) (.cons ((keyIndCodec S).qenc gq) .nil))
              pure ((keyIndCodec S).rdec gq p.1, p.2)) >>= fun x =>
          (simulateQ (handlerImpl (C := keyIndCodec S) (gdh1KeyHandle S K)) (k x.1)).run x.2) >>= f1)
      rw [← hStep]; simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      exact bind_congr_of_forall_mem_support _ fun r hr =>
        ih ((keyIndCodec S).rdec gq r.1) n (hCont _) r.2 (hPres r hr)

private theorem runFrom1Key2_eq_runFrom1Key (S : Setup) (K : Nat)
    (pa2 : params2Ty.denote) (hB : InBoundsParams2 S pa2) (A : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : IsQueryBoundP A (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) K) (secb : Bool) :
    runFrom1Key2 S K A ((pa2, simStateToVal (FgKeyInd1KeySimState.empty S secb).sim),
        min K (min S.N_spk_tot S.N_recv)) =
      runFrom1Key S K A (sim1KeyStateToVal (params2ToFlat S pa2) (FgKeyInd1KeySimState.empty S secb)) := by
  unfold runFrom1Key2 runFrom1Key; rw [← mapState1Key2_init S K pa2 secb]
  exact simulateQ_gdh1KeyHandle2_bind_eq S K A K hA _ (Inv1Key2_init K hB _)
    (fun p => (gdh1KeyFinish2 S K).eval (.cons p.2 (.cons p.1 .nil)))
    (fun p => (gdh1KeyFinish S K).eval (.cons p.2 (.cons p.1 .nil)))
    (fun a s2' => gdh1KeyFinish2_eval_eq S K s2' a)

private theorem fgKeyInd1KeyGapDh2Prog_eval_runFrom1Key2 (S : Setup) (K : Nat)
    (A : OracleComp (unifSpec + keyIndSpec S) Bool) (U V : Bytes) :
    (fgKeyInd1KeyGapDh2Prog S K).eval (fun _ => A) (U, V) =
      (do let pa2 ← unifGdhSign (initParams1Key2Prob S U V); let secb ← unifGdhSign ($ᵗ Bool)
          runFrom1Key2 S K A ((pa2, simStateToVal (FgKeyInd1KeySimState.empty S secb).sim),
            min K (min S.N_spk_tot S.N_recv))) := by
  simp only [CostedReduction.eval, fgKeyInd1KeyGapDh2Prog, initAdv4_1Key2, initAdv4_1Key2Base,
    bindV, letV_eval, Comp.eval, liftGdhComp_eval, gPrim_eval, sBool_eval,
    emptySimE_eval (S := S), initParams1Key2C_eval, v, Expr.eval, Env.get, Ext.wk,
    liftGdhToSign_bind, liftGdhToSign_pure, unifGdhSign, unifGdh,
    FgGapDh_embedPrim_eq, FgGapDh_embedUnif_eq, bind_assoc, pure_bind]
  rfl

/-! ## Query Transfer and Distributional Equivalence -/

/-- Transfers any `IsQueryBoundP` bound (ignoring `unifSpec` draws) from flat-index runs in the
support of `sampleIndexRange (fgTotalIndexCount S)` to `(fgKeyInd1KeyGapDh2Prog S K).eval`. -/
theorem fgKeyInd1KeyGapDh2Prog_transfer_queryBound (S : Setup) (K : Nat)
    (A : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : IsQueryBoundP A (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) K)
    (U V : Bytes) (p : _ → Prop) [DecidablePred p]
    (hpUnif : ∀ n : ℕ, ¬ p (Sum.inl (Sum.inl n))) (B : Nat)
    (hFlat : ∀ idx ∈ support (unifGdhSign (sampleIndexRange (fgTotalIndexCount S))),
      IsQueryBoundP (fgKeyInd1KeyGapDhRunAtFlatComp S K idx A U V) p B) :
    IsQueryBoundP ((fgKeyInd1KeyGapDh2Prog S K).eval (fun _ => A) (U, V)) p B := by
  have hProg : IsQueryBoundP ((fgKeyInd1KeyGapDhProg S K).eval (fun _ => A) (U, V)) p B := by
    rw [fgKeyInd1KeyGapDhProg_eval_eq_of_queryBound S K (fun _ => A) hA U V]
    exact isQueryBoundP_bind_of_zero_mem_support (unifGdhSign_isQueryBoundP_zero _ p hpUnif) hFlat
  rw [fgKeyInd1KeyGapDhProg_eval_runFrom1Key S K A U V] at hProg
  have hRun1 := isQueryBoundP_of_bind_mem_support hProg
  rw [fgKeyInd1KeyGapDh2Prog_eval_runFrom1Key2 S K A U V]
  refine isQueryBoundP_bind_of_zero_mem_support
    (unifGdhSign_isQueryBoundP_zero _ p hpUnif) fun pa2 hpa2 => ?_
  have hpa2Prob : pa2 ∈ support (initParams1Key2Prob S U V) := mem_support_unifGdhSign_iff.mp hpa2
  have hInB := mem_support_initParams1Key2Prob_inBounds S U V hpa2Prob
  obtain ⟨idx, hIdx, hFlatEq⟩ := exists_flat_of_mem_support_initParams1Key2Prob S U V hpa2Prob
  have hEq : (do
      let secb ← unifGdhSign ($ᵗ Bool)
      runFrom1Key2 S K A
        ((pa2, simStateToVal (FgKeyInd1KeySimState.empty S secb).sim),
          min K (min S.N_spk_tot S.N_recv))) =
      (do
        let secb ← unifGdhSign ($ᵗ Bool)
        runFrom1Key S K A
          (sim1KeyStateToVal (params1KeyFlatVal S U V idx)
            (FgKeyInd1KeySimState.empty S secb))) :=
    _root_.bind_congr fun secb => by rw [runFrom1Key2_eq_runFrom1Key S K pa2 hInB A hA secb, hFlatEq]
  rw [hEq]
  exact hRun1 idx (mem_support_unifGdhSign_iff.mpr hIdx)

/-- Transfers any `IsQueryBoundP` bound (ignoring `unifSpec` draws) from
`(fgKeyInd1KeyGapDhProg S K).eval` to `(fgKeyInd1KeyGapDh2Prog S K).eval`. -/
theorem fgKeyInd1KeyGapDh2Prog_queryBound_of_flatProg (S : Setup) (K : Nat)
    (A : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : IsQueryBoundP A (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) K)
    (U V : Bytes) (p : _ → Prop) [DecidablePred p]
    (hpUnif : ∀ n : ℕ, ¬ p (Sum.inl (Sum.inl n))) (B : Nat)
    (hProg : IsQueryBoundP ((fgKeyInd1KeyGapDhProg S K).eval (fun _ => A) (U, V)) p B) :
    IsQueryBoundP ((fgKeyInd1KeyGapDh2Prog S K).eval (fun _ => A) (U, V)) p B := by
  rw [fgKeyInd1KeyGapDhProg_eval_eq_of_queryBound S K (fun _ => A) hA U V] at hProg
  exact fgKeyInd1KeyGapDh2Prog_transfer_queryBound S K A hA U V p hpUnif B
    (isQueryBoundP_of_bind_mem_support hProg)

/-- `fgKeyInd1KeyGapDh2Prog` and `fgKeyInd1KeyGapDhAdv4` induce the exact same output
    distribution in `gapDhWithSignExp`. -/
theorem fgKeyInd1KeyGapDh2Prog_evalDist_gapDhWithSignExp_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    𝒟[gapDhWithSignExp P isValidDhTriple pow8
        { run := fun U V => (fgKeyInd1KeyGapDh2Prog S b.q_total).eval (fun _ => A.1.run) (U, V)
          q_ddh := gdhQueryBudget S b
          q_sig := 2 * min S.N_spk_tot S.N_recv
          q_prim := gdhPrimQueryBudget S b }] =
      𝒟[gapDhWithSignExp P isValidDhTriple pow8 (fgKeyInd1KeyGapDhAdv4 S b A)] := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total := by
    obtain ⟨_, _, _, h, _⟩ := A.2; convert h using 1; funext q; cases q <;> rfl
  exact evalDist_gapDhWithSignExp_of_run_eq_param P isValidDhTriple pow8 S _ _
    (fun _ _ pa2 => do
      let secb ← unifGdhSign ($ᵗ Bool)
      runFrom1Key2 S b.q_total A.1.run
        ((pa2, simStateToVal (FgKeyInd1KeySimState.empty S secb).sim),
          min b.q_total (min S.N_spk_tot S.N_recv)))
    (fun _ _ pa => do
      let secb ← unifGdhSign ($ᵗ Bool)
      runFrom1Key S b.q_total A.1.run (sim1KeyStateToVal pa (FgKeyInd1KeySimState.empty S secb)))
    (fun U V => fgKeyInd1KeyGapDh2Prog_eval_runFrom1Key2 S b.q_total A.1.run U V)
    (fun U V => (fgKeyInd1KeyGapDhProg_eval_eq S b A U V).symm.trans
      (fgKeyInd1KeyGapDhProg_eval_runFrom1Key S b.q_total A.1.run U V))
    (fun _ _ pa2 hB => _root_.bind_congr fun secb =>
      runFrom1Key2_eq_runFrom1Key S b.q_total pa2 hB A.1.run hA secb)

end

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh2Eval
