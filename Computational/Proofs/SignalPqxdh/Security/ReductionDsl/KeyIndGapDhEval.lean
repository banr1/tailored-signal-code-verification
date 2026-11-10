/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhStep
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsBase
public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthGames
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhStepInit
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofs
import Computational.Proofs.ReductionDsl.Size
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Handler and Extractor Dispatch Equivalence for `fgKeyIndGapDhProg`

Proves that `gdhHandle` and `gdhFinish` evaluate to the shallow per-mode `GapDH` simulator steps
and CDH extractors, and establishes syntactic size/cost bounds and `evalDist` equivalence for
the tuple-keyed variant `fgKeyIndGapDh2Prog`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security.FgGapDh.Ik SignalPqxdh.Security.FgGapDh.Opk
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp
open scoped ENNReal

namespace SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Env.get Ext.wk

/-! ## Parameter Tuple Values -/

def paramsDhVal (S : Setup) (useDh1 : Bool) (tIdx spkIdx : Nat) (U V : Bytes) :
    paramsTy.denote :=
  (U, (V, (U, (useDh1, (tIdx, (useDh1, (tIdx, (spkIdx, (false, (S.N_opk_tot,
    if useDh1 then 0 else 1))))))))))

def paramsIkVal (S : Setup) (tIdx pIdx : Nat) (U V : Bytes) : paramsTy.denote :=
  (U, (V, (V, (true, (pIdx, (false, (tIdx, (S.N_spk_tot, (false, (S.N_opk_tot, 2))))))))))

def paramsOpkVal (S : Setup) (tIdx oIdx : Nat) (U V : Bytes) : paramsTy.denote :=
  (U, (V, (U, (false, (S.N_id, (false, (tIdx, (S.N_spk_tot, (true, (oIdx, 3))))))))))

@[simp] theorem initParamsDh_eval (S : Setup) {Γ : List PT}
    (useDh1 : Expr pqxdhOps Γ .bool) (tIdx spkIdx : Expr pqxdhOps Γ .nat)
    (U V : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (initParamsDh S useDh1 tIdx spkIdx U V).eval env =
      paramsDhVal S (useDh1.eval env) (tIdx.eval env) (spkIdx.eval env)
        (U.eval env) (V.eval env) := by
  simp [initParamsDh, paMk, paramsDhVal, Expr.eval]

@[simp] theorem initParamsIk_eval (S : Setup) {Γ : List PT}
    (tIdx pIdx : Expr pqxdhOps Γ .nat) (U V : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (initParamsIk S tIdx pIdx U V).eval env =
      paramsIkVal S (tIdx.eval env) (pIdx.eval env) (U.eval env) (V.eval env) := by
  simp [initParamsIk, paMk, paramsIkVal, Expr.eval]

@[simp] theorem initParamsOpk_eval (S : Setup) {Γ : List PT}
    (tIdx oIdx : Expr pqxdhOps Γ .nat) (U V : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (initParamsOpk S tIdx oIdx U V).eval env =
      paramsOpkVal S (tIdx.eval env) (oIdx.eval env) (U.eval env) (V.eval env) := by
  simp [initParamsOpk, paMk, paramsOpkVal, Expr.eval]

/-! ## `wrapSim` Simplification -/

@[simp] theorem wrapSim_eval {S : Setup} {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (paV : Var Γ₁ paramsTy) (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy))
    (env : Env Δ) (pa : paramsTy.denote)
    (m : OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S))
    (hpa : env.get (Ext.wk paV) = pa)
    (hc : c.eval env = encSimRS <$> m) :
    (wrapSim paV c).eval env = encGdhRS pa <$> m := by
  unfold wrapSim
  simp only [bindV, Comp.eval, v, Expr.eval, Env.get,
    Ext.step_wk', Ext.refl_wk', hc, hpa, map_eq_bind_pure_comp, bind_assoc]
  rfl

/-! ## Full Query Handler Dispatch -/

theorem gdhHandle_eval_step (S : Setup) (K : Nat) (pa : paramsTy.denote)
    (q : KeyIndQuery S) (st : FgKeyIndSimState S) (hB : FgSimListsBounded st K) :
    (gdhHandle S K).eval (.cons (pa, simStateToVal st) (.cons (keyIndQueryToVal q) .nil)) =
      encGdhRS pa <$>
        match q with
        | .initPrin u =>
          fgKeyIndStep pa.2.2.2.1 pa.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
            pa.2.2.1 pa.2.1 (.initPrin u) st
        | .genOPK u j o =>
          if pa.2.2.2.2.2.2.2.2.1 then
            fgGenOPKGdhOpk pa.2.2.2.2.2.2.2.2.2.1 S pa.2.1 u j o st
          else
            fgKeyIndStep pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
              pa.1 pa.2.1 (.genOPK u j o) st
        | .acceptOPK k j o hdr =>
          if pa.2.2.2.2.2.2.2.2.1 then
            fgRunAcceptOPKGdhOpk S K k j o hdr st
          else
            fgRunAcceptOPKGdh S K k j o hdr st
        | q =>
          fgKeyIndStep pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
            pa.1 pa.2.1 q st := by
  cases q with
  | initPrin u =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk']
    exact wrapSim_eval _ _ _ pa _ rfl (initPrinGdhB_eval S K _ _ _ _ pa st rfl rfl rfl hB _ u rfl)
  | corruptIK u =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk']
    exact corruptGdh_eval S K _ _ _ _ pa st rfl rfl rfl hB _ u rfl
  | genSPK u j =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk']
    exact wrapSim_eval _ _ _ pa _ rfl (genSpkGdhB_eval S K _ _ _ _ pa st rfl rfl rfl hB _ u j rfl)
  | genOPK u j o =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk']
    exact wrapSim_eval _ _ _ pa _ rfl
      (genOpkGdhB_eval S K _ _ _ _ pa st rfl rfl rfl hB _ u j o rfl)
  | initiateOPK u i b =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk']
    exact wrapSim_eval _ _ _ pa _ rfl
      (initiateOpkGdhB_eval S K _ _ _ _ pa st rfl rfl rfl hB _ u i b rfl)
  | initiateNoOPK u i b =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk']
    exact wrapSim_eval _ _ _ pa _ rfl
      (initiateNoOpkGdhB_eval S K _ _ _ _ pa st rfl rfl rfl hB _ u i b rfl)
  | acceptOPK k j o h =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk']
    cases hOpk : pa.2.2.2.2.2.2.2.2.1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact wrapSim_eval _ _ _ pa _ rfl
        (acceptOpkGdhB_eval_dh S K _ _ _ _ pa st rfl rfl rfl hB _ k j o h rfl hOpk)
    · simp only [↓reduceIte]
      exact wrapSim_eval _ _ _ pa _ rfl
        (acceptOpkGdhB_eval_opk S K _ _ _ _ pa st rfl rfl rfl hB _ k j o h rfl hOpk)
  | acceptNoOPK k j l h =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk']
    exact wrapSim_eval _ _ _ pa _ rfl
      (acceptNoOpkGdhB_eval S K _ _ _ st rfl rfl hB _ k j l h rfl)
  | testSession sid =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk']
    exact testGdh_eval S K _ _ _ _ pa st rfl rfl rfl hB _ sid rfl
  | roQuery sec =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk']
    exact wrapSim_eval _ _ _ pa _ rfl (roParsedC_eval K _ _ _ st sec rfl rfl hB)
  | revealDhSecrets =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk', rNone]
    rfl
  | revealSessionKey sid =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk']
    exact revealGdh_eval S K _ _ _ _ pa st rfl rfl rfl hB _ sid rfl
  | registerKey sk =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk']
    exact wrapSim_eval _ _ _ pa _ rfl (registerGdhB_eval S _ _ _ _ pa st rfl rfl _ sk rfl)
  | revealSpkSk u j =>
    simp only [gdhHandle, keyIndQueryToVal, keyIndQenc, letV_eval, caseSumV,
      Comp.eval, v, Expr.eval, smBase, simStateToVal, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk']
    exact revealSpkGdh_eval S K _ _ _ _ pa st rfl rfl rfl hB _ u j rfl

/-- `gdhHandle` under `paramsDhVal` evaluates to `fgKeyIndStep`. -/
theorem gdhHandle_eval_dh (S : Setup) (K : Nat) (useDh1 : Bool) (tIdx spkIdx : Nat)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyIndSimState S) (hB : FgSimListsBounded st K) :
    (gdhHandle S K).eval
      (.cons (paramsDhVal S useDh1 tIdx spkIdx U V, simStateToVal st)
        (.cons (keyIndQueryToVal q) .nil)) =
      encGdhRS (paramsDhVal S useDh1 tIdx spkIdx U V) <$>
        fgKeyIndStep useDh1 tIdx spkIdx S K U V q st := by
  rw [gdhHandle_eval_step S K (paramsDhVal S useDh1 tIdx spkIdx U V) q st hB]
  cases q <;> rfl

/-- `gdhHandle` under `paramsIkVal` evaluates to `fgKeyIndStepIk`. -/
theorem gdhHandle_eval_ik (S : Setup) (K : Nat) (tIdx pIdx : Nat)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyIndSimState S) (hB : FgSimListsBounded st K) :
    (gdhHandle S K).eval
      (.cons (paramsIkVal S tIdx pIdx U V, simStateToVal st)
        (.cons (keyIndQueryToVal q) .nil)) =
      encGdhRS (paramsIkVal S tIdx pIdx U V) <$>
        fgKeyIndStepIk tIdx pIdx S K U V q st := by
  rw [gdhHandle_eval_step S K (paramsIkVal S tIdx pIdx U V) q st hB]
  cases q <;> rfl

/-- `gdhHandle` under `paramsOpkVal` evaluates to `fgKeyIndStepOpk`. -/
theorem gdhHandle_eval_opk (S : Setup) (K : Nat) (tIdx oIdx : Nat)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyIndSimState S) (hB : FgSimListsBounded st K) :
    (gdhHandle S K).eval
      (.cons (paramsOpkVal S tIdx oIdx U V, simStateToVal st)
        (.cons (keyIndQueryToVal q) .nil)) =
      encGdhRS (paramsOpkVal S tIdx oIdx U V) <$>
        fgKeyIndStepOpk tIdx oIdx S K U V q st := by
  rw [gdhHandle_eval_step S K (paramsOpkVal S tIdx oIdx U V) q st hB]
  cases q <;> rfl

set_option allowUnsafeReducibility true in
attribute [local semireducible] Env.get Ext.wk

end

/-! ## Extractor Equivalence -/

def findMapStep {α : Type} (f : α → OracleComp GdhSimSpec Bytes) (U V : Bytes) (x : α)
    (acc : Option Bytes) : OracleComp GdhSimSpec (Option Bytes) :=
  match acc with
  | none => do let z ← f x; let ok ← ddhGdhQ U V z; pure (if ok then some z else none)
  | some _ => pure acc

theorem foldML_findMapStep_some {α : Type} (f : α → OracleComp GdhSimSpec Bytes) (U V : Bytes)
    (z : Bytes) (L : List α) :
    foldML (findMapStep f U V) (some z) L = pure (some z) := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [foldML, findMapStep, pure_bind, ih]

theorem foldML_findMapStep {α : Type} (f : α → OracleComp GdhSimSpec Bytes) (U V : Bytes)
    (L : List α) :
    foldML (findMapStep f U V) none L = findMapMGdh f U V L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [foldML, findMapStep, findMapMGdh, bind_assoc]
    refine congrArg (fun h => f x >>= h) (funext fun z => ?_)
    refine congrArg (fun h => ddhGdhQ U V z >>= h) (funext fun ok => ?_)
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, ih]
    · simp only [↓reduceIte, pure_bind, foldML_findMapStep_some]

theorem mem_support_mapML_length {α β : Type} (f : α → OracleComp GdhSimSpec β) (L : List α)
    (ys : List β) (h : ys ∈ support (mapML f L)) : ys.length = L.length := by
  induction L generalizing ys with
  | nil =>
    simp only [mapML] at h
    change ys ∈ support (pure [] : OracleComp GdhSimSpec (List β)) at h
    simp only [support_pure, Set.mem_singleton_iff] at h
    subst h; rfl
  | cons x xs ih =>
    simp only [mapML] at h
    change ys ∈ support (f x >>= fun y => mapML f xs >>= fun zs => pure (y :: zs)) at h
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h
    obtain ⟨y, _, zs, hzs, rfl⟩ := h
    simp [ih zs hzs]

theorem foldML_map {α α' β : Type} (g : α' → α) (f : α → β → OracleComp GdhSimSpec β) (b : β)
    (L : List α') :
    foldML f b (L.map g) = foldML (fun x acc => f (g x) acc) b L := by
  induction L generalizing b with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, foldML, ih]

theorem spkPowsGdh_eq (L : List ((Nat × Nat) × SpkBundleEntry)) :
    spkPowsGdh L = mapML
      (fun x : (Ty.prod (.prod .nat .nat) spkBundleEntryTy).denote => do
        let w ← embedPrim (spec := gapDhOracleSpec) (primQ (.pow8 x.2.2.1))
        pure (x.2.1, w))
      (L.map (Prod.map id spkBundleEntryToVal)) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k, b⟩ := x
    simp only [spkPowsGdh, List.map_cons, mapML, ih, bind_assoc, pure_bind]
    rfl

theorem gPrim_qX25519_pair_eval {Γ : List PT} (a b : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (gPrim (qX25519 (.pair a b))).eval env = primGdhQ (.x25519 (a.eval env) (b.eval env)) := by
  simp only [gPrim_eval, qX25519_eval, Expr.eval]; rfl

theorem respDh1CandC_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (spksV : Var Γ₁ (.list (.prod (.prod .nat .nat) spkBundleEntryTy)))
    (rV : Var Γ₂ keyIndRespEntryTy) (env : Env Δ)
    (spks : List ((Nat × Nat) × SpkBundleEntry)) (r : KeyIndRespEntry S)
    (hspks : env.get (Ext.wk spksV) = spks.map (Prod.map id spkBundleEntryToVal))
    (hr : env.get (Ext.wk rV) = keyIndRespEntryToVal r) (hlen : spks.length ≤ K) :
    (respDh1CandC S K spksV rV).eval env =
      respDh1CandGdh S spks r := by
  unfold respDh1CandC respDh1CandGdh
  rw [gPrim_qX25519_pair_eval]
  let fo := (spks.take S.N_dh).find? (fun x => x.1 == respBundleKey r.sid)
  have h1 : (eCaseOpt (eFind (min K S.N_dh) (v spksV) fun sb =>
      nat2Eq (.fst (v sb)) (respBundleKeyE (reSid (v rV))))
      (litB 32 [])
      fun sb => sbSpkSk (.snd (v sb))).eval env =
      (match fo with
       | some (_, b) => b.spkSk
       | none => []) := by
    dsimp only [eCaseOpt, eFind, litB_eval, sbSpkSk, v, Expr.eval, Env.get,
      Ext.step_wk', Ext.refl_wk']
    have hfind : List.find?
        (fun x => (nat2Eq (Expr.var Var.zero).fst
          (respBundleKeyE (reSid (Expr.var (Ext.wk rV).succ)))).eval (Env.cons x env))
        (List.take (min K S.N_dh) (env.get (Ext.wk spksV))) =
        Option.map (Prod.map id spkBundleEntryToVal) fo := by
      rw [hspks, ← List.map_take, take_minK, List.take_of_length_le hlen,
        List.find?_map]
      congr 2; funext ⟨idx, b⟩
      simp only [Function.comp_def]
      have hsid : (reSid (Expr.var (Ext.wk rV).succ)).eval
          (Env.cons (t := .prod (.prod .nat .nat) spkBundleEntryTy)
            (Prod.map id spkBundleEntryToVal (idx, b)) env) = sessionIdToVal r.sid := by
        simp only [Expr.eval, Env.get_succ', hr, keyIndRespEntryToVal]
      simp only [nat2Eq, Expr.eval, natEq_eval, Env.get_zero', Prod.map_fst, id_eq]
      rw [respBundleKeyE_eval _ _ r.sid hsid, ← nat2_beq]
    rw [hfind]
    clear hfind
    rcases fo with _ | ⟨fst, b⟩ <;> rfl
  have h2 : (hdIkAPk (reHdr (v rV))).eval env = r.hdr.ikAPk := by
    simp only [v, Expr.eval, hr, keyIndRespEntryToVal, hdrV]
  rw [h1, h2]; rfl

macro "finish_simp" : tactic => `(tactic| gdh_simp [gdhFinish, logFindC, extractMode0C,
    spkPowsC, lookupFromPowsE, initDh1CandC, findMapStepC,
    extractCdh2FromAdvRoLog, extractCdh4FromAdvRoLog, extractCdhFromAdvRoLog,
    extractCdhFromSimState, FgGapDh.extractDh2, FgGapDh.extractDh3, FgGapDh.extractDh4,
    List.map_take, Nat.reduceBEq, Bool.false_eq_true, List.take_take, min_self])

theorem gdhFinish_eval_mode2 (S : Setup) (K : Nat) (a : Bool) (pa : paramsTy.denote)
    (st : FgKeyIndSimState S) (hmode : pa.2.2.2.2.2.2.2.2.2.2 = 2) :
    (gdhFinish S K).eval (.cons (pa, simStateToVal st) (.cons a .nil)) =
      extractCdh2FromAdvRoLog K pa.1 pa.2.1 st.advRoLog := by
  simp only [simStateToVal]
  generalize keyIndStateToVal st.base = b
  finish_simp
  simp only [hmode, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
  exact congrArg (fun h => _ >>= h) (funext fun o => by cases o <;> rfl)

theorem gdhFinish_eval_mode3 (S : Setup) (K : Nat) (a : Bool) (pa : paramsTy.denote)
    (st : FgKeyIndSimState S) (hmode : pa.2.2.2.2.2.2.2.2.2.2 = 3) :
    (gdhFinish S K).eval (.cons (pa, simStateToVal st) (.cons a .nil)) =
      extractCdh4FromAdvRoLog K pa.1 pa.2.1 st.advRoLog := by
  simp only [simStateToVal]
  generalize keyIndStateToVal st.base = b
  finish_simp
  simp only [hmode, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  exact congrArg (fun h => _ >>= h) (funext fun o => by cases o <;> rfl)

theorem gdhFinish_eval_mode1 (S : Setup) (K : Nat) (a : Bool) (pa : paramsTy.denote)
    (st : FgKeyIndSimState S) (hmode : pa.2.2.2.2.2.2.2.2.2.2 = 1) :
    (gdhFinish S K).eval (.cons (pa, simStateToVal st) (.cons a .nil)) =
      extractCdhFromSimState S false K pa.1 pa.2.1 st := by
  simp only [simStateToVal]
  generalize keyIndStateToVal st.base = b
  finish_simp
  simp only [hmode, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
  exact congrArg (fun h => _ >>= h) (funext fun o => by cases o <;> rfl)

theorem gdhFinish_eval_mode0 (S : Setup) (K : Nat) (a : Bool) (pa : paramsTy.denote)
    (st : FgKeyIndSimState S) (hmode : pa.2.2.2.2.2.2.2.2.2.2 = 0)
    (hPows : st.advKeyPows.length ≤ K) (hB : KeyIndListsBounded st.base K) :
    (gdhFinish S K).eval (.cons (pa, simStateToVal st) (.cons a .nil)) =
      extractCdhFromSimState S true K pa.1 pa.2.1 st := by
  simp only [simStateToVal, keyIndStateToVal]
  finish_simp
  simp only [hmode, beq_self_eq_true, ↓reduceIte]
  refine congrArg (fun h => _ >>= h) (funext fun o => ?_)
  rcases o with _ | z
  swap
  · rfl
  simp only [spkPowsGdh_eq, List.map_take]
  simp only [← List.map_take, take_minK, List.take_of_length_le hB.spkBundles_le,
    List.take_of_length_le hB.sessions_le, List.take_of_length_le hB.respSessions_le]
  simp only [List.map_take]
  refine bind_congr_of_forall_mem_support _ (fun pows hpows => ?_)
  have hlen := mem_support_mapML_length _ _ _ hpows
  simp only [List.length_take, List.length_map] at hlen
  have hsl := hB.spkBundles_le
  rw [List.take_of_length_le (by omega : pows.length ≤ min K S.N_dh),
    List.take_of_length_le (by omega : st.advKeyPows.length ≤ K)]
  simp only [← List.map_take, foldML_map, ← foldML_findMapStep]
  congr 1
  · congr 1
    funext x acc
    cases acc
    · simp only [findMapStep, initDh1CandWithPowsGdh, lookupSpkSkFromPows, primGdhQ, bind_assoc]
      refine congrArg (fun h => _ >>= h) (funext fun w => ?_)
      cases List.find? (fun x => x.2 == w) pows with
      | some p => rfl
      | none => cases List.find? (fun x => x.2 == w) st.advKeyPows <;> rfl
    · rfl
  · funext o
    cases o
    · simp only
      congr 1
      · congr 1
        funext r acc
        cases acc
        · rw [respDh1CandC_eval S K _ _ _ st.base.spkBundles r rfl rfl hB.spkBundles_le]
          rfl
        · rfl
      · funext o; cases o <;> rfl
    · rfl

/-! ## Tuple-Keyed Program (`fgKeyIndGapDh2Prog`) Bounds & Equivalence -/

section TupleKeyedProg

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] gapDhDdhOracle

/-! ### Syntactic Query Bounds (`wDdhGdh` and `wPrimGdh`) -/

@[simp] private theorem wrapBase2_chal {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queries wDdhGdh wsZero = 0 := by
  simp [wrapBase2, Comp.queries]

@[simp] private theorem wrapSim2_chal {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty) (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queries wDdhGdh wsZero = c.queries wDdhGdh wsZero := by
  simp [wrapSim2, Comp.queries]

@[simp] private theorem wrapBase2_primUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queriesUB wPrimGdh wsZero = c.queriesUB wPrimBase wsZeroBase := by
  simp [wrapBase2, bindV_queriesUB, gPrim_queriesUB_wPrimGdh, Comp.queriesUB]

@[simp] private theorem wrapSim2_primUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty) (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queriesUB wPrimGdh wsZero = c.queriesUB wPrimGdh wsZero := by
  simp [wrapSim2, bindV_queriesUB, Comp.queriesUB]

private theorem bernoulliRatioGdhC_chal {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).queries wDdhGdh wsZero = 0 := by
  unfold bernoulliRatioGdhC
  split_ifs <;> simp [Comp.queries]

private theorem bernoulliRatioGdhC_prim {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).queries wPrimGdh wsZero = 0 := by
  unfold bernoulliRatioGdhC
  split_ifs <;> simp [Comp.queries]

private theorem chooseArm2C_chal {Γ₁ Δ : List PT} {α : PT} [Ext Γ₁ Δ] (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' α)
    (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).queries wDdhGdh wsZero = 0)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).queries wDdhGdh wsZero = 0) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).queries wDdhGdh wsZero = 0 := by
  unfold chooseArm2C
  split_ifs
  · exact h2
  · exact h1
  · simp [bindV_queries, bernoulliRatioGdhC_chal, Comp.queries, h1, h2]

private theorem chooseArm2C_prim {Γ₁ Δ : List PT} {α : PT} [Ext Γ₁ Δ] (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' α)
    (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).queries wPrimGdh wsZero = 0)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).queries wPrimGdh wsZero = 0) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).queries wPrimGdh wsZero = 0 := by
  unfold chooseArm2C
  split_ifs
  · exact h2
  · exact h1
  · simp [bindV_queries, bernoulliRatioGdhC_prim, Comp.queries, h1, h2]

private theorem coordSamplers2_chal (S : Setup) {Δ : List PT} :
    (samplePrin2C S (Δ := Δ)).queries wDdhGdh wsZero = 0 ∧
    (sampleSpkPair2C S (Δ := Δ)).queries wDdhGdh wsZero = 0 ∧
    (sampleOpkTriple2C S (Δ := Δ)).queries wDdhGdh wsZero = 0 ∧
    (sampleSendOpkTarget2C S (Δ := Δ)).queries wDdhGdh wsZero = 0 ∧
    (sampleSendNoOpkTarget2C S (Δ := Δ)).queries wDdhGdh wsZero = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold samplePrin2C; split_ifs <;> simp [Comp.queries]
  · unfold sampleSpkPair2C; split_ifs <;> simp [Comp.queries]
  · unfold sampleOpkTriple2C; split_ifs <;> simp [Comp.queries]
  · unfold sampleSendOpkTarget2C; split_ifs <;> simp [Comp.queries]
  · unfold sampleSendNoOpkTarget2C; split_ifs <;> simp [Comp.queries]

private theorem coordSamplers2_prim (S : Setup) {Δ : List PT} :
    (samplePrin2C S (Δ := Δ)).queries wPrimGdh wsZero = 0 ∧
    (sampleSpkPair2C S (Δ := Δ)).queries wPrimGdh wsZero = 0 ∧
    (sampleOpkTriple2C S (Δ := Δ)).queries wPrimGdh wsZero = 0 ∧
    (sampleSendOpkTarget2C S (Δ := Δ)).queries wPrimGdh wsZero = 0 ∧
    (sampleSendNoOpkTarget2C S (Δ := Δ)).queries wPrimGdh wsZero = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold samplePrin2C; split_ifs <;> simp [Comp.queries]
  · unfold sampleSpkPair2C; split_ifs <;> simp [Comp.queries]
  · unfold sampleOpkTriple2C; split_ifs <;> simp [Comp.queries]
  · unfold sampleSendOpkTarget2C; split_ifs <;> simp [Comp.queries]
  · unfold sampleSendNoOpkTarget2C; split_ifs <;> simp [Comp.queries]

private theorem sampleSendTarget2C_chal (S : Setup) {Δ : List PT} :
    (sampleSendTarget2C S (Δ := Δ)).queries wDdhGdh wsZero = 0 := by
  unfold sampleSendTarget2C
  split_ifs
  · simp [Comp.queries]
  · exact chooseArm2C_chal _ _ _ _
      (fun {Δ'} [_] => (coordSamplers2_chal S (Δ := Δ')).2.2.2.1)
      (fun {Δ'} [_] => (coordSamplers2_chal S (Δ := Δ')).2.2.2.2)

private theorem sampleSendTarget2C_prim (S : Setup) {Δ : List PT} :
    (sampleSendTarget2C S (Δ := Δ)).queries wPrimGdh wsZero = 0 := by
  unfold sampleSendTarget2C
  split_ifs
  · simp [Comp.queries]
  · exact chooseArm2C_prim _ _ _ _
      (fun {Δ'} [_] => (coordSamplers2_prim S (Δ := Δ')).2.2.2.1)
      (fun {Δ'} [_] => (coordSamplers2_prim S (Δ := Δ')).2.2.2.2)

theorem fgKeyIndGapDh2Prog_init_chalQueries (S : Setup) (K : Nat) :
    (fgKeyIndGapDh2Prog S K).init.queries wDdhGdh wsZero = 0 := by
  have hP : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (initParams2C S (Δ := Δ) uv).queries wDdhGdh wsZero = 0 := by
    intro Γ₁ Δ _ uv
    unfold initParams2C
    split_ifs
    · simp [Comp.queries]
    · refine chooseArm2C_chal _ _ _ _ (fun {_} [_] => ?_) (fun {_} [_] => ?_)
      · refine chooseArm2C_chal _ _ _ _ (fun {_} [_] => ?_) (fun {_} [_] => ?_)
        · simp [bindV_queries, (coordSamplers2_chal S).1, (coordSamplers2_chal S).2.1, Comp.queries]
        · simp [bindV_queries, sampleSendTarget2C_chal, (coordSamplers2_chal S).2.1, Comp.queries]
      · refine chooseArm2C_chal _ _ _ _ (fun {_} [_] => ?_) (fun {_} [_] => ?_)
        · simp [bindV_queries, sampleSendTarget2C_chal, (coordSamplers2_chal S).1, Comp.queries]
        · simp [bindV_queries, (coordSamplers2_chal S).2.2.2.1, (coordSamplers2_chal S).2.2.1, Comp.queries]
  simp [fgKeyIndGapDh2Prog, initAdv4_2, bindV_queries, letV_queries, hP, Comp.queries]

theorem fgKeyIndGapDh2Prog_init_primQueries (S : Setup) (K : Nat) :
    (fgKeyIndGapDh2Prog S K).init.queries wPrimGdh wsZero = 0 := by
  have hP : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (initParams2C S (Δ := Δ) uv).queries wPrimGdh wsZero = 0 := by
    intro Γ₁ Δ _ uv
    unfold initParams2C
    split_ifs
    · simp [Comp.queries]
    · refine chooseArm2C_prim _ _ _ _ (fun {_} [_] => ?_) (fun {_} [_] => ?_)
      · refine chooseArm2C_prim _ _ _ _ (fun {_} [_] => ?_) (fun {_} [_] => ?_)
        · simp [bindV_queries, (coordSamplers2_prim S).1, (coordSamplers2_prim S).2.1, Comp.queries]
        · simp [bindV_queries, sampleSendTarget2C_prim, (coordSamplers2_prim S).2.1, Comp.queries]
      · refine chooseArm2C_prim _ _ _ _ (fun {_} [_] => ?_) (fun {_} [_] => ?_)
        · simp [bindV_queries, sampleSendTarget2C_prim, (coordSamplers2_prim S).1, Comp.queries]
        · simp [bindV_queries, (coordSamplers2_prim S).2.2.2.1, (coordSamplers2_prim S).2.2.1, Comp.queries]
  simp [fgKeyIndGapDh2Prog, initAdv4_2, bindV_queries, letV_queries, hP, Comp.queries]

theorem gdhHandle2_chalQueries (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries wDdhGdh wsZero = 4 * K := by
  simp [gdhHandle2, initPrinGdh2B, genSpkGdh2B, genOpkGdh2B, initiateGdh2B,
    finishAcceptGdhC, acceptOpkGdh2B, acceptNoOpkGdhB, roParsedC, roRawFallbackC,
    registerGdhB, Comp.queries]

theorem gdhFinish2_chalQueries (S : Setup) (K : Nat) :
    (gdhFinish2 S K).queries wDdhGdh wsZero = K + (min K S.N_dh) + (min K S.N_sess_tot) := by
  simp only [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC, findMapStep2C,
    initDh1CandC, respDh1CandC, letV_queries, bindV_queries, caseOptV_queries,
    findMV_queries, mapMV_queries, foldMV_queries, ddhQ_queries_wDdhGdh,
    gPrim_queries_wDdhGdh, Comp.queries, Nat.mul_one, Nat.mul_zero,
    Nat.add_zero, Nat.zero_add, Nat.max_zero, max_self]
  omega

theorem gdhHandle2_primUB (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queriesUB wPrimGdh wsZero =
      153 + 72 * (min K S.N_dh) + 16 * (min K S.N_sess_tot) := by
  simp only [gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
    initiateGdh2B, finishAcceptGdhC, acceptOpkGdh2B, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase2_primUB, wrapSim2_primUB,
    letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, caseSumV_queriesUB,
    gPrim_queriesUB_wPrimGdh, koskBundleOkPowsC_primUB, koskSenderOkPowsC_primUB,
    resolveSigPkC_primUB, lookupSpkSkC_primUB, honestPeerC_primUB, checkProvC_primUB,
    findHonestC_primUB, chooseInitRandC_primUB, chooseRespRandC_primUB,
    computePosC_primUB, computeOptPosInitC_primUB, mkSecretPosC_primUB, fgPatchC_primUB,
    sBytes32_queriesUB, sRandom64_queriesUB, sDrKey96_queriesUB,
    qX25519_queriesUB, qX25519Base_queriesUB, qIsCanonical_queriesUB, qPow8_queriesUB,
    qSigPkGen_queriesUB, qSigSign_queriesUB, qSigVerify_queriesUB,
    qKemKeyGen_queriesUB, qKemEncaps_queriesUB, qKemDecaps_queriesUB,
    Comp.queriesUB]
  ring

theorem gdhFinish2_primUB (S : Setup) (K : Nat) :
    (gdhFinish2 S K).queriesUB wPrimGdh wsZero = 3 * (min K S.N_dh) + (min K S.N_sess_tot) := by
  simp only [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC, findMapStep2C,
    initDh1CandC, respDh1CandC, letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB,
    findMV_queriesUB, mapMV_queriesUB, foldMV_queriesUB,
    ddhQ_queriesUB_wPrimGdh, gPrim_queriesUB_wPrimGdh,
    qPow8_queriesUB, qX25519_queriesUB, Comp.queriesUB]
  ring

theorem gdhHandle2_primQueries_le (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries wPrimGdh wsZero ≤ 153 + 72 * S.N_dh + 16 * S.N_sess_tot := by
  have h := Comp.queries_le_queriesUB wPrimGdh wsZero (gdhHandle2 S K)
  rw [gdhHandle2_primUB] at h
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  omega

theorem gdhFinish2_primQueries_le (S : Setup) (K : Nat) :
    (gdhFinish2 S K).queries wPrimGdh wsZero ≤ 3 * S.N_dh + S.N_sess_tot := by
  have h := Comp.queries_le_queriesUB wPrimGdh wsZero (gdhFinish2 S K)
  rw [gdhFinish2_primUB] at h
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  omega

theorem fgKeyIndGapDh2Prog_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyIndGapDh2Prog S b.q_total).totalQueries wPrimGdh wsZero b.q_total ≤
      primQueryBudget S b := by
  have h0 : (fgKeyIndGapDh2Prog S b.q_total).totalQueries wPrimGdh wsZero b.q_total ≤
      b.q_total * (153 + 72 * S.N_dh + 16 * S.N_sess_tot) + 3 * S.N_dh + S.N_sess_tot := by
    simp only [CostedReduction.totalQueries, fgKeyIndGapDh2Prog_init_primQueries]
    have hH := Nat.mul_le_mul_left b.q_total (gdhHandle2_primQueries_le S b.q_total)
    have hF := gdhFinish2_primQueries_le S b.q_total
    change 0 + b.q_total * (gdhHandle2 S b.q_total).queries wPrimGdh wsZero +
      (gdhFinish2 S b.q_total).queries wPrimGdh wsZero ≤ _
    omega
  unfold primQueryBudget
  nlinarith

theorem fgKeyIndGapDh2Prog_totalChalQueries_eq (S : Setup) (K q : Nat) :
    (fgKeyIndGapDh2Prog S K).totalQueries wDdhGdh wsZero q =
      4 * q * K + K + min K S.N_dh + min K S.N_sess_tot := by
  simp only [CostedReduction.totalQueries, fgKeyIndGapDh2Prog_init_chalQueries]
  change 0 + q * (gdhHandle2 S K).queries wDdhGdh wsZero +
    (gdhFinish2 S K).queries wDdhGdh wsZero = _
  rw [gdhHandle2_chalQueries, gdhFinish2_chalQueries]
  ring

theorem fgKeyIndGapDh2Prog_totalChalQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyIndGapDh2Prog S b.q_total).totalQueries wDdhGdh wsZero b.q_total ≤
      4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  rw [fgKeyIndGapDh2Prog_totalChalQueries_eq]
  have md : min b.q_total S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min b.q_total S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  nlinarith

theorem fgKeyIndGapDh2Prog_chalBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := keyIndSpec S)) q)
    (U V : Bytes) :
    ((fgKeyIndGapDh2Prog S K).eval A (U, V)).IsQueryBoundP
      (fun q => q.isRight = true) (4 * q * K + K + min K S.N_dh + min K S.N_sess_tot) := by
  rw [← fgKeyIndGapDh2Prog_totalChalQueries_eq S K q]
  refine CostedReduction.queryBound_eval (fgKeyIndGapDh2Prog S K) (fun q => q.isRight = true)
    wDdhGdh wsZero ?_ ?_ A q hA (U, V)
  · intro g x hx
    cases g with
    | inl t => simp [pqGapDhIface, pqChalIface] at hx
    | inr t => rcases t with ⟨⟩; simp [wDdhGdh]
  · intro n
    simp [pqGapDhIface, pqChalIface]

theorem fgKeyIndGapDh2Prog_primBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := keyIndSpec S)) q)
    (U V : Bytes) :
    ((fgKeyIndGapDh2Prog S K).eval A (U, V)).IsQueryBoundP
      (fun q => isPrimQuery q = true)
      ((fgKeyIndGapDh2Prog S K).totalQueries wPrimGdh wsZero q) := by
  refine CostedReduction.queryBound_eval (fgKeyIndGapDh2Prog S K) (fun q => isPrimQuery q = true)
    wPrimGdh wsZero ?_ ?_ A q hA (U, V)
  · intro g x hx
    cases g with
    | inl t => simp [wPrimGdh]
    | inr t => simp [pqGapDhIface, pqChalIface, isPrimQuery] at hx
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + gapDhDdhOracle.spec) (Sum.inl (Sum.inl n))))
      (fun q => isPrimQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isPrimQuery]

/-! ### Syntactic Cost Bounds -/

@[simp] private theorem wrapBase2_costUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).costUB = c.costUB + 30 := by
  simp only [wrapBase2, smUpd, smMk, bindV_costUB, gPrim_costUB,
    smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, v_costUB, Comp.costUB, Expr.costUB]

@[simp] private theorem wrapSim2_costUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).costUB = c.costUB + 9 := rfl

private theorem bernoulliRatioGdhC_costUB_le {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).costUB ≤
      if A = 0 ∨ B = 0 then 2 else 3 * bits (A + B) + 25 := by
  unfold bernoulliRatioGdhC
  by_cases hA : A = 0
  · simp [hA, Comp.costUB, Expr.costUB]
  by_cases hB : B = 0
  · simp [hA, hB, Comp.costUB, Expr.costUB]
  simp only [hA, hB, or_self, ↓reduceIte]
  split_ifs with hle
  · simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    have hm : bits A ≤ bits (A + B) := bits_mono (by omega)
    omega
  · simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    have hm : bits B ≤ bits (A + B) := bits_mono (by omega)
    omega

private theorem coordSamplers2_costUB_le (S : Setup) {Δ : List PT} :
    (samplePrin2C S (Δ := Δ)).costUB ≤ bits S.N_dh + 10 ∧
    (sampleSpkPair2C S (Δ := Δ)).costUB ≤ 2 * bits S.N_dh + 15 ∧
    (sampleOpkTriple2C S (Δ := Δ)).costUB ≤ 3 * bits S.N_dh + 20 ∧
    (sampleSendOpkTarget2C S (Δ := Δ)).costUB ≤ 2 * bits S.N_dh + 20 ∧
    (sampleSendNoOpkTarget2C S (Δ := Δ)).costUB ≤ 2 * bits S.N_dh + 20 := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold samplePrin2C
    split_ifs
    · simp [Comp.costUB, Expr.costUB]
    · simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have bm : bits S.N_id ≤ bits S.N_dh := bits_mono (by omega)
      omega
  · unfold sampleSpkPair2C
    split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_spk_tot, hc])
      have hR : S.N_recv ≤ S.N_spk_tot := Nat.le_mul_of_pos_left _ hId
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have bm1 : bits S.N_id ≤ bits S.N_dh := bits_mono (by omega)
      have bm2 : bits S.N_recv ≤ bits S.N_dh := bits_mono (by omega)
      omega
  · unfold sampleOpkTriple2C
    split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hSpk : 0 < S.N_spk_tot := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_opk_tot, hc])
      have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc =>
        Nat.ne_of_gt hSpk (by simp [Setup.N_spk_tot, hc])
      have hR : S.N_recv ≤ S.N_spk_tot := Nat.le_mul_of_pos_left _ hId
      have hO : S.N_opk ≤ S.N_opk_tot := Nat.le_mul_of_pos_left _ hSpk
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have bm1 : bits S.N_id ≤ bits S.N_dh := bits_mono (by omega)
      have bm2 : bits S.N_recv ≤ bits S.N_dh := bits_mono (by omega)
      have bm3 : bits S.N_opk ≤ bits S.N_dh := bits_mono (by omega)
      omega
  · unfold sampleSendOpkTarget2C
    split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_send_opk_tot, hc])
      have hS : S.N_send_opk ≤ S.N_send_opk_tot := Nat.le_mul_of_pos_left _ hId
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have bm1 : bits S.N_id ≤ bits S.N_dh := bits_mono (by omega)
      have bm2 : bits S.N_send_opk ≤ bits S.N_dh := bits_mono (by omega)
      omega
  · unfold sampleSendNoOpkTarget2C
    split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_send_no_opk_tot, hc])
      have hS : S.N_send_no_opk ≤ S.N_send_no_opk_tot := Nat.le_mul_of_pos_left _ hId
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have bm1 : bits S.N_id ≤ bits S.N_dh := bits_mono (by omega)
      have bm2 : bits S.N_send_no_opk ≤ bits S.N_dh := bits_mono (by omega)
      omega

private theorem chooseArm2C_costUB_le_arms {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT}
    (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ)
    (B1 B2 : Nat)
    (hc1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).costUB ≤ B1)
    (hc2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).costUB ≤ B2) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).costUB ≤
      3 * bits (w1 + w2) + B1 + B2 + 30 := by
  unfold chooseArm2C
  split_ifs with hw1 hw2
  · exact le_trans hc2 (by omega)
  · exact le_trans hc1 (by omega)
  · dsimp only [bindV]
    simp only [Comp.costUB, v_costUB]
    have hb := bernoulliRatioGdhC_costUB_le (Δ := Δ) w1 w2
    simp only [hw1, hw2, or_self, ↓reduceIte] at hb
    have h1 := hc1 (Δ' := .bool :: Δ)
    have h2 := hc2 (Δ' := .bool :: Δ)
    omega

private theorem sampleSendTarget2C_costUB_le (S : Setup) {Δ : List PT} :
    (sampleSendTarget2C S (Δ := Δ)).costUB ≤ 7 * bits S.N_dh + 75 := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  unfold sampleSendTarget2C
  split_ifs
  · simp [Comp.costUB, Expr.costUB]
  · have hc := chooseArm2C_costUB_le_arms (Γ₁ := Δ) (Δ := Δ)
      S.N_send_opk_tot S.N_send_no_opk_tot
      (fun {Δ'} [_] => sampleSendOpkTarget2C S (Δ := Δ'))
      (fun {Δ'} [_] => sampleSendNoOpkTarget2C S (Δ := Δ'))
      (2 * bits S.N_dh + 20) (2 * bits S.N_dh + 20)
      (fun {Δ'} [_] => (coordSamplers2_costUB_le S (Δ := Δ')).2.2.2.1)
      (fun {Δ'} [_] => (coordSamplers2_costUB_le S (Δ := Δ')).2.2.2.2)
    have bm : bits (S.N_send_opk_tot + S.N_send_no_opk_tot) ≤ bits S.N_dh := bits_mono (by omega)
    omega

theorem fgKeyIndGapDh2Prog_init_cost_le (S : Setup) (K : Nat) :
    (fgKeyIndGapDh2Prog S K).init.cost ≤ 45 * bits S.N_dh + 620 := by
  refine le_trans (fgKeyIndGapDh2Prog S K).init.cost_le_costUB ?_
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hsq : ∀ x, x ≤ S.N_dh * S.N_dh → bits x ≤ 2 * bits S.N_dh + 1 := fun x hx =>
    le_trans (bits_mono hx) (by have hm := bits_mul S.N_dh S.N_dh; omega)
  have hArmA : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (bindV (samplePrin2C S) fun pt => bindV (sampleSpkPair2C S) fun st =>
        Comp.ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
          (v pt) (.bool true) .none (v st) (.bool false) .none (.nat 0)) :
        Comp pqxdhOps pqGapDhIface Δ params2Ty).costUB ≤ 3 * bits S.N_dh + 60 := by
    intro Γ₁ Δ _ uv
    simp only [bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_0]
    have h1 := (coordSamplers2_costUB_le S (Δ := Δ)).1
    have h2 := (coordSamplers2_costUB_le S (Δ := .opt .nat :: Δ)).2.1
    omega
  have hArmC : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (bindV (sampleSendTarget2C S) fun et => bindV (sampleSpkPair2C S) fun st =>
        Comp.ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
          .none (.bool false) (v et) (v st) (.bool false) .none (.nat 1)) :
        Comp pqxdhOps pqGapDhIface Δ params2Ty).costUB ≤ 9 * bits S.N_dh + 135 := by
    intro Γ₁ Δ _ uv
    simp only [bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    have h1 := sampleSendTarget2C_costUB_le S (Δ := Δ)
    have h2 := (coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ)).2.1
    omega
  have hArmB : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (bindV (sampleSendTarget2C S) fun et => bindV (samplePrin2C S) fun pt =>
        Comp.ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.snd (v uv))
          (v pt) (.bool false) (v et) .none (.bool false) .none (.nat 2)) :
        Comp pqxdhOps pqGapDhIface Δ params2Ty).costUB ≤ 8 * bits S.N_dh + 130 := by
    intro Γ₁ Δ _ uv
    simp only [bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_2]
    have h1 := sampleSendTarget2C_costUB_le S (Δ := Δ)
    have h2 := (coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ)).1
    omega
  have hArmD : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (bindV (sampleSendOpkTarget2C S) fun et => bindV (sampleOpkTriple2C S) fun ot =>
        Comp.ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
          .none (.bool false) (v et) .none (.bool true) (v ot) (.nat 3)) :
        Comp pqxdhOps pqGapDhIface Δ params2Ty).costUB ≤ 5 * bits S.N_dh + 75 := by
    intro Γ₁ Δ _ uv
    simp only [bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_3]
    have h1 := (coordSamplers2_costUB_le S (Δ := Δ)).2.2.2.1
    have h2 := (coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ)).2.2.1
    omega
  have hSubAC : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) (S.N_id * S.N_spk_tot) (S.N_send_tot * S.N_spk_tot)
        (fun {_} [_] => bindV (samplePrin2C S) fun pt => bindV (sampleSpkPair2C S) fun st =>
          .ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
            (v pt) (.bool true) .none (v st) (.bool false) .none (.nat 0)))
        (fun {_} [_] => bindV (sampleSendTarget2C S) fun et => bindV (sampleSpkPair2C S) fun st =>
          .ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
            .none (.bool false) (v et) (v st) (.bool false) .none (.nat 1)))).costUB ≤
      18 * bits S.N_dh + 230 := by
    intro Γ₁ Δ _ uv
    have hc := chooseArm2C_costUB_le_arms (Γ₁ := Γ₁) (Δ := Δ)
      (S.N_id * S.N_spk_tot) (S.N_send_tot * S.N_spk_tot) _ _
      (3 * bits S.N_dh + 60) (9 * bits S.N_dh + 135)
      (fun {Δ'} [_] => hArmA (Δ := Δ') uv) (fun {Δ'} [_] => hArmC (Δ := Δ') uv)
    have bsum := hsq (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) (by nlinarith)
    omega
  have hSubBD : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) (S.N_send_tot * S.N_id) (S.N_send_opk_tot * S.N_opk_tot)
        (fun {_} [_] => bindV (sampleSendTarget2C S) fun et => bindV (samplePrin2C S) fun pt =>
          .ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.snd (v uv))
            (v pt) (.bool false) (v et) .none (.bool false) .none (.nat 2)))
        (fun {_} [_] => bindV (sampleSendOpkTarget2C S) fun et => bindV (sampleOpkTriple2C S) fun ot =>
          .ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
            .none (.bool false) (v et) .none (.bool true) (v ot) (.nat 3)))).costUB ≤
      19 * bits S.N_dh + 240 := by
    intro Γ₁ Δ _ uv
    have hc := chooseArm2C_costUB_le_arms (Γ₁ := Γ₁) (Δ := Δ)
      (S.N_send_tot * S.N_id) (S.N_send_opk_tot * S.N_opk_tot) _ _
      (8 * bits S.N_dh + 130) (5 * bits S.N_dh + 75)
      (fun {Δ'} [_] => hArmB (Δ := Δ') uv) (fun {Δ'} [_] => hArmD (Δ := Δ') uv)
    have bsum := hsq (S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot)
      (by nlinarith [Nat.zero_le (S.N_send_no_opk_tot * S.N_opk_tot)])
    omega
  have hInitP : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (initParams2C S (Δ := Δ) uv).costUB ≤ 43 * bits S.N_dh + 505 := by
    intro Γ₁ Δ _ uv
    unfold initParams2C
    split_ifs
    · simp only [pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_0, bits_3]; omega
    · let wAC := S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot
      let wBD := S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot
      have hc := chooseArm2C_costUB_le_arms (Γ₁ := Γ₁) (Δ := Δ) wAC wBD _ _
        (18 * bits S.N_dh + 230) (19 * bits S.N_dh + 240)
        (fun {Δ'} [_] => hSubAC (Δ := Δ') uv) (fun {Δ'} [_] => hSubBD (Δ := Δ') uv)
      have bsum : bits (wAC + wBD) ≤ 2 * bits S.N_dh + 1 :=
        hsq (wAC + wBD)
          (by dsimp only [wAC, wBD]; nlinarith [Nat.zero_le (S.N_send_no_opk_tot * S.N_opk_tot)])
      linarith
  simp only [fgKeyIndGapDh2Prog, initAdv4_2, emptySimE, smMk, emptyStE, stMk,
    letV_costUB, bindV_costUB, gPrim_costUB, sBool_costUB, v_costUB, Comp.costUB, Expr.costUB]
  have hp := hInitP (Γ₁ := [.prod (B 32) (B 32), .prod (B 32) (B 32)])
    (Δ := [.prod (B 32) (B 32), .prod (B 32) (B 32)]) .zero
  linarith

set_option maxRecDepth 100000 in
theorem gdhHandle2_cost_le_min (S : Setup) (K : Nat) :
    (gdhHandle2 S K).cost ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 62000 := by
  refine le_trans (gdhHandle2 S K).cost_le_costUB ?_
  simp only [gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
    initiateGdh2B, finishAcceptGdhC_costUB, acceptOpkGdh2B, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase2_costUB, wrapSim2_costUB,
    pa2U, pa2V, pa2Up, pa2PrinTarget, pa2DhFlag, pa2EphTarget, pa2SpkTarget,
    pa2OpkMode, pa2OpkTarget, ephSidMatchesE,
    stMk, stUpd, peMk, peUpd, sbMk, sbUpd, oeMk, oeUpd, buMk, hdMk, seMk, seUpd, reUpd,
    smMk, smUpd, qKJO, rs, slice32_costUB,
    qK_costUB, qJ_costUB, qO_costUB, qHdr_costUB,
    rNone_costUB, rInitPrin_costUB, rPk_costUB, rCorr_costUB, rBundle_costUB, rHdr_costUB,
    rInitUnfresh_costUB, rDrKey_costUB, rSpkSk_costUB,
    smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
    initSidE,
    natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
    optU32Eq, isSomeE, optFst, optSnd, nonZero32, encEC_costUB, encKEM_costUB,
    eLet2, reMk,
    letV_costUB, bindV_costUB, caseOptV_costUB, caseSumV_costUB,
    eLet_costUB, eCaseOpt_costUB, eCaseSum_costUB, eFind_costUB, eAny_costUB, eMap_costUB,
    gPrim_costUB, koskBundleOkPowsC_costUB, koskSenderOkPowsC_costUB,
    resolveSigPkC_costUB, lookupSpkSkC_costUB, honestPeerC_costUB, checkProvC_costUB,
    findHonestC_costUB, chooseInitRandC_costUB,
    computePosC_costUB, computeOptPosInitC_costUB, mkSecretPosC_costUB, fgPatchC_costUB,
    sBytes32_costUB, sRandom64_costUB, sDrKey96_costUB,
    qX25519_costUB, qX25519Base_costUB, qIsCanonical_costUB, qPow8_costUB,
    qSigPkGen_costUB, qSigSign_costUB, qSigVerify_costUB,
    qKemKeyGen_costUB, qKemEncaps_costUB, qKemDecaps_costUB,
    litB_costUB, takeKB_costUB, lenB_costUB, eqB_costUB,
    u32OfNat_costUB, eqU32_costUB, v_costUB,
    Comp.costUB, Expr.costUB,
    List.length_nil, List.length_replicate, F_X25519_length', PNat.val_ofNat,
    bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
    ↓reduceIte, Bool.false_eq_true]
  linarith

theorem gdhFinish2_cost_le_min (S : Setup) (K : Nat) :
    (gdhFinish2 S K).cost ≤
      69 * (min K S.N_dh) ^ 2 + 69 * K * (min K S.N_dh) +
        66 * (min K S.N_dh) * (min K S.N_sess_tot) +
        423 * (min K S.N_dh) + 263 * (min K S.N_sess_tot) + 2132 * K + 409 := by
  refine le_trans (gdhFinish2 S K).cost_le_costUB ?_
  simp only [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC_costUB, findMapStep2C,
    initDh1CandC_costUB, respDh1CandC_costUB, slice32_costUB,
    smBase_costUB, smLog_costUB, smPows_costUB, pa2U, pa2V, pa2Mode,
    natEq,
    letV_costUB, bindV_costUB, caseOptV_costUB,
    findMV_costUB, foldMV_costUB,
    eCaseOpt_costUB, eMap_costUB,
    ddhQ_costUB, litB_costUB, v_costUB,
    Comp.costUB, Expr.costUB,
    List.length_replicate, PNat.val_ofNat,
    bits_0, bits_1, bits_2, bits_32, bits_64, bits_96, bits_128]
  have h : 69 * (min K S.N_dh) ^ 2 = 69 * (min K S.N_dh * min K S.N_dh) := by ring
  nlinarith

theorem fgKeyIndGapDh2Prog_totalCost_le (S : Setup) (b : QueryBudget) :
    (fgKeyIndGapDh2Prog S b.q_total).totalCost b.q_total ≤ stepCostBudget S b := by
  have hI := fgKeyIndGapDh2Prog_init_cost_le S b.q_total
  have hH := gdhHandle2_cost_le_min S b.q_total
  have hF := gdhFinish2_cost_le_min S b.q_total
  have hmax : max 1 ((gdhHandle2 S b.q_total).cost + 32) ≤
      28015 * b.q_total + 27165 * min b.q_total S.N_dh +
        14742 * min b.q_total S.N_sess_tot + 62032 := by omega
  have hq := Nat.mul_le_mul_left b.q_total hmax
  have htot : (fgKeyIndGapDh2Prog S b.q_total).totalCost b.q_total ≤
      b.q_total * (28015 * b.q_total + 27165 * min b.q_total S.N_dh +
        14742 * min b.q_total S.N_sess_tot + 62032) +
        69 * (min b.q_total S.N_dh) ^ 2 + 69 * b.q_total * min b.q_total S.N_dh +
        66 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot +
        423 * min b.q_total S.N_dh + 263 * min b.q_total S.N_sess_tot +
        45 * bits S.N_dh + 2132 * b.q_total + 1029 := by
    change (fgKeyIndGapDh2Prog S b.q_total).init.cost +
      b.q_total * max 1 ((gdhHandle2 S b.q_total).cost + 32) +
      (gdhFinish2 S b.q_total).cost ≤ _
    linarith
  refine htot.trans ?_
  have hbits : bits S.N_dh = Nat.log 2 S.N_dh + 1 := rfl
  rw [hbits]
  dsimp only [stepCostBudget, _root_.SignalPqxdh.Security.stepCostBudget]
  set q := b.q_total
  set md := min b.q_total S.N_dh
  set ms := min b.q_total S.N_sess_tot
  set ld := Nat.log 2 S.N_dh
  set ls := Nat.log 2 S.N_sess_tot
  have hdiff :
      2 ^ 16 * (q + 1) * (q + 1) + 2 ^ 15 * (q + 1) * (md + ms) +
        2 ^ 10 * (q + 1) * (ld + ls) + 2 ^ 11 * md ^ 2 + 2 ^ 8 * md * ms =
      (q * (28015 * q + 27165 * md + 14742 * ms + 62032) +
        69 * md ^ 2 + 69 * q * md + 66 * md * ms + 423 * md + 263 * ms +
        45 * (ld + 1) + 2132 * q + 1029) +
      (37521 * q ^ 2 + 66908 * q + 64462 + 5534 * q * md + 32345 * md +
        18026 * q * ms + 32505 * ms + 1024 * q * ld + 979 * ld +
        1024 * q * ls + 1024 * ls + 1979 * md ^ 2 + 190 * md * ms) := by ring
  omega

/-! ### Syntactic Program-Size Bounds -/

section SizeSimp

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
  {C : ChallengerOracle} {Γ Δ : List PT} {τ τ₁ τ₂ : PT}

@[local simp] private theorem g2_v_size [Ext Γ Δ] (x : Var Γ τ) :
    (v (Δ := Δ) x).size = 1 := rfl
@[local simp] private theorem g2_bindV_size (c : Comp pqxdhOps I Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (bindV c k).size = c.size + (k .zero).size + 1 := rfl
@[local simp] private theorem g2_letV_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (letV (I := I) e k).size = e.size + 1 + (k .zero).size + 1 := rfl
@[local simp] private theorem g2_caseOptV_size (e : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps I Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (caseOptV e kn ks).size = e.size + kn.size + (ks .zero).size + 1 := rfl
@[local simp] private theorem g2_caseSumV_size (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) :
    (caseSumV e kl kr).size = e.size + (kl .zero).size + (kr .zero).size + 1 := rfl
@[local simp] private theorem g2_findMV_size (N : Nat)
    (xs : Expr pqxdhOps Γ (.list τ)) (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (findMV N xs p).size = xs.size + (p .zero).size + bits N + 1 := rfl
@[local simp] private theorem g2_anyMV_size (N : Nat)
    (xs : Expr pqxdhOps Γ (.list τ)) (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (anyMV N xs p).size = xs.size + (p .zero).size + bits N + 1 := rfl
@[local simp] private theorem g2_mapMV_size (N : Nat)
    (xs : Expr pqxdhOps Γ (.list τ₁)) (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (mapMV N xs f).size = xs.size + (f .zero).size + bits N + 1 := rfl
@[local simp] private theorem g2_foldMV_size (N : Nat)
    (xs : Expr pqxdhOps Γ (.list τ₁)) (z : Expr pqxdhOps Γ τ₂)
    (f : Var (τ₁ :: τ₂ :: Γ) τ₁ → Var (τ₁ :: τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₁ :: τ₂ :: Γ) τ₂) :
    (foldMV N xs z f).size = xs.size + z.size + (f .zero (.succ .zero)).size + bits N + 1 := rfl
@[local simp] private theorem g2_eLet_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eLet e k).size = e.size + (k .zero).size + 1 := rfl
@[local simp] private theorem g2_eCaseOpt_size (e : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Expr pqxdhOps Γ τ₂) (ks : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eCaseOpt e kn ks).size = e.size + kn.size + (ks .zero).size + 1 := rfl
@[local simp] private theorem g2_eCaseSum_size (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Expr pqxdhOps (τ₂ :: Γ) τ) :
    (eCaseSum e kl kr).size = e.size + (kl .zero).size + (kr .zero).size + 1 := rfl
@[local simp] private theorem g2_eFind_size (N : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eFind N xs p).size = xs.size + (p .zero).size + bits N + 1 := rfl
@[local simp] private theorem g2_eAny_size (N : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eAny N xs p).size = xs.size + (p .zero).size + bits N + 1 := rfl
@[local simp] private theorem g2_eMap_size (N : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eMap N xs f).size = xs.size + (f .zero).size + bits N + 1 := rfl
@[local simp] private theorem g2_litB_size (w : ℕ+) (bs : Bytes) :
    (litB w bs (Γ := Γ)).size = 2 := rfl
@[local simp] private theorem g2_catB_size {m n : ℕ+}
    (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) :
    (catB a b).size = a.size + b.size + 2 := rfl
@[local simp] private theorem g2_consB_size {w : ℕ+} (b : UInt8) (a : Expr pqxdhOps Γ (B w)) :
    (consB b a).size = a.size + 1 := rfl
@[local simp] private theorem g2_widenB_size (w d : ℕ+) (a : Expr pqxdhOps Γ (B w)) :
    (widenB w d a).size = a.size + 1 := rfl
@[local simp] private theorem g2_takeKB_size (w k : ℕ+) (a : Expr pqxdhOps Γ (B w)) :
    (takeKB w k a).size = a.size + 1 := rfl
@[local simp] private theorem g2_dropB_size {w : ℕ+}
    (n : Expr pqxdhOps Γ .nat) (a : Expr pqxdhOps Γ (B w)) :
    (dropB n a).size = n.size + a.size + 2 := rfl
@[local simp] private theorem g2_lenB_size {w : ℕ+} (a : Expr pqxdhOps Γ (B w)) :
    (lenB a).size = a.size + 1 := rfl
@[local simp] private theorem g2_eqB_size {m n : ℕ+}
    (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) :
    (eqB a b).size = a.size + b.size + 2 := rfl
@[local simp] private theorem g2_u32OfNat_size (n : Expr pqxdhOps Γ .nat) :
    (u32OfNat n).size = n.size + 1 := rfl
@[local simp] private theorem g2_eqU32_size (a b : Expr pqxdhOps Γ U32) :
    (eqU32 a b).size = a.size + b.size + 2 := rfl

private theorem g2_liftBase_size (c : Comp pqxdhOps pqPrimIface Γ τ) :
    (liftBase (C := C) c).size = c.size := by
  induction c <;> simp_all [liftBase, Comp.size, pqChalIface, pqPrimIface]

@[local simp] private theorem g2_gPrim_size (c : Comp pqxdhOps pqPrimIface Γ τ) :
    (gPrim c).size = c.size :=
  g2_liftBase_size c

@[local simp] private theorem g2_sBool_size : (sBool (Γ := Γ)).size = 2 := rfl
@[local simp] private theorem g2_sBytes32_size : (sBytes32 (Γ := Γ)).size = 2 := rfl
@[local simp] private theorem g2_sRandom64_size : (sRandom64 (Γ := Γ)).size = 2 := rfl
@[local simp] private theorem g2_sDrKey96_size : (sDrKey96 (Γ := Γ)).size = 2 := rfl
@[local simp] private theorem g2_sIndex_size (N : ℕ) : (sIndex N (Γ := Γ)).size = 2 := rfl
@[local simp] private theorem g2_qX25519_size (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) :
    (qX25519 e).size = e.size + 1 := rfl
@[local simp] private theorem g2_qX25519Base_size (e : Expr pqxdhOps Γ (B 32)) :
    (qX25519Base e).size = e.size + 1 := rfl
@[local simp] private theorem g2_qIsCanonical_size (e : Expr pqxdhOps Γ (B 32)) :
    (qIsCanonical e).size = e.size + 1 := rfl
@[local simp] private theorem g2_qPow8_size (e : Expr pqxdhOps Γ (B 32)) :
    (qPow8 e).size = e.size + 1 := rfl
@[local simp] private theorem g2_qSigPkGen_size (e : Expr pqxdhOps Γ (B 32)) :
    (qSigPkGen e).size = e.size + 1 := rfl
@[local simp] private theorem g2_qSigSign_size (m : ℕ+)
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigSign m e).size = e.size + 1 := rfl
@[local simp] private theorem g2_qSigVerify_size (m : ℕ+)
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigVerify m e).size = e.size + 1 := rfl
@[local simp] private theorem g2_qKemKeyGen_size (e : Expr pqxdhOps Γ (B 64)) :
    (qKemKeyGen e).size = e.size + 1 := rfl
@[local simp] private theorem g2_qKemEncaps_size (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) :
    (qKemEncaps e).size = e.size + 1 := rfl
@[local simp] private theorem g2_qKemDecaps_size (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) :
    (qKemDecaps e).size = e.size + 1 := rfl
@[local simp] private theorem g2_qHkdfDerive96_size (w : ℕ+) (e : Expr pqxdhOps Γ (B w)) :
    (qHkdfDerive96 w e).size = e.size + 1 := rfl
@[local simp] private theorem g2_ddhQ_size (x y z : Expr pqxdhOps Γ (B 32)) :
    (ddhQ x y z).size = x.size + (y.size + z.size + 1) + 1 + 1 := rfl
@[local simp] private theorem g2_encEC_size (pk : Expr pqxdhOps Γ (B 32)) :
    (encEC pk).size = pk.size + 1 := rfl
@[local simp] private theorem g2_encKEM_size (pk : Expr pqxdhOps Γ (B 1568)) :
    (encKEM pk).size = pk.size + 1 := rfl
@[local simp] private theorem g2_buildSecretsE_size
    (dh1 dh2 dh3 : Expr pqxdhOps Γ (B 32)) (dh4? : Expr pqxdhOps Γ (.opt (B 32)))
    (ss : Expr pqxdhOps Γ (B 32)) :
    (buildSecretsE dh1 dh2 dh3 dh4? ss).size =
      dh1.size + dh2.size + dh3.size + dh4?.size + ss.size + 63 := by
  unfold buildSecretsE eLet2 eCaseOpt eLet widenB catB litB v
  simp only [Expr.size, pqxdhOps, Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
  ring

private theorem bernoulliRatioGdhC_size_le {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).size ≤ 20 := by
  unfold bernoulliRatioGdhC
  split_ifs <;>
    simp [Comp.size, Expr.size]

private theorem coordSamplers2_size_le (S : Setup) {Δ : List PT} :
    (samplePrin2C S (Δ := Δ)).size ≤ 12 ∧
    (sampleSpkPair2C S (Δ := Δ)).size ≤ 18 ∧
    (sampleOpkTriple2C S (Δ := Δ)).size ≤ 24 ∧
    (sampleSendOpkTarget2C S (Δ := Δ)).size ≤ 20 ∧
    (sampleSendNoOpkTarget2C S (Δ := Δ)).size ≤ 20 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold samplePrin2C; split_ifs <;> simp [Comp.size, Expr.size]
  · unfold sampleSpkPair2C; split_ifs <;> simp [Comp.size, Expr.size]
  · unfold sampleOpkTriple2C; split_ifs <;> simp [Comp.size, Expr.size]
  · unfold sampleSendOpkTarget2C; split_ifs <;> simp [Comp.size, Expr.size]
  · unfold sampleSendNoOpkTarget2C; split_ifs <;> simp [Comp.size, Expr.size]

private theorem chooseArm2C_size_le_arms {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT}
    (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ)
    (B1 B2 : Nat)
    (hc1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).size ≤ B1)
    (hc2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).size ≤ B2) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).size ≤ B1 + B2 + 25 := by
  unfold chooseArm2C
  split_ifs with hw1 hw2
  · exact le_trans hc2 (by omega)
  · exact le_trans hc1 (by omega)
  · dsimp only [bindV]
    simp only [Comp.size, g2_v_size]
    have hb := bernoulliRatioGdhC_size_le (Δ := Δ) w1 w2
    have h1 := hc1 (Δ' := .bool :: Δ)
    have h2 := hc2 (Δ' := .bool :: Δ)
    omega

private theorem sampleSendTarget2C_size_le (S : Setup) {Δ : List PT} :
    (sampleSendTarget2C S (Δ := Δ)).size ≤ 65 := by
  unfold sampleSendTarget2C
  split_ifs
  · simp [Comp.size, Expr.size]
  · exact chooseArm2C_size_le_arms S.N_send_opk_tot S.N_send_no_opk_tot _ _ 20 20
      (fun {Δ'} [_] => (coordSamplers2_size_le S (Δ := Δ')).2.2.2.1)
      (fun {Δ'} [_] => (coordSamplers2_size_le S (Δ := Δ')).2.2.2.2)

theorem fgKeyIndGapDh2Prog_init_size_le (S : Setup) (K : Nat) :
    (fgKeyIndGapDh2Prog S K).init.size ≤ 600 := by
  have hArmA : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (bindV (samplePrin2C S) fun pt => bindV (sampleSpkPair2C S) fun st =>
        Comp.ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
          (v pt) (.bool true) .none (v st) (.bool false) .none (.nat 0)) :
        Comp pqxdhOps pqGapDhIface Δ params2Ty).size ≤ 65 := by
    intro Γ₁ Δ _ uv
    simp only [g2_bindV_size, pa2Mk, g2_v_size, Comp.size, Expr.size, bits_0]
    have h1 := (coordSamplers2_size_le S (Δ := Δ)).1
    have h2 := (coordSamplers2_size_le S (Δ := .opt .nat :: Δ)).2.1
    omega
  have hArmC : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (bindV (sampleSendTarget2C S) fun et => bindV (sampleSpkPair2C S) fun st =>
        Comp.ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
          .none (.bool false) (v et) (v st) (.bool false) .none (.nat 1)) :
        Comp pqxdhOps pqGapDhIface Δ params2Ty).size ≤ 120 := by
    intro Γ₁ Δ _ uv
    simp only [g2_bindV_size, pa2Mk, g2_v_size, Comp.size, Expr.size, bits_1]
    have h1 := sampleSendTarget2C_size_le S (Δ := Δ)
    have h2 := (coordSamplers2_size_le S (Δ := .opt ephTargetTy :: Δ)).2.1
    omega
  have hArmB : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (bindV (sampleSendTarget2C S) fun et => bindV (samplePrin2C S) fun pt =>
        Comp.ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.snd (v uv))
          (v pt) (.bool false) (v et) .none (.bool false) .none (.nat 2)) :
        Comp pqxdhOps pqGapDhIface Δ params2Ty).size ≤ 115 := by
    intro Γ₁ Δ _ uv
    simp only [g2_bindV_size, pa2Mk, g2_v_size, Comp.size, Expr.size, bits_2]
    have h1 := sampleSendTarget2C_size_le S (Δ := Δ)
    have h2 := (coordSamplers2_size_le S (Δ := .opt ephTargetTy :: Δ)).1
    omega
  have hArmD : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (bindV (sampleSendOpkTarget2C S) fun et => bindV (sampleOpkTriple2C S) fun ot =>
        Comp.ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
          .none (.bool false) (v et) .none (.bool true) (v ot) (.nat 3)) :
        Comp pqxdhOps pqGapDhIface Δ params2Ty).size ≤ 80 := by
    intro Γ₁ Δ _ uv
    simp only [g2_bindV_size, pa2Mk, g2_v_size, Comp.size, Expr.size, bits_3]
    have h1 := (coordSamplers2_size_le S (Δ := Δ)).2.2.2.1
    have h2 := (coordSamplers2_size_le S (Δ := .opt ephTargetTy :: Δ)).2.2.1
    omega
  have hSubAC : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) (S.N_id * S.N_spk_tot) (S.N_send_tot * S.N_spk_tot)
        (fun {_} [_] => bindV (samplePrin2C S) fun pt => bindV (sampleSpkPair2C S) fun st =>
          .ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
            (v pt) (.bool true) .none (v st) (.bool false) .none (.nat 0)))
        (fun {_} [_] => bindV (sampleSendTarget2C S) fun et => bindV (sampleSpkPair2C S) fun st =>
          .ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
            .none (.bool false) (v et) (v st) (.bool false) .none (.nat 1)))).size ≤ 210 := by
    intro Γ₁ Δ _ uv
    exact chooseArm2C_size_le_arms _ _ _ _ 65 120
      (fun {Δ'} [_] => hArmA (Δ := Δ') uv) (fun {Δ'} [_] => hArmC (Δ := Δ') uv)
  have hSubBD : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) (S.N_send_tot * S.N_id) (S.N_send_opk_tot * S.N_opk_tot)
        (fun {_} [_] => bindV (sampleSendTarget2C S) fun et => bindV (samplePrin2C S) fun pt =>
          .ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.snd (v uv))
            (v pt) (.bool false) (v et) .none (.bool false) .none (.nat 2)))
        (fun {_} [_] => bindV (sampleSendOpkTarget2C S) fun et => bindV (sampleOpkTriple2C S) fun ot =>
          .ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
            .none (.bool false) (v et) .none (.bool true) (v ot) (.nat 3)))).size ≤ 220 := by
    intro Γ₁ Δ _ uv
    exact chooseArm2C_size_le_arms _ _ _ _ 115 80
      (fun {Δ'} [_] => hArmB (Δ := Δ') uv) (fun {Δ'} [_] => hArmD (Δ := Δ') uv)
  have hInitP : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (initParams2C S (Δ := Δ) uv).size ≤ 455 := by
    intro Γ₁ Δ _ uv
    unfold initParams2C
    split_ifs
    · simp only [pa2Mk, g2_v_size, Comp.size, Expr.size, bits_0, bits_3]; omega
    · exact chooseArm2C_size_le_arms _ _ _ _ 210 220
        (fun {Δ'} [_] => hSubAC (Δ := Δ') uv) (fun {Δ'} [_] => hSubBD (Δ := Δ') uv)
  simp only [fgKeyIndGapDh2Prog, initAdv4_2, emptySimE, smMk, emptyStE, stMk,
    g2_letV_size, g2_bindV_size, g2_gPrim_size, g2_sBool_size, g2_v_size, Comp.size, Expr.size]
  have hp := hInitP (Γ₁ := [.prod (B 32) (B 32), .prod (B 32) (B 32)])
    (Δ := [.prod (B 32) (B 32), .prod (B 32) (B 32)]) .zero
  linarith

set_option linter.unusedSimpArgs false in
theorem gdhFinish2_size_le (S : Setup) (K : Nat) :
    (gdhFinish2 S K).size ≤ 30 * bits K + 1500 := by
  simp (config := { maxSteps := 1000000 }) only [
    gdhFinish2, extractMode0_2C, logFind2C, spkPowsC, findMapStep2C,
    initDh1CandC, respDh1CandC, lookupFromPowsE, respBundleKeyE, slice32,
    smBase, smLog, smPows, pa2U, pa2V, pa2Mode,
    stSpks, stSess, stResps,
    sbSpkSk, sbSpkPk, sePeerSpk, seHdr, reSid, reHdr, hdIkAPk,
    natEq, nat2Eq, orE, mulRight, optBytesEq,
    g2_letV_size, g2_bindV_size, g2_caseOptV_size, g2_findMV_size, g2_mapMV_size, g2_foldMV_size,
    g2_eLet_size, g2_eCaseOpt_size, g2_eCaseSum_size, g2_eFind_size, g2_eMap_size,
    g2_gPrim_size, g2_ddhQ_size, g2_qPow8_size, g2_qX25519_size,
    g2_litB_size, g2_takeKB_size, g2_dropB_size, g2_eqB_size,
    g2_v_size, Comp.size, Expr.size,
    bits_0, bits_1, bits_2, bits_3, bits_32, bits_64, bits_96, bits_128, bits_160, bits_192]
  have bMinDh : bits (min K S.N_dh) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  have bMinSess : bits (min K S.N_sess_tot) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  linarith

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3200000 in
theorem gdhHandle2_size_le (S : Setup) (K : Nat) :
    (gdhHandle2 S K).size ≤ 250 * bits K + 25000 := by
  simp (config := { maxSteps := 4000000 }) only [
    gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
    initiateGdh2B, finishAcceptGdhC, acceptOpkGdh2B, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase2, wrapSim2,
    pa2U, pa2V, pa2Up, pa2PrinTarget, pa2DhFlag, pa2EphTarget, pa2SpkTarget,
    pa2OpkMode, pa2OpkTarget, ephSidMatchesE,
    stMk, stUpd, peMk, peUpd, smMk, smUpd, qK, qJ, qO, qHdr, qKJO, rs, slice32,
    rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rDh, rSpkSk,
    smBase, smFgL, smRaw, smLog, smPows,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, sbUpd,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon,
    sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr, seTested, seRevealed, seMk, seUpd,
    reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal, reDrRand,
    reTested, reRevealed, reMk, reUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
    initSidE, respBundleKeyE, natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
    optU32Eq, optBytesEq, isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE,
    nonZero32, orE, mulRight, g2_buildSecretsE_size, g2_encEC_size, g2_encKEM_size, eLet2,
    koskBundleOkPowsC, koskSenderOkPowsC, isAdvPowsE, isAdvRegC,
    resolveSigPkC, lookupSpkSkC, honestPeerC, checkProvC, isGameSpkC, isGameOpkC,
    findHonestC, chooseInitRandC, chooseRespRandC, partnerC, recordRespC, hkdfOrRoC,
    aiIkSk, aiSpkSk, aiOpkSk, aiPqSk, aiReplay, aiHdr, acceptKeysC,
    computePosC, computeOptPosInitC, mkSecretPosC, mkPairPosC, fgPatchC, entryMatchesC,
    ddhEqC, ddhEqOptC, fePos1, fePos2, fePos3, fePos4, feSs, feDk, feMk,
    g2_letV_size, g2_bindV_size, g2_caseOptV_size, g2_caseSumV_size,
    g2_findMV_size, g2_anyMV_size, g2_mapMV_size, g2_foldMV_size,
    g2_eLet_size, g2_eCaseOpt_size, g2_eCaseSum_size, g2_eFind_size, g2_eAny_size, g2_eMap_size,
    g2_gPrim_size, g2_ddhQ_size,
    g2_sBytes32_size, g2_sRandom64_size, g2_sDrKey96_size,
    g2_qX25519_size, g2_qX25519Base_size, g2_qIsCanonical_size, g2_qPow8_size,
    g2_qSigPkGen_size, g2_qSigSign_size, g2_qSigVerify_size,
    g2_qKemKeyGen_size, g2_qKemEncaps_size, g2_qKemDecaps_size, g2_qHkdfDerive96_size,
    g2_litB_size, g2_catB_size, g2_consB_size, g2_widenB_size,
    g2_takeKB_size, g2_dropB_size, g2_lenB_size, g2_eqB_size,
    g2_u32OfNat_size, g2_eqU32_size,
    g2_v_size, Comp.size, Expr.size,
    bits_0, bits_1, bits_2, bits_3, bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
    ↓reduceIte, Bool.false_eq_true]
  have bMinDh : bits (min K S.N_dh) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  have bMinSess : bits (min K S.N_sess_tot) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  linarith

/-- Syntactic AST size bound on `fgKeyIndGapDh2Prog` independent of `S.N_*`. -/
theorem fgKeyIndGapDh2Prog_size_le (S : Setup) (K : Nat) :
    (fgKeyIndGapDh2Prog S K).size ≤ 280 * bits K + 28000 := by
  have hI := fgKeyIndGapDh2Prog_init_size_le S K
  have hH := gdhHandle2_size_le S K
  have hF := gdhFinish2_size_le S K
  change (fgKeyIndGapDh2Prog S K).init.size + (gdhHandle2 S K).size + (gdhFinish2 S K).size ≤ _
  linarith

/-- AST size bound on `fgKeyIndGapDh2Prog` in terms of `bits (stepCostBudget S b)`. -/
theorem fgKeyIndGapDh2Prog_size_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (fgKeyIndGapDh2Prog S b.q_total).size ≤
      28000 + 280 * bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hS := fgKeyIndGapDh2Prog_size_le S b.q_total
  have hq : bits b.q_total ≤ bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
    apply bits_mono
    unfold _root_.SignalPqxdh.Security.stepCostBudget; dsimp only
    have hmul : 2 ^ 16 * (b.q_total + 1) ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega
  linarith

end SizeSimp

/-! ### Simulation Homomorphism (`params2ToFlat`), Bilinear `gdhQueryBudget`, & `GapDH` Equality -/

/-- Well-formedness of a sampled `params2Ty.denote` tuple: either `fgTotalIndexCount S = 0`, or
    every `some` target coordinate lies strictly within its `Setup` range. -/
def InBoundsParams2 (S : Setup) (p : params2Ty.denote) : Prop :=
  fgTotalIndexCount S = 0 ∨
    ((∀ u, p.2.2.2.1 = some u → u < S.N_id) ∧
     (∀ b u i, p.2.2.2.2.2.1 = some (b, (u, i)) →
       u < S.N_id ∧ (if b then i < S.N_send_opk else i < S.N_send_no_opk)) ∧
     (∀ u j, p.2.2.2.2.2.2.1 = some (u, j) → u < S.N_id ∧ j < S.N_recv) ∧
     (∀ u j o, p.2.2.2.2.2.2.2.2.1 = some (u, (j, o)) →
       u < S.N_id ∧ j < S.N_recv ∧ o < S.N_opk))

section EvalHom
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Env.get Ext.wk

@[inline] private def omap {α β : Type} (f : α → β) : Option α → Option β
  | some a => some (f a)
  | none => none

@[inline] private def omap2 {α β γ : Type} (f : α → β → γ) : Option α → Option β → Option γ
  | some a, some b => some (f a b)
  | _, _ => none

@[inline] private def omap3 {α β γ δ : Type} (f : α → β → γ → δ) :
    Option α → Option β → Option γ → Option δ
  | some a, some b, some c => some (f a b c)
  | _, _, _ => none

private theorem omap_eq_some {α β : Type} {f : α → β} {oa : Option α} {y : β}
    (h : omap f oa = some y) : ∃ a, oa = some a ∧ f a = y := by
  cases oa with
  | none => cases h
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

private theorem omap2_eq_some {α β γ : Type} {f : α → β → γ}
    {oa : Option α} {ob : Option β} {y : γ}
    (h : omap2 f oa ob = some y) : ∃ a b, oa = some a ∧ ob = some b ∧ f a b = y := by
  cases oa with
  | none => cases h
  | some a =>
    cases ob with
    | none => cases h
    | some b => exact ⟨a, b, rfl, rfl, Option.some.inj h⟩

private theorem omap3_eq_some {α β γ δ : Type} {f : α → β → γ → δ}
    {oa : Option α} {ob : Option β} {oc : Option γ} {y : δ}
    (h : omap3 f oa ob oc = some y) :
    ∃ a b c, oa = some a ∧ ob = some b ∧ oc = some c ∧ f a b c = y := by
  cases oa with
  | none => cases h
  | some a =>
    cases ob with
    | none => cases h
    | some b =>
      cases oc with
      | none => cases h
      | some c => exact ⟨a, b, c, rfl, rfl, rfl, Option.some.inj h⟩

private inductive TailSwap (T₂ T₁ : List PT) : List PT → List PT → Type where
  | base : TailSwap T₂ T₁ T₂ T₁
  | cons (t : PT) {Γ₂ Γ₁ : List PT} : TailSwap T₂ T₁ Γ₂ Γ₁ → TailSwap T₂ T₁ (t :: Γ₂) (t :: Γ₁)

private inductive EnvSwap {T₂ T₁ : List PT} (τ₂ : Env T₂) (τ₁ : Env T₁) :
    ∀ {Γ₂ Γ₁ : List PT}, TailSwap T₂ T₁ Γ₂ Γ₁ → Env Γ₂ → Env Γ₁ → Prop where
  | base : EnvSwap τ₂ τ₁ .base τ₂ τ₁
  | cons {t : PT} {Γ₂ Γ₁ : List PT} {w : TailSwap T₂ T₁ Γ₂ Γ₁}
      (x : t.denote) {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁} :
      EnvSwap τ₂ τ₁ w ρ₂ ρ₁ → EnvSwap τ₂ τ₁ (w.cons t) (.cons x ρ₂) (.cons x ρ₁)

private def swapVar {T₂ T₁ : List PT} :
    ∀ {Γ₂ Γ₁ : List PT} (_ : TailSwap T₂ T₁ Γ₂ Γ₁) {u : PT},
      Var Γ₂ u → Option (Var Γ₁ u)
  | _, _, .base, _, _ => none
  | _, _, .cons _ _, _, .zero => some .zero
  | _, _, .cons _ w, _, .succ v => omap Var.succ (swapVar w v)

private theorem swapVar_get {T₂ T₁ : List PT} {τ₂ : Env T₂} {τ₁ : Env T₁} :
    ∀ {Γ₂ Γ₁ : List PT} {w : TailSwap T₂ T₁ Γ₂ Γ₁} {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁},
      EnvSwap τ₂ τ₁ w ρ₂ ρ₁ →
      ∀ {u : PT} (v₂ : Var Γ₂ u) {v₁ : Var Γ₁ u},
        swapVar w v₂ = some v₁ → ρ₂.get v₂ = ρ₁.get v₁
  | _, _, .base, _, _, .base, _, _, _, h => by cases h
  | _, _, .cons _ _, _, _, .cons _ _, _, .zero, _, h => by
    cases Option.some.inj h; simp only [Env.get_zero']
  | _, _, .cons _ _, _, _, .cons _ hEnv, _, .succ v₂, _, h => by
    obtain ⟨v₁', hv, rfl⟩ := omap_eq_some h
    simp only [Env.get_succ']
    exact swapVar_get hEnv v₂ hv

private def swapExpr {T₂ T₁ : List PT} :
    ∀ {Γ₂ Γ₁ : List PT} (_ : TailSwap T₂ T₁ Γ₂ Γ₁) {u : PT},
      Expr pqxdhOps Γ₂ u → Option (Expr pqxdhOps Γ₁ u)
  | _, _, w, _, .var x => omap Expr.var (swapVar w x)
  | _, _, _, _, .unit => some .unit
  | _, _, _, _, .bool b => some (.bool b)
  | _, _, _, _, .nat n => some (.nat n)
  | _, _, w, _, .add a b => omap2 Expr.add (swapExpr w a) (swapExpr w b)
  | _, _, w, _, .sub a b => omap2 Expr.sub (swapExpr w a) (swapExpr w b)
  | _, _, w, _, .mulK k a => omap (Expr.mulK k) (swapExpr w a)
  | _, _, w, _, .divK k a => omap (Expr.divK k) (swapExpr w a)
  | _, _, w, _, .modK k a => omap (Expr.modK k) (swapExpr w a)
  | _, _, w, _, .lt a b => omap2 Expr.lt (swapExpr w a) (swapExpr w b)
  | _, _, w, _, .eqN a b => omap2 Expr.eqN (swapExpr w a) (swapExpr w b)
  | _, _, w, _, .not a => omap Expr.not (swapExpr w a)
  | _, _, w, _, .and a b => omap2 Expr.and (swapExpr w a) (swapExpr w b)
  | _, _, w, _, .ite c a b => omap3 Expr.ite (swapExpr w c) (swapExpr w a) (swapExpr w b)
  | _, _, w, _, .pair a b => omap2 Expr.pair (swapExpr w a) (swapExpr w b)
  | _, _, w, _, .fst a => omap Expr.fst (swapExpr w a)
  | _, _, w, _, .snd a => omap Expr.snd (swapExpr w a)
  | _, _, w, _, .inl a => omap Expr.inl (swapExpr w a)
  | _, _, w, _, .inr a => omap Expr.inr (swapExpr w a)
  | _, _, _, _, .none => some .none
  | _, _, w, _, .some a => omap Expr.some (swapExpr w a)
  | _, _, w, _, .caseOpt e n s =>
    omap3 Expr.caseOpt (swapExpr w e) (swapExpr w n) (swapExpr (w.cons _) s)
  | _, _, w, _, .caseSum e l r =>
    omap3 Expr.caseSum (swapExpr w e) (swapExpr (w.cons _) l) (swapExpr (w.cons _) r)
  | _, _, w, _, .letE e b => omap2 Expr.letE (swapExpr w e) (swapExpr (w.cons _) b)
  | _, _, w, _, .op o a => omap (Expr.op o) (swapExpr w a)
  | _, _, _, _, .nil => some .nil
  | _, _, w, _, .cons x l => omap2 Expr.cons (swapExpr w x) (swapExpr w l)
  | _, _, w, _, .len l => omap Expr.len (swapExpr w l)
  | _, _, w, _, .take n l => omap2 Expr.take (swapExpr w n) (swapExpr w l)
  | _, _, w, _, .appendL K a b => omap2 (Expr.appendL K) (swapExpr w a) (swapExpr w b)
  | _, _, w, _, .findB K l p => omap2 (Expr.findB K) (swapExpr w l) (swapExpr (w.cons _) p)
  | _, _, w, _, .anyB K l p => omap2 (Expr.anyB K) (swapExpr w l) (swapExpr (w.cons _) p)
  | _, _, w, _, .mapB K l f => omap2 (Expr.mapB K) (swapExpr w l) (swapExpr (w.cons _) f)
  | _, _, w, _, .foldrB K l z f =>
    omap3 (Expr.foldrB K) (swapExpr w l) (swapExpr w z) (swapExpr ((w.cons _).cons _) f)
  | _, _, w, _, .tconst a => omap Expr.tconst (swapExpr w a)
  | _, _, w, _, .tget m i => omap2 Expr.tget (swapExpr w m) (swapExpr w i)
  | _, _, w, _, .tset m i a => omap3 Expr.tset (swapExpr w m) (swapExpr w i) (swapExpr w a)

private theorem swapExpr_eval {T₂ T₁ : List PT} {τ₂ : Env T₂} {τ₁ : Env T₁}
    {Γ₂ Γ₁ : List PT} {u : PT} (e₂ : Expr pqxdhOps Γ₂ u) :
    ∀ {w : TailSwap T₂ T₁ Γ₂ Γ₁} {e₁ : Expr pqxdhOps Γ₁ u}
      (_ : swapExpr w e₂ = some e₁) {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁}
      (_ : EnvSwap τ₂ τ₁ w ρ₂ ρ₁),
      e₂.eval ρ₂ = e₁.eval ρ₁ := by
  induction e₂ generalizing Γ₁ with
  | var x =>
    intro w e₁ h ρ₂ ρ₁ hEnv
    obtain ⟨x₁, hx, rfl⟩ := omap_eq_some h
    exact swapVar_get hEnv x hx
  | unit | bool _ | nat _ | none | nil =>
    intro w e₁ h ρ₂ ρ₁ _
    cases Option.some.inj h; rfl
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2
  | and _ _ ih1 ih2 | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2
  | appendL _ _ _ ih1 ih2 | tget _ _ ih1 ih2 =>
    intro w e₁ h ρ₂ ρ₁ hEnv
    obtain ⟨a₁, b₁, ha, hb, rfl⟩ := omap2_eq_some h
    simp only [Expr.eval, ih1 ha hEnv, ih2 hb hEnv]
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | op _ _ ih | len _ ih | tconst _ ih =>
    intro w e₁ h ρ₂ ρ₁ hEnv
    obtain ⟨a₁, ha, rfl⟩ := omap_eq_some h
    simp only [Expr.eval, ih ha hEnv]
  | ite _ _ _ ihc iha ihb | tset _ _ _ ihc iha ihb =>
    intro w e₁ h ρ₂ ρ₁ hEnv
    obtain ⟨c₁, a₁, b₁, hc, ha, hb, rfl⟩ := omap3_eq_some h
    simp only [Expr.eval, ihc hc hEnv, iha ha hEnv, ihb hb hEnv]
  | caseOpt _ _ _ ihe ihn ihs =>
    intro w e₁ h ρ₂ ρ₁ hEnv
    obtain ⟨c₁, n₁, s₁, hc, hn, hs, rfl⟩ := omap3_eq_some h
    simp only [Expr.eval, ihe hc hEnv]
    cases c₁.eval ρ₁ with
    | none => exact ihn hn hEnv
    | some x => exact ihs hs (hEnv.cons x)
  | caseSum _ _ _ ihe ihl ihr =>
    intro w e₁ h ρ₂ ρ₁ hEnv
    obtain ⟨c₁, l₁, r₁, hc, hl, hr, rfl⟩ := omap3_eq_some h
    simp only [Expr.eval, ihe hc hEnv]
    cases c₁.eval ρ₁ with
    | inl x => exact ihl hl (hEnv.cons x)
    | inr y => exact ihr hr (hEnv.cons y)
  | letE _ _ ihe ihb =>
    intro w e₁ h ρ₂ ρ₁ hEnv
    obtain ⟨a₁, b₁, ha, hb, rfl⟩ := omap2_eq_some h
    simp only [Expr.eval, ihe ha hEnv]
    exact ihb hb (hEnv.cons _)
  | findB _ _ _ ihl ihp =>
    intro w e₁ h ρ₂ ρ₁ hEnv
    obtain ⟨l₁, p₁, hl, hp, rfl⟩ := omap2_eq_some h
    simp only [Expr.eval, ihl hl hEnv]
    congr 1; funext x; exact ihp hp (hEnv.cons x)
  | anyB _ _ _ ihl ihp =>
    intro w e₁ h ρ₂ ρ₁ hEnv
    obtain ⟨l₁, p₁, hl, hp, rfl⟩ := omap2_eq_some h
    simp only [Expr.eval, ihl hl hEnv]
    congr 1; funext x; exact ihp hp (hEnv.cons x)
  | mapB _ _ _ ihl ihf =>
    intro w e₁ h ρ₂ ρ₁ hEnv
    obtain ⟨l₁, f₁, hl, hf, rfl⟩ := omap2_eq_some h
    simp only [Expr.eval, ihl hl hEnv]
    congr 1; funext x; exact ihf hf (hEnv.cons x)
  | foldrB _ _ _ _ ihl ihz ihf =>
    intro w e₁ h ρ₂ ρ₁ hEnv
    obtain ⟨l₁, z₁, f₁, hl, hz, hf, rfl⟩ := omap3_eq_some h
    simp only [Expr.eval, ihl hl hEnv, ihz hz hEnv]
    congr 1; funext x acc; exact ihf hf ((hEnv.cons acc).cons x)

private def swapComp {ι : Type} {TS : OracleSpec ι} {I : Iface pqSig TS} {T₂ T₁ : List PT} :
    ∀ {Γ₂ Γ₁ : List PT} (_ : TailSwap T₂ T₁ Γ₂ Γ₁) {u : PT},
      Comp pqxdhOps I Γ₂ u → Option (Comp pqxdhOps I Γ₁ u)
  | _, _, w, _, .ret e => omap Comp.ret (swapExpr w e)
  | _, _, w, _, .bind c k => omap2 Comp.bind (swapComp w c) (swapComp (w.cons _) k)
  | _, _, w, _, .ite b c d => omap3 Comp.ite (swapExpr w b) (swapComp w c) (swapComp w d)
  | _, _, w, _, .caseOpt e n s =>
    omap3 Comp.caseOpt (swapExpr w e) (swapComp w n) (swapComp (w.cons _) s)
  | _, _, w, _, .caseSum e l r =>
    omap3 Comp.caseSum (swapExpr w e) (swapComp (w.cons _) l) (swapComp (w.cons _) r)
  | _, _, w, _, .sample s e => omap (Comp.sample s) (swapExpr w e)
  | _, _, w, _, .query g e => omap (Comp.query g) (swapExpr w e)
  | _, _, w, _, .iter n e body => omap2 (Comp.iter n) (swapExpr w e) (swapComp (w.cons _) body)
  | _, _, w, _, .findM K l p => omap2 (Comp.findM K) (swapExpr w l) (swapComp (w.cons _) p)
  | _, _, w, _, .anyM K l p => omap2 (Comp.anyM K) (swapExpr w l) (swapComp (w.cons _) p)
  | _, _, w, _, .mapM K l f => omap2 (Comp.mapM K) (swapExpr w l) (swapComp (w.cons _) f)
  | _, _, w, _, .consumeFirstM K l p mk =>
    omap3 (Comp.consumeFirstM K) (swapExpr w l) (swapComp (w.cons _) p) (swapExpr (w.cons _) mk)
  | _, _, w, _, .foldM K l z f =>
    omap3 (Comp.foldM K) (swapExpr w l) (swapExpr w z) (swapComp ((w.cons _).cons _) f)

private theorem g2_iterM_congr {ι : Type} {TS : OracleSpec ι} {α : Type}
    {f g : α → OracleComp TS α} (h : ∀ a, f a = g a) :
    ∀ (n : ℕ) (a : α), iterM f n a = iterM g n a
  | 0, _ => rfl
  | n + 1, a => by simp only [iterM, h a]; exact bind_congr fun b => g2_iterM_congr h n b

private theorem g2_findML_congr {ι : Type} {TS : OracleSpec ι} {α : Type}
    {p q : α → OracleComp TS Bool} (h : ∀ x, p x = q x) :
    ∀ xs : List α, findML p xs = findML q xs
  | [] => rfl
  | x :: xs => by simp only [findML, h x, g2_findML_congr h xs]

private theorem g2_anyML_congr {ι : Type} {TS : OracleSpec ι} {α : Type}
    {p q : α → OracleComp TS Bool} (h : ∀ x, p x = q x) :
    ∀ xs : List α, anyML p xs = anyML q xs
  | [] => rfl
  | x :: xs => by simp only [anyML, h x, g2_anyML_congr h xs]

private theorem g2_mapML_congr {ι : Type} {TS : OracleSpec ι} {α β : Type}
    {f g : α → OracleComp TS β} (h : ∀ x, f x = g x) :
    ∀ xs : List α, mapML f xs = mapML g xs
  | [] => rfl
  | x :: xs => by simp only [mapML, h x, g2_mapML_congr h xs]

private theorem g2_consumeFirstML_congr {ι : Type} {TS : OracleSpec ι} {α : Type}
    {p q : α → OracleComp TS Bool} {mk₁ mk₂ : α → α}
    (hp : ∀ x, p x = q x) (hm : ∀ x, mk₁ x = mk₂ x) :
    ∀ xs : List α, consumeFirstML p mk₁ xs = consumeFirstML q mk₂ xs
  | [] => rfl
  | x :: xs => by simp only [consumeFirstML, hp x, hm x, g2_consumeFirstML_congr hp hm xs]

private theorem g2_foldML_congr {ι : Type} {TS : OracleSpec ι} {α β : Type}
    {f g : α → β → OracleComp TS β} (h : ∀ x b, f x b = g x b) :
    ∀ (b : β) (xs : List α), foldML f b xs = foldML g b xs
  | _, [] => rfl
  | b, x :: xs => by simp only [foldML, h x b]; exact bind_congr fun b' => g2_foldML_congr h b' xs

private theorem swapComp_eval {ι : Type} {TS : OracleSpec ι} {I : Iface pqSig TS}
    {T₂ T₁ : List PT} {τ₂ : Env T₂} {τ₁ : Env T₁}
    {Γ₂ Γ₁ : List PT} {u : PT} (c₂ : Comp pqxdhOps I Γ₂ u) :
    ∀ {w : TailSwap T₂ T₁ Γ₂ Γ₁} {c₁ : Comp pqxdhOps I Γ₁ u}
      (_ : swapComp w c₂ = some c₁) {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁}
      (_ : EnvSwap τ₂ τ₁ w ρ₂ ρ₁),
      c₂.eval ρ₂ = c₁.eval ρ₁ := by
  induction c₂ generalizing Γ₁ with
  | ret e =>
    intro w c₁ h ρ₂ ρ₁ hEnv
    obtain ⟨e₁, he, rfl⟩ := omap_eq_some h
    simp only [Comp.eval, swapExpr_eval e he hEnv]
  | bind _ _ ihc ihk =>
    intro w c₁ h ρ₂ ρ₁ hEnv
    obtain ⟨a₁, k₁, ha, hk, rfl⟩ := omap2_eq_some h
    simp only [Comp.eval, ihc ha hEnv]
    exact bind_congr fun x => ihk hk (hEnv.cons x)
  | ite _ _ _ iht ihf =>
    intro w c₁ h ρ₂ ρ₁ hEnv
    obtain ⟨b₁, t₁, f₁, hb, ht, hf, rfl⟩ := omap3_eq_some h
    simp only [Comp.eval, swapExpr_eval _ hb hEnv]
    split_ifs <;> [exact iht ht hEnv; exact ihf hf hEnv]
  | caseOpt _ _ _ ihn ihs =>
    intro w c₁ h ρ₂ ρ₁ hEnv
    obtain ⟨e₁, n₁, s₁, he, hn, hs, rfl⟩ := omap3_eq_some h
    simp only [Comp.eval, swapExpr_eval _ he hEnv]
    cases e₁.eval ρ₁ with
    | none => exact ihn hn hEnv
    | some x => exact ihs hs (hEnv.cons x)
  | caseSum _ _ _ ihl ihr =>
    intro w c₁ h ρ₂ ρ₁ hEnv
    obtain ⟨e₁, l₁, r₁, he, hl, hr, rfl⟩ := omap3_eq_some h
    simp only [Comp.eval, swapExpr_eval _ he hEnv]
    cases e₁.eval ρ₁ with
    | inl x => exact ihl hl (hEnv.cons x)
    | inr y => exact ihr hr (hEnv.cons y)
  | sample _ e =>
    intro w c₁ h ρ₂ ρ₁ hEnv
    obtain ⟨e₁, he, rfl⟩ := omap_eq_some h
    dsimp only [Comp.eval]
    rw [swapExpr_eval e he hEnv]
  | query _ e =>
    intro w c₁ h ρ₂ ρ₁ hEnv
    obtain ⟨e₁, he, rfl⟩ := omap_eq_some h
    dsimp only [Comp.eval]
    rw [swapExpr_eval e he hEnv]
  | iter n e _ ihb =>
    intro w c₁ h ρ₂ ρ₁ hEnv
    obtain ⟨e₁, b₁, he, hb, rfl⟩ := omap2_eq_some h
    simp only [Comp.eval, swapExpr_eval e he hEnv]
    exact g2_iterM_congr (fun x => ihb hb (hEnv.cons x)) n _
  | findM _ l _ ihp =>
    intro w c₁ h ρ₂ ρ₁ hEnv
    obtain ⟨l₁, p₁, hl, hp, rfl⟩ := omap2_eq_some h
    simp only [Comp.eval, swapExpr_eval l hl hEnv]
    exact g2_findML_congr (fun x => ihp hp (hEnv.cons x)) _
  | anyM _ l _ ihp =>
    intro w c₁ h ρ₂ ρ₁ hEnv
    obtain ⟨l₁, p₁, hl, hp, rfl⟩ := omap2_eq_some h
    simp only [Comp.eval, swapExpr_eval l hl hEnv]
    exact g2_anyML_congr (fun x => ihp hp (hEnv.cons x)) _
  | mapM _ l _ ihf =>
    intro w c₁ h ρ₂ ρ₁ hEnv
    obtain ⟨l₁, f₁, hl, hf, rfl⟩ := omap2_eq_some h
    simp only [Comp.eval, swapExpr_eval l hl hEnv]
    exact g2_mapML_congr (fun x => ihf hf (hEnv.cons x)) _
  | consumeFirstM _ l _ mk ihp =>
    intro w c₁ h ρ₂ ρ₁ hEnv
    obtain ⟨l₁, p₁, mk₁, hl, hp, hmk, rfl⟩ := omap3_eq_some h
    simp only [Comp.eval, swapExpr_eval l hl hEnv]
    exact g2_consumeFirstML_congr (fun x => ihp hp (hEnv.cons x))
      (fun x => swapExpr_eval mk hmk (hEnv.cons x)) _
  | foldM _ l z _ ihf =>
    intro w c₁ h ρ₂ ρ₁ hEnv
    obtain ⟨l₁, z₁, f₁, hl, hz, hf, rfl⟩ := omap3_eq_some h
    simp only [Comp.eval, swapExpr_eval l hl hEnv, swapExpr_eval z hz hEnv]
    exact g2_foldML_congr (fun x acc => ihf hf ((hEnv.cons acc).cons x)) _ _

private class AutoSwap {T₂ T₁ : outParam (List PT)}
    {τ₂ : outParam (Env T₂)} {τ₁ : outParam (Env T₁)}
    {Γ₂ Γ₁ : List PT} (ρ₂ : Env Γ₂) (ρ₁ : Env Γ₁) where
  w : TailSwap T₂ T₁ Γ₂ Γ₁
  env : EnvSwap τ₂ τ₁ w ρ₂ ρ₁

private instance (priority := 50) autoSwap_base {R₂ R₁ : List PT}
    (ρ₂ : Env (params2Ty :: R₂)) (ρ₁ : Env (paramsTy :: R₁)) :
    @AutoSwap (params2Ty :: R₂) (paramsTy :: R₁) ρ₂ ρ₁ _ _ ρ₂ ρ₁ := ⟨.base, .base⟩

private instance (priority := 100) autoSwap_cons
    {T₂ T₁ : List PT} {τ₂ : Env T₂} {τ₁ : Env T₁}
    {t : PT} {Γ₂ Γ₁ : List PT} {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁} (x : t.denote)
    [h : @AutoSwap T₂ T₁ τ₂ τ₁ Γ₂ Γ₁ ρ₂ ρ₁] :
    @AutoSwap T₂ T₁ τ₂ τ₁ (t :: Γ₂) (t :: Γ₁) (.cons x ρ₂) (.cons x ρ₁) :=
  ⟨h.w.cons t, h.env.cons x⟩

private theorem eval_swap {ι : Type} {TS : OracleSpec ι} {I : Iface pqSig TS}
    {T₂ T₁ : List PT} {τ₂ : Env T₂} {τ₁ : Env T₁}
    {Γ₂ Γ₁ : List PT} {u : PT}
    {c₂ : Comp pqxdhOps I Γ₂ u} {c₁ : Comp pqxdhOps I Γ₁ u}
    {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁}
    [h : @AutoSwap T₂ T₁ τ₂ τ₁ Γ₂ Γ₁ ρ₂ ρ₁]
    (hc : swapComp h.w c₂ = some c₁ := by rfl) :
    c₂.eval ρ₂ = c₁.eval ρ₁ :=
  swapComp_eval c₂ hc h.env

private theorem eval_swap_expr
    {T₂ T₁ : List PT} {τ₂ : Env T₂} {τ₁ : Env T₁}
    {Γ₂ Γ₁ : List PT} {u : PT}
    {e₂ : Expr pqxdhOps Γ₂ u} {e₁ : Expr pqxdhOps Γ₁ u}
    {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁}
    [h : @AutoSwap T₂ T₁ τ₂ τ₁ Γ₂ Γ₁ ρ₂ ρ₁]
    (he : swapExpr h.w e₂ = some e₁ := by rfl) :
    e₂.eval ρ₂ = e₁.eval ρ₁ :=
  swapExpr_eval e₂ he h.env

private theorem step_letV {ι : Type} {TS : OracleSpec ι} {I : Iface pqSig TS}
    {Γ₂ Γ₁ : List PT} {a u : PT}
    {e₂ : Expr pqxdhOps Γ₂ a} {e₁ : Expr pqxdhOps Γ₁ a}
    {k₂ : Var (a :: Γ₂) a → Comp pqxdhOps I (a :: Γ₂) u}
    {k₁ : Var (a :: Γ₁) a → Comp pqxdhOps I (a :: Γ₁) u}
    {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁}
    (he : e₂.eval ρ₂ = e₁.eval ρ₁)
    (hk : ∀ x : a.denote, (k₂ .zero).eval (.cons x ρ₂) = (k₁ .zero).eval (.cons x ρ₁)) :
    (letV e₂ k₂).eval ρ₂ = (letV e₁ k₁).eval ρ₁ := by
  simp only [letV_eval, he]
  exact hk _

private theorem step_bindV {ι : Type} {TS : OracleSpec ι} {I : Iface pqSig TS}
    {Γ₂ Γ₁ : List PT} {a u : PT}
    {c₂ : Comp pqxdhOps I Γ₂ a} {c₁ : Comp pqxdhOps I Γ₁ a}
    {k₂ : Var (a :: Γ₂) a → Comp pqxdhOps I (a :: Γ₂) u}
    {k₁ : Var (a :: Γ₁) a → Comp pqxdhOps I (a :: Γ₁) u}
    {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁}
    (hc : c₂.eval ρ₂ = c₁.eval ρ₁)
    (hk : ∀ x : a.denote, (k₂ .zero).eval (.cons x ρ₂) = (k₁ .zero).eval (.cons x ρ₁)) :
    (bindV c₂ k₂).eval ρ₂ = (bindV c₁ k₁).eval ρ₁ := by
  dsimp only [bindV, Comp.eval]
  rw [hc]
  exact bind_congr hk

private theorem step_ite {ι : Type} {TS : OracleSpec ι} {I : Iface pqSig TS}
    {Γ₂ Γ₁ : List PT} {u : PT}
    {b₂ : Expr pqxdhOps Γ₂ .bool} {b₁ : Expr pqxdhOps Γ₁ .bool}
    {t₂ f₂ : Comp pqxdhOps I Γ₂ u} {t₁ f₁ : Comp pqxdhOps I Γ₁ u}
    {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁}
    (hb : b₂.eval ρ₂ = b₁.eval ρ₁)
    (ht : t₂.eval ρ₂ = t₁.eval ρ₁)
    (hf : f₂.eval ρ₂ = f₁.eval ρ₁) :
    (Comp.ite b₂ t₂ f₂).eval ρ₂ = (Comp.ite b₁ t₁ f₁).eval ρ₁ := by
  dsimp only [Comp.eval]
  rw [hb]
  split_ifs <;> assumption

private theorem step_caseOptV {ι : Type} {TS : OracleSpec ι} {I : Iface pqSig TS}
    {Γ₂ Γ₁ : List PT} {a u : PT}
    {e₂ : Expr pqxdhOps Γ₂ (.opt a)} {e₁ : Expr pqxdhOps Γ₁ (.opt a)}
    {n₂ : Comp pqxdhOps I Γ₂ u} {n₁ : Comp pqxdhOps I Γ₁ u}
    {s₂ : Var (a :: Γ₂) a → Comp pqxdhOps I (a :: Γ₂) u}
    {s₁ : Var (a :: Γ₁) a → Comp pqxdhOps I (a :: Γ₁) u}
    {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁}
    (he : e₂.eval ρ₂ = e₁.eval ρ₁)
    (hn : n₂.eval ρ₂ = n₁.eval ρ₁)
    (hs : ∀ x : a.denote, (s₂ .zero).eval (.cons x ρ₂) = (s₁ .zero).eval (.cons x ρ₁)) :
    (caseOptV e₂ n₂ s₂).eval ρ₂ = (caseOptV e₁ n₁ s₁).eval ρ₁ := by
  dsimp only [caseOptV, Comp.eval]
  rw [he]
  cases e₁.eval ρ₁ with
  | none => exact hn
  | some x => exact hs x

private theorem step_findMV {ι : Type} {TS : OracleSpec ι} {I : Iface pqSig TS}
    {Γ₂ Γ₁ : List PT} {a : PT} {K : Nat}
    {l₂ : Expr pqxdhOps Γ₂ (.list a)} {l₁ : Expr pqxdhOps Γ₁ (.list a)}
    {p₂ : Var (a :: Γ₂) a → Comp pqxdhOps I (a :: Γ₂) .bool}
    {p₁ : Var (a :: Γ₁) a → Comp pqxdhOps I (a :: Γ₁) .bool}
    {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁}
    (hl : l₂.eval ρ₂ = l₁.eval ρ₁)
    (hp : ∀ x : a.denote, (p₂ .zero).eval (.cons x ρ₂) = (p₁ .zero).eval (.cons x ρ₁)) :
    (findMV K l₂ p₂).eval ρ₂ = (findMV K l₁ p₁).eval ρ₁ := by
  dsimp only [findMV, Comp.eval]
  rw [hl]
  exact g2_findML_congr hp _

private theorem step_foldMV {ι : Type} {TS : OracleSpec ι} {I : Iface pqSig TS}
    {Γ₂ Γ₁ : List PT} {a b : PT} {K : Nat}
    {l₂ : Expr pqxdhOps Γ₂ (.list a)} {l₁ : Expr pqxdhOps Γ₁ (.list a)}
    {z₂ : Expr pqxdhOps Γ₂ b} {z₁ : Expr pqxdhOps Γ₁ b}
    {f₂ : Var (a :: b :: Γ₂) a → Var (a :: b :: Γ₂) b → Comp pqxdhOps I (a :: b :: Γ₂) b}
    {f₁ : Var (a :: b :: Γ₁) a → Var (a :: b :: Γ₁) b → Comp pqxdhOps I (a :: b :: Γ₁) b}
    {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁}
    (hl : l₂.eval ρ₂ = l₁.eval ρ₁)
    (hz : z₂.eval ρ₂ = z₁.eval ρ₁)
    (hf : ∀ (x : a.denote) (acc : b.denote),
      (f₂ .zero (.succ .zero)).eval (.cons x (.cons acc ρ₂)) =
        (f₁ .zero (.succ .zero)).eval (.cons x (.cons acc ρ₁))) :
    (foldMV K l₂ z₂ f₂).eval ρ₂ = (foldMV K l₁ z₁ f₁).eval ρ₁ := by
  dsimp only [foldMV, Comp.eval]
  rw [hl, hz]
  exact g2_foldML_congr hf _ _

private theorem logFind2C_eval_eq (K off : Nat)
    {T₂ T₁ Γ₂ Γ₁ : List PT} {τ₂ : Env T₂} {τ₁ : Env T₁}
    {ρ₂ : Env Γ₂} {ρ₁ : Env Γ₁}
    [h : @AutoSwap T₂ T₁ τ₂ τ₁ Γ₂ Γ₁ ρ₂ ρ₁]
    {Γpa₂ Γsm₂ : List PT} [Ext Γpa₂ Γ₂] [Ext Γsm₂ Γ₂]
    (pa₂ : Var Γpa₂ params2Ty) (sm₂ : Var Γsm₂ simTy)
    {Γpa₁ Γsm₁ : List PT} [Ext Γpa₁ Γ₁] [Ext Γsm₁ Γ₁]
    (pa₁ : Var Γpa₁ paramsTy) (sm₁ : Var Γsm₁ simTy)
    (hUV : ∀ z : (B 32).denote,
      (ddhQ (pa2U (v pa₂)) (pa2V (v pa₂)) (v (.zero : Var (B 32 :: Γ₂) (B 32)))).eval (.cons z ρ₂) =
        (ddhQ (paU (v pa₁)) (paV (v pa₁)) (v (.zero : Var (B 32 :: Γ₁) (B 32)))).eval (.cons z ρ₁))
    (hSm : swapExpr h.w
      (eMap K (smLog (v sm₂)) fun sec => slice32 off (v sec)) =
      some (eMap K (smLog (v sm₁)) fun sec => slice32 off (v sec)) := by rfl) :
    (logFind2C K off pa₂ sm₂).eval ρ₂ = (logFindC K off pa₁ sm₁).eval ρ₁ := by
  unfold logFind2C logFindC
  exact step_bindV (step_findMV (eval_swap_expr hSm) hUV) fun found => eval_swap

/-- `gdhFinish2` agrees identically (`=`) in `OracleComp` with `gdhFinish` on `params2ToFlat S pa2`. -/
theorem gdhFinish2_eval_eq (S : Setup) (K : Nat) (pa2 : params2Ty.denote)
    (sm : simTy.denote) (a : Bool) :
    (gdhFinish2 S K).eval (.cons (pa2, sm) (.cons a .nil)) =
      (gdhFinish S K).eval (.cons (params2ToFlat S pa2, sm) (.cons a .nil)) := by
  rcases pa2 with ⟨U, V, Up, pt, df, et, st, om, ot, md⟩
  unfold gdhFinish2 gdhFinish
  simp only [letV_eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', v, Expr.eval]
  refine step_ite
    (by simp only [natEq, pa2Mode, paMode, Expr.eval, params2ToFlat]; rfl) ?_ ?_
  · unfold extractMode0_2C extractMode0C
    refine step_bindV (step_findMV eval_swap_expr fun z => by
      simp only [ddhQ, pa2U, pa2V, paU, paV, v, Expr.eval, Comp.eval,
        Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', params2ToFlat]; rfl) fun f1 => ?_
    refine step_caseOptV eval_swap_expr ?_ fun _ => eval_swap
    refine step_bindV eval_swap fun spkPows => ?_
    refine step_letV eval_swap_expr fun advPows => ?_
    refine step_bindV (step_foldMV eval_swap_expr eval_swap_expr fun s acc => ?_) fun f2 => ?_
    · unfold findMapStep2C findMapStepC
      refine step_caseOptV eval_swap_expr ?_ fun _ => eval_swap
      refine step_bindV eval_swap fun z => ?_
      refine step_bindV ?_ fun ok => eval_swap
      simp only [ddhQ, pa2U, pa2V, paU, paV, v, Expr.eval, Comp.eval,
        Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', params2ToFlat]; rfl
    · refine step_caseOptV eval_swap_expr ?_ fun _ => eval_swap
      refine step_letV eval_swap_expr fun spks => ?_
      refine step_bindV (step_foldMV eval_swap_expr eval_swap_expr fun r acc => ?_) fun f3 => eval_swap
      unfold findMapStep2C findMapStepC
      refine step_caseOptV eval_swap_expr ?_ fun _ => eval_swap
      refine step_bindV eval_swap fun z => ?_
      refine step_bindV ?_ fun ok => eval_swap
      simp only [ddhQ, pa2U, pa2V, paU, paV, v, Expr.eval, Comp.eval,
        Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', params2ToFlat]; rfl
  · refine step_ite
      (by simp only [natEq, pa2Mode, paMode, Expr.eval, params2ToFlat]; rfl) ?_ ?_
    · exact logFind2C_eval_eq K 96 _ _ _ _ (fun z => by
        simp only [ddhQ, pa2U, pa2V, paU, paV, v, Expr.eval, Comp.eval,
          Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', params2ToFlat]; rfl)
    · refine step_ite
        (by simp only [natEq, pa2Mode, paMode, Expr.eval, params2ToFlat]; rfl) ?_ ?_
      · exact logFind2C_eval_eq K 64 _ _ _ _ (fun z => by
          simp only [ddhQ, pa2U, pa2V, paU, paV, v, Expr.eval, Comp.eval,
            Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', params2ToFlat]; rfl)
      · exact logFind2C_eval_eq K 128 _ _ _ _ (fun z => by
          simp only [ddhQ, pa2U, pa2V, paU, paV, v, Expr.eval, Comp.eval,
            Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', params2ToFlat]; rfl)

private def mapGdh2 (S : Setup) (r : keyIndRespTy.denote × gdhState2Ty.denote) :
    keyIndRespTy.denote × gdhStateTy.denote :=
  (r.1, (params2ToFlat S r.2.1, r.2.2))

private theorem wrapSim2_map_eq (S : Setup) {Γpa₂ Γ₂ Γpa₁ Γ₁ : List PT}
    [Ext Γpa₂ Γ₂] [Ext Γpa₁ Γ₁]
    (pa₂ : Var Γpa₂ params2Ty) (c₂ : Comp pqxdhOps pqGapDhIface Γ₂ (.prod keyIndRespTy simTy))
    (pa₁ : Var Γpa₁ paramsTy) (c₁ : Comp pqxdhOps pqGapDhIface Γ₁ (.prod keyIndRespTy simTy))
    (ρ₂ : Env Γ₂) (ρ₁ : Env Γ₁) (pa2 : params2Ty.denote)
    (hpa₂ : ρ₂.get (Ext.wk pa₂) = pa2)
    (hpa₁ : ρ₁.get (Ext.wk pa₁) = params2ToFlat S pa2)
    (hc : c₂.eval ρ₂ = c₁.eval ρ₁) :
    mapGdh2 S <$> (wrapSim2 pa₂ c₂).eval ρ₂ = (wrapSim pa₁ c₁).eval ρ₁ ∧
      ∀ r ∈ support ((wrapSim2 pa₂ c₂).eval ρ₂), r.2.1 = pa2 := by
  unfold wrapSim2 wrapSim mapGdh2
  simp only [bindV, Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ',
    Ext.step_wk', Ext.refl_wk', hpa₂, hpa₁]
  refine ⟨?_, ?_⟩
  · rw [hc, map_eq_bind_pure_comp]
    simp only [bind_assoc, Function.comp_def, pure_bind]
  · intro r hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨x, _, hx⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hx
    subst hx; rfl

private theorem wrapBase2_map_eq (S : Setup) {Γpa₂ Γsm₂ Γ₂ Γpa₁ Γsm₁ Γ₁ : List PT}
    [Ext Γpa₂ Γ₂] [Ext Γsm₂ Γ₂] [Ext Γpa₁ Γ₁] [Ext Γsm₁ Γ₁]
    (pa₂ : Var Γpa₂ params2Ty) (sm₂ : Var Γsm₂ simTy)
    (c₂ : Comp pqxdhOps pqPrimIface Γ₂ (.prod keyIndRespTy keyIndStateTy))
    (pa₁ : Var Γpa₁ paramsTy) (sm₁ : Var Γsm₁ simTy)
    (c₁ : Comp pqxdhOps pqPrimIface Γ₁ (.prod keyIndRespTy keyIndStateTy))
    (ρ₂ : Env Γ₂) (ρ₁ : Env Γ₁) (pa2 : params2Ty.denote) (sm : simTy.denote)
    (hpa₂ : ρ₂.get (Ext.wk pa₂) = pa2)
    (hpa₁ : ρ₁.get (Ext.wk pa₁) = params2ToFlat S pa2)
    (hsm₂ : ρ₂.get (Ext.wk sm₂) = sm)
    (hsm₁ : ρ₁.get (Ext.wk sm₁) = sm)
    (hc : c₂.eval ρ₂ = c₁.eval ρ₁) :
    mapGdh2 S <$> (wrapBase2 pa₂ sm₂ c₂).eval ρ₂ = (wrapBase pa₁ sm₁ c₁).eval ρ₁ ∧
      ∀ r ∈ support ((wrapBase2 pa₂ sm₂ c₂).eval ρ₂), r.2.1 = pa2 := by
  unfold wrapBase2 wrapBase mapGdh2
  have hg : (gPrim c₂).eval ρ₂ = (gPrim c₁).eval ρ₁ := by
    simp only [gPrim_eval, hc]
  simp only [bindV, Comp.eval, v, Expr.eval, smUpd, smMk, smFgL, smRaw, smLog, smPows,
    Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', hpa₂, hpa₁, hsm₂, hsm₁]
  refine ⟨?_, ?_⟩
  · rw [hg, map_eq_bind_pure_comp]
    simp only [bind_assoc, Function.comp_def, pure_bind]
  · intro r hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨x, _, hx⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hx
    subst hx; rfl

private theorem nat_mul_add_eq_iff {N u₁ j₁ u₂ j₂ : ℕ} (hj₁ : j₁ < N) (hj₂ : j₂ < N) :
    u₁ * N + j₁ = u₂ * N + j₂ ↔ u₁ = u₂ ∧ j₁ = j₂ := by
  constructor
  · intro h
    have hu : u₁ = u₂ := by
      rcases lt_trichotomy u₁ u₂ with hlt | rfl | hgt
      · have : (u₁ + 1) * N ≤ u₂ * N := Nat.mul_le_mul_right N hlt
        nlinarith
      · rfl
      · have : (u₂ + 1) * N ≤ u₁ * N := Nat.mul_le_mul_right N hgt
        nlinarith
    subst hu
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩; rfl

private theorem spkTarget_match_eq (S : Setup) (pa2 : params2Ty.denote)
    (hB : InBoundsParams2 S pa2) (u : Fin S.N_id) (j : Fin S.N_recv) :
    (match pa2.2.2.2.2.2.2.1 with
      | none => false
      | some sp => decide (u.val = sp.1) && decide (j.val = sp.2)) =
      decide (Nat.min S.N_recv S.N_spk_tot * u.val + j.val =
        (params2ToFlat S pa2).2.2.2.2.2.2.2.1) := by
  simp only [Nat.mul_comm (Nat.min S.N_recv S.N_spk_tot) u.val]
  have hIdPos : 0 < S.N_id := Nat.pos_of_ne_zero (by have := u.isLt; omega)
  have hRecvPos : 0 < S.N_recv := Nat.pos_of_ne_zero (by have := j.isLt; omega)
  have hSpkPos : 0 < S.N_spk_tot := by unfold Setup.N_spk_tot; exact Nat.mul_pos hIdPos hRecvPos
  have hTotNe : fgTotalIndexCount S ≠ 0 := by
    unfold fgTotalIndexCount
    have := Nat.mul_pos hIdPos hSpkPos
    omega
  have hMinR : Nat.min S.N_recv S.N_spk_tot = S.N_recv := by
    apply Nat.min_eq_left; unfold Setup.N_spk_tot; nlinarith [u.isLt]
  rcases pa2 with ⟨U, V, Up, pt, df, et, st, om, ot, md⟩
  have hSt := (hB.resolve_left hTotNe).2.2.1
  cases st with
  | none =>
    have hlt : u.val * S.N_recv + j.val < S.N_spk_tot := by
      unfold Setup.N_spk_tot
      have := Nat.mul_le_mul_right S.N_recv u.isLt
      nlinarith [j.isLt]
    simp only [params2ToFlat, hMinR, Nat.ne_of_lt hlt, decide_false]
  | some sp =>
    rcases sp with ⟨uT, jT⟩
    obtain ⟨_, hjT⟩ := hSt uT jT rfl
    simp only [params2ToFlat, hMinR]
    by_cases hEq : u.val = uT ∧ j.val = jT
    · rcases hEq with ⟨rfl, rfl⟩; simp
    · have hNe : u.val * S.N_recv + j.val ≠ uT * S.N_recv + jT :=
        fun h => hEq ((nat_mul_add_eq_iff j.isLt hjT).mp h)
      simp only [hNe, decide_false, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      tauto

private theorem opkTarget_match_eq (S : Setup) (pa2 : params2Ty.denote)
    (hB : InBoundsParams2 S pa2) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) :
    (pa2.2.2.2.2.2.2.2.1 &&
      match pa2.2.2.2.2.2.2.2.2.1 with
      | none => false
      | some op =>
        decide (u.val = op.1) && (decide (j.val = op.2.1) && decide (o.val = op.2.2))) =
      ((params2ToFlat S pa2).2.2.2.2.2.2.2.2.1 &&
        decide (Nat.min S.N_opk S.N_opk_tot *
            (Nat.min S.N_recv S.N_spk_tot * u.val + j.val) + o.val =
          (params2ToFlat S pa2).2.2.2.2.2.2.2.2.2.1)) := by
  simp only [Nat.mul_comm (Nat.min S.N_opk S.N_opk_tot),
    Nat.mul_comm (Nat.min S.N_recv S.N_spk_tot) u.val]
  have hIdPos : 0 < S.N_id := Nat.pos_of_ne_zero (by have := u.isLt; omega)
  have hRecvPos : 0 < S.N_recv := Nat.pos_of_ne_zero (by have := j.isLt; omega)
  have hOpkPos : 0 < S.N_opk := Nat.pos_of_ne_zero (by have := o.isLt; omega)
  have hSpkPos : 0 < S.N_spk_tot := by unfold Setup.N_spk_tot; exact Nat.mul_pos hIdPos hRecvPos
  have hTotNe : fgTotalIndexCount S ≠ 0 := by
    unfold fgTotalIndexCount
    have := Nat.mul_pos hIdPos hSpkPos
    omega
  have hMinR : Nat.min S.N_recv S.N_spk_tot = S.N_recv := by
    apply Nat.min_eq_left; unfold Setup.N_spk_tot; nlinarith [u.isLt]
  have hMinO : Nat.min S.N_opk S.N_opk_tot = S.N_opk := by
    apply Nat.min_eq_left; unfold Setup.N_opk_tot; nlinarith [hSpkPos]
  rcases pa2 with ⟨U, V, Up, pt, df, et, st, om, ot, md⟩
  have hOt := (hB.resolve_left hTotNe).2.2.2
  cases om with
  | false => simp [params2ToFlat]
  | true =>
    have hslt : u.val * S.N_recv + j.val < S.N_spk_tot := by
      unfold Setup.N_spk_tot
      have := Nat.mul_le_mul_right S.N_recv u.isLt
      nlinarith [j.isLt]
    cases ot with
    | none =>
      have hlt : (u.val * S.N_recv + j.val) * S.N_opk + o.val < S.N_opk_tot := by
        unfold Setup.N_opk_tot
        have := Nat.mul_le_mul_right S.N_opk hslt
        nlinarith [o.isLt]
      simp [params2ToFlat, hMinR, hMinO, Nat.ne_of_lt hlt]
    | some op =>
      rcases op with ⟨uT, jT, oT⟩
      obtain ⟨_, hjT, hoT⟩ := hOt uT jT oT rfl
      simp only [params2ToFlat, hMinR, hMinO]
      by_cases hEq : u.val = uT ∧ j.val = jT ∧ o.val = oT
      · rcases hEq with ⟨rfl, rfl, rfl⟩; simp
      · have hNe : (u.val * S.N_recv + j.val) * S.N_opk + o.val ≠
            (uT * S.N_recv + jT) * S.N_opk + oT := by
          intro h
          obtain ⟨h1, rfl⟩ := (nat_mul_add_eq_iff o.isLt hoT).mp h
          obtain ⟨rfl, rfl⟩ := (nat_mul_add_eq_iff j.isLt hjT).mp h1
          exact hEq ⟨rfl, rfl, rfl⟩
        simp only [Bool.true_and, hNe, decide_false, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        tauto

private theorem ephTarget_opk_match_eq (S : Setup) (pa2 : params2Ty.denote)
    (hB : InBoundsParams2 S pa2) (u : Fin S.N_id) (i : Fin S.N_send_opk) :
    ((!pa2.2.2.2.2.1) &&
      match pa2.2.2.2.2.2.1 with
      | none => false
      | some t => t.1 && (decide (u.val = t.2.1) && decide (i.val = t.2.2))) =
      ((!(params2ToFlat S pa2).2.2.2.2.2.1) &&
        decide (Nat.min S.N_send_opk S.N_send_opk_tot * u.val + i.val =
          (params2ToFlat S pa2).2.2.2.2.2.2.1)) := by
  simp only [Nat.mul_comm (Nat.min S.N_send_opk S.N_send_opk_tot) u.val]
  have hIdPos : 0 < S.N_id := Nat.pos_of_ne_zero (by have := u.isLt; omega)
  have hSendOpkPos : 0 < S.N_send_opk := Nat.pos_of_ne_zero (by have := i.isLt; omega)
  have hSendPos : 0 < S.N_send_tot := by
    unfold Setup.N_send_tot Setup.N_send_opk_tot
    have := Nat.mul_pos hIdPos hSendOpkPos
    omega
  have hTotNe : fgTotalIndexCount S ≠ 0 := by
    unfold fgTotalIndexCount
    have := Nat.mul_pos hSendPos hIdPos
    omega
  have hMinSO : Nat.min S.N_send_opk S.N_send_opk_tot = S.N_send_opk := by
    apply Nat.min_eq_left; unfold Setup.N_send_opk_tot; nlinarith [u.isLt]
  rcases pa2 with ⟨U, V, Up, pt, df, et, st, om, ot, md⟩
  have hEt := (hB.resolve_left hTotNe).2.1
  cases df with
  | true => simp [params2ToFlat]
  | false =>
    have hslt : u.val * S.N_send_opk + i.val < S.N_send_opk_tot := by
      unfold Setup.N_send_opk_tot
      have := Nat.mul_le_mul_right S.N_send_opk u.isLt
      nlinarith [i.isLt]
    cases et with
    | none =>
      have hlt : u.val * S.N_send_opk + i.val < S.N_send_tot := by
        unfold Setup.N_send_tot; omega
      simp [params2ToFlat, hMinSO, Nat.ne_of_lt hlt]
    | some t =>
      rcases t with ⟨bT, uT, iT⟩
      cases bT with
      | false =>
        have hne : u.val * S.N_send_opk + i.val ≠
            S.N_send_opk_tot + (uT * Nat.min S.N_send_no_opk S.N_send_no_opk_tot + iT) := by
          omega
        simp [params2ToFlat, hMinSO, hne]
      | true =>
        obtain ⟨_, hiT⟩ := hEt true uT iT rfl
        simp only [params2ToFlat, hMinSO, Bool.false_eq_true, ↓reduceIte]
        by_cases hEq : u.val = uT ∧ i.val = iT
        · rcases hEq with ⟨rfl, rfl⟩; simp
        · have hNe : u.val * S.N_send_opk + i.val ≠ uT * S.N_send_opk + iT :=
            fun h => hEq ((nat_mul_add_eq_iff i.isLt hiT).mp h)
          simp only [Bool.not_false, Bool.true_and, hNe, decide_false,
            Bool.and_eq_false_iff, decide_eq_false_iff_not]
          tauto

private theorem ephTarget_noOpk_match_eq (S : Setup) (pa2 : params2Ty.denote)
    (hB : InBoundsParams2 S pa2) (u : Fin S.N_id) (i : Fin S.N_send_no_opk) :
    ((!pa2.2.2.2.2.1) &&
      match pa2.2.2.2.2.2.1 with
      | none => false
      | some t => (!t.1) && (decide (u.val = t.2.1) && decide (i.val = t.2.2))) =
      ((!(params2ToFlat S pa2).2.2.2.2.2.1) &&
        decide (S.N_send_opk_tot +
            (Nat.min S.N_send_no_opk S.N_send_no_opk_tot * u.val + i.val) =
          (params2ToFlat S pa2).2.2.2.2.2.2.1)) := by
  simp only [Nat.mul_comm (Nat.min S.N_send_no_opk S.N_send_no_opk_tot) u.val]
  have hIdPos : 0 < S.N_id := Nat.pos_of_ne_zero (by have := u.isLt; omega)
  have hSendNoOpkPos : 0 < S.N_send_no_opk := Nat.pos_of_ne_zero (by have := i.isLt; omega)
  have hSendPos : 0 < S.N_send_tot := by
    unfold Setup.N_send_tot Setup.N_send_no_opk_tot
    have := Nat.mul_pos hIdPos hSendNoOpkPos
    omega
  have hTotNe : fgTotalIndexCount S ≠ 0 := by
    unfold fgTotalIndexCount
    have := Nat.mul_pos hSendPos hIdPos
    omega
  have hMinSN : Nat.min S.N_send_no_opk S.N_send_no_opk_tot = S.N_send_no_opk := by
    apply Nat.min_eq_left; unfold Setup.N_send_no_opk_tot; nlinarith [u.isLt]
  rcases pa2 with ⟨U, V, Up, pt, df, et, st, om, ot, md⟩
  have hEt := (hB.resolve_left hTotNe).2.1
  cases df with
  | true => simp [params2ToFlat]
  | false =>
    have hslt : u.val * S.N_send_no_opk + i.val < S.N_send_no_opk_tot := by
      unfold Setup.N_send_no_opk_tot
      have := Nat.mul_le_mul_right S.N_send_no_opk u.isLt
      nlinarith [i.isLt]
    cases et with
    | none =>
      have hlt : S.N_send_opk_tot + (u.val * S.N_send_no_opk + i.val) < S.N_send_tot := by
        unfold Setup.N_send_tot Setup.N_send_opk_tot Setup.N_send_no_opk_tot at *
        nlinarith
      simp [params2ToFlat, hMinSN, Nat.ne_of_lt hlt]
    | some t =>
      rcases t with ⟨bT, uT, iT⟩
      cases bT with
      | true =>
        obtain ⟨huT, hiT⟩ := hEt true uT iT rfl
        have huT' : (uT : Nat) < S.N_id := huT
        have hiT' : (iT : Nat) < S.N_send_opk := by simpa using hiT
        have hMinSO : Nat.min S.N_send_opk S.N_send_opk_tot = S.N_send_opk := by
          apply Nat.min_eq_left; unfold Setup.N_send_opk_tot; nlinarith [huT']
        have h1 : (uT : Nat) * S.N_send_opk + S.N_send_opk ≤ S.N_send_opk_tot := by
          have hmul : ((uT : Nat) + 1) * S.N_send_opk ≤ S.N_id * S.N_send_opk :=
            Nat.mul_le_mul_right S.N_send_opk huT'
          have htot : S.N_id * S.N_send_opk = S.N_send_opk_tot := rfl
          simpa [Nat.add_mul, htot] using hmul
        have hne : S.N_send_opk_tot + (u.val * S.N_send_no_opk + i.val) ≠
            (uT : Nat) * S.N_send_opk + (iT : Nat) :=
          Nat.ne_of_gt (Nat.lt_of_lt_of_le
            (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hiT' _) h1)
            (Nat.le_add_right S.N_send_opk_tot _))
        simp [params2ToFlat, hMinSN, hMinSO, hne]
      | false =>
        obtain ⟨_, hiT⟩ := hEt false uT iT rfl
        simp only [params2ToFlat, hMinSN, Bool.false_eq_true, ↓reduceIte]
        by_cases hEq : u.val = uT ∧ i.val = iT
        · rcases hEq with ⟨rfl, rfl⟩; simp
        · have hNe : S.N_send_opk_tot + (u.val * S.N_send_no_opk + i.val) ≠
              S.N_send_opk_tot + (uT * S.N_send_no_opk + iT) := by
            intro h
            have h' : u.val * S.N_send_no_opk + i.val = uT * S.N_send_no_opk + iT := by omega
            exact hEq ((nat_mul_add_eq_iff i.isLt hiT).mp h')
          simp only [Bool.not_false, Bool.true_and, hNe, decide_false,
            Bool.and_eq_false_iff, decide_eq_false_iff_not]
          tauto

private theorem gdhHandle2_initiateOpk_eq (S : Setup) (K : Nat) (pa2 : params2Ty.denote)
    (hB : InBoundsParams2 S pa2) (sm : simTy.denote)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (b : PreKeyBundleInput) :
    (fun r : keyIndRespTy.denote × gdhState2Ty.denote =>
      (r.1, (params2ToFlat S r.2.1, r.2.2))) <$>
      (gdhHandle2 S K).eval
        (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc (.initiateOPK u i b)) .nil)) =
      (gdhHandle S K).eval
        (.cons (params2ToFlat S pa2, sm)
          (.cons ((keyIndCodec S).qenc (.initiateOPK u i b)) .nil)) ∧
    ∀ r ∈ support ((gdhHandle2 S K).eval
      (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc (.initiateOPK u i b)) .nil))),
      r.2.1 = pa2 := by
  simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
    letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase,
    Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
  refine wrapSim2_map_eq S _ _ _ _ _ _ pa2
    (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
    (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']) ?_
  unfold initiateGdh2B initiateGdhB
  dsimp only [ ↓reduceIte ]
  refine step_letV eval_swap_expr fun bu => ?_
  refine step_ite eval_swap_expr eval_swap ?_
  simp only [letV_eval, initSidE, ite_true, v, Expr.eval, Env.get_zero', Env.get_succ',
    Ext.step_wk', Ext.refl_wk']
  refine step_ite eval_swap_expr eval_swap ?_
  refine step_caseOptV eval_swap_expr eval_swap fun ue => ?_
  refine step_bindV eval_swap fun ok => ?_
  refine step_ite eval_swap_expr eval_swap ?_
  refine step_letV ?_ fun isTE => ?_
  · simp only [ephSidMatchesE, eCaseOpt, eCaseSum, pa2DhFlag, pa2EphTarget,
      paDhFlag, paEphIdx, initSlotIdxE, mulRight, nat2Eq, natEq, v, Expr.eval,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
    refine Eq.trans ?_ (Eq.trans (ephTarget_opk_match_eq S pa2 hB u i) ?_)
    · cases pa2.2.2.2.2.2.1 with
      | none => rfl
      | some t => cases t.1 <;> rfl
    · rfl
  · refine step_bindV eval_swap fun ekSkRaw => ?_
    refine step_bindV eval_swap fun coins => ?_
    refine step_bindV eval_swap fun sigPk => ?_
    refine step_bindV eval_swap fun v1 => ?_
    refine step_bindV eval_swap fun v2 => ?_
    refine step_ite eval_swap_expr eval_swap ?_
    refine step_bindV eval_swap fun krOpt => ?_
    refine step_caseOptV eval_swap_expr eval_swap fun kr => ?_
    refine step_bindV eval_swap fun ekPkRaw => ?_
    refine step_letV eval_swap_expr fun ekSk => ?_
    refine step_letV ?_ fun ekPk => eval_swap
    rcases pa2 with ⟨U, V, Up, pt, df, et, st, om, ot, md⟩
    simp only [pa2U, paU, Expr.eval, Env.get_zero', Env.get_succ', params2ToFlat]

private theorem gdhHandle2_initiateNoOpk_eq (S : Setup) (K : Nat) (pa2 : params2Ty.denote)
    (hB : InBoundsParams2 S pa2) (sm : simTy.denote)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput) :
    (fun r : keyIndRespTy.denote × gdhState2Ty.denote =>
      (r.1, (params2ToFlat S r.2.1, r.2.2))) <$>
      (gdhHandle2 S K).eval
        (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc (.initiateNoOPK u i b)) .nil)) =
      (gdhHandle S K).eval
        (.cons (params2ToFlat S pa2, sm)
          (.cons ((keyIndCodec S).qenc (.initiateNoOPK u i b)) .nil)) ∧
    ∀ r ∈ support ((gdhHandle2 S K).eval
      (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc (.initiateNoOPK u i b)) .nil))),
      r.2.1 = pa2 := by
  simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
    letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase,
    Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
  refine wrapSim2_map_eq S _ _ _ _ _ _ pa2
    (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
    (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']) ?_
  unfold initiateGdh2B initiateGdhB
  dsimp only [ Bool.false_eq_true, ↓reduceIte ]
  refine step_letV eval_swap_expr fun bu => ?_
  refine step_ite eval_swap_expr eval_swap ?_
  simp only [letV_eval, initSidE, Bool.false_eq_true, ite_false, v, Expr.eval,
    Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
  refine step_ite eval_swap_expr eval_swap ?_
  refine step_caseOptV eval_swap_expr eval_swap fun ue => ?_
  refine step_bindV eval_swap fun ok => ?_
  refine step_ite eval_swap_expr eval_swap ?_
  refine step_letV ?_ fun isTE => ?_
  · simp only [ephSidMatchesE, eCaseOpt, eCaseSum, pa2DhFlag, pa2EphTarget,
      paDhFlag, paEphIdx, initSlotIdxE, mulRight, nat2Eq, natEq, v, Expr.eval,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
    refine Eq.trans ?_ (Eq.trans (ephTarget_noOpk_match_eq S pa2 hB u i) ?_)
    · cases pa2.2.2.2.2.2.1 with
      | none => rfl
      | some t => cases t.1 <;> rfl
    · rfl
  · refine step_bindV eval_swap fun ekSkRaw => ?_
    refine step_bindV eval_swap fun coins => ?_
    refine step_bindV eval_swap fun sigPk => ?_
    refine step_bindV eval_swap fun v1 => ?_
    refine step_bindV eval_swap fun v2 => ?_
    refine step_ite eval_swap_expr eval_swap ?_
    refine step_bindV eval_swap fun krOpt => ?_
    refine step_caseOptV eval_swap_expr eval_swap fun kr => ?_
    refine step_bindV eval_swap fun ekPkRaw => ?_
    refine step_letV eval_swap_expr fun ekSk => ?_
    refine step_letV ?_ fun ekPk => eval_swap
    rcases pa2 with ⟨U, V, Up, pt, df, et, st, om, ot, md⟩
    simp only [pa2U, paU, Expr.eval, Env.get_zero', Env.get_succ', params2ToFlat]

private theorem gdhHandle2_acceptOpk_eq (S : Setup) (K : Nat) (pa2 : params2Ty.denote)
    (sm : simTy.denote)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (h : HandshakeHdr) :
    (fun r : keyIndRespTy.denote × gdhState2Ty.denote =>
      (r.1, (params2ToFlat S r.2.1, r.2.2))) <$>
      (gdhHandle2 S K).eval
        (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc (.acceptOPK k j o h)) .nil)) =
      (gdhHandle S K).eval
        (.cons (params2ToFlat S pa2, sm)
          (.cons ((keyIndCodec S).qenc (.acceptOPK k j o h)) .nil)) ∧
    ∀ r ∈ support ((gdhHandle2 S K).eval
      (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc (.acceptOPK k j o h)) .nil))),
      r.2.1 = pa2 := by
  simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
    letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase,
    Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
  refine wrapSim2_map_eq S _ _ _ _ _ _ pa2
    (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
    (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']) ?_
  unfold acceptOpkGdh2B acceptOpkGdhB
  refine step_ite eval_swap_expr eval_swap ?_
  refine step_ite eval_swap_expr eval_swap ?_
  refine step_bindV eval_swap fun sOk => ?_
  refine step_ite eval_swap_expr eval_swap ?_
  refine step_caseOptV eval_swap_expr eval_swap fun ke => ?_
  refine step_caseOptV eval_swap_expr eval_swap fun be => ?_
  refine step_caseOptV eval_swap_expr eval_swap fun oe => ?_
  refine step_ite eval_swap_expr eval_swap ?_
  refine step_letV eval_swap_expr fun kybR => ?_
  refine step_bindV eval_swap fun canon => ?_
  refine step_bindV eval_swap fun dh1Z => ?_
  refine step_bindV eval_swap fun dh2Z => ?_
  refine step_ite ?_ ?_ ?_
  · rcases pa2 with ⟨U, V, Up, pt, df, et, st, om, ot, md⟩
    simp only [pa2OpkMode, paOpkMode, v, Expr.eval, Env.get_zero', Env.get_succ',
      Ext.step_wk', Ext.refl_wk', params2ToFlat]
  · refine step_bindV eval_swap fun ssOpt => ?_
    refine step_ite eval_swap_expr eval_swap ?_
    refine step_caseOptV eval_swap_expr eval_swap fun ss => ?_
    refine step_bindV eval_swap fun p1 => ?_
    refine step_bindV eval_swap fun p2 => ?_
    refine step_bindV eval_swap fun p3 => ?_
    refine step_bindV eval_swap fun p4Raw => ?_
    refine step_letV eval_swap_expr fun p4 => ?_
    refine step_bindV eval_swap fun patchR => eval_swap
  · refine step_bindV eval_swap fun dh4 => ?_
    refine step_bindV eval_swap fun ssOpt => ?_
    refine step_ite eval_swap_expr eval_swap ?_
    refine step_caseOptV eval_swap_expr eval_swap fun ss => ?_
    refine step_bindV eval_swap fun p1 => ?_
    refine step_bindV eval_swap fun p2 => ?_
    refine step_bindV eval_swap fun p3 => ?_
    refine step_bindV eval_swap fun p4Raw => ?_
    refine step_letV eval_swap_expr fun p4 => ?_
    refine step_bindV eval_swap fun patchR => eval_swap

private theorem gdhHandle2_acceptNoOpk_eq (S : Setup) (K : Nat) (pa2 : params2Ty.denote)
    (sm : simTy.denote)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (h : HandshakeHdr) :
    (fun r : keyIndRespTy.denote × gdhState2Ty.denote =>
      (r.1, (params2ToFlat S r.2.1, r.2.2))) <$>
      (gdhHandle2 S K).eval
        (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc (.acceptNoOPK k j l h)) .nil)) =
      (gdhHandle S K).eval
        (.cons (params2ToFlat S pa2, sm)
          (.cons ((keyIndCodec S).qenc (.acceptNoOPK k j l h)) .nil)) ∧
    ∀ r ∈ support ((gdhHandle2 S K).eval
      (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc (.acceptNoOPK k j l h)) .nil))),
      r.2.1 = pa2 := by
  simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
    letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase,
    Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
  refine wrapSim2_map_eq S _ _ _ _ _ _ pa2
    (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
    (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']) ?_
  unfold acceptNoOpkGdhB
  refine step_ite eval_swap_expr eval_swap ?_
  refine step_ite eval_swap_expr eval_swap ?_
  refine step_bindV eval_swap fun sOk => ?_
  refine step_ite eval_swap_expr eval_swap ?_
  refine step_caseOptV eval_swap_expr eval_swap fun ke => ?_
  refine step_caseOptV eval_swap_expr eval_swap fun be => ?_
  refine step_letV eval_swap_expr fun kybR => ?_
  refine step_bindV eval_swap fun canon => ?_
  refine step_bindV eval_swap fun dh1Z => ?_
  refine step_bindV eval_swap fun dh2Z => ?_
  refine step_bindV eval_swap fun ssOpt => ?_
  refine step_ite eval_swap_expr eval_swap eval_swap

set_option maxHeartbeats 400000 in
/-- `gdhHandle2` agrees identically (`=`) in `OracleComp` (modulo `params2ToFlat S`) with `gdhHandle`
    on every valid `KeyIndQuery S` whenever `InBoundsParams2 S pa2` holds. -/
theorem gdhHandle2_eval_map_eq (S : Setup) (K : Nat) (pa2 : params2Ty.denote)
    (hB : InBoundsParams2 S pa2) (sm : simTy.denote) (gq : KeyIndQuery S) :
    (fun r : keyIndRespTy.denote × gdhState2Ty.denote =>
      (r.1, (params2ToFlat S r.2.1, r.2.2))) <$>
      (gdhHandle2 S K).eval (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc gq) .nil)) =
      (gdhHandle S K).eval
        (.cons (params2ToFlat S pa2, sm) (.cons ((keyIndCodec S).qenc gq) .nil)) ∧
    ∀ r ∈ support ((gdhHandle2 S K).eval (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc gq) .nil))),
      r.2.1 = pa2 := by
  cases gq with
  | initPrin u =>
    simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
      letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
    refine wrapSim2_map_eq S _ _ _ _ _ _ pa2
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']) ?_
    unfold initPrinGdh2B initPrinGdhB
    refine step_ite eval_swap_expr eval_swap ?_
    refine step_letV ?_ fun isT => ?_
    · rcases pa2 with ⟨U, V, Up, pt, df, et, st, om, ot, md⟩
      simp only [eCaseOpt, pa2PrinTarget, paPrinFlag, paPrinIdx, natEq, v, Expr.eval,
        Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', params2ToFlat]
      cases pt with
      | none => simp
      | some _ => simp; rfl
    · refine step_bindV eval_swap fun sk0 => ?_
      refine step_bindV eval_swap fun pk0 => ?_
      refine step_bindV eval_swap fun skS => ?_
      refine step_bindV eval_swap fun pkS => ?_
      refine step_letV eval_swap_expr fun sec0 => ?_
      refine step_letV ?_ fun ikPk => eval_swap
      rcases pa2 with ⟨U, V, Up, pt, df, et, st, om, ot, md⟩
      simp only [pa2Up, paUp, v, Expr.eval, Env.get_zero', Env.get_succ',
        Ext.step_wk', Ext.refl_wk', params2ToFlat]
  | corruptIK u =>
    simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
      letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
    exact wrapBase2_map_eq S _ _ _ _ _ _ _ _ pa2 sm
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      eval_swap
  | genSPK u j =>
    simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
      letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
    refine wrapSim2_map_eq S _ _ _ _ _ _ pa2
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']) ?_
    unfold genSpkGdh2B genSpkGdhB
    refine step_ite eval_swap_expr eval_swap ?_
    refine step_caseOptV eval_swap_expr eval_swap fun ue => ?_
    refine step_letV ?_ fun isT => ?_
    · simp only [eCaseOpt, pa2SpkTarget, paSpkIdx, spkFlatIdxE, mulRight, nat2Eq, natEq,
        v, Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
      refine Eq.trans ?_ (Eq.trans (spkTarget_match_eq S pa2 hB u j) ?_)
      · cases pa2.2.2.2.2.2.2.1 <;> rfl
      · rfl
    · refine step_bindV eval_swap fun spkSkRaw => ?_
      refine step_bindV eval_swap fun spkPkRaw => ?_
      refine step_letV eval_swap_expr fun spkSk => ?_
      refine step_letV ?_ fun spkPk => eval_swap
      rcases pa2 with ⟨U, V, Up, pt, df, et, st, om, ot, md⟩
      simp only [pa2V, paV, v, Expr.eval, Env.get_zero', Env.get_succ',
        Ext.step_wk', Ext.refl_wk', params2ToFlat]
  | genOPK u j o =>
    simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
      letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
    refine wrapSim2_map_eq S _ _ _ _ _ _ pa2
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']) ?_
    unfold genOpkGdh2B genOpkGdhB
    refine step_ite eval_swap_expr eval_swap ?_
    refine step_letV ?_ fun isT => ?_
    · simp only [eCaseOpt, pa2OpkMode, pa2OpkTarget, paOpkMode, paOpkIdx, opkFlatIdxE,
        spkFlatIdxE, mulRight, nat3Eq, nat2Eq, natEq, v, Expr.eval,
        Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
      refine Eq.trans ?_ (Eq.trans (opkTarget_match_eq S pa2 hB u j o) ?_)
      · cases pa2.2.2.2.2.2.2.2.2.1 <;> rfl
      · rfl
    · refine step_bindV eval_swap fun opkSkRaw => ?_
      refine step_bindV eval_swap fun opkPkRaw => ?_
      refine step_letV eval_swap_expr fun opkSk => ?_
      refine step_letV ?_ fun opkPk => eval_swap
      rcases pa2 with ⟨U, V, Up, pt, df, et, st, om, ot, md⟩
      simp only [pa2V, paV, v, Expr.eval, Env.get_zero', Env.get_succ',
        Ext.step_wk', Ext.refl_wk', params2ToFlat]
  | initiateOPK u i b => exact gdhHandle2_initiateOpk_eq S K pa2 hB sm u i b
  | initiateNoOPK u i b => exact gdhHandle2_initiateNoOpk_eq S K pa2 hB sm u i b
  | acceptOPK k j o h => exact gdhHandle2_acceptOpk_eq S K pa2 sm k j o h
  | acceptNoOPK k j l h => exact gdhHandle2_acceptNoOpk_eq S K pa2 sm k j l h
  | testSession sid =>
    simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
      letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
    exact wrapBase2_map_eq S _ _ _ _ _ _ _ _ pa2 sm
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      eval_swap
  | roQuery sec =>
    simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
      letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
    exact wrapSim2_map_eq S _ _ _ _ _ _ pa2
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      eval_swap
  | revealDhSecrets =>
    simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
      letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase, rNone,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
      map_pure, support_pure, Set.mem_singleton_iff]
    exact ⟨trivial, fun _ hr => by subst hr; rfl⟩
  | revealSessionKey sid =>
    simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
      letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
    exact wrapBase2_map_eq S _ _ _ _ _ _ _ _ pa2 sm
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      eval_swap
  | registerKey sk =>
    simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
      letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
    exact wrapSim2_map_eq S _ _ _ _ _ _ pa2
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      eval_swap
  | revealSpkSk u j =>
    simp only [gdhHandle2, gdhHandle, keyIndCodec, keyIndQenc,
      letV_eval, caseSumV, Comp.eval, v, Expr.eval, smBase,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
    exact wrapBase2_map_eq S _ _ _ _ _ _ _ _ pa2 sm
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      (by simp only [Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk'])
      eval_swap

end EvalHom

/-! ### Tuple-Keyed Parameter Distribution, Query-Bound Transfer, and `GapDH` Equivalence -/

section TupleKeyedEvalDist
set_option linter.style.haveILetI false

private def paramsFlatVal2 (S : Setup) (U V : Bytes) (idx : Nat) : paramsTy.denote :=
  let nA := S.N_id * S.N_spk_tot
  let nC := S.N_send_tot * S.N_spk_tot
  let nB := S.N_send_tot * S.N_id
  if idx < nA then
    paramsDhVal S true (idx / S.N_spk_tot) (idx % S.N_spk_tot) U V
  else if idx < nA + nC then
    let r := idx - nA
    paramsDhVal S false (r / S.N_spk_tot) (r % S.N_spk_tot) U V
  else if idx < nA + nC + nB then
    let r := idx - (nA + nC)
    paramsIkVal S (r / S.N_id) (r % S.N_id) U V
  else
    let r := idx - (nA + nC + nB)
    paramsOpkVal S (r / S.N_opk_tot) (r % S.N_opk_tot) U V

private def runFromFlat (S : Setup) (K : Nat) (mx : OracleComp (unifSpec + keyIndSpec S) Bool)
    (x0 : gdhStateTy.denote) : OracleComp GdhSimSpec Bytes := do
  let (b, s') ← (simulateQ (handlerImpl (C := keyIndCodec S) (gdhHandle S K)) mx).run x0
  (gdhFinish S K).eval (.cons s' (.cons b .nil))

private def runFromTuple (S : Setup) (K : Nat) (mx : OracleComp (unifSpec + keyIndSpec S) Bool)
    (x0 : gdhState2Ty.denote) : OracleComp GdhSimSpec Bytes := do
  let (b, s') ← (simulateQ (handlerImpl (C := keyIndCodec S) (gdhHandle2 S K)) mx).run x0
  (gdhFinish2 S K).eval (.cons s' (.cons b .nil))

private theorem runFromTuple_eq_runFromFlat (S : Setup) (K : Nat)
    (hHandle : ∀ pa2, InBoundsParams2 S pa2 → ∀ sm gq,
      (fun r : keyIndRespTy.denote × gdhState2Ty.denote =>
        (r.1, (params2ToFlat S r.2.1, r.2.2))) <$>
        (gdhHandle2 S K).eval (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc gq) .nil)) =
        (gdhHandle S K).eval
          (.cons (params2ToFlat S pa2, sm) (.cons ((keyIndCodec S).qenc gq) .nil)) ∧
      ∀ r ∈ support ((gdhHandle2 S K).eval (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc gq) .nil))),
        r.2.1 = pa2)
    (hFinish : ∀ pa2 sm a,
      (gdhFinish2 S K).eval (.cons (pa2, sm) (.cons a .nil)) =
        (gdhFinish S K).eval (.cons (params2ToFlat S pa2, sm) (.cons a .nil)))
    (mx : OracleComp (unifSpec + keyIndSpec S) Bool)
    (pa2 : params2Ty.denote) (hB : InBoundsParams2 S pa2) (sm : simTy.denote) :
    runFromTuple S K mx (pa2, sm) = runFromFlat S K mx (params2ToFlat S pa2, sm) := by
  induction mx using OracleComp.inductionOn generalizing sm with
  | pure a =>
    simp only [runFromTuple, runFromFlat, simulateQ_pure, StateT.run_pure, pure_bind]
    exact hFinish pa2 sm a
  | query_bind q k ih =>
    rcases q with uq | gq
    · unfold runFromTuple runFromFlat
      rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
      change (((pqGapDhIface.fwdU uq >>= fun u => pure (u, (pa2, sm))) >>= fun x =>
          (simulateQ (handlerImpl (C := keyIndCodec S) (gdhHandle2 S K)) (k x.1)).run x.2) >>=
          fun bs => (gdhFinish2 S K).eval (.cons bs.2 (.cons bs.1 .nil))) =
        (((pqGapDhIface.fwdU uq >>= fun u => pure (u, (params2ToFlat S pa2, sm))) >>= fun x =>
          (simulateQ (handlerImpl (C := keyIndCodec S) (gdhHandle S K)) (k x.1)).run x.2) >>=
          fun bs => (gdhFinish S K).eval (.cons bs.2 (.cons bs.1 .nil)))
      simp only [bind_assoc, pure_bind]
      exact bind_congr fun u => ih u sm
    · obtain ⟨hEq, hSup⟩ := hHandle pa2 hB sm gq
      unfold runFromTuple runFromFlat
      rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
      change (((do let p ← (gdhHandle2 S K).eval (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc gq) .nil))
                   pure ((keyIndCodec S).rdec gq p.1, p.2)) >>= fun x =>
          (simulateQ (handlerImpl (C := keyIndCodec S) (gdhHandle2 S K)) (k x.1)).run x.2) >>=
          fun bs => (gdhFinish2 S K).eval (.cons bs.2 (.cons bs.1 .nil))) =
        (((do let p ← (gdhHandle S K).eval (.cons (params2ToFlat S pa2, sm) (.cons ((keyIndCodec S).qenc gq) .nil))
              pure ((keyIndCodec S).rdec gq p.1, p.2)) >>= fun x =>
          (simulateQ (handlerImpl (C := keyIndCodec S) (gdhHandle S K)) (k x.1)).run x.2) >>=
          fun bs => (gdhFinish S K).eval (.cons bs.2 (.cons bs.1 .nil)))
      rw [← hEq]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      refine bind_congr_of_forall_mem_support _ fun r hr => ?_
      have hr2 : r.2 = (pa2, r.2.2) := Prod.ext (hSup r hr) rfl
      rw [hr2]
      exact ih ((keyIndCodec S).rdec gq r.1) r.2.2

private theorem unifGdh_pure {α : Type} (a : α) :
    unifGdh (pure a) = (pure a : OracleComp GdhSimSpec α) := rfl

private theorem unifGdh_query_bind {α : Type} (q : unifSpec.Domain)
    (c : unifSpec.Range q → ProbComp α) :
    unifGdh (liftM (OracleSpec.query (spec := unifSpec) q) >>= c) =
      (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inl q))) >>=
        fun u => unifGdh (c u)) := rfl

private theorem unifGdh_bind {α β : Type} (m : ProbComp α) (f : α → ProbComp β) :
    unifGdh (m >>= f) = (unifGdh m >>= fun x => unifGdh (f x)) := by
  induction m using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [bind_assoc, unifGdh_query_bind, unifGdh_query_bind, bind_assoc]
    exact bind_congr ih

private theorem simulateQ_unifGdh {α : Type} (P : Primitives)
    (ddhImpl : QueryImpl gapDhOracleSpec ProbComp) (mx : ProbComp α) :
    simulateQ (primBaseImpl P + ddhImpl) (unifGdh mx) = mx := by
  induction mx using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [unifGdh_query_bind, simulateQ_bind]
    have hq : simulateQ (primBaseImpl P + ddhImpl)
        (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inl q)))) =
        liftM (OracleSpec.query q) := by
      rw [simulateQ_query]
      simp [primBaseImpl]
    rw [hq]
    exact bind_congr ih

private theorem mem_support_unifGdh {α : Type} (mx : ProbComp α) (x : α) :
    x ∈ support (unifGdh mx) ↔ x ∈ support mx := by
  induction mx using OracleComp.inductionOn with
  | pure a => simp [unifGdh_pure]
  | query_bind q k ih =>
    rw [unifGdh_query_bind, mem_support_bind_iff, mem_support_bind_iff]
    simp only [support_query, Set.mem_univ, true_and]
    exact exists_congr ih

private theorem isQueryBoundP_of_bind_mem_support {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {α β : Type} {m : OracleComp spec α} {f : α → OracleComp spec β}
    {p : ι → Prop} [DecidablePred p] {B : Nat}
    (h : IsQueryBoundP (m >>= f) p B) :
    ∀ x ∈ support m, IsQueryBoundP (f x) p B := by
  induction m using OracleComp.inductionOn generalizing B with
  | pure a =>
    intro x hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    simpa only [pure_bind] using h
  | query_bind q k ih =>
    intro x hx
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
    rw [mem_support_bind_iff] at hx
    rcases hx with ⟨u, _, hxu⟩
    by_cases hp : p q
    · simp only [hp, ↓reduceIte] at h
      exact (ih u (h.2 u) x hxu).mono (Nat.sub_le B 1)
    · simp only [hp, ↓reduceIte] at h
      exact ih u (h.2 u) x hxu

private theorem isQueryBoundP_unifGdh_bind {α β : Type} (mx : ProbComp α)
    (f : α → OracleComp GdhSimSpec β) (B : Nat)
    (hf : ∀ x ∈ support mx, IsQueryBoundP (f x) (fun q => q.isRight = true) B) :
    IsQueryBoundP (unifGdh mx >>= f) (fun q => q.isRight = true) B := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    rw [unifGdh_pure, pure_bind]
    exact hf a (by simp)
  | query_bind q k ih =>
    rw [unifGdh_query_bind, bind_assoc, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp), fun u => ?_⟩
    simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte]
    exact ih u fun x hx => hf x (by
      rw [mem_support_bind_iff]
      exact ⟨u, by simp, hx⟩)

private noncomputable def bernoulliRatioProb (A B : Nat) : ProbComp Bool :=
  if A = 0 then pure false
  else if B = 0 then pure true
  else if A ≤ B then do
    let x ← FgGapDh.sampleIndexRange (A + B)
    let y1 ← FgGapDh.sampleIndexRange A
    let y2 ← FgGapDh.sampleIndexRange A
    pure (decide (x < y1 + y2 + 1))
  else do
    let x ← FgGapDh.sampleIndexRange (A + B)
    let y1 ← FgGapDh.sampleIndexRange B
    let y2 ← FgGapDh.sampleIndexRange B
    pure (!decide (x < y1 + y2 + 1))

private noncomputable def chooseArm2Prob {α : Type} (w1 w2 : Nat)
    (m1 m2 : ProbComp α) : ProbComp α :=
  if w1 = 0 then m2
  else if w2 = 0 then m1
  else do
    let b ← bernoulliRatioProb w1 w2
    if b then m1 else m2

private noncomputable def samplePrin2Prob (S : Setup) : ProbComp (Option Nat) :=
  if S.N_id = 0 then pure none
  else do
    let u ← FgGapDh.sampleIndexRange S.N_id
    pure (some u)

private noncomputable def sampleSpkPair2Prob (S : Setup) : ProbComp (Option (Nat × Nat)) :=
  if S.N_spk_tot = 0 then pure none
  else do
    let u ← FgGapDh.sampleIndexRange S.N_id
    let j ← FgGapDh.sampleIndexRange S.N_recv
    pure (some (u, j))

private noncomputable def sampleOpkTriple2Prob (S : Setup) :
    ProbComp (Option (Nat × (Nat × Nat))) :=
  if S.N_opk_tot = 0 then pure none
  else do
    let u ← FgGapDh.sampleIndexRange S.N_id
    let j ← FgGapDh.sampleIndexRange S.N_recv
    let o ← FgGapDh.sampleIndexRange S.N_opk
    pure (some (u, (j, o)))

private noncomputable def sampleSendOpkTarget2Prob (S : Setup) :
    ProbComp (Option (Bool × (Nat × Nat))) :=
  if S.N_send_opk_tot = 0 then pure none
  else do
    let u ← FgGapDh.sampleIndexRange S.N_id
    let i ← FgGapDh.sampleIndexRange S.N_send_opk
    pure (some (true, (u, i)))

private noncomputable def sampleSendNoOpkTarget2Prob (S : Setup) :
    ProbComp (Option (Bool × (Nat × Nat))) :=
  if S.N_send_no_opk_tot = 0 then pure none
  else do
    let u ← FgGapDh.sampleIndexRange S.N_id
    let i ← FgGapDh.sampleIndexRange S.N_send_no_opk
    pure (some (false, (u, i)))

private noncomputable def sampleSendTarget2Prob (S : Setup) :
    ProbComp (Option (Bool × (Nat × Nat))) :=
  if S.N_send_tot = 0 then pure none
  else chooseArm2Prob S.N_send_opk_tot S.N_send_no_opk_tot
    (sampleSendOpkTarget2Prob S) (sampleSendNoOpkTarget2Prob S)

private noncomputable def initParams2Prob (S : Setup) (U V : Bytes) : ProbComp params2Ty.denote :=
  if fgTotalIndexCount S = 0 then
    pure (U, V, U, none, false, some (true, 0, 0), none, true, some (0, 0, 0), 3)
  else
    let nA := S.N_id * S.N_spk_tot
    let nC := S.N_send_tot * S.N_spk_tot
    let nB := S.N_send_tot * S.N_id
    let nD := S.N_send_opk_tot * S.N_opk_tot
    chooseArm2Prob (nA + nC) (nB + nD)
      (chooseArm2Prob nA nC
        (do let pt ← samplePrin2Prob S
            let st ← sampleSpkPair2Prob S
            pure (U, V, U, pt, true, none, st, false, none, 0))
        (do let et ← sampleSendTarget2Prob S
            let st ← sampleSpkPair2Prob S
            pure (U, V, U, none, false, et, st, false, none, 1)))
      (chooseArm2Prob nB nD
        (do let et ← sampleSendTarget2Prob S
            let pt ← samplePrin2Prob S
            pure (U, V, V, pt, false, et, none, false, none, 2))
        (do let et ← sampleSendOpkTarget2Prob S
            let ot ← sampleOpkTriple2Prob S
            pure (U, V, U, none, false, et, none, true, ot, 3)))

section EvalInitBridge
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Env.get Ext.wk

private theorem initParamsFlat_eval2 (S : Setup) {Γ : List PT}
    (U V : Expr pqxdhOps Γ (B 32)) (idx : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (initParamsFlat S U V idx).eval env =
      paramsFlatVal2 S (U.eval env) (V.eval env) (idx.eval env) := by
  simp only [initParamsFlat, paramsFlatVal2, initParamsDh_eval, initParamsIk_eval,
    initParamsOpk_eval, Expr.eval]
  split_ifs <;> simp_all

private theorem emptySimE_eval2 {S : Setup} {Γ : List PT} (secb : Expr pqxdhOps Γ .bool) (env : Env Γ) :
    (emptySimE secb).eval env =
      simStateToVal (_root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty S
        (secb.eval env)) := by
  simp [emptySimE, emptyStE, smMk, stMk, Expr.eval, simStateToVal,
    _root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty,
    keyIndStateToVal, KeyIndState.empty]

private theorem fgKeyIndGapDhProg_eval_runFromFlat (S : Setup) (K : Nat)
    (mx : OracleComp (unifSpec + keyIndSpec S) Bool) (U V : Bytes) :
    (fgKeyIndGapDhProg S K).eval (fun _ => mx) (U, V) =
      (do
        let idx ← unifGdh (FgGapDh.sampleIndexRange (fgTotalIndexCount S))
        let secb ← unifGdh ($ᵗ Bool)
        runFromFlat S K mx
          (paramsFlatVal2 S U V idx,
            simStateToVal (FgGapDh.FgKeyIndSimState.empty S secb))) := by
  simp only [CostedReduction.eval, CostedReduction.impl, fgKeyIndGapDhProg, initAdv4, bindV,
    letV_eval, Comp.eval, gPrim_eval, sIndex_eval, sBool_eval, initParamsFlat_eval2,
    emptySimE_eval2 (S := S), v, Expr.eval, Env.get_zero', Env.get_succ',
    Ext.step_wk', Ext.refl_wk', unifGdh, FgGapDh_embedPrim_eq, FgGapDh_embedUnif_eq,
    bind_assoc, pure_bind]
  rfl

private theorem gPrim_sIndex_eval {Δ : List PT} (N : Nat) (env : Env Δ) :
    (gPrim (sIndex N)).eval env = unifGdh (FgGapDh.sampleIndexRange N) := by
  simp [sIndex_eval, unifGdh]

private theorem bernoulliRatioGdhC_eval (A B : Nat) {Δ : List PT} (env : Env Δ) :
    (bernoulliRatioGdhC A B).eval env = unifGdh (bernoulliRatioProb A B) := by
  unfold bernoulliRatioGdhC bernoulliRatioProb
  by_cases hA : A = 0
  · simp only [hA, ↓reduceIte, Comp.eval, Expr.eval, unifGdh_pure]
  · by_cases hB : B = 0
    · simp only [hA, hB, ↓reduceIte, Comp.eval, Expr.eval, unifGdh_pure]
    · by_cases hAB : A ≤ B <;>
        · simp only [hA, hB, hAB, ↓reduceIte, bindV, v, gPrim_sIndex_eval, Comp.eval, Expr.eval,
            Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
            unifGdh_bind, unifGdh_pure]
          rfl

private theorem chooseArm2C_eval {Γ₁ Δ : List PT} {α : PT} [Ext Γ₁ Δ] (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' α)
    (m1 m2 : ProbComp α.denote) (env : Env Δ)
    (hc1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'] (env' : Env Δ'),
      (∀ {τ} (x : Var Γ₁ τ), env'.get (Ext.wk x) = env.get (Ext.wk x)) →
      (c1 (Δ' := Δ')).eval env' = unifGdh m1)
    (hc2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'] (env' : Env Δ'),
      (∀ {τ} (x : Var Γ₁ τ), env'.get (Ext.wk x) = env.get (Ext.wk x)) →
      (c2 (Δ' := Δ')).eval env' = unifGdh m2) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).eval env =
      unifGdh (chooseArm2Prob w1 w2 m1 m2) := by
  unfold chooseArm2C chooseArm2Prob
  by_cases h1 : w1 = 0
  · simp only [h1, ↓reduceIte]
    exact hc2 env (fun _ => rfl)
  · by_cases h2 : w2 = 0
    · simp only [h1, h2, ↓reduceIte]
      exact hc1 env (fun _ => rfl)
    · simp only [h1, h2, ↓reduceIte, bindV, v, Comp.eval, Expr.eval,
        bernoulliRatioGdhC_eval, Env.get_zero', Ext.refl_wk', unifGdh_bind]
      refine bind_congr fun b => ?_
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine hc2 _ fun x => ?_
        simp [Ext.step_wk', Env.get_succ']
      · simp only [↓reduceIte]
        refine hc1 _ fun x => ?_
        simp [Ext.step_wk', Env.get_succ']

private theorem samplePrin2C_eval (S : Setup) {Δ : List PT} (env : Env Δ) :
    (samplePrin2C S).eval env = unifGdh (samplePrin2Prob S) := by
  unfold samplePrin2C samplePrin2Prob
  split_ifs <;>
    simp only [bindV, v, gPrim_sIndex_eval, Comp.eval, Expr.eval,
      Env.get_zero', Ext.refl_wk', unifGdh_bind, unifGdh_pure]

private theorem sampleSpkPair2C_eval (S : Setup) {Δ : List PT} (env : Env Δ) :
    (sampleSpkPair2C S).eval env = unifGdh (sampleSpkPair2Prob S) := by
  unfold sampleSpkPair2C sampleSpkPair2Prob
  split_ifs <;>
    simp only [bindV, v, gPrim_sIndex_eval, Comp.eval, Expr.eval,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
      unifGdh_bind, unifGdh_pure]

private theorem sampleOpkTriple2C_eval (S : Setup) {Δ : List PT} (env : Env Δ) :
    (sampleOpkTriple2C S).eval env = unifGdh (sampleOpkTriple2Prob S) := by
  unfold sampleOpkTriple2C sampleOpkTriple2Prob
  split_ifs <;>
    simp only [bindV, v, gPrim_sIndex_eval, Comp.eval, Expr.eval,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
      unifGdh_bind, unifGdh_pure]

private theorem sampleSendOpkTarget2C_eval (S : Setup) {Δ : List PT} (env : Env Δ) :
    (sampleSendOpkTarget2C S).eval env = unifGdh (sampleSendOpkTarget2Prob S) := by
  unfold sampleSendOpkTarget2C sampleSendOpkTarget2Prob
  split_ifs <;>
    simp only [bindV, v, gPrim_sIndex_eval, Comp.eval, Expr.eval,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
      unifGdh_bind, unifGdh_pure]

private theorem sampleSendNoOpkTarget2C_eval (S : Setup) {Δ : List PT} (env : Env Δ) :
    (sampleSendNoOpkTarget2C S).eval env = unifGdh (sampleSendNoOpkTarget2Prob S) := by
  unfold sampleSendNoOpkTarget2C sampleSendNoOpkTarget2Prob
  split_ifs <;>
    simp only [bindV, v, gPrim_sIndex_eval, Comp.eval, Expr.eval,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
      unifGdh_bind, unifGdh_pure]

private theorem sampleSendTarget2C_eval (S : Setup) {Δ : List PT} (env : Env Δ) :
    (sampleSendTarget2C S).eval env = unifGdh (sampleSendTarget2Prob S) := by
  unfold sampleSendTarget2C sampleSendTarget2Prob
  by_cases h0 : S.N_send_tot = 0
  · simp [h0, Comp.eval, Expr.eval, unifGdh_pure]
  · simp only [h0, ↓reduceIte]
    exact chooseArm2C_eval (Γ₁ := Δ) (Δ := Δ) S.N_send_opk_tot S.N_send_no_opk_tot _ _ _ _ env
      (fun env' _ => sampleSendOpkTarget2C_eval S env')
      (fun env' _ => sampleSendNoOpkTarget2C_eval S env')

private theorem initParams2C_eval (S : Setup) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (B 32) (B 32))) (env : Env Δ) (U V : Bytes)
    (huv : env.get (Ext.wk uv) = (U, V)) :
    (initParams2C S uv).eval env = unifGdh (initParams2Prob S U V) := by
  unfold initParams2C initParams2Prob
  by_cases h0 : fgTotalIndexCount S = 0
  · simp [h0, pa2Mk, v, Comp.eval, Expr.eval, huv, unifGdh_pure]
  · simp only [h0, ↓reduceIte]
    refine chooseArm2C_eval (Γ₁ := Γ₁) _ _ _ _ _ _ env (fun env1 h1 => ?_) (fun env1 h1 => ?_)
    · refine chooseArm2C_eval (Γ₁ := Γ₁) _ _ _ _ _ _ env1 (fun env2 h2 => ?_) (fun env2 h2 => ?_)
      · have huv2 : env2.get (Ext.wk uv) = (U, V) := (h2 uv).trans ((h1 uv).trans huv)
        simp only [bindV, pa2Mk, v, Comp.eval, Expr.eval,
          samplePrin2C_eval, sampleSpkPair2C_eval,
          Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', huv2,
          unifGdh_bind, unifGdh_pure]
      · have huv2 : env2.get (Ext.wk uv) = (U, V) := (h2 uv).trans ((h1 uv).trans huv)
        simp only [bindV, pa2Mk, v, Comp.eval, Expr.eval,
          sampleSendTarget2C_eval, sampleSpkPair2C_eval,
          Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', huv2,
          unifGdh_bind, unifGdh_pure]
    · refine chooseArm2C_eval (Γ₁ := Γ₁) _ _ _ _ _ _ env1 (fun env2 h2 => ?_) (fun env2 h2 => ?_)
      · have huv2 : env2.get (Ext.wk uv) = (U, V) := (h2 uv).trans ((h1 uv).trans huv)
        simp only [bindV, pa2Mk, v, Comp.eval, Expr.eval,
          sampleSendTarget2C_eval, samplePrin2C_eval,
          Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', huv2,
          unifGdh_bind, unifGdh_pure]
      · have huv2 : env2.get (Ext.wk uv) = (U, V) := (h2 uv).trans ((h1 uv).trans huv)
        simp only [bindV, pa2Mk, v, Comp.eval, Expr.eval,
          sampleSendOpkTarget2C_eval, sampleOpkTriple2C_eval,
          Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', huv2,
          unifGdh_bind, unifGdh_pure]

private theorem fgKeyIndGapDh2Prog_eval_runFromTuple (S : Setup) (K : Nat)
    (mx : OracleComp (unifSpec + keyIndSpec S) Bool) (U V : Bytes) :
    (fgKeyIndGapDh2Prog S K).eval (fun _ => mx) (U, V) =
      (do
        let pa2 ← unifGdh (initParams2Prob S U V)
        let secb ← unifGdh ($ᵗ Bool)
        runFromTuple S K mx
          (pa2, simStateToVal (FgGapDh.FgKeyIndSimState.empty S secb))) := by
  have hInit := initParams2C_eval S (Γ₁ := [.prod (B 32) (B 32), .prod (B 32) (B 32)])
    (Δ := [.prod (B 32) (B 32), .prod (B 32) (B 32)]) .zero
    (.cons (U, V) (.cons (U, V) .nil)) U V rfl
  simp only [CostedReduction.eval, CostedReduction.impl, fgKeyIndGapDh2Prog, initAdv4_2, bindV,
    letV_eval, Comp.eval, gPrim_eval, sBool_eval, emptySimE_eval2 (S := S),
    v, Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
    hInit, unifGdh, FgGapDh_embedPrim_eq, FgGapDh_embedUnif_eq,
    bind_assoc, pure_bind]
  rfl

set_option allowUnsafeReducibility true in
attribute [local semireducible] Env.get Ext.wk
end EvalInitBridge

/-! ### Explicit Flat-to-Tuple Bijection `params2OfFlat` and Distribution Helpers -/

private def spk2OfFlat (S : Setup) (s : Nat) : Option (Nat × Nat) :=
  some (s / S.N_recv, s % S.N_recv)

private def opk2OfFlat (S : Setup) (oIdx : Nat) : Option (Nat × (Nat × Nat)) :=
  some ((oIdx / S.N_opk) / S.N_recv, ((oIdx / S.N_opk) % S.N_recv, oIdx % S.N_opk))

private def sendOpk2OfFlat (S : Setup) (t : Nat) : Option (Bool × (Nat × Nat)) :=
  some (true, (t / S.N_send_opk, t % S.N_send_opk))

private def sendNoOpk2OfFlat (S : Setup) (r : Nat) : Option (Bool × (Nat × Nat)) :=
  some (false, (r / S.N_send_no_opk, r % S.N_send_no_opk))

private def send2OfFlat (S : Setup) (t : Nat) : Option (Bool × (Nat × Nat)) :=
  if t < S.N_send_opk_tot then sendOpk2OfFlat S t else sendNoOpk2OfFlat S (t - S.N_send_opk_tot)

private def params2OfFlat (S : Setup) (U V : Bytes) (idx : Nat) : params2Ty.denote :=
  if fgTotalIndexCount S = 0 then
    (U, (V, (U, (none, (false, (some (true, (0, 0)), (none, (true, (some (0, (0, 0)), 3)))))))))
  else
    let nA := S.N_id * S.N_spk_tot
    let nC := S.N_send_tot * S.N_spk_tot
    let nB := S.N_send_tot * S.N_id
    if idx < nA then
      (U, (V, (U, (some (idx / S.N_spk_tot),
        (true, (none, (spk2OfFlat S (idx % S.N_spk_tot), (false, (none, 0)))))))))
    else if idx < nA + nC then
      let r := idx - nA
      (U, (V, (U, (none,
        (false, (send2OfFlat S (r / S.N_spk_tot), (spk2OfFlat S (r % S.N_spk_tot), (false, (none, 1)))))))))
    else if idx < nA + nC + nB then
      let r := idx - (nA + nC)
      (U, (V, (V, (some (r % S.N_id),
        (false, (send2OfFlat S (r / S.N_id), (none, (false, (none, 2)))))))))
    else
      let r := idx - (nA + nC + nB)
      (U, (V, (U, (none,
        (false, (sendOpk2OfFlat S (r / S.N_opk_tot), (none, (true, (opk2OfFlat S (r % S.N_opk_tot), 3)))))))))

private theorem mem_support_sampleIndexRange_lt {N x : ℕ} (hN : 0 < N)
    (hx : x ∈ support (FgGapDh.sampleIndexRange N)) : x < N := by
  simp only [FgGapDh.sampleIndexRange, hN, ↓reduceDIte, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨i, _, rfl⟩
  exact i.isLt

private theorem mem_support_sampleIndexRange_of_lt {N x : ℕ} (hx : x < N) :
    x ∈ support (FgGapDh.sampleIndexRange N) := by
  have hN : 0 < N := by omega
  simp only [FgGapDh.sampleIndexRange, hN, ↓reduceDIte, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff]
  exact ⟨⟨x, hx⟩, by simp, rfl⟩

private theorem div_lt_of_lt_mul {a m n : ℕ} (h : a < m * n) : a / n < m := by
  have hmn : m * n ≠ 0 := by omega
  have hn : 0 < n := Nat.pos_of_mul_pos_left (Nat.pos_of_ne_zero hmn)
  exact (Nat.div_lt_iff_lt_mul hn).mpr h

private theorem mod_lt_of_lt_mul {a m n : ℕ} (h : a < m * n) : a % n < n := by
  have hmn : m * n ≠ 0 := by omega
  exact Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Nat.pos_of_ne_zero hmn))

private theorem div_mul_add_mod_eq (a n : ℕ) : (a / n) * n + a % n = a := by
  rw [Nat.mul_comm, Nat.div_add_mod]

private theorem min_send_opk {S : Setup} (h : 0 < S.N_send_opk_tot) :
    S.N_send_opk.min S.N_send_opk_tot = S.N_send_opk := by
  unfold Setup.N_send_opk_tot at h ⊢
  exact Nat.min_eq_left (Nat.le_mul_of_pos_left _ (Nat.pos_of_mul_pos_right h))

private theorem min_send_no_opk {S : Setup} (h : 0 < S.N_send_no_opk_tot) :
    S.N_send_no_opk.min S.N_send_no_opk_tot = S.N_send_no_opk := by
  unfold Setup.N_send_no_opk_tot at h ⊢
  exact Nat.min_eq_left (Nat.le_mul_of_pos_left _ (Nat.pos_of_mul_pos_right h))

private theorem min_spk_recv {S : Setup} (h : 0 < S.N_spk_tot) :
    S.N_recv.min S.N_spk_tot = S.N_recv := by
  unfold Setup.N_spk_tot at h ⊢
  exact Nat.min_eq_left (Nat.le_mul_of_pos_left _ (Nat.pos_of_mul_pos_right h))

private theorem min_opk_slot {S : Setup} (h : 0 < S.N_opk_tot) :
    S.N_opk.min S.N_opk_tot = S.N_opk := by
  unfold Setup.N_opk_tot at h ⊢
  exact Nat.min_eq_left (Nat.le_mul_of_pos_left _ (Nat.pos_of_mul_pos_right h))

private theorem spk2OfFlat_inBounds {S : Setup} {s u j : ℕ}
    (hs : s < S.N_spk_tot) (hEq : spk2OfFlat S s = some (u, j)) :
    u < S.N_id ∧ j < S.N_recv := by
  simp only [spk2OfFlat, Option.some.injEq, Prod.mk.injEq] at hEq
  rcases hEq with ⟨rfl, rfl⟩
  exact ⟨div_lt_of_lt_mul hs, mod_lt_of_lt_mul hs⟩

private theorem opk2OfFlat_inBounds {S : Setup} {oIdx u j o : ℕ}
    (ho : oIdx < S.N_opk_tot) (hEq : opk2OfFlat S oIdx = some (u, (j, o))) :
    u < S.N_id ∧ j < S.N_recv ∧ o < S.N_opk := by
  simp only [opk2OfFlat, Option.some.injEq, Prod.mk.injEq] at hEq
  rcases hEq with ⟨rfl, rfl, rfl⟩
  have hs : oIdx / S.N_opk < S.N_spk_tot := div_lt_of_lt_mul ho
  exact ⟨div_lt_of_lt_mul hs, mod_lt_of_lt_mul hs, mod_lt_of_lt_mul ho⟩

private theorem sendOpk2OfFlat_inBounds {S : Setup} {t : ℕ} {b : Bool} {u i : ℕ}
    (ht : t < S.N_send_opk_tot) (hEq : sendOpk2OfFlat S t = some (b, (u, i))) :
    u < S.N_id ∧ (if b then i < S.N_send_opk else i < S.N_send_no_opk) := by
  simp only [sendOpk2OfFlat, Option.some.injEq, Prod.mk.injEq] at hEq
  rcases hEq with ⟨rfl, rfl, rfl⟩
  exact ⟨div_lt_of_lt_mul ht, by simp [mod_lt_of_lt_mul ht]⟩

private theorem send2OfFlat_inBounds {S : Setup} {t : ℕ} {b : Bool} {u i : ℕ}
    (ht : t < S.N_send_tot) (hEq : send2OfFlat S t = some (b, (u, i))) :
    u < S.N_id ∧ (if b then i < S.N_send_opk else i < S.N_send_no_opk) := by
  unfold send2OfFlat at hEq
  by_cases hlt : t < S.N_send_opk_tot
  · simp only [hlt, ↓reduceIte] at hEq
    exact sendOpk2OfFlat_inBounds hlt hEq
  · simp only [hlt, ↓reduceIte] at hEq
    have hr : t - S.N_send_opk_tot < S.N_send_no_opk_tot := by
      unfold Setup.N_send_tot at ht; omega
    simp only [sendNoOpk2OfFlat, Option.some.injEq, Prod.mk.injEq] at hEq
    rcases hEq with ⟨rfl, rfl, rfl⟩
    exact ⟨div_lt_of_lt_mul hr, by simp [mod_lt_of_lt_mul hr]⟩

private theorem params2OfFlat_inBounds (S : Setup) (U V : Bytes) (idx : Nat)
    (hIdx : idx ∈ support (FgGapDh.sampleIndexRange (fgTotalIndexCount S))) :
    InBoundsParams2 S (params2OfFlat S U V idx) := by
  by_cases h0 : fgTotalIndexCount S = 0
  · exact Or.inl h0
  · right
    have hLt : idx < fgTotalIndexCount S :=
      mem_support_sampleIndexRange_lt (Nat.pos_of_ne_zero h0) hIdx
    unfold params2OfFlat
    dsimp only
    simp only [h0, ↓reduceIte]
    by_cases h1 : idx < S.N_id * S.N_spk_tot
    · simp only [h1, ↓reduceIte]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro u hu; simp only [Option.some.injEq] at hu; subst hu; exact div_lt_of_lt_mul h1
      · intro _ _ _ h; cases h
      · intro u j h; exact spk2OfFlat_inBounds (mod_lt_of_lt_mul h1) h
      · intro _ _ _ h; cases h
    · by_cases h2 : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot
      · simp only [h1, h2, ↓reduceIte]
        have hr : idx - S.N_id * S.N_spk_tot < S.N_send_tot * S.N_spk_tot := by omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro _ h; cases h
        · intro b u i h; exact send2OfFlat_inBounds (div_lt_of_lt_mul hr) h
        · intro u j h; exact spk2OfFlat_inBounds (mod_lt_of_lt_mul hr) h
        · intro _ _ _ h; cases h
      · by_cases h3 : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id
        · simp only [h1, h2, h3, ↓reduceIte]
          have hr : idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) <
              S.N_send_tot * S.N_id := by omega
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro u hu; simp only [Option.some.injEq] at hu; subst hu; exact mod_lt_of_lt_mul hr
          · intro b u i h; exact send2OfFlat_inBounds (div_lt_of_lt_mul hr) h
          · intro _ _ h; cases h
          · intro _ _ _ h; cases h
        · simp only [h1, h2, h3, ↓reduceIte]
          have hr : idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) <
              S.N_send_opk_tot * S.N_opk_tot := by
            unfold fgTotalIndexCount at hLt; omega
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro _ h; cases h
          · intro b u i h; exact sendOpk2OfFlat_inBounds (div_lt_of_lt_mul hr) h
          · intro _ _ h; cases h
          · intro u j o h; exact opk2OfFlat_inBounds (mod_lt_of_lt_mul hr) h

private theorem spk2OfFlat_val {S : Setup} {s : ℕ} (hs : s < S.N_spk_tot) :
    s / S.N_recv * S.N_recv.min S.N_spk_tot + s % S.N_recv = s := by
  rw [min_spk_recv (Nat.lt_of_le_of_lt (Nat.zero_le _) hs), div_mul_add_mod_eq]

private theorem opk2OfFlat_val {S : Setup} {oIdx : ℕ} (ho : oIdx < S.N_opk_tot) :
    (oIdx / S.N_opk / S.N_recv * S.N_recv.min S.N_spk_tot + oIdx / S.N_opk % S.N_recv) *
      S.N_opk.min S.N_opk_tot + oIdx % S.N_opk = oIdx := by
  have hs : oIdx / S.N_opk < S.N_spk_tot := div_lt_of_lt_mul ho
  rw [min_spk_recv (Nat.lt_of_le_of_lt (Nat.zero_le _) hs),
    min_opk_slot (Nat.lt_of_le_of_lt (Nat.zero_le _) ho),
    div_mul_add_mod_eq, div_mul_add_mod_eq]

private theorem params2ToFlat_params2OfFlat (S : Setup) (U V : Bytes) (idx : Nat)
    (hIdx : idx ∈ support (FgGapDh.sampleIndexRange (fgTotalIndexCount S))) :
    params2ToFlat S (params2OfFlat S U V idx) = paramsFlatVal2 S U V idx := by
  by_cases h0 : fgTotalIndexCount S = 0
  · simp only [FgGapDh.sampleIndexRange, h0, lt_self_iff_false, ↓reduceDIte,
      support_pure, Set.mem_singleton_iff] at hIdx
    subst hIdx
    have hZeroes : S.N_id * S.N_spk_tot = 0 ∧ S.N_send_tot * S.N_spk_tot = 0 ∧
        S.N_send_tot * S.N_id = 0 ∧ S.N_send_opk_tot * S.N_opk_tot = 0 := by
      unfold fgTotalIndexCount at h0; omega
    simp [params2OfFlat, params2ToFlat, paramsFlatVal2, paramsOpkVal, h0,
      hZeroes.1, hZeroes.2.1, hZeroes.2.2.1]
  · have hLt : idx < fgTotalIndexCount S :=
      mem_support_sampleIndexRange_lt (Nat.pos_of_ne_zero h0) hIdx
    unfold params2OfFlat paramsFlatVal2
    dsimp only
    simp only [h0, ↓reduceIte]
    by_cases h1 : idx < S.N_id * S.N_spk_tot
    · simp only [h1, ↓reduceIte, params2ToFlat, paramsDhVal, spk2OfFlat,
        spk2OfFlat_val (mod_lt_of_lt_mul h1)]
      simp
    · by_cases h2 : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot
      · have hr : idx - S.N_id * S.N_spk_tot < S.N_send_tot * S.N_spk_tot := by omega
        have ht : (idx - S.N_id * S.N_spk_tot) / S.N_spk_tot < S.N_send_tot :=
          div_lt_of_lt_mul hr
        have hs : (idx - S.N_id * S.N_spk_tot) % S.N_spk_tot < S.N_spk_tot :=
          mod_lt_of_lt_mul hr
        simp only [h1, h2, ↓reduceIte, params2ToFlat, paramsDhVal, spk2OfFlat, send2OfFlat]
        by_cases hlt : (idx - S.N_id * S.N_spk_tot) / S.N_spk_tot < S.N_send_opk_tot
        · simp only [hlt, ↓reduceIte, sendOpk2OfFlat, spk2OfFlat_val hs,
            min_send_opk (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt), div_mul_add_mod_eq]
          simp
        · have hno : (idx - S.N_id * S.N_spk_tot) / S.N_spk_tot - S.N_send_opk_tot <
              S.N_send_no_opk_tot := by
            unfold Setup.N_send_tot at ht; omega
          simp only [hlt, ↓reduceIte, sendNoOpk2OfFlat, spk2OfFlat_val hs,
            min_send_no_opk (Nat.lt_of_le_of_lt (Nat.zero_le _) hno), div_mul_add_mod_eq,
            Nat.add_sub_of_le (Nat.le_of_not_lt hlt)]
          simp
      · by_cases h3 : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id
        · have hr : idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) <
              S.N_send_tot * S.N_id := by omega
          have ht : (idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot)) / S.N_id <
              S.N_send_tot := div_lt_of_lt_mul hr
          simp only [h1, h2, h3, ↓reduceIte, params2ToFlat, paramsIkVal, send2OfFlat]
          by_cases hlt : (idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot)) / S.N_id <
              S.N_send_opk_tot
          · simp only [hlt, ↓reduceIte, sendOpk2OfFlat,
              min_send_opk (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt), div_mul_add_mod_eq]
            simp
          · have ht' : (idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot)) / S.N_id <
                S.N_send_opk_tot + S.N_send_no_opk_tot := ht
            have hno : (idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot)) / S.N_id -
                S.N_send_opk_tot < S.N_send_no_opk_tot := by omega
            simp only [hlt, ↓reduceIte, sendNoOpk2OfFlat,
              min_send_no_opk (Nat.lt_of_le_of_lt (Nat.zero_le _) hno), div_mul_add_mod_eq,
              Nat.add_sub_of_le (Nat.le_of_not_lt hlt)]
            simp
        · have hr : idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) <
              S.N_send_opk_tot * S.N_opk_tot := by
            unfold fgTotalIndexCount at hLt; omega
          have htOpk := div_lt_of_lt_mul hr
          have ho := mod_lt_of_lt_mul hr
          simp only [h1, h2, h3, ↓reduceIte, params2ToFlat, paramsOpkVal, sendOpk2OfFlat,
            opk2OfFlat, min_send_opk (Nat.lt_of_le_of_lt (Nat.zero_le _) htOpk),
            div_mul_add_mod_eq, opk2OfFlat_val ho]
          simp

/-! ### Support Realization of `initParams2Prob` -/

private theorem chooseArm2Prob_mem_support {α : Type} {w1 w2 : ℕ} {m1 m2 : ProbComp α} {x : α}
    (hw : 0 < w1 + w2) (hx : x ∈ support (chooseArm2Prob w1 w2 m1 m2))
    {f1 f2 : ℕ → α}
    (h1 : 0 < w1 → ∀ y ∈ support m1, ∃ i < w1, y = f1 i)
    (h2 : 0 < w2 → ∀ y ∈ support m2, ∃ j < w2, y = f2 j) :
    ∃ k < w1 + w2, x = if k < w1 then f1 k else f2 (k - w1) := by
  unfold chooseArm2Prob at hx
  by_cases hw1 : w1 = 0
  · simp only [hw1, ↓reduceIte] at hx
    obtain ⟨j, hj, rfl⟩ := h2 (by omega) x hx
    exact ⟨j, by omega, by simp [hw1]⟩
  · by_cases hw2 : w2 = 0
    · simp only [hw1, hw2, ↓reduceIte] at hx
      obtain ⟨i, hi, rfl⟩ := h1 (Nat.pos_of_ne_zero hw1) x hx
      exact ⟨i, by omega, by simp [hi]⟩
    · simp only [hw1, hw2, ↓reduceIte, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨b, _, hxb⟩
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at hxb
        obtain ⟨j, hj, rfl⟩ := h2 (Nat.pos_of_ne_zero hw2) x hxb
        exact ⟨w1 + j, by omega, by simp [Nat.not_lt.mpr (Nat.le_add_right w1 j)]⟩
      · simp only [↓reduceIte] at hxb
        obtain ⟨i, hi, rfl⟩ := h1 (Nat.pos_of_ne_zero hw1) x hxb
        exact ⟨i, by omega, by simp [hi]⟩

private theorem prod_mem_support {α β γ : Type} {M N : ℕ} {m1 : ProbComp α} {m2 : ProbComp β}
    (mk : α → β → γ) {x : γ} (hMN : 0 < M * N)
    (hx : x ∈ support (m1 >>= fun a => m2 >>= fun b => pure (mk a b)))
    {f1 : ℕ → α} {f2 : ℕ → β}
    (h1 : 0 < M → ∀ a ∈ support m1, ∃ i < M, a = f1 i)
    (h2 : 0 < N → ∀ b ∈ support m2, ∃ j < N, b = f2 j) :
    ∃ k < M * N, x = mk (f1 (k / N)) (f2 (k % N)) := by
  have hM : 0 < M := Nat.pos_of_mul_pos_right hMN
  have hN : 0 < N := Nat.pos_of_mul_pos_left hMN
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨a, ha, b, hb, rfl⟩
  obtain ⟨i, hi, rfl⟩ := h1 hM a ha
  obtain ⟨j, hj, rfl⟩ := h2 hN b hb
  refine ⟨i * N + j, by nlinarith, ?_⟩
  have hdiv : (i * N + j) / N = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (i * N + j) % N = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [hdiv, hmod]

private theorem samplePrin2Prob_mem_support {S : Setup} (h : 0 < S.N_id)
    (x : Option Nat) (hx : x ∈ support (samplePrin2Prob S)) :
    ∃ u < S.N_id, x = some u := by
  have h0 : S.N_id ≠ 0 := Nat.ne_of_gt h
  simp only [samplePrin2Prob, h0, ↓reduceIte, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at hx
  rcases hx with ⟨u, hu, rfl⟩
  exact ⟨u, mem_support_sampleIndexRange_lt h hu, rfl⟩

private theorem sampleSpkPair2Prob_mem_support {S : Setup} (h : 0 < S.N_spk_tot)
    (x : Option (Nat × Nat)) (hx : x ∈ support (sampleSpkPair2Prob S)) :
    ∃ s < S.N_spk_tot, x = spk2OfFlat S s := by
  have h0 : S.N_spk_tot ≠ 0 := Nat.ne_of_gt h
  unfold sampleSpkPair2Prob at hx
  simp only [h0, ↓reduceIte] at hx
  exact prod_mem_support (fun u j => some (u, j)) h hx
    (fun hM u hu => ⟨u, mem_support_sampleIndexRange_lt hM hu, rfl⟩)
    (fun hN j hj => ⟨j, mem_support_sampleIndexRange_lt hN hj, rfl⟩)

private theorem sampleOpkTriple2Prob_mem_support {S : Setup} (h : 0 < S.N_opk_tot)
    (x : Option (Nat × (Nat × Nat))) (hx : x ∈ support (sampleOpkTriple2Prob S)) :
    ∃ oIdx < S.N_opk_tot, x = opk2OfFlat S oIdx := by
  have h0 : S.N_opk_tot ≠ 0 := Nat.ne_of_gt h
  unfold sampleOpkTriple2Prob at hx
  simp only [h0, ↓reduceIte] at hx
  have hRew : (FgGapDh.sampleIndexRange S.N_id >>= fun u =>
      FgGapDh.sampleIndexRange S.N_recv >>= fun j =>
      FgGapDh.sampleIndexRange S.N_opk >>= fun o => pure (some (u, (j, o)))) =
      ((FgGapDh.sampleIndexRange S.N_id >>= fun u =>
        FgGapDh.sampleIndexRange S.N_recv >>= fun j => pure (u, j)) >>= fun uj =>
        FgGapDh.sampleIndexRange S.N_opk >>= fun o => pure (some (uj.1, (uj.2, o)))) := by
    simp only [bind_assoc, pure_bind]
  rw [hRew] at hx
  exact prod_mem_support (fun uj o => some (uj.1, (uj.2, o))) h hx
    (fun hSpk uj huj => prod_mem_support Prod.mk hSpk huj
      (fun hM u hu => ⟨u, mem_support_sampleIndexRange_lt hM hu, rfl⟩)
      (fun hN j hj => ⟨j, mem_support_sampleIndexRange_lt hN hj, rfl⟩))
    (fun hO o ho => ⟨o, mem_support_sampleIndexRange_lt hO ho, rfl⟩)

private theorem sampleSendOpkTarget2Prob_mem_support {S : Setup} (h : 0 < S.N_send_opk_tot)
    (x : Option (Bool × (Nat × Nat))) (hx : x ∈ support (sampleSendOpkTarget2Prob S)) :
    ∃ t < S.N_send_opk_tot, x = sendOpk2OfFlat S t := by
  have h0 : S.N_send_opk_tot ≠ 0 := Nat.ne_of_gt h
  unfold sampleSendOpkTarget2Prob at hx
  simp only [h0, ↓reduceIte] at hx
  exact prod_mem_support (fun u i => some (true, (u, i))) h hx
    (fun hM u hu => ⟨u, mem_support_sampleIndexRange_lt hM hu, rfl⟩)
    (fun hN i hi => ⟨i, mem_support_sampleIndexRange_lt hN hi, rfl⟩)

private theorem sampleSendNoOpkTarget2Prob_mem_support {S : Setup} (h : 0 < S.N_send_no_opk_tot)
    (x : Option (Bool × (Nat × Nat))) (hx : x ∈ support (sampleSendNoOpkTarget2Prob S)) :
    ∃ r < S.N_send_no_opk_tot, x = sendNoOpk2OfFlat S r := by
  have h0 : S.N_send_no_opk_tot ≠ 0 := Nat.ne_of_gt h
  unfold sampleSendNoOpkTarget2Prob at hx
  simp only [h0, ↓reduceIte] at hx
  exact prod_mem_support (fun u i => some (false, (u, i))) h hx
    (fun hM u hu => ⟨u, mem_support_sampleIndexRange_lt hM hu, rfl⟩)
    (fun hN i hi => ⟨i, mem_support_sampleIndexRange_lt hN hi, rfl⟩)

private theorem sampleSendTarget2Prob_mem_support {S : Setup} (h : 0 < S.N_send_tot)
    (x : Option (Bool × (Nat × Nat))) (hx : x ∈ support (sampleSendTarget2Prob S)) :
    ∃ t < S.N_send_tot, x = send2OfFlat S t := by
  have h0 : S.N_send_tot ≠ 0 := Nat.ne_of_gt h
  unfold sampleSendTarget2Prob at hx
  simp only [h0, ↓reduceIte] at hx
  exact chooseArm2Prob_mem_support h hx
    (fun h1 y hy => sampleSendOpkTarget2Prob_mem_support h1 y hy)
    (fun h2 y hy => sampleSendNoOpkTarget2Prob_mem_support h2 y hy)

private theorem initParams2Prob_mem_support (S : Setup) (U V : Bytes)
    {pa2 : params2Ty.denote} (hpa : pa2 ∈ support (initParams2Prob S U V)) :
    ∃ idx ∈ support (FgGapDh.sampleIndexRange (fgTotalIndexCount S)),
      pa2 = params2OfFlat S U V idx := by
  unfold initParams2Prob at hpa
  by_cases h0 : fgTotalIndexCount S = 0
  · simp only [h0, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hpa
    refine ⟨0, ?_, ?_⟩
    · simp [FgGapDh.sampleIndexRange, h0]
    · simp [params2OfFlat, h0, hpa]
  · simp only [h0, ↓reduceIte] at hpa
    have hTotPos : 0 < (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) +
        (S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot) := by
      unfold fgTotalIndexCount at h0; omega
    obtain ⟨idx, hIdxLt, rfl⟩ := chooseArm2Prob_mem_support hTotPos hpa
      (f1 := fun k => if k < S.N_id * S.N_spk_tot then
          (U, (V, (U, (some (k / S.N_spk_tot),
            (true, (none, (spk2OfFlat S (k % S.N_spk_tot), (false, (none, 0)))))))))
        else
          let r := k - S.N_id * S.N_spk_tot
          (U, (V, (U, (none,
            (false, (send2OfFlat S (r / S.N_spk_tot),
              (spk2OfFlat S (r % S.N_spk_tot), (false, (none, 1))))))))))
      (f2 := fun k => if k < S.N_send_tot * S.N_id then
          (U, (V, (V, (some (k % S.N_id),
            (false, (send2OfFlat S (k / S.N_id), (none, (false, (none, 2)))))))))
        else
          let r := k - S.N_send_tot * S.N_id
          (U, (V, (U, (none,
            (false, (sendOpk2OfFlat S (r / S.N_opk_tot),
              (none, (true, (opk2OfFlat S (r % S.N_opk_tot), 3))))))))))
      (fun hAC y hy => chooseArm2Prob_mem_support hAC hy
        (fun hA z hz => prod_mem_support
          (fun pt st => (U, (V, (U, (pt, (true, (none, (st, (false, (none, 0))))))))))
          hA hz
          (fun hId p hp => samplePrin2Prob_mem_support hId p hp)
          (fun hSpk s hs => sampleSpkPair2Prob_mem_support hSpk s hs))
        (fun hC z hz => prod_mem_support
          (fun et st => (U, (V, (U, (none, (false, (et, (st, (false, (none, 1))))))))))
          hC hz
          (fun hSend e he => sampleSendTarget2Prob_mem_support hSend e he)
          (fun hSpk s hs => sampleSpkPair2Prob_mem_support hSpk s hs)))
      (fun hBD y hy => chooseArm2Prob_mem_support hBD hy
        (fun hB z hz => prod_mem_support
          (fun et pt => (U, (V, (V, (pt, (false, (et, (none, (false, (none, 2))))))))))
          hB hz
          (fun hSend e he => sampleSendTarget2Prob_mem_support hSend e he)
          (fun hId p hp => samplePrin2Prob_mem_support hId p hp))
        (fun hD z hz => prod_mem_support
          (fun et ot => (U, (V, (U, (none, (false, (et, (none, (true, (ot, 3))))))))))
          hD hz
          (fun hSO e he => sampleSendOpkTarget2Prob_mem_support hSO e he)
          (fun hOpk o ho => sampleOpkTriple2Prob_mem_support hOpk o ho)))
    have hIdxTot : idx < fgTotalIndexCount S := by
      unfold fgTotalIndexCount; omega
    refine ⟨idx, mem_support_sampleIndexRange_of_lt hIdxTot, ?_⟩
    unfold params2OfFlat
    dsimp only
    simp only [h0, ↓reduceIte]
    by_cases h1 : idx < S.N_id * S.N_spk_tot
    · have h1' : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot := by omega
      simp [h1, h1']
    · by_cases h2 : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot
      · simp [h1, h2]
      · by_cases h3 : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id
        · have h3' : idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) <
              S.N_send_tot * S.N_id := by omega
          simp [h1, h2, h3, h3']
        · have h3' : ¬ (idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) <
              S.N_send_tot * S.N_id) := by omega
          have hSub : idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) -
              S.N_send_tot * S.N_id =
              idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) := by
            omega
          simp [h1, h2, h3, h3', hSub]

/-! ### Exact `evalDist` Equivalence of `initParams2Prob` -/

private theorem evalDist_sampleIndexRange_bind_bool {N : ℕ} (hN : 0 < N)
    (g : ℕ → ProbComp Bool) (z : Bool) :
    𝒟[FgGapDh.sampleIndexRange N >>= g] {z} =
      ∑ k ∈ Finset.range N, 𝒟[g k] {z} * (N : ℝ≥0∞)⁻¹ := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  letI : MeasurableSpace (Fin N) := ⊤
  simp only [FgGapDh.sampleIndexRange, hN, ↓reduceDIte, bind_assoc, pure_bind]
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton z)
      (Measurable.of_discrete).aemeasurable,
    MeasureTheory.lintegral_fintype]
  simp_rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun k => 𝒟[g k] {z} * (N : ℝ≥0∞)⁻¹) N

private theorem mul_evalDist_sampleIndexRange_bool {N : ℕ} (hN : 0 < N)
    (f : ℕ → ProbComp Bool) (z : Bool) :
    (N : ℝ≥0∞) * 𝒟[FgGapDh.sampleIndexRange N >>= f] {z} =
      ∑ i ∈ Finset.range N, 𝒟[f i] {z} := by
  have hN0 : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hNtop : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  rw [evalDist_sampleIndexRange_bind_bool hN, ← Finset.sum_mul,
    ← mul_assoc, mul_comm (N : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel hN0 hNtop, mul_one]

private theorem sum_range_mul_div_mod_ennreal2 (M N : ℕ) (g : ℕ → ℕ → ℝ≥0∞) :
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

private theorem sum_range_lt_split2 (c K : ℕ) (hc : c ≤ K) (a b : ℝ≥0∞) :
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

private theorem sum_range_odd2 (m : ℕ) :
    ∑ x ∈ Finset.range m, (2 * x + 1) = m * m := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

private theorem sum_range_sq_add_one2 (m : ℕ) :
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
    have h1 := sum_range_odd2 k
    have h2 : ∑ _x ∈ Finset.range k, (2 * k + 1) = k * (2 * k + 1) := by simp
    nlinarith

private theorem sum_range_sq_sub_add_one2 (m K : ℕ) (h : m + m ≤ K) :
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
  rw [sum_range_sq_add_one2] at hAdd
  have hmK : m ≤ K := by omega
  zify [hmK] at hAdd ⊢
  nlinarith

private theorem evalDist_bernoulliCube_scaled_bool {M K : ℕ} (hM : 0 < M) (hMK : M + M ≤ K)
    (pT pF : ProbComp Bool) (z : Bool) :
    (K : ℝ≥0∞) * 𝒟[FgGapDh.sampleIndexRange K >>= fun x =>
        FgGapDh.sampleIndexRange M >>= fun y1 => FgGapDh.sampleIndexRange M >>= fun y2 =>
          if decide (x < y1 + y2 + 1) = true then pT else pF] {z} =
      (M : ℝ≥0∞) * 𝒟[pT] {z} + ((K - M : ℕ) : ℝ≥0∞) * 𝒟[pF] {z} := by
  have hK : 0 < K := by omega
  have hM0 : (M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
  have hMtop : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top M
  rw [mul_evalDist_sampleIndexRange_bool hK]
  have hInner : ∀ x ∈ Finset.range K,
      𝒟[FgGapDh.sampleIndexRange M >>= fun y1 => FgGapDh.sampleIndexRange M >>= fun y2 =>
          if decide (x < y1 + y2 + 1) = true then pT else pF] {z} =
        ∑ y1 ∈ Finset.range M,
          (∑ y2 ∈ Finset.range M,
            (if x < y1 + y2 + 1 then 𝒟[pT] {z} else 𝒟[pF] {z}) * (M : ℝ≥0∞)⁻¹) *
            (M : ℝ≥0∞)⁻¹ := by
    intro x _
    rw [evalDist_sampleIndexRange_bind_bool hM]
    refine Finset.sum_congr rfl fun y1 _ => congrArg (· * (M : ℝ≥0∞)⁻¹) ?_
    rw [evalDist_sampleIndexRange_bind_bool hM]
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
    refine congrArg (fun t : ℝ≥0∞ => t * (M : ℝ≥0∞)⁻¹)
      (congrArg (fun t : ℝ≥0∞ => t * (M : ℝ≥0∞)⁻¹) ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y2 hy2 => ?_
    have hy2' : y2 < M := Finset.mem_range.mp hy2
    exact sum_range_lt_split2 (y1 + y2 + 1) K (by omega) _ _
  rw [hSwap2]
  simp_rw [← Finset.sum_mul]
  have hSplit : (∑ y1 ∈ Finset.range M, ∑ y2 ∈ Finset.range M,
      (((y1 + y2 + 1 : ℕ) : ℝ≥0∞) * 𝒟[pT] {z} +
        ((K - (y1 + y2 + 1) : ℕ) : ℝ≥0∞) * 𝒟[pF] {z})) =
      ((M * M * M : ℕ) : ℝ≥0∞) * 𝒟[pT] {z} +
        ((M * M * (K - M) : ℕ) : ℝ≥0∞) * 𝒟[pF] {z} := by
    rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
    simp_rw [← Finset.sum_mul, ← Nat.cast_sum (R := ℝ≥0∞)]
    rw [sum_range_sq_add_one2 M, sum_range_sq_sub_add_one2 M K hMK]
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

private theorem evalDist_bernoulliRatioProb_scaled_bool {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (pT pF : ProbComp Bool) (z : Bool) :
    ((A + B : ℕ) : ℝ≥0∞) * 𝒟[bernoulliRatioProb A B >>= fun u =>
        if u = true then pT else pF] {z} =
      (A : ℝ≥0∞) * 𝒟[pT] {z} + (B : ℝ≥0∞) * 𝒟[pF] {z} := by
  have hA0 : A ≠ 0 := Nat.ne_of_gt hA
  have hB0 : B ≠ 0 := Nat.ne_of_gt hB
  unfold bernoulliRatioProb
  simp only [hA0, hB0, ↓reduceIte]
  by_cases hAB : A ≤ B
  · simp only [hAB, ↓reduceIte, bind_assoc, pure_bind]
    rw [evalDist_bernoulliCube_scaled_bool hA (by omega), Nat.add_sub_cancel_left]
  · simp only [hAB, ↓reduceIte, bind_assoc, pure_bind]
    have hRew : (FgGapDh.sampleIndexRange (A + B) >>= fun x =>
        FgGapDh.sampleIndexRange B >>= fun y1 => FgGapDh.sampleIndexRange B >>= fun y2 =>
          if (!decide (x < y1 + y2 + 1)) = true then pT else pF) =
        (FgGapDh.sampleIndexRange (A + B) >>= fun x =>
          FgGapDh.sampleIndexRange B >>= fun y1 => FgGapDh.sampleIndexRange B >>= fun y2 =>
            if decide (x < y1 + y2 + 1) = true then pF else pT) := by
      refine bind_congr fun x => bind_congr fun y1 => bind_congr fun y2 => ?_
      cases decide (x < y1 + y2 + 1) <;> rfl
    rw [hRew, evalDist_bernoulliCube_scaled_bool hB (by omega), Nat.add_sub_cancel_right, add_comm]

private theorem evalDist_chooseArm2Prob_bind {α : Type} {w1 w2 : ℕ} (hw : 0 < w1 + w2)
    (m1 m2 : ProbComp α) (f1 f2 : ℕ → α) (g : α → ProbComp Bool) (z : Bool)
    (h1 : 0 < w1 → 𝒟[m1 >>= g] {z} = 𝒟[FgGapDh.sampleIndexRange w1 >>= fun i => g (f1 i)] {z})
    (h2 : 0 < w2 → 𝒟[m2 >>= g] {z} = 𝒟[FgGapDh.sampleIndexRange w2 >>= fun j => g (f2 j)] {z}) :
    𝒟[chooseArm2Prob w1 w2 m1 m2 >>= g] {z} =
      𝒟[FgGapDh.sampleIndexRange (w1 + w2) >>= fun k =>
        g (if k < w1 then f1 k else f2 (k - w1))] {z} := by
  unfold chooseArm2Prob
  by_cases hw1 : w1 = 0
  · simp only [hw1, ↓reduceIte, Nat.zero_add, Nat.not_lt_zero, Nat.sub_zero]
    exact h2 (by omega)
  · by_cases hw2 : w2 = 0
    · simp only [hw1, hw2, ↓reduceIte, Nat.add_zero]
      rw [h1 (Nat.pos_of_ne_zero hw1)]
      have hPos1 : 0 < w1 := Nat.pos_of_ne_zero hw1
      rw [evalDist_sampleIndexRange_bind_bool hPos1, evalDist_sampleIndexRange_bind_bool hPos1]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp [Finset.mem_range.mp hk]
    · have hp1 : 0 < w1 := Nat.pos_of_ne_zero hw1
      have hp2 : 0 < w2 := Nat.pos_of_ne_zero hw2
      simp only [hw1, hw2, ↓reduceIte]
      have hBind : ((bernoulliRatioProb w1 w2 >>= fun b => if b = true then m1 else m2) >>= g) =
          (bernoulliRatioProb w1 w2 >>= fun b => if b = true then m1 >>= g else m2 >>= g) := by
        rw [bind_assoc]
        refine bind_congr fun b => ?_
        cases b <;> rfl
      rw [hBind]
      have hNe0 : ((w1 + w2 : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hw)
      have hNeTop : ((w1 + w2 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top (w1 + w2)
      refine (ENNReal.mul_right_inj hNe0 hNeTop).mp ?_
      rw [evalDist_bernoulliRatioProb_scaled_bool hp1 hp2, h1 hp1, h2 hp2,
        mul_evalDist_sampleIndexRange_bool hp1, mul_evalDist_sampleIndexRange_bool hp2,
        mul_evalDist_sampleIndexRange_bool hw, Finset.sum_range_add]
      congr 1
      · refine Finset.sum_congr rfl fun i hi => ?_
        simp [Finset.mem_range.mp hi]
      · refine Finset.sum_congr rfl fun j _ => ?_
        simp [Nat.not_lt.mpr (Nat.le_add_right w1 j)]

private theorem evalDist_prod_bind {α β : Type} {M N : ℕ} (hMN : 0 < M * N)
    (m1 : ProbComp α) (m2 : ProbComp β) (f1 : ℕ → α) (f2 : ℕ → β)
    (g : α → β → ProbComp Bool) (z : Bool)
    (h1 : 0 < M → ∀ h : α → ProbComp Bool,
      𝒟[m1 >>= h] {z} = 𝒟[FgGapDh.sampleIndexRange M >>= fun i => h (f1 i)] {z})
    (h2 : 0 < N → ∀ h : β → ProbComp Bool,
      𝒟[m2 >>= h] {z} = 𝒟[FgGapDh.sampleIndexRange N >>= fun j => h (f2 j)] {z}) :
    𝒟[m1 >>= fun a => m2 >>= fun b => g a b] {z} =
      𝒟[FgGapDh.sampleIndexRange (M * N) >>= fun k => g (f1 (k / N)) (f2 (k % N))] {z} := by
  have hM : 0 < M := Nat.pos_of_mul_pos_right hMN
  have hN : 0 < N := Nat.pos_of_mul_pos_left hMN
  rw [h1 hM, evalDist_sampleIndexRange_bind_bool hM, evalDist_sampleIndexRange_bind_bool hMN,
    sum_range_mul_div_mod_ennreal2 M N
      (fun i j => 𝒟[g (f1 i) (f2 j)] {z} * ((M * N : ℕ) : ℝ≥0∞)⁻¹)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2 hN, evalDist_sampleIndexRange_bind_bool hN, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.cast_mul, ENNReal.mul_inv (.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)))
    (.inl (ENNReal.natCast_ne_top M)), mul_assoc, mul_comm (M : ℝ≥0∞)⁻¹]

private theorem evalDist_samplePrin2Prob_bind {S : Setup} (h : 0 < S.N_id)
    (g : Option Nat → ProbComp Bool) (z : Bool) :
    𝒟[samplePrin2Prob S >>= g] {z} =
      𝒟[FgGapDh.sampleIndexRange S.N_id >>= fun u => g (some u)] {z} := by
  simp [samplePrin2Prob, Nat.ne_of_gt h]

private theorem evalDist_sampleSpkPair2Prob_bind {S : Setup} (h : 0 < S.N_spk_tot)
    (g : Option (Nat × Nat) → ProbComp Bool) (z : Bool) :
    𝒟[sampleSpkPair2Prob S >>= g] {z} =
      𝒟[FgGapDh.sampleIndexRange S.N_spk_tot >>= fun s => g (spk2OfFlat S s)] {z} := by
  unfold sampleSpkPair2Prob
  simp only [Nat.ne_of_gt h, ↓reduceIte, bind_assoc, pure_bind]
  exact evalDist_prod_bind h _ _ id id (fun u j => g (some (u, j))) z
    (fun _ _ => rfl) (fun _ _ => rfl)

private theorem evalDist_sampleOpkTriple2Prob_bind {S : Setup} (h : 0 < S.N_opk_tot)
    (g : Option (Nat × (Nat × Nat)) → ProbComp Bool) (z : Bool) :
    𝒟[sampleOpkTriple2Prob S >>= g] {z} =
      𝒟[FgGapDh.sampleIndexRange S.N_opk_tot >>= fun oIdx => g (opk2OfFlat S oIdx)] {z} := by
  unfold sampleOpkTriple2Prob
  simp only [Nat.ne_of_gt h, ↓reduceIte, bind_assoc, pure_bind]
  have hAssoc : (FgGapDh.sampleIndexRange S.N_id >>= fun u =>
      FgGapDh.sampleIndexRange S.N_recv >>= fun j =>
      FgGapDh.sampleIndexRange S.N_opk >>= fun o => g (some (u, (j, o)))) =
      ((FgGapDh.sampleIndexRange S.N_id >>= fun u =>
        FgGapDh.sampleIndexRange S.N_recv >>= fun j => pure (u, j)) >>= fun uj =>
        FgGapDh.sampleIndexRange S.N_opk >>= fun o => g (some (uj.1, (uj.2, o)))) := by
    simp only [bind_assoc, pure_bind]
  rw [hAssoc]
  exact evalDist_prod_bind h _ _ (fun s => (s / S.N_recv, s % S.N_recv)) id
    (fun uj o => g (some (uj.1, (uj.2, o)))) z
    (fun hSpk h1 => by
      simp only [bind_assoc, pure_bind]
      exact evalDist_prod_bind hSpk _ _ id id (fun u j => h1 (u, j)) z
        (fun _ _ => rfl) (fun _ _ => rfl))
    (fun _ _ => rfl)

private theorem evalDist_sampleSendOpkTarget2Prob_bind {S : Setup} (h : 0 < S.N_send_opk_tot)
    (g : Option (Bool × (Nat × Nat)) → ProbComp Bool) (z : Bool) :
    𝒟[sampleSendOpkTarget2Prob S >>= g] {z} =
      𝒟[FgGapDh.sampleIndexRange S.N_send_opk_tot >>= fun t => g (sendOpk2OfFlat S t)] {z} := by
  unfold sampleSendOpkTarget2Prob
  simp only [Nat.ne_of_gt h, ↓reduceIte, bind_assoc, pure_bind]
  exact evalDist_prod_bind h _ _ id id (fun u i => g (some (true, (u, i)))) z
    (fun _ _ => rfl) (fun _ _ => rfl)

private theorem evalDist_sampleSendNoOpkTarget2Prob_bind {S : Setup} (h : 0 < S.N_send_no_opk_tot)
    (g : Option (Bool × (Nat × Nat)) → ProbComp Bool) (z : Bool) :
    𝒟[sampleSendNoOpkTarget2Prob S >>= g] {z} =
      𝒟[FgGapDh.sampleIndexRange S.N_send_no_opk_tot >>= fun r => g (sendNoOpk2OfFlat S r)] {z} := by
  unfold sampleSendNoOpkTarget2Prob
  simp only [Nat.ne_of_gt h, ↓reduceIte, bind_assoc, pure_bind]
  exact evalDist_prod_bind h _ _ id id (fun u i => g (some (false, (u, i)))) z
    (fun _ _ => rfl) (fun _ _ => rfl)

private theorem evalDist_sampleSendTarget2Prob_bind {S : Setup} (h : 0 < S.N_send_tot)
    (g : Option (Bool × (Nat × Nat)) → ProbComp Bool) (z : Bool) :
    𝒟[sampleSendTarget2Prob S >>= g] {z} =
      𝒟[FgGapDh.sampleIndexRange S.N_send_tot >>= fun t => g (send2OfFlat S t)] {z} := by
  have h0 : S.N_send_tot ≠ 0 := Nat.ne_of_gt h
  unfold sampleSendTarget2Prob
  simp only [h0, ↓reduceIte]
  exact evalDist_chooseArm2Prob_bind h _ _ (sendOpk2OfFlat S) (sendNoOpk2OfFlat S) g z
    (fun h1 => evalDist_sampleSendOpkTarget2Prob_bind h1 g z)
    (fun h2 => evalDist_sampleSendNoOpkTarget2Prob_bind h2 g z)

private theorem evalDist_initParams2Prob_bind (S : Setup) (U V : Bytes)
    (g : params2Ty.denote → ProbComp Bool) (z : Bool) :
    𝒟[initParams2Prob S U V >>= g] {z} =
      𝒟[FgGapDh.sampleIndexRange (fgTotalIndexCount S) >>= fun idx =>
        g (params2OfFlat S U V idx)] {z} := by
  unfold initParams2Prob
  by_cases h0 : fgTotalIndexCount S = 0
  · simp [h0, FgGapDh.sampleIndexRange, params2OfFlat]
  · simp only [h0, ↓reduceIte]
    have hTotEq : (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) +
        (S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot) = fgTotalIndexCount S := by
      unfold fgTotalIndexCount; omega
    have hTotPos : 0 < (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) +
        (S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot) := by omega
    let fAC : ℕ → params2Ty.denote := fun k =>
      if k < S.N_id * S.N_spk_tot then
        (U, (V, (U, (some (k / S.N_spk_tot),
          (true, (none, (spk2OfFlat S (k % S.N_spk_tot), (false, (none, 0)))))))))
      else
        let r := k - S.N_id * S.N_spk_tot
        (U, (V, (U, (none,
          (false, (send2OfFlat S (r / S.N_spk_tot),
            (spk2OfFlat S (r % S.N_spk_tot), (false, (none, 1)))))))))
    let fBD : ℕ → params2Ty.denote := fun k =>
      if k < S.N_send_tot * S.N_id then
        (U, (V, (V, (some (k % S.N_id),
          (false, (send2OfFlat S (k / S.N_id), (none, (false, (none, 2)))))))))
      else
        let r := k - S.N_send_tot * S.N_id
        (U, (V, (U, (none,
          (false, (sendOpk2OfFlat S (r / S.N_opk_tot),
            (none, (true, (opk2OfFlat S (r % S.N_opk_tot), 3)))))))))
    rw [evalDist_chooseArm2Prob_bind hTotPos _ _ fAC fBD g z
      (fun hAC => evalDist_chooseArm2Prob_bind hAC _ _
        (fun k => (U, (V, (U, (some (k / S.N_spk_tot),
          (true, (none, (spk2OfFlat S (k % S.N_spk_tot), (false, (none, 0))))))))))
        (fun r => (U, (V, (U, (none,
          (false, (send2OfFlat S (r / S.N_spk_tot),
            (spk2OfFlat S (r % S.N_spk_tot), (false, (none, 1))))))))))
        g z
        (fun hA => by
          simp only [bind_assoc, pure_bind]
          exact evalDist_prod_bind hA _ _ some (spk2OfFlat S)
            (fun pt st => g (U, (V, (U, (pt, (true, (none, (st, (false, (none, 0)))))))))) z
            (fun hId h1 => evalDist_samplePrin2Prob_bind hId h1 z)
            (fun hSpk h2 => evalDist_sampleSpkPair2Prob_bind hSpk h2 z))
        (fun hC => by
          simp only [bind_assoc, pure_bind]
          exact evalDist_prod_bind hC _ _ (send2OfFlat S) (spk2OfFlat S)
            (fun et st => g (U, (V, (U, (none, (false, (et, (st, (false, (none, 1)))))))))) z
            (fun hSend h1 => evalDist_sampleSendTarget2Prob_bind hSend h1 z)
            (fun hSpk h2 => evalDist_sampleSpkPair2Prob_bind hSpk h2 z)))
      (fun hBD => evalDist_chooseArm2Prob_bind hBD _ _
        (fun r => (U, (V, (V, (some (r % S.N_id),
          (false, (send2OfFlat S (r / S.N_id), (none, (false, (none, 2))))))))))
        (fun r => (U, (V, (U, (none,
          (false, (sendOpk2OfFlat S (r / S.N_opk_tot),
            (none, (true, (opk2OfFlat S (r % S.N_opk_tot), 3))))))))))
        g z
        (fun hB => by
          simp only [bind_assoc, pure_bind]
          exact evalDist_prod_bind hB _ _ (send2OfFlat S) some
            (fun et pt => g (U, (V, (V, (pt, (false, (et, (none, (false, (none, 2)))))))))) z
            (fun hSend h1 => evalDist_sampleSendTarget2Prob_bind hSend h1 z)
            (fun hId h2 => evalDist_samplePrin2Prob_bind hId h2 z))
        (fun hD => by
          simp only [bind_assoc, pure_bind]
          exact evalDist_prod_bind hD _ _ (sendOpk2OfFlat S) (opk2OfFlat S)
            (fun et ot => g (U, (V, (U, (none, (false, (et, (none, (true, (ot, 3)))))))))) z
            (fun hSO h1 => evalDist_sampleSendOpkTarget2Prob_bind hSO h1 z)
            (fun hOpk h2 => evalDist_sampleOpkTriple2Prob_bind hOpk h2 z)))]
    rw [hTotEq]
    have hPosTot : 0 < fgTotalIndexCount S := Nat.pos_of_ne_zero h0
    rw [evalDist_sampleIndexRange_bind_bool hPosTot, evalDist_sampleIndexRange_bind_bool hPosTot]
    refine Finset.sum_congr rfl fun idx _ => congrArg (· * _) ?_
    have hArgEq : (if idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot then fAC idx
        else fBD (idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot))) =
        params2OfFlat S U V idx := by
      unfold params2OfFlat
      dsimp only [fAC, fBD]
      simp only [h0, ↓reduceIte]
      by_cases h1 : idx < S.N_id * S.N_spk_tot
      · have h1' : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot := by omega
        simp [h1, h1']
      · by_cases h2 : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot
        · simp [h1, h2]
        · by_cases h3 : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id
          · have h3' : idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) <
                S.N_send_tot * S.N_id := by omega
            simp [h1, h2, h3, h3']
          · have h3' : ¬ (idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) <
                S.N_send_tot * S.N_id) := by omega
            have hSub : idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) -
                S.N_send_tot * S.N_id =
                idx - (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) := by
              omega
            simp [h1, h2, h3, h3', hSub]
    rw [hArgEq]

/-! ### Top-Level Theorems -/

/-- Semantic bilinear `gdhQueryBudget` bound for `fgKeyIndGapDh2Prog`. -/
theorem fgKeyIndGapDh2Prog_chalBounded_gdhQueryBudget (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) :
    ((fgKeyIndGapDh2Prog S b.q_total).eval (fun _ => A.1.run) (U, V)).IsQueryBoundP
      (fun q => q.isRight = true) (gdhQueryBudget S b) := by
  have hFlat := fgKeyIndGapDhProg_chalBounded_gdhQueryBudget S b A U V
  rw [fgKeyIndGapDhProg_eval_runFromFlat] at hFlat
  have hPerIdx := isQueryBoundP_of_bind_mem_support hFlat
  rw [fgKeyIndGapDh2Prog_eval_runFromTuple]
  refine isQueryBoundP_unifGdh_bind (initParams2Prob S U V) _ (gdhQueryBudget S b) fun pa2 hpa => ?_
  obtain ⟨idx, hIdx, rfl⟩ := initParams2Prob_mem_support S U V hpa
  have hB : InBoundsParams2 S (params2OfFlat S U V idx) := params2OfFlat_inBounds S U V idx hIdx
  have hEq : (do let secb ← unifGdh ($ᵗ Bool)
                 runFromTuple S b.q_total A.1.run
                   (params2OfFlat S U V idx, simStateToVal (FgGapDh.FgKeyIndSimState.empty S secb))) =
      (do let secb ← unifGdh ($ᵗ Bool)
          runFromFlat S b.q_total A.1.run
            (paramsFlatVal2 S U V idx, simStateToVal (FgGapDh.FgKeyIndSimState.empty S secb))) := by
    refine bind_congr fun secb => ?_
    rw [runFromTuple_eq_runFromFlat S b.q_total (gdhHandle2_eval_map_eq S b.q_total) (gdhFinish2_eval_eq S b.q_total)
      A.1.run _ hB, params2ToFlat_params2OfFlat S U V idx hIdx]
  rw [hEq]
  exact hPerIdx idx ((mem_support_unifGdh _ idx).mpr hIdx)

/-- `evalDist` equality between `fgKeyIndGapDh2Prog` and `fgKeyIndGapDhProg` under `gapDhExp`. -/
theorem fgKeyIndGapDh2Prog_evalDist_gapDhExp_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    𝒟[gapDhExp P isValidDhTriple pow8
        { run := fun U V => (fgKeyIndGapDh2Prog S b.q_total).eval (fun _ => A.1.run) (U, V)
          q_ddh := gdhQueryBudget S b
          q_prim := primQueryBudget S b }] =
      𝒟[gapDhExp P isValidDhTriple pow8
        { run := fun U V => (fgKeyIndGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)
          q_ddh := gdhQueryBudget S b
          q_prim := primQueryBudget S b }] := by
  have hExt : ∀ p q : ProbComp Bool,
      (∀ z : Bool, 𝒟[p] {z} = 𝒟[q] {z}) → 𝒟[p] = 𝒟[q] :=
    fun _ _ hEq => MeasureTheory.Measure.ext_of_singleton hEq
  have hCongrBind : ∀ (m : ProbComp Bytes) (f1 f2 : Bytes → ProbComp Bool),
      (∀ x, 𝒟[f1 x] = 𝒟[f2 x]) → 𝒟[m >>= f1] = 𝒟[m >>= f2] := by
    intro m f1 f2 hf
    letI : MeasurableSpace Bytes := ⊤
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    congr 1
    exact funext hf
  let adv2 : GapDhAdv :=
    { run := fun U V => (fgKeyIndGapDh2Prog S b.q_total).eval (fun _ => A.1.run) (U, V)
      q_ddh := gdhQueryBudget S b
      q_prim := primQueryBudget S b }
  let adv1 : GapDhAdv :=
    { run := fun U V => (fgKeyIndGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)
      q_ddh := gdhQueryBudget S b
      q_prim := primQueryBudget S b }
  change 𝒟[gapDhExp P isValidDhTriple pow8 adv2] = 𝒟[gapDhExp P isValidDhTriple pow8 adv1]
  rw [gapDhExp, gapDhExp]
  refine hCongrBind sampleScalar32 _ _ fun u =>
    hCongrBind sampleScalar32 _ _ fun v =>
      hExt _ _ fun z => ?_
  let U := P.x25519Base u
  let V := P.x25519Base v
  let ddhImpl : QueryImpl gapDhOracleSpec ProbComp := fun (X, Y, Z) =>
    pure (isValidDhTriple X Y Z)
  let impl := primBaseImpl P + ddhImpl
  let contFlat (pa : paramsTy.denote) : ProbComp Bool :=
    ($ᵗ Bool) >>= fun secb =>
      simulateQ impl (runFromFlat S b.q_total A.1.run
        (pa, simStateToVal (FgGapDh.FgKeyIndSimState.empty S secb))) >>= fun Z =>
        pure (pow8 Z == pow8 (P.x25519 u V))
  have hL : (simulateQ impl (adv2.run U V) >>= fun Z => pure (pow8 Z == pow8 (P.x25519 u V))) =
      (initParams2Prob S U V >>= fun pa2 => contFlat (params2ToFlat S pa2)) := by
    change (simulateQ impl ((fgKeyIndGapDh2Prog S b.q_total).eval (fun _ => A.1.run) (U, V)) >>=
        fun Z => pure (pow8 Z == pow8 (P.x25519 u V))) = _
    rw [fgKeyIndGapDh2Prog_eval_runFromTuple, simulateQ_bind, simulateQ_unifGdh, bind_assoc]
    refine bind_congr_of_forall_mem_support _ fun pa2 hpa => ?_
    obtain ⟨idx, hIdx, rfl⟩ := initParams2Prob_mem_support S U V hpa
    have hB := params2OfFlat_inBounds S U V idx hIdx
    rw [simulateQ_bind, simulateQ_unifGdh, bind_assoc]
    refine bind_congr fun secb => ?_
    rw [runFromTuple_eq_runFromFlat S b.q_total (gdhHandle2_eval_map_eq S b.q_total) (gdhFinish2_eval_eq S b.q_total)
      A.1.run _ hB]
  have hR : (simulateQ impl (adv1.run U V) >>= fun Z => pure (pow8 Z == pow8 (P.x25519 u V))) =
      (FgGapDh.sampleIndexRange (fgTotalIndexCount S) >>= fun idx =>
        contFlat (paramsFlatVal2 S U V idx)) := by
    change (simulateQ impl ((fgKeyIndGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)) >>=
        fun Z => pure (pow8 Z == pow8 (P.x25519 u V))) = _
    rw [fgKeyIndGapDhProg_eval_runFromFlat, simulateQ_bind, simulateQ_unifGdh, bind_assoc]
    refine bind_congr fun idx => ?_
    rw [simulateQ_bind, simulateQ_unifGdh, bind_assoc]
  change 𝒟[simulateQ impl (adv2.run U V) >>= fun Z => pure (pow8 Z == pow8 (P.x25519 u V))] {z} =
    𝒟[simulateQ impl (adv1.run U V) >>= fun Z => pure (pow8 Z == pow8 (P.x25519 u V))] {z}
  rw [hL, hR, evalDist_initParams2Prob_bind S U V (fun pa2 => contFlat (params2ToFlat S pa2)) z]
  by_cases h0 : fgTotalIndexCount S = 0
  · have hIdx0 : (0 : ℕ) ∈ support (FgGapDh.sampleIndexRange (fgTotalIndexCount S)) := by
      simp [FgGapDh.sampleIndexRange, h0]
    simp only [FgGapDh.sampleIndexRange, h0, lt_self_iff_false, ↓reduceDIte, pure_bind]
    rw [params2ToFlat_params2OfFlat S U V 0 hIdx0]
  · have hPos : 0 < fgTotalIndexCount S := Nat.pos_of_ne_zero h0
    rw [evalDist_sampleIndexRange_bind_bool hPos, evalDist_sampleIndexRange_bind_bool hPos]
    refine Finset.sum_congr rfl fun idx hMem => congrArg (· * _) ?_
    rw [params2ToFlat_params2OfFlat S U V idx
      (mem_support_sampleIndexRange_of_lt (Finset.mem_range.mp hMem))]

end TupleKeyedEvalDist

theorem fgKeyIndGapDh2Prog_gapDh_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapDH P isValidDhTriple pow8
        { run := fun U V => (fgKeyIndGapDh2Prog S b.q_total).eval (fun _ => A.1.run) (U, V)
          q_ddh := gdhQueryBudget S b
          q_prim := primQueryBudget S b } =
      GapDH P isValidDhTriple pow8
        { run := fun U V => (fgKeyIndGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)
          q_ddh := gdhQueryBudget S b
          q_prim := primQueryBudget S b } := by
  simp only [GapDH, fgKeyIndGapDh2Prog_evalDist_gapDhExp_eq]

end TupleKeyedProg

end SignalPqxdh.Security.ReductionDsl.KeyIndGapDh

