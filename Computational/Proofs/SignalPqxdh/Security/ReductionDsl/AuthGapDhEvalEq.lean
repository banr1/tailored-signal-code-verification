/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhGrow
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepBase
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepPows
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhFinish
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepRecv
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepSend
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepSmall
import Computational.Proofs.SpecLemmas.SignalPqxdh.Game
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Evaluation Equivalence for `fgAuthGapDhProg`

Proves that simulating `(fgAuthGapDhProg S b.q_total).eval` yields the same output distribution as
the shallow reduction `fgAuthGapDhAdv4 S b A`, via per-query handler equivalence and bounded
state-list invariants.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp
open scoped ENNReal

section Dispatch

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  [h₃ : Ext Γ₃ Δ] (env : Env Δ) (st : FgAuthSimState S) (U V : Bytes) (useDh1 : Bool)
  (t sIdx : Nat)

theorem fgStepC_eval (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    (qv : AuthQuery S)
    (hpa : Env.get env (h₁.wk pa) = paVal U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hq : Env.get env (h₃.wk q) = authQueryToVal qv) (hB : AgBnd K st) :
    (fgStepC S K pa sim q).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V qv st := by
  cases qv <;>
    simp only [fgStepC, caseSumV, v, Comp.eval_caseSumC_elim, Expr.eval, hq, authQueryToVal,
      authQenc, Sum.elim_inl, Sum.elim_inr]
  case initPrin u =>
    exact fgInitPrinC_eval (hpa := hpa) (hsim := hsim) (uf := u) (hu := rfl) (hB := hB) ..
  case corruptIK u =>
    exact fgCorruptC_eval (hsim := hsim) (uf := u) (hu := rfl) (hB := hB) ..
  case genSPK u j =>
    exact fgGenSpkC_eval (hpa := hpa) (hsim := hsim) (uf := u) (jf := j) (hx := rfl) (hB := hB) ..
  case genOPK u j o =>
    exact fgGenOpkC_eval (hsim := hsim) (uf := u) (jf := j) (of := o) (hx := rfl) (hB := hB) ..
  case sendOPK u i b m0 m1 =>
    exact fgSendC_eval_opk (hpa := hpa) (hsim := hsim) (hx := rfl) (hB := hB) ..
  case sendNoOPK u i b m0 m1 =>
    exact fgSendC_eval_noopk (hpa := hpa) (hsim := hsim) (hx := rfl) (hB := hB) ..
  case recvOPK k j o msg =>
    exact fgRecvB_eval_opk (hsim := hsim) (hx := rfl) (hB := hB) ..
  case recvNoOPK k j l msg =>
    exact fgRecvB_eval_noopk (hsim := hsim) (hx := rfl) (hB := hB) ..
  case roQuery sec =>
    exact fgRoC_eval (hsim := hsim) (hsec := rfl) (hB := hB) ..
  case roRootQuery rk dh =>
    exact fgRoRootC_eval (hsim := hsim) (hx := rfl) ..
  case revealDhSecrets =>
    simp only [Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, Sum.elim_inl, Sum.elim_inr,
      Comp.eval, Expr.eval, aNone, hsim, fgAuthStep, map_pure, authRespToVal, authRenc]
  case registerKey sk =>
    exact fgRegisterC_eval (hsim := hsim) (hsk := rfl) ..

end Dispatch

theorem fgHandleDsl_eval (S : Setup) (K : Nat) (st : FgAuthSimState S) (U V : Bytes)
    (useDh1 : Bool) (t sIdx : Nat) (hB : AgBnd K st) (qv : AuthQuery S) :
    (fgHandleDsl S K).eval (.cons (paVal U V useDh1 t sIdx, fgSimToVal st)
        (.cons (authQueryToVal qv) .nil)) =
      (fun r => (authRespToVal r.1, (paVal U V useDh1 t sIdx, fgSimToVal r.2))) <$>
        fgAuthStepHalt useDh1 t sIdx S K U V qv st := by
  have hs := fgStepC_eval S K
    ((.cons (fgSimToVal st) (.cons (paVal U V useDh1 t sIdx)
      (.cons ((paVal U V useDh1 t sIdx, fgSimToVal st) : gsTy.denote)
        (.cons (authQueryToVal qv) .nil)))) :
        Env [fgSimTy, paramsTy, gsTy, authQueryTy]) st U V useDh1 t sIdx
    (.vz : Var [paramsTy, gsTy, authQueryTy] paramsTy)
    (.vz : Var [fgSimTy, paramsTy, gsTy, authQueryTy] fgSimTy)
    (.vs .vz : Var [gsTy, authQueryTy] authQueryTy) qv rfl rfl rfl hB
  simp only [fgHandleDsl]
  ag_unfold
  rw [hs]
  simp only [fgSimToVal, paVal, authStateToVal]
  simp only [take_map_of_le _ _ hB.base.principals_le, fgAuthStepHalt, isTargetPrinCorrupted,
    List.find?_map, Function.comp_def, Prod.map_fst, id_eq, map_eq_bind_pure_comp, bind_assoc,
    pure_bind]
  rcases hf : List.find? (fun x => x.1 == t) st.base.principals with _ | ⟨i, e⟩
  · simp only [hf, Option.map_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  · have hc : (Prod.map id principalEntryToVal (i, e)).2.2.2.2.2 = e.corrupted := rfl
    simp only [hf, Option.map_some, hc]
    cases useDh1 <;> cases hcor : e.corrupted <;>
      simp only [Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
    rfl

/-- With `k` game queries still allowed, every state list has at most `K - k` entries. -/
def AgInv {S : Setup} (K k : Nat) (st : FgAuthSimState S) : Prop :=
  k + st.base.principals.length ≤ K ∧
  k + st.base.spkBundles.length ≤ K ∧
  k + st.base.opkEntries.length ≤ K ∧
  k + st.base.sessions.length ≤ K ∧
  k + st.base.usedSendSessions.length ≤ K ∧
  k + st.base.usedRecvOPK.length ≤ K ∧
  k + st.base.usedRecvNoOPK.length ≤ K ∧
  k + st.base.seenKyberBaseKeys.length ≤ K ∧
  k + st.base.roCache.length ≤ K ∧
  k + st.base.rootRoCache.length ≤ K ∧
  k + st.base.advKeys.length ≤ K ∧
  k + st.rawRoCache.length ≤ K ∧
  k + st.advKeyPows.length ≤ K

theorem AgInv.mono {S : Setup} (K k : Nat) (st : FgAuthSimState S) (h : AgInv K (k + 1) st) :
    AgInv K k st := by
  simp only [AgInv] at h ⊢; omega

theorem AgInv.of_grow {S : Setup} (K k : Nat) (st st' : FgAuthSimState S)
    (h : AgInv K (k + 1) st) (hg : AGrow st st') : AgInv K k st' := by
  simp only [AgInv, AGrow] at h hg ⊢; omega

theorem AgInv.empty (S : Setup) (K : Nat) (secb : Bool) :
    AgInv K K (FgAuthSimState.empty S secb) := by
  simp only [AgInv, FgAuthSimState.empty, AuthState.empty, List.length_nil, Nat.add_zero,
    Nat.le_refl, and_self]

theorem AgInv.bnd {S : Setup} (K k : Nat) (st : FgAuthSimState S) (h : AgInv K k st) :
    AgBnd K st := by
  simp only [AgInv] at h
  exact ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega⟩, by omega, by omega⟩

theorem agEmbedPrim_eq {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (mx : OracleComp PrimBaseSpec α) :
    FgGapDh.embedPrim (spec := spec) mx = Security.embedPrim (spec := spec) mx := rfl

theorem agValToAuthResp_authRespToVal (r : AuthResponse) :
    valToAuthResp (authRespToVal r) = r := valToAuthResp_authRespToVal r

theorem fgInitDsl_eval (S : Setup) (U V : Bytes) :
    (fgInitDsl S).eval (.cons (U, V) .nil) =
      (unifGdh (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot) >>= fun p =>
        unifGdh ($ᵗ Bool) >>= fun secb =>
          pure ((), (paVal U V (decide (p.1 < S.N_id))
            (if p.1 < S.N_id then p.1 else p.1 - S.N_id) p.2,
            fgSimToVal (FgAuthSimState.empty S secb)))) := by
  simp only [fgInitDsl, bindV, letV, v, emptySimE, emptyAuthStE, fsMk, stMk,
    Comp.eval_letC, eval_sampleIndexC, eval_sampleBoolC, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    sampleIndexRange2, unifGdh, FgGapDh.embedUnif, _root_.SignalPqxdh.Security.embedUnif,
    liftComp_bind, agEmbedPrim_eq, embedPrim_bind, bind_assoc, liftComp_pure, embedPrim_pure,
    pure_bind]
  refine bind_congr' rfl fun a => bind_congr' rfl fun b => bind_congr' rfl fun c => ?_
  by_cases h : a < S.N_id <;>
    simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;> rfl

theorem fgFinishDsl_eval (S : Setup) (K : Nat) (st : FgAuthSimState S) (U V : Bytes)
    (useDh1 : Bool) (t sIdx : Nat) (hB : AgBnd K st) (a : Bool) :
    (fgFinishDsl S K).eval (.cons (paVal U V useDh1 t sIdx, fgSimToVal st) (.cons a .nil)) =
      extractCdhFromAuthSimState S useDh1 K U V st :=
  fgExtractC_eval S K
    ((.cons (fgSimToVal st) (.cons (paVal U V useDh1 t sIdx)
      (.cons ((paVal U V useDh1 t sIdx, fgSimToVal st) : gsTy.denote) (.cons a .nil)))) :
        Env [fgSimTy, paramsTy, gsTy, .bool]) st U V useDh1 t sIdx
    (.vz : Var [paramsTy, gsTy, .bool] paramsTy)
    (.vz : Var [fgSimTy, paramsTy, gsTy, .bool] fgSimTy) rfl rfl hB

theorem agRun_eq (S : Setup) (K : Nat) (U V : Bytes) (useDh1 : Bool) (t sIdx : Nat)
    (A : OracleComp (unifSpec + authSpec S) Bool)
    (hA : IsQueryBoundP A (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) K) (secb : Bool) :
    (do
      let x ← runWithIfaceStep pqGapDhIface
        (fun q st => do
          let r ← (fgHandleDsl S K).eval (.cons st (.cons (authQueryToVal q) .nil))
          pure (valToAuthResp r.1, r.2))
        A (paVal U V useDh1 t sIdx, fgSimToVal (FgAuthSimState.empty S secb))
      (fgFinishDsl S K).eval (.cons x.2 (.cons x.1 .nil))) =
      (do
        let x ← runWithGdhStep (fgAuthStepHalt useDh1 t sIdx S K U V) A
          (FgAuthSimState.empty S secb)
        extractCdhFromAuthSimState S useDh1 K U V x.2) := by
  refine agRunBridge (GSpec := authSpec S) _ (fgAuthStepHalt useDh1 t sIdx S K U V)
    (fun st => (paVal U V useDh1 t sIdx, fgSimToVal st)) (AgInv K) (AgInv.mono K)
    (fun k q st h => ?_)
    (fun k q st h x hx =>
      AgInv.of_grow K k st x.2 h (fgAuthStepHalt_grow useDh1 t sIdx K U V q st x hx))
    _ _ (fun a st h => ?_) A K hA _ (AgInv.empty S K secb)
  · simp only [fgHandleDsl_eval S K st U V useDh1 t sIdx (AgInv.bnd K (k + 1) st h) q,
      map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind,
      agValToAuthResp_authRespToVal]
  · simp only [fgFinishDsl_eval S K st U V useDh1 t sIdx (AgInv.bnd K 0 st h)]

theorem GRed_eval_pqGapDhIface {κ : Type} {G : OracleSpec κ} {C : GameCodec pqSig G}
    {rIn aIn aOut out : Ty pqSig} (R : CostedReduction pqxdhOps pqGapDhIface G C rIn aIn aOut out)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) :
    R.eval A x =
      (do
        let p ← R.init.eval (.cons x .nil)
        let y ← runWithIfaceStep pqGapDhIface
          (fun q st => do
            let p ← R.handle.eval (.cons st (.cons (C.qenc q) .nil))
            return (C.rdec q p.1, p.2))
          (A p.1) p.2
        R.finish.eval (.cons y.2 (.cons y.1 .nil))) := by
  unfold CostedReduction.eval CostedReduction.impl
  refine bind_congr fun ⟨a, s⟩ => ?_
  dsimp only
  rw [simulateQ_handlerImpl_eq_runWithIfaceStep]

theorem fg2StepC_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ]
    (env : Env Δ) (st : FgAuthSimState S) (U V : Bytes) (useDh1 : Bool) (t sIdx : Nat)
    (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    (qv : AuthQuery S)
    (hpa : Env.get env (h₁.wk pa) = fg2PaVal S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hq : Env.get env (h₃.wk q) = authQueryToVal qv) (hB : AgBnd K st) :
    (fg2StepC S K pa sim q).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V qv st := by
  cases qv <;>
    simp only [fg2StepC, caseSumV, v, Comp.eval_caseSumC_elim, Expr.eval, hq, authQueryToVal,
      authQenc, Sum.elim_inl, Sum.elim_inr]
  case initPrin u =>
    exact fg2InitPrinC_eval (hpa := hpa) (hsim := hsim) (uf := u) (hu := rfl) (hB := hB) ..
  case corruptIK u =>
    exact fgCorruptC_eval (hsim := hsim) (uf := u) (hu := rfl) (hB := hB) ..
  case genSPK u j =>
    exact fg2GenSpkC_eval (hpa := hpa) (hsim := hsim) (uf := u) (jf := j) (hx := rfl) (hB := hB) ..
  case genOPK u j o =>
    exact fgGenOpkC_eval (hsim := hsim) (uf := u) (jf := j) (of := o) (hx := rfl) (hB := hB) ..
  case sendOPK u i b m0 m1 =>
    exact fg2SendC_eval_opk (hpa := hpa) (hsim := hsim) (hx := rfl) (hB := hB) ..
  case sendNoOPK u i b m0 m1 =>
    exact fg2SendC_eval_noopk (hpa := hpa) (hsim := hsim) (hx := rfl) (hB := hB) ..
  case recvOPK k j o msg =>
    exact fgRecvB_eval_opk (hsim := hsim) (hx := rfl) (hB := hB) ..
  case recvNoOPK k j l msg =>
    exact fgRecvB_eval_noopk (hsim := hsim) (hx := rfl) (hB := hB) ..
  case roQuery sec =>
    exact fgRoC_eval (hsim := hsim) (hsec := rfl) (hB := hB) ..
  case roRootQuery rk dh =>
    exact fgRoRootC_eval (hsim := hsim) (hx := rfl) ..
  case revealDhSecrets =>
    simp only [Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, Sum.elim_inl, Sum.elim_inr,
      Comp.eval, Expr.eval, aNone, hsim, fgAuthStep, map_pure, authRespToVal, authRenc]
  case registerKey sk =>
    exact fgRegisterC_eval (hsim := hsim) (hsk := rfl) ..

theorem fg2HandleDsl_eval (S : Setup) (K : Nat) (st : FgAuthSimState S) (U V : Bytes)
    (useDh1 : Bool) (t sIdx : Nat) (hB : AgBnd K st) (qv : AuthQuery S) :
    (fg2HandleDsl S K).eval (.cons (fg2PaVal S U V useDh1 t sIdx, fgSimToVal st)
        (.cons (authQueryToVal qv) .nil)) =
      (fun r => (authRespToVal r.1, (fg2PaVal S U V useDh1 t sIdx, fgSimToVal r.2))) <$>
        fgAuthStepHalt useDh1 t sIdx S K U V qv st := by
  have hs := fg2StepC_eval S K
    ((.cons (fgSimToVal st) (.cons (fg2PaVal S U V useDh1 t sIdx)
      (.cons ((fg2PaVal S U V useDh1 t sIdx, fgSimToVal st) : fg2GsTy.denote)
        (.cons (authQueryToVal qv) .nil)))) :
        Env [fgSimTy, fg2ParamsTy, fg2GsTy, authQueryTy]) st U V useDh1 t sIdx
    (.vz : Var [fg2ParamsTy, fg2GsTy, authQueryTy] fg2ParamsTy)
    (.vz : Var [fgSimTy, fg2ParamsTy, fg2GsTy, authQueryTy] fgSimTy)
    (.vs .vz : Var [fg2GsTy, authQueryTy] authQueryTy) qv rfl rfl rfl hB
  simp only [fg2HandleDsl]
  ag_unfold
  rw [hs]
  simp only [fgSimToVal, fg2PaVal, authStateToVal, (paTargetChoice_dh1 S useDh1 t).1]
  simp only [take_map_of_le _ _ hB.base.principals_le, fgAuthStepHalt, isTargetPrinCorrupted,
    List.find?_map, Function.comp_def, Prod.map_fst, id_eq, map_eq_bind_pure_comp, bind_assoc,
    pure_bind]
  cases useDh1
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · rw [(paTargetChoice_dh1 S true t).2 rfl]
    rcases hf : List.find? (fun x => x.1 == t) st.base.principals with _ | ⟨i, e⟩
    · simp only [hf, Option.map_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    · have hc : (Prod.map id principalEntryToVal (i, e)).2.2.2.2.2 = e.corrupted := rfl
      simp only [hf, Option.map_some, hc]
      cases hcor : e.corrupted <;>
        simp only [Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
      rfl

/-- `AgInv` strengthened with `respRecs` length tracking for `K`-clamped extraction. -/
def AgInvResp {S : Setup} (K k : Nat) (st : FgAuthSimState S) : Prop :=
  AgInv K k st ∧ k + st.respRecs.length ≤ K

theorem AgInvResp.mono {S : Setup} (K k : Nat) (st : FgAuthSimState S)
    (h : AgInvResp K (k + 1) st) : AgInvResp K k st :=
  ⟨h.1.mono, by have := h.2; omega⟩

theorem AgInvResp.of_grow {S : Setup} (K k : Nat) (st st' : FgAuthSimState S)
    (h : AgInvResp K (k + 1) st) (hg : AGrow st st')
    (hr : st'.respRecs.length ≤ st.respRecs.length + 1) : AgInvResp K k st' :=
  ⟨AgInv.of_grow K k st st' h.1 hg, by have := h.2; omega⟩

theorem AgInvResp.empty (S : Setup) (K : Nat) (secb : Bool) :
    AgInvResp K K (FgAuthSimState.empty S secb) :=
  ⟨AgInv.empty S K secb, by simp [FgAuthSimState.empty]⟩

theorem AgInvResp.bnd {S : Setup} (K k : Nat) (st : FgAuthSimState S) (h : AgInvResp K k st) :
    AgBnd K st := h.1.bnd

theorem fg2FinishDsl_eval (S : Setup) (K : Nat) (st : FgAuthSimState S) (U V : Bytes)
    (useDh1 : Bool) (t sIdx : Nat) (hB : AgBnd K st) (hresp : st.respRecs.length ≤ K) (a : Bool) :
    (fg2FinishDsl S K).eval (.cons (fg2PaVal S U V useDh1 t sIdx, fgSimToVal st) (.cons a .nil)) =
      extractCdhFromAuthSimState S useDh1 K U V st :=
  fg2ExtractC_eval S K
    ((.cons (fgSimToVal st) (.cons (fg2PaVal S U V useDh1 t sIdx)
      (.cons ((fg2PaVal S U V useDh1 t sIdx, fgSimToVal st) : fg2GsTy.denote) (.cons a .nil)))) :
        Env [fgSimTy, fg2ParamsTy, fg2GsTy, .bool]) st U V useDh1 t sIdx
    (.vz : Var [fg2ParamsTy, fg2GsTy, .bool] fg2ParamsTy)
    (.vz : Var [fgSimTy, fg2ParamsTy, fg2GsTy, .bool] fgSimTy) rfl rfl hB hresp

theorem ag2Run_eq (S : Setup) (K : Nat) (U V : Bytes) (useDh1 : Bool) (t sIdx : Nat)
    (A : OracleComp (unifSpec + authSpec S) Bool)
    (hA : IsQueryBoundP A (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) K) (secb : Bool) :
    (do
      let x ← runWithIfaceStep pqGapDhIface
        (fun q st => do
          let r ← (fg2HandleDsl S K).eval (.cons st (.cons (authQueryToVal q) .nil))
          pure (valToAuthResp r.1, r.2))
        A (fg2PaVal S U V useDh1 t sIdx, fgSimToVal (FgAuthSimState.empty S secb))
      (fg2FinishDsl S K).eval (.cons x.2 (.cons x.1 .nil))) =
      (do
        let x ← runWithGdhStep (fgAuthStepHalt useDh1 t sIdx S K U V) A
          (FgAuthSimState.empty S secb)
        extractCdhFromAuthSimState S useDh1 K U V x.2) := by
  refine agRunBridge (GSpec := authSpec S) _ (fgAuthStepHalt useDh1 t sIdx S K U V)
    (fun st => (fg2PaVal S U V useDh1 t sIdx, fgSimToVal st)) (AgInvResp K) (AgInvResp.mono K)
    (fun k q st h => ?_)
    (fun k q st h x hx =>
      AgInvResp.of_grow K k st x.2 h
        (fgAuthStepHalt_grow useDh1 t sIdx K U V q st x hx)
        (fgAuthStepHalt_respRecs_grow useDh1 t sIdx K U V q st x hx))
    _ _ (fun a st h => ?_) A K hA _ (AgInvResp.empty S K secb)
  · simp only [fg2HandleDsl_eval S K st U V useDh1 t sIdx (AgInvResp.bnd K (k + 1) st h) q,
      map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind,
      agValToAuthResp_authRespToVal]
  · have hresp : st.respRecs.length ≤ K := by have := h.2; omega
    simp only [fg2FinishDsl_eval S K st U V useDh1 t sIdx (AgInvResp.bnd K 0 st h) hresp]

open _root_.SignalPqxdh.Security.FgGapDh (sampleIndexRange)

private def tcOfFlat (S : Setup) (flatIdx : Nat) : targetChoiceTy.denote :=
  paTargetChoice S (decide (flatIdx < S.N_id))
    (if flatIdx < S.N_id then flatIdx else flatIdx - S.N_id)

private noncomputable def sampleSpkProb (S : Setup) : ProbComp (Option (Nat × Nat)) :=
  if S.N_spk_tot = 0 then
    pure none
  else do
    let u ← sampleIndexRange S.N_id
    let j ← sampleIndexRange S.N_recv
    pure (some (u, j))

private noncomputable def sampleTargetInner (A B uT : Nat) : ProbComp targetChoiceTy.denote :=
  if A = 0 ∧ B = 0 then
    pure (false, (uT, (false, 0)))
  else if B = 0 then do
    let i ← sampleIndexRange A
    pure (false, (uT, (true, i)))
  else if A = 0 then do
    let i ← sampleIndexRange B
    pure (false, (uT, (false, i)))
  else if A ≤ B then do
    let x ← sampleIndexRange A
    let y ← sampleIndexRange (A + B)
    if decide (y < 2 * x + 1) = true then
      let i ← sampleIndexRange A
      pure (false, (uT, (true, i)))
    else
      let i ← sampleIndexRange B
      pure (false, (uT, (false, i)))
  else do
    let x ← sampleIndexRange B
    let y ← sampleIndexRange (A + B)
    if decide (y < 2 * x + 1) = true then
      let i ← sampleIndexRange B
      pure (false, (uT, (false, i)))
    else
      let i ← sampleIndexRange A
      pure (false, (uT, (true, i)))

private noncomputable def sampleTargetProb (S : Setup) : ProbComp targetChoiceTy.denote :=
  if S.N_id = 0 then
    pure (false, (0, (false, 0)))
  else do
    let uT ← sampleIndexRange S.N_id
    let z ← sampleIndexRange (1 + S.N_send_opk + S.N_send_no_opk)
    if (z == 0) = true then
      pure (true, (uT, (false, 0)))
    else
      sampleTargetInner S.N_send_opk S.N_send_no_opk uT

private theorem fgSampleSpkC_eval (S : Setup) {Γ : List (Ty pqSig)} (env : Env Γ) :
    (fgSampleSpkC S).eval env = unifGdh (sampleSpkProb S) := by
  unfold fgSampleSpkC sampleSpkProb
  by_cases h0 : S.N_spk_tot = 0
  · simp [h0, Comp.eval, Expr.eval, unifGdh, FgGapDh.embedUnif, agEmbedPrim_eq]
  · simp only [h0, ↓reduceIte, bindV, v, eval_sampleIndexC, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, unifGdh, FgGapDh.embedUnif,
      _root_.SignalPqxdh.Security.embedUnif, liftComp_bind, liftComp_pure,
      agEmbedPrim_eq, embedPrim_bind, embedPrim_pure]

private theorem fgSampleTargetC_eval (S : Setup) {Γ : List (Ty pqSig)} (env : Env Γ) :
    (fgSampleTargetC S).eval env = unifGdh (sampleTargetProb S) := by
  unfold fgSampleTargetC sampleTargetProb
  by_cases h0 : S.N_id = 0
  · simp [h0, Comp.eval, Expr.eval, unifGdh, FgGapDh.embedUnif, agEmbedPrim_eq]
  · simp only [h0, ↓reduceIte, bindV, v, eval_natEq, eval_sampleIndexC, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
      unifGdh, FgGapDh.embedUnif, _root_.SignalPqxdh.Security.embedUnif,
      liftComp_bind, agEmbedPrim_eq, embedPrim_bind]
    refine bind_congr' rfl fun uT => bind_congr' rfl fun z => ?_
    by_cases hz : (z == 0) = true
    · simp [hz]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      unfold sampleTargetInner
      split_ifs <;>
        simp only [eval_sampleIndexC, Comp.eval, Expr.eval, Env.get_vs, Env.get_vz,
          _root_.SignalPqxdh.Security.embedUnif, liftComp_bind, liftComp_pure,
          embedPrim_bind, embedPrim_pure]
      · refine bind_congr' rfl fun (x : Nat) => bind_congr' rfl fun (y : Nat) => ?_
        by_cases hlt : y < 2 * x + 1 <;>
          simp only [hlt, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
            liftComp_bind, liftComp_pure, embedPrim_bind, embedPrim_pure]
      · refine bind_congr' rfl fun (x : Nat) => bind_congr' rfl fun (y : Nat) => ?_
        by_cases hlt : y < 2 * x + 1 <;>
          simp only [hlt, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
            liftComp_bind, liftComp_pure, embedPrim_bind, embedPrim_pure]

private theorem fg2InitDsl_eval (S : Setup) (U V : Bytes) :
    (fg2InitDsl S).eval (.cons (U, V) .nil) =
      (unifGdh (sampleTargetProb S) >>= fun tc =>
        unifGdh (sampleSpkProb S) >>= fun spk =>
          unifGdh ($ᵗ Bool) >>= fun secb =>
            pure ((), ((U, (V, (tc.1, (tc.2.1, (tc.2.2.1, (tc.2.2.2, spk)))))),
              fgSimToVal (FgAuthSimState.empty S secb)))) := by
  simp only [fg2InitDsl, bindV, v, emptySimE, emptyAuthStE, fsMk, stMk,
    fgSampleTargetC_eval, fgSampleSpkC_eval, eval_sampleBoolC, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz]
  rfl

private theorem simulateQ_unifGdh {α : Type} (P : Primitives)
    (ddhImpl : QueryImpl gapDhOracleSpec ProbComp) (mx : ProbComp α) :
    simulateQ (primBaseImpl P + ddhImpl) (unifGdh mx) = mx := by
  unfold unifGdh FgGapDh.embedUnif
  rw [agEmbedPrim_eq]
  unfold _root_.SignalPqxdh.Security.embedPrim
  induction mx using OracleComp.inductionOn with
  | pure a =>
    simp [simulateQ_pure]
  | query_bind k cont ih =>
    rw [liftComp_bind, liftComp_query]
    simp [primBaseImpl]
    exact bind_congr ih

private theorem evalDist_sampleIndexRange_bind_singleton {N : ℕ} (hN : 0 < N)
    (g : ℕ → ProbComp Bool) (z : Bool) :
    𝒟[sampleIndexRange N >>= g] {z} =
      ∑ k ∈ Finset.range N, 𝒟[g k] {z} * (N : ℝ≥0∞)⁻¹ := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let : MeasurableSpace (Fin N) := ⊤
  simp only [sampleIndexRange, hN, ↓reduceDIte, bind_assoc, pure_bind]
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton z)
      (Measurable.of_discrete).aemeasurable,
    MeasureTheory.lintegral_fintype]
  simp_rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun k => 𝒟[g k] {z} * (N : ℝ≥0∞)⁻¹) N

private theorem sum_range_mul_div_mod_ennreal (M N : ℕ) (g : ℕ → ℕ → ℝ≥0∞) :
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

private theorem evalDist_sampleSpkProb_bind (S : Setup)
    (g : Option (Nat × Nat) → ProbComp Bool) (z : Bool) :
    𝒟[sampleSpkProb S >>= g] {z} =
      𝒟[sampleIndexRange S.N_spk_tot >>= fun sIdx => g (paSpkOpt S sIdx)] {z} := by
  unfold sampleSpkProb
  by_cases h0 : S.N_spk_tot = 0
  · simp [h0, sampleIndexRange, paSpkOpt]
  · simp only [h0, ↓reduceIte, bind_assoc, pure_bind]
    have hPos : 0 < S.N_id * S.N_recv := Nat.pos_of_ne_zero h0
    have hM : 0 < S.N_id := Nat.pos_of_mul_pos_right hPos
    have hN : 0 < S.N_recv := Nat.pos_of_mul_pos_left hPos
    change _ = 𝒟[sampleIndexRange (S.N_id * S.N_recv) >>= fun sIdx => g (paSpkOpt S sIdx)] {z}
    rw [evalDist_sampleIndexRange_bind_singleton hPos, evalDist_sampleIndexRange_bind_singleton hM]
    have hRew : ∑ sIdx ∈ Finset.range (S.N_id * S.N_recv),
        𝒟[g (paSpkOpt S sIdx)] {z} * ((S.N_id * S.N_recv : ℕ) : ℝ≥0∞)⁻¹ =
        ∑ sIdx ∈ Finset.range (S.N_id * S.N_recv),
        𝒟[g (some (sIdx / S.N_recv, sIdx % S.N_recv))] {z} * ((S.N_id * S.N_recv : ℕ) : ℝ≥0∞)⁻¹ := by
      refine Finset.sum_congr rfl fun sIdx hs => ?_
      have hslt : sIdx < S.N_spk_tot := Finset.mem_range.mp hs
      simp [paSpkOpt, hslt]
    rw [hRew, sum_range_mul_div_mod_ennreal S.N_id S.N_recv
      (fun u j => 𝒟[g (some (u, j))] {z} * ((S.N_id * S.N_recv : ℕ) : ℝ≥0∞)⁻¹)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [evalDist_sampleIndexRange_bind_singleton hN, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.cast_mul, ENNReal.mul_inv (.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)))
      (.inl (ENNReal.natCast_ne_top S.N_id)), mul_assoc, mul_comm (S.N_id : ℝ≥0∞)⁻¹]

private theorem sum_range_odd (m : ℕ) :
    ∑ x ∈ Finset.range m, (2 * x + 1) = m * m := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

private theorem sum_range_sub_odd (m K : ℕ) (h : m + m ≤ K) :
    ∑ x ∈ Finset.range m, (K - (2 * x + 1)) = m * (K - m) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    zify [show 2 * k + 1 ≤ K by omega, show k ≤ K by omega, show k + 1 ≤ K by omega]
    ring

private theorem sum_range_lt_split (c K : ℕ) (hc : c ≤ K) (a b : ℝ≥0∞) :
    (∑ y ∈ Finset.range K, if y < c then a else b) =
      (c : ℝ≥0∞) * a + ((K - c : ℕ) : ℝ≥0∞) * b := by
  have hK : K = c + (K - c) := (Nat.add_sub_of_le hc).symm
  conv_lhs => rw [hK]
  rw [Finset.sum_range_add]
  congr 1
  · trans (∑ _y ∈ Finset.range c, a)
    · refine Finset.sum_congr rfl fun y hy => ?_
      have hlt : y < c := Finset.mem_range.mp hy
      simp [hlt]
    · simp
  · trans (∑ _y ∈ Finset.range (K - c), b)
    · refine Finset.sum_congr rfl fun y _ => ?_
      have hge : ¬ (c + y < c) := by omega
      simp [hge]
    · simp

private theorem mul_evalDist_sampleIndexRange {N : ℕ} (hN : 0 < N)
    (f : ℕ → ProbComp Bool) (z : Bool) :
    (N : ℝ≥0∞) * 𝒟[sampleIndexRange N >>= f] {z} =
      ∑ i ∈ Finset.range N, 𝒟[f i] {z} := by
  have hN0 : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hNtop : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  rw [evalDist_sampleIndexRange_bind_singleton hN, ← Finset.sum_mul,
    ← mul_assoc, mul_comm (N : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel hN0 hNtop, mul_one]

private theorem evalDist_bernoulliSquare_scaled {M K : ℕ} (hM : 0 < M) (hMK : M + M ≤ K)
    (pT pF : ProbComp Bool) (z : Bool) :
    (K : ℝ≥0∞) * 𝒟[sampleIndexRange M >>= fun x => sampleIndexRange K >>= fun y =>
        if decide (y < 2 * x + 1) = true then pT else pF] {z} =
      (M : ℝ≥0∞) * 𝒟[pT] {z} + ((K - M : ℕ) : ℝ≥0∞) * 𝒟[pF] {z} := by
  have hK : 0 < K := by omega
  have hM0 : (M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
  have hMtop : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top M
  rw [evalDist_sampleIndexRange_bind_singleton hM, Finset.mul_sum]
  have hEach : ∀ x ∈ Finset.range M,
      (K : ℝ≥0∞) * (𝒟[sampleIndexRange K >>= fun y =>
          if decide (y < 2 * x + 1) = true then pT else pF] {z} * (M : ℝ≥0∞)⁻¹) =
        (((2 * x + 1 : ℕ) : ℝ≥0∞) * 𝒟[pT] {z} +
          ((K - (2 * x + 1) : ℕ) : ℝ≥0∞) * 𝒟[pF] {z}) * (M : ℝ≥0∞)⁻¹ := by
    intro x hx
    have hxl : x < M := Finset.mem_range.mp hx
    rw [← mul_assoc, mul_evalDist_sampleIndexRange hK]
    congr 1
    trans (∑ y ∈ Finset.range K, if y < 2 * x + 1 then 𝒟[pT] {z} else 𝒟[pF] {z})
    · refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : y < 2 * x + 1 <;> simp [hy]
    · exact sum_range_lt_split (2 * x + 1) K (by omega) _ _
  rw [Finset.sum_congr rfl hEach]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp_rw [mul_assoc]
    rw [← Finset.sum_mul, ← Nat.cast_sum, sum_range_odd M, Nat.cast_mul,
      mul_comm (𝒟[pT] {z}) (M : ℝ≥0∞)⁻¹,
      mul_assoc (M : ℝ≥0∞) (M : ℝ≥0∞) ((M : ℝ≥0∞)⁻¹ * 𝒟[pT] {z}),
      ← mul_assoc (M : ℝ≥0∞) (M : ℝ≥0∞)⁻¹ (𝒟[pT] {z}),
      ENNReal.mul_inv_cancel hM0 hMtop, one_mul]
  · simp_rw [mul_assoc]
    rw [← Finset.sum_mul, ← Nat.cast_sum, sum_range_sub_odd M K hMK, Nat.cast_mul,
      mul_comm (M : ℝ≥0∞) ((K - M : ℕ) : ℝ≥0∞), mul_assoc,
      ← mul_assoc (M : ℝ≥0∞) (𝒟[pF] {z}), mul_comm (M : ℝ≥0∞) (𝒟[pF] {z}),
      mul_assoc, ENNReal.mul_inv_cancel hM0 hMtop, mul_one]

private theorem evalDist_sampleTargetInner_scaled (A B uT : ℕ)
    (g : targetChoiceTy.denote → ProbComp Bool) (z : Bool) :
    ((A + B : ℕ) : ℝ≥0∞) * 𝒟[sampleTargetInner A B uT >>= g] {z} =
      (∑ i ∈ Finset.range A, 𝒟[g (false, (uT, (true, i)))] {z}) +
        (∑ i ∈ Finset.range B, 𝒟[g (false, (uT, (false, i)))] {z}) := by
  unfold sampleTargetInner
  split_ifs with hab hb ha hab_le
  · rcases hab with ⟨rfl, rfl⟩
    simp
  · subst hb
    have hA : 0 < A := Nat.pos_of_ne_zero fun h => hab ⟨h, rfl⟩
    simp only [bind_assoc, pure_bind, Finset.range_zero, Finset.sum_empty, add_zero]
    exact mul_evalDist_sampleIndexRange hA _ z
  · subst ha
    have hB : 0 < B := Nat.pos_of_ne_zero hb
    simp only [bind_assoc, pure_bind, Finset.range_zero, Finset.sum_empty, zero_add]
    exact mul_evalDist_sampleIndexRange hB _ z
  · have hA : 0 < A := Nat.pos_of_ne_zero ha
    have hB : 0 < B := Nat.pos_of_ne_zero hb
    have hBind : (do
        let x ← sampleIndexRange A
        let y ← sampleIndexRange (A + B)
        if decide (y < 2 * x + 1) = true then
          let i ← sampleIndexRange A
          pure (false, (uT, (true, i)))
        else
          let i ← sampleIndexRange B
          pure (false, (uT, (false, i)))) >>= g =
        (sampleIndexRange A >>= fun x => sampleIndexRange (A + B) >>= fun y =>
          if decide (y < 2 * x + 1) = true then
            sampleIndexRange A >>= fun i => g (false, (uT, (true, i)))
          else
            sampleIndexRange B >>= fun i => g (false, (uT, (false, i)))) := by
      simp only [bind_assoc]
      refine bind_congr fun x => bind_congr fun y => ?_
      by_cases hy : decide (y < 2 * x + 1) = true <;>
        simp only [hy, ↓reduceIte, Bool.false_eq_true, bind_assoc, pure_bind]
    rw [hBind, evalDist_bernoulliSquare_scaled hA (by omega), Nat.add_sub_cancel_left,
      mul_evalDist_sampleIndexRange hA, mul_evalDist_sampleIndexRange hB]
  · have hA : 0 < A := Nat.pos_of_ne_zero ha
    have hB : 0 < B := Nat.pos_of_ne_zero hb
    have hBind : (do
        let x ← sampleIndexRange B
        let y ← sampleIndexRange (A + B)
        if decide (y < 2 * x + 1) = true then
          let i ← sampleIndexRange B
          pure (false, (uT, (false, i)))
        else
          let i ← sampleIndexRange A
          pure (false, (uT, (true, i)))) >>= g =
        (sampleIndexRange B >>= fun x => sampleIndexRange (A + B) >>= fun y =>
          if decide (y < 2 * x + 1) = true then
            sampleIndexRange B >>= fun i => g (false, (uT, (false, i)))
          else
            sampleIndexRange A >>= fun i => g (false, (uT, (true, i)))) := by
      simp only [bind_assoc]
      refine bind_congr fun x => bind_congr fun y => ?_
      by_cases hy : decide (y < 2 * x + 1) = true <;>
        simp only [hy, ↓reduceIte, Bool.false_eq_true, bind_assoc, pure_bind]
    rw [hBind, evalDist_bernoulliSquare_scaled hB (by omega), Nat.add_sub_cancel_right,
      mul_evalDist_sampleIndexRange hB, mul_evalDist_sampleIndexRange hA, add_comm]

private theorem evalDist_sampleTargetProb_bind (S : Setup)
    (g : targetChoiceTy.denote → ProbComp Bool) (z : Bool) :
    𝒟[sampleTargetProb S >>= g] {z} =
      𝒟[sampleIndexRange (S.N_id + S.N_send_tot) >>= fun idx => g (tcOfFlat S idx)] {z} := by
  unfold sampleTargetProb
  by_cases hId : S.N_id = 0
  · have hOpk0 : S.N_send_opk_tot = 0 := by simp [Setup.N_send_opk_tot, hId]
    have hSend0 : S.N_send_tot = 0 := by
      simp [Setup.N_send_tot, Setup.N_send_no_opk_tot, hOpk0, hId]
    simp [hId, hOpk0, hSend0, sampleIndexRange, tcOfFlat, paTargetChoice]
  · simp only [hId, ↓reduceIte, bind_assoc]
    have hPosId : 0 < S.N_id := Nat.pos_of_ne_zero hId
    let A := S.N_send_opk
    let B := S.N_send_no_opk
    let W := 1 + A + B
    have hPosW : 0 < W := by omega
    have hTotEq : S.N_id + S.N_send_tot = S.N_id + (S.N_id * A + S.N_id * B) := rfl
    have hTotMul : S.N_id + S.N_send_tot = S.N_id * W := by
      dsimp only [W, A, B]; rw [hTotEq]; ring
    have hPosTot : 0 < S.N_id + S.N_send_tot := by rw [hTotMul]; exact Nat.mul_pos hPosId hPosW
    rw [evalDist_sampleIndexRange_bind_singleton hPosId,
      evalDist_sampleIndexRange_bind_singleton hPosTot]
    have hInv : ((S.N_id + S.N_send_tot : ℕ) : ℝ≥0∞)⁻¹ =
        (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ := by
      rw [hTotMul, Nat.cast_mul, ENNReal.mul_inv (.inl (Nat.cast_ne_zero.mpr hId))
        (.inl (ENNReal.natCast_ne_top S.N_id)), mul_comm]
    simp_rw [hInv, ← mul_assoc]
    conv_rhs => rw [hTotEq]
    rw [Finset.sum_range_add, Finset.sum_range_add]
    have hB1 : ∑ idx ∈ Finset.range S.N_id,
        𝒟[g (tcOfFlat S idx)] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ =
        ∑ uT ∈ Finset.range S.N_id,
          𝒟[g (true, (uT, (false, 0)))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ := by
      refine Finset.sum_congr rfl fun uT hu => ?_
      have hlt : uT < S.N_id := Finset.mem_range.mp hu
      simp [tcOfFlat, paTargetChoice, hlt]
    have hB2 : ∑ t ∈ Finset.range (S.N_id * A),
        𝒟[g (tcOfFlat S (S.N_id + t))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ =
        ∑ uT ∈ Finset.range S.N_id,
          (∑ i ∈ Finset.range A, 𝒟[g (false, (uT, (true, i)))] {z}) *
            (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ := by
      have hSub : ∑ t ∈ Finset.range (S.N_id * A),
          𝒟[g (tcOfFlat S (S.N_id + t))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ =
          ∑ t ∈ Finset.range (S.N_id * A),
            𝒟[g (false, (t / A, (true, t % A)))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have hlt : t < S.N_send_opk_tot := Finset.mem_range.mp ht
        have hge : ¬ (S.N_id + t < S.N_id) := by omega
        simp [tcOfFlat, paTargetChoice, hge, hlt]; rfl
      rw [hSub, sum_range_mul_div_mod_ennreal S.N_id A
        (fun uT i => 𝒟[g (false, (uT, (true, i)))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹)]
      refine Finset.sum_congr rfl fun uT _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
    have hB3 : ∑ r ∈ Finset.range (S.N_id * B),
        𝒟[g (tcOfFlat S (S.N_id + (S.N_id * A + r)))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ =
        ∑ uT ∈ Finset.range S.N_id,
          (∑ i ∈ Finset.range B, 𝒟[g (false, (uT, (false, i)))] {z}) *
            (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ := by
      have hSub : ∑ r ∈ Finset.range (S.N_id * B),
          𝒟[g (tcOfFlat S (S.N_id + (S.N_id * A + r)))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ =
          ∑ r ∈ Finset.range (S.N_id * B),
            𝒟[g (false, (r / B, (false, r % B)))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hlt : r < S.N_send_no_opk_tot := Finset.mem_range.mp hr
        have hge1 : ¬ (S.N_id + (S.N_id * A + r) < S.N_id) := by omega
        have hsub1 : S.N_id + (S.N_id * A + r) - S.N_id = S.N_send_opk_tot + r := by
          change S.N_id + (S.N_send_opk_tot + r) - S.N_id = _; omega
        have hge2 : ¬ (S.N_send_opk_tot + r < S.N_send_opk_tot) := by omega
        have hlt2 : S.N_send_opk_tot + r < S.N_send_tot := by
          unfold Setup.N_send_tot; omega
        simp [tcOfFlat, paTargetChoice, hge1, hsub1, hge2, hlt2]; rfl
      rw [hSub, sum_range_mul_div_mod_ennreal S.N_id B
        (fun uT i => 𝒟[g (false, (uT, (false, i)))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹)]
      refine Finset.sum_congr rfl fun uT _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
    rw [hB1, hB2, hB3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun uT _ => ?_
    rw [evalDist_sampleIndexRange_bind_singleton hPosW]
    have hW : W = (A + B) + 1 := by dsimp only [W]; omega
    conv_lhs => arg 1; arg 1; rw [hW]
    rw [Finset.sum_range_succ']
    simp only [beq_self_eq_true, ↓reduceIte, pure_bind, Nat.succ_ne_zero, beq_iff_eq,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [add_comm, ← add_mul, ← mul_assoc (((A + B : ℕ) : ℝ≥0∞)),
      evalDist_sampleTargetInner_scaled A B uT g z]
    ring

/-- Simulating `(fgAuthGapDhProg S b.q_total).eval` under any boolean observer produces the same
    distribution as `(fgAuthGapDhAdv4 S b A).run U V`. -/
theorem fgAuthGapDhProg_simulateQ_evalDist_eq (P : Primitives)
    (ddhImpl : QueryImpl gapDhOracleSpec ProbComp)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) (U V : Bytes)
    (obs : Bytes → ProbComp Bool) :
    𝒟[simulateQ (primBaseImpl P + ddhImpl)
        ((fgAuthGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)) >>= obs] =
      𝒟[simulateQ (primBaseImpl P + ddhImpl) ((fgAuthGapDhAdv4 S b A).run U V) >>= obs] := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1
    funext q; cases q <;> rfl
  let runAt (tc : targetChoiceTy.denote) (spk : Option (Nat × Nat)) : ProbComp Bool :=
    ($ᵗ Bool) >>= fun secb =>
      simulateQ (primBaseImpl P + ddhImpl) (do
        let x ← runWithIfaceStep pqGapDhIface
          (fun q st => do
            let r ← (fg2HandleDsl S b.q_total).eval (.cons st (.cons (authQueryToVal q) .nil))
            pure (valToAuthResp r.1, r.2))
          A.1.run
          ((U, (V, (tc.1, (tc.2.1, (tc.2.2.1, (tc.2.2.2, spk)))))),
            fgSimToVal (FgAuthSimState.empty S secb))
        (fg2FinishDsl S b.q_total).eval (.cons x.2 (.cons x.1 .nil))) >>= obs
  have hDsl : (simulateQ (primBaseImpl P + ddhImpl)
      ((fgAuthGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)) >>= obs) =
      (sampleTargetProb S >>= fun tc => sampleSpkProb S >>= fun spk => runAt tc spk) := by
    have hDsl0 : simulateQ (primBaseImpl P + ddhImpl)
        ((fgAuthGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)) =
        (sampleTargetProb S >>= fun tc => sampleSpkProb S >>= fun spk =>
          ($ᵗ Bool) >>= fun secb =>
            simulateQ (primBaseImpl P + ddhImpl) (do
              let x ← runWithIfaceStep pqGapDhIface
                (fun q st => do
                  let r ← (fg2HandleDsl S b.q_total).eval (.cons st (.cons (authQueryToVal q) .nil))
                  pure (valToAuthResp r.1, r.2))
                A.1.run
                ((U, (V, (tc.1, (tc.2.1, (tc.2.2.1, (tc.2.2.2, spk)))))),
                  fgSimToVal (FgAuthSimState.empty S secb))
              (fg2FinishDsl S b.q_total).eval (.cons x.2 (.cons x.1 .nil)))) := by
      rw [GRed_eval_pqGapDhIface]
      dsimp only [fgAuthGapDhProg, authCodec]
      rw [fg2InitDsl_eval]
      simp only [bind_assoc, pure_bind]
      rw [simulateQ_bind, simulateQ_unifGdh]
      refine bind_congr fun tc => ?_
      rw [simulateQ_bind, simulateQ_unifGdh]
      refine bind_congr fun spk => ?_
      rw [simulateQ_bind, simulateQ_unifGdh]
    rw [hDsl0]
    simp only [bind_assoc]
    rfl
  have hSh : (simulateQ (primBaseImpl P + ddhImpl) ((fgAuthGapDhAdv4 S b A).run U V) >>= obs) =
      (sampleIndexRange (S.N_id + S.N_send_tot) >>= fun flatIdx =>
        sampleIndexRange S.N_spk_tot >>= fun bIdx =>
          runAt (tcOfFlat S flatIdx) (paSpkOpt S bIdx)) := by
    have hSh0 : simulateQ (primBaseImpl P + ddhImpl) ((fgAuthGapDhAdv4 S b A).run U V) =
        (sampleIndexRange (S.N_id + S.N_send_tot) >>= fun flatIdx =>
          sampleIndexRange S.N_spk_tot >>= fun bIdx =>
            ($ᵗ Bool) >>= fun secb =>
              simulateQ (primBaseImpl P + ddhImpl) (do
                let x ← runWithIfaceStep pqGapDhIface
                  (fun q st => do
                    let r ← (fg2HandleDsl S b.q_total).eval (.cons st (.cons (authQueryToVal q) .nil))
                    pure (valToAuthResp r.1, r.2))
                  A.1.run
                  ((U, (V, ((tcOfFlat S flatIdx).1, ((tcOfFlat S flatIdx).2.1,
                    ((tcOfFlat S flatIdx).2.2.1, ((tcOfFlat S flatIdx).2.2.2, paSpkOpt S bIdx)))))),
                    fgSimToVal (FgAuthSimState.empty S secb))
                (fg2FinishDsl S b.q_total).eval (.cons x.2 (.cons x.1 .nil)))) := by
      dsimp only [fgAuthGapDhAdv4]
      rw [simulateQ_bind]
      change (simulateQ (primBaseImpl P + ddhImpl)
          (unifGdh (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot)) >>= _) = _
      rw [simulateQ_unifGdh]
      simp only [sampleIndexRange2, bind_assoc, pure_bind]
      refine bind_congr fun flatIdx => bind_congr fun bIdx => ?_
      by_cases h : flatIdx < S.N_id
      · simp only [h, decide_true, ↓reduceIte, tcOfFlat, fgAuthGapDhRunAt]
        rw [simulateQ_bind]
        change (simulateQ (primBaseImpl P + ddhImpl) (unifGdh ($ᵗ Bool)) >>= _) = _
        rw [simulateQ_unifGdh]
        refine bind_congr fun secb => congrArg (simulateQ _) ?_
        exact (ag2Run_eq S b.q_total U V true flatIdx bIdx A.1.run hA secb).symm
      · simp only [h, decide_false, ↓reduceIte, tcOfFlat, fgAuthGapDhRunAt]
        rw [simulateQ_bind]
        change (simulateQ (primBaseImpl P + ddhImpl) (unifGdh ($ᵗ Bool)) >>= _) = _
        rw [simulateQ_unifGdh]
        refine bind_congr fun secb => congrArg (simulateQ _) ?_
        exact (ag2Run_eq S b.q_total U V false (flatIdx - S.N_id) bIdx A.1.run hA secb).symm
    rw [hSh0]
    simp only [bind_assoc]
    rfl
  rw [hDsl, hSh]
  refine MeasureTheory.Measure.ext_of_singleton fun z => ?_
  rw [evalDist_sampleTargetProb_bind S (fun tc => sampleSpkProb S >>= fun spk => runAt tc spk) z]
  by_cases hTot0 : S.N_id + S.N_send_tot = 0
  · simp only [hTot0, sampleIndexRange, lt_self_iff_false, ↓reduceDIte, pure_bind]
    exact evalDist_sampleSpkProb_bind S (fun spk => runAt (tcOfFlat S 0) spk) z
  · have hPos : 0 < S.N_id + S.N_send_tot := Nat.pos_of_ne_zero hTot0
    rw [evalDist_sampleIndexRange_bind_singleton hPos, evalDist_sampleIndexRange_bind_singleton hPos]
    refine Finset.sum_congr rfl fun flatIdx _ => ?_
    exact congrArg (· * _) (evalDist_sampleSpkProb_bind S (fun spk => runAt (tcOfFlat S flatIdx) spk) z)

end SignalPqxdh.Security.ReductionDsl.AuthHs
