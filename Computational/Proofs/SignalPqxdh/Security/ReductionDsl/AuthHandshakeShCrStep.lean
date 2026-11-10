/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrComp
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimRecv
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import VCVio.EvalDist.Monad.Basic

/-!
# Branch Evaluation for `shcrReductionAuthProg`

Proves that the `KemShCr` handler, pause, resume, and extraction branches of
`shcrReductionAuthProg` evaluate to their shallow counterparts.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp RoKem

theorem nRecvEff_mul_add_eq_flatIdx (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv) :
    nRecvEff S * u.val + j.val = RoKem.spkBundleFlatIdx S u j := by
  have hN : S.N_id ≠ 0 := Nat.ne_of_gt u.pos
  simp only [nRecvEff, hN, ↓reduceIte, RoKem.spkBundleFlatIdx, Nat.mul_comm]

private theorem pair_beq_eq_flatIdx_beq (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv)
    (bIdx : Nat) :
    (u.val == bIdx / S.N_recv && j.val == bIdx % S.N_recv) =
      (RoKem.spkBundleFlatIdx S u j == bIdx) := by
  have hj : j.val < S.N_recv := j.isLt
  have hpos : 0 < S.N_recv := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, RoKem.spkBundleFlatIdx]
  constructor
  · rintro ⟨hu, hj'⟩
    have hdm := Nat.div_add_mod bIdx S.N_recv
    rw [hu, hj', Nat.mul_comm]
    omega
  · intro h
    have hdiv : (u.val * S.N_recv + j.val) / S.N_recv = u.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hj, Nat.add_zero]
    have hmod : (u.val * S.N_recv + j.val) % S.N_recv = j.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    exact ⟨by rw [← h, hdiv], by rw [← h, hmod]⟩

section Br
variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  (env : Env Δ) (sV : Var Γ₁ shcrStTy) (h : AuthShCrState S) (sIdx : Nat) (chosen : Bytes)
  (hs : env.get (h₁.wk sV) = shcrStToVal sIdx chosen h) (hB : AuthBaseListsBounded K h.base)
include hs hB

theorem shcrSendOpk_eval (xV : Var Γ₂ sendQTy) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hx : env.get (h₂.wk xV) = (u.val, (i.val, (preKeyBundleToVal b, (m0, m1))))) :
    (shcrSendC S K true sV xV).eval env =
      encSCS sIdx chosen <$> (pqxdhAuthShCrPrimImpl true S (.sendOPK u i b m0 m1)).run h := by
  unfold shcrSendC
  simp only [letV, bindV, caseOptV, Comp.eval_letC, Comp.eval, Expr.eval, v, hx, hs, Env.get_vs,
    Env.get_vz, Ext.step_wk, Ext.refl_wk, sendGuardE, scBase, shcrStToVal, buOpkB, isSomeE,
    ite_true]
  simp only [pqxdhAuthShCrPrimImpl]
  obtain ⟨ikB, spkId, spkB, spkSig, opkB, pqspkId, pqspkB, pqspkSig⟩ := b
  rcases opkB with _ | ⟨oid, opk⟩
  · simp [encSCS, authRespToVal, aNone, Expr.eval, shcrStToVal, preKeyBundleToVal]
  simp only [preKeyBundleToVal, bundleV, Option.isNone_some, Bool.not_true, Bool.false_eq_true,
    ite_false]
  set b : PreKeyBundleInput :=
    ⟨ikB, spkId, spkB, spkSig, some (oid, opk), pqspkId, pqspkB, pqspkSig⟩ with hbdef
  erw [preCheckC_eval S K (Env.cons (authStateToVal h.base) env) true Var.vz h.base rfl hB xV
    (.sendOPK u i) u i.val b m0 m1 (by simpa using hx) rfl]
  simp only [runAuthShCrSendPrim, StateT.run, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | ui
  · simp [encSCS, authRespToVal, aNone, Expr.eval, shcrStToVal]
  simp only [Option.map_some, eval_sampleBytes32,
    sampleScalar32, sampleCoins32, SignalPqxdh.Security.embedUnif, bind_assoc]
  refine bind_congr fun ek => ?_
  refine bind_congr fun coins => ?_
  refine bind_congr fun eph => ?_
  refine bind_congr fun spc => ?_
  erw [checkSigsC_eval S K _ Var.vz h.base (by simp) Var.vz b rfl hB.principals_le]
  refine bind_congr fun ok => ?_
  cases ok
  · simp [encSCS, authRespToVal, aNone, Expr.eval, shcrStToVal]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, eval_queryPrim,
    PTag.dec_kemEncaps, SignalPqxdh.LegacyCosted.PTag.enc, id_map,
    bind_assoc, pauseToVal, preKeyBundleToVal, bundleV]
  refine bind_congr fun enc => ?_
  rcases enc with _ | ⟨ss, ct⟩
  · simp [encSCS, authRespToVal, aNone, Expr.eval, shcrStToVal]
  simp only [bind_assoc]
  erw [finishC_eval S K _ Var.vz h.base rfl hB Var.vz (.sendOPK u i) b m0 m1 ui rfl Var.vz ek eph
    spc rfl Var.vz ss ct rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun o => ?_
  simp only [Function.comp_apply, pure_bind]
  erw [shcrFinC_eval S _ sV h sIdx chosen (by simpa using hs) _ (.sendOPK u i) rfl _ pqspkB rfl
    Var.vz ss ct rfl Var.vz o rfl]

theorem shcrSendNoOpk_eval (xV : Var Γ₂ sendQTy) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hx : env.get (h₂.wk xV) = (u.val, (i.val, (preKeyBundleToVal b, (m0, m1))))) :
    (shcrSendC S K false sV xV).eval env =
      encSCS sIdx chosen <$> (pqxdhAuthShCrPrimImpl true S (.sendNoOPK u i b m0 m1)).run h := by
  unfold shcrSendC
  simp only [letV, bindV, caseOptV, Comp.eval_letC, Comp.eval, Expr.eval, v, hx, hs, Env.get_vs,
    Env.get_vz, Ext.step_wk, Ext.refl_wk, sendGuardE, scBase, shcrStToVal, buOpkB, isSomeE,
    Bool.false_eq_true, ↓reduceIte]
  simp only [pqxdhAuthShCrPrimImpl]
  obtain ⟨ikB, spkId, spkB, spkSig, opkB, pqspkId, pqspkB, pqspkSig⟩ := b
  rcases opkB with _ | ⟨oid, opk⟩
  case some =>
    simp [encSCS, authRespToVal, aNone, Expr.eval, shcrStToVal, preKeyBundleToVal]
  simp only [preKeyBundleToVal, bundleV, Option.isSome_none, Bool.false_eq_true, ite_false]
  set b : PreKeyBundleInput := ⟨ikB, spkId, spkB, spkSig, none, pqspkId, pqspkB, pqspkSig⟩
    with hbdef
  erw [preCheckC_eval S K (Env.cons (authStateToVal h.base) env) false Var.vz h.base rfl hB xV
    (.sendNoOPK u i) u i.val b m0 m1 (by simpa using hx) rfl]
  simp only [runAuthShCrSendPrim, StateT.run, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | ui
  · simp [encSCS, authRespToVal, aNone, Expr.eval, shcrStToVal]
  simp only [Option.map_some, eval_sampleBytes32,
    sampleScalar32, sampleCoins32, SignalPqxdh.Security.embedUnif, bind_assoc]
  refine bind_congr fun ek => ?_
  refine bind_congr fun coins => ?_
  refine bind_congr fun eph => ?_
  refine bind_congr fun spc => ?_
  erw [checkSigsC_eval S K _ Var.vz h.base (by simp) Var.vz b rfl hB.principals_le]
  refine bind_congr fun ok => ?_
  cases ok
  · simp [encSCS, authRespToVal, aNone, Expr.eval, shcrStToVal]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, eval_queryPrim,
    PTag.dec_kemEncaps, SignalPqxdh.LegacyCosted.PTag.enc, id_map,
    bind_assoc, pauseToVal, preKeyBundleToVal, bundleV]
  refine bind_congr fun enc => ?_
  rcases enc with _ | ⟨ss, ct⟩
  · simp [encSCS, authRespToVal, aNone, Expr.eval, shcrStToVal]
  simp only [bind_assoc]
  erw [finishC_eval S K _ Var.vz h.base rfl hB Var.vz (.sendNoOPK u i) b m0 m1 ui rfl Var.vz ek
    eph spc rfl Var.vz ss ct rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun o => ?_
  simp only [Function.comp_apply, pure_bind]
  erw [shcrFinC_eval S _ sV h sIdx chosen (by simpa using hs) _ (.sendNoOPK u i) rfl _ pqspkB rfl
    Var.vz ss ct rfl Var.vz o rfl]

theorem shcrGenSpk_eval (xV : Var Γ₂ (.prod .nat .nat)) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hx : env.get (h₂.wk xV) = (u.val, j.val)) :
    (shcrGenSpkB S K sV xV).eval env =
      encSCS sIdx chosen <$> (pqxdhAuthShCrPrimImpl true S (.genSPK u j)).run h := by
  have hgen : ∀ {Δ' : List (Ty pqSig)} [h₁' : Ext Γ₁ Δ'] [h₂' : Ext Γ₂ Δ'] (env' : Env Δ'),
      env'.get (h₁'.wk sV) = shcrStToVal sIdx chosen h → env'.get (h₂'.wk xV) = (u.val, j.val) →
      (onBase sV fun g => genSpkB K g xV).eval env' =
        encSCS sIdx chosen <$> (liftShCrBasePrim (pqxdhAuthSimImplPrim S (.genSPK u j))).run h :=
    fun env' hs' hx' => onBase_eval S env' sV h sIdx chosen hs' (fun g => genSpkB K g xV) _
      (genSpkB_eval (Γ₁ := authStateTy :: _) S K (.cons (authStateToVal h.base) env') h.base .vz
        xV u j rfl (by simpa using hx') hB)
  unfold shcrGenSpkB
  simp only [pqxdhAuthShCrPrimImpl, runAuthShCrGenSPKPrim, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, StateT.run]
  rcases ht : h.targetBIdx? with _ | bIdx
  · simp only [caseOptV, Comp.eval, Expr.eval, v, hs, scTB, shcrStToVal, ht, Option.map_none]
    exact hgen env hs hx
  · simp only [caseOptV, Comp.eval, Expr.eval, v, hs, scTB, shcrStToVal, ht, Option.map_some,
      hx, nat2Eq, eval_natEq, Env.get_vz, Env.get_vs, Ext.step_wk, Ext.refl_wk,
      pair_beq_eq_flatIdx_beq]
    by_cases hc : (RoKem.spkBundleFlatIdx S u j == bIdx) = true
    · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      send_unfold
      simp only [hs, hx,
        shcrStToVal, authStateToVal, take_map_of_le _ _ hB.spkBundles_le,
        take_map_of_le _ _ hB.principals_le]
      simp only [genSpkTargetAuthPrim]
      have ha : (h.base.spkBundles.any fun x => x.1 == (↑u, ↑j)) =
          ((h.base.spkBundles.map (Prod.map id spkBundleEntryToVal)).any
            fun x => x.1.1 == ↑u && x.1.2 == ↑j) := by
        simp only [List.any_map]; congr 1
      rw [← ha, hs]
      by_cases h3 : (h.base.spkBundles.any fun x => x.1 == (↑u, ↑j)) = true
      · rw [ite_eq_left h3, ite_eq_left h3]
        simp [encSCS, shcrStToVal, authStateToVal, authRespToVal, ht]
      simp only [h3, Bool.false_eq_true, ↓reduceIte, List.find?_map]
      have hpred : ((fun x : Nat × principalEntryTy.denote => x.1 == (u : Nat)) ∘
          Prod.map id principalEntryToVal) = (fun x => x.1 == u.val) := rfl
      rw [hpred]
      rcases hfd : h.base.principals.find? (fun x => x.1 == u.val) with _ | ⟨i, e⟩
      · rw [hfd]; simp [encSCS, shcrStToVal, authStateToVal, authRespToVal, ht]
      rw [hfd]
      simp only [Option.map_some, Prod.map, id, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_def, pure_bind, sampleScalar32, shcrStToVal]
      simp [encSCS, shcrStToVal, authStateToVal, authRespToVal, ht, encodeEC, encodeKEM,
        principalEntryToVal, spkBundleEntryToVal]
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      exact hgen _ (by simpa using hs) (by simpa using hx)

end Br

section Br2
variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  (env : Env Δ) (sV : Var Γ₁ shcrStTy) (h : AuthShCrState S) (sIdx : Nat) (chosen : Bytes)
  (hs : env.get (h₁.wk sV) = shcrStToVal sIdx chosen h) (n : Nat)
  (hB : AuthBaseListsBounded n h.base) (hn : n + 1 ≤ K)
include hs hB hn

theorem shcrAcceptOpk_eval (xV : Var Γ₂ recvQTy) (k : Fin S.N_id) (j : Fin S.N_recv)
    (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hx : env.get (h₂.wk xV) = (k.val, (j.val, (o.val, preKeyMsgToVal msg)))) :
    (shcrAcceptB S K true sV xV).eval env =
      encSCS sIdx chosen <$> (pqxdhAuthShCrPrimImpl true S (.recvOPK k j o msg)).run h := by
  unfold shcrAcceptB
  simp only [bindV, Comp.eval]
  rw [onBase_eval S env sV h sIdx chosen hs _ _
    (recvB_eval_opk (Γ₁ := authStateTy :: Δ) S K (.cons (authStateToVal h.base) env) h.base .vz xV
      k j o msg rfl (by simpa using hx) (hB.mono (by omega)))]
  simp only [pqxdhAuthShCrPrimImpl, runAuthShCrAcceptPrim, StateT.run, stApply_bind,
    liftShCrBasePrim, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine (pqxdhAuthSimImplPrim_hol S n _ h.base hB).bind_congr _ _ fun p hp => ?_
  obtain ⟨r, base'⟩ := p
  simp only [recordAcceptKemGenericPrim, isNoneAuthShCrResp, Bool.false_eq_true, ↓reduceIte]
  send_unfold
  simp only [hx, encSCS, shcrStToVal,
    authStateToVal, take_map_of_le _ _ (le_trans hp.spkBundles_le hn)]
  simp only [List.find?_map]
  have hpred :
      ((fun x : (Nat × Nat) × spkBundleEntryTy.denote => x.1.1 == (k : Nat) && x.1.2 == (j : Nat)) ∘
        Prod.map id spkBundleEntryToVal) = (fun x => x.1 == ((k : Nat), (j : Nat))) := by
    funext x; rfl
  rw [hpred, hx]
  rcases hb : List.find? (fun x => x.1 == ((k : Nat), (j : Nat))) base'.spkBundles with _ | ⟨b', bE⟩
  · rw [hb]; simp []
  · rw [hb]
    simp [preKeyMsgToVal, map_eq_bind_pure_comp]
    refine bind_congr fun ss => ?_
    rcases ss with _ | ss <;>
      simp [recvRecToVal]

theorem shcrAcceptNoOpk_eval (xV : Var Γ₂ recvQTy) (k : Fin S.N_id) (j : Fin S.N_recv)
    (o : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hx : env.get (h₂.wk xV) = (k.val, (j.val, (o.val, preKeyMsgToVal msg)))) :
    (shcrAcceptB S K false sV xV).eval env =
      encSCS sIdx chosen <$> (pqxdhAuthShCrPrimImpl true S (.recvNoOPK k j o msg)).run h := by
  unfold shcrAcceptB
  simp only [bindV, Comp.eval]
  rw [onBase_eval S env sV h sIdx chosen hs _ _
    (recvB_eval_noopk (Γ₁ := authStateTy :: Δ) S K (.cons (authStateToVal h.base) env) h.base .vz xV
      k j o msg rfl (by simpa using hx) (hB.mono (by omega)))]
  simp only [pqxdhAuthShCrPrimImpl, runAuthShCrAcceptPrim, StateT.run, stApply_bind,
    liftShCrBasePrim, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine (pqxdhAuthSimImplPrim_hol S n _ h.base hB).bind_congr _ _ fun p hp => ?_
  obtain ⟨r, base'⟩ := p
  simp only [recordAcceptKemGenericPrim, isNoneAuthShCrResp, Bool.false_eq_true, ↓reduceIte]
  send_unfold
  simp only [hx, encSCS, shcrStToVal,
    authStateToVal, take_map_of_le _ _ (le_trans hp.spkBundles_le hn)]
  simp only [List.find?_map]
  have hpred :
      ((fun x : (Nat × Nat) × spkBundleEntryTy.denote => x.1.1 == (k : Nat) && x.1.2 == (j : Nat)) ∘
        Prod.map id spkBundleEntryToVal) = (fun x => x.1 == ((k : Nat), (j : Nat))) := by
    funext x; rfl
  rw [hpred, hx]
  rcases hb : List.find? (fun x => x.1 == ((k : Nat), (j : Nat))) base'.spkBundles with _ | ⟨b', bE⟩
  · rw [hb]; simp []
  · rw [hb]
    simp [preKeyMsgToVal, map_eq_bind_pure_comp]
    refine bind_congr fun ss => ?_
    rcases ss with _ | ss <;>
      simp [recvRecToVal]

end Br2

section Ext
variable (S : Setup) {Γ₁ Γ₃ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₃ : Ext Γ₃ Δ] (env : Env Δ)

theorem shcrExtractC_eval (Q : Nat) (scV : Var Γ₁ (.prod (B 32) (B 1568))) (sV : Var Γ₃ shcrStTy)
    (h : AuthShCrState S) (sIdx : Nat) (chosen ss ct : Bytes)
    (hsc : env.get (h₁.wk scV) = (ss, ct)) (hs : env.get (h₃.wk sV) = shcrStToVal sIdx chosen h) :
    (shcrExtractC Q scV sV).eval env =
      extractCollidingKemCtPrim Q h.targetPk h.targetSk chosen ct ss h.recvKemRecs := by
  unfold shcrExtractC extractCollidingKemCtPrim
  simp only [findMV, bindV, v, eval_queryPrim, PTag.dec_kemDecaps, SignalPqxdh.LegacyCosted.PTag.enc, id_map, Comp.eval,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, hs, shcrStToVal, scRR, scTSk,
    scTPk, scChosen, findML_eq_findMPrim]
  rw [← List.map_take, findMPrim_map, map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr' (congrArg (findMPrim · _) (funext fun r => ?_)) fun o => ?_
  · unfold isWinningKemShCrCtPrim
    erw [hs]
    refine bind_congr' rfl fun dec => ?_
    rcases dec with _ | d
    · simp [optBytesEq, eLet2, eLet, eCaseOpt, v, Expr.eval_bytesBeq, Expr.eval, hs, hsc,
        shcrStToVal, rrCt, recvRecToVal]
    · simp only [optBytesEq, eLet2, eLet, eCaseOpt, v, Expr.eval_bytesBeq, Expr.eval, Env.get_vs,
        Env.get_vz, Ext.step_wk, Ext.refl_wk, hs, hsc, shcrStToVal, rrCt, recvRecToVal]
      congr 1
      by_cases hc : r.kemCt = ct <;> by_cases hd : d = ss <;> by_cases hp : chosen = h.targetPk <;>
        simp [hc, hd, hp]
  · rcases o with _ | r <;>
      simp [eCaseOpt, rrCt, Expr.eval, hsc, recvRecToVal]

end Ext

set_option hygiene false in
macro "shcr_generic" q:term:max core:term:max : tactic => `(tactic| (
  refine Eq.trans (b := encSCS sIdx chosen <$>
      (liftShCrBasePrim (S := S) (pqxdhAuthSimImplPrim S $q)).run h) ?_ rfl
  exact onBase_eval S _ _ h sIdx chosen (by simpa using hs) _ _ $core))

/-- Post-pause handler `shcrPostC` evaluates to `pqxdhAuthShCrPrimImpl true S`. -/
theorem shcrPostC_eval (S : Setup) (K n : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ]
    [h₂ : Ext Γ₂ Δ] (sV : Var Γ₁ shcrStTy) (qV : Var Γ₂ authQueryTy) (env : Env Δ)
    (q : AuthQuery S) (h : AuthShCrState S) (sIdx : Nat) (chosen : Bytes)
    (hs : env.get (h₁.wk sV) = shcrStToVal sIdx chosen h)
    (hq : env.get (h₂.wk qV) = authQueryToVal q)
    (hB : AuthBaseListsBounded n h.base) (hn : n + 1 ≤ K) :
    (shcrPostC S K sV qV).eval env =
      encSCS sIdx chosen <$> (pqxdhAuthShCrPrimImpl true S q).run h := by
  have hK : AuthBaseListsBounded K h.base := hB.mono (by omega)
  unfold shcrPostC
  cases q <;> simp only [caseSumV, v, Comp.eval_caseSumC_elim, Expr.eval, hq, authQueryToVal]
  case initPrin u =>
    shcr_generic (.initPrin u) (initPrinB_eval S K _ h.base .vz _ u rfl (by simp) hK)
  case corruptIK u =>
    shcr_generic (.corruptIK u) (corruptB_eval S K _ h.base .vz _ u rfl (by simp) hK)
  case genSPK u j =>
    exact shcrGenSpk_eval S K _ _ h sIdx chosen (by simpa using hs) hK _ u j (by simp)
  case genOPK u j o =>
    shcr_generic (.genOPK u j o) (genOpkB_eval S K _ h.base .vz _ u j o rfl (by simp) hK)
  case sendOPK u i b m0 m1 =>
    exact shcrSendOpk_eval S K _ _ h sIdx chosen (by simpa using hs) hK _ u i b m0 m1 (by simp)
  case sendNoOPK u i b m0 m1 =>
    exact shcrSendNoOpk_eval S K _ _ h sIdx chosen (by simpa using hs) hK _ u i b m0 m1 (by simp)
  case recvOPK k j o msg =>
    exact shcrAcceptOpk_eval S K _ _ h sIdx chosen (by simpa using hs) n hB hn _ k j o msg (by simp)
  case recvNoOPK k j l msg =>
    exact shcrAcceptNoOpk_eval S K _ _ h sIdx chosen (by simpa using hs) n hB hn _ k j l msg
      (by simp)
  case roQuery sec =>
    shcr_generic (.roQuery sec) (roB_eval S K _ h.base .vz _ sec rfl (by simp) hK)
  case roRootQuery rk dh =>
    shcr_generic (.roRootQuery rk dh) (roRootB_eval S K _ h.base .vz _ rk dh rfl (by simp) hK)
  case revealDhSecrets =>
    have hl : (liftShCrBasePrim (S := S) (pure AuthResponse.noneResp :
        StateT (AuthState S) (OracleComp PrimBaseSpec) AuthResponse)).run h =
        pure (AuthResponse.noneResp, h) := by
      simp only [liftShCrBasePrim, StateT.run]; rfl
    simp [Comp.eval, Expr.eval, aNone, hs, hl, pqxdhAuthShCrPrimImpl, pqxdhAuthSimImplPrim,
      encSCS, authRespToVal]
  case registerKey sk =>
    shcr_generic (.registerKey sk) (registerB_eval S _ h.base .vz _ sk rfl (by simp))

end SignalPqxdh.Security.ReductionDsl.AuthHs
