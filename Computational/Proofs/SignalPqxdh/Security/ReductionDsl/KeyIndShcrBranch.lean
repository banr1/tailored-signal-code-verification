/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndShcrComp
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCoreHol
import VCVio.EvalDist.Monad.Basic

/-!
# `shcrKeyIndProg` Branch Evaluation

Proves that the `KemShCr` DSL handler branches (`shcrInitiateC`, `shcrGenSpkB`, `shcrAcceptB`,
`shcrPostC`) evaluate to their shallow counterparts.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp RoKem

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

attribute [simp] bundleV hdrV drKeyV sidV keyIndRenc keyIndQenc

theorem finishKeyIndBasePrim_isSome (S : Setup) (sid : SessionId S) (b : PreKeyBundleInput)
    (e : PrincipalEntry) (ek ss ct : Bytes) (s : KeyIndState S) :
    HoldsOnLeaves (fun p : KeyIndResponse × Option (KeyIndState S) => p.2.isSome = true)
      (finishKeyIndBasePrim S sid b e ek ss ct s) := by
  unfold finishKeyIndBasePrim
  repeat (first
    | (refine HoldsOnLeaves.pure ?_; rfl)
    | (refine HoldsOnLeaves.bind_const _ (fun _ => ?_))
    | split)

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
variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
  (sV : Var Γ₁ shcrStTy) (env : Env Δ) (h : KeyIndShCrState S) (sIdx : Nat) (chosen : Bytes)
  (hs : env.get (Ext.wk sV) = shcrStToVal h sIdx chosen) (hB : KeyIndListsBounded h.base K)
include hs hB

theorem shcrInitiateOpk_eval (xV : Var Γ₂ initQTy) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (b : PreKeyBundleInput) (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal b))) :
    (shcrInitiateC S K true sV xV).eval env =
      encSCS sIdx chosen <$> (pqxdhKeyIndShCrPrimImpl true S (.initiateOPK u i b)).run h := by
  unfold shcrInitiateC
  simp only [letV_eval, bindV, caseOptV, Comp.eval, Expr.eval, v, hx, hs, Env.get_succ',
    Env.get_zero', Ext.step_wk', Ext.refl_wk', initSidE, initGuardE, scBase, shcrStToVal, buOpkB,
    isSomeE, ite_true]
  simp only [pqxdhKeyIndShCrPrimImpl]
  obtain ⟨ikB, spkId, spkB, spkSig, opkB, pqspkId, pqspkB, pqspkSig⟩ := b
  rcases opkB with _ | ⟨oid, opk⟩
  · simp [encSCS, keyIndRespToVal, rNone, Expr.eval, shcrStToVal]
  simp only [preKeyBundleToVal, bundleV, Option.isNone_some, Bool.not_true, Bool.false_eq_true,
    ite_false]
  erw [preCheckC_eval S K _ Var.zero h.base rfl hB Var.zero (.sendOPK u i) rfl Var.zero u.val rfl
    Var.zero ⟨ikB, spkId, spkB, spkSig, some (oid, opk), pqspkId, pqspkB, pqspkSig⟩ rfl]
  simp only [runKeyIndShCrInitiatePrim, ← preCheckFullPrim_snd, StateT.run]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | ⟨k, e⟩
  · simp [encSCS, keyIndRespToVal, rNone, Expr.eval, shcrStToVal]
  simp only [Option.map_some, Prod.map, id, sBytes32_eval, sampleScalar32, sampleCoins32,
    SignalPqxdh.Security.embedUnif, bind_assoc]
  refine bind_congr fun ek => ?_
  refine bind_congr fun coins => ?_
  erw [checkSigsC_eval S K _ Var.zero h.base rfl Var.zero
    ⟨ikB, spkId, spkB, spkSig, some (oid, opk), pqspkId, pqspkB, pqspkSig⟩ rfl hB.principals_le]
  refine bind_congr fun ok => ?_
  cases ok
  · simp [encSCS, keyIndRespToVal, rNone, Expr.eval, shcrStToVal]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, qKemEncaps_eval, Expr.eval,
    Env.get_succ', Env.get_zero', buPqspkB, bind_assoc]
  apply bind_congr; intro enc
  rcases enc with _ | ⟨ss, ct⟩
  · simp [encSCS, keyIndRespToVal, rNone, Expr.eval, shcrStToVal]
  simp only [bind_assoc]
  erw [initFinishC_eval S K _ Var.zero h.base rfl hB Var.zero (.sendOPK u i) rfl Var.zero
    ⟨ikB, spkId, spkB, spkSig, some (oid, opk), pqspkId, pqspkB, pqspkSig⟩ rfl Var.zero k e rfl
    Var.zero ek rfl Var.zero ss ct rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  refine (finishKeyIndBasePrim_isSome S _ _ e ek ss ct h.base).bind_congr _ _ fun p hp => ?_
  rcases p with ⟨r, _ | base'⟩
  · simp at hp
  simp [encFin, shcrFinE, applyShCrFinish, encSCS, shcrStToVal, initRecToVal, Expr.eval]
  simp [hs, shcrStToVal]

theorem shcrInitiateNoOpk_eval (xV : Var Γ₂ initQTy) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (b : PreKeyBundleInput) (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal b))) :
    (shcrInitiateC S K false sV xV).eval env =
      encSCS sIdx chosen <$> (pqxdhKeyIndShCrPrimImpl true S (.initiateNoOPK u i b)).run h := by
  unfold shcrInitiateC
  simp only [letV_eval, bindV, caseOptV, Comp.eval, Expr.eval, v, hx, hs, Env.get_succ',
    Env.get_zero', Ext.step_wk', Ext.refl_wk', initSidE, initGuardE, scBase, shcrStToVal, buOpkB,
    isSomeE, Bool.false_eq_true, ↓reduceIte]
  simp only [pqxdhKeyIndShCrPrimImpl]
  obtain ⟨ikB, spkId, spkB, spkSig, opkB, pqspkId, pqspkB, pqspkSig⟩ := b
  rcases opkB with _ | ⟨oid, opk⟩
  case some => simp [encSCS, keyIndRespToVal, rNone, Expr.eval, shcrStToVal]
  simp only [preKeyBundleToVal, bundleV, Option.isSome_none, Bool.false_eq_true, ite_false]
  erw [preCheckC_eval S K _ Var.zero h.base rfl hB Var.zero (.sendNoOPK u i) rfl Var.zero u.val rfl
    Var.zero ⟨ikB, spkId, spkB, spkSig, none, pqspkId, pqspkB, pqspkSig⟩ rfl]
  simp only [runKeyIndShCrInitiatePrim, ← preCheckFullPrim_snd, StateT.run]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | ⟨k, e⟩
  · simp [encSCS, keyIndRespToVal, rNone, Expr.eval, shcrStToVal]
  simp only [Option.map_some, Prod.map, id, sBytes32_eval, sampleScalar32, sampleCoins32,
    SignalPqxdh.Security.embedUnif, bind_assoc]
  refine bind_congr fun ek => ?_
  refine bind_congr fun coins => ?_
  erw [checkSigsC_eval S K _ Var.zero h.base rfl Var.zero
    ⟨ikB, spkId, spkB, spkSig, none, pqspkId, pqspkB, pqspkSig⟩ rfl hB.principals_le]
  refine bind_congr fun ok => ?_
  cases ok
  · simp [encSCS, keyIndRespToVal, rNone, Expr.eval, shcrStToVal]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, qKemEncaps_eval, Expr.eval,
    Env.get_succ', Env.get_zero', buPqspkB, bind_assoc]
  apply bind_congr; intro enc
  rcases enc with _ | ⟨ss, ct⟩
  · simp [encSCS, keyIndRespToVal, rNone, Expr.eval, shcrStToVal]
  simp only [bind_assoc]
  erw [initFinishC_eval S K _ Var.zero h.base rfl hB Var.zero (.sendNoOPK u i) rfl Var.zero
    ⟨ikB, spkId, spkB, spkSig, none, pqspkId, pqspkB, pqspkSig⟩ rfl Var.zero k e rfl
    Var.zero ek rfl Var.zero ss ct rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  refine (finishKeyIndBasePrim_isSome S _ _ e ek ss ct h.base).bind_congr _ _ fun p hp => ?_
  rcases p with ⟨r, _ | base'⟩
  · simp at hp
  simp [encFin, shcrFinE, applyShCrFinish, encSCS, shcrStToVal, initRecToVal, Expr.eval]
  simp [hs, shcrStToVal]

theorem shcrGenSpk_eval (xV : Var Γ₂ (.prod .nat .nat)) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hx : env.get (Ext.wk xV) = (u.val, j.val)) :
    (shcrGenSpkB S K sV xV).eval env =
      encSCS sIdx chosen <$> (pqxdhKeyIndShCrPrimImpl true S (.genSPK u j)).run h := by
  have hgen : ∀ {Δ' : List PT} [Ext Γ₁ Δ'] [Ext Γ₂ Δ'] (env' : Env Δ'),
      env'.get (Ext.wk sV) = shcrStToVal h sIdx chosen → env'.get (Ext.wk xV) = (u.val, j.val) →
      (onBase sV fun g => genSpkB K g xV).eval env' =
        encSCS sIdx chosen <$>
          (liftShCrBasePrim (pqxdhKeyIndImplPrim true S (.genSPK u j))).run h :=
    fun env' hs' hx' => onBase_eval S env' sV h sIdx chosen hs' (fun g => genSpkB K g xV) _
      (genSpkB_eval (Γ₁ := keyIndStateTy :: _) true S K .zero (.cons (keyIndStateToVal h.base) env')
        h.base rfl hB xV u j (by simpa [Ext.step_wk', Env.get_succ'] using hx'))
  unfold shcrGenSpkB
  simp only [pqxdhKeyIndShCrPrimImpl, runKeyIndShCrGenSPKPrim, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, StateT.run]
  rcases ht : h.targetBIdx? with _ | bIdx
  · simp only [caseOptV, Comp.eval, Expr.eval, v, hs, scTB, shcrStToVal, ht, Option.map_none]
    exact hgen env hs hx
  · simp only [caseOptV, Comp.eval, Expr.eval, v, hs, scTB, shcrStToVal, ht, Option.map_some,
      hx, nat2Eq, natEq_eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
      pair_beq_eq_flatIdx_beq S u j bIdx]
    by_cases hc : (RoKem.spkBundleFlatIdx S u j == bIdx) = true
    · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      core_simp [hs, hx, scBase, scUpd, scTPk, scTSk, scTB, scCnt, scIR, scRR, scSIdx, scChosen,
        shcrStToVal, List.take_of_length_le, hB.spkBundles_le, hB.principals_le, Prod.map, id]
      simp only [genSpkTargetKeyIndPrim]
      have ha : (h.base.spkBundles.any fun x => x.1 == (↑u, ↑j)) =
          (h.base.spkBundles.any fun x => x.1.1 == ↑u && x.1.2 == ↑j) := by
        congr 1
      rw [ha]
      by_cases h3 : (h.base.spkBundles.any fun x => x.1.1 == ↑u && x.1.2 == ↑j) = true
      · simp [h3, encSCS, shcrStToVal, keyIndStateToVal, keyIndRespToVal, ht]
      simp only [h3, Bool.false_eq_true, ↓reduceIte]
      rcases hfd : h.base.principals.find? (fun x => x.1 == u.val) with _ | ⟨i, e⟩
      · simp [hfd, encSCS, shcrStToVal, keyIndStateToVal, keyIndRespToVal, ht]
      simp only [hfd, Option.map_some, Prod.map, id, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_def, pure_bind, sampleScalar32]
      erw [hs]
      simp [encSCS, shcrStToVal, keyIndStateToVal, keyIndRespToVal, ht, encodeEC, encodeKEM,
        map_eq_bind_pure_comp]
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      exact hgen _ (by simpa [Ext.step_wk', Env.get_succ'] using hs)
        (by simpa [Ext.step_wk', Env.get_succ'] using hx)

end Br

theorem isNoneRespE_eval {Γ : List PT} (e : Expr pqxdhOps Γ keyIndRespTy) (envΓ : Env Γ)
    (x : KeyIndResponse) (he : e.eval envΓ = keyIndRespToVal x) :
    (isNoneRespE e).eval envΓ = isNoneKeyIndResp x := by
  cases x <;> simp [isNoneRespE, eCaseSum, Expr.eval, he, isNoneKeyIndResp, keyIndRespToVal]

section Br2
variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
  (sV : Var Γ₁ shcrStTy) (env : Env Δ) (h : KeyIndShCrState S) (sIdx : Nat) (chosen : Bytes)
  (hs : env.get (Ext.wk sV) = shcrStToVal h sIdx chosen) (n : Nat)
  (hB : KeyIndListsBounded h.base n) (hn : n + 1 ≤ K)
include hs hB hn

theorem shcrAcceptOpk_eval (xV : Var Γ₂ accQTy) (k : Fin S.N_id) (j : Fin S.N_recv)
    (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (hx : env.get (Ext.wk xV) = (k.val, (j.val, (o.val, handshakeHdrToVal hdr)))) :
    (shcrAcceptB S K true sV xV).eval env =
      encSCS sIdx chosen <$> (pqxdhKeyIndShCrPrimImpl true S (.acceptOPK k j o hdr)).run h := by
  unfold shcrAcceptB
  simp only [bindV, ↓reduceIte, Comp.eval]
  rw [onBase_eval S env sV h sIdx chosen hs _ _
    (acceptOpkB_eval (Γ₁ := keyIndStateTy :: Δ) true S K .zero (.cons (keyIndStateToVal h.base) env)
      h.base rfl (hB.mono (by omega)) xV k j o hdr
      (by simpa [Ext.step_wk', Env.get_succ'] using hx))]
  simp only [pqxdhKeyIndShCrPrimImpl, runKeyIndShCrAcceptPrim, StateT.run, kstApply_bind,
    liftShCrBasePrim, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine (pqxdhKeyIndImplPrim_hol true S n _ h.base hB).bind_congr _ _ fun p hp => ?_
  obtain ⟨r, base'⟩ := p
  rw [isNoneRespE_eval _ _ r (by simp [Expr.eval, v, encSCS])]
  simp only [recordAcceptKemGenericPrim]
  cases hr : isNoneKeyIndResp r
  · simp only [Bool.false_eq_true, ↓reduceIte]
    core_simp [encSCS, shcrStToVal, scBase, List.take_of_length_le, hp.spkBundles_le,
      show base'.spkBundles.length ≤ K from le_trans hp.spkBundles_le hn, hx]
    have hf : List.find? (fun x => (Prod.map id spkBundleEntryToVal x).1.1 == ↑k &&
        (Prod.map id spkBundleEntryToVal x).1.2 == ↑j) base'.spkBundles =
        List.find? (fun x => x.1 == (↑k, ↑j)) base'.spkBundles := by
      congr 1
    rw [hf]
    rcases hb : List.find? (fun x => x.1 == (↑k, ↑j)) base'.spkBundles with _ | ⟨b', bE⟩
    · simp [hb]
    · obtain ⟨ikA, ekA, sId, oId, pqId, ct⟩ := hdr
      erw [hx]
      simp [hb, handshakeHdrToVal, map_eq_bind_pure_comp]
      apply bind_congr; intro ss
      rcases ss with _ | ss <;>
        simp [recvRecToVal, RoKem.spkBundleFlatIdx]
  · simp [Expr.eval, v, encSCS]

theorem shcrAcceptNoOpk_eval (xV : Var Γ₂ accQTy) (k : Fin S.N_id) (j : Fin S.N_recv)
    (l : Fin S.N_no_opk) (hdr : HandshakeHdr)
    (hx : env.get (Ext.wk xV) = (k.val, (j.val, (l.val, handshakeHdrToVal hdr)))) :
    (shcrAcceptB S K false sV xV).eval env =
      encSCS sIdx chosen <$> (pqxdhKeyIndShCrPrimImpl true S (.acceptNoOPK k j l hdr)).run h := by
  unfold shcrAcceptB
  simp only [bindV, Bool.false_eq_true, ↓reduceIte, Comp.eval]
  rw [onBase_eval S env sV h sIdx chosen hs _ _
    (acceptNoOpkB_eval (Γ₁ := keyIndStateTy :: Δ) true S K .zero
      (.cons (keyIndStateToVal h.base) env)
      h.base rfl (hB.mono (by omega)) xV k j l hdr
      (by simpa [Ext.step_wk', Env.get_succ'] using hx))]
  simp only [pqxdhKeyIndShCrPrimImpl, runKeyIndShCrAcceptPrim, StateT.run, kstApply_bind,
    liftShCrBasePrim, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine (pqxdhKeyIndImplPrim_hol true S n _ h.base hB).bind_congr _ _ fun p hp => ?_
  obtain ⟨r, base'⟩ := p
  rw [isNoneRespE_eval _ _ r (by simp [Expr.eval, v, encSCS])]
  simp only [recordAcceptKemGenericPrim]
  cases hr : isNoneKeyIndResp r
  · simp only [Bool.false_eq_true, ↓reduceIte]
    core_simp [encSCS, shcrStToVal, scBase, List.take_of_length_le, hp.spkBundles_le,
      show base'.spkBundles.length ≤ K from le_trans hp.spkBundles_le hn, hx]
    have hf : List.find? (fun x => (Prod.map id spkBundleEntryToVal x).1.1 == ↑k &&
        (Prod.map id spkBundleEntryToVal x).1.2 == ↑j) base'.spkBundles =
        List.find? (fun x => x.1 == (↑k, ↑j)) base'.spkBundles := by
      congr 1
    rw [hf]
    rcases hb : List.find? (fun x => x.1 == (↑k, ↑j)) base'.spkBundles with _ | ⟨b', bE⟩
    · simp [hb]
    · obtain ⟨ikA, ekA, sId, oId, pqId, ct⟩ := hdr
      erw [hx]
      simp [hb, handshakeHdrToVal, map_eq_bind_pure_comp]
      apply bind_congr; intro ss
      rcases ss with _ | ss <;>
        simp [recvRecToVal, RoKem.spkBundleFlatIdx]
  · simp [Expr.eval, v, encSCS]

end Br2

set_option hygiene false in
macro "shcr_generic" q:term:max core:term:max : tactic => `(tactic| (
  refine Eq.trans (b := encSCS sIdx chosen <$>
      (liftShCrBasePrim (S := S) (pqxdhKeyIndImplPrim true S $q)).run h) ?_ rfl
  exact onBase_eval S _ _ h sIdx chosen (by exact hs) _ _ $core))

/-- `shcrPostC` evaluates to `pqxdhKeyIndShCrPrimImpl true S`. -/
theorem shcrPostC_eval (S : Setup) (K n : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sV : Var Γ₁ shcrStTy) (qV : Var Γ₂ keyIndQueryTy) (env : Env Δ) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (sIdx : Nat) (chosen : Bytes)
    (hs : env.get (Ext.wk sV) = shcrStToVal h sIdx chosen)
    (hq : env.get (Ext.wk qV) = keyIndQueryToVal q)
    (hB : KeyIndListsBounded h.base n) (hn : n + 1 ≤ K) :
    (shcrPostC S K sV qV).eval env =
      encSCS sIdx chosen <$> (pqxdhKeyIndShCrPrimImpl true S q).run h := by
  have hK : KeyIndListsBounded h.base K := hB.mono (by omega)
  unfold shcrPostC
  cases q <;> simp only [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal, Env.get_zero',
    Ext.refl_wk']
  case initPrin u => shcr_generic (.initPrin u) (initPrinB_eval true S K _ _ h.base rfl hK _ u rfl)
  case corruptIK u => shcr_generic (.corruptIK u) (corruptB_eval true S K _ _ h.base rfl hK _ u rfl)
  case genSPK u j => exact shcrGenSpk_eval S K _ _ h sIdx chosen (by exact hs) hK _ u j rfl
  case genOPK u j o =>
    shcr_generic (.genOPK u j o) (genOpkB_eval true S K _ _ h.base rfl hK _ u j o rfl)
  case initiateOPK u i bu =>
    exact shcrInitiateOpk_eval S K _ _ h sIdx chosen (by exact hs) hK _ u i bu rfl
  case initiateNoOPK u i bu =>
    exact shcrInitiateNoOpk_eval S K _ _ h sIdx chosen (by exact hs) hK _ u i bu rfl
  case acceptOPK k j o hdr =>
    exact shcrAcceptOpk_eval S K _ _ h sIdx chosen (by exact hs) n hB hn _ k j o hdr rfl
  case acceptNoOPK k j l hdr =>
    exact shcrAcceptNoOpk_eval S K _ _ h sIdx chosen (by exact hs) n hB hn _ k j l hdr rfl
  case testSession sid =>
    shcr_generic (.testSession sid) (testB_eval true S K _ _ h.base rfl hK _ sid rfl)
  case roQuery sec => shcr_generic (.roQuery sec) (roB_eval true S K _ _ h.base rfl hK _ sec rfl)
  case revealDhSecrets => shcr_generic .revealDhSecrets (revealDhB_eval true S K _ _ h.base rfl hK)
  case revealSessionKey sid =>
    shcr_generic (.revealSessionKey sid) (revealB_eval true S K _ _ h.base rfl hK _ sid rfl)
  case registerKey sk =>
    shcr_generic (.registerKey sk)
      (registerB_eval (useRo := true) (S := S) (s := h.base) (hs := rfl) (sk := sk) (hsk := rfl))
  case revealSpkSk u j =>
    shcr_generic (.revealSpkSk u j) (revealSpkB_eval true S K _ _ h.base rfl hK _ u j rfl)

end SignalPqxdh.Security.ReductionDsl.KeyInd
