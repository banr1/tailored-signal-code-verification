/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCoreHol
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKem
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SigBudgetSim
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SigNoQuery
import VCVio.EvalDist.Monad.Basic

/-!
# Evaluation of `sigKeyIndProg`

Proves that the costed-DSL reduction `sigKeyIndProg` (`sigKeyIndDslAdv`) has the same `SigEufCma`
experiment distribution and advantage as the shallow `sigReductionKeyIndCore`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

set_option allowUnsafeReducibility true in
attribute [implicit_reducible] eufCmaSignOracle

attribute [simp] bundleV hdrV drKeyV sidV keyIndRenc keyIndQenc

theorem liftBase_eq_liftChal {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) : liftBase (C := C) c = c.liftChal (C := C) := by
  induction c <;> simp [liftBase, Comp.liftChal, *] <;> rfl

@[simp] theorem liftBase_eval {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) (env : Env Γ) :
    (liftBase (C := C) c).eval env =
      _root_.SignalPqxdh.Security.embedPrim (spec := C.spec) (c.eval env) := by
  rw [liftBase_eq_liftChal, Comp.eval_liftChal]

@[simp] theorem cost_liftBase {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) : (liftBase (C := C) c).cost = c.cost := by
  induction c <;> simp [liftBase, Comp.cost, *]; rfl

@[simp] theorem widenEC_eval {Γ : List PT} (e : Expr pqxdhOps Γ (B 33)) (env : Env Γ) :
    (widenEC e).eval env = e.eval env := rfl

@[simp] theorem qChalSign_eval (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) (env : Env Γ) :
    (qChalSign m msg).eval env =
      liftM (OracleSpec.query (spec := PrimBaseSpec + eufCmaSignOracle.spec)
        (Sum.inr (SigQuery.sign (msg.eval env)))) := by
  change id <$>
      liftM (OracleSpec.query (spec := PrimBaseSpec + eufCmaSignOracle.spec)
        (Sum.inr (SigQuery.sign (msg.eval env)))) = _
  exact id_map _

/-! ## Branch evaluation -/

def sigStToVal {S : Setup} (p : SigReductionState (KeyIndState S) × Nat) : sigStTy.denote :=
  (keyIndStateToVal p.1.gameState, (p.1.targetParty, (p.1.targetPk, (p.1.forgery, p.2))))

section Branches
variable (useRo : Bool) (S : Setup) (K : Nat) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
  (sV : Var Γ₁ sigStTy) (env : Env Δ) (s : SigReductionState (KeyIndState S)) (b : Nat)
  (hs : env.get (Ext.wk sV) = sigStToVal (s, b))
include hs

theorem onGame_eval
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) →
      Comp pqxdhOps pqPrimIface (keyIndStateTy :: Δ) RS)
    (core : OracleComp PrimBaseSpec (KeyIndResponse × KeyIndState S))
    (hbr : (br .zero).eval (.cons (keyIndStateToVal s.gameState) env) = encRS <$> core) :
    (onGame sV br).eval env =
      (fun p : KeyIndResponse × KeyIndState S =>
        (keyIndRespToVal p.1, sigStToVal ({ s with gameState := p.2 }, b))) <$>
        _root_.SignalPqxdh.Security.embedPrim (spec := eufCmaSignOracle.spec) core := by
  unfold onGame
  simp only [bindV, letV_eval, Comp.eval, Expr.eval, v, Ext.step_wk',
    Env.get_succ', hs, sgGame, sgUpd, sgTarget, sgPk, sgForgery, sgBudget,
    sigStToVal, liftBase_eval]
  rw [hbr, embedPrim_map, map_eq_bind_pure_comp, map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_def, pure_bind]
  rfl

variable {Γ₂ : List PT} [Ext Γ₂ Δ] (hf : s.forgery = none) (hB : KeyIndListsBounded s.gameState K)
include hf hB

theorem sigInitPrinB_eval (uV : Var Γ₂ .nat) (u : Fin S.N_id) (hu : env.get (Ext.wk uV) = u.val) :
    (sigInitPrinB K sV uV).eval env =
      Prod.map keyIndRespToVal id <$>
        sigLiftStep sigStToVal (stepKeyIndForSigPrim useRo S (.initPrin u)) s b := by
  rcases s with ⟨g, tp, tpk, fg⟩
  subst hf
  unfold sigInitPrinB
  have c1 : (eAny K (stPrin (sgGame (v sV))) fun e => natEq (.fst (v e)) (v uV)).eval env =
      g.principals.any (fun x => x.1 == u.val) := by
    simp only [Expr.eval, v, eAny, hs, hu, stPrin, sgGame, natEq_eval, Env.get_zero',
      Env.get_succ', Ext.step_wk', Ext.refl_wk', keyIndStateToVal, sigStToVal, List.any_map,
      Function.comp_def, List.take_of_length_le, List.length_map, hB.principals_le, Prod.map, id]
  have c2 : (natEq (v uV) (sgTarget (v sV))).eval env = (u.val == tp) := by
    simp only [Expr.eval, v, hs, hu, sgTarget, natEq_eval, sigStToVal]
  simp only [Comp.eval, c1, c2]
  by_cases h1 : (g.principals.any fun x => x.1 == u.val) = true
  · simp only [h1, ite_true, sigLiftStep, stepKeyIndForSigPrim, Option.isSome_none,
      Bool.false_eq_true, ite_false, embedPrim_pure, pure_bind, sigLiftK, map_pure]
    simp only [Expr.eval, v, hs, Prod.map, id]
    rfl
  by_cases h2 : (u.val == tp) = true
  · simp only [h1, h2, ite_true, ite_false, sigLiftStep, stepKeyIndForSigPrim, Option.isSome_none,
      Bool.false_eq_true]
    core_simp [hs, hu, sgPk, sgUpd, sgGame, sgTarget, sgForgery, sgBudget, sigStToVal,
      liftBase_eval]
    simp only [embedPrim_bind, embedPrim_pure, bind_assoc, pure_bind, sigLiftK, sampleScalar32,
      map_eq_bind_pure_comp, Function.comp_def, Prod.map, id]
    rfl
  · simp only [h1, h2, ite_false, Bool.false_eq_true]
    rw [onGame_eval S sV env _ b hs _ _
      (initPrinB_eval useRo S K .zero (.cons (keyIndStateToVal g) env) g rfl hB uV u hu)]
    simp only [sigLiftStep, stepKeyIndForSigPrim, Option.isSome_none, Bool.false_eq_true, ite_false,
      h1, h2]
    simp only [embedPrim_bind, embedPrim_pure, bind_assoc, pure_bind, sigLiftK,
      map_eq_bind_pure_comp, Function.comp_def, Prod.map, id]

theorem sigCorruptB_eval (uV : Var Γ₂ .nat) (u : Fin S.N_id) (hu : env.get (Ext.wk uV) = u.val) :
    (sigCorruptB K sV uV).eval env =
      Prod.map keyIndRespToVal id <$>
        sigLiftStep sigStToVal (stepKeyIndForSigPrim useRo S (.corruptIK u)) s b := by
  rcases s with ⟨g, tp, tpk, fg⟩
  subst hf
  unfold sigCorruptB
  have c2 : (natEq (v uV) (sgTarget (v sV))).eval env = (u.val == tp) := by
    simp only [Expr.eval, v, hs, hu, sgTarget, natEq_eval, sigStToVal]
  by_cases h2 : (u.val == tp) = true
  · simp only [Comp.eval, c2, h2, ite_true]
    simp only [caseOptV, Comp.eval, Expr.eval, eFind, eMap, v, hs, hu, stUpd, stPrin, sgGame, sgUpd,
      sgTarget, sgPk, sgForgery, sgBudget, rNone, peUpd, peMk, peSecIKA0, peSecIKAsign, peIkAPk,
      peIkSignPk, natEq_eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
      keyIndStateToVal, sigStToVal, List.take_of_length_le, List.length_map,
      hB.principals_le]
    simp only [sigLiftStep, stepKeyIndForSigPrim, Option.isSome_none, Bool.false_eq_true, ite_false,
      h2, ite_true]
    rcases hfd : g.principals.find? (fun x => x.1 == u.val) with _ | ⟨i, e⟩
    · simp [List.find?_map, hfd, sigLiftK, sigStToVal, keyIndStateToVal]
    · simp [List.find?_map, hfd, Function.comp_def, sigLiftK, sigStToVal, keyIndStateToVal,
        List.map_map]
      intro a b' _; split_ifs <;> rfl
  · simp only [Comp.eval, c2, h2, ite_false, Bool.false_eq_true]
    rw [onGame_eval S sV env _ b hs _ _
      (corruptB_eval useRo S K .zero (.cons (keyIndStateToVal g) env) g rfl hB uV u hu)]
    simp only [sigLiftStep, stepKeyIndForSigPrim, Option.isSome_none, Bool.false_eq_true, ite_false,
      h2]
    simp only [embedPrim_bind, embedPrim_pure, bind_assoc, pure_bind, sigLiftK,
      map_eq_bind_pure_comp, Function.comp_def, Prod.map, id]

theorem sigGenSpkB_eval (xV : Var Γ₂ (.prod .nat .nat)) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hx : env.get (Ext.wk xV) = (u.val, j.val)) :
    (sigGenSpkB K sV xV).eval env =
      Prod.map keyIndRespToVal id <$>
        sigLiftStep sigStToVal (stepKeyIndForSigPrim useRo S (.genSPK u j)) s b := by
  rcases s with ⟨g, tp, tpk, fg⟩
  subst hf
  unfold sigGenSpkB
  have c2 : (natEq (.fst (v xV)) (sgTarget (v sV))).eval env = (u.val == tp) := by
    simp only [Expr.eval, v, hs, hx, sgTarget, natEq_eval, sigStToVal]
  by_cases h2 : (u.val == tp) = true
  · simp only [Comp.eval, c2, h2, ite_true]
    have c3 : (eAny K (stSpks (sgGame (v sV))) fun e => nat2Eq (.fst (v e)) (v xV)).eval env =
        g.spkBundles.any (fun x => x.1.1 == u.val && x.1.2 == j.val) := by
      core_simp [hs, hx, sgGame, sigStToVal, List.take_of_length_le, hB.spkBundles_le, Prod.map, id]
    simp only [c3, sigLiftStep, stepKeyIndForSigPrim, Option.isSome_none, Bool.false_eq_true,
      ite_false, h2, ite_true, nat2_beq]
    by_cases h3 : (g.spkBundles.any fun x => x.1.1 == u.val && x.1.2 == j.val) = true
    · simp only [h3, ite_true, embedPrim_pure, pure_bind, sigLiftK, map_pure]
      simp only [Expr.eval, v, hs, Prod.map, id]
      rfl
    simp only [h3, ite_false, Bool.false_eq_true]
    core_simp [hs, hx, sgGame, sgUpd, sgPk, sgTarget, sgForgery, sgBudget, sigStToVal,
      List.take_of_length_le, hB.principals_le, liftBase_eval, qChalSign_eval]
    rcases hfd : g.principals.find? (fun x => x.1 == u.val) with _ | ⟨i, e⟩
    · simp [hfd, sigLiftK, sigStToVal, keyIndStateToVal]
    · simp [hfd]
      cases b with
      | zero =>
        simp only [sigLiftK, ite_true, sampleScalar32, Prod.map, id, sigStToVal,
          keyIndStateToVal, map_eq_bind_pure_comp, Function.comp_def, pure_bind, Prod.mk.eta,
          List.map_id']
        rfl
      | succ b' =>
        simp only [sigLiftK, Nat.add_one_ne_zero, ite_false, sampleScalar32, sampleKemKeyGenPrim,
          embedPrim_bind, bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def, Prod.map,
          id, sigStToVal, keyIndStateToVal, Nat.add_sub_cancel, Prod.mk.eta, List.map_id',
          List.map_cons]
        rfl
  · simp only [Comp.eval, c2, h2, ite_false, Bool.false_eq_true]
    rw [onGame_eval S sV env _ b hs _ _
      (genSpkB_eval useRo S K .zero (.cons (keyIndStateToVal g) env) g rfl hB xV u j hx)]
    simp only [sigLiftStep, stepKeyIndForSigPrim, Option.isSome_none, Bool.false_eq_true, ite_false,
      h2]
    simp only [embedPrim_bind, embedPrim_pure, bind_assoc, pure_bind, sigLiftK,
      map_eq_bind_pure_comp, Function.comp_def, Prod.map, id]

omit hf in
theorem extractC_eval (buV : Var Γ₂ preKeyBundleTy) (bu : PreKeyBundleInput)
    (hbu : env.get (Ext.wk buV) = preKeyBundleToVal bu) :
    (extractC S K sV buV).eval env =
      _root_.SignalPqxdh.Security.embedPrim (spec := eufCmaSignOracle.spec)
        (extractBundleForgeryPrim S s.targetParty s.targetPk
          s.gameState.principals s.gameState.spkBundles bu s.forgery) := by
  rcases s with ⟨g, tp, tpk, fg⟩
  unfold extractC extractBundleForgeryPrim
  simp only [bindV, letV_eval, Comp.eval, liftBase_eval]
  rw [honestPeerC_eval]
  core_simp [hs, hbu, sgGame, sgForgery, sgTarget, sgPk, sigStToVal, decPrin_enc,
    preKeyBundleToVal, List.take_of_length_le, hB.spkBundles_le, widenEC_eval]
  simp only [embedPrim_bind, embedPrim_pure, Prod.map, id]
  rw [decPrin_enc, List.take_of_length_le hB.principals_le]
  refine bind_congr2 rfl fun peer => bind_congr2 ?_ fun v1 => bind_congr2 ?_ fun v2 => ?_
  · rw [hs, hbu]; rfl
  · rw [hs, hbu]; rfl
  · congr 1
    rcases fg with _ | fg
    · rcases peer with _ | k
      · rfl
      · simp only [encodeEC, encodeKEM]
        rfl
    · rfl

theorem sigInitiateOpkB_eval (xV : Var Γ₂ initQTy) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (bu : PreKeyBundleInput) (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal bu))) :
    (sigInitiateB useRo S K true sV xV).eval env =
      Prod.map keyIndRespToVal id <$>
        sigLiftStep sigStToVal (stepKeyIndForSigPrim useRo S (.initiateOPK u i bu)) s b := by
  have hE := extractC_eval S K sV (.cons (preKeyBundleToVal bu) env) s b hs hB
    (Γ₂ := preKeyBundleTy :: Δ) .zero bu rfl
  rcases s with ⟨g, tp, tpk, fg⟩
  subst hf
  unfold sigInitiateB
  simp only [letV_eval, bindV, Comp.eval, Expr.eval, v, hx, liftBase_eval, ↓reduceIte]
  rw [hE]
  simp only [sigLiftStep, stepKeyIndForSigPrim, Option.isSome_none, Bool.false_eq_true, ite_false,
    embedPrim_bind, embedPrim_pure, bind_assoc, map_eq_bind_pure_comp]
  refine bind_congr2 rfl fun fg' => ?_
  have hI := initiateOpkB_eval useRo S K
    (Γ₁ := keyIndStateTy :: .opt (.prod (B 1569) (B 64)) :: preKeyBundleTy :: Δ) .zero
    (.cons (keyIndStateToVal g) (.cons fg' (.cons (preKeyBundleToVal bu) env))) g rfl hB
    xV u i bu hx
  simp only [Env.get_succ', Env.get_zero', Ext.step_wk', Ext.refl_wk', hs, sigStToVal]
  rw [hI]
  simp only [map_eq_bind_pure_comp, embedPrim_bind, embedPrim_pure, bind_assoc, pure_bind, sigLiftK,
    Function.comp_def, encRS, Prod.map, id, sigStToVal]

theorem sigInitiateNoOpkB_eval (xV : Var Γ₂ initQTy) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (bu : PreKeyBundleInput) (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal bu))) :
    (sigInitiateB useRo S K false sV xV).eval env =
      Prod.map keyIndRespToVal id <$>
        sigLiftStep sigStToVal (stepKeyIndForSigPrim useRo S (.initiateNoOPK u i bu)) s b := by
  have hE := extractC_eval S K sV (.cons (preKeyBundleToVal bu) env) s b hs hB
    (Γ₂ := preKeyBundleTy :: Δ) .zero bu rfl
  rcases s with ⟨g, tp, tpk, fg⟩
  subst hf
  unfold sigInitiateB
  simp only [letV_eval, bindV, Comp.eval, Expr.eval, v, hx, liftBase_eval, Bool.false_eq_true,
    ↓reduceIte]
  rw [hE]
  simp only [sigLiftStep, stepKeyIndForSigPrim, Option.isSome_none, Bool.false_eq_true, ite_false,
    embedPrim_bind, embedPrim_pure, bind_assoc, map_eq_bind_pure_comp]
  refine bind_congr2 rfl fun fg' => ?_
  have hI := initiateNoOpkB_eval useRo S K
    (Γ₁ := keyIndStateTy :: .opt (.prod (B 1569) (B 64)) :: preKeyBundleTy :: Δ) .zero
    (.cons (keyIndStateToVal g) (.cons fg' (.cons (preKeyBundleToVal bu) env))) g rfl hB
    xV u i bu hx
  simp only [Env.get_succ', Env.get_zero', Ext.step_wk', Ext.refl_wk', hs, sigStToVal]
  rw [hI]
  simp only [map_eq_bind_pure_comp, embedPrim_bind, embedPrim_pure, bind_assoc, pure_bind, sigLiftK,
    Function.comp_def, encRS, Prod.map, id, sigStToVal]

end Branches

theorem sigLiftStep_done_map {S : Setup} (s : SigReductionState (KeyIndState S)) (b : Nat)
    (m : OracleComp PrimBaseSpec (KeyIndResponse × KeyIndState S)) :
    Prod.map keyIndRespToVal id <$> sigLiftStep (sigStToVal (S := S))
        (fun s => do
          let (out, gs') ← m
          return SigStepResultPrim.done out { s with gameState := gs' }) s b =
      (fun p : KeyIndResponse × KeyIndState S =>
        (keyIndRespToVal p.1, sigStToVal ({ s with gameState := p.2 }, b))) <$>
        _root_.SignalPqxdh.Security.embedPrim (spec := eufCmaSignOracle.spec) m := by
  simp only [sigLiftStep, embedPrim_bind, embedPrim_pure, bind_assoc, pure_bind, sigLiftK,
    map_eq_bind_pure_comp, Function.comp_def, Prod.map, id_eq]

abbrev sigH (useRo : Bool) (S : Setup) (K : Nat) (q : KeyIndQuery S)
    (s : SigReductionState (KeyIndState S)) (b : Nat) :=
  (sigHandleC useRo S K (Γ₁ := [sigStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [sigStTy, keyIndQueryTy]) .zero .zero).eval
    (.cons (sigStToVal (s, b)) (.cons (keyIndQueryToVal q) .nil))

set_option hygiene false in
macro "sig_generic" q:term:max core:term:max : tactic => `(tactic| (
  refine Eq.trans (b := (fun p : KeyIndResponse × KeyIndState S =>
      (keyIndRespToVal p.1, sigStToVal ({ (⟨g, tp, tpk, none⟩ : SigReductionState _) with
        gameState := p.2 }, b))) <$>
      _root_.SignalPqxdh.Security.embedPrim (spec := eufCmaSignOracle.spec)
        ((pqxdhKeyIndImplPrim useRo S $q).run g)) ?_ ?_
  · exact onGame_eval S _ _ ⟨g, tp, tpk, none⟩ b rfl _ _ $core
  · exact (sigLiftStep_done_map _ b _).symm))

theorem sigH_eval (useRo : Bool) (S : Setup) (K : Nat) (q : KeyIndQuery S)
    (s : SigReductionState (KeyIndState S)) (b : Nat) (hB : KeyIndListsBounded s.gameState K) :
    sigH useRo S K q s b =
      Prod.map keyIndRespToVal id <$>
        sigLiftStep sigStToVal (stepKeyIndForSigPrim useRo S q) s b := by
  rcases s with ⟨g, tp, tpk, _ | fg⟩
  · cases q with
    | initPrin u => exact sigInitPrinB_eval useRo S K _ _ _ b rfl rfl hB _ u rfl
    | corruptIK u => exact sigCorruptB_eval useRo S K _ _ _ b rfl rfl hB _ u rfl
    | genSPK u j => exact sigGenSpkB_eval useRo S K _ _ _ b rfl rfl hB _ u j rfl
    | genOPK u j o => sig_generic (.genOPK u j o) (genOpkB_eval useRo S K _ _ g rfl hB _ u j o rfl)
    | initiateOPK u i bu => exact sigInitiateOpkB_eval useRo S K _ _ _ b rfl rfl hB _ u i bu rfl
    | initiateNoOPK u i bu => exact sigInitiateNoOpkB_eval useRo S K _ _ _ b rfl rfl hB _ u i bu rfl
    | acceptOPK k j o h =>
      sig_generic (.acceptOPK k j o h) (acceptOpkB_eval useRo S K _ _ g rfl hB _ k j o h rfl)
    | acceptNoOPK k j l h =>
      sig_generic (.acceptNoOPK k j l h) (acceptNoOpkB_eval useRo S K _ _ g rfl hB _ k j l h rfl)
    | testSession sid =>
      sig_generic (.testSession sid) (testB_eval useRo S K _ _ g rfl hB _ sid rfl)
    | roQuery sec => sig_generic (.roQuery sec) (roB_eval useRo S K _ _ g rfl hB _ sec rfl)
    | revealDhSecrets => sig_generic .revealDhSecrets (revealDhB_eval useRo S K _ _ g rfl hB)
    | revealSessionKey sid =>
      sig_generic (.revealSessionKey sid) (revealB_eval useRo S K _ _ g rfl hB _ sid rfl)
    | registerKey sk =>
      sig_generic (.registerKey sk)
        (registerB_eval (useRo := useRo) (S := S) (s := g) (hs := rfl) (sk := sk) (hsk := rfl))
    | revealSpkSk u j =>
      sig_generic (.revealSpkSk u j) (revealSpkB_eval useRo S K _ _ g rfl hB _ u j rfl)
  · simp only [sigLiftStep, stepKeyIndForSigPrim, Option.isSome_some, ↓reduceIte, embedPrim_pure,
      pure_bind, sigLiftK, map_pure]
    rfl

theorem sig_generic_hol (useRo : Bool) (S : Setup) (n : Nat) (q : KeyIndQuery S)
    (s : SigReductionState (KeyIndState S)) (fg : Option (Bytes × Bytes))
    (hB : KeyIndListsBounded s.gameState n) :
    HoldsOnLeaves (SigResInv (R := KeyIndResponse) (fun s' : SigReductionState (KeyIndState S) =>
        KeyIndListsBounded s'.gameState (n + 1)))
      (do
        let (out, gs') ← (pqxdhKeyIndImplPrim useRo S q).run s.gameState
        return SigStepResultPrim.done out { s with gameState := gs', forgery := fg }) :=
  HoldsOnLeaves.bind (pqxdhKeyIndImplPrim_hol useRo S n q s.gameState hB)
    fun _ hx => HoldsOnLeaves.pure hx

theorem stepKeyIndForSigPrim_hol (useRo : Bool) (S : Setup) (n : Nat) (q : KeyIndQuery S)
    (s : SigReductionState (KeyIndState S)) (hB : KeyIndListsBounded s.gameState n) :
    HoldsOnLeaves (SigResInv (fun s' : SigReductionState (KeyIndState S) =>
        KeyIndListsBounded s'.gameState (n + 1)))
      (stepKeyIndForSigPrim useRo S q s) := by
  have hB1 : KeyIndListsBounded s.gameState (n + 1) := hB.mono (Nat.le_succ n)
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hB
  unfold stepKeyIndForSigPrim
  split_ifs with hf
  · exact HoldsOnLeaves.pure hB1
  cases q <;> dsimp only
  case initPrin u =>
    split_ifs
    · exact HoldsOnLeaves.pure hB1
    · refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
        HoldsOnLeaves.pure ?_
      khol_leaf
    · exact sig_generic_hol useRo S n _ s s.forgery ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
  case corruptIK u =>
    split_ifs
    · split
      · exact HoldsOnLeaves.pure hB1
      · refine HoldsOnLeaves.pure ?_
        khol_leaf
    · exact sig_generic_hol useRo S n _ s s.forgery ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
  case genSPK u j =>
    split_ifs
    · exact HoldsOnLeaves.pure hB1
    · split
      · exact HoldsOnLeaves.pure hB1
      · refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
          HoldsOnLeaves.pure ⟨hB1, fun _ _ _ => ?_⟩
        khol_leaf
    · exact sig_generic_hol useRo S n _ s s.forgery ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
  case initiateOPK u i bu =>
    exact HoldsOnLeaves.bind_const _ fun fg =>
      sig_generic_hol useRo S n _ s fg ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
  case initiateNoOPK u i bu =>
    exact HoldsOnLeaves.bind_const _ fun fg =>
      sig_generic_hol useRo S n _ s fg ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
  all_goals exact sig_generic_hol useRo S n _ s s.forgery ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩

/-! ## Full reduction -/

theorem rdec_map_keyIndRespToVal {ι : Type} {spec : OracleSpec.{0, 0} ι}
    (S : Setup) (q : KeyIndQuery S)
    (m : OracleComp spec (KeyIndResponse × sigStTy.denote)) :
    (do
      let p ← Prod.map keyIndRespToVal id <$> m
      return ((keyIndCodec S).rdec q p.1, p.2)) = m := by
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_def, pure_bind, Prod.map, id, keyIndCodec, keyIndRespToVal,
    keyIndRdec_keyIndRenc, Prod.mk.eta, bind_pure]

private theorem runWithSigBudgetPrim_eq_of_ge {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI}
    {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (SigStepResultPrim St (GSpec.Range q)))
    (mx : OracleComp (unifSpec + GSpec) α) (rem : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ ιI => q.isRight = true) rem)
    (st : St) (b₁ b₂ : Nat) (hb₁ : rem ≤ b₁) (hb₂ : rem ≤ b₂) :
    runWithSigBudgetPrim step mx st b₁ = runWithSigBudgetPrim step mx st b₂ := by
  induction mx using OracleComp.inductionOn generalizing rem st b₁ b₂ with
  | pure a => rfl
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hMx
    rcases q with uq | gq
    · have hCont : ∀ u, IsQueryBoundP (k u) (fun q : ℕ ⊕ ιI => q.isRight = true) rem := by
        intro u; simpa using hMx.2 u
      change (liftM (OracleSpec.query (spec := PrimBaseSpec + sigOracleSpec)
          (Sum.inl (Sum.inl uq))) >>= fun u => runWithSigBudgetPrim step (k u) st b₁) =
        (liftM (OracleSpec.query (spec := PrimBaseSpec + sigOracleSpec)
          (Sum.inl (Sum.inl uq))) >>= fun u => runWithSigBudgetPrim step (k u) st b₂)
      exact congrArg _ (funext fun u => ih u rem (hCont u) st b₁ b₂ hb₁ hb₂)
    · have hPos : 0 < rem := hMx.1.resolve_left (by simp)
      have hCont : ∀ r, IsQueryBoundP (k r) (fun q : ℕ ⊕ ιI => q.isRight = true) (rem - 1) := by
        intro r; simpa using hMx.2 r
      rcases b₁ with _ | b₁'
      · omega
      rcases b₂ with _ | b₂'
      · omega
      change (_root_.SignalPqxdh.Security.embedPrim (spec := sigOracleSpec) (step gq st) >>= fun sr =>
          match sr with
          | .done res st' => runWithSigBudgetPrim step (k res) st' (b₁' + 1)
          | .signTwo msg1 k1 fallback => do
            let sig1 ← query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inr (SigQuery.sign msg1))
            let pq ← _root_.SignalPqxdh.Security.embedPrim (spec := sigOracleSpec) sampleKemKeyGenPrim
            let (msg2, k2) := k1 pq sig1
            let sig2 ← query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inr (SigQuery.sign msg2))
            let p := k2 sig2
            runWithSigBudgetPrim step (k p.1) p.2 b₁') =
        (_root_.SignalPqxdh.Security.embedPrim (spec := sigOracleSpec) (step gq st) >>= fun sr =>
          match sr with
          | .done res st' => runWithSigBudgetPrim step (k res) st' (b₂' + 1)
          | .signTwo msg1 k1 fallback => do
            let sig1 ← query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inr (SigQuery.sign msg1))
            let pq ← _root_.SignalPqxdh.Security.embedPrim (spec := sigOracleSpec) sampleKemKeyGenPrim
            let (msg2, k2) := k1 pq sig1
            let sig2 ← query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inr (SigQuery.sign msg2))
            let p := k2 sig2
            runWithSigBudgetPrim step (k p.1) p.2 b₂')
      refine congrArg _ (funext fun sr => ?_)
      rcases sr with ⟨res, st'⟩ | ⟨msg1, k1, fb⟩
      · exact ih res (rem - 1) (hCont res) st' (b₁' + 1) (b₂' + 1) (by omega) (by omega)
      · dsimp only
        refine congrArg _ (funext fun sig1 => congrArg _ (funext fun pq => ?_))
        rcases k1 pq sig1 with ⟨msg2, k2⟩
        dsimp only
        exact congrArg _ (funext fun sig2 =>
          ih (k2 sig2).1 (rem - 1) (hCont (k2 sig2).1) (k2 sig2).2 b₁' b₂' (by omega) (by omega))

theorem sigKeyIndProg_eval_eq_of_bound (useRo : Bool) (S : Setup) (K : Nat) (A : KeyIndAdversary S)
    (pk : Bytes) (hN : 0 < S.N_id) (rem : Nat)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) rem) (hK : rem ≤ K) :
    (sigKeyIndProg useRo S K).eval (fun _ => A.run) pk =
      sigReductionKeyIndCoreRun useRo S A pk := by
  have hstep : ∀ (q : KeyIndQuery S) (st : SigReductionState (KeyIndState S)) (b : Nat),
      KeyIndListsBounded st.gameState K →
      (do
          let p ← (sigKeyIndProg useRo S K).handle.eval
            (.cons (sigStToVal (st, b)) (.cons ((keyIndCodec S).qenc q) .nil))
          return ((keyIndCodec S).rdec q p.1, p.2) :
          OracleComp (PrimBaseSpec + sigOracleSpec) _) =
        sigLiftStep sigStToVal (stepKeyIndForSigPrim useRo S q) st b := by
    intro q st b hB
    change (do let p ← sigH useRo S K q st b; return ((keyIndCodec S).rdec q p.1, p.2)) = _
    rw [sigH_eval useRo S K q st b hB]
    exact rdec_map_keyIndRespToVal S q _
  have : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
  have hinit1 : (sigKeyIndProg useRo S K).init.eval (.cons pk .nil) =
      (do
        let k ← _root_.SignalPqxdh.Security.embedPrim (spec := eufCmaSignOracle.spec)
          (_root_.SignalPqxdh.Security.embedUnif ($ᵗ (Fin S.N_id)))
        let secb ← _root_.SignalPqxdh.Security.embedPrim (spec := eufCmaSignOracle.spec)
          (_root_.SignalPqxdh.Security.embedUnif ($ᵗ Bool))
        pure ((), sigStToVal (⟨KeyIndState.empty S secb, k.val, pk, none⟩, min K S.N_spk_tot))) := by
    simp only [sigKeyIndProg, bindV, Comp.eval, Expr.eval, v, emptyStE, stMk, keyIndStateToVal,
      KeyIndState.empty, List.map_nil, sigStToVal, liftBase_eval, sIndex_eval, sBool_eval,
      FgGapDh.sampleIndexRange, hN, dite_true, _root_.SignalPqxdh.Security.embedUnif,
      liftComp_bind, liftComp_pure, embedPrim_bind, embedPrim_pure, bind_assoc, pure_bind,
      Env.get_succ', Env.get_zero', Ext.step_wk', Ext.refl_wk']
  have hfin1 : ∀ (st : sigStTy.denote) (a : Bool),
      (sigKeyIndProg useRo S K).finish.eval (.cons st (.cons a .nil)) =
        pure (st.2.2.2.1.getD ([], [])) := by
    intro st a
    have hN0 : S.N_id ≠ 0 := Nat.ne_of_gt hN
    rcases st with ⟨g, k, pk, _ | fg, b⟩ <;>
      simp [sigKeyIndProg, Comp.eval, Expr.eval, hN0, eCaseOpt, sgForgery, v]
  rw [GRed_eval_pqSigIface, hinit1]
  simp only [sigReductionKeyIndCoreRun, hN, dite_true, simulateKeyIndForSigPrim,
    simulateForSigPrim, bind_assoc, pure_bind]
  refine bind_congr fun k => bind_congr fun secb => ?_
  have hbud :
      runWithSigBudgetPrim (stepKeyIndForSigPrim useRo S) A.run
        ⟨KeyIndState.empty S secb, k.val, pk, none⟩ (min K S.N_spk_tot) =
      runWithSigBudgetPrim (stepKeyIndForSigPrim useRo S) A.run
        ⟨KeyIndState.empty S secb, k.val, pk, none⟩ S.N_spk_tot := by
    by_cases hle : S.N_spk_tot ≤ K
    · rw [Nat.min_eq_right hle]
    · exact runWithSigBudgetPrim_eq_of_ge (stepKeyIndForSigPrim useRo S) A.run rem hA _ _ _
        (by omega) (by omega)
  have hsim := runWithIfaceStep_sig_map_state_bounded sigStToVal
    (fun s : SigReductionState (KeyIndState S) => s.forgery.getD ([], []))
    (fun st : sigStTy.denote => st.2.2.2.1.getD ([], [])) (fun _ _ => rfl)
    (fun n st => KeyIndListsBounded st.gameState n) (fun h hB => hB.mono h)
    (stepKeyIndForSigPrim useRo S)
    (fun q st => do
      let p ← (sigKeyIndProg useRo S K).handle.eval
        (.cons st (.cons ((keyIndCodec S).qenc q) .nil))
      return ((keyIndCodec S).rdec q p.1, p.2))
    K hstep (fun n q st hB => stepKeyIndForSigPrim_hol useRo S n q st hB) A.run rem hA 0
    ⟨KeyIndState.empty S secb, k.val, pk, none⟩ (min K S.N_spk_tot)
    (by constructor <;> exact Nat.le_refl _) (by omega)
  rw [hbud] at hsim
  have hsim2 := congrArg (fun m => Prod.snd <$> m) hsim
  simp only [Prod.map, id, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
    pure_bind] at hsim2
  refine Eq.trans ?_ hsim2
  refine bind_congr fun x => ?_
  exact hfin1 x.2 x.1

theorem sigKeyIndProg_eval_eq_of_pos (useRo : Bool) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (pk : Bytes) (hN : 0 < S.N_id) :
    (sigKeyIndProg useRo S b.q_total).eval (fun _ => A.1.run) pk =
      (sigReductionKeyIndCore useRo S b A).run pk := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total := by
    have h := A.2.2.2.2.1
    convert h using 1; funext q; cases q <;> rfl
  exact sigKeyIndProg_eval_eq_of_bound useRo S b.q_total A.1 pk hN b.q_total hA le_rfl

/-- `SigEufCma` adversary obtained by running `sigKeyIndProg` with capacity `b.q_total`. -/
def sigKeyIndDslAdv (useRo : Bool) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : SigEufCmaAdv where
  run pk := (sigKeyIndProg useRo S b.q_total).eval (fun _ => A.1.run) pk
  q_sig := (sigReductionKeyIndCore useRo S b A).q_sig
  q_prim := (sigReductionKeyIndCore useRo S b A).q_prim

theorem sigKeyIndProg_finish_eval_of_N_id_zero (useRo : Bool) (S : Setup) (K : Nat)
    (hN0 : S.N_id = 0) (st : sigStTy.denote) (a : Bool) :
    (sigKeyIndProg useRo S K).finish.eval (.cons st (.cons a .nil)) =
      pure ([], []) := by
  simp [sigKeyIndProg, Comp.eval, Expr.eval, hN0]

/-- `sigKeyIndDslAdv` and the shallow `sigReductionKeyIndCore` have the same `SigEufCma` experiment
    distribution. -/
theorem sigKeyIndProg_evalDist_eq (P : Primitives) (useRo : Bool) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    𝒟[sigEufCmaExp P (sigKeyIndDslAdv useRo S b A)] =
      𝒟[sigEufCmaExp P (sigReductionKeyIndCore useRo S b A)] := by
  by_cases hN : 0 < S.N_id
  · have hrun : sigKeyIndDslAdv useRo S b A = sigReductionKeyIndCore useRo S b A := by
      have h := fun pk => sigKeyIndProg_eval_eq_of_pos useRo S b A pk hN
      simp only [sigKeyIndDslAdv, h]
    rw [hrun]
  · have hN0 : S.N_id = 0 := by omega
    rcases A with ⟨A0, hA0⟩
    let pre := fun (pk : Bytes) => do
      let p ← (sigKeyIndProg useRo S b.q_total).init.eval (.cons pk .nil)
      (simulateQ (sigKeyIndProg useRo S b.q_total).impl A0.run).run p.2
    have h1 : ∀ pk, (sigKeyIndProg useRo S b.q_total).eval (fun _ => A0.run) pk =
        (pre pk >>= fun _ => Pure.pure ([], [])) := by
      intro pk
      unfold CostedReduction.eval
      dsimp only [pre]
      rw [bind_assoc]
      refine bind_congr fun ⟨a, st0⟩ => ?_
      dsimp only
      refine bind_congr fun ⟨b_out, st1⟩ => ?_
      dsimp only
      exact sigKeyIndProg_finish_eval_of_N_id_zero useRo S b.q_total hN0 st1 b_out
    refine sigEufCmaExp_evalDist_noSig P _ _ pre ([], []) h1 ?_ ?_
    · intro pk
      simp [sigReductionKeyIndCore, sigReductionKeyIndCoreRun, hN]
    · intro pk
      have h := sigKeyIndProg_chalBounded useRo S b.q_total (fun _ => A0.run) pk
      have h2 : 2 * S.N_spk_tot = 0 := by simp [Setup.N_spk_tot, hN0]
      rw [h2] at h
      exact h

theorem sigKeyIndProg_sigEufCma_eq (P : Primitives) (useRo : Bool) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    SigEufCma P (sigKeyIndDslAdv useRo S b A) =
      SigEufCma P (sigReductionKeyIndCore useRo S b A) := by
  unfold SigEufCma; rw [sigKeyIndProg_evalDist_eq]

end SignalPqxdh.Security.ReductionDsl.KeyInd
