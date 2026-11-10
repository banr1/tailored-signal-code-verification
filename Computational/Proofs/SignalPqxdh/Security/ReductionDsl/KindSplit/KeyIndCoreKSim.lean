/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.ReductionDsl.StepSimTwoStage -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimHelpers
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimArms
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimArmsSess

/-!
# Two-Stage Forgetful Simulation for `shcrKeyInd1KeyKindAtomicProg`

Proves `shcrKeyInd1KeyKindAtomicProg_twoStageForgetSim`, establishing two-stage forgetful step
simulation (`TwoStageForgetSim`) from `shcrKeyInd1KeyKindAtomicProg` to
`shcrKeyInd1KeyActiveAtomicProg` for any challenger input.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSim

open OracleSpec OracleComp
open _root_.SignalPqxdh (
  Setup QueryBudget KeyIndQuery keyIndSpec activeSendCount activeSpkCount
)
open _root_.ReductionDsl (
  Ty Var Expr Comp Env pqAtomicSig pqAtomicOps pqPrimIface pqKeyIndCodec
  PB drKeyT
)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (
  embedTy embedVal projVal embedEnv mapComp mapComp_eval compRename compRename_eval
  embedVal_projVal projVal_embedVal liftKeyIndHandle liftKeyIndHandle_eval
  liftKeyInd2Stage tlPrimKeyInd
)
open _root_.Computational.Proofs.ReductionDsl.StepSim (bumpPred bumpPred_apply)
open _root_.Computational.Proofs.ReductionDsl.StepSimTwoStage (
  TwoStageForgetSim forgetPreOut
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  Ext PT SCS accQTy bindV caseOptV caseSumV corruptB emptyStE genOpkB hkdfOrRoC initPrin1KeyB
  keyIndLoopBound keyIndQueryTy keyIndStateTy letV onBase pauseCheckC pauseTy registerB revealB
  revealDhB revealSpkB roB sBool sIndex scBase scChosen scCnt scIR scMk scRR scSIdx scTB scTPk
  scTSk scUpd shcrAcceptB shcrFinE shcrResumeC shcrStTy testB v
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (twoVarRen)
open _root_.Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  shcr1KeyActivePostC shcr1KeyActivePreC shcrActiveGenSpkB shcrActivePostTailC
  shcrKeyInd1KeyActiveAtomicProg shcrKeyInd1KeyActiveDslProg
)
open _root_.Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (
  shcr1KeyKindBaseInit shcr1KeyKindBaseInit_unsupported shcr1KeyKindHandlePostC
  shcr1KeyKindHandlePreC shcr1KeyKindInitC shcr1KeyKindResumeC shcrKeyInd1KeyKindAtomicProg
  shcrChDoneLeg_unsupported shcrExtractLeg_unsupported
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  dispatchKeyIndQ emptyRoAvlE keyIndCoreFuels roAvlTy roListAtomicTy roListLegacyTy
  roShadowQueryC runAt2 runAt3 runAt6 shcrChDoneLeg shcrExtractLeg shcrKindChDoneC
  shcrKindFinishC shcrKindHandlePostC shcrKindHandlePreC shcrKindResumeC shcrKindStTy
  shcrResumePostRoC shcrResumePreRoC shcrRoListAtomicE
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase (
  BaseOnlineLenInv RoCacheAvlInv ShcrPauseInv ShcrSimInv dispatchKeyIndQ_eval fixSent
  fixSent_keyIndSentinel forgetShcrKindActive keyIndSimBounds keyIndSimPred
  mem_support_sIndex_lt roShadowQueryC_eval_sim runAt2_eval runAt3_eval runAt6_eval
  stRoList stSessList
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimHelpers (
  embedVal_roList_eq fixSent_of_lt_activeSendCount fixShcrLegacySent
  forgetShcrKindActive_eq_embed hkdfOrRoC_unsup initFinishPostRoC_fuel_eq
  initFinishPostRoC_mem_support ro_bounds_of_le shcr1KeyActiveFinish_unsup
  shcr1KeyActiveHandlePost_unsup shcr1KeyActiveHandlePre_unsup shcr1KeyActiveInit_unsup
  shcr1KeyActiveResume_unsup shcrExtractLeg_eq_active shcrResumeC_eq_split
  shcrResumePostRoC_fixSent_comm shcrResumePostRoC_unsup shcrResumePreRoC_unsup
  shcrRoListAtomicE_eval
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimArms (
  activePostEval activePreEval shcrCorruptArm_sim shcrGenOpkArm_sim shcrGenSpkArm_sim
  shcrInitPrinArm_sim shcrRegKeyArm_sim shcrRevDhArm_sim shcrRevSpkArm_sim shcrRoArmK_sim
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimArmsSess (
  shcrAccNoOpkArmPost_sim shcrAccOpkArmPost_sim shcrInitNoOpkArmPost_sim
  shcrInitNoOpkArmPre_sim shcrInitOpkArmPost_sim shcrInitOpkArmPre_sim
  shcrRevSessArm_sim shcrTestArm_sim
)

private def activeInitC (S : Setup) (b : QueryBudget) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [.prod (_root_.SignalPqxdh.LegacyCosted.B 1568) (_root_.SignalPqxdh.LegacyCosted.B 3168)]
      (.prod .unit shcrStTy) :=
  let n_spk := activeSpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  if n_spk * n_send = 0 then
    bindV sBool fun secb =>
    .ret (.pair .unit (scMk (emptyStE (v secb)) .none
      (.fst (.var (.succ .zero))) (.snd (.var (.succ .zero))) (.nat 0) .nil .nil
      (.nat (b.q_total + 1)) (.fst (.var (.succ .zero)))))
  else
    bindV (sIndex n_spk) fun spkOrd =>
    bindV (sIndex n_send) fun sIdx =>
    bindV sBool fun secb =>
    .ret (.pair .unit (scMk (emptyStE (v secb)) (.some (.pair (v spkOrd) (.nat 0)))
      (.fst (.var (.succ (.succ (.succ .zero))))) (.snd (.var (.succ (.succ (.succ .zero)))))
      (.nat 0) .nil .nil (v sIdx) (.fst (.var (.succ (.succ (.succ .zero)))))))

private theorem shcr1KeyKindBaseInit_sim (S : Setup) (b : QueryBudget)
    (xL : Ty.denote (.prod (_root_.SignalPqxdh.LegacyCosted.B 1568)
      (_root_.SignalPqxdh.LegacyCosted.B 3168))) :
    Prod.map id (fixShcrLegacySent S b) <$>
      (shcr1KeyKindBaseInit S b).eval (.cons xL .nil) =
    (activeInitC S b).eval (.cons xL .nil) := by
  unfold shcr1KeyKindBaseInit activeInitC
  dsimp only
  split_ifs with hZero
  · simp only [bindV, Comp.eval, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    congr 1; funext secb
    simp only [Prod.map, id_eq, emptyStE, fixShcrLegacySent, fixSent_keyIndSentinel,
      Ext.wk, v, Expr.eval, Env.get]
  · have hSendPos : 0 < activeSendCount S b.q_on :=
      Nat.pos_of_ne_zero (right_ne_zero_of_mul hZero)
    simp only [bindV, Comp.eval, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    congr 1; funext spkOrd
    refine _root_.Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ ?_
    intro sIdx hsIdx
    have hLt : sIdx < activeSendCount S b.q_on := mem_support_sIndex_lt _ hSendPos _ hsIdx
    have hFix : fixSent S b sIdx = sIdx := fixSent_of_lt_activeSendCount hLt
    congr 1; funext secb
    simp only [Prod.map, id_eq, emptyStE, fixShcrLegacySent, Ext.wk, hFix, v, Expr.eval, Env.get]

private theorem shcr_hInit (S : Setup) (b : QueryBudget)
    (x : (embedTy (.prod (_root_.SignalPqxdh.LegacyCosted.B 1568)
      (_root_.SignalPqxdh.LegacyCosted.B 3168))).denote) :
    Prod.map id (forgetShcrKindActive S b) <$>
      (shcr1KeyKindInitC S b).eval (.cons x .nil) =
      (mapComp tlPrimKeyInd (activeInitC S b)).eval (.cons x .nil) ∧
    ∀ (as' : (Ty.prod .unit shcrKindStTy).denote),
      as' ∈ support ((shcr1KeyKindInitC S b).eval (.cons x .nil)) →
      ShcrSimInv S b 0 as'.2 := by
  let rInTy : PT := .prod (_root_.SignalPqxdh.LegacyCosted.B 1568)
    (_root_.SignalPqxdh.LegacyCosted.B 3168)
  let xL := projVal rInTy x
  have hx : Env.cons x Env.nil = embedEnv (Env.cons xL Env.nil) := by
    change Env.cons x Env.nil = Env.cons (embedVal rInTy xL) Env.nil
    rw [embedVal_projVal]
  let emptyAvl : roAvlTy.denote := (emptyRoAvlE (Γ := [])).eval .nil
  have hLhsEval : (shcr1KeyKindInitC S b).eval (.cons x .nil) =
      (fun p : Unit × Ty.denote shcrStTy => ((), (embedVal shcrStTy p.2, emptyAvl))) <$>
        (shcr1KeyKindBaseInit S b).eval (.cons xL .nil) := by
    simp only [shcr1KeyKindInitC, Comp.eval]
    rw [hx, mapComp_eval tlPrimKeyInd _ (shcr1KeyKindBaseInit_unsupported S b)]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
      emptyAvl, emptyRoAvlE, Expr.eval, Env.get]
    congr 1
  have hActUnsup : (activeInitC S b).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 :=
    shcr1KeyActiveInit_unsup S b
  refine ⟨?_, ?_⟩
  · rw [hLhsEval, hx, mapComp_eval tlPrimKeyInd _ hActUnsup, ← shcr1KeyKindBaseInit_sim S b xL]
    simp only [Functor.map_map]
    refine congrArg (· <$> _) (funext fun ⟨⟨⟩, sL⟩ => ?_)
    simp only [Prod.map, id_eq, forgetShcrKindActive_eq_embed, projVal_embedVal]
    rfl
  · intro as' has'
    rw [hLhsEval, map_eq_bind_pure_comp, mem_support_bind_iff] at has'
    rcases has' with ⟨⟨⟨⟩, sL⟩, hsMem, hasEq⟩
    simp only [Function.comp_def, support_pure, Set.mem_singleton_iff] at hasEq
    subst hasEq
    have hEmptyBase : ∃ secb : Bool,
        sL.1 = (secb, ([], ([], ([], ([], ([], ([], ([], ([], ([], [])))))))))) ∧
        sL.2.2.2.2.1 = 0 ∧ sL.2.2.2.2.2.1 = [] ∧ sL.2.2.2.2.2.2.1 = [] := by
      unfold shcr1KeyKindBaseInit at hsMem
      dsimp only at hsMem
      split_ifs at hsMem with hZero
      · simp only [bindV, Comp.eval, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hsMem
        rcases hsMem with ⟨secb, _, hEq⟩
        injection hEq with _ hsEq; subst hsEq
        exact ⟨secb, rfl, rfl, rfl, rfl⟩
      · simp only [bindV, Comp.eval, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hsMem
        rcases hsMem with ⟨spkOrd, _, sIdx, _, secb, _, hEq⟩
        injection hEq with _ hsEq; subst hsEq
        exact ⟨secb, rfl, rfl, rfl, rfl⟩
    rcases hEmptyBase with ⟨secb, hBase, hCnt, hIR, hRR⟩
    have hProjS : projVal shcrStTy (embedVal shcrStTy sL) = sL := projVal_embedVal shcrStTy sL
    have hProjB : projVal keyIndStateTy (embedVal shcrStTy sL).1 = sL.1 :=
      projVal_embedVal keyIndStateTy sL.1
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hProjB, hBase]; exact BaseOnlineLenInv.empty secb
    · rw [hProjB, hBase]; exact Nat.zero_le _
    · rw [hProjB, hBase]; exact RoCacheAvlInv.empty _ _
    · rw [hProjS, hCnt]; exact Nat.zero_le _
    · rw [hProjS, hIR]; exact Nat.zero_le _
    · rw [hProjS, hRR]; exact Nat.zero_le _

private theorem shcr_hChDone (S : Setup) (b : QueryBudget)
    (sK : shcrKindStTy.denote) (bOut : (Ty.bool : Ty pqAtomicSig).denote) :
    shcrKindChDoneC.eval (.cons sK (.cons bOut .nil)) =
      (mapComp tlPrimKeyInd
        (Comp.ret (O := pqxdhOps) (I := _root_.SignalPqxdh.LegacyCosted.pqPrimIface)
          (Γ := [shcrStTy, .bool]) (scTPk (.var .zero)))).eval
        (.cons (forgetShcrKindActive S b sK) (.cons bOut .nil)) := by
  let sL := projVal shcrStTy sK.1
  have hs1 : sK.1 = embedVal shcrStTy sL := (embedVal_projVal shcrStTy sK.1).symm
  let bL : (Ty.bool : Ty pqSig).denote := bOut
  simp only [shcrKindChDoneC]
  rw [runAt2_eval]
  have hEnvL : Env.cons ((Expr.fst Expr.v0 :
      Expr pqAtomicOps [shcrKindStTy, .bool] (embedTy shcrStTy)).eval (.cons sK (.cons bOut .nil)))
      (.cons ((Expr.v1 : Expr pqAtomicOps [shcrKindStTy, .bool] .bool).eval
        (.cons sK (.cons bOut .nil))) .nil) =
      embedEnv (.cons sL (.cons bL .nil)) := by
    simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, hs1]; exact rfl
  have hEnvR : Env.cons (forgetShcrKindActive S b sK) (Env.cons bOut Env.nil) =
      embedEnv (.cons (fixShcrLegacySent S b sL) (.cons bL .nil)) := by
    rw [forgetShcrKindActive_eq_embed]; exact rfl
  rw [hEnvL, mapComp_eval tlPrimKeyInd _ shcrChDoneLeg_unsupported,
    hEnvR, mapComp_eval tlPrimKeyInd _ rfl]
  rfl

private theorem shcr_hFinish (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (sK : shcrKindStTy.denote) (bOut : (Ty.bool : Ty pqAtomicSig).denote)
    (y : (Ty.prod (PB 32) (PB 1568) : Ty pqAtomicSig).denote)
    (hc : ∀ j, c j ≤ keyIndSimBounds b j) (hInv : ShcrSimInv S b c sK) :
    (shcrKeyInd1KeyKindAtomicProg S b).finish.eval (.cons sK (.cons bOut (.cons y .nil))) =
      (shcrKeyInd1KeyActiveAtomicProg S b).finish.eval
        (.cons (forgetShcrKindActive S b sK) (.cons bOut (.cons y .nil))) := by
  let f := keyIndCoreFuels S b
  let yTy : PT := .prod (_root_.SignalPqxdh.LegacyCosted.B 32)
    (_root_.SignalPqxdh.LegacyCosted.B 1568)
  let sL := projVal shcrStTy sK.1
  let bL : (Ty.bool : Ty pqSig).denote := bOut
  let yL := projVal yTy y
  have hs1 : sK.1 = embedVal shcrStTy sL := (embedVal_projVal shcrStTy sK.1).symm
  have hy  : (y : (embedTy yTy).denote) = embedVal yTy yL := (embedVal_projVal yTy y).symm
  let actFin : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [shcrStTy, .bool, yTy] (_root_.SignalPqxdh.LegacyCosted.B 1568) :=
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.shcrExtractC
      (Γ₁ := [yTy]) (Γ₃ := [shcrStTy, .bool, yTy]) (Δ := [shcrStTy, .bool, yTy])
      b.q_total .zero .zero
  change (shcrKindFinishC f.M_on).eval (.cons sK (.cons bOut (.cons y .nil))) =
    (mapComp tlPrimKeyInd actFin).eval
      (.cons (forgetShcrKindActive S b sK) (.cons bOut (.cons y .nil)))
  simp only [shcrKindFinishC]
  rw [runAt3_eval]
  have hEnvL : Env.cons ((Expr.fst Expr.v0 :
        Expr pqAtomicOps [shcrKindStTy, .bool, embedTy yTy] (embedTy shcrStTy)).eval
          (.cons sK (.cons bOut (.cons y .nil))))
      (.cons ((Expr.v1 : Expr pqAtomicOps [shcrKindStTy, .bool, embedTy yTy] .bool).eval
        (.cons sK (.cons bOut (.cons y .nil))))
      (.cons ((Expr.v2 : Expr pqAtomicOps [shcrKindStTy, .bool, embedTy yTy] (embedTy yTy)).eval
        (.cons sK (.cons bOut (.cons y .nil)))) .nil)) =
      embedEnv (.cons sL (.cons bL (.cons yL .nil))) := by
    simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, hs1, hy]; exact rfl
  have hEnvR : (Env.cons (forgetShcrKindActive S b sK) (.cons bOut (.cons y .nil)) :
      Env [embedTy shcrStTy, .bool, embedTy yTy]) =
      embedEnv (.cons (fixShcrLegacySent S b sL) (.cons bL (.cons yL .nil))) := by
    rw [forgetShcrKindActive_eq_embed, hy]; exact rfl
  have hFinUnsup : actFin.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 :=
    shcr1KeyActiveFinish_unsup S b
  rw [hEnvL, mapComp_eval tlPrimKeyInd _ (shcrExtractLeg_unsupported f.M_on),
    hEnvR, mapComp_eval tlPrimKeyInd actFin hFinUnsup]
  have hRR : (sL.2.2.2.2.2.2.1).length ≤ f.M_on := Nat.le_trans hInv.rr_le (hc 0)
  have hLe : f.M_on ≤ b.q_total := Nat.min_le_right _ _
  exact congrArg (_ <$> ·) (shcrExtractLeg_eq_active S b sL bL yL hRR hLe)

private theorem letV_eval_local {ι : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqSig T}
    {Γ : List PT} {σ τ : PT} (e : Expr pqxdhOps Γ σ)
    (k : Var (σ :: Γ) σ → Comp pqxdhOps I (σ :: Γ) τ) (env : Env Γ) :
    (letV e k).eval env = (k .zero).eval (.cons (e.eval env) env) := by
  simp only [letV, Comp.eval, pure_bind]

private theorem bindV_eval_local {ι : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqSig T}
    {Γ : List PT} {σ τ : PT} (c : Comp pqxdhOps I Γ σ)
    (k : Var (σ :: Γ) σ → Comp pqxdhOps I (σ :: Γ) τ) (env : Env Γ) :
    (bindV c k).eval env = c.eval env >>= fun x => (k .zero).eval (.cons x env) := rfl

private theorem shcrResumePreRoC_fixSent_eq (S : Setup) (b : QueryBudget)
    (sL : shcrStTy.denote) (pL : pauseTy.denote)
    (yL : (Ty.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
      (_root_.SignalPqxdh.LegacyCosted.B 1568)).denote) :
    shcrResumePreRoC.eval (.cons sL (.cons pL (.cons yL .nil))) =
      shcrResumePreRoC.eval (.cons (fixShcrLegacySent S b sL) (.cons pL (.cons yL .nil))) := by
  have hUnused : shcrResumePreRoC =
      compRename (Γ := [pauseTy, .prod (_root_.SignalPqxdh.LegacyCosted.B 32)
          (_root_.SignalPqxdh.LegacyCosted.B 1568)])
        (fun {_} v => Var.succ v)
        (let Δ' : List PT :=
          [pauseTy, .prod (_root_.SignalPqxdh.LegacyCosted.B 32)
            (_root_.SignalPqxdh.LegacyCosted.B 1568)]
         let d : Var Δ' pauseTy := .zero
         let sc : Var Δ' (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
           (_root_.SignalPqxdh.LegacyCosted.B 1568)) := .succ .zero
         letV (.fst (.snd (v d))) fun bu =>
         letV (.snd (.snd (v d))) fun uE =>
         bindV _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sBytes32 fun ekSk =>
         bindV (_root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK.initFinishPreRoC bu uE ekSk sc) fun sp =>
         .ret (.pair (.fst (v sp)) (.pair (v ekSk) (.snd (v sp))))) := rfl
  rw [hUnused]
  rw [compRename_eval _ _ (.cons pL (.cons yL .nil))
        (.cons sL (.cons pL (.cons yL .nil))) (fun {_} v => by cases v <;> rfl),
      compRename_eval _ _ (.cons pL (.cons yL .nil))
        (.cons (fixShcrLegacySent S b sL) (.cons pL (.cons yL .nil)))
        (fun {_} v => by cases v <;> rfl)]

private theorem shcrResumePostRoC_fuel_eq (S : Setup) {K₁ K₂ : ℕ} {c : Fin 3 → ℕ}
    (dk : _root_.SignalPqxdh.LegacyCosted.drKeyT.denote)
    (roNew : roListLegacyTy.denote)
    (ep : (Ty.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
      (_root_.SignalPqxdh.LegacyCosted.B 32)).denote)
    (sL : shcrStTy.denote) (pL : pauseTy.denote)
    (yL : (Ty.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
      (_root_.SignalPqxdh.LegacyCosted.B 1568)).denote)
    (hLen : BaseOnlineLenInv c sL.1) (h1 : c 0 ≤ K₁) (h2 : K₁ ≤ K₂) :
    (shcrResumePostRoC S K₁).eval
      (.cons dk (.cons roNew (.cons ep (.cons sL (.cons pL (.cons yL .nil)))))) =
    (shcrResumePostRoC S K₂).eval
      (.cons dk (.cons roNew (.cons ep (.cons sL (.cons pL (.cons yL .nil)))))) := by
  dsimp only [shcrResumePostRoC]
  rw [letV_eval_local, letV_eval_local, letV_eval_local,
      letV_eval_local, letV_eval_local, letV_eval_local, bindV_eval_local]
  congr 1
  refine initFinishPostRoC_fuel_eq (c := c) S _ _ _ _ _ _ _ _ _ _ ?_ h1 h2
  simpa only [v, scBase, Expr.eval, Env.get, Ext.wk] using hLen

private theorem shcrFinE_chosen_fields {Γ : List PT}
    (s : Expr pqxdhOps Γ shcrStTy)
    (sid : Expr pqxdhOps Γ _root_.SignalPqxdh.LegacyCosted.sidT)
    (bu : Expr pqxdhOps Γ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (sc : Expr pqxdhOps Γ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
      (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    (r : Expr pqxdhOps Γ (.prod _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndRespTy
      keyIndStateTy))
    (ch : Expr pqxdhOps (SCS :: Γ) (_root_.SignalPqxdh.LegacyCosted.B 1568))
    (env : Env Γ) {res : SCS.denote}
    (h : res = (Expr.pair (.fst (v (Var.zero : Var (SCS :: Γ) SCS)))
      (scUpd (.snd (v (Var.zero : Var (SCS :: Γ) SCS))) (chosen := ch))).eval
      (.cons ((shcrFinE s sid bu sc r).eval env) env)) :
    res.2.1 = (r.eval env).2 ∧
    res.2.2.2.2.2.1 = (s.eval env).2.2.2.2.1 + 1 ∧
    res.2.2.2.2.2.2.1.length = (s.eval env).2.2.2.2.2.1.length + 1 ∧
    res.2.2.2.2.2.2.2.1 = (s.eval env).2.2.2.2.2.2.1 := by
  subst h
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem shcr1KeyKindResumeC_eval (S : Setup) (b : QueryBudget)
    (sK : shcrKindStTy.denote) (pK : (embedTy pauseTy).denote)
    (y : (embedTy (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
      (_root_.SignalPqxdh.LegacyCosted.B 1568))).denote) :
    (shcr1KeyKindResumeC S b).eval (.cons sK (.cons pK (.cons y .nil))) =
      ((runAt3 (.fst .v0) .v1 .v2 (mapComp tlPrimKeyInd shcrResumePreRoC)).eval
          (.cons sK (.cons pK (.cons y .nil))) >>= fun preAt =>
        (roShadowQueryC tlPrimKeyInd (keyIndCoreFuels S b).roCap
          (shcrRoListAtomicE (.fst .v1)) (.snd .v1) (.fst .v0)).eval
          (.cons preAt (.cons sK (.cons pK (.cons y .nil)))) >>= fun out =>
        (runAt6 (.fst .v0) (.fst (.snd .v0)) (.snd .v1) (.fst .v2) .v3 .v4
          (mapComp tlPrimKeyInd (shcrResumePostRoC S (keyIndCoreFuels S b).M_on))).eval
          (.cons out (.cons preAt (.cons sK (.cons pK (.cons y .nil))))) >>= fun resAt =>
        (pure (resAt.1, (resAt.2, out.2.2)) :
          OracleComp _ (((pqKeyIndCodec S).R.prod shcrKindStTy).denote))) := rfl

private theorem shcr_hResume (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (pK : (embedTy pauseTy).denote) (sK : shcrKindStTy.denote)
    (y : (embedTy (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
      (_root_.SignalPqxdh.LegacyCosted.B 1568))).denote)
    (hc : ∀ j, c j ≤ keyIndSimBounds b j) (hP : ShcrPauseInv S b c pK sK) :
    Prod.map id (forgetShcrKindActive S b) <$>
      (shcr1KeyKindResumeC S b).eval (.cons sK (.cons pK (.cons y .nil))) =
      (mapComp tlPrimKeyInd
        (shcrResumeC S (keyIndLoopBound b)
          (Γ₁ := [.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
            (_root_.SignalPqxdh.LegacyCosted.B 1568)])
          (Γ₂ := [pauseTy, .prod (_root_.SignalPqxdh.LegacyCosted.B 32)
            (_root_.SignalPqxdh.LegacyCosted.B 1568)])
          (Γ₃ := [shcrStTy, pauseTy, .prod (_root_.SignalPqxdh.LegacyCosted.B 32)
            (_root_.SignalPqxdh.LegacyCosted.B 1568)])
          (Δ := [shcrStTy, pauseTy, .prod (_root_.SignalPqxdh.LegacyCosted.B 32)
            (_root_.SignalPqxdh.LegacyCosted.B 1568)])
          .zero .zero .zero)).eval
        (.cons (forgetShcrKindActive S b sK) (.cons pK (.cons y .nil))) ∧
    ∀ (vs' : (Ty.prod ((pqKeyIndCodec S).R) shcrKindStTy).denote),
      vs' ∈ support ((shcr1KeyKindResumeC S b).eval (.cons sK (.cons pK (.cons y .nil)))) →
      ShcrSimInv S b c vs'.2 := by
  let f := keyIndCoreFuels S b
  let K := keyIndLoopBound b
  let scTy : PT := .prod (_root_.SignalPqxdh.LegacyCosted.B 32)
    (_root_.SignalPqxdh.LegacyCosted.B 1568)
  let preTy : PT := .prod (_root_.SignalPqxdh.LegacyCosted.B 192)
    (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32))
  let sL := projVal shcrStTy sK.1
  let pL := projVal pauseTy pK
  let yL := projVal scTy y
  have hs1 : sK.1 = embedVal shcrStTy sL := (embedVal_projVal shcrStTy sK.1).symm
  have hp  : pK = embedVal pauseTy pL := (embedVal_projVal pauseTy pK).symm
  have hy  : y = embedVal scTy yL := (embedVal_projVal scTy y).symm
  have ⟨hLtK, hRoomCap⟩ := ro_bounds_of_le S b hc hP.online_len.counts_eq
    (Nat.le_of_succ_le hP.ro_room)
  have hLeK : f.M_on ≤ K := by dsimp only [f, K, keyIndCoreFuels, keyIndLoopBound]; omega
  have hActUnsup := shcr1KeyActiveResume_unsup S b
  let env0 : Env [shcrKindStTy, embedTy pauseTy, embedTy scTy] := .cons sK (.cons pK (.cons y .nil))
  have hPreStep : (runAt3 (.fst .v0) .v1 .v2 (mapComp tlPrimKeyInd shcrResumePreRoC)).eval env0 =
      embedVal preTy <$> shcrResumePreRoC.eval (.cons sL (.cons pL (.cons yL .nil))) := by
    rw [runAt3_eval]
    have hE : Env.cons ((Expr.fst Expr.v0 : Expr pqAtomicOps _ (embedTy shcrStTy)).eval env0)
        (.cons ((Expr.v1 : Expr pqAtomicOps _ (embedTy pauseTy)).eval env0)
          (.cons ((Expr.v2 : Expr pqAtomicOps _ (embedTy scTy)).eval env0) .nil)) =
        embedEnv (.cons sL (.cons pL (.cons yL .nil))) := by
      simp only [env0, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, hs1, hp, hy]
    rw [hE, mapComp_eval tlPrimKeyInd _ shcrResumePreRoC_unsup]
  have hRoSim : ∀ pre : preTy.denote,
      let env1 := Env.cons (embedVal preTy pre) env0
      Prod.map id Prod.fst <$>
          (roShadowQueryC tlPrimKeyInd f.roCap (shcrRoListAtomicE (.fst .v1)) (.snd .v1)
            (.fst .v0)).eval env1 =
        (hkdfOrRoC K true
          (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
          (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
          .zero (.var (.succ .zero))).eval (.cons sL.1 (.cons pre.1 .nil)) ∧
      ∀ out ∈ support ((roShadowQueryC tlPrimKeyInd f.roCap (shcrRoListAtomicE (.fst .v1))
          (.snd .v1) (.fst .v0)).eval env1),
        RoCacheAvlInv K f.roCap out.2.1 out.2.2 ∧
        out.2.1.length ≤ (embedVal roListLegacyTy (stRoList sL.1)).length + 1 := by
    intro pre env1
    have hRoListEq : (shcrRoListAtomicE (.fst .v1)).eval env1 =
        embedVal roListLegacyTy (stRoList sL.1) := by
      rw [shcrRoListAtomicE_eval]
      simp only [env1, env0, Expr.eval, Expr.v1, Env.get, hs1, projVal_embedVal]
    have hTblEq : (Expr.snd Expr.v1 : Expr pqAtomicOps _ roAvlTy).eval env1 = sK.2 := rfl
    have hSecEq : (Expr.fst Expr.v0 : Expr pqAtomicOps _ (PB 192)).eval env1 = pre.1 := rfl
    have hSim := roShadowQueryC_eval_sim tlPrimKeyInd env1 K f.roCap
      (shcrRoListAtomicE (.fst .v1)) (.snd .v1) (.fst .v0) sL.1 (hkdfOrRoC_unsup K)
      hRoListEq (by rw [hRoListEq, hTblEq]; exact hP.ro_avl)
      (by rw [hRoListEq, embedVal_roList_eq]; exact hLtK)
      (by rw [hRoListEq, embedVal_roList_eq]; exact hRoomCap)
    have hRhsEq : (mapComp tlPrimKeyInd (hkdfOrRoC K true
        (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        .zero (.var (.succ .zero)))).eval
        (.cons (embedVal keyIndStateTy sL.1) (.cons pre.1 .nil)) =
      (hkdfOrRoC K true
        (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        .zero (.var (.succ .zero))).eval (.cons sL.1 (.cons pre.1 .nil)) := by
      have hMC := mapComp_eval tlPrimKeyInd _ (hkdfOrRoC_unsup K) (.cons sL.1 (.cons pre.1 .nil))
      change (mapComp tlPrimKeyInd _).eval (embedEnv (.cons sL.1 (.cons pre.1 .nil))) = _
      rw [hMC]
      have hId : embedVal (.prod _root_.SignalPqxdh.LegacyCosted.drKeyT roListLegacyTy) = id := by
        funext ⟨⟨_, _, _⟩, l⟩; exact Prod.ext rfl (embedVal_roList_eq l)
      rw [hId, id_map]
    rw [hSecEq, hRhsEq] at hSim
    exact ⟨hSim.1, fun out hout => by rw [← hRoListEq]; exact hSim.2 out hout⟩
  have hPostStep : ∀ (pre : preTy.denote)
      (out : (drKeyT (ℓ := 0) (Pt := Empty)).denote × roListAtomicTy.denote × roAvlTy.denote),
      (runAt6 (.fst .v0) (.fst (.snd .v0)) (.snd .v1) (.fst .v2) .v3 .v4
        (mapComp tlPrimKeyInd (shcrResumePostRoC S f.M_on))).eval
        (.cons out (.cons (embedVal preTy pre) env0)) =
      embedVal SCS <$> (shcrResumePostRoC S f.M_on).eval
        (.cons out.1 (.cons out.2.1 (.cons pre.2 (.cons sL (.cons pL (.cons yL .nil)))))) := by
    intro pre out
    let env2 : Env [.prod (drKeyT (ℓ := 0) (Pt := Empty)) (.prod roListAtomicTy roAvlTy),
        embedTy preTy, shcrKindStTy, embedTy pauseTy, embedTy scTy] :=
      .cons out (.cons (embedVal preTy pre) env0)
    change (runAt6 (.fst .v0) (.fst (.snd .v0)) (.snd .v1) (.fst .v2) .v3 .v4
      (mapComp tlPrimKeyInd (shcrResumePostRoC S f.M_on))).eval env2 = _
    rw [runAt6_eval]
    have hDk : out.1 = embedVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1 := by
      rcases out.1 with ⟨_, _, _⟩; rfl
    have hRo : out.2.1 = embedVal roListLegacyTy out.2.1 := (embedVal_roList_eq out.2.1).symm
    let envLeg : Env [_root_.SignalPqxdh.LegacyCosted.drKeyT, roListLegacyTy,
        .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32),
        shcrStTy, pauseTy, scTy] :=
      .cons out.1 (.cons out.2.1 (.cons pre.2 (.cons sL (.cons pL (.cons yL .nil)))))
    have hE : Env.cons ((Expr.fst Expr.v0 : Expr pqAtomicOps _ _).eval env2)
        (.cons ((Expr.fst (Expr.snd Expr.v0) : Expr pqAtomicOps _ _).eval env2)
        (.cons ((Expr.snd Expr.v1 : Expr pqAtomicOps _ _).eval env2)
        (.cons ((Expr.fst Expr.v2 : Expr pqAtomicOps _ _).eval env2)
        (.cons ((Expr.v3 : Expr pqAtomicOps _ _).eval env2)
        (.cons ((Expr.v4 : Expr pqAtomicOps _ _).eval env2) .nil))))) =
        embedEnv envLeg := by
      simp only [env2, env0, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
        Env.get, hs1, hp, hy]
      rw [hDk, hRo]; rfl
    rw [hE, mapComp_eval tlPrimKeyInd _ (shcrResumePostRoC_unsup S f.M_on)]
  have hPostFuel : ∀ (dk : _root_.SignalPqxdh.LegacyCosted.drKeyT.denote)
      (roNew : roListLegacyTy.denote) (ep : (Ty.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
        (_root_.SignalPqxdh.LegacyCosted.B 32)).denote),
      (shcrResumePostRoC S f.M_on).eval
        (.cons dk (.cons roNew (.cons ep (.cons sL (.cons pL (.cons yL .nil)))))) =
      (shcrResumePostRoC S K).eval
        (.cons dk (.cons roNew (.cons ep (.cons sL (.cons pL (.cons yL .nil)))))) :=
    fun dk roNew ep => shcrResumePostRoC_fuel_eq S dk roNew ep sL pL yL hP.online_len (hc 0) hLeK
  refine ⟨?_, ?_⟩
  · have hRhs : (mapComp tlPrimKeyInd
        (shcrResumeC S K
          (Γ₁ := [scTy]) (Γ₂ := [pauseTy, scTy]) (Γ₃ := [shcrStTy, pauseTy, scTy])
          (Δ := [shcrStTy, pauseTy, scTy]) .zero .zero .zero)).eval
        (.cons (forgetShcrKindActive S b sK) (.cons pK (.cons y .nil))) =
      embedVal SCS <$> (shcrResumeC S K
          (Γ₁ := [scTy]) (Γ₂ := [pauseTy, scTy]) (Γ₃ := [shcrStTy, pauseTy, scTy])
          (Δ := [shcrStTy, pauseTy, scTy]) .zero .zero .zero).eval
        (.cons (fixShcrLegacySent S b sL) (.cons pL (.cons yL .nil))) := by
      have hEnvR : (Env.cons (forgetShcrKindActive S b sK) (.cons pK (.cons y .nil)) :
          Env [embedTy shcrStTy, embedTy pauseTy, embedTy scTy]) =
          embedEnv (.cons (fixShcrLegacySent S b sL) (.cons pL (.cons yL .nil))) := by
        rw [forgetShcrKindActive_eq_embed, hp, hy]
      have hResUnsup : (shcrResumeC S K
          (Γ₁ := [scTy]) (Γ₂ := [pauseTy, scTy]) (Γ₃ := [shcrStTy, pauseTy, scTy])
          (Δ := [shcrStTy, pauseTy, scTy]) .zero .zero .zero).queries
          tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := hActUnsup
      rw [hEnvR, mapComp_eval tlPrimKeyInd _ hResUnsup]
    rw [hRhs, shcrResumeC_eq_split, shcr1KeyKindResumeC_eval S b sK pK y,
      hPreStep, shcrResumePreRoC_fixSent_eq S b sL pL yL]
    conv_lhs =>
      rw [map_bind, map_eq_bind_pure_comp, bind_assoc]
      simp only [Function.comp_def, pure_bind]
    conv_rhs => rw [map_bind]
    refine congrArg (_ >>= ·) (funext fun pre => ?_)
    rw [map_bind, map_bind]
    have hLhsCont :
        (fun out : (drKeyT (ℓ := 0) (Pt := Empty)).denote ×
            roListAtomicTy.denote × roAvlTy.denote =>
          Prod.map id (forgetShcrKindActive S b) <$>
            ((runAt6 (.fst .v0) (.fst (.snd .v0)) (.snd .v1) (.fst .v2) .v3 .v4
              (mapComp tlPrimKeyInd (shcrResumePostRoC S f.M_on))).eval
              (.cons out (.cons (embedVal preTy pre) env0)) >>= fun resAt =>
              pure (resAt.1, (resAt.2, out.2.2)))) =
        (fun out =>
          embedVal SCS <$> (shcrResumePostRoC S K).eval
            (.cons out.1 (.cons out.2.1
              (.cons pre.2 (.cons (fixShcrLegacySent S b sL) (.cons pL (.cons yL .nil))))))) := by
      funext out
      have hPureMap :
          ((embedVal SCS <$> (shcrResumePostRoC S K).eval
              (.cons out.1 (.cons out.2.1
                (.cons pre.2 (.cons sL (.cons pL (.cons yL .nil))))))) >>=
            fun resAt => pure (resAt.1, (resAt.2, out.2.2))) =
          (fun resAt : (embedTy SCS).denote => (resAt.1, (resAt.2, out.2.2))) <$>
            (embedVal SCS <$> (shcrResumePostRoC S K).eval
              (.cons out.1 (.cons out.2.1
                (.cons pre.2 (.cons sL (.cons pL (.cons yL .nil))))))) :=
        (map_eq_bind_pure_comp _ _ _).symm
      rw [hPostStep pre out, hPostFuel, hPureMap, Functor.map_map, Functor.map_map,
        ← shcrResumePostRoC_fixSent_comm, Functor.map_map]
      refine congrArg (· <$> _) (funext fun ⟨rOut, sOut⟩ => ?_)
      simp only [Prod.map, id_eq, forgetShcrKindActive_eq_embed]
      exact Prod.ext rfl (congrArg (embedVal shcrStTy ∘ fixShcrLegacySent S b)
        (projVal_embedVal shcrStTy sOut))
    rw [hLhsCont]
    have hRoEq := (hRoSim pre).1
    have hFstSent : (fixShcrLegacySent S b sL).1 = sL.1 := rfl
    rw [hFstSent, ← hRoEq]
    rw [map_eq_bind_pure_comp, bind_assoc]
    simp only [Function.comp_def, pure_bind]
    rfl
  · intro vs' hMem
    rw [shcr1KeyKindResumeC_eval S b sK pK y,
      hPreStep, map_eq_bind_pure_comp, mem_support_bind_iff] at hMem
    rcases hMem with ⟨preAt, hPreAt, hMem⟩
    rw [mem_support_bind_iff] at hPreAt
    rcases hPreAt with ⟨pre, _, hPreEq⟩
    simp only [Function.comp_def, support_pure, Set.mem_singleton_iff] at hPreEq
    subst hPreEq
    rw [mem_support_bind_iff] at hMem
    rcases hMem with ⟨out, hout, hMem⟩
    obtain ⟨hAvl', hRoLen'⟩ := (hRoSim pre).2 out hout
    rw [hPostStep pre out, map_eq_bind_pure_comp, mem_support_bind_iff] at hMem
    rcases hMem with ⟨resAt, hResAt, hVsEq⟩
    rw [mem_support_bind_iff] at hResAt
    rcases hResAt with ⟨res, hResMem, hResAtEq⟩
    simp only [Function.comp_def, support_pure, Set.mem_singleton_iff] at hResAtEq
    subst hResAtEq
    simp only [support_pure, Set.mem_singleton_iff] at hVsEq
    subst hVsEq
    dsimp only [shcrResumePostRoC] at hResMem
    iterate 6 rw [letV_eval_local] at hResMem
    rw [bindV_eval_local, mem_support_bind_iff] at hResMem
    rcases hResMem with ⟨r, hrMem, hResEq⟩
    rw [letV_eval_local] at hResEq
    simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hResEq
    obtain ⟨hPrin, hSpks, hOpks, hSess, hResps, hUsedO, hUsedN, hKyb, hRoSt, hAdv⟩ :=
      initFinishPostRoC_mem_support S f.M_on _ _ _ _ _ _ _ _ _ _ hrMem
    dsimp only [v, scBase, Expr.eval, Env.get, Ext.wk] at hPrin hSpks hOpks hSess hResps hUsedO hUsedN hKyb hRoSt hAdv
    obtain ⟨hResBase, hResCnt, hResIR, hResRR⟩ := shcrFinE_chosen_fields _ _ _ _ _ _ _ hResEq
    simp only [v, Expr.eval, Env.get, Ext.wk] at hResBase hResCnt hResIR hResRR
    have hProjS' : projVal shcrStTy (embedVal shcrStTy res.2) = res.2 :=
      projVal_embedVal shcrStTy res.2
    have hProjB' : projVal keyIndStateTy (embedVal shcrStTy res.2).1 = r.2 := by
      change projVal keyIndStateTy (embedVal keyIndStateTy res.2.1) = r.2
      rw [projVal_embedVal, hResBase]
    change ShcrSimInv S b c (embedVal shcrStTy res.2, out.2.2)
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hProjB']
      exact ⟨by rw [hPrin]; exact hP.online_len.prin_le,
             by rw [hSpks]; exact hP.online_len.spks_le,
             by rw [hOpks]; exact hP.online_len.opks_le,
             by rw [hSess]; exact hP.sess_room,
             by rw [hResps]; exact hP.online_len.resps_le,
             by rw [hUsedO]; exact hP.online_len.usedO_le,
             by rw [hUsedN]; exact hP.online_len.usedN_le,
             by rw [hKyb]; exact hP.online_len.kyb_le,
             by rw [hAdv]; exact hP.online_len.adv_le,
             hP.online_len.counts_eq⟩
    · rw [hProjB', hRoSt]
      have hRoRoom : (embedVal roListLegacyTy (stRoList sL.1)).length + 1 ≤ c 2 := by
        rw [embedVal_roList_eq]; exact hP.ro_room
      exact Nat.le_trans hRoLen' hRoRoom
    · rw [hProjB', hRoSt, embedVal_roList_eq]
      exact hAvl'
    · rw [hProjS', hResCnt]; exact hP.cnt_room
    · rw [hProjS', hResIR]; exact hP.ir_room
    · rw [hProjS', hResRR]; exact hP.rr_le

private theorem shcr_hPost (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (sK : shcrKindStTy.denote) (t : KeyIndQuery S)
    (hc : ∀ j, c j ≤ keyIndSimBounds b j)
    (hroom : ∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j)
    (hInv : ShcrSimInv S b c sK) :
    Prod.map id (forgetShcrKindActive S b) <$>
      (shcr1KeyKindHandlePostC S b).eval (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      (liftKeyIndHandle tlPrimKeyInd S
        (shcr1KeyActivePostC S (keyIndLoopBound b)
          (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
          (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero)).eval
        (.cons (forgetShcrKindActive S b sK) (.cons ((pqKeyIndCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support ((shcr1KeyKindHandlePostC S b).eval
        (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) p.2 := by
  have hBound : ∀ j, bumpPred (keyIndSimPred S) c t j ≤ keyIndSimBounds b j := by
    intro j; simp only [bumpPred_apply]; split_ifs with h
    · exact hroom j h
    · exact hc j
  have hPostUnsup : (shcr1KeyActivePostC S (keyIndLoopBound b)
      (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).queries
      tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := shcr1KeyActiveHandlePost_unsup S b
  rw [forgetShcrKindActive_eq_embed, liftKeyIndHandle_eval tlPrimKeyInd S _ hPostUnsup]
  change Prod.map id (forgetShcrKindActive S b) <$> _ = activePostEval S b sK t ∧ _
  dsimp only [shcr1KeyKindHandlePostC, shcrKindHandlePostC, ite_true]
  rw [dispatchKeyIndQ_eval]
  cases t with
  | initPrin u => exact shcrInitPrinArm_sim S b c sK u hInv hBound
  | corruptIK u => exact shcrCorruptArm_sim S b c sK u hInv hBound
  | genSPK u j => exact shcrGenSpkArm_sim S b c sK u j hInv hBound
  | genOPK u j o => exact shcrGenOpkArm_sim S b c sK u j o hInv hBound
  | initiateOPK u i bu => exact shcrInitOpkArmPost_sim S b c sK u i bu hInv hBound
  | initiateNoOPK u i bu => exact shcrInitNoOpkArmPost_sim S b c sK u i bu hInv hBound
  | acceptOPK k j o hdr => exact shcrAccOpkArmPost_sim S b c sK k j o hdr hInv hBound
  | acceptNoOPK k j l hdr => exact shcrAccNoOpkArmPost_sim S b c sK k j l hdr hInv hBound
  | testSession sid => exact shcrTestArm_sim S b c sK sid hInv hBound
  | roQuery sec => exact shcrRoArmK_sim S b c sK sec hInv hBound
  | revealDhSecrets => exact shcrRevDhArm_sim S b c sK hInv hBound
  | revealSessionKey sid => exact shcrRevSessArm_sim S b c sK sid hInv hBound
  | registerKey sk => exact shcrRegKeyArm_sim S b c sK sk hInv hBound
  | revealSpkSk u j => exact shcrRevSpkArm_sim S b c sK u j hInv hBound

private theorem twoVarRen_eval {P R : PT} {Δ₁ Δ₂ : List PT}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface [P, shcrStTy] R)
    (x₁ : Var Δ₁ P) (s₁ : Var Δ₁ shcrStTy) (env₁ : Env Δ₁)
    (x₂ : Var Δ₂ P) (s₂ : Var Δ₂ shcrStTy) (env₂ : Env Δ₂)
    (hx : env₁.get x₁ = env₂.get x₂) (hs : env₁.get s₁ = env₂.get s₂) :
    (compRename (twoVarRen x₁ s₁) c).eval env₁ = (compRename (twoVarRen x₂ s₂) c).eval env₂ := by
  rw [compRename_eval c _ (.cons (env₁.get x₁) (.cons (env₁.get s₁) .nil)) env₁
        (fun {_} v => by cases v with
          | zero => rfl | succ v => cases v with | zero => rfl | succ v => nomatch v),
      compRename_eval c _ (.cons (env₂.get x₂) (.cons (env₂.get s₂) .nil)) env₂
        (fun {_} v => by cases v with
          | zero => rfl | succ v => cases v with | zero => rfl | succ v => nomatch v),
      hx, hs]

private theorem arm2_wk_eval {P : PT}
    (arm0 : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface [P, shcrStTy] SCS)
    {Δ₁ Δ₂ : List PT} [Ext [shcrStTy, keyIndQueryTy] (P :: Δ₁)]
    [Ext [shcrStTy, keyIndQueryTy] (P :: Δ₂)]
    {c₁ : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (P :: Δ₁) SCS}
    {c₂ : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (P :: Δ₂) SCS}
    (env₁ : Env (P :: Δ₁)) (env₂ : Env (P :: Δ₂))
    (hc₁ : c₁ = compRename (twoVarRen .zero
      (Ext.wk (Var.zero : Var [shcrStTy, keyIndQueryTy] shcrStTy))) arm0)
    (hc₂ : c₂ = compRename (twoVarRen .zero
      (Ext.wk (Var.zero : Var [shcrStTy, keyIndQueryTy] shcrStTy))) arm0)
    (hx : env₁.get .zero = env₂.get .zero)
    (hs : env₁.get (Ext.wk (Var.zero : Var [shcrStTy, keyIndQueryTy] shcrStTy)) =
          env₂.get (Ext.wk (Var.zero : Var [shcrStTy, keyIndQueryTy] shcrStTy))) :
    c₁.eval env₁ = c₂.eval env₂ := by
  rw [hc₁, hc₂]
  exact twoVarRen_eval arm0 _ _ env₁ _ _ env₂ hx hs

private theorem caseSumV_inl_eval {A B R : PT} {Δ : List PT}
    {e : Expr pqxdhOps Δ (.sum A B)} {a : A.denote}
    (l : Var (A :: Δ) A → Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (A :: Δ) R)
    (r : Var (B :: Δ) B → Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (B :: Δ) R)
    (env : Env Δ) (he : e.eval env = .inl a) :
    (caseSumV e l r).eval env = (l .zero).eval (.cons a env) := by
  simp only [caseSumV, Comp.eval, he]

private theorem caseSumV_inr_eval {A B R : PT} {Δ : List PT}
    {e : Expr pqxdhOps Δ (.sum A B)} {b : B.denote}
    (l : Var (A :: Δ) A → Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (A :: Δ) R)
    (r : Var (B :: Δ) B → Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (B :: Δ) R)
    (env : Env Δ) (he : e.eval env = .inr b) :
    (caseSumV e l r).eval env = (r .zero).eval (.cons b env) := by
  simp only [caseSumV, Comp.eval, he]

private theorem shcrAcceptB_wk_eval (S : Setup) (K : ℕ) (opk : Bool)
    {Δ₁ Δ₂ : List PT} [Ext [shcrStTy, keyIndQueryTy] (accQTy :: Δ₁)]
    [Ext [shcrStTy, keyIndQueryTy] (accQTy :: Δ₂)]
    (env₁ : Env (accQTy :: Δ₁)) (env₂ : Env (accQTy :: Δ₂))
    (hx : env₁.get .zero = env₂.get .zero)
    (hs : env₁.get (Ext.wk (Var.zero : Var [shcrStTy, keyIndQueryTy] shcrStTy)) =
          env₂.get (Ext.wk (Var.zero : Var [shcrStTy, keyIndQueryTy] shcrStTy))) :
    (shcrAcceptB S K opk
      (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := accQTy :: Δ₁) .zero .zero).eval env₁ =
    (shcrAcceptB S K opk
      (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := accQTy :: Δ₂) .zero .zero).eval env₂ := by
  cases opk with
  | false =>
      exact arm2_wk_eval (shcrAcceptB S K false
        (Γ₁ := [shcrStTy]) (Γ₂ := [accQTy, shcrStTy]) .zero .zero) env₁ env₂ rfl rfl hx hs
  | true =>
      exact arm2_wk_eval (shcrAcceptB S K true
        (Γ₁ := [shcrStTy]) (Γ₂ := [accQTy, shcrStTy]) .zero .zero) env₁ env₂ rfl rfl hx hs

private theorem shcr1KeyActivePostC_wk_eval (S : Setup) (K : ℕ)
    (sL : shcrStTy.denote) (t : KeyIndQuery S)
    (h1 : ∀ u i bu, t ≠ .initiateOPK u i bu)
    (h2 : ∀ u i bu, t ≠ .initiateNoOPK u i bu) :
    (shcr1KeyActivePostC S K
      (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := .opt pauseTy :: [shcrStTy, keyIndQueryTy]) .zero .zero).eval
      (.cons none (.cons sL
        (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil))) =
    (shcr1KeyActivePostC S K
      (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).eval
      (.cons sL (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil)) := by
  cases t with
  | initiateOPK u i bu => exact False.elim (h1 u i bu rfl)
  | initiateNoOPK u i bu => exact False.elim (h2 u i bu rfl)
  | initPrin u =>
      dsimp only [shcr1KeyActivePostC, shcrActivePostTailC, caseSumV,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        Comp.eval, v, Expr.eval, Env.get]
      exact arm2_wk_eval (onBase (Γ₁ := [shcrStTy]) .zero fun g =>
        initPrin1KeyB K g (Var.zero : Var [.nat, shcrStTy] .nat)) _ _ rfl rfl rfl rfl
  | corruptIK u =>
      dsimp only [shcr1KeyActivePostC, shcrActivePostTailC, caseSumV,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        Comp.eval, v, Expr.eval, Env.get]
      exact arm2_wk_eval (onBase (Γ₁ := [shcrStTy]) .zero fun g =>
        corruptB K g (Var.zero : Var [.nat, shcrStTy] .nat)) _ _ rfl rfl rfl rfl
  | genSPK u j =>
      dsimp only [shcr1KeyActivePostC, shcrActivePostTailC, caseSumV,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        Comp.eval, v, Expr.eval, Env.get]
      exact arm2_wk_eval (shcrActiveGenSpkB S K
        (Γ₁ := [shcrStTy]) (Γ₂ := [.prod .nat .nat, shcrStTy]) .zero .zero) _ _ rfl rfl rfl rfl
  | genOPK u j o =>
      dsimp only [shcr1KeyActivePostC, shcrActivePostTailC, caseSumV,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        Comp.eval, v, Expr.eval, Env.get]
      exact arm2_wk_eval (onBase (Γ₁ := [shcrStTy]) .zero fun g =>
        genOpkB K g (Var.zero : Var [.prod .nat (.prod .nat .nat), shcrStTy] _)) _ _ rfl rfl rfl rfl
  | acceptOPK k j o hdr =>
      conv_lhs =>
        dsimp only [shcr1KeyActivePostC]
        rw [caseSumV_inr_eval _ _ _ rfl]
        dsimp only [shcrActivePostTailC]
        rw [caseSumV_inr_eval _ _ _ rfl, caseSumV_inr_eval _ _ _ rfl,
            caseSumV_inr_eval _ _ _ rfl, caseSumV_inr_eval _ _ _ rfl,
            caseSumV_inr_eval _ _ _ rfl, caseSumV_inl_eval _ _ _ rfl]
      conv_rhs =>
        dsimp only [shcr1KeyActivePostC]
        rw [caseSumV_inr_eval _ _ _ rfl]
        dsimp only [shcrActivePostTailC]
        rw [caseSumV_inr_eval _ _ _ rfl, caseSumV_inr_eval _ _ _ rfl,
            caseSumV_inr_eval _ _ _ rfl, caseSumV_inr_eval _ _ _ rfl,
            caseSumV_inr_eval _ _ _ rfl, caseSumV_inl_eval _ _ _ rfl]
      exact shcrAcceptB_wk_eval S K true _ _ rfl rfl
  | acceptNoOPK k j l hdr =>
      conv_lhs =>
        dsimp only [shcr1KeyActivePostC]
        rw [caseSumV_inr_eval _ _ _ rfl]
        dsimp only [shcrActivePostTailC]
        rw [caseSumV_inr_eval _ _ _ rfl, caseSumV_inr_eval _ _ _ rfl,
            caseSumV_inr_eval _ _ _ rfl, caseSumV_inr_eval _ _ _ rfl,
            caseSumV_inr_eval _ _ _ rfl, caseSumV_inr_eval _ _ _ rfl,
            caseSumV_inl_eval _ _ _ rfl]
      conv_rhs =>
        dsimp only [shcr1KeyActivePostC]
        rw [caseSumV_inr_eval _ _ _ rfl]
        dsimp only [shcrActivePostTailC]
        rw [caseSumV_inr_eval _ _ _ rfl, caseSumV_inr_eval _ _ _ rfl,
            caseSumV_inr_eval _ _ _ rfl, caseSumV_inr_eval _ _ _ rfl,
            caseSumV_inr_eval _ _ _ rfl, caseSumV_inr_eval _ _ _ rfl,
            caseSumV_inl_eval _ _ _ rfl]
      exact shcrAcceptB_wk_eval S K false _ _ rfl rfl
  | testSession sid =>
      dsimp only [shcr1KeyActivePostC, shcrActivePostTailC, caseSumV,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        Comp.eval, v, Expr.eval, Env.get]
      exact arm2_wk_eval (onBase (Γ₁ := [shcrStTy]) .zero fun g =>
        testB K g (Var.zero : Var [_root_.SignalPqxdh.LegacyCosted.sidT, shcrStTy] _))
        _ _ rfl rfl rfl rfl
  | roQuery sec =>
      dsimp only [shcr1KeyActivePostC, shcrActivePostTailC, caseSumV,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        Comp.eval, v, Expr.eval, Env.get]
      exact arm2_wk_eval (onBase (Γ₁ := [shcrStTy]) .zero fun g =>
        roB true K g (Var.zero : Var [_root_.SignalPqxdh.LegacyCosted.B 192, shcrStTy] _))
        _ _ rfl rfl rfl rfl
  | revealDhSecrets =>
      dsimp only [shcr1KeyActivePostC, shcrActivePostTailC, caseSumV,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        Comp.eval, v, Expr.eval, Env.get]
      exact arm2_wk_eval (onBase (Γ₁ := [shcrStTy]) (Δ := [.unit, shcrStTy]) .zero fun g =>
        revealDhB true K g) _ _ rfl rfl rfl rfl
  | revealSessionKey sid =>
      dsimp only [shcr1KeyActivePostC, shcrActivePostTailC, caseSumV,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        Comp.eval, v, Expr.eval, Env.get]
      exact arm2_wk_eval (onBase (Γ₁ := [shcrStTy]) .zero fun g =>
        revealB K g (Var.zero : Var [_root_.SignalPqxdh.LegacyCosted.sidT, shcrStTy] _))
        _ _ rfl rfl rfl rfl
  | registerKey sk =>
      dsimp only [shcr1KeyActivePostC, shcrActivePostTailC, caseSumV,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        Comp.eval, v, Expr.eval, Env.get]
      exact arm2_wk_eval (onBase (Γ₁ := [shcrStTy]) .zero fun g =>
        registerB g (Var.zero : Var [_root_.SignalPqxdh.LegacyCosted.B 32, shcrStTy] _))
        _ _ rfl rfl rfl rfl
  | revealSpkSk u j =>
      dsimp only [shcr1KeyActivePostC, shcrActivePostTailC, caseSumV,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        Comp.eval, v, Expr.eval, Env.get]
      exact arm2_wk_eval (onBase (Γ₁ := [shcrStTy]) .zero fun g =>
        revealSpkB K g (Var.zero : Var [.prod .nat .nat, shcrStTy] _)) _ _ rfl rfl rfl rfl

private theorem wrapInl_pre_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    {A : Ty pqAtomicSig}
    (arm : Comp pqAtomicOps pqPrimIface [A, shcrKindStTy, (pqKeyIndCodec S).Q]
      (.prod ((pqKeyIndCodec S).R) shcrKindStTy))
    (a : A.denote) (sK : shcrKindStTy.denote) (t : KeyIndQuery S)
    (h1 : ∀ u i bu, t ≠ .initiateOPK u i bu)
    (h2 : ∀ u i bu, t ≠ .initiateNoOPK u i bu)
    (hSim : Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons a (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
      ∀ vs' ∈ support (arm.eval (.cons a (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
        ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2) :
    forgetPreOut id (forgetShcrKindActive S b) <$>
        (Comp.bind arm (.ret (.inl .v0)) :
          Comp pqAtomicOps pqPrimIface [A, shcrKindStTy, (pqKeyIndCodec S).Q]
            (.sum (.prod ((pqKeyIndCodec S).R) shcrKindStTy)
              (.prod (PB 1568) (.prod (embedTy pauseTy) shcrKindStTy)))).eval
          (.cons a (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePreEval S b sK t ∧
    (∀ vOut sK₁, .inl (vOut, sK₁) ∈ support
        ((Comp.bind arm (.ret (.inl .v0)) :
          Comp pqAtomicOps pqPrimIface [A, shcrKindStTy, (pqKeyIndCodec S).Q]
            (.sum (.prod ((pqKeyIndCodec S).R) shcrKindStTy)
              (.prod (PB 1568) (.prod (embedTy pauseTy) shcrKindStTy)))).eval
          (.cons a (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))) →
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) sK₁) ∧
    (∀ cOut pK sK₁, .inr (cOut, pK, sK₁) ∈ support
        ((Comp.bind arm (.ret (.inl .v0)) :
          Comp pqAtomicOps pqPrimIface [A, shcrKindStTy, (pqKeyIndCodec S).Q]
            (.sum (.prod ((pqKeyIndCodec S).R) shcrKindStTy)
              (.prod (PB 1568) (.prod (embedTy pauseTy) shcrKindStTy)))).eval
          (.cons a (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))) →
      ShcrPauseInv S b (bumpPred (keyIndSimPred S) c t) pK sK₁) := by
  have hNoPause : (pauseCheckC S (keyIndLoopBound b)
      (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).eval
      (.cons (fixShcrLegacySent S b (projVal shcrStTy sK.1))
        (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil)) = pure none := by
    cases t with
    | initiateOPK u i bu => exact False.elim (h1 u i bu rfl)
    | initiateNoOPK u i bu => exact False.elim (h2 u i bu rfl)
    | _ =>
        simp only [pauseCheckC, caseSumV,
          _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
          Comp.eval, v, Expr.eval, Env.get, Ext.wk]
  refine ⟨?_, ?_, ?_⟩
  · have hL : forgetPreOut id (forgetShcrKindActive S b) <$>
        (Comp.bind arm (.ret (.inl .v0)) :
          Comp pqAtomicOps pqPrimIface [A, shcrKindStTy, (pqKeyIndCodec S).Q]
            (.sum (.prod ((pqKeyIndCodec S).R) shcrKindStTy)
              (.prod (PB 1568) (.prod (embedTy pauseTy) shcrKindStTy)))).eval
          (.cons a (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
        Sum.inl <$> activePostEval S b sK t := by
      change forgetPreOut id (forgetShcrKindActive S b) <$>
        (arm.eval (.cons a (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) >>=
          (pure ∘ Sum.inl)) = _
      rw [← map_eq_bind_pure_comp, Functor.map_map]
      change (fun x => Sum.inl (Prod.map id (forgetShcrKindActive S b) x)) <$>
        arm.eval (.cons a (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) = _
      rw [← Functor.map_map, hSim.1]
    rw [hL]
    dsimp only [activePreEval, shcr1KeyActivePreC]
    rw [bindV_eval_local, hNoPause, pure_bind]
    dsimp only [caseOptV, Comp.eval, v, Expr.eval, Env.get]
    rw [bindV_eval_local, shcr1KeyActivePostC_wk_eval S (keyIndLoopBound b) _ t h1 h2]
    change Sum.inl <$> (embedVal SCS <$> _) =
      embedVal (.sum SCS (.prod (_root_.SignalPqxdh.LegacyCosted.B 1568) (.prod pauseTy shcrStTy))) <$>
        (_ >>= (pure ∘ Sum.inl))
    rw [← map_eq_bind_pure_comp, Functor.map_map, Functor.map_map]
    rfl
  · intro vOut sK₁ hMem
    simp only [Comp.eval, Expr.eval, Expr.v0, Env.get, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff, Sum.inl.injEq] at hMem
    rcases hMem with ⟨vs', hvs', rfl⟩
    exact hSim.2 (vOut, sK₁) hvs'
  · intro cOut pK sK₁ hMem
    simp only [Comp.eval, Expr.eval, Expr.v0, Env.get, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff, reduceCtorEq] at hMem
    rcases hMem with ⟨_, _, ⟨⟩⟩

private theorem shcr_hPre (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (sK : shcrKindStTy.denote) (t : KeyIndQuery S)
    (hc : ∀ j, c j ≤ keyIndSimBounds b j)
    (hroom : ∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j)
    (hInv : ShcrSimInv S b c sK) :
    forgetPreOut id (forgetShcrKindActive S b) <$>
      (shcr1KeyKindHandlePreC S b).eval (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      (liftKeyIndHandle tlPrimKeyInd S
        (shcr1KeyActivePreC S (keyIndLoopBound b)
          (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
          (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero)).eval
        (.cons (forgetShcrKindActive S b sK) (.cons ((pqKeyIndCodec S).qenc t) .nil)) ∧
    (∀ vOut sK₁, .inl (vOut, sK₁) ∈ support ((shcr1KeyKindHandlePreC S b).eval
        (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) →
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) sK₁) ∧
    (∀ cOut pK sK₁, .inr (cOut, pK, sK₁) ∈ support ((shcr1KeyKindHandlePreC S b).eval
        (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) →
      ShcrPauseInv S b (bumpPred (keyIndSimPred S) c t) pK sK₁) := by
  have hBound : ∀ j, bumpPred (keyIndSimPred S) c t j ≤ keyIndSimBounds b j := by
    intro j; simp only [bumpPred_apply]; split_ifs with h
    · exact hroom j h
    · exact hc j
  have hPreUnsup : (shcr1KeyActivePreC S (keyIndLoopBound b)
      (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).queries
      tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := shcr1KeyActiveHandlePre_unsup S b
  rw [forgetShcrKindActive_eq_embed, liftKeyIndHandle_eval tlPrimKeyInd S _ hPreUnsup]
  change forgetPreOut id (forgetShcrKindActive S b) <$> _ = activePreEval S b sK t ∧ _
  dsimp only [shcr1KeyKindHandlePreC, shcrKindHandlePreC, ite_true]
  rw [dispatchKeyIndQ_eval]
  cases t with
  | initPrin u =>
      apply wrapInl_pre_sim S b c
      · intro _ _ _ h; cases h
      · intro _ _ _ h; cases h
      · exact shcrInitPrinArm_sim S b c sK u hInv hBound
  | corruptIK u =>
      apply wrapInl_pre_sim S b c
      · intro _ _ _ h; cases h
      · intro _ _ _ h; cases h
      · exact shcrCorruptArm_sim S b c sK u hInv hBound
  | genSPK u j =>
      apply wrapInl_pre_sim S b c
      · intro _ _ _ h; cases h
      · intro _ _ _ h; cases h
      · exact shcrGenSpkArm_sim S b c sK u j hInv hBound
  | genOPK u j o =>
      apply wrapInl_pre_sim S b c
      · intro _ _ _ h; cases h
      · intro _ _ _ h; cases h
      · exact shcrGenOpkArm_sim S b c sK u j o hInv hBound
  | initiateOPK u i bu =>
      have h := shcrInitOpkArmPre_sim S b c sK u i bu hInv hBound
      exact ⟨h.1, fun vOut sK₁ hm => h.2.1 (vOut, sK₁) hm,
        fun cOut pK sK₁ hm => h.2.2 (cOut, pK, sK₁) hm⟩
  | initiateNoOPK u i bu =>
      have h := shcrInitNoOpkArmPre_sim S b c sK u i bu hInv hBound
      exact ⟨h.1, fun vOut sK₁ hm => h.2.1 (vOut, sK₁) hm,
        fun cOut pK sK₁ hm => h.2.2 (cOut, pK, sK₁) hm⟩
  | acceptOPK k j o hdr =>
      apply wrapInl_pre_sim S b c
      · intro _ _ _ h; cases h
      · intro _ _ _ h; cases h
      · exact shcrAccOpkArmPost_sim S b c sK k j o hdr hInv hBound
  | acceptNoOPK k j l hdr =>
      apply wrapInl_pre_sim S b c
      · intro _ _ _ h; cases h
      · intro _ _ _ h; cases h
      · exact shcrAccNoOpkArmPost_sim S b c sK k j l hdr hInv hBound
  | testSession sid =>
      apply wrapInl_pre_sim S b c
      · intro _ _ _ h; cases h
      · intro _ _ _ h; cases h
      · exact shcrTestArm_sim S b c sK sid hInv hBound
  | roQuery sec =>
      apply wrapInl_pre_sim S b c
      · intro _ _ _ h; cases h
      · intro _ _ _ h; cases h
      · exact shcrRoArmK_sim S b c sK sec hInv hBound
  | revealDhSecrets =>
      apply wrapInl_pre_sim S b c
      · intro _ _ _ h; cases h
      · intro _ _ _ h; cases h
      · exact shcrRevDhArm_sim S b c sK hInv hBound
  | revealSessionKey sid =>
      apply wrapInl_pre_sim S b c
      · intro _ _ _ h; cases h
      · intro _ _ _ h; cases h
      · exact shcrRevSessArm_sim S b c sK sid hInv hBound
  | registerKey sk =>
      apply wrapInl_pre_sim S b c
      · intro _ _ _ h; cases h
      · intro _ _ _ h; cases h
      · exact shcrRegKeyArm_sim S b c sK sk hInv hBound
  | revealSpkSk u j =>
      apply wrapInl_pre_sim S b c
      · intro _ _ _ h; cases h
      · intro _ _ _ h; cases h
      · exact shcrRevSpkArm_sim S b c sK u j hInv hBound

/-- Two-stage forgetful step simulation from `shcrKeyInd1KeyKindAtomicProg S b` to
`shcrKeyInd1KeyActiveAtomicProg S b`. -/
theorem shcrKeyInd1KeyKindAtomicProg_twoStageForgetSim
    (S : Setup) (b : QueryBudget)
    (x : (Ty.prod (PB 1568) (PB 3168) : Ty pqAtomicSig).denote) :
    TwoStageForgetSim
      (shcrKeyInd1KeyKindAtomicProg S b)
      (shcrKeyInd1KeyActiveAtomicProg S b)
      id
      (forgetShcrKindActive S b)
      (keyIndSimPred S)
      (keyIndSimBounds b)
      x
      (ShcrSimInv S b)
      (ShcrPauseInv S b) where
  hInit   := shcr_hInit S b x
  hPre    := shcr_hPre S b
  hChDone := fun _ sK bOut _ _ => shcr_hChDone S b sK bOut
  hResume := shcr_hResume S b
  hPost   := shcr_hPost S b
  hFinish := shcr_hFinish S b

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSim
