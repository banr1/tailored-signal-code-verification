/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Auth.Headline
public import Computational.Proofs.ReductionDsl.StepSimTwoStage -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyAeadCpa -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimCpa

public section

set_option autoImplicit false

/-!
# Two-Stage Forgetful-Simulation Bridges for the Kind-Split One-Key `Auth` `cpa` Reduction

**Checked by Lean.** Bridges `TwoStageForgetSim` on the kind-split one-key `Auth` `cpa` reduction
to `aeadIndCpaExp` experiment equality, `AeadIndCpa` advantage equality, and the shallow-to-DSL
advantage bound `pqxdhAuth1KeyKind_cpa_le`.
-/

open OracleComp OracleSpec
open SignalPqxdh (Setup QueryBudget BoundedAdv AuthAdversary Primitives
  AuthQuery authSpec isGameQuery PrimBaseSpec AeadIndCpaAdv aeadIndCpaExp AeadIndCpa
  sampleMessageKeys80 primBaseImpl)
open SignalPqxdh.Costed (PB pqAtomicSig pqAtomicOps authCodec pqAuthPrimIface)
open SignalPqxdh.LegacyCosted (B)
open SignalPqxdh.Security (primQueryBudget Auth1KeyCostedReductionFamily
  aeadCpaReductionAuthFixed1Key)
open ReductionDsl (Ty TwoStageCostedReduction Mid)
open Computational.Proofs.ReductionDsl.StepSim (isGamePred instDecidablePredIsGamePred
  isQueryBoundP_min)
open Computational.Proofs.ReductionDsl.StepSimTwoStage (TwoStageForgetSim
  twoStage_simulateQ_eval_bind_eq_of_forgetSim)
open Computational.Proofs.SignalPqxdh.AtomicLift (tlAuthPrim liftAuth2Stage
  liftAuth2Stage_eval1 liftAuth2Stage_eval2 embedTy embedMid embedVal aeadIndCpa_eq_of_state_map)
open SignalPqxdh.Security.ReductionDsl.AuthAead (cpaChOutTy aeadCpaRedProg1Key aeadCpaDsl1KeyAdv
  aeadCpaDsl1KeyAdv_aeadIndCpa_eq)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (aeadCpa1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds instDecidablePredAuthSimPred aeadCpaOldAtomicProg)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs
  (pqxdhAuth1KeyKindCostedSims)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimCpa
  (aeadCpa1KeyKindProg_twoStageForgetSim)

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindCpaEq

theorem aeadCpaOldAtomicProg_def_eq (S : Setup) (b : QueryBudget) :
    aeadCpaOldAtomicProg S b = liftAuth2Stage tlAuthPrim S (aeadCpaRedProg1Key S b.q_total) :=
  rfl

/-- Reference `AeadIndCpaAdv` induced by `aeadCpaOldAtomicProg S b`. -/
@[expose] def aeadCpaOldAtomicAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : AeadIndCpaAdv where
  State := Mid (authSpec S) Bool (aeadCpaOldAtomicProg S b).π.denote
    (aeadCpaOldAtomicProg S b).σ.denote
    (Ty.prod (PB 158) (Ty.prod (PB 32) (PB 32))).denote
  choose := do
    let r ← (aeadCpaOldAtomicProg S b).eval1 (fun _ => A.1.run) () b.q_total false
    pure (r.1.1, r.1.2.1, r.1.2.2, r.2)
  dist st c? :=
    (aeadCpaOldAtomicProg S b).eval2 st c? b.q_total false
  q_prim := primQueryBudget S b

private theorem cpa1Key_choose_map_eq {S : Setup} {b : QueryBudget}
    (m1 : OracleComp PrimBaseSpec ((embedTy cpaChOutTy).denote ×
      Mid (authSpec S) Bool (embedTy (aeadCpaRedProg1Key S b.q_total).π).denote
        (embedTy (aeadCpaRedProg1Key S b.q_total).σ).denote (embedTy cpaChOutTy).denote))
    (m2 : OracleComp PrimBaseSpec (cpaChOutTy.denote ×
      Mid (authSpec S) Bool (aeadCpaRedProg1Key S b.q_total).π.denote
        (aeadCpaRedProg1Key S b.q_total).σ.denote cpaChOutTy.denote))
    (h : m1 = Prod.map (embedVal cpaChOutTy) (embedMid (ch := cpaChOutTy)) <$> m2) :
    (do let r ← m1; pure (r.1.1, r.1.2.1, r.1.2.2, r.2)) =
      (fun (ad, m0, m1, st) => (ad, m0, m1, embedMid (ch := cpaChOutTy) st)) <$>
        (do let r ← m2; pure (r.1.1, r.1.2.1, r.1.2.2, r.2)) := by
  subst h
  rw [bind_map_left, map_bind]
  refine bind_congr fun ⟨⟨ad, m0, m1⟩, st⟩ => ?_
  simp [embedVal]

private theorem aeadCpaOldAtomicAdv_aeadIndCpa_eq (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    AeadIndCpa Prim (aeadCpaOldAtomicAdv S b A) =
      AeadIndCpa Prim (aeadCpaReductionAuthFixed1Key S b A) := by
  refine Eq.trans (aeadIndCpa_eq_of_state_map Prim (aeadCpaDsl1KeyAdv S b A.1)
    (aeadCpaOldAtomicAdv S b A) (embedMid (ch := cpaChOutTy))
    ?_ (fun st c? => ?_))
    (aeadCpaDsl1KeyAdv_aeadIndCpa_eq Prim S b A)
  · exact cpa1Key_choose_map_eq _ _ (liftAuth2Stage_eval1 tlAuthPrim S (fun _ => rfl)
      (aeadCpaRedProg1Key S b.q_total) (fun _ => A.1.run) () b.q_total false)
  · have hc : embedVal (.opt (B 32)) c? = c? := by cases c? <;> rfl
    have hId : embedVal .bool = id := rfl
    have h2 : (aeadCpaOldAtomicProg S b).eval2 (embedMid (ch := cpaChOutTy) st)
        (embedVal (.opt (B 32)) c?) b.q_total false =
        embedVal .bool <$> (aeadCpaRedProg1Key S b.q_total).eval2 st c? b.q_total false :=
      liftAuth2Stage_eval2 tlAuthPrim S (fun _ => rfl) (aeadCpaRedProg1Key S b.q_total)
        st c? b.q_total false
    rw [hc, hId, id_map] at h2
    exact h2

private theorem isQueryBoundP_of_imp {ι₀ : Type} {spec : OracleSpec ι₀} {α : Type}
    {oa : OracleComp spec α} {p p₀ : ι₀ → Prop}
    [DecidablePred p] [DecidablePred p₀]
    (himp : ∀ q, p q → p₀ q) {m : Nat}
    (h₀ : oa.IsQueryBoundP p₀ m) :
    oa.IsQueryBoundP p m := by
  induction oa using OracleComp.inductionOn generalizing m with
  | pure x => exact isQueryBoundP_pure p x m
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h₀ ⊢
    refine ⟨?_, fun u => ?_⟩
    · by_cases hp : p t
      · exact Or.inr (h₀.1.resolve_left (not_not.mpr (himp t hp)))
      · exact Or.inl hp
    · refine (ih u (h₀.2 u)).mono ?_
      by_cases hp : p t
      · have hp₀ : p₀ t := himp t hp
        simp only [hp, hp₀, ite_true]
        exact Nat.le_refl _
      · simp only [hp, ite_false]
        split <;> omega

/-- Transfers `BoundedAdv` query bounds on `A` to the 4-slot `authSimPred` budget family. -/
theorem boundedAdv_isQueryBoundP_auth (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    ∀ (_ : Unit) (j : Fin 4),
      A.1.run.IsQueryBoundP
        (isGamePred (G := authSpec S) (authSimPred S j))
        (authSimBounds b j) := by
  intro _ j
  obtain ⟨hRo, _, _, hRoRoot, hTot, hOn⟩ := A.2
  have hTotSub : ∀ (p : AuthQuery S → Prop) [DecidablePred p],
      A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) p) b.q_total := by
    intro p _
    refine isQueryBoundP_of_imp (fun q hq => ?_) hTot
    cases q with
    | inl _ => exact False.elim hq
    | inr _ => rfl
  match j with
  | ⟨0, _⟩ =>
    refine isQueryBoundP_min ?_ (hTotSub (authSimPred S ⟨0, by omega⟩))
    refine isQueryBoundP_of_imp (fun q hq => ?_) hOn
    cases q with
    | inl _ => exact False.elim hq
    | inr t => exact hq
  | ⟨1, _⟩ =>
    refine isQueryBoundP_min ?_ (hTotSub (authSimPred S ⟨1, by omega⟩))
    refine isQueryBoundP_of_imp (fun q hq => ?_) hRo
    cases q with
    | inl _ => exact False.elim hq
    | inr t => exact hq
  | ⟨2, _⟩ =>
    refine isQueryBoundP_min ?_ (hTotSub (authSimPred S ⟨2, by omega⟩))
    refine isQueryBoundP_of_imp (fun q hq => ?_) hRoRoot
    cases q with
    | inl _ => exact False.elim hq
    | inr t => exact hq
  | ⟨3, _⟩ =>
    exact hTotSub (authSimPred S ⟨3, by omega⟩)

/-- `aeadIndCpaExp` equality from a `TwoStageForgetSim` against `aeadCpaOldAtomicProg S b`. -/
theorem aeadIndCpaExp_auth_eq_of_twoStageForgetSim
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forgetπ : (R_new.cpa b).π.denote → (aeadCpaOldAtomicProg S b).π.denote}
    {forgetσ : (R_new.cpa b).σ.denote → (aeadCpaOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.cpa b).σ.denote → Prop}
    {InvPause : (Fin m → Nat) → (R_new.cpa b).π.denote → (R_new.cpa b).σ.denote → Prop}
    (hSim : TwoStageForgetSim (R_new.cpa b) (aeadCpaOldAtomicProg S b)
      forgetπ forgetσ P B () Inv InvPause)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    aeadIndCpaExp Prim (R_new.eval.cpa b A) =
      aeadIndCpaExp Prim (aeadCpaOldAtomicAdv S b A) := by
  unfold aeadIndCpaExp
  dsimp only [Auth1KeyCostedReductionFamily.eval, aeadCpaOldAtomicAdv]
  refine congrArg (($ᵗ Bool) >>= ·) (funext fun bit => ?_)
  refine congrArg (sampleMessageKeys80 >>= ·) (funext fun mk => ?_)
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  exact twoStage_simulateQ_eval_bind_eq_of_forgetSim (primBaseImpl Prim) hSim
    (fun _ => A.1.run) hA b.q_total b.q_total false
    (fun chOut eval2Sim =>
      if chOut.2.1.length != chOut.2.2.length then do
        let coin ← $ᵗ Bool
        return coin
      else do
        let ct := Prim.aeadEnc mk chOut.1 (if bit then chOut.2.2 else chOut.2.1)
        let b' ← eval2Sim (some ct)
        return (b' == bit))

theorem aeadIndCpa_auth_eq_of_twoStageForgetSim
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forgetπ : (R_new.cpa b).π.denote → (aeadCpaOldAtomicProg S b).π.denote}
    {forgetσ : (R_new.cpa b).σ.denote → (aeadCpaOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.cpa b).σ.denote → Prop}
    {InvPause : (Fin m → Nat) → (R_new.cpa b).π.denote → (R_new.cpa b).σ.denote → Prop}
    (hSim : TwoStageForgetSim (R_new.cpa b) (aeadCpaOldAtomicProg S b)
      forgetπ forgetσ P B () Inv InvPause)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    AeadIndCpa Prim (R_new.eval.cpa b A) = AeadIndCpa Prim (aeadCpaOldAtomicAdv S b A) := by
  unfold AeadIndCpa
  rw [aeadIndCpaExp_auth_eq_of_twoStageForgetSim Prim S b R_new hSim A hA]

theorem cpa_le_of_twoStageForgetSim
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forgetπ : (R_new.cpa b).π.denote → (aeadCpaOldAtomicProg S b).π.denote}
    {forgetσ : (R_new.cpa b).σ.denote → (aeadCpaOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.cpa b).σ.denote → Prop}
    {InvPause : (Fin m → Nat) → (R_new.cpa b).π.denote → (R_new.cpa b).σ.denote → Prop}
    (hSim : TwoStageForgetSim (R_new.cpa b) (aeadCpaOldAtomicProg S b)
      forgetπ forgetσ P B () Inv InvPause)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    AeadIndCpa Prim (aeadCpaReductionAuthFixed1Key S b A) ≤
      AeadIndCpa Prim (R_new.eval.cpa b A) := by
  rw [aeadIndCpa_auth_eq_of_twoStageForgetSim Prim S b R_new hSim A hA,
    aeadCpaOldAtomicAdv_aeadIndCpa_eq Prim S b A]

theorem pqxdhAuth1KeyKind_cpa_eq (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).cpa b = aeadCpa1KeyKindProg S b := rfl

theorem aeadIndCpaExp_pqxdhAuth1KeyKind_eq
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    aeadIndCpaExp Prim ((pqxdhAuth1KeyKindCostedSims S).eval.cpa b A) =
      aeadIndCpaExp Prim (aeadCpaOldAtomicAdv S b A) :=
  aeadIndCpaExp_auth_eq_of_twoStageForgetSim Prim S b (pqxdhAuth1KeyKindCostedSims S)
    (aeadCpa1KeyKindProg_twoStageForgetSim S b ()) A
    (boundedAdv_isQueryBoundP_auth S b A)

theorem aeadIndCpa_pqxdhAuth1KeyKind_eq
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    AeadIndCpa Prim ((pqxdhAuth1KeyKindCostedSims S).eval.cpa b A) =
      AeadIndCpa Prim (aeadCpaOldAtomicAdv S b A) := by
  unfold AeadIndCpa
  rw [aeadIndCpaExp_pqxdhAuth1KeyKind_eq Prim S b A]

/-- Shallow-to-DSL `AeadIndCpa` advantage bound for `(pqxdhAuth1KeyKindCostedSims S).eval.cpa`. -/
theorem pqxdhAuth1KeyKind_cpa_le
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    AeadIndCpa Prim (aeadCpaReductionAuthFixed1Key S b A) ≤
      AeadIndCpa Prim ((pqxdhAuth1KeyKindCostedSims S).eval.cpa b A) := by
  rw [aeadIndCpa_pqxdhAuth1KeyKind_eq Prim S b A, aeadCpaOldAtomicAdv_aeadIndCpa_eq Prim S b A]

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindCpaEq
