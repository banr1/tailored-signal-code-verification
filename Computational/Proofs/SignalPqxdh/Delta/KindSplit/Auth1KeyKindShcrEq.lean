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
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyShCrEval -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimShcr

public section

set_option autoImplicit false

/-!
# Two-Stage Forgetful-Simulation Bridges for One-Key Auth `shcr`

**Checked by Lean.**

Bridges `TwoStageForgetSim` on the shadow-indexed one-key Auth `shcr` reduction to `kemShCrExp`
experiment equality, `KemShCr` advantage equality, and the shallow-to-DSL advantage transfer
`Auth1KeyDslFamily.shcr_le`.
-/

open OracleComp OracleSpec
open SignalPqxdh (Setup QueryBudget BoundedAdv AuthAdversary Primitives
  AuthQuery authSpec isGameQuery KemShCrAdv kemShCrExp KemShCr
  sampleKemKeyGen sampleCoins32 primBaseImpl kyberCtLen kyberPkLen)
open SignalPqxdh.Costed (PB pqAtomicSig pqAtomicOps authCodec pqAuthPrimIface)
open SignalPqxdh.LegacyCosted (B)
open SignalPqxdh.Security (primQueryBudget Auth1KeyCostedReductionFamily shcrReductionAuth1Key)
open ReductionDsl (Ty TwoStageCostedReduction Mid)
open Computational.Proofs.ReductionDsl.StepSim (isGamePred instDecidablePredIsGamePred
  isQueryBoundP_min)
open Computational.Proofs.ReductionDsl.StepSimTwoStage (TwoStageForgetSim
  twoStage_simulateQ_eval_bind_eq_of_forgetSim)
open Computational.Proofs.SignalPqxdh.AtomicLift (tlAuthPrim liftAuth2Stage
  liftAuth2Stage_eval1 liftAuth2Stage_eval2 embedMid embedVal kemShCr_eq_of_state_map)
open SignalPqxdh.Security.ReductionDsl.AuthHs (shcrAuth1KeyDslProg shcrAuth1KeyDslAdv
  shcrAuth1KeyDslAdv_kemShCr_eq)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (shcrAuth1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds instDecidablePredAuthSimPred shcrOldAtomicProg)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs
  (pqxdhAuth1KeyKindCostedSims)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimShcr
  (shcrAuth1KeyKindProg_twoStageForgetSim)

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindShcrEq

theorem shcrOldAtomicProg_def_eq (S : Setup) (b : QueryBudget) :
    shcrOldAtomicProg S b = liftAuth2Stage tlAuthPrim S (shcrAuth1KeyDslProg S b) :=
  rfl

/-- Reference `KemShCrAdv` induced by `shcrOldAtomicProg S b`. -/
@[expose] def shcrOldAtomicAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : KemShCrAdv where
  State := Mid (authSpec S) Bool (shcrOldAtomicProg S b).π.denote
    (shcrOldAtomicProg S b).σ.denote (PB 1568).denote
  choosePk pk sk :=
    (shcrOldAtomicProg S b).eval1 (fun _ => A.1.run) (pk, sk) b.q_total false
  findCollision st ss ct :=
    (shcrOldAtomicProg S b).eval2 st (ss, ct) b.q_total false
  q_prim := primQueryBudget S b

private theorem shcrOldAtomicAdv_kemShCr_eq (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    KemShCr Prim (shcrOldAtomicAdv S b A) =
      KemShCr Prim (shcrReductionAuth1Key S b A) := by
  refine Eq.trans (kemShCr_eq_of_state_map Prim (shcrAuth1KeyDslAdv S b A.1)
    (shcrOldAtomicAdv S b A)
    (embedMid (ch := B 1568))
    (fun pk sk => ?_) (fun st ss ct => ?_))
    (shcrAuth1KeyDslAdv_kemShCr_eq Prim S b A)
  · exact liftAuth2Stage_eval1 tlAuthPrim S (fun _ => rfl) (shcrAuth1KeyDslProg S b)
      (fun _ => A.1.run) (pk, sk) b.q_total false
  · have hId : embedVal (B 1568) = id := rfl
    have h2 : (shcrOldAtomicProg S b).eval2 (embedMid (ch := B 1568) st)
        (embedVal (.prod (B 32) (B 1568)) (ss, ct)) b.q_total false =
        embedVal (B 1568) <$> (shcrAuth1KeyDslProg S b).eval2 st (ss, ct) b.q_total false :=
      liftAuth2Stage_eval2 tlAuthPrim S (fun _ => rfl) (shcrAuth1KeyDslProg S b)
        st (ss, ct) b.q_total false
    rw [hId, id_map] at h2
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

/-- Discharges the `IsQueryBoundP` hypothesis of `twoStage_simulateQ_eval_bind_eq_of_forgetSim`
from `BoundedAdv` across the four `AuthCoreKSimBase` budget slots. -/
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

/-- Proves `kemShCrExp` equality against `shcrOldAtomicAdv` from a `TwoStageForgetSim` bundle on
`R_new.shcr b`. -/
theorem kemShCrExp_auth_eq_of_twoStageForgetSim
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forgetπ : (R_new.shcr b).π.denote → (shcrOldAtomicProg S b).π.denote}
    {forgetσ : (R_new.shcr b).σ.denote → (shcrOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.shcr b).σ.denote → Prop}
    {InvPause : (Fin m → Nat) → (R_new.shcr b).π.denote → (R_new.shcr b).σ.denote → Prop}
    (hSim : ∀ pksk : ((.prod (PB 1568) (PB 3168)) : Ty pqAtomicSig).denote,
      TwoStageForgetSim (R_new.shcr b) (shcrOldAtomicProg S b)
        forgetπ forgetσ P B pksk Inv InvPause)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    kemShCrExp Prim (R_new.eval.shcr b A) =
      kemShCrExp Prim (shcrOldAtomicAdv S b A) := by
  unfold kemShCrExp
  dsimp only [Auth1KeyCostedReductionFamily.eval, shcrOldAtomicAdv]
  refine congrArg (sampleKemKeyGen Prim >>= ·) (funext fun ⟨pk, sk⟩ => ?_)
  exact twoStage_simulateQ_eval_bind_eq_of_forgetSim (primBaseImpl Prim) (hSim (pk, sk))
    (fun _ => A.1.run) hA b.q_total b.q_total false
    (fun pk' eval2Sim => do
      let r ← sampleCoins32
      let some (ss, ct) := Prim.kemEncaps pk' r | return false
      let ct' ← eval2Sim (ss, ct)
      return (decide (Prim.kemDecaps sk ct' = some ss) && decide (ct' ≠ ct ∨ pk' ≠ pk) &&
              decide (ct'.length = kyberCtLen ∧ pk'.length = kyberPkLen)))

theorem kemShCr_auth_eq_of_twoStageForgetSim
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forgetπ : (R_new.shcr b).π.denote → (shcrOldAtomicProg S b).π.denote}
    {forgetσ : (R_new.shcr b).σ.denote → (shcrOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.shcr b).σ.denote → Prop}
    {InvPause : (Fin m → Nat) → (R_new.shcr b).π.denote → (R_new.shcr b).σ.denote → Prop}
    (hSim : ∀ pksk : ((.prod (PB 1568) (PB 3168)) : Ty pqAtomicSig).denote,
      TwoStageForgetSim (R_new.shcr b) (shcrOldAtomicProg S b)
        forgetπ forgetσ P B pksk Inv InvPause)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    KemShCr Prim (R_new.eval.shcr b A) = KemShCr Prim (shcrOldAtomicAdv S b A) := by
  unfold KemShCr
  rw [kemShCrExp_auth_eq_of_twoStageForgetSim Prim S b R_new hSim A hA]

theorem shcr_le_of_twoStageForgetSim
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forgetπ : (R_new.shcr b).π.denote → (shcrOldAtomicProg S b).π.denote}
    {forgetσ : (R_new.shcr b).σ.denote → (shcrOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.shcr b).σ.denote → Prop}
    {InvPause : (Fin m → Nat) → (R_new.shcr b).π.denote → (R_new.shcr b).σ.denote → Prop}
    (hSim : ∀ pksk : ((.prod (PB 1568) (PB 3168)) : Ty pqAtomicSig).denote,
      TwoStageForgetSim (R_new.shcr b) (shcrOldAtomicProg S b)
        forgetπ forgetσ P B pksk Inv InvPause)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    KemShCr Prim (shcrReductionAuth1Key S b A) ≤ KemShCr Prim (R_new.eval.shcr b A) := by
  rw [kemShCr_auth_eq_of_twoStageForgetSim Prim S b R_new hSim A hA,
    shcrOldAtomicAdv_kemShCr_eq Prim S b A]

theorem pqxdhAuth1KeyKind_shcr_eq (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).shcr b = shcrAuth1KeyKindProg S b := rfl

theorem kemShCrExp_pqxdhAuth1KeyKind_eq
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    kemShCrExp Prim ((pqxdhAuth1KeyKindCostedSims S).eval.shcr b A) =
      kemShCrExp Prim (shcrOldAtomicAdv S b A) :=
  kemShCrExp_auth_eq_of_twoStageForgetSim Prim S b (pqxdhAuth1KeyKindCostedSims S)
    (shcrAuth1KeyKindProg_twoStageForgetSim S b) A
    (boundedAdv_isQueryBoundP_auth S b A)

theorem kemShCr_pqxdhAuth1KeyKind_eq
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    KemShCr Prim ((pqxdhAuth1KeyKindCostedSims S).eval.shcr b A) =
      KemShCr Prim (shcrOldAtomicAdv S b A) := by
  unfold KemShCr
  rw [kemShCrExp_pqxdhAuth1KeyKind_eq Prim S b A]

theorem pqxdhAuth1KeyKind_shcr_le
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    KemShCr Prim (shcrReductionAuth1Key S b A) ≤
      KemShCr Prim ((pqxdhAuth1KeyKindCostedSims S).eval.shcr b A) := by
  rw [kemShCr_pqxdhAuth1KeyKind_eq Prim S b A, shcrOldAtomicAdv_kemShCr_eq Prim S b A]

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindShcrEq
