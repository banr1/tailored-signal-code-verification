/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Auth.Headline
public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigWire -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhWire -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimA

public section

set_option autoImplicit false

/-!
# Forgetful-Simulation Bridges for One-Key Auth `sig` and `gdh` Kind-Split Reductions

**Checked by Lean.**

Transfers `ForgetSim` simulation instances for the shadow-indexed one-key Auth `sig`
(`a1s2KindProg`) and `gdh` (`a1g2KindProg`) reductions to `CostedReduction.eval` equality,
semantic query bounds, and `GapSigEufCma` / `GapDhWithSign` advantage bounds on
`pqxdhAuth1KeyKindCostedSims`.
-/

open OracleComp OracleSpec
open SignalPqxdh (Setup QueryBudget BoundedAdv AuthAdversary QueryBounded Primitives Bytes
  AuthQuery authSpec isAuthOnlineQuery isAuthRoQuery isAuthRoRootQuery isGameQuery
  GapSigEufCma GapDhWithSign GapSigEufCmaAdv GapDhWithSignAdv)
open SignalPqxdh.Costed (PB pqAtomicSig pqAtomicOps authCodec pqAuthSigAndDdhIface)
open SignalPqxdh.LegacyCosted (B)
open SignalPqxdh.Security (authGdhQueryBudget gdhPrimQueryBudget Auth1KeyCostedReductionFamily)
open ReductionDsl (Ty CostedReduction)
open Computational.Proofs.ReductionDsl.StepSim (ForgetSim isGamePred instDecidablePredIsGamePred
  isQueryBoundP_min)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds instDecidablePredAuthSimPred)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK
  (a1g2KindProg a1s2KindProg)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs
  (pqxdhAuth1KeyKindCostedSims)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase
  (gdhOldAtomicProg sigOldAtomicProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimA
  (a1g2KindProg_forgetSim a1s2KindProg_forgetSim)
open Computational.Proofs.SignalPqxdh.AtomicLift (tlAuthSigDdh liftAuth1Stage
  liftAuth1Stage_eval embedVal)
open SignalPqxdh.Security.ReductionDsl.AuthHs (sigAuth1KeyDslProg sigAuth1KeyDslAdv
  sigAuth1Key_sig_le sigAuth1KeyDslAdv_bounded fgAuth1KeyGapDhProg fgAuth1KeyGapDhDslAdv
  fgAuth1KeyGapDhDslAdv_bounded fgAuth1KeyGapDhProg_gapDhWithSign_eq)
open Proofs.SignalPqxdh.Security (sigReductionAuth1Key fgAuth1KeyGapDhAdv4)

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindSiggdhEq

theorem sigOldAtomicProg_def_eq (S : Setup) (b : QueryBudget) :
    sigOldAtomicProg S b = liftAuth1Stage tlAuthSigDdh S (sigAuth1KeyDslProg S b) :=
  rfl

theorem gdhOldAtomicProg_def_eq (S : Setup) (b : QueryBudget) :
    gdhOldAtomicProg S b = liftAuth1Stage tlAuthSigDdh S (fgAuth1KeyGapDhProg S b.q_total) :=
  rfl

private theorem sigOldAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) (pk : Bytes) :
    (sigOldAtomicProg S b).eval adv pk = (sigAuth1KeyDslProg S b).eval adv pk := by
  have h := liftAuth1Stage_eval tlAuthSigDdh S (fun _ => rfl) (sigAuth1KeyDslProg S b) adv pk
  have hId : embedVal (.prod (B 1569) (B 64)) = id := by
    funext ⟨x, y⟩; rfl
  rw [hId, id_map] at h
  exact h

private theorem gdhOldAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) (U V : Bytes) :
    (gdhOldAtomicProg S b).eval adv (U, V) =
      (fgAuth1KeyGapDhProg S b.q_total).eval adv (U, V) := by
  have h := liftAuth1Stage_eval tlAuthSigDdh S (fun _ => rfl)
    (fgAuth1KeyGapDhProg S b.q_total) adv (U, V)
  have hId : embedVal (B 32) = id := rfl
  rw [hId, id_map] at h
  exact h

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

/-- Converts `BoundedAdv (AuthAdversary S) b` into the 4-slot `IsQueryBoundP` hypotheses for `authSimPred`. -/
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

theorem eval_sig_run_eq_of_forgetSim
    (S : Setup) (b : QueryBudget)
    (R' : CostedReduction pqAtomicOps pqAuthSigAndDdhIface (authSpec S) (authCodec S)
      (PB 32) .unit .bool (.prod (PB 1569) (PB 64)))
    {forget : R'.σ.denote → (sigOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → R'.σ.denote → Prop}
    (hSim : ∀ pk : (PB 32).denote,
      ForgetSim R' (sigOldAtomicProg S b) forget P B pk Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j))
    (pk : (PB 32).denote) :
    R'.eval (fun _ => A.1.run) pk = (sigOldAtomicProg S b).eval (fun _ => A.1.run) pk :=
  (hSim pk).eval_eq (fun _ => A.1.run) hA

/-- Equality of evaluated `GapSigEufCmaAdv` adversaries from a `ForgetSim` instance against `sigOldAtomicProg`. -/
theorem eval_sig_eq_dslAdv_of_forgetSim
    (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.sig b).σ.denote → (sigOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.sig b).σ.denote → Prop}
    (hSim : ∀ pk : (PB 32).denote,
      ForgetSim (R_new.sig b) (sigOldAtomicProg S b) forget P B pk Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    R_new.eval.sig b A = sigAuth1KeyDslAdv S b A :=
  congrArg (fun r =>
    ({ run := r, q_sig := 2 * min S.N_spk_tot S.N_recv, q_ddh := authGdhQueryBudget S b,
       q_prim := gdhPrimQueryBudget S b } : GapSigEufCmaAdv))
    (funext fun pk =>
      (eval_sig_run_eq_of_forgetSim S b (R_new.sig b) hSim A hA pk).trans
        (sigOldAtomicProg_eval_eq S b (fun _ => A.1.run) pk))

theorem sig_bounded_of_forgetSim
    (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.sig b).σ.denote → (sigOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.sig b).σ.denote → Prop}
    (hSim : ∀ pk : (PB 32).denote,
      ForgetSim (R_new.sig b) (sigOldAtomicProg S b) forget P B pk Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    (R_new.eval.sig b A).Bounded := by
  rw [eval_sig_eq_dslAdv_of_forgetSim S b R_new hSim A hA]
  exact sigAuth1KeyDslAdv_bounded S b A

theorem sig_le_of_forgetSim
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.sig b).σ.denote → (sigOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.sig b).σ.denote → Prop}
    (hSim : ∀ pk : (PB 32).denote,
      ForgetSim (R_new.sig b) (sigOldAtomicProg S b) forget P B pk Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    GapSigEufCma Prim Prim.isValidDhTriple (sigReductionAuth1Key S b A) ≤
      GapSigEufCma Prim Prim.isValidDhTriple (R_new.eval.sig b A) := by
  rw [eval_sig_eq_dslAdv_of_forgetSim S b R_new hSim A hA]
  exact sigAuth1Key_sig_le Prim Prim.isValidDhTriple S b A

theorem eval_gdh_run_eq_of_forgetSim
    (S : Setup) (b : QueryBudget)
    (R' : CostedReduction pqAtomicOps pqAuthSigAndDdhIface (authSpec S) (authCodec S)
      (.prod (PB 32) (PB 32)) .unit .bool (PB 32))
    {forget : R'.σ.denote → (gdhOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → R'.σ.denote → Prop}
    (hSim : ∀ uv : ((.prod (PB 32) (PB 32)) : Ty pqAtomicSig).denote,
      ForgetSim R' (gdhOldAtomicProg S b) forget P B uv Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j))
    (uv : ((.prod (PB 32) (PB 32)) : Ty pqAtomicSig).denote) :
    R'.eval (fun _ => A.1.run) uv = (gdhOldAtomicProg S b).eval (fun _ => A.1.run) uv :=
  (hSim uv).eval_eq (fun _ => A.1.run) hA

/-- Equality of evaluated `GapDhWithSignAdv` adversaries from a `ForgetSim` instance against `gdhOldAtomicProg`. -/
theorem eval_gdh_eq_dslAdv_of_forgetSim
    (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.gdh b).σ.denote → (gdhOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.gdh b).σ.denote → Prop}
    (hSim : ∀ uv : ((.prod (PB 32) (PB 32)) : Ty pqAtomicSig).denote,
      ForgetSim (R_new.gdh b) (gdhOldAtomicProg S b) forget P B uv Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    R_new.eval.gdh b A = fgAuth1KeyGapDhDslAdv S b A :=
  congrArg (fun r =>
    ({ run := r, q_ddh := authGdhQueryBudget S b, q_sig := 2 * min S.N_spk_tot S.N_recv,
       q_prim := gdhPrimQueryBudget S b } : GapDhWithSignAdv))
    (funext fun U => funext fun V =>
      (eval_gdh_run_eq_of_forgetSim S b (R_new.gdh b) hSim A hA (U, V)).trans
        (gdhOldAtomicProg_eval_eq S b (fun _ => A.1.run) U V))

theorem gdh_bounded_of_forgetSim
    (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.gdh b).σ.denote → (gdhOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.gdh b).σ.denote → Prop}
    (hSim : ∀ uv : ((.prod (PB 32) (PB 32)) : Ty pqAtomicSig).denote,
      ForgetSim (R_new.gdh b) (gdhOldAtomicProg S b) forget P B uv Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    (R_new.eval.gdh b A).Bounded := by
  rw [eval_gdh_eq_dslAdv_of_forgetSim S b R_new hSim A hA]
  exact fgAuth1KeyGapDhDslAdv_bounded S b A

theorem gdh_le_of_forgetSim
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.gdh b).σ.denote → (gdhOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.gdh b).σ.denote → Prop}
    (hSim : ∀ uv : ((.prod (PB 32) (PB 32)) : Ty pqAtomicSig).denote,
      ForgetSim (R_new.gdh b) (gdhOldAtomicProg S b) forget P B uv Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    GapDhWithSign Prim Prim.isValidDhTriple Prim.pow8 (fgAuth1KeyGapDhAdv4 S b A) ≤
      GapDhWithSign Prim Prim.isValidDhTriple Prim.pow8 (R_new.eval.gdh b A) := by
  rw [eval_gdh_eq_dslAdv_of_forgetSim S b R_new hSim A hA]
  exact (fgAuth1KeyGapDhProg_gapDhWithSign_eq Prim Prim.isValidDhTriple Prim.pow8 S b A).ge

theorem a1s2KindProg_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (pk : Bytes) :
    (a1s2KindProg S b).eval (fun _ => A.1.run) pk =
      (sigOldAtomicProg S b).eval (fun _ => A.1.run) pk :=
  (a1s2KindProg_forgetSim S b pk).eval_eq (fun _ => A.1.run)
    (boundedAdv_isQueryBoundP_auth S b A)

theorem a1g2KindProg_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (uv : Bytes × Bytes) :
    (a1g2KindProg S b).eval (fun _ => A.1.run) uv =
      (gdhOldAtomicProg S b).eval (fun _ => A.1.run) uv :=
  (a1g2KindProg_forgetSim S b uv).eval_eq (fun _ => A.1.run)
    (boundedAdv_isQueryBoundP_auth S b A)

theorem eval_sig_eq_dslAdv (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S) (hSig : R_new.sig b = a1s2KindProg S b)
    (A : BoundedAdv (AuthAdversary S) b) :
    R_new.eval.sig b A = sigAuth1KeyDslAdv S b A := by
  refine congrArg (fun r =>
    ({ run := r, q_sig := 2 * min S.N_spk_tot S.N_recv, q_ddh := authGdhQueryBudget S b,
       q_prim := gdhPrimQueryBudget S b } : GapSigEufCmaAdv)) (funext fun pk => ?_)
  rw [hSig, a1s2KindProg_eval_eq S b A pk, sigOldAtomicProg_eval_eq S b (fun _ => A.1.run) pk]

theorem a1s2KindProg_sig_bounded (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S) (hSig : R_new.sig b = a1s2KindProg S b)
    (A : BoundedAdv (AuthAdversary S) b) :
    (R_new.eval.sig b A).Bounded := by
  rw [eval_sig_eq_dslAdv S b R_new hSig A]
  exact sigAuth1KeyDslAdv_bounded S b A

theorem a1s2KindProg_sig_le (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S) (hSig : R_new.sig b = a1s2KindProg S b)
    (A : BoundedAdv (AuthAdversary S) b) :
    GapSigEufCma Prim Prim.isValidDhTriple (sigReductionAuth1Key S b A) ≤
      GapSigEufCma Prim Prim.isValidDhTriple (R_new.eval.sig b A) := by
  rw [eval_sig_eq_dslAdv S b R_new hSig A]
  exact sigAuth1Key_sig_le Prim Prim.isValidDhTriple S b A

theorem eval_gdh_eq_dslAdv (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S) (hGdh : R_new.gdh b = a1g2KindProg S b)
    (A : BoundedAdv (AuthAdversary S) b) :
    R_new.eval.gdh b A = fgAuth1KeyGapDhDslAdv S b A := by
  refine congrArg (fun r =>
    ({ run := r, q_ddh := authGdhQueryBudget S b, q_sig := 2 * min S.N_spk_tot S.N_recv,
       q_prim := gdhPrimQueryBudget S b } : GapDhWithSignAdv)) (funext fun U => funext fun V => ?_)
  rw [hGdh, a1g2KindProg_eval_eq S b A (U, V),
    gdhOldAtomicProg_eval_eq S b (fun _ => A.1.run) U V]

theorem a1g2KindProg_gdh_bounded (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S) (hGdh : R_new.gdh b = a1g2KindProg S b)
    (A : BoundedAdv (AuthAdversary S) b) :
    (R_new.eval.gdh b A).Bounded := by
  rw [eval_gdh_eq_dslAdv S b R_new hGdh A]
  exact fgAuth1KeyGapDhDslAdv_bounded S b A

theorem a1g2KindProg_gdh_le (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S) (hGdh : R_new.gdh b = a1g2KindProg S b)
    (A : BoundedAdv (AuthAdversary S) b) :
    GapDhWithSign Prim Prim.isValidDhTriple Prim.pow8 (fgAuth1KeyGapDhAdv4 S b A) ≤
      GapDhWithSign Prim Prim.isValidDhTriple Prim.pow8 (R_new.eval.gdh b A) := by
  rw [eval_gdh_eq_dslAdv S b R_new hGdh A]
  exact (fgAuth1KeyGapDhProg_gapDhWithSign_eq Prim Prim.isValidDhTriple Prim.pow8 S b A).ge

theorem pqxdhAuth1KeyKind_sig_eq (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).sig b = a1s2KindProg S b := rfl

theorem pqxdhAuth1KeyKind_gdh_eq (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).gdh b = a1g2KindProg S b := rfl

/-- Semantic query compliance for `(pqxdhAuth1KeyKindCostedSims S).eval.sig`. -/
theorem pqxdhAuth1KeyKind_sig_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    ((pqxdhAuth1KeyKindCostedSims S).eval.sig b A).Bounded :=
  a1s2KindProg_sig_bounded S b (pqxdhAuth1KeyKindCostedSims S) rfl A

/-- Shallow-to-DSL `GapSigEufCma` advantage bound for `(pqxdhAuth1KeyKindCostedSims S).eval.sig`. -/
theorem pqxdhAuth1KeyKind_sig_le (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    GapSigEufCma Prim Prim.isValidDhTriple (sigReductionAuth1Key S b A) ≤
      GapSigEufCma Prim Prim.isValidDhTriple ((pqxdhAuth1KeyKindCostedSims S).eval.sig b A) :=
  a1s2KindProg_sig_le Prim S b (pqxdhAuth1KeyKindCostedSims S) rfl A

/-- Semantic query compliance for `(pqxdhAuth1KeyKindCostedSims S).eval.gdh`. -/
theorem pqxdhAuth1KeyKind_gdh_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    ((pqxdhAuth1KeyKindCostedSims S).eval.gdh b A).Bounded :=
  a1g2KindProg_gdh_bounded S b (pqxdhAuth1KeyKindCostedSims S) rfl A

/-- Shallow-to-DSL `GapDhWithSign` advantage bound for `(pqxdhAuth1KeyKindCostedSims S).eval.gdh`. -/
theorem pqxdhAuth1KeyKind_gdh_le (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    GapDhWithSign Prim Prim.isValidDhTriple Prim.pow8 (fgAuth1KeyGapDhAdv4 S b A) ≤
      GapDhWithSign Prim Prim.isValidDhTriple Prim.pow8
        ((pqxdhAuth1KeyKindCostedSims S).eval.gdh b A) :=
  a1g2KindProg_gdh_le Prim S b (pqxdhAuth1KeyKindCostedSims S) rfl A

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindSiggdhEq
