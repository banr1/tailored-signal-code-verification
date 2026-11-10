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
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfCk -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfMk -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfBounds -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfHmac -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3E -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3D
import Computational.Proofs.SpecLemmas.SignalPqxdh.Game
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrf

public section

set_option autoImplicit false

/-!
# Forgetful-Simulation Bridges for One-Key Auth `ck`, `mk`, and `int`

**Checked by Lean.**

Bridges `ForgetSim` bundles on the shadow-indexed one-key Auth `ck`, `mk`, and `int` reductions to
`CostedReduction.eval` equality, semantic query-bound compliance (`ck_bounded`, `mk_bounded`,
`int_bounded`), and shallow-to-DSL advantage transfers (`ck_le`, `mk_le`, `int_le`).
-/

open OracleComp OracleSpec
open SignalPqxdh (Setup QueryBudget BoundedAdv AuthAdversary QueryBounded Primitives Bytes
  AuthQuery authSpec isGameQuery PrimBaseSpec isPrimQuery₀
  PrfCkAdv PrfMsgKeysAdv PrfHmacAdv PrfChainKey PrfMsgKeys PrfHmac)
open SignalPqxdh.Costed (PB pqAtomicSig pqAtomicOps authCodec pqAuthPrimIface pqPrfMkIface
  pqPrfHmacIface)
open SignalPqxdh.Security (primQueryBudget Auth1KeyCostedReductionFamily prfHmacReductionAuth1Key
  PrimBounded primBounded_bind_le primBounded_embedUnif AuthHybridStateFixed)
open SignalPqxdh.Security.AuthSubHops1to3 (prfCkReductionAuthFixed1Key
  prfMsgKeysReductionAuthFixed1Key authCkStepWithPrim1Key
  authCkPreSampleRunPrim1Key primBounded_authCkStepWithPrim sampAtCkPrim
  primBounded_sampAtCkPrim primBounded_finalizeAuthFixedPrim primBounded_runWithPrimStep)
open ReductionDsl (Ty CostedReduction)
open Computational.Proofs.ReductionDsl.StepSim (ForgetSim isGamePred instDecidablePredIsGamePred
  isQueryBoundP_min)
open Computational.Proofs.SignalPqxdh.AtomicLift (tlAuthPrim tlPrfMk tlPrfHmac
  liftAuth1Stage liftAuth1Stage_eval embedVal)
open SignalPqxdh.Security.ReductionDsl.AuthPrf (prfCkRedProg1Key prfCkRedProg1Key_prfCk_eq
  prfCkReductionAuthFixed1KeyDslAdv prfCkReductionAuthFixed1KeyDslAdv_eq
  AuthQuery.NotInitPrin authCkStepWithPrim1Key_eq_of_ne primBounded_stepAuthOtherPrim1Key
  prfMsgKeysRedProg1Key prfMsgKeysRedProg1Key_prfMsgKeys_eq
  prfMsgKeys1KeyDslAdv_bounded prfMsgKeys1KeyDslAdv_prim_queries)
open SignalPqxdh.Security.ReductionDsl.AuthPrfHmac (prfHmacRedProg1Key prfHmac1KeyDslAdv
  prfHmac1KeyDslAdv_bounded prfHmac1KeyDslAdv_prfHmac_eq)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (prfCk1KeyKindProg prfMsgKeys1KeyKindProg prfHmac1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds instDecidablePredAuthSimPred
   prfCkOldAtomicProg prfMkOldAtomicProg prfHmacOldAtomicProg)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs
  (pqxdhAuth1KeyKindCostedSims)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrf
  (prfCk1KeyKindProg_forgetSim prfMsgKeys1KeyKindProg_forgetSim prfHmac1KeyKindProg_forgetSim)

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindPrfEq

theorem prfCkOldAtomicProg_def_eq (S : Setup) (b : QueryBudget) :
    prfCkOldAtomicProg S b = liftAuth1Stage tlAuthPrim S (prfCkRedProg1Key S b.q_total) :=
  rfl

theorem prfMkOldAtomicProg_def_eq (S : Setup) (b : QueryBudget) :
    prfMkOldAtomicProg S b = liftAuth1Stage tlPrfMk S (prfMsgKeysRedProg1Key S b.q_total) :=
  rfl

theorem prfHmacOldAtomicProg_def_eq (S : Setup) (b : QueryBudget) :
    prfHmacOldAtomicProg S b = liftAuth1Stage tlPrfHmac S (prfHmacRedProg1Key S b.q_total) :=
  rfl

private theorem prfCkOldAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) (mkSeed ck1 : Bytes) :
    (prfCkOldAtomicProg S b).eval adv (mkSeed, ck1) =
      (prfCkRedProg1Key S b.q_total).eval adv (mkSeed, ck1) := by
  have h := liftAuth1Stage_eval tlAuthPrim S (fun _ => rfl)
    (prfCkRedProg1Key S b.q_total) adv (mkSeed, ck1)
  have hId : embedVal .bool = id := rfl
  rw [hId, id_map] at h
  exact h

private theorem prfMkOldAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) :
    (prfMkOldAtomicProg S b).eval adv () =
      (prfMsgKeysRedProg1Key S b.q_total).eval adv () := by
  have h := liftAuth1Stage_eval tlPrfMk S (fun _ => rfl)
    (prfMsgKeysRedProg1Key S b.q_total) adv ()
  have hId : embedVal .bool = id := rfl
  rw [hId, id_map] at h
  exact h

private theorem prfHmacOldAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) :
    (prfHmacOldAtomicProg S b).eval adv () =
      (prfHmacRedProg1Key S b.q_total).eval adv () := by
  have h := liftAuth1Stage_eval tlPrfHmac S (fun _ => rfl)
    (prfHmacRedProg1Key S b.q_total) adv ()
  have hId : embedVal .bool = id := rfl
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

/-- Discharges the `IsQueryBoundP` hypothesis of `ForgetSim.eval_eq` from `BoundedAdv` across the
four `AuthCoreKSimBase` budget slots. -/
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

/-- Identifies `R_new.eval.ck b A` with the `prfCkRedProg1Key` distinguisher given a `ForgetSim`
bundle on `R_new.ck b`. -/
theorem eval_ck_eq_dslAdv_of_forgetSim
    (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.ck b).σ.denote → (prfCkOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.ck b).σ.denote → Prop}
    (hSim : ∀ chalPair : ((.prod (PB 32) (PB 32)) : Ty pqAtomicSig).denote,
      ForgetSim (R_new.ck b) (prfCkOldAtomicProg S b) forget P B chalPair Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    R_new.eval.ck b A =
      ({ dist := fun mkSeed ck1 => (prfCkRedProg1Key S b.q_total).eval (fun _ => A.1.run) (mkSeed, ck1),
         q_prf := 1, q_prim := primQueryBudget S b } : PrfCkAdv) :=
  congrArg (fun r => ({ dist := r, q_prf := 1, q_prim := primQueryBudget S b } : PrfCkAdv))
    (funext fun mkSeed => funext fun ck1 =>
      ((hSim (mkSeed, ck1)).eval_eq (fun _ => A.1.run) hA).trans
        (prfCkOldAtomicProg_eval_eq S b (fun _ => A.1.run) mkSeed ck1))

theorem ck_le_of_forgetSim
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.ck b).σ.denote → (prfCkOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.ck b).σ.denote → Prop}
    (hSim : ∀ chalPair : ((.prod (PB 32) (PB 32)) : Ty pqAtomicSig).denote,
      ForgetSim (R_new.ck b) (prfCkOldAtomicProg S b) forget P B chalPair Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    PrfChainKey Prim (prfCkReductionAuthFixed1Key S b A) ≤
      PrfChainKey Prim (R_new.eval.ck b A) := by
  rw [eval_ck_eq_dslAdv_of_forgetSim S b R_new hSim A hA]
  exact (prfCkRedProg1Key_prfCk_eq Prim S b A).ge

private theorem primBounded_authCkStepWithPrim1Key_aux (S : Setup)
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (hSamp : ∀ s, PrimBounded (sampAt s) 2)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    PrimBounded (authCkStepWithPrim1Key S sampAt q hst) (S.N_dh * 26 + 21) := by
  by_cases hI : AuthQuery.NotInitPrin q
  · rw [authCkStepWithPrim1Key_eq_of_ne sampAt q hI hst]
    exact primBounded_authCkStepWithPrim S sampAt hSamp q hst
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      by_contra hne; push Not at hne; exact hI hne
    exact (primBounded_stepAuthOtherPrim1Key S (.initPrin u) hst).mono (by omega)

private theorem prfCkReductionAuthFixed1Key_bounded_aux (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfCkReductionAuthFixed1Key S b A).Bounded := fun mkSeedChal ck1_1Chal => by
  obtain ⟨_, _, _, _, hTot, _⟩ := A.2
  refine primBounded_bind_le (b.q_total * (S.N_dh * 26 + 21) + S.N_dh * 5)
    (primBounded_embedUnif _ 0)
    (fun idx => ?_)
    (by dsimp [prfCkReductionAuthFixed1Key]; omega)
  unfold authCkPreSampleRunPrim1Key
  refine primBounded_bind_le (b.q_total * (S.N_dh * 26 + 21) + S.N_dh * 5)
    (primBounded_embedUnif ($ᵗ Bool) 0)
    (fun secb => ?_) (by omega)
  refine primBounded_bind_le (S.N_dh * 5)
    (primBounded_runWithPrimStep
      (authCkStepWithPrim1Key S (sampAtCkPrim idx (mkSeedChal, ck1_1Chal)))
      (S.N_dh * 26 + 21)
      (fun q s => primBounded_authCkStepWithPrim1Key_aux S
        (sampAtCkPrim idx (mkSeedChal, ck1_1Chal))
        (primBounded_sampAtCkPrim idx (mkSeedChal, ck1_1Chal)) q s)
      A.1.run b.q_total hTot
      (AuthHybridStateFixed.empty S secb))
    (fun ⟨b', finalSt⟩ => primBounded_finalizeAuthFixedPrim S secb b' finalSt.toAuthHybridState)
    (by omega)

theorem ck_bounded_of_forgetSim
    (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.ck b).σ.denote → (prfCkOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.ck b).σ.denote → Prop}
    (hSim : ∀ chalPair : ((.prod (PB 32) (PB 32)) : Ty pqAtomicSig).denote,
      ForgetSim (R_new.ck b) (prfCkOldAtomicProg S b) forget P B chalPair Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    (R_new.eval.ck b A).Bounded := by
  rw [eval_ck_eq_dslAdv_of_forgetSim S b R_new hSim A hA]
  intro mkSeed ck1
  change ((prfCkReductionAuthFixed1KeyDslAdv S b A).dist mkSeed ck1).IsQueryBoundP
    (fun q => isPrimQuery₀ q = true) (primQueryBudget S b)
  rw [prfCkReductionAuthFixed1KeyDslAdv_eq]
  exact (prfCkReductionAuthFixed1Key_bounded_aux S b A mkSeed ck1).mono
    (by dsimp [prfCkReductionAuthFixed1Key, primQueryBudget]; nlinarith)

/-- Identifies `R_new.eval.mk b A` with the `prfMsgKeysRedProg1Key` adversary given a `ForgetSim`
bundle on `R_new.mk b`. -/
theorem eval_mk_eq_dslAdv_of_forgetSim
    (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.mk b).σ.denote → (prfMkOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.mk b).σ.denote → Prop}
    (hSim : ForgetSim (R_new.mk b) (prfMkOldAtomicProg S b) forget P B () Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    R_new.eval.mk b A =
      ({ run := (prfMsgKeysRedProg1Key S b.q_total).eval (fun _ => A.1.run) (),
         q_prf := S.N_recv_tot + 1, q_prim := primQueryBudget S b } : PrfMsgKeysAdv) :=
  congrArg (fun r =>
    ({ run := r, q_prf := S.N_recv_tot + 1, q_prim := primQueryBudget S b } : PrfMsgKeysAdv))
    ((hSim.eval_eq (fun _ => A.1.run) hA).trans
      (prfMkOldAtomicProg_eval_eq S b (fun _ => A.1.run)))

theorem mk_bounded_of_forgetSim
    (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.mk b).σ.denote → (prfMkOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.mk b).σ.denote → Prop}
    (hSim : ForgetSim (R_new.mk b) (prfMkOldAtomicProg S b) forget P B () Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    (R_new.eval.mk b A).Bounded := by
  rw [eval_mk_eq_dslAdv_of_forgetSim S b R_new hSim A hA]
  exact ⟨(prfMsgKeys1KeyDslAdv_bounded S b A).1,
    (prfMsgKeys1KeyDslAdv_bounded S b A).2.mono (prfMsgKeys1KeyDslAdv_prim_queries S b A)⟩

theorem mk_le_of_forgetSim
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.mk b).σ.denote → (prfMkOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.mk b).σ.denote → Prop}
    (hSim : ForgetSim (R_new.mk b) (prfMkOldAtomicProg S b) forget P B () Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    PrfMsgKeys Prim (prfMsgKeysReductionAuthFixed1Key S b A) ≤
      PrfMsgKeys Prim (R_new.eval.mk b A) := by
  rw [eval_mk_eq_dslAdv_of_forgetSim S b R_new hSim A hA]
  exact (prfMsgKeysRedProg1Key_prfMsgKeys_eq Prim S b A).ge

/-- Identifies `R_new.eval.int b A` with `prfHmac1KeyDslAdv S b A` given a `ForgetSim` bundle on
`R_new.int b`. -/
theorem eval_int_eq_dslAdv_of_forgetSim
    (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.int b).σ.denote → (prfHmacOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.int b).σ.denote → Prop}
    (hSim : ForgetSim (R_new.int b) (prfHmacOldAtomicProg S b) forget P B () Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    R_new.eval.int b A = prfHmac1KeyDslAdv S b A :=
  congrArg (fun r =>
    ({ run := r, q_prf := S.N_recv_tot + 1, q_prim := primQueryBudget S b } : PrfHmacAdv))
    ((hSim.eval_eq (fun _ => A.1.run) hA).trans
      (prfHmacOldAtomicProg_eval_eq S b (fun _ => A.1.run)))

theorem int_bounded_of_forgetSim
    (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.int b).σ.denote → (prfHmacOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.int b).σ.denote → Prop}
    (hSim : ForgetSim (R_new.int b) (prfHmacOldAtomicProg S b) forget P B () Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    (R_new.eval.int b A).Bounded := by
  rw [eval_int_eq_dslAdv_of_forgetSim S b R_new hSim A hA]
  exact prfHmac1KeyDslAdv_bounded S b A

theorem int_le_of_forgetSim
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (R_new : Auth1KeyCostedReductionFamily S)
    {forget : (R_new.int b).σ.denote → (prfHmacOldAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → AuthQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (R_new.int b).σ.denote → Prop}
    (hSim : ForgetSim (R_new.int b) (prfHmacOldAtomicProg S b) forget P B () Inv)
    (A : BoundedAdv (AuthAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m), A.1.run.IsQueryBoundP (isGamePred (G := authSpec S) (P j)) (B j)) :
    PrfHmac Prim (prfHmacReductionAuth1Key S b A) ≤
      PrfHmac Prim (R_new.eval.int b A) := by
  rw [eval_int_eq_dslAdv_of_forgetSim S b R_new hSim A hA]
  exact (prfHmac1KeyDslAdv_prfHmac_eq S Prim b A).ge

theorem pqxdhAuth1KeyKind_ck_eq (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).ck b = prfCk1KeyKindProg S b := rfl

theorem pqxdhAuth1KeyKind_mk_eq (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).mk b = prfMsgKeys1KeyKindProg S b := rfl

theorem pqxdhAuth1KeyKind_int_eq (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).int b = prfHmac1KeyKindProg S b := rfl

theorem prfCk1KeyKindProg_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (chalPair : Bytes × Bytes) :
    (prfCk1KeyKindProg S b).eval (fun _ => A.1.run) chalPair =
      (prfCkOldAtomicProg S b).eval (fun _ => A.1.run) chalPair :=
  (prfCk1KeyKindProg_forgetSim S b chalPair).eval_eq (fun _ => A.1.run)
    (boundedAdv_isQueryBoundP_auth S b A)

theorem prfMsgKeys1KeyKindProg_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfMsgKeys1KeyKindProg S b).eval (fun _ => A.1.run) () =
      (prfMkOldAtomicProg S b).eval (fun _ => A.1.run) () :=
  (prfMsgKeys1KeyKindProg_forgetSim S b ()).eval_eq (fun _ => A.1.run)
    (boundedAdv_isQueryBoundP_auth S b A)

theorem prfHmac1KeyKindProg_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfHmac1KeyKindProg S b).eval (fun _ => A.1.run) () =
      (prfHmacOldAtomicProg S b).eval (fun _ => A.1.run) () :=
  (prfHmac1KeyKindProg_forgetSim S b ()).eval_eq (fun _ => A.1.run)
    (boundedAdv_isQueryBoundP_auth S b A)

theorem pqxdhAuth1KeyKind_eval_ck_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (pqxdhAuth1KeyKindCostedSims S).eval.ck b A =
      ({ dist := fun mkSeed ck1 =>
           (prfCkRedProg1Key S b.q_total).eval (fun _ => A.1.run) (mkSeed, ck1),
         q_prf := 1, q_prim := primQueryBudget S b } : PrfCkAdv) :=
  congrArg (fun r => ({ dist := r, q_prf := 1, q_prim := primQueryBudget S b } : PrfCkAdv))
    (funext fun mkSeed => funext fun ck1 =>
      (prfCk1KeyKindProg_eval_eq S b A (mkSeed, ck1)).trans
        (prfCkOldAtomicProg_eval_eq S b (fun _ => A.1.run) mkSeed ck1))

theorem pqxdhAuth1KeyKind_ck_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    ((pqxdhAuth1KeyKindCostedSims S).eval.ck b A).Bounded := by
  rw [pqxdhAuth1KeyKind_eval_ck_eq S b A]
  intro mkSeed ck1
  change ((prfCkReductionAuthFixed1KeyDslAdv S b A).dist mkSeed ck1).IsQueryBoundP
    (fun q => isPrimQuery₀ q = true) (primQueryBudget S b)
  rw [prfCkReductionAuthFixed1KeyDslAdv_eq]
  exact (prfCkReductionAuthFixed1Key_bounded_aux S b A mkSeed ck1).mono
    (by dsimp [prfCkReductionAuthFixed1Key, primQueryBudget]; nlinarith)

theorem pqxdhAuth1KeyKind_ck_le (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    PrfChainKey Prim (prfCkReductionAuthFixed1Key S b A) ≤
      PrfChainKey Prim ((pqxdhAuth1KeyKindCostedSims S).eval.ck b A) := by
  rw [pqxdhAuth1KeyKind_eval_ck_eq S b A]
  exact (prfCkRedProg1Key_prfCk_eq Prim S b A).ge

theorem pqxdhAuth1KeyKind_eval_mk_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (pqxdhAuth1KeyKindCostedSims S).eval.mk b A =
      ({ run := (prfMsgKeysRedProg1Key S b.q_total).eval (fun _ => A.1.run) (),
         q_prf := S.N_recv_tot + 1, q_prim := primQueryBudget S b } : PrfMsgKeysAdv) :=
  congrArg (fun r =>
    ({ run := r, q_prf := S.N_recv_tot + 1, q_prim := primQueryBudget S b } : PrfMsgKeysAdv))
    ((prfMsgKeys1KeyKindProg_eval_eq S b A).trans
      (prfMkOldAtomicProg_eval_eq S b (fun _ => A.1.run)))

theorem pqxdhAuth1KeyKind_mk_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    ((pqxdhAuth1KeyKindCostedSims S).eval.mk b A).Bounded := by
  rw [pqxdhAuth1KeyKind_eval_mk_eq S b A]
  exact ⟨(prfMsgKeys1KeyDslAdv_bounded S b A).1,
    (prfMsgKeys1KeyDslAdv_bounded S b A).2.mono (prfMsgKeys1KeyDslAdv_prim_queries S b A)⟩

theorem pqxdhAuth1KeyKind_mk_le (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    PrfMsgKeys Prim (prfMsgKeysReductionAuthFixed1Key S b A) ≤
      PrfMsgKeys Prim ((pqxdhAuth1KeyKindCostedSims S).eval.mk b A) := by
  rw [pqxdhAuth1KeyKind_eval_mk_eq S b A]
  exact (prfMsgKeysRedProg1Key_prfMsgKeys_eq Prim S b A).ge

theorem pqxdhAuth1KeyKind_eval_int_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (pqxdhAuth1KeyKindCostedSims S).eval.int b A = prfHmac1KeyDslAdv S b A :=
  congrArg (fun r =>
    ({ run := r, q_prf := S.N_recv_tot + 1, q_prim := primQueryBudget S b } : PrfHmacAdv))
    ((prfHmac1KeyKindProg_eval_eq S b A).trans
      (prfHmacOldAtomicProg_eval_eq S b (fun _ => A.1.run)))

theorem pqxdhAuth1KeyKind_int_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    ((pqxdhAuth1KeyKindCostedSims S).eval.int b A).Bounded := by
  rw [pqxdhAuth1KeyKind_eval_int_eq S b A]
  exact prfHmac1KeyDslAdv_bounded S b A

theorem pqxdhAuth1KeyKind_int_le (Prim : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    PrfHmac Prim (prfHmacReductionAuth1Key S b A) ≤
      PrfHmac Prim ((pqxdhAuth1KeyKindCostedSims S).eval.int b A) := by
  rw [pqxdhAuth1KeyKind_eval_int_eq S b A]
  exact (prfHmac1KeyDslAdv_prfHmac_eq S Prim b A).ge

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindPrfEq
