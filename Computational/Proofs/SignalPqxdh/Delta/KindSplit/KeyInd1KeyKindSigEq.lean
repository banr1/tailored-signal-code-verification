/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimA

public section

set_option autoImplicit false

/-!
# One-Stage Forgetful-Simulation Bridges for `KeyInd` `sig`

**Checked by Lean.**

Bridges `ForgetSim` on `sigKeyInd1KeyKindAtomicProg` against `sigKeyInd1KeyActiveAtomicProg`
to `CostedReduction.eval` equality, `GapSigEufCma` and `GapSigEufCmaReal` advantage
equalities, and `.Bounded` preservation.
-/

open OracleComp OracleSpec
open SignalPqxdh (Setup QueryBudget BoundedAdv KeyIndAdversary Primitives Bytes
  KeyIndQuery keyIndSpec isKeyIndOnlineQuery isKeyIndRoQuery isGameQuery
  GapSigEufCmaAdv GapSigEufCma GapSigEufCmaReal)
open SignalPqxdh.Costed (PB pqAtomicOps pqKeyIndCodec pqSigAndDdhIface)
open SignalPqxdh.Security (gdhQueryBudget gdhPrimQueryBudget KeyIndCostedReductionFamily)
open ReductionDsl (Ty CostedReduction)
open Computational.Proofs.ReductionDsl.StepSim (ForgetSim isGamePred instDecidablePredIsGamePred
  isQueryBoundP_min)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs
  (sigKeyInd1KeyActiveAtomicProg pqxdhKeyInd1KeyActiveCostedSims)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs
  (sigKeyInd1KeyKindAtomicProg pqxdhKeyInd1KeyKindCostedSims)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase
  (keyIndSimPred keyIndSimBounds instDecidablePredKeyIndSimPred)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimA
  (sigKeyInd1KeyKindAtomicProg_forgetSim)

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindSigEq

theorem pqxdhKeyInd1KeyKindCostedSims_sig_eq (S : Setup) :
    (pqxdhKeyInd1KeyKindCostedSims S).sig = sigKeyInd1KeyKindAtomicProg S :=
  rfl

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

/-- Discharges the per-slot `IsQueryBoundP` obligation from `BoundedAdv` across
`keyIndSimPred` and `keyIndSimBounds`. -/
theorem boundedAdv_isQueryBoundP_keyInd (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    ∀ (_ : Unit) (j : Fin 3),
      A.1.run.IsQueryBoundP
        (isGamePred (G := keyIndSpec S) (keyIndSimPred S j))
        (keyIndSimBounds b j) := by
  intro _ j
  obtain ⟨hRo, _, _, hTot, hOn⟩ := A.2
  have hTotSub : ∀ (p : KeyIndQuery S → Prop) [DecidablePred p],
      A.1.run.IsQueryBoundP (isGamePred (G := keyIndSpec S) p) b.q_total := by
    intro p _
    refine isQueryBoundP_of_imp (fun q hq => ?_) hTot
    cases q with
    | inl _ => exact False.elim hq
    | inr _ => rfl
  match j with
  | ⟨0, _⟩ =>
    refine isQueryBoundP_min ?_ (hTotSub (keyIndSimPred S ⟨0, by omega⟩))
    refine isQueryBoundP_of_imp (fun q hq => ?_) hOn
    cases q with
    | inl _ => exact False.elim hq
    | inr t => exact hq
  | ⟨1, _⟩ =>
    refine isQueryBoundP_min ?_ (hTotSub (keyIndSimPred S ⟨1, by omega⟩))
    refine isQueryBoundP_of_imp (fun q hq => ?_) hRo
    cases q with
    | inl _ => exact False.elim hq
    | inr t => exact hq
  | ⟨2, _⟩ =>
    exact hTotSub (keyIndSimPred S ⟨2, by omega⟩)

/-- Derives `CostedReduction.eval` equality for `sigKeyInd1KeyKindAtomicProg` from a `ForgetSim`
bundle against `sigKeyInd1KeyActiveAtomicProg`. -/
theorem sigKeyInd1KeyKindAtomicProg_eval_eq_of_forgetSim
    (S : Setup) (b : QueryBudget)
    {forget : (sigKeyInd1KeyKindAtomicProg S b).σ.denote →
      (sigKeyInd1KeyActiveAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → KeyIndQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (sigKeyInd1KeyKindAtomicProg S b).σ.denote → Prop}
    (hSim : ∀ pk : (PB 32).denote,
      ForgetSim (sigKeyInd1KeyKindAtomicProg S b) (sigKeyInd1KeyActiveAtomicProg S b)
        forget P B pk Inv)
    (A : BoundedAdv (KeyIndAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m),
      A.1.run.IsQueryBoundP (isGamePred (G := keyIndSpec S) (P j)) (B j))
    (pk : Bytes) :
    (sigKeyInd1KeyKindAtomicProg S b).eval (fun _ => A.1.run) pk =
      (sigKeyInd1KeyActiveAtomicProg S b).eval (fun _ => A.1.run) pk :=
  (hSim pk).eval_eq (fun _ => A.1.run) hA

theorem sigKeyInd1KeyKindAtomicProg_eval_eq
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) (pk : Bytes) :
    (sigKeyInd1KeyKindAtomicProg S b).eval (fun _ => A.1.run) pk =
      (sigKeyInd1KeyActiveAtomicProg S b).eval (fun _ => A.1.run) pk :=
  sigKeyInd1KeyKindAtomicProg_eval_eq_of_forgetSim S b
    (sigKeyInd1KeyKindAtomicProg_forgetSim S b) A
    (boundedAdv_isQueryBoundP_keyInd S b A) pk

/-- Equality of evaluated `GapSigEufCmaAdv` adversaries between `pqxdhKeyInd1KeyKindCostedSims`
and `pqxdhKeyInd1KeyActiveCostedSims`. -/
theorem pqxdhKeyInd1KeyKindCostedSims_eval_sig_eq
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    (pqxdhKeyInd1KeyKindCostedSims S).eval.sig b A =
      (pqxdhKeyInd1KeyActiveCostedSims S).eval.sig b A :=
  congrArg (fun r =>
    ({ run := r, q_sig := 2 * min S.N_spk_tot S.N_recv, q_ddh := gdhQueryBudget S b,
       q_prim := gdhPrimQueryBudget S b } : GapSigEufCmaAdv))
    (funext fun pk => sigKeyInd1KeyKindAtomicProg_eval_eq S b A pk)

theorem gapSigEufCma_keyInd1KeyKind_eq
    (Prim : Primitives) (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapSigEufCma Prim Prim.isValidDhTriple ((pqxdhKeyInd1KeyKindCostedSims S).eval.sig b A) =
      GapSigEufCma Prim Prim.isValidDhTriple ((pqxdhKeyInd1KeyActiveCostedSims S).eval.sig b A) := by
  rw [pqxdhKeyInd1KeyKindCostedSims_eval_sig_eq S b A]

theorem gapSigEufCmaReal_keyInd1KeyKind_eq
    (Prim : Primitives) (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapSigEufCmaReal Prim Prim.isValidDhTriple ((pqxdhKeyInd1KeyKindCostedSims S).eval.sig b A) =
      GapSigEufCmaReal Prim Prim.isValidDhTriple
        ((pqxdhKeyInd1KeyActiveCostedSims S).eval.sig b A) := by
  rw [pqxdhKeyInd1KeyKindCostedSims_eval_sig_eq S b A]

theorem pqxdhKeyInd1KeyKindCostedSims_sig_bounded
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (hAct : ((pqxdhKeyInd1KeyActiveCostedSims S).eval.sig b A).Bounded) :
    ((pqxdhKeyInd1KeyKindCostedSims S).eval.sig b A).Bounded := by
  rw [pqxdhKeyInd1KeyKindCostedSims_eval_sig_eq S b A]
  exact hAct

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindSigEq
