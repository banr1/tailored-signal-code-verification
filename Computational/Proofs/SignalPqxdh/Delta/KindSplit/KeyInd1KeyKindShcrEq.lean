/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Proofs.ReductionDsl.StepSimTwoStage -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyDefs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSim

public section

set_option autoImplicit false

/-!
# Two-Stage Forgetful-Simulation Bridges for `KeyInd` `shcr`

**Checked by Lean.**

Bridges `TwoStageForgetSim` on `shcrKeyInd1KeyKindAtomicProg` against
`shcrKeyInd1KeyActiveAtomicProg` to `kemShCrExp` experiment equality, `KemShCr` and
`KemShCrReal` advantage equalities, and `KI1KeyActiveHopG0G3Stmt` transfer.
-/

open OracleComp OracleSpec
open SignalPqxdh (Setup QueryBudget BoundedAdv KeyIndAdversary Primitives
  KeyIndQuery keyIndSpec isKeyIndOnlineQuery isKeyIndRoQuery isGameQuery
  GapSigEufCmaReal KemShCrAdv kemShCrExp KemShCr KemShCrReal
  sampleKemKeyGen sampleCoins32 primBaseImpl kyberCtLen kyberPkLen)
open SignalPqxdh.Costed (PB pqAtomicSig pqAtomicOps pqKeyIndCodec pqPrimIface)
open SignalPqxdh.Security (KeyIndCostedReductionFamily)
open ReductionDsl (Ty TwoStageCostedReduction)
open Computational.Proofs.ReductionDsl.StepSim (isGamePred instDecidablePredIsGamePred
  isQueryBoundP_min)
open Computational.Proofs.ReductionDsl.StepSimTwoStage (TwoStageForgetSim
  twoStage_simulateQ_eval_bind_eq_of_forgetSim)
open Proofs.SignalPqxdh.Security.PqxdhDelta (KI1KeyActiveHopG0G3Stmt)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs
  (shcrKeyInd1KeyActiveAtomicProg pqxdhKeyInd1KeyActiveCostedSims)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs
  (shcrKeyInd1KeyKindAtomicProg pqxdhKeyInd1KeyKindCostedSims)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase
  (keyIndSimPred keyIndSimBounds instDecidablePredKeyIndSimPred)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSim
  (shcrKeyInd1KeyKindAtomicProg_twoStageForgetSim)

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindShcrEq

theorem pqxdhKeyInd1KeyKindCostedSims_shcr_eq (S : Setup) :
    (pqxdhKeyInd1KeyKindCostedSims S).shcr = shcrKeyInd1KeyKindAtomicProg S :=
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

/-- Derives `kemShCrExp` experiment equality for `shcrKeyInd1KeyKindAtomicProg` from a
`TwoStageForgetSim` bundle against `shcrKeyInd1KeyActiveAtomicProg`. -/
theorem kemShCrExp_keyInd1KeyKind_eq_of_twoStageForgetSim
    (Prim : Primitives) (S : Setup) (b : QueryBudget)
    {forgetπ : (shcrKeyInd1KeyKindAtomicProg S b).π.denote →
      (shcrKeyInd1KeyActiveAtomicProg S b).π.denote}
    {forgetσ : (shcrKeyInd1KeyKindAtomicProg S b).σ.denote →
      (shcrKeyInd1KeyActiveAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → KeyIndQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (shcrKeyInd1KeyKindAtomicProg S b).σ.denote → Prop}
    {InvPause : (Fin m → Nat) → (shcrKeyInd1KeyKindAtomicProg S b).π.denote →
      (shcrKeyInd1KeyKindAtomicProg S b).σ.denote → Prop}
    (hSim : ∀ pksk : ((.prod (PB 1568) (PB 3168)) : Ty pqAtomicSig).denote,
      TwoStageForgetSim (shcrKeyInd1KeyKindAtomicProg S b) (shcrKeyInd1KeyActiveAtomicProg S b)
        forgetπ forgetσ P B pksk Inv InvPause)
    (A : BoundedAdv (KeyIndAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m),
      A.1.run.IsQueryBoundP (isGamePred (G := keyIndSpec S) (P j)) (B j)) :
    kemShCrExp Prim ((pqxdhKeyInd1KeyKindCostedSims S).eval.shcr b A) =
      kemShCrExp Prim ((pqxdhKeyInd1KeyActiveCostedSims S).eval.shcr b A) := by
  unfold kemShCrExp
  dsimp only [KeyIndCostedReductionFamily.eval, pqxdhKeyInd1KeyKindCostedSims,
    pqxdhKeyInd1KeyActiveCostedSims]
  refine congrArg (sampleKemKeyGen Prim >>= ·) (funext fun ⟨pk, sk⟩ => ?_)
  exact twoStage_simulateQ_eval_bind_eq_of_forgetSim (primBaseImpl Prim) (hSim (pk, sk))
    (fun _ => A.1.run) hA b.q_total b.q_total false
    (fun pk' eval2Sim => do
      let r ← sampleCoins32
      let some (ss, ct) := Prim.kemEncaps pk' r | return false
      let ct' ← eval2Sim (ss, ct)
      return (decide (Prim.kemDecaps sk ct' = some ss) && decide (ct' ≠ ct ∨ pk' ≠ pk) &&
              decide (ct'.length = kyberCtLen ∧ pk'.length = kyberPkLen)))

theorem kemShCrExp_keyInd1KeyKind_eq
    (Prim : Primitives) (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    kemShCrExp Prim ((pqxdhKeyInd1KeyKindCostedSims S).eval.shcr b A) =
      kemShCrExp Prim ((pqxdhKeyInd1KeyActiveCostedSims S).eval.shcr b A) :=
  kemShCrExp_keyInd1KeyKind_eq_of_twoStageForgetSim Prim S b
    (shcrKeyInd1KeyKindAtomicProg_twoStageForgetSim S b) A
    (boundedAdv_isQueryBoundP_keyInd S b A)

theorem kemShCr_keyInd1KeyKind_eq
    (Prim : Primitives) (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCr Prim ((pqxdhKeyInd1KeyKindCostedSims S).eval.shcr b A) =
      KemShCr Prim ((pqxdhKeyInd1KeyActiveCostedSims S).eval.shcr b A) := by
  unfold KemShCr
  rw [kemShCrExp_keyInd1KeyKind_eq Prim S b A]

theorem kemShCrReal_keyInd1KeyKind_eq
    (Prim : Primitives) (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCrReal Prim ((pqxdhKeyInd1KeyKindCostedSims S).eval.shcr b A) =
      KemShCrReal Prim ((pqxdhKeyInd1KeyActiveCostedSims S).eval.shcr b A) := by
  unfold KemShCrReal
  rw [kemShCr_keyInd1KeyKind_eq Prim S b A]

/-- Transfers `KI1KeyActiveHopG0G3Stmt` from `pqxdhKeyInd1KeyActiveCostedSims` to
`pqxdhKeyInd1KeyKindCostedSims`. -/
theorem ki1KeyActiveHopG0G3_of_active (S : Setup)
    (hAct : KI1KeyActiveHopG0G3Stmt S
      (pqxdhKeyInd1KeyActiveCostedSims S).eval.sig
      (pqxdhKeyInd1KeyActiveCostedSims S).eval.shcr)
    (hSigEq : ∀ Prim b A,
      GapSigEufCmaReal Prim Prim.isValidDhTriple
        ((pqxdhKeyInd1KeyKindCostedSims S).eval.sig b A) =
      GapSigEufCmaReal Prim Prim.isValidDhTriple
        ((pqxdhKeyInd1KeyActiveCostedSims S).eval.sig b A)) :
    KI1KeyActiveHopG0G3Stmt S
      (pqxdhKeyInd1KeyKindCostedSims S).eval.sig
      (pqxdhKeyInd1KeyKindCostedSims S).eval.shcr := by
  intro Prim hPrim b A
  have h := hAct Prim hPrim b A
  dsimp only at h ⊢
  rw [hSigEq Prim b A, kemShCrReal_keyInd1KeyKind_eq Prim S b A]
  exact h

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindShcrEq
