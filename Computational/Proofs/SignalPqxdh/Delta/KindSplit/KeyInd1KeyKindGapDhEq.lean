/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyDefs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimA

public section

set_option autoImplicit false

/-!
# Forgetful-Simulation Bridges for the One-Key KeyInd `gdh` Kind-Split Reduction

**Checked by Lean.**

Transfers the `ForgetSim` simulation between `fgKeyInd1KeyGapDhKindAtomicProg` and
`fgKeyInd1KeyGapDhActiveAtomicProg` to `CostedReduction.eval` equality, `GapDhWithSign` advantage
equality, `KI1KeyActiveG3BoundStmt`, and semantic query bounds on `pqxdhKeyInd1KeyKindCostedSims`.
-/

open OracleComp OracleSpec
open SignalPqxdh (Setup QueryBudget BoundedAdv KeyIndAdversary Primitives Bytes
  KeyIndQuery keyIndSpec isKeyIndOnlineQuery isKeyIndRoQuery isGameQuery
  GapDhWithSignAdv GapDhWithSign GapDhWithSignReal)
open SignalPqxdh.Costed (PB pqAtomicSig pqAtomicOps pqKeyIndCodec pqSigAndDdhIface)
open SignalPqxdh.Security (gdhQueryBudget gdhPrimQueryBudget KeyIndCostedReductionFamily)
open ReductionDsl (Ty CostedReduction)
open Computational.Proofs.ReductionDsl.StepSim (ForgetSim isGamePred instDecidablePredIsGamePred
  isQueryBoundP_min)
open Proofs.SignalPqxdh.Security.PqxdhDelta (KI1KeyActiveG3BoundStmt)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs
  (fgKeyInd1KeyGapDhActiveAtomicProg pqxdhKeyInd1KeyActiveCostedSims)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs
  (fgKeyInd1KeyGapDhKindAtomicProg pqxdhKeyInd1KeyKindCostedSims)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase
  (keyIndSimPred keyIndSimBounds instDecidablePredKeyIndSimPred)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimA
  (fgKeyInd1KeyGapDhKindAtomicProg_forgetSim)

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindGapDhEq

theorem pqxdhKeyInd1KeyKindCostedSims_gdh_eq (S : Setup) :
    (pqxdhKeyInd1KeyKindCostedSims S).gdh = fgKeyInd1KeyGapDhKindAtomicProg S :=
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

/-- Converts `BoundedAdv (KeyIndAdversary S) b` into the 3-slot `IsQueryBoundP` hypotheses for `keyIndSimPred`. -/
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

theorem fgKeyInd1KeyGapDhKindAtomicProg_eval_eq_of_forgetSim
    (S : Setup) (b : QueryBudget)
    {forget : (fgKeyInd1KeyGapDhKindAtomicProg S b).σ.denote →
      (fgKeyInd1KeyGapDhActiveAtomicProg S b).σ.denote}
    {m : Nat} {P : Fin m → KeyIndQuery S → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → Nat}
    {Inv : (Fin m → Nat) → (fgKeyInd1KeyGapDhKindAtomicProg S b).σ.denote → Prop}
    (hSim : ∀ uv : ((.prod (PB 32) (PB 32)) : Ty pqAtomicSig).denote,
      ForgetSim (fgKeyInd1KeyGapDhKindAtomicProg S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b)
        forget P B uv Inv)
    (A : BoundedAdv (KeyIndAdversary S) b)
    (hA : ∀ (_ : Unit) (j : Fin m),
      A.1.run.IsQueryBoundP (isGamePred (G := keyIndSpec S) (P j)) (B j))
    (uv : Bytes × Bytes) :
    (fgKeyInd1KeyGapDhKindAtomicProg S b).eval (fun _ => A.1.run) uv =
      (fgKeyInd1KeyGapDhActiveAtomicProg S b).eval (fun _ => A.1.run) uv :=
  (hSim uv).eval_eq (fun _ => A.1.run) hA

theorem fgKeyInd1KeyGapDhKindAtomicProg_eval_eq
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) (uv : Bytes × Bytes) :
    (fgKeyInd1KeyGapDhKindAtomicProg S b).eval (fun _ => A.1.run) uv =
      (fgKeyInd1KeyGapDhActiveAtomicProg S b).eval (fun _ => A.1.run) uv :=
  fgKeyInd1KeyGapDhKindAtomicProg_eval_eq_of_forgetSim S b
    (fgKeyInd1KeyGapDhKindAtomicProg_forgetSim S b) A
    (boundedAdv_isQueryBoundP_keyInd S b A) uv

/-- Equality of the evaluated `GapDhWithSignAdv` adversaries between the kind-split and active-count `gdh` reductions. -/
theorem pqxdhKeyInd1KeyKindCostedSims_eval_gdh_eq
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    (pqxdhKeyInd1KeyKindCostedSims S).eval.gdh b A =
      (pqxdhKeyInd1KeyActiveCostedSims S).eval.gdh b A :=
  congrArg (fun r =>
    ({ run := r, q_ddh := gdhQueryBudget S b, q_sig := 2 * min S.N_spk_tot S.N_recv,
       q_prim := gdhPrimQueryBudget S b } : GapDhWithSignAdv))
    (funext fun U => funext fun V => fgKeyInd1KeyGapDhKindAtomicProg_eval_eq S b A (U, V))

theorem gapDhWithSign_keyInd1KeyKind_eq
    (Prim : Primitives) (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapDhWithSign Prim Prim.isValidDhTriple Prim.pow8
        ((pqxdhKeyInd1KeyKindCostedSims S).eval.gdh b A) =
      GapDhWithSign Prim Prim.isValidDhTriple Prim.pow8
        ((pqxdhKeyInd1KeyActiveCostedSims S).eval.gdh b A) := by
  rw [pqxdhKeyInd1KeyKindCostedSims_eval_gdh_eq S b A]

theorem gapDhWithSignReal_keyInd1KeyKind_eq
    (Prim : Primitives) (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapDhWithSignReal Prim Prim.isValidDhTriple Prim.pow8
        ((pqxdhKeyInd1KeyKindCostedSims S).eval.gdh b A) =
      GapDhWithSignReal Prim Prim.isValidDhTriple Prim.pow8
        ((pqxdhKeyInd1KeyActiveCostedSims S).eval.gdh b A) := by
  rw [pqxdhKeyInd1KeyKindCostedSims_eval_gdh_eq S b A]

/-- Transfers `KI1KeyActiveG3BoundStmt` from `pqxdhKeyInd1KeyActiveCostedSims` to `pqxdhKeyInd1KeyKindCostedSims`. -/
theorem ki1KeyActiveG3Bound_of_active (S : Setup)
    (hAct : KI1KeyActiveG3BoundStmt S (pqxdhKeyInd1KeyActiveCostedSims S).eval.gdh) :
    KI1KeyActiveG3BoundStmt S (pqxdhKeyInd1KeyKindCostedSims S).eval.gdh := by
  intro Prim hPrim δ hδ b A
  have h := hAct Prim hPrim δ hδ b A
  dsimp only at h ⊢
  rw [gapDhWithSignReal_keyInd1KeyKind_eq Prim S b A]
  exact h

/-- Transfers semantic query compliance for `gdh` from `pqxdhKeyInd1KeyActiveCostedSims` to `pqxdhKeyInd1KeyKindCostedSims`. -/
theorem pqxdhKeyInd1KeyKindCostedSims_gdh_bounded
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (hAct : ((pqxdhKeyInd1KeyActiveCostedSims S).eval.gdh b A).Bounded) :
    ((pqxdhKeyInd1KeyKindCostedSims S).eval.gdh b A).Bounded := by
  rw [pqxdhKeyInd1KeyKindCostedSims_eval_gdh_eq S b A]
  exact hAct

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindGapDhEq
