/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.XeddsaRom.Statements
public import Computational.Proofs.SignalPqxdh.XeddsaRom.HvzkSim
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Reductions from `GapDhWithSignRo` to standalone `GapDH`

**Checked by Lean.** Combines the HVZK signing simulation bound (`gapDhWithSignRo_le_sim`) with two
black-box `GapDH` reductions: `gapDhAdv1A` guesses the Edwards public-key sign bit uniformly in one
run (`GapDhWithSignRoBound1A`), and `gapDhAdv1B` checks its first candidate against `ddhOracle`
before a fallback second run to eliminate the factor-2 sign-bit loss (`GapDhWithSignRoBound1B`).
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.XeddsaRom.GapDhWithSignReduction

open MeasureTheory (Measure IsProbabilityMeasure lintegral_const_mul lintegral_mono)
open scoped ENNReal
open OracleComp OracleSpec
open scoped OracleSpec.PrimitiveQuery
open _root_.SignalPqxdh (
  Bytes Primitives PrimQuery primSpec primImpl PrimBaseSpec primBaseImpl isPrimQuery
  DdhQuery gapDhOracleSpec SigQuery sigOracleSpec
  GapDhAdv gapDhExp GapDH WellFormedPrimitivesδ
  sampleScalar32
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519 (
  clampedScalarZMod
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.Statements (
  sha512RoSpec Sha512RoComp sha512RoImpl
  xeddsaSignRo xeddsaVerifyRo primRoStep primRoImpl primBaseRoImpl
  XeddsaRomOracleSpec isRomPrimQuery isRomDdhChalQuery
  GapDhWithSignRoAdv GapDhWithSignRo
  XeddsaCurveWitness XeddsaCurveLaws
  xeddsaChalBudget xeddsaSimLoss
  GapDhWithSignRoBound1A GapDhWithSignRoBound1B
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.HvzkSim (
  xeddsaSimSign gapDhWithSignSimRun gapDhWithSignSimExpAt gapDhWithSignSimExp
  gapDhWithSignRo_le_sim
)

/-! ## Embedding simulated signing into `GapDhAdv` -/

def liftProbToGapDh {α : Type} (mx : ProbComp α) :
    OracleComp (PrimBaseSpec + gapDhOracleSpec) α :=
  simulateQ (fun k => liftM ((PrimBaseSpec + gapDhOracleSpec).query (.inl (.inl k)))) mx

private theorem simulateQ_liftProbToGapDh {α : Type} (P : Primitives)
    (ddhImpl : QueryImpl gapDhOracleSpec ProbComp) (mx : ProbComp α) :
    simulateQ (primBaseImpl P + ddhImpl) (liftProbToGapDh mx) = mx := by
  unfold liftProbToGapDh
  induction mx using OracleComp.inductionOn with
  | pure a =>
      simp [simulateQ_pure]
  | query_bind k cont ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, QueryImpl.add_apply_inl, primBaseImpl,
        QueryImpl.ofLift_apply]
      congr 1
      funext u
      exact ih u

private theorem isQueryBoundP_ddh_liftProbToGapDh {α : Type} (mx : ProbComp α) :
    (liftProbToGapDh mx).IsQueryBoundP (fun q => q.isRight = true) 0 := by
  unfold liftProbToGapDh
  induction mx using OracleComp.inductionOn with
  | pure a =>
      simp [simulateQ_pure]
  | query_bind k cont ih =>
      rw [simulateQ_bind]
      have hq :
          (liftM ((PrimBaseSpec + gapDhOracleSpec).query (.inl (.inl k))) :
            OracleComp (PrimBaseSpec + gapDhOracleSpec) (Fin (k + 1))).IsQueryBoundP
            (fun q => q.isRight = true) 0 := by
        rw [isQueryBoundP_query_iff]
        intro hp
        simp at hp
      simpa only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        Nat.zero_add] using isQueryBoundP_bind hq (fun u _ => ih u)

private theorem isQueryBoundP_prim_liftProbToGapDh {α : Type} (mx : ProbComp α) :
    (liftProbToGapDh mx).IsQueryBoundP (fun q => isPrimQuery q = true) 0 := by
  unfold liftProbToGapDh
  induction mx using OracleComp.inductionOn with
  | pure a =>
      simp [simulateQ_pure]
  | query_bind k cont ih =>
      rw [simulateQ_bind]
      have hq :
          (liftM ((PrimBaseSpec + gapDhOracleSpec).query (.inl (.inl k))) :
            OracleComp (PrimBaseSpec + gapDhOracleSpec) (Fin (k + 1))).IsQueryBoundP
            (fun q => isPrimQuery q = true) 0 := by
        rw [isQueryBoundP_query_iff]
        intro hp
        simp [isPrimQuery] at hp
      simpa only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        Nat.zero_add] using isQueryBoundP_bind hq (fun u _ => ih u)

def primStepInGapDh (P : Primitives) :
    QueryImpl primSpec
      (StateT sha512RoSpec.QueryCache (OracleComp (PrimBaseSpec + gapDhOracleSpec))) := fun
  | .sigSign sk m r => StateT.mk fun c =>
      liftProbToGapDh ((simulateQ sha512RoImpl (xeddsaSignRo P sk m r)).run c)
  | .sigVerify pk m sg => StateT.mk fun c =>
      liftProbToGapDh ((simulateQ sha512RoImpl (xeddsaVerifyRo P pk m sg)).run c)
  | pq => StateT.mk fun c =>
      (fun v => (v, c)) <$>
        (liftM ((PrimBaseSpec + gapDhOracleSpec).query (.inl (.inr pq))) :
          OracleComp (PrimBaseSpec + gapDhOracleSpec) (primSpec.Range pq))

private theorem simulateQ_primStepInGapDh_run (P : Primitives)
    (ddhImpl : QueryImpl gapDhOracleSpec ProbComp)
    (pq : PrimQuery) (c : sha512RoSpec.QueryCache) :
    simulateQ (primBaseImpl P + ddhImpl) ((primStepInGapDh P pq).run c) =
      (primRoImpl P pq).run c := by
  cases pq <;>
    first
    | exact simulateQ_liftProbToGapDh P ddhImpl _
    | simp [primStepInGapDh, primRoImpl, primRoStep, simulateQ_map, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, primBaseImpl, primImpl]

private theorem isQueryBoundP_ddh_primStepInGapDh (P : Primitives)
    (pq : PrimQuery) (c : sha512RoSpec.QueryCache) :
    ((primStepInGapDh P pq).run c).IsQueryBoundP (fun q => q.isRight = true) 0 := by
  cases pq <;>
    first
    | exact isQueryBoundP_ddh_liftProbToGapDh _
    | (dsimp only [primStepInGapDh, StateT.run, StateT.mk]
       rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
       intro hp; simp at hp)

private theorem isQueryBoundP_prim_primStepInGapDh (P : Primitives)
    (pq : PrimQuery) (c : sha512RoSpec.QueryCache) :
    ((primStepInGapDh P pq).run c).IsQueryBoundP (fun q => isPrimQuery q = true) 1 := by
  cases pq <;>
    first
    | exact (isQueryBoundP_prim_liftProbToGapDh _).mono (Nat.zero_le 1)
    | (dsimp only [primStepInGapDh, StateT.run, StateT.mk]
       rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
       intro _; exact Nat.zero_lt_one)

/-- `XeddsaRomOracleSpec` handler inside `GapDhAdv` simulating XEdDSA signing at candidate sign bit
`bSim` while forwarding DDH and non-XEdDSA primitive queries to the challenger. -/
noncomputable def simStep (P : Primitives) (U : Bytes) (bSim : UInt8) :
    QueryImpl XeddsaRomOracleSpec
      (StateT sha512RoSpec.QueryCache (OracleComp (PrimBaseSpec + gapDhOracleSpec)))
  | .inl (.inl (.inl k)) => StateT.mk fun c =>
      (fun u => (u, c)) <$>
        (liftM ((PrimBaseSpec + gapDhOracleSpec).query (.inl (.inl k))) :
          OracleComp (PrimBaseSpec + gapDhOracleSpec) (Fin (k + 1)))
  | .inl (.inl (.inr pq)) => primStepInGapDh P pq
  | .inl (.inr bs) => StateT.mk fun c =>
      liftProbToGapDh ((sha512RoImpl bs).run c)
  | .inr (.inl (.sign m)) => StateT.mk fun c =>
      liftProbToGapDh ((xeddsaSimSign P U bSim m).run c)
  | .inr (.inr dq) => StateT.mk fun c =>
      (fun b => (b, c)) <$>
        (liftM ((PrimBaseSpec + gapDhOracleSpec).query (.inr dq)) :
          OracleComp (PrimBaseSpec + gapDhOracleSpec) Bool)

private theorem simulateQ_simStep_run (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (U : Bytes) (bSim : UInt8)
    (q : XeddsaRomOracleSpec.Domain) (c : sha512RoSpec.QueryCache) :
    let ddhImpl : QueryImpl gapDhOracleSpec ProbComp := fun (X, Y, Z) =>
      pure (isValidDhTriple X Y Z)
    let sigRo : QueryImpl sigOracleSpec Sha512RoComp := fun (.sign m) =>
      xeddsaSimSign P U bSim m
    let ddhRo : QueryImpl gapDhOracleSpec Sha512RoComp := fun (X, Y, Z) =>
      pure (isValidDhTriple X Y Z)
    simulateQ (primBaseImpl P + ddhImpl) ((simStep P U bSim q).run c) =
      ((primBaseRoImpl P + (sigRo + ddhRo)) q).run c := by
  dsimp only
  rcases q with (((k | pq) | bs) | (⟨m⟩ | ⟨X, Y, Z⟩))
  · simp [simStep, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, primBaseImpl, primBaseRoImpl,
      QueryImpl.ofLift_apply, StateT.run_monadLift, map_eq_bind_pure_comp]
  · simp only [simStep, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, primBaseRoImpl]
    exact simulateQ_primStepInGapDh_run P _ pq c
  · simp [simStep, simulateQ_liftProbToGapDh, primBaseRoImpl]
  · simp [simStep, simulateQ_liftProbToGapDh]
  · simp [simStep, simulateQ_map, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query]

private theorem simulateQ_simStep_oa {α : Type} (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (U : Bytes) (bSim : UInt8)
    (oa : OracleComp XeddsaRomOracleSpec α) (c : sha512RoSpec.QueryCache) :
    let ddhImpl : QueryImpl gapDhOracleSpec ProbComp := fun (X, Y, Z) =>
      pure (isValidDhTriple X Y Z)
    let sigRo : QueryImpl sigOracleSpec Sha512RoComp := fun (.sign m) =>
      xeddsaSimSign P U bSim m
    let ddhRo : QueryImpl gapDhOracleSpec Sha512RoComp := fun (X, Y, Z) =>
      pure (isValidDhTriple X Y Z)
    simulateQ (primBaseImpl P + ddhImpl) ((simulateQ (simStep P U bSim) oa).run c) =
      (simulateQ (primBaseRoImpl P + (sigRo + ddhRo)) oa).run c := by
  let ddhImpl : QueryImpl gapDhOracleSpec ProbComp := fun (X, Y, Z) =>
    pure (isValidDhTriple X Y Z)
  let sigRo : QueryImpl sigOracleSpec Sha512RoComp := fun (.sign m) =>
    xeddsaSimSign P U bSim m
  let ddhRo : QueryImpl gapDhOracleSpec Sha512RoComp := fun (X, Y, Z) =>
    pure (isValidDhTriple X Y Z)
  change simulateQ (primBaseImpl P + ddhImpl) ((simulateQ (simStep P U bSim) oa).run c) =
    (simulateQ (primBaseRoImpl P + (sigRo + ddhRo)) oa).run c
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
      simp [simulateQ_pure]
  | query_bind q cont ih =>
      rw [simulateQ_query_bind, StateT.run_bind, simulateQ_bind,
        simulateQ_query_bind, StateT.run_bind]
      have hstep := simulateQ_simStep_run P isValidDhTriple U bSim q c
      dsimp only at hstep
      change (simulateQ (primBaseImpl P + ddhImpl) ((simStep P U bSim q).run c) >>= _) =
        (((primBaseRoImpl P + (sigRo + ddhRo)) q).run c >>= _)
      rw [hstep]
      congr 1
      funext p
      exact ih p.1 p.2

noncomputable def simRunInGapDh (P : Primitives) (A : GapDhWithSignRoAdv)
    (bSim : UInt8) (U V : Bytes) :
    OracleComp (PrimBaseSpec + gapDhOracleSpec) Bytes :=
  (simulateQ (simStep P U bSim) (A.run U V)).run' ∅

private theorem simulateQ_simRunInGapDh (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (A : GapDhWithSignRoAdv) (bSim : UInt8) (U V : Bytes) :
    let ddhImpl : QueryImpl gapDhOracleSpec ProbComp := fun (X, Y, Z) =>
      pure (isValidDhTriple X Y Z)
    simulateQ (primBaseImpl P + ddhImpl) (simRunInGapDh P A bSim U V) =
      gapDhWithSignSimRun P isValidDhTriple U V bSim A := by
  dsimp only
  unfold simRunInGapDh gapDhWithSignSimRun
  rw [StateT.run'_eq, StateT.run'_eq, simulateQ_map,
    simulateQ_simStep_oa P isValidDhTriple U bSim (A.run U V) ∅]

private theorem isQueryBoundP_ddh_simRunInGapDh (P : Primitives)
    {A : GapDhWithSignRoAdv} (hA : A.Bounded) (bSim : UInt8) (U V : Bytes) :
    (simRunInGapDh P A bSim U V).IsQueryBoundP (fun q => q.isRight = true) A.q_ddh := by
  unfold simRunInGapDh
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine (hA.1 U V).simulateQ_run_StateT_of_step (fun q c => ?_) ∅
  rcases q with (((k | pq) | bs) | (⟨m⟩ | dq))
  · simp only [simStep, StateT.run, StateT.mk, isRomDdhChalQuery, Bool.false_eq_true, ↓reduceIte,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    intro hp; simp at hp
  · simp only [simStep, isRomDdhChalQuery, Bool.false_eq_true, ↓reduceIte]
    exact isQueryBoundP_ddh_primStepInGapDh P pq c
  · simp only [simStep, StateT.run, StateT.mk, isRomDdhChalQuery, Bool.false_eq_true, ↓reduceIte]
    exact isQueryBoundP_ddh_liftProbToGapDh _
  · simp only [simStep, StateT.run, StateT.mk, isRomDdhChalQuery, Bool.false_eq_true, ↓reduceIte]
    exact isQueryBoundP_ddh_liftProbToGapDh _
  · simp only [simStep, StateT.run, StateT.mk, isRomDdhChalQuery, ↓reduceIte,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    intro _; exact Nat.zero_lt_one

private theorem isQueryBoundP_prim_simRunInGapDh (P : Primitives)
    {A : GapDhWithSignRoAdv} (hA : A.Bounded) (bSim : UInt8) (U V : Bytes) :
    (simRunInGapDh P A bSim U V).IsQueryBoundP (fun q => isPrimQuery q = true) A.q_prim := by
  unfold simRunInGapDh
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine (hA.2.2.1 U V).simulateQ_run_StateT_of_step (fun q c => ?_) ∅
  rcases q with (((k | pq) | bs) | (⟨m⟩ | dq))
  · simp only [simStep, StateT.run, StateT.mk, isRomPrimQuery, Bool.false_eq_true, ↓reduceIte,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    intro hp; simp [isPrimQuery] at hp
  · simp only [simStep, isRomPrimQuery, ↓reduceIte]
    exact isQueryBoundP_prim_primStepInGapDh P pq c
  · simp only [simStep, StateT.run, StateT.mk, isRomPrimQuery, Bool.false_eq_true, ↓reduceIte]
    exact isQueryBoundP_prim_liftProbToGapDh _
  · simp only [simStep, StateT.run, StateT.mk, isRomPrimQuery, Bool.false_eq_true, ↓reduceIte]
    exact isQueryBoundP_prim_liftProbToGapDh _
  · simp only [simStep, StateT.run, StateT.mk, isRomPrimQuery, Bool.false_eq_true, ↓reduceIte,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    intro hp; simp [isPrimQuery] at hp

private noncomputable def gapDhExpAt (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (u v : Bytes) (B : GapDhAdv) : ProbComp Bool := do
  let U := P.x25519Base u
  let V := P.x25519Base v
  let ddhImpl : QueryImpl gapDhOracleSpec ProbComp := fun (X, Y, Z) =>
    pure (isValidDhTriple X Y Z)
  let Z ← simulateQ (primBaseImpl P + ddhImpl) (B.run U V)
  return (pow8 Z == pow8 (P.x25519 u V))

private theorem evalDist_bind_true_le_const_mul {α : Type}
    (mx : ProbComp α) (f g : α → ProbComp Bool) (c : ℝ≥0∞)
    (hfg : ∀ a, 𝒟[f a] {true} ≤ c * 𝒟[g a] {true}) :
    𝒟[mx >>= f] {true} ≤ c * 𝒟[mx >>= g] {true} := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace Bool := ⊤
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
    evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
    ← lintegral_const_mul c Measurable.of_discrete]
  exact lintegral_mono hfg

/-! ## Single-run reduction (`GapDhWithSignRoBound1A`) -/

/-- Single-run `GapDH` adversary that samples a uniform sign-bit guess for `simRunInGapDh`. -/
noncomputable def gapDhAdv1A (P : Primitives) (A : GapDhWithSignRoAdv) : GapDhAdv where
  run U V := do
    let coin ← liftProbToGapDh ($ᵗ Bool)
    simRunInGapDh P A (if coin then 1 else 0) U V
  q_ddh := A.q_ddh
  q_prim := A.q_prim

private theorem gapDhAdv1A_bounded (P : Primitives) {A : GapDhWithSignRoAdv} (hA : A.Bounded) :
    (gapDhAdv1A P A).Bounded := by
  refine ⟨fun U V => ?_, fun U V => ?_⟩
  · dsimp only [gapDhAdv1A]
    simpa only [Nat.zero_add] using
      isQueryBoundP_bind (isQueryBoundP_ddh_liftProbToGapDh ($ᵗ Bool))
        (fun coin _ => isQueryBoundP_ddh_simRunInGapDh P hA (if coin then 1 else 0) U V)
  · dsimp only [gapDhAdv1A]
    simpa only [Nat.zero_add] using
      isQueryBoundP_bind (isQueryBoundP_prim_liftProbToGapDh ($ᵗ Bool))
        (fun coin _ => isQueryBoundP_prim_simRunInGapDh P hA (if coin then 1 else 0) U V)

private theorem gapDhExpAt_adv1A (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (u v : Bytes) (A : GapDhWithSignRoAdv) :
    gapDhExpAt P isValidDhTriple pow8 u v (gapDhAdv1A P A) =
      (($ᵗ Bool) >>= fun coin =>
        gapDhWithSignSimExpAt P isValidDhTriple pow8 u v (if coin then 1 else 0) A) := by
  unfold gapDhExpAt gapDhAdv1A gapDhWithSignSimExpAt
  dsimp only
  rw [simulateQ_bind, simulateQ_liftProbToGapDh, bind_assoc]
  congr 1
  funext coin
  rw [simulateQ_simRunInGapDh]

private theorem simExpAt_le_two_mul_gapDhExpAt_adv1A (P : Primitives) (C : XeddsaCurveWitness P)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (u v : Bytes) (A : GapDhWithSignRoAdv) :
    𝒟[gapDhWithSignSimExpAt P isValidDhTriple pow8 u v
        (C.edSign (clampedScalarZMod u)) A] {true} ≤
      2 * 𝒟[gapDhExpAt P isValidDhTriple pow8 u v (gapDhAdv1A P A)] {true} := by
  let : MeasurableSpace Bool := ⊤
  let f : Bool → ProbComp Bool := fun coin =>
    gapDhWithSignSimExpAt P isValidDhTriple pow8 u v (if coin then 1 else 0) A
  rw [gapDhExpAt_adv1A, ← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
  have hsum :
      Pr{let y ← ($ᵗ Bool) >>= f}[y = true] =
        (2 : ℝ≥0∞)⁻¹ * Pr{let y ← f true}[y = true] +
          (2 : ℝ≥0∞)⁻¹ * Pr{let y ← f false}[y = true] := by
    rw [prEvent_bind_eq_sum_fintype ($ᵗ Bool) f (fun y => y = true), Fintype.sum_bool,
      SampleableType.prEvent_uniformSample_eq_singleton,
      SampleableType.prEvent_uniformSample_eq_singleton]
    simp [Fintype.card_bool]
  have htwo :
      2 * Pr{let y ← ($ᵗ Bool) >>= f}[y = true] =
        Pr{let y ← f true}[y = true] + Pr{let y ← f false}[y = true] := by
    rw [hsum, mul_add, ← mul_assoc, ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul, one_mul]
  change Pr{let y ← _}[y = true] ≤ 2 * Pr{let y ← ($ᵗ Bool) >>= f}[y = true]
  rw [htwo]
  rcases C.edSign_bool (clampedScalarZMod u) with h0 | h1
  · rw [h0]
    exact le_add_self
  · rw [h1]
    exact le_self_add

/-- Single-run `2×` reduction from `GapDhWithSignRo` to standalone `GapDH`. -/
theorem gapDhWithSignRoBound1A_holds : GapDhWithSignRoBound1A := by
  intro P hWF hCurve A hA
  obtain ⟨C⟩ := hCurve
  refine ⟨gapDhAdv1A P A, gapDhAdv1A_bounded P hA, le_rfl, le_rfl, ?_⟩
  have hsim := gapDhWithSignRo_le_sim P hWF C A hA
  have hdom_enn :
      𝒟[gapDhWithSignSimExp P C P.isValidDhTriple P.pow8 A] {true} ≤
        2 * 𝒟[gapDhExp P P.isValidDhTriple P.pow8 (gapDhAdv1A P A)] {true} :=
    evalDist_bind_true_le_const_mul sampleScalar32 _ _ 2 fun u =>
      evalDist_bind_true_le_const_mul sampleScalar32 _ _ 2 fun v =>
        simExpAt_le_two_mul_gapDhExpAt_adv1A P C P.isValidDhTriple P.pow8 u v A
  have hp_le_one :
      𝒟[gapDhExp P P.isValidDhTriple P.pow8 (gapDhAdv1A P A)] {true} ≤ 1 := by
    let : MeasurableSpace Bool := ⊤
    exact evalDist_apply_le_one _ _
  have hrhs_ne_top :
      2 * 𝒟[gapDhExp P P.isValidDhTriple P.pow8 (gapDhAdv1A P A)] {true} ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ne_top_of_le_ne_top ENNReal.one_ne_top hp_le_one)
  have hdom_real :
      (𝒟[gapDhWithSignSimExp P C P.isValidDhTriple P.pow8 A] {true}).toReal ≤
        2 * GapDH P P.isValidDhTriple P.pow8 (gapDhAdv1A P A) := by
    have hmono := ENNReal.toReal_mono hrhs_ne_top hdom_enn
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hmono
    exact hmono
  linarith

/-! ## Two-run DDH-checked reduction (`GapDhWithSignRoBound1B`) -/

/-- Two-run `GapDH` adversary that tests the `bSim = 0` candidate against `ddhOracle` before falling
back to `bSim = 1`. -/
noncomputable def gapDhAdv1B (P : Primitives) (A : GapDhWithSignRoAdv) : GapDhAdv where
  run U V := do
    let Z₀ ← simRunInGapDh P A 0 U V
    let ok ← liftM ((PrimBaseSpec + gapDhOracleSpec).query (.inr (U, V, Z₀)))
    if ok then return Z₀ else simRunInGapDh P A 1 U V
  q_ddh := 2 * A.q_ddh + 1
  q_prim := 2 * A.q_prim

private theorem gapDhAdv1B_bounded (P : Primitives) {A : GapDhWithSignRoAdv} (hA : A.Bounded) :
    (gapDhAdv1B P A).Bounded := by
  refine ⟨fun U V => ?_, fun U V => ?_⟩
  · dsimp only [gapDhAdv1B]
    have h0 := isQueryBoundP_ddh_simRunInGapDh P hA 0 U V
    have hrest : ∀ Z₀ : Bytes,
        ((liftM ((PrimBaseSpec + gapDhOracleSpec).query (.inr (U, V, Z₀))) :
            OracleComp (PrimBaseSpec + gapDhOracleSpec) Bool) >>= fun ok =>
          if ok then pure Z₀ else simRunInGapDh P A 1 U V).IsQueryBoundP
          (fun q => q.isRight = true) (1 + A.q_ddh) := fun Z₀ => by
      have hq :
          (liftM ((PrimBaseSpec + gapDhOracleSpec).query (.inr (U, V, Z₀))) :
            OracleComp (PrimBaseSpec + gapDhOracleSpec) Bool).IsQueryBoundP
            (fun q => q.isRight = true) 1 := by
        rw [isQueryBoundP_query_iff]
        intro _; exact Nat.zero_lt_one
      refine isQueryBoundP_bind hq (fun ok _ => ?_)
      cases ok
      · exact isQueryBoundP_ddh_simRunInGapDh P hA 1 U V
      · simp
    exact (isQueryBoundP_bind h0 (fun Z₀ _ => hrest Z₀)).mono (by omega)
  · dsimp only [gapDhAdv1B]
    have h0 := isQueryBoundP_prim_simRunInGapDh P hA 0 U V
    have hrest : ∀ Z₀ : Bytes,
        ((liftM ((PrimBaseSpec + gapDhOracleSpec).query (.inr (U, V, Z₀))) :
            OracleComp (PrimBaseSpec + gapDhOracleSpec) Bool) >>= fun ok =>
          if ok then pure Z₀ else simRunInGapDh P A 1 U V).IsQueryBoundP
          (fun q => isPrimQuery q = true) (0 + A.q_prim) := fun Z₀ => by
      have hq :
          (liftM ((PrimBaseSpec + gapDhOracleSpec).query (.inr (U, V, Z₀))) :
            OracleComp (PrimBaseSpec + gapDhOracleSpec) Bool).IsQueryBoundP
            (fun q => isPrimQuery q = true) 0 := by
        rw [isQueryBoundP_query_iff]
        intro hp; simp [isPrimQuery] at hp
      refine isQueryBoundP_bind hq (fun ok _ => ?_)
      cases ok
      · exact isQueryBoundP_prim_simRunInGapDh P hA 1 U V
      · simp
    exact (isQueryBoundP_bind h0 (fun Z₀ _ => hrest Z₀)).mono (by omega)

private theorem isValidDhTriple_eq_pow8_beq (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (u v Z : Bytes) :
    P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) Z =
      (P.pow8 Z == P.pow8 (P.x25519 u (P.x25519Base v))) := by
  cases h : P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) Z
  · symm
    rw [beq_eq_false_iff_ne]
    intro heq
    have htrue := (hWF.ddh_consistent u v Z).mpr heq
    rw [h] at htrue
    exact Bool.false_ne_true htrue
  · symm
    rw [beq_iff_eq]
    exact (hWF.ddh_consistent u v Z).mp h

private theorem gapDhExpAt_adv1B (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (u v : Bytes) (A : GapDhWithSignRoAdv) :
    gapDhExpAt P P.isValidDhTriple P.pow8 u v (gapDhAdv1B P A) =
      (gapDhWithSignSimRun P P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) 0 A >>= fun Z₀ =>
        if P.pow8 Z₀ == P.pow8 (P.x25519 u (P.x25519Base v)) then
          pure true
        else
          gapDhWithSignSimExpAt P P.isValidDhTriple P.pow8 u v 1 A) := by
  unfold gapDhExpAt gapDhAdv1B gapDhWithSignSimExpAt
  dsimp only
  rw [simulateQ_bind, simulateQ_simRunInGapDh, bind_assoc]
  congr 1
  funext Z₀
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, QueryImpl.add_apply_inr, pure_bind]
  rw [isValidDhTriple_eq_pow8_beq P hWF u v Z₀]
  cases hwin : (P.pow8 Z₀ == P.pow8 (P.x25519 u (P.x25519Base v)))
  · simp [simulateQ_simRunInGapDh]
  · simp [simulateQ_pure, hwin]

private theorem simExpAt_le_gapDhExpAt_adv1B (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (C : XeddsaCurveWitness P) (u v : Bytes) (A : GapDhWithSignRoAdv) :
    𝒟[gapDhWithSignSimExpAt P P.isValidDhTriple P.pow8 u v
        (C.edSign (clampedScalarZMod u)) A] {true} ≤
      𝒟[gapDhExpAt P P.isValidDhTriple P.pow8 u v (gapDhAdv1B P A)] {true} := by
  let : MeasurableSpace Bytes := ⊤
  let : MeasurableSpace Bool := ⊤
  set m₀ := gapDhWithSignSimRun P P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) 0 A
  set m₁ := gapDhWithSignSimExpAt P P.isValidDhTriple P.pow8 u v 1 A
  let k : Bytes → ProbComp Bool := fun Z₀ =>
    if P.pow8 Z₀ == P.pow8 (P.x25519 u (P.x25519Base v)) then pure true else m₁
  rw [gapDhExpAt_adv1B P hWF u v A]
  change 𝒟[_] {true} ≤ 𝒟[m₀ >>= k] {true}
  rcases C.edSign_bool (clampedScalarZMod u) with h0 | h1
  · rw [h0]
    unfold gapDhWithSignSimExpAt
    exact evalDist_bind_apply_mono_of_discrete m₀ _ k MeasurableSet.of_discrete fun Z₀ => by
      dsimp only [k]
      cases hwin : (P.pow8 Z₀ == P.pow8 (P.x25519 u (P.x25519Base v)))
      · simp
      · simp
  · rw [h1]
    have : IsProbabilityMeasure 𝒟[m₀] := ⟨evalDist_apply_univ_eq_one m₀⟩
    exact le_evalDist_bind_apply m₀ k Measurable.of_discrete MeasurableSet.of_discrete
      (Filter.Eventually.of_forall fun Z₀ => by
        dsimp only [k]
        cases hwin : (P.pow8 Z₀ == P.pow8 (P.x25519 u (P.x25519Base v)))
        · exact le_rfl
        · simp)

/-- Two-run DDH-checked `1×` reduction from `GapDhWithSignRo` to standalone `GapDH`. -/
theorem gapDhWithSignRoBound1B_holds : GapDhWithSignRoBound1B := by
  intro P hWF hCurve A hA
  obtain ⟨C⟩ := hCurve
  refine ⟨gapDhAdv1B P A, gapDhAdv1B_bounded P hA, le_rfl, le_rfl, ?_⟩
  have hsim := gapDhWithSignRo_le_sim P hWF C A hA
  have hdom_enn :
      𝒟[gapDhWithSignSimExp P C P.isValidDhTriple P.pow8 A] {true} ≤
        𝒟[gapDhExp P P.isValidDhTriple P.pow8 (gapDhAdv1B P A)] {true} := by
    let : MeasurableSpace Bytes := ⊤
    let : MeasurableSpace Bool := ⊤
    exact evalDist_bind_apply_mono_of_discrete sampleScalar32 _ _ MeasurableSet.of_discrete
      fun u => evalDist_bind_apply_mono_of_discrete sampleScalar32 _ _ MeasurableSet.of_discrete
        fun v => simExpAt_le_gapDhExpAt_adv1B P hWF C u v A
  have hp_le_one :
      𝒟[gapDhExp P P.isValidDhTriple P.pow8 (gapDhAdv1B P A)] {true} ≤ 1 := by
    let : MeasurableSpace Bool := ⊤
    exact evalDist_apply_le_one _ _
  have hdom_real :
      (𝒟[gapDhWithSignSimExp P C P.isValidDhTriple P.pow8 A] {true}).toReal ≤
        GapDH P P.isValidDhTriple P.pow8 (gapDhAdv1B P A) :=
    ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hp_le_one) hdom_enn
  linarith

end Computational.Proofs.SignalPqxdh.XeddsaRom.GapDhWithSignReduction
