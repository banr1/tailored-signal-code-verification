/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.EvalDistEq
public import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Bijective Uniform Couplings and Marginal Splitting

Uniform-sampling equivalences (`=ᵈ` and `𝒟[·]` equalities) along bijections, product and marginal
projections, `List.Vector` / `BitVec` tape splits, and uniform `Bool` symmetries.
-/

set_option autoImplicit false

@[expose] public section

namespace Computational.Proofs.GameHop.Rnd

open OracleSpec OracleComp
open scoped ENNReal
open MeasureTheory (Measure lintegral_congr)
open ProbabilityTheory (uniformOn map_uniformOn_univ_of_bijective)
open OracleComp.ProgramLogic (wp wp_map wp_congr_evalDist)

section SupportBind

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} [OracleSpec.AnswerMeasure spec]

theorem evalDistEq_bind_right_of_mem_support {α β : Type}
    (mx : OracleComp spec α) {f g : α → OracleComp spec β}
    (hfg : ∀ a ∈ support mx, f a =ᵈ g a) :
    mx >>= f =ᵈ mx >>= g := by
  classical
  let f' : α → OracleComp spec β := fun a => if a ∈ support mx then f a else g a
  have h1 : mx >>= f = mx >>= f' :=
    bind_congr_of_forall_mem_support mx fun a ha => by
      dsimp only [f']; simp only [ha, ↓reduceIte]
  rw [h1]
  refine EvalDistEq.bind_right mx fun a => ?_
  by_cases ha : a ∈ support mx
  · dsimp only [f']; simp only [ha, ↓reduceIte]; exact hfg a ha
  · dsimp only [f']; simp only [ha, ↓reduceIte]; exact EvalDistEq.rfl

theorem evalDist_bind_congr_of_mem_support {α β : Type} [MeasurableSpace β]
    (mx : ProbComp α) (f g : α → ProbComp β)
    (hfg : ∀ a ∈ support mx, 𝒟[f a] = 𝒟[g a]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  classical
  let f' : α → ProbComp β := fun a => if a ∈ support mx then f a else g a
  have h1 : mx >>= f = mx >>= f' :=
    bind_congr_of_forall_mem_support mx fun a ha => by
      dsimp only [f']; simp only [ha, ↓reduceIte]
  rw [h1]
  refine evalDist_bind_congr mx f' g fun a => ?_
  by_cases ha : a ∈ support mx
  · dsimp only [f']; simp only [ha, ↓reduceIte]; exact hfg a ha
  · dsimp only [f']; simp only [ha, ↓reduceIte]

end SupportBind

section BijectiveUniform

variable {α β γ δ : Type} [SampleableType α] [SampleableType β]

/-- Mapping `$ᵗ α` through a bijection `f : α → β` yields `$ᵗ β` in distribution. -/
theorem evalDistEq_uniformSample_of_bijective {f : α → β} (hf : Function.Bijective f) :
    f <$> ($ᵗ α : ProbComp α) =ᵈ ($ᵗ β : ProbComp β) :=
  SampleableType.map_uniformSample_evalDistEq_of_bijective hf

theorem evalDistEq_uniformSample_return_of_bijective {f : α → β} (hf : Function.Bijective f) :
    (do let a ← ($ᵗ α : ProbComp α); pure (f a)) =ᵈ ($ᵗ β : ProbComp β) := by
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    SampleableType.map_uniformSample_evalDistEq_of_bijective hf

theorem evalDistEq_uniformSample_equiv (e : α ≃ β) :
    e <$> ($ᵗ α : ProbComp α) =ᵈ ($ᵗ β : ProbComp β) :=
  SampleableType.map_uniformSample_evalDistEq_of_bijective e.bijective

theorem evalDistEq_uniformSample_bind_of_bijective {f : α → β} (hf : Function.Bijective f)
    (k : β → ProbComp δ) :
    (do let a ← ($ᵗ α : ProbComp α); k (f a)) =ᵈ
      (do let b ← ($ᵗ β : ProbComp β); k b) := by
  have h := (evalDistEq_uniformSample_of_bijective hf).bind_left k
  simpa only [bind_map_left, Function.comp_def] using h

theorem evalDist_uniformSample_bind_of_bijective [MeasurableSpace δ]
    {f : α → β} (hf : Function.Bijective f) (k : β → ProbComp δ) :
    𝒟[do let a ← ($ᵗ α : ProbComp α); k (f a)] =
      𝒟[do let b ← ($ᵗ β : ProbComp β); k b] :=
  (evalDistEq_uniformSample_bind_of_bijective hf k).evalDist_eq

theorem wp_uniformSample_equiv (e : α ≃ β) (post : β → ℝ≥0∞) :
    wp ($ᵗ α : ProbComp α) (fun x => post (e x)) = wp ($ᵗ β : ProbComp β) post := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have hmap := wp_map e ($ᵗ α : ProbComp α) post
  dsimp only [Function.comp_def] at hmap
  rw [← hmap]
  refine wp_congr_evalDist ?_ post Measurable.of_discrete
  exact (evalDistEq_uniformSample_equiv e).evalDist_eq

theorem evalDistEq_uniformSample_pair_of_bijective [SampleableType γ]
    {g : α → β → γ} (hg : Function.Bijective (Function.uncurry g)) :
    (do let a ← ($ᵗ α : ProbComp α); let b ← ($ᵗ β : ProbComp β); pure (g a b)) =ᵈ
      ($ᵗ γ : ProbComp γ) :=
  EvalDistEq.of_forall_prEvent_eq fun p => by
    simpa only [prEvent_norm] using SampleableType.prEvent_uniformSample_pair_of_bijective hg p

theorem evalDistEq_uniformSample_prod :
    ($ᵗ (α × β) : ProbComp (α × β)) =ᵈ
      (do let a ← ($ᵗ α : ProbComp α); let b ← ($ᵗ β : ProbComp β); pure (a, b)) :=
  (evalDistEq_uniformSample_pair_of_bijective (g := Prod.mk) Function.bijective_id).symm

/-- First-component marginal of `$ᵗ γ` under a bijection `g : γ → α × β` equals `$ᵗ α`. -/
theorem evalDistEq_marginal_fst_of_bijective [SampleableType γ]
    {g : γ → α × β} (hg : Function.Bijective g) :
    (fun z => (g z).1) <$> ($ᵗ γ : ProbComp γ) =ᵈ ($ᵗ α : ProbComp α) := by
  have h1 : (fun z => (g z).1) <$> ($ᵗ γ : ProbComp γ) = Prod.fst <$> (g <$> ($ᵗ γ : ProbComp γ)) := by
    rw [Functor.map_map]
  rw [h1]
  refine ((evalDistEq_uniformSample_of_bijective hg).map Prod.fst).trans ?_
  exact EvalDistEq.of_forall_prEvent_eq fun p => by
    rw [prEvent_map]
    exact SampleableType.prEvent_uniformSample_fst p

theorem evalDistEq_marginal_snd_of_bijective [SampleableType γ]
    {g : γ → α × β} (hg : Function.Bijective g) :
    (fun z => (g z).2) <$> ($ᵗ γ : ProbComp γ) =ᵈ ($ᵗ β : ProbComp β) := by
  have hswap : Function.Bijective (fun z => Prod.swap (g z)) :=
    (Equiv.prodComm α β).bijective.comp hg
  exact evalDistEq_marginal_fst_of_bijective hswap

theorem evalDistEq_marginal_fst_bind_of_bijective [SampleableType γ]
    {g : γ → α × β} (hg : Function.Bijective g) (k : α → ProbComp δ) :
    (do let z ← ($ᵗ γ : ProbComp γ); k (g z).1) =ᵈ
      (do let a ← ($ᵗ α : ProbComp α); k a) := by
  have h := (evalDistEq_marginal_fst_of_bijective hg).bind_left k
  simpa only [bind_map_left, Function.comp_def] using h

theorem evalDistEq_marginal_snd_bind_of_bijective [SampleableType γ]
    {g : γ → α × β} (hg : Function.Bijective g) (k : β → ProbComp δ) :
    (do let z ← ($ᵗ γ : ProbComp γ); k (g z).2) =ᵈ
      (do let b ← ($ᵗ β : ProbComp β); k b) := by
  have h := (evalDistEq_marginal_snd_of_bijective hg).bind_left k
  simpa only [bind_map_left, Function.comp_def] using h

end BijectiveUniform

section StructuredTapes

/-- Equivalence splitting `List.Vector α (m + n)` into `List.Vector α m × List.Vector α n`. -/
def equivVectorSplit (α : Type) (m n : ℕ) :
    List.Vector α (m + n) ≃ List.Vector α m × List.Vector α n where
  toFun v :=
    (List.Vector.ofFn (fun i : Fin m => v.get ⟨i.val, by omega⟩),
     List.Vector.ofFn (fun j : Fin n => v.get ⟨m + j.val, by omega⟩))
  invFun p :=
    List.Vector.ofFn (fun k : Fin (m + n) =>
      if h : k.val < m then p.1.get ⟨k.val, h⟩
      else p.2.get ⟨k.val - m, by omega⟩)
  left_inv v := by
    apply List.Vector.ext; intro k
    simp only [List.Vector.get_ofFn]
    split_ifs with h
    · rfl
    · congr 1; ext; dsimp only; omega
  right_inv := fun ⟨v₁, v₂⟩ => by
    ext : 1
    · apply List.Vector.ext; intro i
      simp only [List.Vector.get_ofFn, i.isLt, ↓reduceDIte]
    · apply List.Vector.ext; intro j
      have hnot : ¬ (m + j.val < m) := by omega
      have hsub : m + j.val - m = j.val := by omega
      simp only [List.Vector.get_ofFn, hnot, ↓reduceDIte]
      congr 1; ext; exact hsub

theorem evalDistEq_uniformSample_vector_split {α : Type} [SampleableType α] (m n : ℕ) :
    equivVectorSplit α m n <$> ($ᵗ List.Vector α (m + n) : ProbComp _) =ᵈ
      (do
        let v₁ ← ($ᵗ List.Vector α m : ProbComp _)
        let v₂ ← ($ᵗ List.Vector α n : ProbComp _)
        pure (v₁, v₂)) :=
  (evalDistEq_uniformSample_equiv (equivVectorSplit α m n)).trans evalDistEq_uniformSample_prod

/-- Equivalence splitting `BitVec (m + n)` into its high `m` bits and low `n` bits. -/
def equivBitVecSplit (m n : ℕ) : BitVec (m + n) ≃ BitVec m × BitVec n where
  toFun w := (w.extractLsb' n m, w.extractLsb' 0 n)
  invFun p := p.1 ++ p.2
  left_inv w := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    split_ifs with h
    · simp [h]
    · have hle : n ≤ i := Nat.not_lt.mp h
      have hlt : i - n < m := by omega
      simp [hlt, Nat.add_sub_of_le hle]
  right_inv := fun ⟨hi, lo⟩ => by
    ext : 1
    · apply BitVec.eq_of_getLsbD_eq; intro i hlt
      have hnot : ¬ (n + i < n) := by omega
      simp [BitVec.getLsbD_append, hlt, hnot]
    · apply BitVec.eq_of_getLsbD_eq; intro i hlt
      simp [BitVec.getLsbD_append, hlt]

theorem evalDistEq_uniformSample_bitVec_split (m n : ℕ) :
    equivBitVecSplit m n <$> ($ᵗ BitVec (m + n) : ProbComp _) =ᵈ
      (do
        let hi ← ($ᵗ BitVec m : ProbComp _)
        let lo ← ($ᵗ BitVec n : ProbComp _)
        pure (hi, lo)) :=
  (evalDistEq_uniformSample_equiv (equivBitVecSplit m n)).trans evalDistEq_uniformSample_prod

end StructuredTapes

section UniformBool

theorem evalDistEq_uniformBool_not :
    Bool.not <$> ($ᵗ Bool : ProbComp Bool) =ᵈ ($ᵗ Bool : ProbComp Bool) :=
  evalDistEq_uniformSample_of_bijective
    (Function.bijective_iff_has_inverse.mpr ⟨Bool.not, Bool.not_not, Bool.not_not⟩)

theorem evalDistEq_uniformBool_xor (c : Bool) :
    (fun b => xor b c) <$> ($ᵗ Bool : ProbComp Bool) =ᵈ ($ᵗ Bool : ProbComp Bool) := by
  refine evalDistEq_uniformSample_of_bijective ?_
  exact Function.bijective_iff_has_inverse.mpr
    ⟨fun b => xor b c, fun b => by cases b <;> cases c <;> rfl,
      fun b => by cases b <;> cases c <;> rfl⟩

theorem evalDistEq_uniformBool_beq (c : Bool) :
    (fun b => b == c) <$> ($ᵗ Bool : ProbComp Bool) =ᵈ ($ᵗ Bool : ProbComp Bool) := by
  refine evalDistEq_uniformSample_of_bijective ?_
  exact Function.bijective_iff_has_inverse.mpr
    ⟨fun b => b == c, fun b => by cases b <;> cases c <;> rfl,
      fun b => by cases b <;> cases c <;> rfl⟩

theorem evalDist_select_swap {α : Type} [MeasurableSpace α] (x y : ProbComp α) :
    𝒟[do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then x else y] =
      𝒟[do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then y else x] := by
  rw [← ProbComp.evalDist_bind_not_uniformBool (fun sel => if sel then y else x)]
  refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun sel => ?_
  cases sel <;> rfl

theorem evalDist_uniformBool_ite_true (x y : ProbComp Bool) :
    𝒟[do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then x else y] {true} =
      (𝒟[x] {true} + 𝒟[y] {true}) / 2 := by
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply (measurableSet_singleton true) Measurable.of_discrete.aemeasurable,
    MeasureTheory.lintegral_fintype, Fintype.sum_bool]
  simp [div_eq_mul_inv, add_mul]

end UniformBool

end Computational.Proofs.GameHop.Rnd
