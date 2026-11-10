/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCLazy
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtM
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Lazy
public import LibsignalBinary.Specifications.CryptoGames.Primitives
import VCVio.EvalDist.EvalDistEq
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.Measure

/-!
# Birthday Bound for One-Time AES-256-CBC IND-CPA

**Checked by Lean.**

Proves the collision bound `n(n - 1)/2 / 2^128` for `CBC.cbc_indcpa`: under a uniform random block
function, sequential CBC outputs are uniform unless two block-function inputs collide.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory
namespace CryptoGames.CBC.Bday

theorem uniform_prod (α β : Type) [SampleableType α] [SampleableType β] :
    ($ᵗ (α × β) : ProbComp (α × β)) =
      (do let a ← $ᵗ α; let b ← $ᵗ β; pure (a, b)) :=
  CryptoGames.AEADScheme.EtMProof.uniform_prod α β

private def unifVec : (n : ℕ) → ProbComp (List.Vector Block n)
  | 0 => pure List.Vector.nil
  | n + 1 => do
    let c ← $ᵗ Block
    let cs ← unifVec n
    pure (c ::ᵥ cs)

private theorem unifVec_evalDistEq :
    ∀ n : ℕ, EvalDistEq (unifVec n) ($ᵗ (List.Vector Block n))
  | 0 => by
    have hsub : ($ᵗ (List.Vector Block 0) : ProbComp _) =
        (fun _ => List.Vector.nil) <$> ($ᵗ (List.Vector Block 0)) := by
      have hid : (fun _ : List.Vector Block 0 => List.Vector.nil) = id := by
        funext v; exact Subsingleton.elim List.Vector.nil v
      simp [hid]
    rw [unifVec, hsub]
    exact (OracleComp.EvalDistEq.map_const _ List.Vector.nil).symm
  | n + 1 => by
    have hbij : Function.Bijective
        (fun p : Block × List.Vector Block n => p.1 ::ᵥ p.2) :=
      (Equiv.mk (fun p => p.1 ::ᵥ p.2) (fun v => (v.head, v.tail))
        (fun ⟨c, cs⟩ => by simp) (fun v => v.cons_head_tail)).bijective
    have h1 : EvalDistEq (unifVec (n + 1))
        (do let c ← $ᵗ Block; let cs ← $ᵗ (List.Vector Block n); pure (c ::ᵥ cs)) :=
      EvalDistEq.bind_right ($ᵗ Block) fun c =>
        EvalDistEq.bind_left (unifVec_evalDistEq n) fun cs => pure (c ::ᵥ cs)
    have h2 : (do let c ← $ᵗ Block; let cs ← $ᵗ (List.Vector Block n); pure (c ::ᵥ cs)) =
        (fun p : Block × List.Vector Block n => p.1 ::ᵥ p.2) <$>
          ($ᵗ (Block × List.Vector Block n)) := by
      rw [uniform_prod Block (List.Vector Block n)]
      simp [map_eq_bind_pure_comp, bind_assoc]
    rw [h2] at h1
    exact h1.trans (SampleableType.map_uniformSample_evalDistEq_of_bijective hbij)

private theorem lookup_ne_none_mem {y : Block} :
    ∀ {tbl : List (Block × Block)}, tbl.lookup y ≠ none → y ∈ tbl.map Prod.fst
  | [], h => absurd rfl h
  | (k, v) :: tl, h => by
    simp only [List.lookup, List.map_cons, List.mem_cons] at h ⊢
    rcases hk : (y == k) with _ | _
    · rw [hk] at h
      exact Or.inr (lookup_ne_none_mem h)
    · exact Or.inl (beq_iff_eq.mp hk)

private theorem xor_invol (a b : Block) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

private theorem measure_bad_le (p₀ x : Block) (tbl : List (Block × Block)) :
    letI : MeasurableSpace Block := ⊤
    𝒟[($ᵗ Block : ProbComp Block)]
      {c : Block | ((x, c) :: tbl).lookup (p₀ ^^^ c) ≠ none} ≤
      ((tbl.length + 1 : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
  let : MeasurableSpace Block := ⊤
  let S : Finset Block := ((x :: tbl.map Prod.fst).map (p₀ ^^^ ·)).toFinset
  have hsub : {c : Block | ((x, c) :: tbl).lookup (p₀ ^^^ c) ≠ none} ⊆
      ⋃ z ∈ S, ({z} : Set Block) := by
    intro c hc
    have hmem := lookup_ne_none_mem hc
    simp only [List.map_cons] at hmem
    have hcS : c ∈ S := by
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨p₀ ^^^ c, hmem, xor_invol p₀ c⟩
    exact Set.mem_biUnion hcS rfl
  have hcard : S.card ≤ tbl.length + 1 := by
    calc S.card
        ≤ ((x :: tbl.map Prod.fst).map (p₀ ^^^ ·)).length := List.toFinset_card_le _
      _ = tbl.length + 1 := by simp
  calc 𝒟[($ᵗ Block : ProbComp Block)]
        {c : Block | ((x, c) :: tbl).lookup (p₀ ^^^ c) ≠ none}
      ≤ 𝒟[($ᵗ Block : ProbComp Block)] (⋃ z ∈ S, ({z} : Set Block)) := measure_mono hsub
    _ ≤ ∑ z ∈ S, 𝒟[($ᵗ Block : ProbComp Block)] {z} := measure_biUnion_finset_le S _
    _ = ∑ _z ∈ S, ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_bitVec]
        norm_num
    _ = (S.card : ℝ≥0∞) / 2 ^ 128 := by
        rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ ((tbl.length + 1 : ℕ) : ℝ≥0∞) / 2 ^ 128 :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hcard) _

private theorem tri_succ (m : ℕ) : (m + 1) * m / 2 = m + m * (m - 1) / 2 := by
  cases m with
  | zero => rfl
  | succ k =>
    have heq : (k + 2) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by omega : 0 < 2), Nat.add_sub_cancel, add_comm]

private theorem bday_step_arith (m L : ℕ) :
    (L + 1) + (m * (L + 2) + m * (m - 1) / 2) =
      (m + 1) * (L + 1) + (m + 1) * m / 2 := by
  rw [tri_succ m]
  ring

private theorem lazy_miss_le :
    ∀ (m : ℕ) (x : Block) (tbl : List (Block × Block)),
      tbl.lookup x = none →
      ∀ (P : List.Vector Block m) (G : List.Vector Block (m + 1) → ProbComp Bool) (b : Bool),
        𝒟[(do let c ← lazyStep x; let cs ← cbcM lazyStep c P; pure (c ::ᵥ cs)).run' tbl >>= G] {b} ≤
          𝒟[unifVec (m + 1) >>= G] {b} +
            ((m * (tbl.length + 1) + m * (m - 1) / 2 : ℕ) : ℝ≥0∞) / 2 ^ 128
  | 0, x, tbl, hx, P, G, b => by
    have hL : (do let c ← lazyStep x; let cs ← cbcM lazyStep c P; pure (c ::ᵥ cs)).run' tbl =
        unifVec 1 := by
      simp [lazyStep, hx, cbcM, unifVec, StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc]
    rw [hL]
    simp
  | m + 1, x, tbl, hx, P, G, b => by
    let : MeasurableSpace Block := ⊤
    let f : Block → ProbComp Bool := fun c =>
      (do let c' ← lazyStep (P.head ^^^ c)
          let cs' ← cbcM lazyStep c' P.tail
          pure (c' ::ᵥ cs')).run' ((x, c) :: tbl) >>= fun cs => G (c ::ᵥ cs)
    let g : Block → ProbComp Bool := fun c =>
      unifVec (m + 1) >>= fun cs => G (c ::ᵥ cs)
    let εm : ℝ≥0∞ := ((m * (tbl.length + 2) + m * (m - 1) / 2 : ℕ) : ℝ≥0∞) / 2 ^ 128
    let bad : Set Block := {c : Block | ((x, c) :: tbl).lookup (P.head ^^^ c) ≠ none}
    have hLHS :
        ((do let c ← lazyStep x; let cs ← cbcM lazyStep c P; pure (c ::ᵥ cs)).run' tbl >>= G) =
        (($ᵗ Block) >>= f) := by
      simp only [lazyStep, cbcM, hx, StateT.run'_eq, StateT.run_bind, StateT.run_get,
        StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, map_bind, map_pure,
        bind_assoc, pure_bind, f]
    have hRHS : (unifVec (m + 2) >>= G) = (($ᵗ Block) >>= g) := by
      simp only [unifVec, bind_assoc, pure_bind, g]
    rw [hLHS, hRHS, evalDist_bind_of_discrete, evalDist_bind_of_discrete,
      Measure.bind_apply (measurableSet_singleton b) Measurable.of_discrete.aemeasurable,
      Measure.bind_apply (measurableSet_singleton b) Measurable.of_discrete.aemeasurable]
    have hpt : ∀ c : Block,
        𝒟[f c] {b} ≤ bad.indicator 1 c + (𝒟[g c] {b} + εm) := by
      intro c
      by_cases hc : c ∈ bad
      · simp only [Set.indicator_of_mem hc, Pi.one_apply]
        exact (CryptoGames.AEADScheme.EtMProof.apply_le_one (f c) {b}).trans le_self_add
      · simp only [Set.indicator_of_notMem hc, zero_add]
        have hmiss : ((x, c) :: tbl).lookup (P.head ^^^ c) = none := Classical.not_not.mp hc
        simpa [f, g, εm, List.length_cons, Nat.add_assoc] using
          lazy_miss_le m (P.head ^^^ c) ((x, c) :: tbl) hmiss P.tail (fun cs => G (c ::ᵥ cs)) b
    calc ∫⁻ c, 𝒟[f c] {b} ∂𝒟[($ᵗ Block : ProbComp Block)]
        ≤ ∫⁻ c, (bad.indicator 1 c + (𝒟[g c] {b} + εm)) ∂𝒟[($ᵗ Block : ProbComp Block)] :=
          lintegral_mono hpt
      _ = ∫⁻ c, bad.indicator 1 c ∂𝒟[($ᵗ Block : ProbComp Block)] +
            (∫⁻ c, 𝒟[g c] {b} ∂𝒟[($ᵗ Block : ProbComp Block)] +
              ∫⁻ _c, εm ∂𝒟[($ᵗ Block : ProbComp Block)]) := by
          rw [lintegral_add_left Measurable.of_discrete,
            lintegral_add_left Measurable.of_discrete]
      _ = 𝒟[($ᵗ Block : ProbComp Block)] bad +
            (∫⁻ c, 𝒟[g c] {b} ∂𝒟[($ᵗ Block : ProbComp Block)] + εm) := by
          rw [lintegral_indicator_one MeasurableSet.of_discrete, lintegral_const,
            evalDist_apply_univ_eq_one, mul_one]
      _ = ∫⁻ c, 𝒟[g c] {b} ∂𝒟[($ᵗ Block : ProbComp Block)] +
            (𝒟[($ᵗ Block : ProbComp Block)] bad + εm) := by
          rw [← add_assoc, add_comm (𝒟[($ᵗ Block : ProbComp Block)] bad), add_assoc]
      _ ≤ ∫⁻ c, 𝒟[g c] {b} ∂𝒟[($ᵗ Block : ProbComp Block)] +
            (((tbl.length + 1 : ℕ) : ℝ≥0∞) / 2 ^ 128 + εm) :=
          add_le_add le_rfl (add_le_add (measure_bad_le P.head x tbl) le_rfl)
      _ = ∫⁻ c, 𝒟[g c] {b} ∂𝒟[($ᵗ Block : ProbComp Block)] +
            (((m + 1) * (tbl.length + 1) + (m + 1) * m / 2 : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
          congr 1
          dsimp only [εm]
          rw [← ENNReal.add_div, ← Nat.cast_add, bday_step_arith m tbl.length]

theorem cbcLazy_close {n : ℕ} (P : List.Vector Block n)
    (F : List.Vector Block n → ProbComp Bool) :
    𝒟[cbcLazy P >>= F].boolDist 𝒟[$ᵗ (List.Vector Block n) >>= F] ≤
      ((n * (n - 1) / 2 : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
  have hunif : 𝒟[unifVec n >>= F] = 𝒟[$ᵗ (List.Vector Block n) >>= F] :=
    (EvalDistEq.bind_left (unifVec_evalDistEq n) F).evalDist_eq
  rw [← hunif]
  cases n with
  | zero =>
    have heq : 𝒟[cbcLazy P >>= F] = 𝒟[unifVec 0 >>= F] := by
      have hP : P = List.Vector.nil := Subsingleton.elim P List.Vector.nil
      subst hP
      simp only [cbcLazy, cbcM, StateT.run'_eq, StateT.run_pure, map_pure, bind_assoc, pure_bind,
        unifVec]
      exact OracleComp.evalDist_bind_const ($ᵗ Block) (F List.Vector.nil)
    rw [heq]
    simp
  | succ m =>
    refine Measure.boolDist_le_of_apply_le _ _ fun b => ?_
    unfold cbcLazy
    rw [bind_assoc]
    refine CryptoGames.AEADScheme.EtMProof.bind_le_of_support ($ᵗ Block) _
      (measurableSet_singleton b) fun iv _ => ?_
    have hstep := lazy_miss_le m (P.head ^^^ iv) [] rfl P.tail F b
    have harith : (m + 1) * (m + 1 - 1) / 2 =
        m * (List.length ([] : List (Block × Block)) + 1) + m * (m - 1) / 2 := by
      simp [tri_succ m]
    rw [harith]
    exact hstep

end CryptoGames.CBC.Bday
