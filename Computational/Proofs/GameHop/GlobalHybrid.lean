/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.GameHop.Advantage
public import Computational.Proofs.GameHop.Rnd

/-!
# Multi-Instance Hybrids, Partition-Kill Hybrids, and Prefix Sandwiches

Protocol-agnostic multi-step `boolDist` and `boolBias` telescopes, partition-masking hybrids
(`gameKill`), and two-stage pause/resume prefix-sandwich reductions.
-/

set_option autoImplicit false

@[expose] public section

namespace Computational.Proofs.GameHop.GlobalHybrid

open OracleSpec OracleComp
open scoped ENNReal
open MeasureTheory (Measure)
open Computational.Proofs.GameHop.Rnd (evalDist_select_swap)
open Computational.Proofs.GameHop.Advantage (boolBias_le_add_two_mul_boolDist
  boolBias_le_two_mul_boolDist_of_eq_zero boolDist_le_of_select_eq
  boolDist_le_iSup_flip_of_beq_not_le evalDist_bind_mono_prob_of_support)

section StandardTelescope

theorem boolDist_hybrid_le_sum_range (H : ℕ → ProbComp Bool) (N : ℕ) :
    𝒟[H 0].boolDist 𝒟[H N] ≤ ∑ k ∈ Finset.range N, 𝒟[H k].boolDist 𝒟[H (k + 1)] :=
  Measure.boolDist_le_sum_range (fun k => 𝒟[H k]) N

theorem boolDist_hybrid_rev_le_sum_range (H : ℕ → ProbComp Bool) (N : ℕ) :
    𝒟[H N].boolDist 𝒟[H 0] ≤ ∑ k ∈ Finset.range N, 𝒟[H (k + 1)].boolDist 𝒟[H k] := by
  rw [Measure.boolDist_comm]
  refine (Measure.boolDist_le_sum_range (fun k => 𝒟[H k]) N).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Measure.boolDist_comm]

theorem boolBias_hybrid_le_add_two_mul_sum_range (H : ℕ → ProbComp Bool) (N : ℕ) :
    𝒟[H 0].boolBias ≤
      𝒟[H N].boolBias + 2 * ∑ k ∈ Finset.range N, 𝒟[H k].boolDist 𝒟[H (k + 1)] :=
  (boolBias_le_add_two_mul_boolDist 𝒟[H 0] 𝒟[H N]).trans
    (by gcongr; exact boolDist_hybrid_le_sum_range H N)

theorem boolBias_hybrid_le_two_mul_sum_range_of_unbiased (H : ℕ → ProbComp Bool) (N : ℕ)
    (hN : 𝒟[H N].boolBias = 0) :
    𝒟[H 0].boolBias ≤ 2 * ∑ k ∈ Finset.range N, 𝒟[H k].boolDist 𝒟[H (k + 1)] := by
  simpa [hN] using boolBias_hybrid_le_add_two_mul_sum_range H N

end StandardTelescope

section PartitionKillHybrid

/-- Partition-kill hybrid replacing the output with `$ᵗ Bool` when `canon a ∈ S`, and running
`out a` otherwise. -/
def gameKill {α τ : Type} [DecidableEq τ] (run : ProbComp α) (canon : α → τ)
    (out : α → ProbComp Bool) (S : Finset τ) : ProbComp Bool := do
  let a ← run
  if canon a ∈ S then ($ᵗ Bool : ProbComp Bool)
  else out a

/-- Single-tag hybrid branch running `out a` when `canon a = t₀`, and `$ᵗ Bool` otherwise. -/
def gameOnlyTag {α τ : Type} [DecidableEq τ] (run : ProbComp α) (canon : α → τ)
    (out : α → ProbComp Bool) (t₀ : τ) : ProbComp Bool := do
  let a ← run
  if canon a = t₀ then out a
  else ($ᵗ Bool : ProbComp Bool)

@[simp]
theorem gameKill_empty {α τ : Type} [DecidableEq τ] (run : ProbComp α) (canon : α → τ)
    (out : α → ProbComp Bool) :
    gameKill run canon out ∅ = (run >>= out) := by
  simp [gameKill]

private theorem ite_bind_bool {m : Type → Type} [Monad m] {α β : Type} (c : Bool)
    (x : m α) (f g : α → m β) :
    (if c then x >>= f else x >>= g) = (x >>= fun a => if c then f a else g a) := by
  cases c <;> rfl

theorem evalDist_select_gameKill_insert {α τ : Type} [DecidableEq τ]
    (run : ProbComp α) (canon : α → τ) (out : α → ProbComp Bool)
    (S : Finset τ) (t₀ : τ) (ht₀ : t₀ ∉ S) :
    𝒟[do
        let sel ← ($ᵗ Bool : ProbComp Bool)
        if sel then gameKill run canon out S else ($ᵗ Bool : ProbComp Bool)] =
      𝒟[do
        let sel ← ($ᵗ Bool : ProbComp Bool)
        if sel then gameKill run canon out (insert t₀ S)
        else gameOnlyTag run canon out t₀] := by
  have hcoin :
      𝒟[do
          let sel ← ($ᵗ Bool : ProbComp Bool)
          if sel then gameKill run canon out S else ($ᵗ Bool : ProbComp Bool)] =
        𝒟[do
          let sel ← ($ᵗ Bool : ProbComp Bool)
          if sel then gameKill run canon out S
          else do
            let _ ← run
            ($ᵗ Bool : ProbComp Bool)] := by
    refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun sel => ?_
    cases sel
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (evalDist_bind_const run ($ᵗ Bool : ProbComp Bool)).symm
    · rfl
  rw [hcoin]
  unfold gameKill gameOnlyTag
  simp only [ite_bind_bool _ run]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) run,
    OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) run]
  refine evalDist_bind_congr run _ _ fun a => ?_
  by_cases hcan : canon a = t₀
  · simp only [hcan, ht₀, ↓reduceIte, Finset.mem_insert_self]
    exact evalDist_select_swap (out a) ($ᵗ Bool : ProbComp Bool)
  · have hmem : canon a ∈ insert t₀ S ↔ canon a ∈ S := by simp [Finset.mem_insert, hcan]
    simp [hmem, hcan]

theorem gameKill_boolDist_insert {α β τ : Type} [DecidableEq τ]
    (run₀ : ProbComp α) (canon₀ : α → τ) (out₀ : α → ProbComp Bool)
    (run₁ : ProbComp β) (canon₁ : β → τ) (out₁ : β → ProbComp Bool)
    (S : Finset τ) (t₀ : τ) (ht₀ : t₀ ∉ S) :
    𝒟[gameKill run₀ canon₀ out₀ S].boolDist 𝒟[gameKill run₁ canon₁ out₁ S] ≤
      𝒟[gameKill run₀ canon₀ out₀ (insert t₀ S)].boolDist
          𝒟[gameKill run₁ canon₁ out₁ (insert t₀ S)] +
        𝒟[gameOnlyTag run₀ canon₀ out₀ t₀].boolDist
          𝒟[gameOnlyTag run₁ canon₁ out₁ t₀] :=
  boolDist_le_of_select_eq _ _ _ _ _ _
    (evalDist_select_gameKill_insert run₀ canon₀ out₀ S t₀ ht₀)
    (evalDist_select_gameKill_insert run₁ canon₁ out₁ S t₀ ht₀)

theorem gameKill_boolDist_union_le {α β τ : Type} [DecidableEq τ]
    (run₀ : ProbComp α) (canon₀ : α → τ) (out₀ : α → ProbComp Bool)
    (run₁ : ProbComp β) (canon₁ : β → τ) (out₁ : β → ProbComp Bool)
    (T : Finset τ) :
    ∀ S : Finset τ, Disjoint S T →
      𝒟[gameKill run₀ canon₀ out₀ S].boolDist 𝒟[gameKill run₁ canon₁ out₁ S] ≤
        𝒟[gameKill run₀ canon₀ out₀ (S ∪ T)].boolDist
            𝒟[gameKill run₁ canon₁ out₁ (S ∪ T)] +
          ∑ t₀ ∈ T,
            𝒟[gameOnlyTag run₀ canon₀ out₀ t₀].boolDist
              𝒟[gameOnlyTag run₁ canon₁ out₁ t₀] := by
  induction T using Finset.induction_on with
  | empty =>
    intro S _; simp
  | @insert t₀ T ht₀_not_T ih =>
    intro S hdisj
    have ht₀_not_S : t₀ ∉ S := (Finset.disjoint_insert_right.mp hdisj).1
    have hdisj' : Disjoint (insert t₀ S) T :=
      Finset.disjoint_insert_left.mpr ⟨ht₀_not_T, (Finset.disjoint_insert_right.mp hdisj).2⟩
    have hstep := gameKill_boolDist_insert run₀ canon₀ out₀ run₁ canon₁ out₁ S t₀ ht₀_not_S
    have hih := ih (insert t₀ S) hdisj'
    have hunion : insert t₀ S ∪ T = S ∪ insert t₀ T := by ext x; simp
    rw [hunion] at hih
    rw [Finset.sum_insert ht₀_not_T]
    calc _ ≤ _ := hstep
      _ ≤ (𝒟[gameKill run₀ canon₀ out₀ (S ∪ insert t₀ T)].boolDist
              𝒟[gameKill run₁ canon₁ out₁ (S ∪ insert t₀ T)] +
            ∑ x ∈ T, 𝒟[gameOnlyTag run₀ canon₀ out₀ x].boolDist
              𝒟[gameOnlyTag run₁ canon₁ out₁ x]) +
            𝒟[gameOnlyTag run₀ canon₀ out₀ t₀].boolDist
              𝒟[gameOnlyTag run₁ canon₁ out₁ t₀] := add_le_add hih le_rfl
      _ = _ := by ac_rfl

/-- Bounds `boolDist` by summing single-tag `gameOnlyTag` distances when killing all tags in `T`
equates the two games. -/
theorem boolDist_le_sum_finset_of_gameKill {α β τ : Type} [DecidableEq τ]
    (run₀ : ProbComp α) (canon₀ : α → τ) (out₀ : α → ProbComp Bool)
    (run₁ : ProbComp β) (canon₁ : β → τ) (out₁ : β → ProbComp Bool)
    (T : Finset τ)
    (hkilled : 𝒟[gameKill run₀ canon₀ out₀ T] = 𝒟[gameKill run₁ canon₁ out₁ T]) :
    𝒟[run₀ >>= out₀].boolDist 𝒟[run₁ >>= out₁] ≤
      ∑ t₀ ∈ T,
        𝒟[gameOnlyTag run₀ canon₀ out₀ t₀].boolDist
          𝒟[gameOnlyTag run₁ canon₁ out₁ t₀] := by
  have hunion := gameKill_boolDist_union_le run₀ canon₀ out₀ run₁ canon₁ out₁ T ∅
    (Finset.disjoint_empty_left T)
  rw [Finset.empty_union, gameKill_empty, gameKill_empty, hkilled, Measure.boolDist_self,
    zero_add] at hunion
  exact hunion

end PartitionKillHybrid

section PrefixHybrid

/-- Priority-cascade output bit `if W1 then true else if W0 then false else b'` for two-stage
prefix hybrids. -/
def slotStepOut (W1 W0 b' : Bool) : Bool :=
  if W1 then true else if W0 then false else b'

def slotStepY1 (C coin W1 W0 win b' : Bool) : Bool :=
  if !C then coin else slotStepOut (W1 || win) W0 b'

def slotStepY0 (C coin W1 W0 win b' : Bool) : Bool :=
  if !C then coin else slotStepOut W1 (W0 || win) b'

/-- Post-processed output bit emitted by a paused prefix reduction. -/
def slotStepWRed (E C coin W1 W0 b' flip : Bool) : Bool :=
  if !E then false else if !C then (coin ^^ flip) else (slotStepOut W1 W0 b' ^^ flip)

theorem slotStep_bool_le_true (E C coin W1 W0 win b' flip : Bool) :
    (E && (slotStepY1 C coin W1 W0 win b' == !flip)) ≤
      (slotStepWRed E C coin W1 W0 b' flip || (E && win)) := by
  cases E <;> cases C <;> cases coin <;> cases W1 <;> cases W0 <;>
    cases win <;> cases b' <;> cases flip <;> decide

theorem slotStep_bool_le_false (E C coin W1 W0 win b' flip : Bool) :
    (slotStepWRed E C coin W1 W0 b' flip && !(E && win)) ≤
      (E && (slotStepY0 C coin W1 W0 win b' == !flip)) := by
  cases E <;> cases C <;> cases coin <;> cases W1 <;> cases W0 <;>
    cases win <;> cases b' <;> cases flip <;> decide

private theorem evalDist_map_pair_split (m : ProbComp (Bool × Bool)) (flip : Bool) :
    𝒟[(fun p : Bool × Bool => p.2 == !flip) <$> m] {true} =
      𝒟[(fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$> m] {true} +
        𝒟[(fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$> m] {true} := by
  rw [evalDist_map_of_discrete, evalDist_map_of_discrete, evalDist_map_of_discrete,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton true),
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton true),
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton true),
    ← MeasureTheory.measure_union
      (Set.disjoint_iff.mpr fun ⟨p₁, p₂⟩ ⟨h₁, h₂⟩ => by cases p₁ <;> simp_all)
      MeasurableSet.of_discrete]
  congr 1; ext ⟨p₁, p₂⟩; cases p₁ <;> simp

/-- Two-stage prefix-sandwich bound reducing `boolDist` on `pairExp` to
`⨆ flip, 𝒟[oa >>= redGame flip].boolBias` when unpaused branches agree and paused branches sandwich
`redTrue` and `redFalse`. -/
theorem boolDist_bind_pair_sandwich_le_iSup_flip {α : Type}
    (oa : ProbComp α)
    (pairExp : Bool → α → ProbComp (Bool × Bool))
    (redTrue redFalse redGame : Bool → α → ProbComp Bool)
    (h_unpaused : ∀ flip : Bool, ∀ pst ∈ support oa,
      𝒟[(fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$> pairExp true pst] {true} =
        𝒟[(fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$> pairExp false pst] {true})
    (h_true_le : ∀ flip : Bool, ∀ pst ∈ support oa,
      𝒟[(fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$> pairExp true pst] {true} ≤
        𝒟[redTrue flip pst] {true})
    (h_false_ge : ∀ flip : Bool, ∀ pst ∈ support oa,
      𝒟[redFalse flip pst] {true} ≤
        𝒟[(fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$> pairExp false pst] {true})
    (h_bias : ∀ flip : Bool,
      𝒟[oa >>= redTrue flip].boolDist 𝒟[oa >>= redFalse flip] ≤
        𝒟[oa >>= redGame flip].boolBias) :
    𝒟[oa >>= fun pst => Prod.snd <$> pairExp true pst].boolDist
        𝒟[oa >>= fun pst => Prod.snd <$> pairExp false pst] ≤
      ⨆ flip : Bool, 𝒟[oa >>= redGame flip].boolBias := by
  refine boolDist_le_iSup_flip_of_beq_not_le _ _ _ fun flip => ?_
  simp only [map_bind, Functor.map_map]
  have hsplit : ∀ b : Bool,
      𝒟[oa >>= fun pst => (fun p : Bool × Bool => p.2 == !flip) <$> pairExp b pst] {true} =
        𝒟[oa >>= fun pst => (fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$> pairExp b pst] {true} +
          𝒟[oa >>= fun pst => (fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$> pairExp b pst] {true} := by
    intro b
    let : MeasurableSpace α := ⊤
    simp only [evalDist_bind_of_discrete,
      Measure.bind_apply (measurableSet_singleton true) Measurable.of_discrete.aemeasurable]
    simp_rw [evalDist_map_pair_split _ flip]
    exact MeasureTheory.lintegral_add_left Measurable.of_discrete _
  have h0 :
      𝒟[oa >>= fun pst => (fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$> pairExp true pst] {true} =
        𝒟[oa >>= fun pst => (fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$> pairExp false pst] {true} :=
    le_antisymm
      (evalDist_bind_mono_prob_of_support oa _ _ (measurableSet_singleton true)
        fun pst hp => (h_unpaused flip pst hp).le)
      (evalDist_bind_mono_prob_of_support oa _ _ (measurableSet_singleton true)
        fun pst hp => (h_unpaused flip pst hp).ge)
  have h1 :
      𝒟[oa >>= fun pst => (fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$> pairExp true pst] {true} ≤
        𝒟[oa >>= redTrue flip] {true} :=
    evalDist_bind_mono_prob_of_support oa _ _ (measurableSet_singleton true) (h_true_le flip)
  have h2 :
      𝒟[oa >>= redFalse flip] {true} ≤
        𝒟[oa >>= fun pst => (fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$> pairExp false pst] {true} :=
    evalDist_bind_mono_prob_of_support oa _ _ (measurableSet_singleton true) (h_false_ge flip)
  have h3 := (Measure.apply_true_le_add_boolDist 𝒟[oa >>= redTrue flip] 𝒟[oa >>= redFalse flip]).trans
    (add_le_add le_rfl (h_bias flip))
  rw [hsplit true, hsplit false, h0]
  calc 𝒟[oa >>= fun pst => (fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$> pairExp true pst] {true} +
        𝒟[oa >>= fun pst => (fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$> pairExp false pst] {true}
      ≤ (𝒟[oa >>= redFalse flip] {true} + 𝒟[oa >>= redGame flip].boolBias) +
          𝒟[oa >>= fun pst => (fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$> pairExp false pst] {true} :=
        add_le_add (h1.trans h3) le_rfl
    _ ≤ (𝒟[oa >>= fun pst => (fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$> pairExp false pst] {true} +
          𝒟[oa >>= redGame flip].boolBias) +
          𝒟[oa >>= fun pst => (fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$> pairExp false pst] {true} :=
        add_le_add (add_le_add h2 le_rfl) le_rfl
    _ = _ := by ac_rfl

end PrefixHybrid

end Computational.Proofs.GameHop.GlobalHybrid
