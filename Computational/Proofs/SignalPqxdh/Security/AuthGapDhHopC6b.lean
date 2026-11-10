/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC3b
import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC2b
import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC5
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
import VCVio.EvalDist.Monad.Basic

/-!
# `Auth` hop `G3 → G3.5`: `RelProbUpToBad` framework and `roCache`-erasure step couplings

Develops the `isAuthG3Abort`-absorbing `RelProbUpToBad` coupling framework, proves off-`roCache`
query commutation on `AuthAdvCutoffState` and `AuthAdvLatchedState`, and bounds `advRoLog` and
`respRecs` lengths under `QueryBounded`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal BigOperators
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security

/-! ## `RelProbUpToBad` step-or-abort framework -/

theorem evalDist_finalizeAuthKosk_of_isAuthG3Abort {S : Setup} (P : Primitives)
    (secb b' : Bool) (finalSt : AuthHybridState S)
    (hAbort : isAuthG3Abort P finalSt = true) :
    𝒟[finalizeAuthKosk S P secb b' finalSt] = 𝒟[$ᵗ Bool] := by
  rw [finalizeAuthKosk_of_isAuthG3Abort P secb b' finalSt hAbort]

theorem probExpect_map_eq {α β : Type} (f : α → β) (mx : ProbComp α) (w : β → ℝ≥0∞) :
    probExpect (f <$> mx) w = probExpect mx (fun x => w (f x)) := by
  rw [map_eq_bind_pure_comp, probExpect_bind]
  exact le_antisymm
    (probExpect_mono_of_support mx _ _ (fun x _ => by simp [Function.comp, probExpect_pure]))
    (probExpect_mono_of_support mx _ _ (fun x _ => by simp [Function.comp, probExpect_pure]))

theorem RelProbUpToBad.of_map_left {α : Type} {R : α → α → Prop} {bad : α → Bool}
    (f : α → α) (m : ProbComp α)
    (hR : ∀ x ∈ support m, bad x = false → R (f x) x) :
    RelProbUpToBad R bad (f <$> m) m := by
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · rw [probExpect_map_eq]
    refine probExpect_mono_of_support m _ _ (fun x hx => ?_)
    cases hb : bad x
    · exact hle (f x) x (hR x hx hb)
    · rw [hw6 x hb]; exact hw5 (f x)
  · rw [probExpect_map_eq]
    refine probExpect_mono_of_support m _ _ (fun x hx => ?_)
    cases hb : bad x
    · exact hle (f x) x (hR x hx hb)
    · rw [hw6 x hb]; exact zero_le

theorem RelProbUpToBad.mono {α : Type} {R1 R2 : α → α → Prop} {bad1 bad2 : α → Bool}
    {m5 m6 : ProbComp α}
    (h : RelProbUpToBad R1 bad1 m5 m6)
    (hR : ∀ x5 x6, R1 x5 x6 → bad2 x6 = false → R2 x5 x6)
    (hBad : ∀ x6, bad1 x6 = true → bad2 x6 = true) :
    RelProbUpToBad R2 bad2 m5 m6 := by
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · refine h.1 w5 w6 hw5 (fun y6 hb1 => hw6 y6 (hBad y6 hb1)) (fun y5 y6 h1 => ?_)
    cases hb2 : bad2 y6
    · exact hle y5 y6 (hR y5 y6 h1 hb2)
    · rw [hw6 y6 hb2]; exact hw5 y5
  · refine h.2 w6 w5 (fun y6 hb1 => hw6 y6 (hBad y6 hb1)) (fun y5 y6 h1 => ?_)
    cases hb2 : bad2 y6
    · exact hle y5 y6 (hR y5 y6 h1 hb2)
    · rw [hw6 y6 hb2]; exact zero_le

theorem RelProbUpToBad.evalDist_bind_step_le {α : Type}
    {R : α → α → Prop} {bad : α → Bool}
    {m5 m6 : ProbComp α}
    (hStep : RelProbUpToBad R bad m5 m6)
    (k5 k6 kb6 : α → ProbComp Bool)
    (hBadMono : ∀ y6, bad y6 = true → 𝒟[kb6 y6] {true} = 1)
    (hCont : ∀ y5 y6, R y5 y6 → bad y6 = false →
      𝒟[k5 y5] {true} ≤ 𝒟[k6 y6] {true} + 𝒟[kb6 y6] {true} ∧
      𝒟[k6 y6] {true} ≤ 𝒟[k5 y5] {true} + 𝒟[kb6 y6] {true}) :
    𝒟[m5 >>= k5] {true} ≤ 𝒟[m6 >>= k6] {true} + 𝒟[m6 >>= kb6] {true} ∧
    𝒟[m6 >>= k6] {true} ≤ 𝒟[m5 >>= k5] {true} + 𝒟[m6 >>= kb6] {true} := by
  have h5 : 𝒟[m5 >>= k5] {true} = probExpect m5 (fun y => 𝒟[k5 y] {true}) := by
    let _ : MeasurableSpace α := ⊤
    have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
    unfold probExpect
    rw [evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable]
  have h6 : 𝒟[m6 >>= k6] {true} = probExpect m6 (fun y => 𝒟[k6 y] {true}) := by
    let _ : MeasurableSpace α := ⊤
    have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
    unfold probExpect
    rw [evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable]
  have hb6 : 𝒟[m6 >>= kb6] {true} = probExpect m6 (fun y => 𝒟[kb6 y] {true}) := by
    let _ : MeasurableSpace α := ⊤
    have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
    unfold probExpect
    rw [evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable]
  rw [h5, h6, hb6]
  refine ⟨?_, ?_⟩
  · calc probExpect m5 (fun y => 𝒟[k5 y] {true})
        ≤ probExpect m6 (fun y => min 1 (𝒟[k6 y] {true} + 𝒟[kb6 y] {true})) := by
          refine hStep.1 _ _ (fun _ => MeasureTheory.prob_le_one)
            (fun y6 hb => ?_) (fun y5 y6 hR => ?_)
          · rw [hBadMono y6 hb]; exact min_eq_left (by simp)
          · cases hb : bad y6
            · exact le_min (MeasureTheory.prob_le_one) (hCont y5 y6 hR hb).1
            · rw [hBadMono y6 hb, min_eq_left (by simp)]; exact MeasureTheory.prob_le_one
      _ ≤ probExpect m6 (fun y => 𝒟[k6 y] {true}) + probExpect m6 (fun y => 𝒟[kb6 y] {true}) := by
          apply probExpect_add_le
          intro y; exact min_le_right _ _
  · calc probExpect m6 (fun y => 𝒟[k6 y] {true})
        ≤ probExpect m6 (fun y => if bad y then 0 else (𝒟[k6 y] {true} - 𝒟[kb6 y] {true})) +
          probExpect m6 (fun y => 𝒟[kb6 y] {true}) := by
          apply probExpect_add_le
          intro y
          cases hb : bad y
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact le_tsub_add
          · simp only [↓reduceIte, zero_add, hBadMono y hb]
            exact MeasureTheory.prob_le_one
      _ ≤ probExpect m5 (fun y => 𝒟[k5 y] {true}) + probExpect m6 (fun y => 𝒟[kb6 y] {true}) := by
          gcongr
          refine hStep.2 _ _ (fun y6 hb => by simp [hb]) (fun y5 y6 hR => ?_)
          cases hb : bad y6
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact tsub_le_iff_right.mpr (hCont y5 y6 hR hb).2
          · simp

/-! ## Off-`roCache` state agreement and step couplings -/

def withAuthBaseRoCache {S : Setup} (c : List (Bytes × DRKey)) (st : AuthState S) : AuthState S :=
  { st with roCache := c }

def withAuthHybRoCache {S : Setup} (c : List (Bytes × DRKey)) (hst : AuthHybridState S) :
    AuthHybridState S :=
  { hst with base := withAuthBaseRoCache c hst.base }

def withAuthAdvRoCache {S : Setup} (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    AuthAdvCutoffState S :=
  { s with hyb := withAuthHybRoCache c s.hyb }

@[simp]
theorem withAuthAdvRoCache_self {S : Setup} (s : AuthAdvCutoffState S) :
    withAuthAdvRoCache s.hyb.base.roCache s = s := rfl

@[simp]
theorem withAuthAdvRoCache_withAuthAdvRoCache {S : Setup} (c1 c2 : List (Bytes × DRKey))
    (s : AuthAdvCutoffState S) :
    withAuthAdvRoCache c1 (withAuthAdvRoCache c2 s) = withAuthAdvRoCache c1 s := rfl

@[simp]
theorem withAuthAdvRoCache_roCache {S : Setup} (c : List (Bytes × DRKey))
    (s : AuthAdvCutoffState S) :
    (withAuthAdvRoCache c s).hyb.base.roCache = c := rfl

theorem isAuthG3Abort_withAuthAdvRoCache {S : Setup} (P : Primitives)
    (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    isAuthG3Abort P (withAuthAdvRoCache c s).hyb = isAuthG3Abort P s.hyb :=
  isAuthG3Abort_withBaseRoCache P c s.hyb

theorem pqxdhAuthAdvStageImpl_initPrin_withAuthAdvRoCache (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl .g3_5 S P (.initPrin u)).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl .g3 S P (.initPrin u)).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, liftAuthBase, pqxdhAuthImpl,
      withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;>
      simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift, monadLift_self, Prod.map,
        withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon]

theorem pqxdhAuthAdvStageImpl_corruptIK_withAuthAdvRoCache (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl .g3_5 S P (.corruptIK u)).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl .g3 S P (.corruptIK u)).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, liftAuthBase, pqxdhAuthImpl,
      withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    cases s.hyb.base.principals.find? (fun (idx, _) => idx == u.val) <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map, withAuthAdvRoCache, withAuthHybRoCache,
        withAuthBaseRoCache, hWon]

theorem pqxdhAuthAdvStageImpl_genSPK_withAuthAdvRoCache (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl .g3_5 S P (.genSPK u j)).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl .g3 S P (.genSPK u j)).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, liftAuthBase, pqxdhAuthImpl,
      withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    cases s.hyb.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp [StateT.run_pure, Prod.map, withAuthAdvRoCache, withAuthHybRoCache,
        withAuthBaseRoCache, hWon]
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      split_ifs <;>
        simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift, monadLift_self, Prod.map,
          withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon]

theorem pqxdhAuthAdvStageImpl_genOPK_withAuthAdvRoCache (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl .g3_5 S P (.genOPK u j o)).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl .g3 S P (.genOPK u j o)).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, liftAuthBase, pqxdhAuthImpl,
      withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;>
      simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift, monadLift_self, Prod.map,
        withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon]

theorem pqxdhAuthAdvStageImpl_registerKey_withAuthAdvRoCache (S : Setup) (P : Primitives)
    (sk : Bytes) (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl .g3_5 S P (.registerKey sk)).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl .g3 S P (.registerKey sk)).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, liftAuthBase, pqxdhAuthImpl,
      registerAdvKey, withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon,
      Bool.true_and, Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind,
      StateT.run_get, pure_bind]
    split_ifs <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map, withAuthAdvRoCache, withAuthHybRoCache,
        withAuthBaseRoCache, hWon]

theorem pqxdhAuthAdvStageImpl_roRootQuery_withAuthAdvRoCache (S : Setup) (P : Primitives)
    (rk dh : Bytes) (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl .g3_5 S P (.roRootQuery rk dh)).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl .g3 S P (.roRootQuery rk dh)).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, liftAuthBase, pqxdhAuthImpl,
      withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;>
      simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift, monadLift_self, Prod.map,
        withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon]

theorem pqxdhAuthAdvStageImpl_revealDhSecrets_withAuthAdvRoCache (S : Setup) (P : Primitives)
    (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl .g3_5 S P .revealDhSecrets).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl .g3 S P .revealDhSecrets).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl, pqxdhAuthHybridKoskImpl, liftAuthBase, pqxdhAuthImpl,
      withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    simp [StateT.run_pure, StateT.run_set, Prod.map, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon]

/-! ## `badAuthFgDh1AtNonEmpty` agreement and lookup helpers -/

theorem find_principals_eq_some_of_mem {S : Setup}
    {principals : List (Nat × PrincipalEntry)}
    (hV : ValidPrincipals S principals) {u : Nat} {e : PrincipalEntry}
    (hMem : (u, e) ∈ principals) :
    principals.find? (fun (idx, _) => idx == u) = some (u, e) := by
  have hNodup := hV.2
  induction principals with
  | nil => nomatch hMem
  | cons hd tl ih =>
    rcases hd with ⟨u', e'⟩
    rw [List.map_cons, List.nodup_cons] at hNodup
    rcases List.mem_cons.mp hMem with hEq | hTl
    · injection hEq with hu he; subst hu; subst he; simp [List.find?]
    · have hNe : (u' == u) = false := by
        cases hBeq : (u' == u)
        · rfl
        · have huEq : u' = u := beq_iff_eq.mp hBeq
          exact False.elim (hNodup.1 (List.mem_map.mpr ⟨(u, e), hTl, huEq.symm⟩))
      simp only [List.find?_cons, hNe]
      exact ih ⟨fun x hx => hV.1 x (List.mem_cons_of_mem _ hx), hNodup.2⟩ hTl hNodup.2

theorem find_spkBundles_flatIdx_eq_some_of_mem {S : Setup}
    {spkBundles : List ((Nat × Nat) × SpkBundleEntry)}
    (hV : ValidSpkBundles S spkBundles) {k j : Nat} {bEntry : SpkBundleEntry}
    (hMem : ((k, j), bEntry) ∈ spkBundles) :
    spkBundles.find? (fun (idx, _) => spkBundleFlatIdxVal S idx == spkBundleFlatIdxVal S (k, j)) =
      some ((k, j), bEntry) := by
  have hNodup := hV.2
  induction spkBundles with
  | nil => nomatch hMem
  | cons hd tl ih =>
    rcases hd with ⟨⟨k', j'⟩, b'⟩
    rw [List.map_cons, List.nodup_cons] at hNodup
    rcases List.mem_cons.mp hMem with hEq | hTl
    · injection hEq with hkj hb; injection hkj with hk hj; subst hk; subst hj; subst hb
      simp [List.find?]
    · have h1hd := hV.1 ((k', j'), b') List.mem_cons_self
      have h1Mem := hV.1 ((k, j), bEntry) (List.mem_cons_of_mem _ hTl)
      have hNe : (spkBundleFlatIdxVal S (k', j') == spkBundleFlatIdxVal S (k, j)) = false := by
        cases hBeq : (spkBundleFlatIdxVal S (k', j') == spkBundleFlatIdxVal S (k, j))
        · rfl
        · have hFlatEq : spkBundleFlatIdxVal S (k', j') = spkBundleFlatIdxVal S (k, j) :=
            beq_iff_eq.mp hBeq
          have hjLt' : j' < S.N_recv := h1hd.2
          have hjLt : j < S.N_recv := h1Mem.2
          have hNpos : 0 < S.N_recv := by omega
          have hkEq : k' = k := by
            have hdiv' : (k' * S.N_recv + j') / S.N_recv = k' := by
              rw [Nat.add_comm, Nat.add_mul_div_right _ _ hNpos, Nat.div_eq_of_lt hjLt',
                Nat.zero_add]
            have hdiv : (k * S.N_recv + j) / S.N_recv = k := by
              rw [Nat.add_comm, Nat.add_mul_div_right _ _ hNpos, Nat.div_eq_of_lt hjLt,
                Nat.zero_add]
            unfold spkBundleFlatIdxVal at hFlatEq
            dsimp only at hFlatEq
            calc k' = (k' * S.N_recv + j') / S.N_recv := hdiv'.symm
              _ = (k * S.N_recv + j) / S.N_recv := by rw [hFlatEq]
              _ = k := hdiv
          have hjEq : j' = j := by
            unfold spkBundleFlatIdxVal at hFlatEq
            dsimp only at hFlatEq
            rw [hkEq] at hFlatEq
            omega
          exact False.elim (hNodup.1 (List.mem_map.mpr ⟨((k, j), bEntry), hTl,
            by rw [hkEq, hjEq]⟩))
      simp only [List.find?_cons, hNe]
      exact ih ⟨fun x hx => hV.1 x (List.mem_cons_of_mem _ hx), hNodup.2⟩ hTl hNodup.2

theorem spkBundleFlatIdxVal_mem_range {S : Setup}
    {spkBundles : List ((Nat × Nat) × SpkBundleEntry)}
    (hV : ValidSpkBundles S spkBundles) {k j : Nat} {bEntry : SpkBundleEntry}
    (hMem : ((k, j), bEntry) ∈ spkBundles) :
    spkBundleFlatIdxVal S (k, j) ∈ List.range S.N_spk_tot := by
  have ⟨hkLt, hjLt⟩ := hV.1 ((k, j), bEntry) hMem
  rw [List.mem_range]
  unfold spkBundleFlatIdxVal Setup.N_spk_tot
  dsimp only
  have h1 : k + 1 ≤ S.N_id := hkLt
  have h2 : (k + 1) * S.N_recv ≤ S.N_id * S.N_recv := Nat.mul_le_mul_right S.N_recv h1
  nlinarith

theorem consumeMatchingSentOPK_true_imp_exists_match (P : Primitives) (r : RecvdOPKEvent) :
    ∀ (l : List SentOPKEvent),
      (consumeMatchingSentOPK P r l).1 = true →
      ∃ s ∈ l, matchSentOPK P r s = true
  | [], h => nomatch h
  | s :: rest, h => by
    unfold consumeMatchingSentOPK at h
    split_ifs at h with hMatch
    · exact ⟨s, List.mem_cons_self, hMatch⟩
    · rcases consumeMatchingSentOPK_true_imp_exists_match P r rest h with ⟨s0, hs0, hM0⟩
      exact ⟨s0, List.mem_cons_of_mem _ hs0, hM0⟩

theorem consumeMatchingSentNoOPK_true_imp_exists_match (P : Primitives) (r : RecvdNoOPKEvent) :
    ∀ (l : List SentNoOPKEvent),
      (consumeMatchingSentNoOPK P r l).1 = true →
      ∃ s ∈ l, matchSentNoOPK P r s = true
  | [], h => nomatch h
  | s :: rest, h => by
    unfold consumeMatchingSentNoOPK at h
    split_ifs at h with hMatch
    · exact ⟨s, List.mem_cons_self, hMatch⟩
    · rcases consumeMatchingSentNoOPK_true_imp_exists_match P r rest h with ⟨s0, hs0, hM0⟩
      exact ⟨s0, List.mem_cons_of_mem _ hs0, hM0⟩

/-! ## Latched `GapDH` combiner, log-length bounds, and latched step couplings -/

/-- Per-index sticky `DH1` (`badAuthFgDh1LatchedAt`) `GapDH` coupling statement under `runAuthFgLatchedSim`. -/
abbrev AuthFgDh1LatchedCouplingStmt (S : Setup) : Prop :=
  ∀ (b : QueryBudget) (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (A : BoundedAdv (AuthAdversary S) b)
      (uIdx : ℕ), uIdx ∈ Finset.range S.N_id →
      ∀ (bIdx : ℕ), bIdx ∈ Finset.range S.N_spk_tot →
        (𝒟[runAuthFgLatchedSim S P A.1 >>= fun x =>
            pure (badAuthFgDh1LatchedAt P b.q_ro uIdx bIdx x.2.2)] {true}).toReal ≤
          GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdvAt true uIdx bIdx S b A)

theorem prob_badAuthFgDh3At_runAuthFgLatchedSim_le_gapDh (S : Setup) (b : QueryBudget)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (AuthAdversary S) b)
    (sIdx : ℕ) (hsIdx : sIdx ∈ Finset.range S.N_send_tot)
    (bIdx : ℕ) (hbIdx : bIdx ∈ Finset.range S.N_spk_tot) :
    (𝒟[runAuthFgLatchedSim S P A.1 >>= fun x =>
        pure (badAuthFgDh3At P b.q_ro sIdx bIdx
          x.2.2.base x.2.2.advRoLog x.2.2.respRecs)] {true}).toReal ≤
      GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdvAt false sIdx bIdx S b A) := by
  rw [evalDist_runAuthFgLatchedSim_badAuthFgDh3At_eq S P b.q_ro sIdx bIdx A.1]
  exact prob_badAuthFgDh3At_le_gapDh S b P hP A sIdx hsIdx bIdx hbIdx

/-- Combined `Pr[badAuthFgAnyLatched]` `GapDH` bound under `runAuthFgLatchedSim`, given per-index `DH1` bounds. -/
theorem prob_badAuthFgAnyLatched_runAuthFgLatchedSim_le_gapDh_of_dh1 (S : Setup)
    (b : QueryBudget) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (A : BoundedAdv (AuthAdversary S) b)
    (hDh1 : ∀ uIdx ∈ Finset.range S.N_id, ∀ bIdx ∈ Finset.range S.N_spk_tot,
      (𝒟[runAuthFgLatchedSim S P A.1 >>= fun x =>
          pure (badAuthFgDh1LatchedAt P b.q_ro uIdx bIdx x.2.2)] {true}).toReal ≤
        GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdvAt true uIdx bIdx S b A)) :
    (𝒟[runAuthFgLatchedSim S P A.1 >>= fun x =>
        pure (badAuthFgAnyLatched P b.q_ro x.2.2)] {true}).toReal ≤
      ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdv4 S b A) :=
  prob_badAuthFgAnyLatched_le_gapDh_of_dh1_dh3 b P A (runAuthFgLatchedSim S P A.1)
    (fun x => x.2.2) hDh1
    (fun sIdx hsIdx bIdx hbIdx =>
      prob_badAuthFgDh3At_runAuthFgLatchedSim_le_gapDh S b P hP A sIdx hsIdx bIdx hbIdx)

def authRoStepInc {S : Setup} : AuthQuery S → ℕ
  | .roQuery _ => 1
  | _          => 0

def authRecvStepInc {S : Setup} : AuthQuery S → ℕ
  | .recvOPK _ _ _ _   => 1
  | .recvNoOPK _ _ _ _ => 1
  | _                  => 0

theorem authRoStepInc_eq_ite {S : Setup} (q : AuthQuery S) :
    authRoStepInc q = (if isAuthRoQuery (Sum.inr q) then 1 else 0) := by
  cases q <;> rfl

theorem authRecvStepInc_eq_ite {S : Setup} (q : AuthQuery S) :
    authRecvStepInc q = (if isAuthRecvQuery (Sum.inr q) then 1 else 0) := by
  cases q <;> rfl

theorem advRoLog_length_pqxdhAuthAdvStageImpl {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvCutoffState S)
    (y : AuthResponse × AuthAdvCutoffState S)
    (hy : y ∈ support ((pqxdhAuthAdvStageImpl stage S P q).run s)) :
    y.2.advRoLog.length = s.advRoLog.length + authRoStepInc q := by
  cases q with
  | roQuery secrets =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | recvOPK k j o msg =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | recvNoOPK k j l msg =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | initPrin u =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | corruptIK u =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | genSPK u j =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | genOPK u j o =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | roRootQuery rk dh =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | revealDhSecrets =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | registerKey sk =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]

theorem respRecs_length_pqxdhAuthAdvStageImpl {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvCutoffState S)
    (y : AuthResponse × AuthAdvCutoffState S)
    (hy : y ∈ support ((pqxdhAuthAdvStageImpl stage S P q).run s)) :
    y.2.respRecs.length = s.respRecs.length + authRecvStepInc q := by
  cases q with
  | roQuery secrets =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | recvOPK k j o msg =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | recvNoOPK k j l msg =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | initPrin u =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | corruptIK u =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | genSPK u j =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | genOPK u j o =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | roRootQuery rk dh =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | revealDhSecrets =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | registerKey sk =>
    unfold pqxdhAuthAdvStageImpl at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]

theorem mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl
    {S : Setup} (stage : AuthHybridStage) (P : Primitives)
    (q : AuthQuery S) (s : AuthAdvLatchedState S)
    (y : AuthResponse × AuthAdvLatchedState S)
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s)) :
    (y.1, y.2.adv) ∈ support ((pqxdhAuthAdvStageImpl stage S P q).run s.adv) := by
  rw [← map_adv_pqxdhAuthAdvLatchedStageImpl stage S P q s, support_map]
  exact ⟨y, hy, rfl⟩

theorem advRoLog_length_pqxdhAuthAdvLatchedStageImpl {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvLatchedState S)
    (y : AuthResponse × AuthAdvLatchedState S)
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s)) :
    y.2.adv.advRoLog.length = s.adv.advRoLog.length + authRoStepInc q :=
  advRoLog_length_pqxdhAuthAdvStageImpl stage P q s.adv (y.1, y.2.adv)
    (mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl stage P q s y hy)

theorem respRecs_length_pqxdhAuthAdvLatchedStageImpl {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvLatchedState S)
    (y : AuthResponse × AuthAdvLatchedState S)
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s)) :
    y.2.adv.respRecs.length = s.adv.respRecs.length + authRecvStepInc q :=
  respRecs_length_pqxdhAuthAdvStageImpl stage P q s.adv (y.1, y.2.adv)
    (mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl stage P q s y hy)

theorem isAuthG3Abort_mono_pqxdhAuthAdvLatchedStageImpl {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvLatchedState S)
    (hAbort : isAuthG3Abort P s.hyb = true)
    (y : AuthResponse × AuthAdvLatchedState S)
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s)) :
    isAuthG3Abort P y.2.hyb = true :=
  isAuthG3Abort_mono_pqxdhAuthAdvStageImpl stage P q s.adv hAbort (y.1, y.2.adv)
    (mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl stage P q s y hy)

def withAuthAdvLatchedRoCache {S : Setup} (c : List (Bytes × DRKey))
    (s : AuthAdvLatchedState S) : AuthAdvLatchedState S :=
  { s with adv := withAuthAdvRoCache c s.adv }

@[simp]
theorem withAuthAdvLatchedRoCache_self {S : Setup} (s : AuthAdvLatchedState S) :
    withAuthAdvLatchedRoCache s.adv.hyb.base.roCache s = s := rfl

@[simp]
theorem withAuthAdvLatchedRoCache_withAuthAdvLatchedRoCache {S : Setup}
    (c1 c2 : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    withAuthAdvLatchedRoCache c1 (withAuthAdvLatchedRoCache c2 s) =
      withAuthAdvLatchedRoCache c1 s := rfl

/-- Two `AuthAdvLatchedState S` states agree on all fields (including `latchedDh1`) except `adv.hyb.base.roCache`. -/
def AuthAdvLatchedAgreeOffRo {S : Setup} (s1 s2 : AuthAdvLatchedState S) : Prop :=
  s1 = withAuthAdvLatchedRoCache s1.adv.hyb.base.roCache s2

theorem AuthAdvLatchedAgreeOffRo.refl {S : Setup} (s : AuthAdvLatchedState S) :
    AuthAdvLatchedAgreeOffRo s s := rfl

theorem AuthAdvLatchedAgreeOffRo.of_withAuthAdvLatchedRoCache {S : Setup}
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    AuthAdvLatchedAgreeOffRo (withAuthAdvLatchedRoCache c s) s := rfl

theorem latchDh1ForPrincipal_withAuthBaseRoCache {S : Setup} (P : Primitives)
    (uVal : ℕ) (c : List (Bytes × DRKey)) (st : AuthState S)
    (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (latched : List (Nat × Nat)) :
    latchDh1ForPrincipal S P uVal (withAuthBaseRoCache c st) advRoLog respRecs latched =
      latchDh1ForPrincipal S P uVal st advRoLog respRecs latched := rfl

theorem pqxdhAuthAdvLatchedStageImpl_corruptIK_withAuthAdvLatchedRoCache
    (S : Setup) (P : Primitives) (u : Fin S.N_id)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.corruptIK u)).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.corruptIK u)).run s) := by
  unfold pqxdhAuthAdvLatchedStageImpl withAuthAdvLatchedRoCache
  dsimp only [StateT.run_mk]
  rw [show (withAuthAdvRoCache c s.adv).hyb.base = withAuthBaseRoCache c s.adv.hyb.base from rfl,
      show (withAuthAdvRoCache c s.adv).advRoLog = s.adv.advRoLog from rfl,
      show (withAuthAdvRoCache c s.adv).respRecs = s.adv.respRecs from rfl,
      latchDh1ForPrincipal_withAuthBaseRoCache,
      pqxdhAuthAdvStageImpl_corruptIK_withAuthAdvRoCache]
  simp [Prod.map, map_eq_bind_pure_comp, bind_assoc]

theorem pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt
    {S : Setup} (P : Primitives) (q : AuthQuery S)
    (hNotCorrupt : ∀ u, q ≠ .corruptIK u)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S)
    (hComm : (pqxdhAuthAdvStageImpl .g3_5 S P q).run (withAuthAdvRoCache c s.adv) =
      Prod.map id (withAuthAdvRoCache c) <$> ((pqxdhAuthAdvStageImpl .g3 S P q).run s.adv)) :
    (pqxdhAuthAdvLatchedStageImpl .g3_5 S P q).run (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl .g3 S P q).run s) := by
  cases q with
  | corruptIK u => exact False.elim (hNotCorrupt u rfl)
  | _ =>
    unfold pqxdhAuthAdvLatchedStageImpl withAuthAdvLatchedRoCache
    dsimp only [StateT.run_mk]
    rw [hComm]
    simp [Prod.map, map_eq_bind_pure_comp, bind_assoc]

theorem relProbUpToBad_of_withAuthAdvLatchedRoCache_comm
    {S : Setup} (P : Primitives) (q : AuthQuery S)
    (Inv : AuthAdvLatchedState S → AuthAdvLatchedState S → Prop)
    (badFg : AuthFgCutoffState S → Bool)
    (s35 s3 : AuthAdvLatchedState S)
    (hAg : AuthAdvLatchedAgreeOffRo s35 s3)
    (hComm : (pqxdhAuthAdvLatchedStageImpl .g3_5 S P q).run
        (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache s3) =
      Prod.map id (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache) <$>
        ((pqxdhAuthAdvLatchedStageImpl .g3 S P q).run s3))
    (hInvPres : ∀ y3 ∈ support ((pqxdhAuthAdvLatchedStageImpl .g3 S P q).run s3),
      badFg y3.2.toFg = false →
      Inv (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache y3.2) y3.2 ∨
      isAuthG3Abort P y3.2.hyb = true) :
    RelProbUpToBad
      (fun y35 y3 =>
        (y35.1 = y3.1 ∧ Inv y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badFg y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P q).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P q).run s3) := by
  rw [hAg, hComm]
  refine RelProbUpToBad.of_map_left
    (Prod.map id (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache)) _
    (fun y3 hy3 hbF => ?_)
  dsimp only [Prod.map, id_eq]
  rcases hInvPres y3 hy3 hbF with hInv' | hAb3'
  · exact Or.inl ⟨rfl, hInv'⟩
  · refine Or.inr ⟨?_, hAb3'⟩
    unfold AuthAdvLatchedState.hyb withAuthAdvLatchedRoCache
    rw [isAuthG3Abort_withAuthAdvRoCache]
    exact hAb3'

end Proofs.SignalPqxdh.Security
