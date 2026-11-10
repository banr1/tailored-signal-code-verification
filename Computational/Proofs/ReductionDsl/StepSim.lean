/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.KindedCost -- proof-setup: allow-public-import

/-!
# Forgetful Simulation Under `IsQueryBoundP` Budget Families

Proves that two one-stage `CostedReduction`s `R'` and `R` related by a pure state projection
`forget` and step invariant `Inv` have identical `OracleComp` evaluations on every adversary
satisfying a family of `IsQueryBoundP` query bounds. Provides the `ForgetSim` bundle, disjoint
per-kind wrappers, and `IsQueryBoundP` combinators (`isQueryBoundP_min`, `isQueryBoundP_or_add`).
-/

public section

set_option autoImplicit false

open OracleSpec OracleComp
open ReductionDsl (
  Sig Ty Expr Comp Env Ops Iface GameCodec
  handlerImpl CostedReduction
  isQueryKind
)

namespace Computational.Proofs.ReductionDsl.StepSim

section QueryBudgetFamily

/-- Lifts a game-query predicate `p : κ → Prop` to `(unifSpec + G).Domain`, ignoring coin queries. -/
@[expose] def isGamePred {κ : Type} {G : OracleSpec κ} (p : κ → Prop) :
    (unifSpec + G).Domain → Prop
  | .inl _ => False
  | .inr t => p t

instance instDecidablePredIsGamePred {κ : Type} {G : OracleSpec κ}
    (p : κ → Prop) [DecidablePred p] :
    DecidablePred (isGamePred (G := G) p) := fun q =>
  match q with
  | .inl _ => isFalse id
  | .inr t => inferInstanceAs (Decidable (p t))

@[simp] theorem isGamePred_inl {κ : Type} {G : OracleSpec κ} (p : κ → Prop) (n : ℕ) :
    isGamePred (G := G) p (.inl n) = False :=
  rfl

@[simp] theorem isGamePred_inr {κ : Type} {G : OracleSpec κ} (p : κ → Prop) (t : κ) :
    isGamePred (G := G) p (.inr t) = p t :=
  rfl

@[simp] theorem isGamePred_eq_isQueryKind {κ : Type} {G : OracleSpec κ} {k : ℕ}
    (kind : κ → Fin k) (i : Fin k) :
    isGamePred (G := G) (fun t => kind t = i) = isQueryKind (G := G) kind i := by
  funext q
  cases q <;> rfl

/-- Increments every counter `j` whose predicate `P j` holds on `t`. -/
@[expose] def bumpPred {κ : Type} {m : ℕ} (P : Fin m → κ → Prop) [∀ j, DecidablePred (P j)]
    (c : Fin m → ℕ) (t : κ) : Fin m → ℕ :=
  fun j => c j + if P j t then 1 else 0

@[simp] theorem bumpPred_apply {κ : Type} {m : ℕ} (P : Fin m → κ → Prop)
    [∀ j, DecidablePred (P j)] (c : Fin m → ℕ) (t : κ) (j : Fin m) :
    bumpPred P c t j = c j + if P j t then 1 else 0 :=
  rfl

/-- Decrements every remaining budget `j` whose predicate `P j` holds on `t`. -/
@[expose] def decPred {κ : Type} {m : ℕ} (P : Fin m → κ → Prop) [∀ j, DecidablePred (P j)]
    (qRem : Fin m → ℕ) (t : κ) : Fin m → ℕ :=
  fun j => if P j t then qRem j - 1 else qRem j

@[simp] theorem decPred_apply {κ : Type} {m : ℕ} (P : Fin m → κ → Prop)
    [∀ j, DecidablePred (P j)] (qRem : Fin m → ℕ) (t : κ) (j : Fin m) :
    decPred P qRem t j = if P j t then qRem j - 1 else qRem j :=
  rfl

theorem decPred_le {κ : Type} {m : ℕ} (P : Fin m → κ → Prop) [∀ j, DecidablePred (P j)]
    (qRem : Fin m → ℕ) (t : κ) (j : Fin m) :
    decPred P qRem t j ≤ qRem j := by
  simp only [decPred_apply]
  split <;> omega

@[expose] def bumpCount {k : ℕ} (c : Fin k → ℕ) (i : Fin k) : Fin k → ℕ :=
  Function.update c i (c i + 1)

@[simp] theorem bumpCount_self {k : ℕ} (c : Fin k → ℕ) (i : Fin k) :
    bumpCount c i i = c i + 1 := by
  simp [bumpCount]

@[simp] theorem bumpCount_of_ne {k : ℕ} (c : Fin k → ℕ) {i j : Fin k} (h : j ≠ i) :
    bumpCount c i j = c j := by
  simp [bumpCount, h]

theorem bumpPred_eq_bumpCount {κ : Type} {k : ℕ} (kind : κ → Fin k) (c : Fin k → ℕ) (t : κ) :
    bumpPred (fun j t' => kind t' = j) c t = bumpCount c (kind t) := by
  funext j
  by_cases h : kind t = j
  · subst h
    simp [bumpPred, bumpCount]
  · have hne : j ≠ kind t := Ne.symm h
    simp [bumpPred, bumpCount, h, hne]

theorem isQueryBoundP_coin_byPred {κ : Type} {G : OracleSpec κ} {α : Type} {m : ℕ}
    {P : Fin m → κ → Prop} [∀ j, DecidablePred (P j)] {qRem : Fin m → ℕ} {num : ℕ}
    {mx : Fin (num + 1) → OracleComp (unifSpec + G) α}
    (h : ∀ j, (liftM ((unifSpec + G).query (.inl num)) >>= mx).IsQueryBoundP
      (isGamePred (G := G) (P j)) (qRem j))
    (u : Fin (num + 1)) :
    ∀ j, (mx u).IsQueryBoundP (isGamePred (G := G) (P j)) (qRem j) := by
  intro j
  have hj := h j
  rw [isQueryBoundP_query_bind_iff] at hj
  simpa [isGamePred] using hj.2 u

theorem isQueryBoundP_game_byPred {κ : Type} {G : OracleSpec κ} {α : Type} {m : ℕ}
    {P : Fin m → κ → Prop} [∀ j, DecidablePred (P j)] {qRem : Fin m → ℕ} {t : κ}
    {mx : G t → OracleComp (unifSpec + G) α}
    (h : ∀ j, (liftM ((unifSpec + G).query (.inr t)) >>= mx).IsQueryBoundP
      (isGamePred (G := G) (P j)) (qRem j)) :
    (∀ j, P j t → 0 < qRem j) ∧
    ∀ (u : G t) (j : Fin m),
      (mx u).IsQueryBoundP (isGamePred (G := G) (P j)) (decPred P qRem t j) := by
  refine ⟨fun j hp => ?_, fun u j => ?_⟩
  · have hj := h j
    rw [isQueryBoundP_query_bind_iff] at hj
    exact hj.1.resolve_left (by simp [isGamePred, hp])
  · have hj := h j
    rw [isQueryBoundP_query_bind_iff] at hj
    have h2 := hj.2 u
    have heq : (if isGamePred (G := G) (P j) (.inr t) then qRem j - 1 else qRem j) =
        decPred P qRem t j := by
      by_cases hp : P j t <;> simp [isGamePred, decPred, hp]
    rwa [heq] at h2

theorem bumpPred_add_decPred_le {κ : Type} {m : ℕ} (P : Fin m → κ → Prop)
    [∀ j, DecidablePred (P j)] {c qRem B : Fin m → ℕ} {t : κ}
    (hc : ∀ j, c j + qRem j ≤ B j) (hpos : ∀ j, P j t → 0 < qRem j) :
    ∀ j, bumpPred P c t j + decPred P qRem t j ≤ B j := by
  intro j
  simp only [bumpPred_apply, decPred_apply]
  by_cases hp : P j t
  · have hcj := hc j
    have hpj := hpos j hp
    simp only [hp, ite_true]
    omega
  · have hcj := hc j
    simp only [hp, ite_false]
    omega

theorem isQueryBoundP_min {ι₀ : Type} {spec : OracleSpec ι₀} {α : Type}
    {oa : OracleComp spec α} {p : ι₀ → Prop} [DecidablePred p] {m₁ m₂ : ℕ}
    (h₁ : oa.IsQueryBoundP p m₁) (h₂ : oa.IsQueryBoundP p m₂) :
    oa.IsQueryBoundP p (min m₁ m₂) := by
  rcases Nat.le_total m₁ m₂ with hle | hle
  · rwa [Nat.min_eq_left hle]
  · rwa [Nat.min_eq_right hle]

/-- Bounds queries satisfying `p` by `m₁ + m₂` when `p` is covered by `p₁ ∨ p₂`. -/
theorem isQueryBoundP_or_add {ι₀ : Type} {spec : OracleSpec ι₀} {α : Type}
    {oa : OracleComp spec α} {p p₁ p₂ : ι₀ → Prop}
    [DecidablePred p] [DecidablePred p₁] [DecidablePred p₂]
    (hcov : ∀ q, p q → p₁ q ∨ p₂ q) {m₁ m₂ : ℕ}
    (h₁ : oa.IsQueryBoundP p₁ m₁) (h₂ : oa.IsQueryBoundP p₂ m₂) :
    oa.IsQueryBoundP p (m₁ + m₂) := by
  induction oa using OracleComp.inductionOn generalizing m₁ m₂ with
  | pure x => exact isQueryBoundP_pure p x (m₁ + m₂)
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h₁ h₂ ⊢
    refine ⟨?_, fun u => ?_⟩
    · by_cases hp : p t
      · right
        rcases hcov t hp with hp₁ | hp₂
        · have := h₁.1.resolve_left (not_not.mpr hp₁); omega
        · have := h₂.1.resolve_left (not_not.mpr hp₂); omega
      · exact Or.inl hp
    · refine (ih u (h₁.2 u) (h₂.2 u)).mono ?_
      by_cases hp : p t
      · rcases hcov t hp with hp₁ | hp₂
        · have := h₁.1.resolve_left (not_not.mpr hp₁)
          simp only [hp, hp₁, ite_true]
          split <;> omega
        · have := h₂.1.resolve_left (not_not.mpr hp₂)
          simp only [hp, hp₂, ite_true]
          split <;> omega
      · simp only [hp, ite_false]
        split <;> split <;> omega

theorem bind_congr_support {ι₀ : Type} {spec : OracleSpec ι₀} {α β : Type}
    (oa : OracleComp spec α) (f g : α → OracleComp spec β)
    (h : ∀ x ∈ support oa, f x = g x) : oa >>= f = oa >>= g :=
  OracleComp.bind_congr_of_forall_mem_support oa h

theorem mem_support_simulateQ {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0} ι₁} {S₂ : OracleSpec ι₂}
    {α : Type} (impl : QueryImpl S₁ (OracleComp S₂)) (oa : OracleComp S₁ α) {x : α}
    (hx : x ∈ support (simulateQ impl oa)) : x ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simpa [simulateQ_pure] using hx
  | query_bind q mx ih =>
    rw [simulateQ_query_bind, mem_support_bind_iff] at hx
    obtain ⟨u, -, hxu⟩ := hx
    rw [mem_support_bind_iff]
    exact ⟨u, mem_support_query q u, ih u hxu⟩

end QueryBudgetFamily

section OneStage

variable {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
  {G : OracleSpec κ} {C : GameCodec S G}
  {rIn aIn aOut out : Ty S}

/-- Forgetful `StateT` simulation for `handlerImpl` under query-budget family `(P, B)`. -/
theorem simulateQ_handlerImpl_forget
    {σ' σ : Ty S}
    (h' : Comp O I [σ', C.Q] (.prod C.R σ'))
    (h : Comp O I [σ, C.Q] (.prod C.R σ))
    (forget : σ'.denote → σ.denote)
    {m : ℕ} (P : Fin m → κ → Prop) [∀ j, DecidablePred (P j)] (B : Fin m → ℕ)
    (Inv : (Fin m → ℕ) → σ'.denote → Prop)
    (hStep : ∀ (c : Fin m → ℕ) (s' : σ'.denote) (t : κ),
      (∀ j, c j ≤ B j) →
      (∀ j, P j t → c j + 1 ≤ B j) →
      Inv c s' →
      Prod.map id forget <$> h'.eval (.cons s' (.cons (C.qenc t) .nil)) =
        h.eval (.cons (forget s') (.cons (C.qenc t) .nil)) ∧
      ∀ p ∈ support (h'.eval (.cons s' (.cons (C.qenc t) .nil))),
        Inv (bumpPred P c t) p.2)
    {α : Type} (oa : OracleComp (unifSpec + G) α) :
    ∀ (c qRem : Fin m → ℕ),
      (∀ j, oa.IsQueryBoundP (isGamePred (G := G) (P j)) (qRem j)) →
      (∀ j, c j + qRem j ≤ B j) →
      ∀ (s' : σ'.denote), Inv c s' →
        Prod.map id forget <$> ((simulateQ (handlerImpl (C := C) h') oa).run s') =
          (simulateQ (handlerImpl (C := C) h) oa).run (forget s') ∧
        ∀ bs' ∈ support ((simulateQ (handlerImpl (C := C) h') oa).run s'),
          ∃ c', (∀ j, c' j ≤ B j) ∧ Inv c' bs'.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c qRem _ hc s' hInv
    refine ⟨by simp [simulateQ_pure], ?_⟩
    intro bs' hbs'
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hbs'
    subst hbs'
    exact ⟨c, fun j => Nat.le_trans (Nat.le_add_right _ _) (hc j), hInv⟩
  | query_bind q mx ih =>
    intro c qRem hA hc s' hInv
    cases q with
    | inl num =>
      have hcont := isQueryBoundP_coin_byPred hA
      simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
        monadLift_self, handlerImpl, StateT.run_bind, StateT.run_lift, map_bind,
        bind_assoc, pure_bind, id_eq]
      refine ⟨?_, ?_⟩
      · refine bind_congr fun u => (ih u c qRem (hcont u) hc s' hInv).1
      · intro bs' hbs'
        rw [mem_support_bind_iff] at hbs'
        obtain ⟨u, -, hbs'⟩ := hbs'
        exact (ih u c qRem (hcont u) hc s' hInv).2 bs' hbs'
    | inr t =>
      obtain ⟨hpos, hcont⟩ := isQueryBoundP_game_byPred hA
      have hcB : ∀ j, c j ≤ B j := fun j => Nat.le_trans (Nat.le_add_right _ _) (hc j)
      have hroom : ∀ j, P j t → c j + 1 ≤ B j := fun j hp => by
        have := hc j; have := hpos j hp; omega
      have hc' : ∀ j, bumpPred P c t j + decPred P qRem t j ≤ B j :=
        bumpPred_add_decPred_le P hc hpos
      obtain ⟨hEq, hPres⟩ := hStep c s' t hcB hroom hInv
      simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
        monadLift_self, handlerImpl, StateT.run_bind, StateT.run_mk, map_bind, bind_assoc,
        pure_bind, id_eq]
      refine ⟨?_, ?_⟩
      · rw [← hEq, bind_map_left]
        refine bind_congr_support _ _ _ fun p hp => ?_
        dsimp only [Prod.map, id_eq]
        exact (ih (C.rdec t p.1) (bumpPred P c t) (decPred P qRem t)
          (hcont (C.rdec t p.1)) hc' p.2 (hPres p hp)).1
      · intro bs' hbs'
        rw [mem_support_bind_iff] at hbs'
        obtain ⟨p, hp, hbs'⟩ := hbs'
        exact (ih (C.rdec t p.1) (bumpPred P c t) (decPred P qRem t)
          (hcont (C.rdec t p.1)) hc' p.2 (hPres p hp)).2 bs' hbs'

/-- Two one-stage `CostedReduction`s related by `forget` and step invariant `Inv` have equal
`eval` on every adversary bounded by `(P, B)`. -/
theorem costedReduction_eval_eq_of_forgetSim
    (R' R : CostedReduction O I G C rIn aIn aOut out)
    (forget : R'.σ.denote → R.σ.denote)
    {m : ℕ} (P : Fin m → κ → Prop) [∀ j, DecidablePred (P j)] (B : Fin m → ℕ)
    (x : rIn.denote)
    (Inv : (Fin m → ℕ) → R'.σ.denote → Prop)
    (hInit :
      Prod.map id forget <$> R'.init.eval (.cons x .nil) = R.init.eval (.cons x .nil) ∧
      ∀ as' ∈ support (R'.init.eval (.cons x .nil)), Inv 0 as'.2)
    (hHandle : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (t : κ),
      (∀ j, c j ≤ B j) →
      (∀ j, P j t → c j + 1 ≤ B j) →
      Inv c s' →
      Prod.map id forget <$> R'.handle.eval (.cons s' (.cons (C.qenc t) .nil)) =
        R.handle.eval (.cons (forget s') (.cons (C.qenc t) .nil)) ∧
      ∀ p ∈ support (R'.handle.eval (.cons s' (.cons (C.qenc t) .nil))),
        Inv (bumpPred P c t) p.2)
    (hFinish : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (b : aOut.denote),
      (∀ j, c j ≤ B j) →
      Inv c s' →
      R'.finish.eval (.cons s' (.cons b .nil)) =
        R.finish.eval (.cons (forget s') (.cons b .nil)))
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hA : ∀ a j, (A a).IsQueryBoundP (isGamePred (G := G) (P j)) (B j)) :
    R'.eval A x = R.eval A x := by
  unfold CostedReduction.eval CostedReduction.impl
  rw [← hInit.1, bind_map_left]
  refine bind_congr_support _ _ _ fun as' has' => ?_
  have hSim := simulateQ_handlerImpl_forget R'.handle R.handle forget P B Inv hHandle
    (A as'.1) 0 B (hA as'.1) (fun j => by simp) as'.2 (hInit.2 as' has')
  dsimp only [Prod.map, id_eq]
  rw [← hSim.1, bind_map_left]
  refine bind_congr_support _ _ _ fun bs' hbs' => ?_
  obtain ⟨c', hc', hInv'⟩ := hSim.2 bs' hbs'
  exact hFinish c' bs'.2 bs'.1 hc' hInv'

/-- Step-simulation obligations relating two one-stage `CostedReduction`s via `forget` and
invariant `Inv` under query-budget family `(P, B)`. -/
structure ForgetSim
    (R' R : CostedReduction O I G C rIn aIn aOut out)
    (forget : R'.σ.denote → R.σ.denote)
    {m : ℕ} (P : Fin m → κ → Prop) [∀ j, DecidablePred (P j)] (B : Fin m → ℕ)
    (x : rIn.denote)
    (Inv : (Fin m → ℕ) → R'.σ.denote → Prop) : Prop where
  hInit :
    Prod.map id forget <$> R'.init.eval (.cons x .nil) = R.init.eval (.cons x .nil) ∧
    ∀ as' ∈ support (R'.init.eval (.cons x .nil)), Inv 0 as'.2
  hHandle : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (t : κ),
    (∀ j, c j ≤ B j) →
    (∀ j, P j t → c j + 1 ≤ B j) →
    Inv c s' →
    Prod.map id forget <$> R'.handle.eval (.cons s' (.cons (C.qenc t) .nil)) =
      R.handle.eval (.cons (forget s') (.cons (C.qenc t) .nil)) ∧
    ∀ p ∈ support (R'.handle.eval (.cons s' (.cons (C.qenc t) .nil))),
      Inv (bumpPred P c t) p.2
  hFinish : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (b : aOut.denote),
    (∀ j, c j ≤ B j) →
    Inv c s' →
    R'.finish.eval (.cons s' (.cons b .nil)) =
      R.finish.eval (.cons (forget s') (.cons b .nil))

/-- Deduces `R'.eval A x = R.eval A x` from `ForgetSim` for any `(P, B)`-bounded adversary `A`. -/
theorem ForgetSim.eval_eq
    {R' R : CostedReduction O I G C rIn aIn aOut out}
    {forget : R'.σ.denote → R.σ.denote}
    {m : ℕ} {P : Fin m → κ → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → ℕ}
    {x : rIn.denote}
    {Inv : (Fin m → ℕ) → R'.σ.denote → Prop}
    (hSim : ForgetSim R' R forget P B x Inv)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hA : ∀ a j, (A a).IsQueryBoundP (isGamePred (G := G) (P j)) (B j)) :
    R'.eval A x = R.eval A x :=
  costedReduction_eval_eq_of_forgetSim R' R forget P B x Inv
    hSim.hInit hSim.hHandle hSim.hFinish A hA

theorem ForgetSim.simulateQ_eval_eq
    {ι' : Type} {T' : OracleSpec ι'}
    (impl : QueryImpl T (OracleComp T'))
    {R' R : CostedReduction O I G C rIn aIn aOut out}
    {forget : R'.σ.denote → R.σ.denote}
    {m : ℕ} {P : Fin m → κ → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → ℕ}
    {x : rIn.denote}
    {Inv : (Fin m → ℕ) → R'.σ.denote → Prop}
    (hSim : ForgetSim R' R forget P B x Inv)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hA : ∀ a j, (A a).IsQueryBoundP (isGamePred (G := G) (P j)) (B j)) :
    simulateQ impl (R'.eval A x) = simulateQ impl (R.eval A x) :=
  congrArg (simulateQ impl) (hSim.eval_eq A hA)

/-- Constructs `ForgetSim` from disjoint per-kind obligations (`P i t := kind t = i`). -/
theorem ForgetSim.ofByKind
    (R' R : CostedReduction O I G C rIn aIn aOut out)
    (forget : R'.σ.denote → R.σ.denote)
    {k : ℕ} (kind : κ → Fin k) (counts : Fin k → ℕ)
    (x : rIn.denote)
    (Inv : (Fin k → ℕ) → R'.σ.denote → Prop)
    (hInit :
      Prod.map id forget <$> R'.init.eval (.cons x .nil) = R.init.eval (.cons x .nil) ∧
      ∀ as' ∈ support (R'.init.eval (.cons x .nil)), Inv 0 as'.2)
    (hHandle : ∀ (c : Fin k → ℕ) (s' : R'.σ.denote) (t : κ),
      (∀ i, c i ≤ counts i) →
      c (kind t) + 1 ≤ counts (kind t) →
      Inv c s' →
      Prod.map id forget <$> R'.handle.eval (.cons s' (.cons (C.qenc t) .nil)) =
        R.handle.eval (.cons (forget s') (.cons (C.qenc t) .nil)) ∧
      ∀ p ∈ support (R'.handle.eval (.cons s' (.cons (C.qenc t) .nil))),
        Inv (bumpCount c (kind t)) p.2)
    (hFinish : ∀ (c : Fin k → ℕ) (s' : R'.σ.denote) (b : aOut.denote),
      (∀ i, c i ≤ counts i) →
      Inv c s' →
      R'.finish.eval (.cons s' (.cons b .nil)) =
        R.finish.eval (.cons (forget s') (.cons b .nil))) :
    ForgetSim R' R forget (fun i t => kind t = i) counts x Inv where
  hInit := hInit
  hHandle := fun c₀ s₀ t hc₀ hroom₀ hInv₀ => by
    rw [bumpPred_eq_bumpCount]; exact hHandle c₀ s₀ t hc₀ (hroom₀ (kind t) rfl) hInv₀
  hFinish := hFinish

theorem simulateQ_handlerImpl_forget_byKind
    {σ' σ : Ty S}
    (h' : Comp O I [σ', C.Q] (.prod C.R σ'))
    (h : Comp O I [σ, C.Q] (.prod C.R σ))
    (forget : σ'.denote → σ.denote)
    {k : ℕ} (kind : κ → Fin k) (counts : Fin k → ℕ)
    (Inv : (Fin k → ℕ) → σ'.denote → Prop)
    (hStep : ∀ (c : Fin k → ℕ) (s' : σ'.denote) (t : κ),
      (∀ i, c i ≤ counts i) →
      c (kind t) + 1 ≤ counts (kind t) →
      Inv c s' →
      Prod.map id forget <$> h'.eval (.cons s' (.cons (C.qenc t) .nil)) =
        h.eval (.cons (forget s') (.cons (C.qenc t) .nil)) ∧
      ∀ p ∈ support (h'.eval (.cons s' (.cons (C.qenc t) .nil))),
        Inv (bumpCount c (kind t)) p.2)
    {α : Type} (oa : OracleComp (unifSpec + G) α)
    (c qRem : Fin k → ℕ)
    (hA : ∀ i, oa.IsQueryBoundP (isQueryKind (G := G) kind i) (qRem i))
    (hc : ∀ i, c i + qRem i ≤ counts i)
    (s' : σ'.denote) (hInv : Inv c s') :
    Prod.map id forget <$> ((simulateQ (handlerImpl (C := C) h') oa).run s') =
      (simulateQ (handlerImpl (C := C) h) oa).run (forget s') ∧
    ∀ bs' ∈ support ((simulateQ (handlerImpl (C := C) h') oa).run s'),
      ∃ c', (∀ i, c' i ≤ counts i) ∧ Inv c' bs'.2 := by
  refine simulateQ_handlerImpl_forget h' h forget (fun i t => kind t = i) counts Inv
    (fun c₀ s₀ t hc₀ hroom₀ hInv₀ => ?_) oa c qRem
    (fun i => by simpa [isGamePred_eq_isQueryKind] using hA i) hc s' hInv
  rw [bumpPred_eq_bumpCount]
  exact hStep c₀ s₀ t hc₀ (hroom₀ (kind t) rfl) hInv₀

theorem costedReduction_eval_eq_of_forgetSim_byKind
    (R' R : CostedReduction O I G C rIn aIn aOut out)
    (forget : R'.σ.denote → R.σ.denote)
    {k : ℕ} (kind : κ → Fin k) (counts : Fin k → ℕ)
    (x : rIn.denote)
    (Inv : (Fin k → ℕ) → R'.σ.denote → Prop)
    (hInit :
      Prod.map id forget <$> R'.init.eval (.cons x .nil) = R.init.eval (.cons x .nil) ∧
      ∀ as' ∈ support (R'.init.eval (.cons x .nil)), Inv 0 as'.2)
    (hHandle : ∀ (c : Fin k → ℕ) (s' : R'.σ.denote) (t : κ),
      (∀ i, c i ≤ counts i) →
      c (kind t) + 1 ≤ counts (kind t) →
      Inv c s' →
      Prod.map id forget <$> R'.handle.eval (.cons s' (.cons (C.qenc t) .nil)) =
        R.handle.eval (.cons (forget s') (.cons (C.qenc t) .nil)) ∧
      ∀ p ∈ support (R'.handle.eval (.cons s' (.cons (C.qenc t) .nil))),
        Inv (bumpCount c (kind t)) p.2)
    (hFinish : ∀ (c : Fin k → ℕ) (s' : R'.σ.denote) (b : aOut.denote),
      (∀ i, c i ≤ counts i) →
      Inv c s' →
      R'.finish.eval (.cons s' (.cons b .nil)) =
        R.finish.eval (.cons (forget s') (.cons b .nil)))
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hA : ∀ a i, (A a).IsQueryBoundP (isQueryKind (G := G) kind i) (counts i)) :
    R'.eval A x = R.eval A x := by
  refine costedReduction_eval_eq_of_forgetSim R' R forget (fun i t => kind t = i) counts x Inv
    hInit (fun c₀ s₀ t hc₀ hroom₀ hInv₀ => ?_) hFinish A
    (fun a i => by simpa [isGamePred_eq_isQueryKind] using hA a i)
  rw [bumpPred_eq_bumpCount]
  exact hHandle c₀ s₀ t hc₀ (hroom₀ (kind t) rfl) hInv₀

end OneStage

section ToyTest

@[expose] def toyCacheSpec : OracleSpec (ℕ ⊕ ℕ) := fun _ => Bool

@[expose] def toyCacheCodec (S : Sig) : GameCodec S toyCacheSpec where
  Q := .sum .nat .nat
  R := .bool
  qenc := id
  rdec := fun _ b => b
  codecCost := 1

@[expose] def toyCachePred (j : Fin 2) (q : ℕ ⊕ ℕ) : Prop :=
  if j = 0 then q.isLeft = true else True

instance instDecidablePredToyCachePred (j : Fin 2) : DecidablePred (toyCachePred j) :=
  fun q => by unfold toyCachePred; infer_instance

@[expose] def toyListCacheOld {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (q_total : ℕ) :
    CostedReduction O I toyCacheSpec (toyCacheCodec S) .unit .unit .bool .bool where
  σ := .list .nat
  init := .ret (.pair .unit .nil)
  handle :=
    .caseSum .v1
      (.ite (.anyB q_total .v1 (.eqN .v0 .v1))
        (.ret (.pair (.bool true) .v1))
        (.ret (.pair (.bool false) (.cons .v0 .v1))))
      (.ret (.pair (.bool false) .v1))
  finish :=
    .ret (.and .v1 (.anyB q_total .v0 (.eqN .v0 (.nat 0))))

@[expose] def toyListCacheNew {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (q_total n_on : ℕ) :
    CostedReduction O I toyCacheSpec (toyCacheCodec S) .unit .unit .bool .bool where
  σ := .prod (.list .nat) .nat
  init := .ret (.pair .unit (.pair .nil (.nat 0)))
  handle :=
    .caseSum .v1
      (.ite (.anyB (min q_total n_on) (.fst .v1) (.eqN .v0 .v1))
        (.ret (.pair (.bool true) (.pair (.fst .v1) (.add (.snd .v1) (.nat 1)))))
        (.ret (.pair (.bool false) (.pair (.cons .v0 (.fst .v1)) (.add (.snd .v1) (.nat 1))))))
      (.ret (.pair (.bool false) .v1))
  finish :=
    .ret (.and .v1 (.anyB (min q_total n_on) (.fst .v0) (.eqN .v0 (.nat 0))))

@[expose] def toyListCacheInv (c : Fin 2 → ℕ) (s' : List ℕ × ℕ) : Prop :=
  s'.2 = c 0 ∧ s'.1.length ≤ c 0

/-- `toyListCacheNew` and `toyListCacheOld` agree on every adversary within the online and total
query budgets. -/
theorem toyListCacheNew_eval_eq_toyListCacheOld
    {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (q_total n_on : ℕ)
    (A : Unit → OracleComp (unifSpec + toyCacheSpec) Bool)
    (hOn : (A ()).IsQueryBoundP (isGamePred (G := toyCacheSpec) (fun q => q.isLeft = true))
      (min q_total n_on))
    (hTot : (A ()).IsQueryBoundP (isGamePred (G := toyCacheSpec) (fun _ => True)) q_total) :
    (toyListCacheNew (O := O) (I := I) q_total n_on).eval A () =
      (toyListCacheOld (O := O) (I := I) q_total).eval A () := by
  let B : Fin 2 → ℕ := ![min q_total n_on, q_total]
  refine costedReduction_eval_eq_of_forgetSim
    (toyListCacheNew q_total n_on) (toyListCacheOld q_total) Prod.fst
    toyCachePred B () toyListCacheInv ?_ ?_ ?_ A ?_
  · refine ⟨by simp [toyListCacheNew, toyListCacheOld, Comp.eval, Expr.eval, Prod.map], ?_⟩
    intro as' has'
    simp only [toyListCacheNew, Comp.eval, Expr.eval, support_pure] at has'
    subst has'
    simp [toyListCacheInv]
  · intro c ⟨cache, ctr⟩ t hc hroom ⟨hctr, hlen⟩
    dsimp only at hctr hlen
    have hc0 : c 0 ≤ min q_total n_on := hc 0
    have htake_new : cache.take (min q_total n_on) = cache :=
      List.take_of_length_le (Nat.le_trans hlen hc0)
    have htake_old : cache.take q_total = cache :=
      List.take_of_length_le (Nat.le_trans hlen (Nat.le_trans hc0 (Nat.min_le_left _ _)))
    cases t with
    | inl key =>
      have hroom0 : c 0 + 1 ≤ min q_total n_on := hroom 0 rfl
      simp only [toyListCacheNew, toyListCacheOld, toyCacheCodec, Comp.eval, Expr.eval, Env.get,
        Expr.v0, Expr.v1, htake_new, htake_old]
      by_cases hhit : (cache.any fun x => decide (x = key)) = true
      · refine ⟨by simp [hhit, Prod.map], ?_⟩
        intro p hp
        simp [hhit] at hp
        subst hp
        simp only [toyListCacheInv, bumpPred_apply, toyCachePred, ↓reduceIte, Sum.isLeft_inl]
        omega
      · simp only [Bool.not_eq_true] at hhit
        refine ⟨by simp [hhit, Prod.map], ?_⟩
        intro p hp
        simp [hhit] at hp
        subst hp
        simp only [toyListCacheInv, bumpPred_apply, toyCachePred, ↓reduceIte, Sum.isLeft_inl,
          List.length_cons]
        omega
    | inr tag =>
      simp only [toyListCacheNew, toyListCacheOld, toyCacheCodec, Comp.eval, Expr.eval, Env.get,
        Expr.v1]
      refine ⟨by simp [Prod.map], ?_⟩
      intro p hp
      simp at hp
      subst hp
      simp only [toyListCacheInv, bumpPred_apply, toyCachePred, ↓reduceIte, Sum.isLeft_inr,
        Bool.false_eq_true, Nat.add_zero]
      exact ⟨hctr, hlen⟩
  · intro c ⟨cache, ctr⟩ b hc ⟨_, hlen⟩
    have hc0 : c 0 ≤ min q_total n_on := hc 0
    have htake_new : cache.take (min q_total n_on) = cache :=
      List.take_of_length_le (Nat.le_trans hlen hc0)
    have htake_old : cache.take q_total = cache :=
      List.take_of_length_le (Nat.le_trans hlen (Nat.le_trans hc0 (Nat.min_le_left _ _)))
    simp [toyListCacheNew, toyListCacheOld, Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v1,
      htake_new, htake_old]
  · intro ⟨⟩ j
    fin_cases j
    · convert hOn using 2
      · ext q; simp [toyCachePred]
      · simp [B]
    · convert hTot using 2
      · ext q; simp [toyCachePred]
      · simp [B]

@[expose] def toyWitnessAdv : Unit → OracleComp (unifSpec + toyCacheSpec) Bool := fun () => do
  let b₁ ← liftM ((unifSpec + toyCacheSpec).query (.inr (.inl 0)))
  let _ ← liftM ((unifSpec + toyCacheSpec).query (.inr (.inr 9)))
  let b₂ ← liftM ((unifSpec + toyCacheSpec).query (.inr (.inl 0)))
  return (!b₁ && b₂)

theorem toyListCacheNew_witness_nonvacuous
    {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T} :
    (toyWitnessAdv ()).IsQueryBoundP (isGamePred (G := toyCacheSpec) (fun q => q.isLeft = true))
      (min 5 2) ∧
    (toyWitnessAdv ()).IsQueryBoundP (isGamePred (G := toyCacheSpec) (fun _ => True)) 5 ∧
    (toyListCacheNew (O := O) (I := I) 5 2).eval toyWitnessAdv () =
      (toyListCacheOld (O := O) (I := I) 5).eval toyWitnessAdv () := by
  have hOn : (toyWitnessAdv ()).IsQueryBoundP
      (isGamePred (G := toyCacheSpec) (fun q => q.isLeft = true)) (min 5 2) := by
    unfold toyWitnessAdv
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr (by decide), fun b₁ => ?_⟩
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [isGamePred]), fun _ => ?_⟩
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr (by decide), fun b₂ => ?_⟩
    exact isQueryBoundP_pure _ _ _
  have hTot : (toyWitnessAdv ()).IsQueryBoundP
      (isGamePred (G := toyCacheSpec) (fun _ => True)) 5 := by
    unfold toyWitnessAdv
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr (by decide), fun b₁ => ?_⟩
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr (by decide), fun _ => ?_⟩
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr (by decide), fun b₂ => ?_⟩
    exact isQueryBoundP_pure _ _ _
  exact ⟨hOn, hTot, toyListCacheNew_eval_eq_toyListCacheOld 5 2 toyWitnessAdv hOn hTot⟩

end ToyTest

end Computational.Proofs.ReductionDsl.StepSim
