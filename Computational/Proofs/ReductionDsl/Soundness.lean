/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Soundness of Static Query Bounds

Proves that static query counts (`Comp.queries`, `CostedReduction.totalQueries`, and two-stage /
coin-fueled variants) upper-bound target oracle queries during evaluation.
-/

@[expose] public section

namespace ReductionDsl

open OracleComp

variable {S : Sig} {ι : Type} {T : OracleSpec ι} {O : Ops S} {I : Iface S T}

theorem iterM_queryBound {α : Type} {P : ι → Prop} [DecidablePred P] (f : α → OracleComp T α)
    (k : ℕ) (hf : ∀ a, (f a).IsQueryBoundP P k) :
    ∀ n a, (iterM f n a).IsQueryBoundP P (n * k)
  | 0, a => by simp [iterM]
  | n + 1, a => by
    simp only [iterM]
    have := isQueryBoundP_bind (hf a) (fun z _ => iterM_queryBound f k hf n z)
    exact this.mono (by rw [Nat.succ_mul]; omega)

section ListLoops

variable {α β : Type} {P : ι → Prop} [DecidablePred P] {k : ℕ}

theorem findML_queryBound (p : α → OracleComp T Bool) (hp : ∀ x, (p x).IsQueryBoundP P k) :
    ∀ xs : List α, (findML p xs).IsQueryBoundP P (xs.length * k)
  | [] => by simp [findML]
  | x :: xs => by
    simp only [findML]
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm]
    refine isQueryBoundP_bind (hp x) (fun b _ => ?_)
    split
    · exact (isQueryBoundP_pure (spec := T) P _ 0).mono (Nat.zero_le _)
    · exact findML_queryBound p hp xs

theorem anyML_queryBound (p : α → OracleComp T Bool) (hp : ∀ x, (p x).IsQueryBoundP P k) :
    ∀ xs : List α, (anyML p xs).IsQueryBoundP P (xs.length * k)
  | [] => by simp [anyML]
  | x :: xs => by
    simp only [anyML]
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm]
    refine isQueryBoundP_bind (hp x) (fun b _ => ?_)
    split
    · exact (isQueryBoundP_pure (spec := T) P _ 0).mono (Nat.zero_le _)
    · exact anyML_queryBound p hp xs

theorem mapML_queryBound (f : α → OracleComp T β) (hf : ∀ x, (f x).IsQueryBoundP P k) :
    ∀ xs : List α, (mapML f xs).IsQueryBoundP P (xs.length * k)
  | [] => by simp [mapML]
  | x :: xs => by
    simp only [mapML]
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact isQueryBoundP_bind (hf x) (fun y _ =>
      (isQueryBoundP_bind (mapML_queryBound f hf xs) (fun ys _ =>
        isQueryBoundP_pure (spec := T) P (y :: ys) 0)).mono (by omega))

theorem consumeFirstML_queryBound (p : α → OracleComp T Bool) (mk : α → α)
    (hp : ∀ x, (p x).IsQueryBoundP P k) :
    ∀ xs : List α, (consumeFirstML p mk xs).IsQueryBoundP P (xs.length * k)
  | [] => by simp [consumeFirstML]
  | x :: xs => by
    simp only [consumeFirstML]
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm]
    refine isQueryBoundP_bind (hp x) (fun b _ => ?_)
    split
    · exact (isQueryBoundP_pure (spec := T) P _ 0).mono (Nat.zero_le _)
    · exact isQueryBoundP_bind (consumeFirstML_queryBound p mk hp xs)
        (fun r _ => isQueryBoundP_pure (spec := T) P _ 0) |>.mono (by omega)

theorem foldML_queryBound (f : α → β → OracleComp T β) (hf : ∀ x b, (f x b).IsQueryBoundP P k) :
    ∀ (b : β) (xs : List α), (foldML f b xs).IsQueryBoundP P (xs.length * k)
  | b, [] => by simp [foldML]
  | b, x :: xs => by
    simp only [foldML]
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact isQueryBoundP_bind (hf x b) (fun b' _ => foldML_queryBound f hf b' xs)

theorem take_mul_le (xs : List α) (K k : ℕ) : (xs.take K).length * k ≤ K * k :=
  Nat.mul_le_mul_right _ (by simp)

end ListLoops

theorem liftP_queryBound (P : ι → Prop) [DecidablePred P] (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    {α : Type} (p : ProbComp α) : (I.liftP p).IsQueryBoundP P 0 := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [Iface.liftP]
  | query_bind t mx ih =>
    simp only [Iface.liftP, simulateQ_query_bind] at ih ⊢
    exact isQueryBoundP_bind (hU t) (fun u _ => ih u)

/-- Evaluating `c` makes at most `c.queries w ws` target `P`-queries. -/
theorem Comp.queryBound_eval (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ)
    (ws : I.smp.Samp → ℕ) (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    ∀ ρ : Env Γ, (c.eval ρ).IsQueryBoundP P (c.queries w ws) := by
  induction c with
  | ret e => intro ρ; simp [Comp.eval]
  | bind c k ihc ihk =>
    intro ρ
    exact isQueryBoundP_bind (ihc ρ) (fun x _ => ihk (.cons x ρ))
  | ite b c d ihc ihd =>
    intro ρ; simp only [Comp.eval, Comp.queries]
    split
    · exact (ihc ρ).mono (le_max_left _ _)
    · exact (ihd ρ).mono (le_max_right _ _)
  | caseOpt e n s ihn ihs =>
    intro ρ; simp only [Comp.eval, Comp.queries]
    split
    · exact (ihn ρ).mono (le_max_left _ _)
    · exact (ihs _).mono (le_max_right _ _)
  | caseSum e l r ihl ihr =>
    intro ρ; simp only [Comp.eval, Comp.queries]
    split
    · exact (ihl _).mono (le_max_left _ _)
    · exact (ihr _).mono (le_max_right _ _)
  | sample s e => intro ρ; exact (liftP_queryBound P hU _).mono (Nat.zero_le _)
  | query g e =>
    intro ρ
    simp only [Comp.eval, Comp.queries, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    intro h; have := hw g _ h; omega
  | iter n e body ihb =>
    intro ρ
    exact iterM_queryBound _ _ (fun a => ihb (.cons a ρ)) n _
  | findM K l p ihp =>
    intro ρ; simp only [Comp.eval, Comp.queries]
    exact (findML_queryBound _ (fun x => ihp (.cons x ρ)) _).mono (take_mul_le _ _ _)
  | anyM K l p ihp =>
    intro ρ; simp only [Comp.eval, Comp.queries]
    exact (anyML_queryBound _ (fun x => ihp (.cons x ρ)) _).mono (take_mul_le _ _ _)
  | mapM K l f ihf =>
    intro ρ; simp only [Comp.eval, Comp.queries]
    exact (mapML_queryBound _ (fun x => ihf (.cons x ρ)) _).mono (take_mul_le _ _ _)
  | consumeFirstM K l p mk ihp =>
    intro ρ; simp only [Comp.eval, Comp.queries]
    exact (consumeFirstML_queryBound _ _ (fun x => ihp (.cons x ρ)) _).mono (take_mul_le _ _ _)
  | foldM K l z f ihf =>
    intro ρ; simp only [Comp.eval, Comp.queries]
    exact (foldML_queryBound _ (fun x b => ihf (.cons x (.cons b ρ))) _ _).mono
      (take_mul_le _ _ _)

theorem simulateQ_run_StateT_of_step_le {κ : Type} {spec : OracleSpec κ} {σ α : Type}
    {p : κ → Prop} [DecidablePred p] {q : ι → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ (OracleComp T))} {k : ℕ}
    (hstep : ∀ t s, ((impl t).run s).IsQueryBoundP q (if p t then k else 0)) :
    ∀ {oa : OracleComp spec α} {n : ℕ}, oa.IsQueryBoundP p n →
      ∀ s, ((simulateQ impl oa).run s).IsQueryBoundP q (n * k) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x => intro n _ s; simp [simulateQ_pure]
  | query_bind t mx ih =>
    intro n h s
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_query_bind, StateT.run_bind]
    have hbind := isQueryBoundP_bind (hstep t s) (fun x _ => ih x.1 (h.2 x.1) x.2)
    refine hbind.mono ?_
    by_cases hp : p t
    · have : 0 < n := h.1.resolve_left (not_not.mpr hp)
      simp only [hp, ite_true]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp [Nat.succ_mul]; omega
    · simp [hp]

/-- The game-query predicate on `A`'s oracles. -/
def isGameQuery {κ : Type} {G : OracleSpec κ} : (unifSpec + G).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance {κ : Type} {G : OracleSpec κ} : DecidablePred (isGameQuery (G := G)) := fun t =>
  match t with
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- Evaluating `R` on an adversary making at most `q` game queries makes at most
`R.totalQueries w ws q` target `P`-queries. -/
theorem CostedReduction.queryBound_eval {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out) (P : ι → Prop)
    [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (q : ℕ)
    (hA : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := G)) q) (x : rIn.denote) :
    (R.eval A x).IsQueryBoundP P (R.totalQueries w ws q) := by
  have hstep : ∀ t s, ((R.impl t).run s).IsQueryBoundP P
      (if isGameQuery t then R.handle.queries w ws else 0) := by
    intro t s
    cases t with
    | inl n =>
      have := isQueryBoundP_bind (n := 0) (m := 0) (hU n)
        (fun a _ => isQueryBoundP_pure (spec := T) P (a, s) 0)
      simpa [CostedReduction.impl, handlerImpl, isGameQuery] using this
    | inr t =>
      have := isQueryBoundP_bind
        (Comp.queryBound_eval P w ws hw hU R.handle (.cons s (.cons (C.qenc t) .nil)))
        (fun x _ => isQueryBoundP_pure (spec := T) P (C.rdec t x.1, x.2) 0)
      simpa [CostedReduction.impl, handlerImpl, isGameQuery] using this
  unfold CostedReduction.eval CostedReduction.totalQueries
  have h1 := isQueryBoundP_bind (Comp.queryBound_eval P w ws hw hU R.init (.cons x .nil))
    (fun as _ => isQueryBoundP_bind (simulateQ_run_StateT_of_step_le hstep (hA as.1) as.2)
      (fun x _ => Comp.queryBound_eval P w ws hw hU R.finish (.cons x.2 (.cons x.1 .nil))))
  refine (h1.mono (by rw [Nat.mul_comm]; omega))

theorem runFuel_queryBound {κ : Type} {G : OracleSpec κ} {C : GameCodec S G} {σ : Ty S}
    (h : Comp O I [σ, C.Q] (.prod C.R σ)) (P : ι → Prop) [DecidablePred P]
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0) {α : Type} (dflt : α)
    (oa : OracleComp (unifSpec + G) α) :
    ∀ (fuel : ℕ) (s : σ.denote),
      (runFuel h dflt oa fuel s).IsQueryBoundP P (fuel * h.queries w ws) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel s; simp [runFuel]
  | query_bind q mx ih =>
    intro fuel s
    cases q with
    | inl n =>
      simpa [runFuel] using isQueryBoundP_bind (hU n) (fun u _ => ih u fuel s)
    | inr t =>
      cases fuel with
      | zero =>
        simp [runFuel]
      | succ f =>
        simp only [runFuel, construct_query_bind]
        have hh := Comp.queryBound_eval P w ws hw hU h (.cons s (.cons (C.qenc t) .nil))
        exact (isQueryBoundP_bind hh (fun p _ => ih (C.rdec t p.1) f p.2)).mono
          (by rw [Nat.succ_mul]; omega)

theorem TwoStageCostedReduction.run1_queryBound {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S} (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g) (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α) :
    ∀ (fuel : ℕ) (s : R.σ.denote),
      (R.run1 dflt oa fuel s).IsQueryBoundP P (fuel * R.handlePre.queries w ws) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel s; simp [TwoStageCostedReduction.run1]
  | query_bind q mx ih =>
    intro fuel s
    cases q with
    | inl n =>
      simpa [TwoStageCostedReduction.run1] using isQueryBoundP_bind (hU n) (fun u _ => ih u fuel s)
    | inr t =>
      cases fuel with
      | zero =>
        simp [TwoStageCostedReduction.run1]
      | succ f =>
        simp only [TwoStageCostedReduction.run1, construct_query_bind]
        have hh := Comp.queryBound_eval P w ws hw hU R.handlePre
          (.cons s (.cons (C.qenc t) .nil))
        refine IsQueryBoundP.mono
          (isQueryBoundP_bind hh (m := f * R.handlePre.queries w ws) fun res _ => ?_)
          (by rw [Nat.succ_mul]; omega)
        rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · exact ih (C.rdec t v) f s'
        · exact (isQueryBoundP_pure (spec := T) P (Mid.paused t c p s' mx) 0).mono (Nat.zero_le _)

theorem TwoStageCostedReduction.eval1_queryBound {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S} (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g) (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote)
    (fuel : ℕ) (dflt : aOut.denote) :
    (R.eval1 A x fuel dflt).IsQueryBoundP P
      (R.init.queries w ws + fuel * R.handlePre.queries w ws + R.chDone.queries w ws) := by
  unfold TwoStageCostedReduction.eval1
  refine IsQueryBoundP.mono
    (isQueryBoundP_bind (Comp.queryBound_eval P w ws hw hU R.init (.cons x .nil)) fun as _ =>
      isQueryBoundP_bind (R.run1_queryBound P w ws hw hU dflt (A as.1) fuel as.2)
        (m := R.chDone.queries w ws) fun m _ => ?_) (by omega)
  cases m with
  | done b s' =>
    exact isQueryBoundP_bind
      (Comp.queryBound_eval P w ws hw hU R.chDone (.cons s' (.cons b .nil)))
      (fun c _ => isQueryBoundP_pure (spec := T) P (c, Mid.done b s') 0)
  | paused t c p s' k =>
    exact (isQueryBoundP_pure (spec := T) P (c, Mid.paused t c p s' k) 0).mono (Nat.zero_le _)

theorem TwoStageCostedReduction.eval2_queryBound {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S} (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g) (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    (m : Mid G aOut.denote R.π.denote R.σ.denote ch.denote) (y : rIn2.denote)
    (fuel : ℕ) (dflt : aOut.denote) :
    (R.eval2 m y fuel dflt).IsQueryBoundP P
      (R.resume.queries w ws + fuel * R.handlePost.queries w ws + R.finish.queries w ws) := by
  cases m with
  | done b s =>
    simp only [TwoStageCostedReduction.eval2, pure_bind]
    exact (Comp.queryBound_eval P w ws hw hU R.finish
      (.cons s (.cons b (.cons y .nil)))).mono (by omega)
  | paused t c p s k =>
    simp only [TwoStageCostedReduction.eval2]
    refine IsQueryBoundP.mono
      (isQueryBoundP_bind
        (Comp.queryBound_eval P w ws hw hU R.resume (.cons s (.cons p (.cons y .nil))))
        fun vs _ => isQueryBoundP_bind
          (runFuel_queryBound R.handlePost P w ws hw hU dflt (k (C.rdec t vs.1)) fuel vs.2)
          fun bs _ => Comp.queryBound_eval P w ws hw hU R.finish
            (.cons bs.2 (.cons bs.1 (.cons y .nil)))) (by omega)

/-! ## Coin-bounded execution -/

/-- The coin-query predicate on `A`'s oracles (`.inl` draws from `unifSpec`). -/
def isCoinQuery {κ : Type} {G : OracleSpec κ} : (unifSpec + G).Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance {κ : Type} {G : OracleSpec κ} : DecidablePred (isCoinQuery (G := G)) := fun t =>
  match t with
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

@[simp] theorem Expr.costWithTbl_ram {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) :
    e.costWithTbl 64 128 = e.cost := by
  induction e <;> simp_all [Expr.costWithTbl, Expr.cost]

@[simp] theorem Comp.costWithTbl_ram {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    c.costWithTbl 64 128 = c.cost := by
  induction c <;> simp_all [Comp.costWithTbl, Comp.cost]

theorem runFuelBounded_queryBound {κ : Type} {G : OracleSpec κ} {C : GameCodec S G} {σ : Ty S}
    (h : Comp O I [σ, C.Q] (.prod C.R σ)) (P : ι → Prop) [DecidablePred P]
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU0 : ∀ n, (I.fwdU n).IsQueryBoundP P 0) {α : Type} (dflt : α)
    (oa : OracleComp (unifSpec + G) α) :
    ∀ (uFuel gFuel : ℕ) (s : σ.denote),
      (runFuelBounded h dflt oa uFuel gFuel s).IsQueryBoundP P (gFuel * h.queries w ws) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro uFuel gFuel s; simp [runFuelBounded]
  | query_bind q mx ih =>
    intro uFuel gFuel s
    cases q with
    | inl n =>
      cases uFuel with
      | zero => simp [runFuelBounded]
      | succ uf =>
        simpa [runFuelBounded] using isQueryBoundP_bind (hU0 n) (fun u _ => ih u uf gFuel s)
    | inr t =>
      cases gFuel with
      | zero => simp [runFuelBounded]
      | succ gf =>
        simp only [runFuelBounded, construct_query_bind]
        have hh := Comp.queryBound_eval P w ws hw hU0 h (.cons s (.cons (C.qenc t) .nil))
        exact (isQueryBoundP_bind hh (fun p _ => ih (C.rdec t p.1) uFuel gf p.2)).mono
          (by rw [Nat.succ_mul]; omega)

theorem TwoStageCostedReduction.run1Bounded_queryBound {κ : Type} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g) (hU0 : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α) :
    ∀ (uFuel gFuel : ℕ) (s : R.σ.denote),
      (R.run1Bounded dflt oa uFuel gFuel s).IsQueryBoundP P
        (gFuel * R.handlePre.queries w ws) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro uFuel gFuel s; simp [TwoStageCostedReduction.run1Bounded]
  | query_bind q mx ih =>
    intro uFuel gFuel s
    cases q with
    | inl n =>
      cases uFuel with
      | zero => simp [TwoStageCostedReduction.run1Bounded]
      | succ uf =>
        simpa [TwoStageCostedReduction.run1Bounded] using
          isQueryBoundP_bind (hU0 n) (fun u _ => ih u uf gFuel s)
    | inr t =>
      cases gFuel with
      | zero => simp [TwoStageCostedReduction.run1Bounded]
      | succ gf =>
        simp only [TwoStageCostedReduction.run1Bounded, construct_query_bind]
        have hh := Comp.queryBound_eval P w ws hw hU0 R.handlePre
          (.cons s (.cons (C.qenc t) .nil))
        refine IsQueryBoundP.mono
          (isQueryBoundP_bind hh (m := gf * R.handlePre.queries w ws) fun res _ => ?_)
          (by rw [Nat.succ_mul]; omega)
        rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · exact ih (C.rdec t v) uFuel gf s'
        · exact (isQueryBoundP_pure (spec := T) P (Mid.paused t c p s' mx) 0).mono (Nat.zero_le _)

theorem runFuelBounded_eq_runFuel {κ : Type} {G : OracleSpec κ} {C : GameCodec S G} {σ : Ty S}
    (h : Comp O I [σ, C.Q] (.prod C.R σ)) {α : Type} (dflt : α)
    {oa : OracleComp (unifSpec + G) α} :
    ∀ {uFuel : ℕ}, oa.IsQueryBoundP (isCoinQuery (G := G)) uFuel →
      ∀ (gFuel : ℕ) (s : σ.denote),
        runFuelBounded h dflt oa uFuel gFuel s = runFuel h dflt oa gFuel s := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro uFuel _ gFuel s
    simp [runFuelBounded, runFuel]
  | query_bind q mx ih =>
    intro uFuel hcoin gFuel s
    rw [isQueryBoundP_query_bind_iff] at hcoin
    cases q with
    | inl n =>
      have hpos : 0 < uFuel := hcoin.1.resolve_left (by simp [isCoinQuery])
      obtain ⟨uf, rfl⟩ : ∃ uf, uFuel = uf + 1 := ⟨uFuel - 1, by omega⟩
      have hsub : ∀ u, (mx u).IsQueryBoundP (isCoinQuery (G := G)) uf := by
        intro u; simpa [isCoinQuery] using hcoin.2 u
      simp only [runFuelBounded, runFuel, construct_query_bind]
      congr 1; funext u
      exact ih u (hsub u) gFuel s
    | inr t =>
      have hsub : ∀ u, (mx u).IsQueryBoundP (isCoinQuery (G := G)) uFuel := by
        intro u; simpa [isCoinQuery] using hcoin.2 u
      cases gFuel with
      | zero =>
        simp [runFuelBounded, runFuel]
      | succ gf =>
        simp only [runFuelBounded, runFuel, construct_query_bind]
        congr 1; funext p
        exact ih (C.rdec t p.1) (hsub _) gf p.2

theorem TwoStageCostedReduction.run1Bounded_eq_run1 {κ : Type} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out) {α : Type} (dflt : α)
    {oa : OracleComp (unifSpec + G) α} :
    ∀ {uFuel : ℕ}, oa.IsQueryBoundP (isCoinQuery (G := G)) uFuel →
      ∀ (gFuel : ℕ) (s : R.σ.denote),
        R.run1Bounded dflt oa uFuel gFuel s = R.run1 dflt oa gFuel s := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro uFuel _ gFuel s
    simp [TwoStageCostedReduction.run1Bounded, TwoStageCostedReduction.run1]
  | query_bind q mx ih =>
    intro uFuel hcoin gFuel s
    rw [isQueryBoundP_query_bind_iff] at hcoin
    cases q with
    | inl n =>
      have hpos : 0 < uFuel := hcoin.1.resolve_left (by simp [isCoinQuery])
      obtain ⟨uf, rfl⟩ : ∃ uf, uFuel = uf + 1 := ⟨uFuel - 1, by omega⟩
      have hsub : ∀ u, (mx u).IsQueryBoundP (isCoinQuery (G := G)) uf := by
        intro u; simpa [isCoinQuery] using hcoin.2 u
      simp only [TwoStageCostedReduction.run1Bounded, TwoStageCostedReduction.run1,
        construct_query_bind]
      congr 1; funext u
      exact ih u (hsub u) gFuel s
    | inr t =>
      have hsub : ∀ u, (mx u).IsQueryBoundP (isCoinQuery (G := G)) uFuel := by
        intro u; simpa [isCoinQuery] using hcoin.2 u
      cases gFuel with
      | zero =>
        simp [TwoStageCostedReduction.run1Bounded, TwoStageCostedReduction.run1]
      | succ gf =>
        simp only [TwoStageCostedReduction.run1Bounded, TwoStageCostedReduction.run1,
          construct_query_bind]
        congr 1; funext res
        rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · exact ih (C.rdec t v) (hsub _) gf s'
        · rfl

theorem TwoStageCostedReduction.eval1Bounded_eq_eval1 {κ : Type} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote)
    (uFuel gFuel : ℕ) (dflt : aOut.denote)
    (hcoin : ∀ a, (A a).IsQueryBoundP (isCoinQuery (G := G)) uFuel) :
    R.eval1Bounded A x uFuel gFuel dflt = R.eval1 A x gFuel dflt := by
  unfold TwoStageCostedReduction.eval1Bounded TwoStageCostedReduction.eval1
  congr 1; funext p; rcases p with ⟨a, s⟩; dsimp only
  rw [R.run1Bounded_eq_run1 dflt (hcoin a) gFuel s]

end ReductionDsl
