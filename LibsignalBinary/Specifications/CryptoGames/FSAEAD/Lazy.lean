/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VCVio.OracleComp.EvalDist.AnswerMeasure
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.EvalDist.Measure

/-!
# Lazy-sampling toolkit for the hybrid arguments of ACD19 Thm 5

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Observational equality `DEq` on `ProbComp` (equal distributions under every Boolean continuation,
avoiding measurable-space instances on state types) and slot-filling simulation relations (`Idem`,
`Comm`, `Rel`, `RC`) on `StateT (H × S) ProbComp` that close under `bind` and lift to `simulateQ`.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory

namespace CryptoGames.Lazy

variable {α β γ : Type}

/-- Observational equality of probabilistic computations: equal distributions under every Boolean
continuation. -/
def DEq (x y : ProbComp α) : Prop := ∀ F : α → ProbComp Bool, 𝒟[x >>= F] = 𝒟[y >>= F]

namespace DEq

variable {x y z : ProbComp α}

@[refl] theorem refl (x : ProbComp α) : DEq x x := fun _ => rfl

theorem symm (h : DEq x y) : DEq y x := fun F => (h F).symm

theorem trans (h₁ : DEq x y) (h₂ : DEq y z) : DEq x z := fun F => (h₁ F).trans (h₂ F)

theorem of_eq (h : x = y) : DEq x y := h ▸ refl x

theorem bind_left (h : DEq x y) (f : α → ProbComp β) : DEq (x >>= f) (y >>= f) := fun F => by
  simpa only [bind_assoc] using h (fun a => f a >>= F)

theorem bind_right (x : ProbComp α) {f g : α → ProbComp β} (h : ∀ a, DEq (f a) (g a)) :
    DEq (x >>= f) (x >>= g) := fun F => by
  simp only [bind_assoc]
  exact evalDist_bind_congr x _ _ fun a => h a F

theorem bind {f g : α → ProbComp β} (h : DEq x y) (hf : ∀ a, DEq (f a) (g a)) :
    DEq (x >>= f) (y >>= g) :=
  (bind_left h f).trans (bind_right y hf)

theorem map (h : DEq x y) (f : α → β) : DEq (f <$> x) (f <$> y) := by
  simpa only [map_eq_bind_pure_comp] using bind_left h (pure ∘ f)

theorem swap (x : ProbComp α) (y : ProbComp β) (f : α → β → ProbComp γ) :
    DEq (x >>= fun a => y >>= fun b => f a b) (y >>= fun b => x >>= fun a => f a b) := fun F => by
  simp only [bind_assoc]
  exact OracleComp.evalDist_bind_bind_swap x y _

/-- Equal Boolean distributions. -/
theorem evalDist_eq {x y : ProbComp Bool} (h : DEq x y) : 𝒟[x] = 𝒟[y] := by
  simpa only [bind_pure] using h pure

/-- A computation whose result is ignored can be dropped. -/
theorem bind_const (x : ProbComp α) (y : ProbComp β) : DEq (x >>= fun _ => y) y := fun F => by
  simp only [bind_assoc]
  exact OracleComp.evalDist_bind_const x _

end DEq

/-! ### Fill kernels -/

section Fill

variable {H S : Type} (fill : H → S → ProbComp S)

/-- Fill the slot of a state. -/
def fillSt (s : H × S) : ProbComp (H × S) := (s.1, ·) <$> fill s.1 s.2

/-- Fill the slot of the output state. -/
def fillOut : α × (H × S) → ProbComp (α × (H × S)) := fun z => (z.1, ·) <$> fillSt fill z.2

/-- Filling twice is filling once. -/
def Idem : Prop := ∀ h sl, DEq (fill h sl >>= fill h) (fill h sl)

/-- `x` commutes with filling, once the output is filled. -/
def Comm (x : StateT (H × S) ProbComp α) : Prop :=
  ∀ s, DEq (fillSt fill s >>= x.run >>= fillOut fill) (x.run s >>= fillOut fill)

/-- `xB` from a filled state behaves like `xA` from a filled state, followed by a fill. -/
def Rel (xA xB : StateT (H × S) ProbComp α) : Prop :=
  ∀ s, DEq (fillSt fill s >>= xB.run) (fillSt fill s >>= xA.run >>= fillOut fill)

/-- `Rel` together with `Comm` of the first computation: the form closed under `bind`. -/
def RC (xA xB : StateT (H × S) ProbComp α) : Prop := Rel fill xA xB ∧ Comm fill xA

variable {fill}

theorem fillSt_idem (hI : Idem fill) (s : H × S) :
    DEq (fillSt fill s >>= fillSt fill) (fillSt fill s) := by
  obtain ⟨h, sl⟩ := s
  simp only [fillSt, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  have := DEq.bind_left (hI h sl) (pure ∘ fun x => (h, x))
  simpa only [bind_assoc] using this

theorem Comm.pure (hI : Idem fill) (a : α) : Comm fill (pure a : StateT (H × S) ProbComp α) := by
  intro s
  simp only [StateT.run_pure, bind_assoc, pure_bind, fillOut]
  have := DEq.map (fillSt_idem hI s) (a, ·)
  simpa only [map_bind] using this

theorem Comm.bind {x : StateT (H × S) ProbComp α} {f : α → StateT (H × S) ProbComp β}
    (hx : Comm fill x) (hf : ∀ a, Comm fill (f a)) : Comm fill (x >>= f) := by
  intro s
  simp only [StateT.run_bind, bind_assoc]
  have hins : ∀ z : α × (H × S),
      DEq ((f z.1).run z.2 >>= fillOut fill)
        (fillSt fill z.2 >>= (f z.1).run >>= fillOut fill) := fun z => (hf z.1 z.2).symm
  refine (DEq.bind_right _ fun s₁ => DEq.bind_right _ fun z => hins z).trans ?_
  refine DEq.trans ?_ (DEq.bind_right _ fun z => (hins z).symm)
  have hx' := DEq.bind_left (hx s) fun z => (f z.1).run z.2 >>= fillOut fill
  simp only [fillOut, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind] at hx' ⊢
  exact hx'

theorem Rel.bind {xA xB : StateT (H × S) ProbComp α} {fA fB : α → StateT (H × S) ProbComp β}
    (hx : Rel fill xA xB) (hf : ∀ a, Rel fill (fA a) (fB a)) (hc : ∀ a, Comm fill (fA a)) :
    Rel fill (xA >>= fA) (xB >>= fB) := by
  intro s
  simp only [StateT.run_bind, bind_assoc]
  have h1 := DEq.bind_left (hx s) fun z => (fB z.1).run z.2
  simp only [bind_assoc] at h1
  refine h1.trans ?_
  refine DEq.bind_right _ fun s₁ => DEq.bind_right _ fun z => ?_
  have h2 := (hf z.1 z.2).trans (hc z.1 z.2)
  simpa only [fillOut, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind] using h2

theorem Rel.pure (hI : Idem fill) (a : α) :
    Rel fill (pure a : StateT (H × S) ProbComp α) (pure a) := by
  intro s
  have e : (Pure.pure a : StateT (H × S) ProbComp α).run = fun s => Pure.pure (a, s) := by
    funext s; rfl
  simp only [e, bind_assoc, pure_bind, fillOut]
  have := DEq.map (fillSt_idem hI s) (a, ·)
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def] at this ⊢
  exact this.symm

theorem RC.bind {xA xB : StateT (H × S) ProbComp α} {fA fB : α → StateT (H × S) ProbComp β}
    (hx : RC fill xA xB) (hf : ∀ a, RC fill (fA a) (fB a)) : RC fill (xA >>= fA) (xB >>= fB) :=
  ⟨Rel.bind hx.1 (fun a => (hf a).1) fun a => (hf a).2, Comm.bind hx.2 fun a => (hf a).2⟩

theorem RC.pure (hI : Idem fill) (a : α) : RC fill (pure a : StateT (H × S) ProbComp α) (pure a) :=
  ⟨Rel.pure hI a, Comm.pure hI a⟩

/-! ### Lifting to `simulateQ` -/

variable {ι : Type} {spec : OracleSpec ι}

theorem Comm.simulateQ (hI : Idem fill) {impl : QueryImpl spec (StateT (H × S) ProbComp)}
    (himpl : ∀ t, Comm fill (impl t)) (oa : OracleComp spec α) :
    Comm fill (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [simulateQ_pure] using Comm.pure hI a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map]
    exact Comm.bind (himpl t) ih

theorem Rel.simulateQ (hI : Idem fill) {implA implB : QueryImpl spec (StateT (H × S) ProbComp)}
    (hrel : ∀ t, Rel fill (implA t) (implB t)) (hcomm : ∀ t, Comm fill (implA t))
    (oa : OracleComp spec α) :
    Rel fill (simulateQ implA oa) (simulateQ implB oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [simulateQ_pure] using Rel.pure hI a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map]
    exact Rel.bind (hrel t) ih fun a => Comm.simulateQ hI hcomm (k a)

/-- Observations that ignore the slot cannot see a final fill. -/
theorem map_fillOut (F : α → H → Bool) (y : ProbComp (α × (H × S))) :
    DEq ((fun z => F z.1 z.2.1) <$> (y >>= fillOut fill)) ((fun z => F z.1 z.2.1) <$> y) := by
  have e : (fun z => F z.1 z.2.1) <$> y = y >>= fun z => pure (F z.1 z.2.1) := by
    rw [map_eq_bind_pure_comp]; rfl
  rw [e, map_bind]
  refine DEq.bind_right y fun z => ?_
  simp only [fillOut, fillSt, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  exact DEq.bind_const _ _

end Fill

end CryptoGames.Lazy
