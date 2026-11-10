/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.GameHop.ReductionDsl.SupportWP

/-!
# Potential-Based Query Bounds for `ReductionDsl`

Re-exports `SupportWP` potential lemmas and defines the `HoldsOnLeaves` continuation-congruence
predicate.
-/

@[expose] public section

set_option autoImplicit false

namespace ReductionDsl

open OracleSpec OracleComp
open Computational.Proofs.GameHop.ReductionDsl

variable {ι : Type} {T : OracleSpec ι}

abbrev PotOK {α : Type} (P : ι → Prop) [DecidablePred P]
    (B : α → ℕ) (oa : OracleComp T α) (n : ℕ) : Prop :=
  SupportWP.PotOK P B oa n

theorem PotOK.bindPot {α γ : Type} {P : ι → Prop} [DecidablePred P]
    {B₁ : α → ℕ} {B₂ : γ → ℕ} {oa : OracleComp T α}
    {f : α → OracleComp T γ} {n : ℕ}
    (hoa : PotOK P B₁ oa n) (hf : ∀ a, PotOK P B₂ (f a) (B₁ a)) :
    PotOK P B₂ (oa >>= f) n :=
  SupportWP.PotOK.bindPot hoa hf

theorem PotOK.toQueryBound {α : Type} {P : ι → Prop} [DecidablePred P]
    {B : α → ℕ} {oa : OracleComp T α} {n : ℕ}
    (h : PotOK P B oa n) (hB : ∀ a, B a = 0) :
    oa.IsQueryBoundP P n :=
  SupportWP.PotOK.toQueryBound h hB

export SupportWP (potC_bind potC_caseSum potC_ite potC_ret potOK_simulateQ_handlerImpl)

end ReductionDsl

namespace SignalPqxdh.Security.ReductionDsl

open OracleSpec OracleComp

/-- `HoldsOnLeaves P m` states that every leaf `pure a` reachable in `m` satisfies `P a`,
    expressed directly via continuation congruence under `>>=`. -/
structure HoldsOnLeaves {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (P : α → Prop) (m : OracleComp spec α) : Prop where
  bind_congr : ∀ {β : Type} (f g : α → OracleComp spec β),
    (∀ a, P a → f a = g a) → m >>= f = m >>= g

theorem HoldsOnLeaves.pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : α → Prop} {a : α} (ha : P a) :
    HoldsOnLeaves P (Pure.pure a : OracleComp spec α) :=
  ⟨fun f g hfg => by simp [hfg a ha]⟩

theorem HoldsOnLeaves.bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α γ : Type}
    {P : α → Prop} {Q : γ → Prop} {m : OracleComp spec α} {k : α → OracleComp spec γ}
    (hm : HoldsOnLeaves P m) (hk : ∀ a, P a → HoldsOnLeaves Q (k a)) :
    HoldsOnLeaves Q (m >>= k) :=
  ⟨fun f g hfg => by
    rw [bind_assoc, hm.bind_congr _ _ (fun a ha => (hk a ha).bind_congr f g hfg), ← bind_assoc]⟩

theorem HoldsOnLeaves.const {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (m : OracleComp spec α) :
    HoldsOnLeaves (fun _ => True) m :=
  ⟨fun f g hfg => by congr 1; funext a; exact hfg a trivial⟩

theorem HoldsOnLeaves.bind_const {ι : Type} {spec : OracleSpec.{0, 0} ι} {α γ : Type}
    {Q : γ → Prop} (m : OracleComp spec α) {k : α → OracleComp spec γ}
    (hk : ∀ a, HoldsOnLeaves Q (k a)) :
    HoldsOnLeaves Q (m >>= k) :=
  HoldsOnLeaves.bind (HoldsOnLeaves.const m) (fun a _ => hk a)

theorem HoldsOnLeaves.mono {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P Q : α → Prop} {m : OracleComp spec α}
    (hm : HoldsOnLeaves P m) (hImp : ∀ a, P a → Q a) :
    HoldsOnLeaves Q m :=
  ⟨fun f g hfg => hm.bind_congr f g (fun a ha => hImp a ha |> hfg a)⟩

theorem HoldsOnLeaves.map {ι : Type} {spec : OracleSpec.{0, 0} ι} {α γ : Type}
    {P : α → Prop} {Q : γ → Prop} {m : OracleComp spec α} (f : α → γ)
    (hm : HoldsOnLeaves P m) (hf : ∀ a, P a → Q (f a)) :
    HoldsOnLeaves Q (f <$> m) := by
  rw [map_eq_bind_pure_comp]
  exact HoldsOnLeaves.bind hm (fun a ha => HoldsOnLeaves.pure (hf a ha))

end SignalPqxdh.Security.ReductionDsl
