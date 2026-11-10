/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core

/-!
# Per-Query-Kind Target-Query Counts

Defines the proof-side input-specialized target-query count `Comp.queriesAt` and per-query-kind
predicates `ValidKindQueries`, `totalQueriesByKind`, and `QueriesBoundedByKind` for
`CostedReduction` and `TwoStageCostedReduction`. Soundness against `OracleComp.IsQueryBoundP` is
proved in `KindedCost.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace ReductionDsl

variable {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
  {κ : Type} {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out ch rIn2 : Ty S}

/-- Weighted target queries/samples of `c` starting from `ρ`, charging only the taken arm on
branches and specializing pure-prefix `bind` continuations. -/
def Comp.queriesAt (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → Env Γ → ℕ
  | _, _, .ret _, _ => 0
  | _, _, .bind c k, ρ =>
    c.queriesAt w ws ρ + match c.pureEval? ρ with
      | Option.some x => k.queriesAt w ws (.cons x ρ)
      | Option.none => k.queries w ws
  | _, _, .ite b c d, ρ => if b.eval ρ then c.queriesAt w ws ρ else d.queriesAt w ws ρ
  | _, _, .caseOpt e n s, ρ => match e.eval ρ with
    | Option.none => n.queriesAt w ws ρ
    | Option.some x => s.queriesAt w ws (.cons x ρ)
  | _, _, .caseSum e l r, ρ => match e.eval ρ with
    | Sum.inl x => l.queriesAt w ws (.cons x ρ)
    | Sum.inr y => r.queriesAt w ws (.cons y ρ)
  | _, _, .sample s _, _ => ws s
  | _, _, .query g _, _ => w g
  | _, _, .iter n _ body, _ => n * body.queries w ws
  | _, _, .findM K _ p, _ => K * p.queries w ws
  | _, _, .anyM K _ p, _ => K * p.queries w ws
  | _, _, .mapM K _ f, _ => K * f.queries w ws
  | _, _, .consumeFirstM K _ p _, _ => K * p.queries w ws
  | _, _, .foldM K _ _ f, _ => K * f.queries w ws

def CostedReduction.ValidKindQueries (R : CostedReduction O I G C rIn aIn aOut out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {n : ℕ} (kind : κ → Fin n) (hQ : Fin n → ℕ) : Prop :=
  ∀ (s : R.σ.denote) (t : κ),
    R.handle.queriesAt w ws (.cons s (.cons (C.qenc t) .nil)) ≤ hQ (kind t)

def CostedReduction.totalQueriesByKind (R : CostedReduction O I G C rIn aIn aOut out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {n : ℕ} (hQ qKind : Fin n → ℕ) : ℕ :=
  R.init.queries w ws + (List.ofFn fun i => qKind i * hQ i).sum + R.finish.queries w ws

/-- `R` makes at most `Q` weighted target queries under classifier `kind` and counts `qKind`. -/
def CostedReduction.QueriesBoundedByKind (R : CostedReduction O I G C rIn aIn aOut out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {n : ℕ} (kind : κ → Fin n) (qKind : Fin n → ℕ)
    (Q : ℕ) : Prop :=
  ∃ hQ : Fin n → ℕ, R.ValidKindQueries w ws kind hQ ∧ R.totalQueriesByKind w ws hQ qKind ≤ Q

def TwoStageCostedReduction.ValidKindQueries
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {n : ℕ} (kind : κ → Fin n) (hQ : Fin n → ℕ) : Prop :=
  ∀ (s : R.σ.denote) (t : κ),
    R.handlePre.queriesAt w ws (.cons s (.cons (C.qenc t) .nil)) ≤ hQ (kind t) ∧
    R.handlePost.queriesAt w ws (.cons s (.cons (C.qenc t) .nil)) ≤ hQ (kind t)

def TwoStageCostedReduction.totalQueriesByKind
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {n : ℕ} (hQ qKind : Fin n → ℕ) : ℕ :=
  R.init.queries w ws + (List.ofFn fun i => qKind i * hQ i).sum +
    max (R.chDone.queries w ws) (R.resume.queries w ws) + R.finish.queries w ws

def TwoStageCostedReduction.QueriesBoundedByKind
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {n : ℕ} (kind : κ → Fin n) (qKind : Fin n → ℕ)
    (Q : ℕ) : Prop :=
  ∃ hQ : Fin n → ℕ, R.ValidKindQueries w ws kind hQ ∧ R.totalQueriesByKind w ws hQ qKind ≤ Q

end ReductionDsl
