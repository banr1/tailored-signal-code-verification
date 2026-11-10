/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRF.CostedTables
public import Computational.Proofs.ReductionDsl.Soundness -- shake: keep

/-!
# `ReductionDsl` Tutorial Examples

Checked examples accompanying `Computational/docs/REDUCTION_DSL_TUTORIAL.md`: a stateless PRF
forwarder (`fwdRed`) with its cost, query count, handler semantics, and lifted query bound, and a
stateful query-counting reduction (`countRed`).
-/

@[expose] public section

set_option autoImplicit false

namespace ReductionDslTutorial

open ReductionDsl OracleSpec OracleComp CryptoGames CryptoGames.PRF.Costed

variable (Inp Tg : Type)

abbrev S := prfSig Inp Tg
abbrev O := prfConstantInputOps (S := S Inp Tg) (.base .inp) (Empty.elim : Empty → Inp)
abbrev I := prfIface (S := S Inp Tg) (.base .inp) (.base .tag)
abbrev C := prfCodec (S := S Inp Tg) (.base .inp) (.base .tag)

/-- Stateless reduction forwarding each PRF query directly to the target PRF oracle. -/
def fwdRed : CostedReduction (O Inp Tg) (I Inp Tg) (MACScheme.prfSpec Inp Tg) (C Inp Tg)
    .unit .unit .bool .bool where
  σ := .unit
  init := .ret (.pair .unit .unit)
  handle := .bind (.query () .v1) (.ret (.pair .v0 .v1))
  finish := .ret .v1

example (q : ℕ) : (fwdRed Inp Tg).totalCost q = q * 8 + 6 := by
  simp [CostedReduction.totalCost, fwdRed, I, C, prfCodec, prfIface, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
  omega

example (q : ℕ) : (fwdRed Inp Tg).totalQueries (fun _ => 1) (fun s => nomatch s) q = q := by
  simp [CostedReduction.totalQueries, fwdRed, Comp.queries]

example (x : Inp) :
    (fwdRed Inp Tg).handle.eval (.cons () (.cons x .nil)) =
      (fun t => (t, ())) <$>
        (query (spec := unifSpec + MACScheme.prfSpec Inp Tg) (.inr x)) := by
  rfl

example (A : Unit → OracleComp (unifSpec + MACScheme.prfSpec Inp Tg) Bool) (q : ℕ)
    (hA : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := MACScheme.prfSpec Inp Tg)) q) :
    ((fwdRed Inp Tg).eval A ()).IsQueryBoundP
      (isGameQuery (G := MACScheme.prfSpec Inp Tg)) q := by
  have := CostedReduction.queryBound_eval (fwdRed Inp Tg)
    (isGameQuery (G := MACScheme.prfSpec Inp Tg)) (fun _ => 1) (fun s => nomatch s)
    (fun _ _ _ => le_rfl) (fun n => by simp [prfIface, I, isGameQuery]) A q hA ()
  refine this.mono (le_of_eq ?_)
  simp [CostedReduction.totalQueries, fwdRed, Comp.queries]

/-- Stateful PRF forwarder that counts queries and outputs `A`'s bit only when fewer than 10
queries were made. -/
def countRed : CostedReduction (O Inp Tg) (I Inp Tg) (MACScheme.prfSpec Inp Tg) (C Inp Tg)
    .unit .unit .bool .bool where
  σ := .nat
  init := .ret (.pair .unit (.nat 0))
  handle := .bind (.query () .v1) (.ret (.pair .v0 (.add .v1 (.nat 1))))
  finish := .ret (.ite (.lt .v0 (.nat 10)) .v1 (.bool false))

example (q : ℕ) : (countRed Inp Tg).totalCost q = q * 10 + 13 := by
  have h10 : Nat.log 2 10 = 3 := by decide
  simp [CostedReduction.totalCost, countRed, I, C, h10, prfCodec, prfIface, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, bits]
  omega

end ReductionDslTutorial
