/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FSAEAD.PubCosted
public import Computational.Proofs.ReductionDsl.Soundness
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.PubDefs

/-!
# Costed `pubRed` Soundness, Cost, and Query Bounds

Proves evaluation agreement (`pubRedProg_eval`), static step-cost (`pubRedProg_totalCost`), and
target query bounds (`pubRedProg_queries`) for `pubRedProg`.
-/

@[expose] public section

namespace CryptoGames.FSAEAD.Costed

open ReductionDsl OracleComp

@[simp] theorem _root_.ReductionDsl.Env.get_cons_zero {S : Sig} {Γ : List (Ty S)} {t : Ty S}
    (x : t.denote) (ρ : Env Γ) : (Env.cons x ρ).get Var.zero = x := rfl

@[simp] theorem _root_.ReductionDsl.Env.get_cons_succ {S : Sig} {Γ : List (Ty S)} {t u : Ty S}
    (x : u.denote) (ρ : Env Γ) (v : Var Γ t) : (Env.cons x ρ).get (Var.succ v) = ρ.get v := rfl

variable {SS RS AD Pub M C : Type} (pubOf : C → Option Pub) (k : ℕ)

theorem pubRedProg_impl :
    (pubRedProg (SS := SS) (RS := RS) (AD := AD) (M := M) pubOf k).impl = pubRedImpl pubOf := by
  funext t
  rcases t with n | (((((⟨a, p, m⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩)
  all_goals (apply StateT.ext; intro (s : Bool))
  all_goals simp [CostedReduction.impl, handlerImpl, pubRedProg, pubHandle, pubRedImpl, pubCodec,
    fsaeadIface, Comp.eval,
    Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v7,
    transmitQuery, challengeQuery, corruptSenderQuery, corruptReceiverQuery, deliverQuery,
    injectQuery, withPubE, StateT.run_lift, StateT.run_bind]
  case inr.inl.inl.inr =>
    rw [map_eq_bind_pure_comp]
    refine bind_congr fun r => ?_
    cases r <;> simp [StateT.run_set]
  case inr.inl.inr =>
    cases h : pubOf c <;> simp [StateT.run_lift]
    refine congrArg (· <$> _) (funext fun r => ?_)
    rcases r with _ | _ | ⟨i, _ | m⟩ <;> rfl
  case inr.inr =>
    cases h : pubOf c <;> simp [StateT.run_lift, StateT.run_get]
    · cases s <;> rfl
    · refine congrArg (· <$> _) (funext fun r => ?_)
      rcases r with _ | _ | ⟨i, _ | m⟩ <;> rfl

theorem pubRedProg_eval (A : Adversary SS RS AD (Pub × M) C) :
    (pubRedProg pubOf k).eval (fun _ => A) () = pubRed pubOf A := by
  have h := pubRedProg_impl (SS := SS) (RS := RS) (AD := AD) (M := M) pubOf k
  simp only [CostedReduction.eval, pubRedProg, Comp.eval, Expr.eval, Expr.v1, pubRed, StateT.run'] at h ⊢
  rw [h, pure_bind, map_eq_bind_pure_comp]
  rfl

theorem pubHandle_cost :
    (pubHandle (SS := SS) (RS := RS) (AD := AD) (M := M) pubOf k).cost = k + 44 := by
  simp [pubHandle, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
    Expr.v7, withPubE, fsaeadIface, fsOps]
  omega

theorem pubRedProg_totalCost (q : ℕ) :
    (pubRedProg (SS := SS) (RS := RS) (AD := AD) (M := M) pubOf k).totalCost q =
      q * (k + 50) + 6 := by
  have h := pubHandle_cost (SS := SS) (RS := RS) (AD := AD) (M := M) pubOf k
  simp only [CostedReduction.totalCost, pubRedProg, pubCodec, fsaeadIface, Comp.cost, Expr.cost,
    Expr.v1] at h ⊢
  rw [h, max_eq_right (by omega), show k + 44 + 6 = k + 50 by omega]; omega

theorem pubRedProg_queries (A : Adversary SS RS AD (Pub × M) C) (q : ℕ)
    (hA : A.IsQueryBoundP (isGameQuery (G := spec SS RS AD (Pub × M) C)) q) :
    (pubRedProg pubOf k).eval (fun _ => A) () |>.IsQueryBoundP
      (isGameQuery (G := spec SS RS (AD × Pub) M C)) q := by
  have := CostedReduction.queryBound_eval (pubRedProg pubOf k)
    (isGameQuery (G := spec SS RS (AD × Pub) M C)) (fun _ => 1) (fun s => nomatch s)
    (fun _ _ _ => le_rfl) (fun n => by simp [fsaeadIface, isGameQuery]) (fun _ => A) q
    (fun _ => hA) ()
  refine this.mono (le_of_eq ?_)
  simp [CostedReduction.totalQueries, pubRedProg, pubHandle, Comp.queries]

end CryptoGames.FSAEAD.Costed
