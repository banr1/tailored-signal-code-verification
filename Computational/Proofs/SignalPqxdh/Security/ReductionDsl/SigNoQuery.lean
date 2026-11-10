/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.Assumptions
public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthGames
import VCVio.EvalDist.Monad.Basic

/-!
# Signing-Query-Free Adversaries in the `SigEufCma` Experiment

Shows that a `SigEufCma` adversary making zero signing queries and discarding its result for a
constant `c` has the same experiment distribution as returning `c` directly.
-/

@[expose] public section

set_option autoImplicit false
namespace SignalPqxdh.Security.ReductionDsl
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp

theorem simulateQ_noSig_evalDist (P : Primitives) {σ : Type}
    (impl : QueryImpl sigOracleSpec (StateT σ ProbComp))
    {α β γ : Type} [MeasurableSpace γ] (mx : OracleComp (PrimBaseSpec + sigOracleSpec) α) (c : β)
    (hmx : IsQueryBoundP (mx >>= fun _ => pure c)
      (fun q : (ℕ ⊕ PrimQuery) ⊕ SigQuery => q.isRight = true) 0)
    (s : σ) (g : β × σ → ProbComp γ) :
    𝒟[(simulateQ ((primBaseImpl P).liftTarget (StateT σ ProbComp) + impl)
        (mx >>= fun _ => pure c)).run s >>= g] = 𝒟[g (c, s)] := by
  induction mx using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at hmx
    rcases t with tp | ts
    · have hk : ∀ u, IsQueryBoundP (k u >>= fun _ => pure c)
          (fun q : (ℕ ⊕ PrimQuery) ⊕ SigQuery => q.isRight = true) 0 := by
        intro u; simpa using hmx.2 u
      rw [bind_assoc, simulateQ_bind, simulateQ_query, StateT.run_bind, bind_assoc]
      have hrun : ((OracleSpec.query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inl tp)).cont <$>
          ((primBaseImpl P).liftTarget (StateT σ ProbComp) + impl)
            (OracleSpec.query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inl tp)).input).run s =
          (primBaseImpl P tp >>= fun u => pure (u, s)) := by
        simp [QueryImpl.liftTarget]
      rw [hrun]
      simp only [bind_assoc, pure_bind]
      refine (evalDist_bind_congr _ _ (fun _ => g (c, s)) fun u => ?_).trans
        (evalDist_bind_const _ _)
      exact ih u (hk u) s
    · simp at hmx

/-- Two `SigEufCma` adversaries, one running a signing-query-free `mx pk` and discarding its
result for the constant `c`, the other returning `c` directly, have the same experiment
distribution. -/
theorem sigEufCmaExp_evalDist_noSig (P : Primitives) (A B : SigEufCmaAdv) {α : Type}
    (mx : Bytes → OracleComp (PrimBaseSpec + sigOracleSpec) α) (c : Bytes × Bytes)
    (hA : ∀ pk, A.run pk = mx pk >>= fun _ => pure c) (hB : ∀ pk, B.run pk = pure c)
    (h0 : ∀ pk, IsQueryBoundP (A.run pk)
      (fun q : (ℕ ⊕ PrimQuery) ⊕ SigQuery => q.isRight = true) 0) :
    𝒟[sigEufCmaExp P A] = 𝒟[sigEufCmaExp P B] := by
  unfold sigEufCmaExp
  refine evalDist_bind_congr _ _ _ fun sk => ?_
  simp only [hB, simulateQ_pure, StateT.run_pure, pure_bind]
  rw [hA]
  have h := h0 (P.sigPkGen sk)
  rw [hA] at h
  exact simulateQ_noSig_evalDist P _ (mx _) c h [] _

end SignalPqxdh.Security.ReductionDsl
