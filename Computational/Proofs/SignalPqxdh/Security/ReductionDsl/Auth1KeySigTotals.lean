/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigBounds
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDhProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrProofs

/-!
# Init / Finish Bounds and Query Bridges for the One-Key `Auth` Sig Program

**Checked by Lean.** Bounds the `init` and `finish` stages of `sigAuth1KeyProg` and instantiates
`CostedReduction.queryBound_eval` for signing, DDH, and primitive queries.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle
end

theorem a1s_init_cost_le (S : Setup) (K : Nat) :
    (sigAuth1KeyProg S K).init.cost ≤ 400 + 6 * S.N_dh := by
  have hb1 : bits S.N_id ≤ S.N_dh + 1 := by
    have := bits_le_succ S.N_id
    unfold Setup.N_dh; omega
  have hb3 : bits (min K (min S.N_spk_tot S.N_recv)) ≤ S.N_dh + 1 := by
    have := bits_le_succ (min K (min S.N_spk_tot S.N_recv))
    have : min K (min S.N_spk_tot S.N_recv) ≤ min S.N_spk_tot S.N_recv := Nat.min_le_right _ _
    have : min S.N_spk_tot S.N_recv ≤ S.N_spk_tot := Nat.min_le_left _ _
    unfold Setup.N_dh; omega
  dsimp only [sigAuth1KeyProg]
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  simp only [a1sInit2Dsl, a1sDummyPa, a1sMk, emptySimE, emptyAuthStE, fsMk, stMk,
    bindV, letV, Comp.costUB_letC,
    costUB_sampleIndexC, costUB_sampleBoolC,
    v, Comp.costUB, Expr.costUB, bits_0]
  omega

theorem a1s_init_cost_le_tight (S : Setup) (K : Nat) :
    (sigAuth1KeyProg S K).init.cost ≤ 400 + Nat.log 2 S.N_dh + K := by
  have hb1 : bits S.N_id ≤ Nat.log 2 S.N_dh + 1 := by
    unfold bits
    have := Nat.log_mono_right (b := 2) (by unfold Setup.N_dh; omega : S.N_id ≤ S.N_dh)
    omega
  have hb3 : bits (min K (min S.N_spk_tot S.N_recv)) ≤ K + 1 := by
    unfold bits
    have := le_trans (Nat.log_mono_right (b := 2) (Nat.min_le_left K (min S.N_spk_tot S.N_recv)))
      (Nat.log_le_self 2 K)
    omega
  dsimp only [sigAuth1KeyProg]
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  simp only [a1sInit2Dsl, a1sDummyPa, a1sMk, emptySimE, emptyAuthStE, fsMk, stMk,
    bindV, letV, Comp.costUB_letC,
    costUB_sampleIndexC, costUB_sampleBoolC,
    v, Comp.costUB, Expr.costUB, bits_0]
  omega

theorem a1s_finish_cost_le (S : Setup) (K : Nat) :
    (sigAuth1KeyProg S K).finish.cost ≤ 5000 := by
  dsimp only [sigAuth1KeyProg]
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  simp only [a1sFinishDsl, a1sFg, eCaseOpt, costUB_litBytes,
    v, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]
  omega

theorem a1s_init_queries (S : Setup) (K : Nat) (w : pqSigAndDdhIface.Tag → ℕ) :
    (sigAuth1KeyProg S K).init.queries w SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  simp [sigAuth1KeyProg, a1sInit2Dsl, bindV, letV, Comp.letC, Comp.sampleIndexC, Comp.sampleBoolC,
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight, Comp.queries]

theorem a1s_finish_queries (S : Setup) (K : Nat) (w : pqSigAndDdhIface.Tag → ℕ) :
    (sigAuth1KeyProg S K).finish.queries w SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  simp [sigAuth1KeyProg, a1sFinishDsl, Comp.queries]

theorem sigAuth1KeyProg_sigBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := authSpec S)) q)
    (pk : Bytes) :
    ((sigAuth1KeyProg S K).eval A pk).IsQueryBoundP
      (fun q => isSigChalQuery q = true)
      ((sigAuth1KeyProg S K).totalQueries
        SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q) := by
  refine CostedReduction.queryBound_eval (sigAuth1KeyProg S K)
    (fun q => isSigChalQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_ A q hA pk
  · intro g x hx
    cases g with
    | inl t => simp [pqSigAndDdhIface, pqChalIface, isSigChalQuery] at hx
    | inr t =>
      cases t with
      | inl m => simp [SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight]
      | inr u =>
        rcases u with ⟨⟩
        simp [pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, isSigChalQuery] at hx
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl n))))
      (fun q => isSigChalQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isSigChalQuery]

theorem sigAuth1KeyProg_ddhBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := authSpec S)) q)
    (pk : Bytes) :
    ((sigAuth1KeyProg S K).eval A pk).IsQueryBoundP
      (fun q => isDdhChalQuery q = true)
      ((sigAuth1KeyProg S K).totalQueries
        SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q) := by
  refine CostedReduction.queryBound_eval (sigAuth1KeyProg S K)
    (fun q => isDdhChalQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_ A q hA pk
  · intro g x hx
    cases g with
    | inl t => simp [pqSigAndDdhIface, pqChalIface, isDdhChalQuery] at hx
    | inr t =>
      cases t with
      | inl m => simp [pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, isDdhChalQuery] at hx
      | inr u => rcases u with ⟨⟩; simp [SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl n))))
      (fun q => isDdhChalQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isDdhChalQuery]

theorem sigAuth1KeyProg_primBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := authSpec S)) q)
    (pk : Bytes) :
    ((sigAuth1KeyProg S K).eval A pk).IsQueryBoundP
      (fun q => isPrimQuery q = true)
      ((sigAuth1KeyProg S K).totalQueries
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q) := by
  refine CostedReduction.queryBound_eval (sigAuth1KeyProg S K)
    (fun q => isPrimQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_ A q hA pk
  · intro g x hx
    cases g with
    | inl t => simp [SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
    | inr t => simp [pqSigAndDdhIface, pqChalIface, isPrimQuery] at hx
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl n))))
      (fun q => isPrimQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isPrimQuery]

end SignalPqxdh.Security.ReductionDsl.AuthHs
