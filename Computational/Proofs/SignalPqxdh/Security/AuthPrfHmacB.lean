/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthHmac
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs
import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import VCVio.CryptoFoundations.SecExp.Measure
import VCVio.EvalDist.Monad.Basic

/-!
# PQXDH authentication: `PrfHmac` of `prfHmacOfMu` as a rank-averaged gap

`PrfHmacReal P (prfHmacOfMu B) = |E_j Pr[W_true j] - E_j Pr[W_false j]|`, where `j` is the uniform
target rank in `[0, N)`, `N = B.q_enc + B.q_dec`, and `W_b j` runs `prfHmacOfMu B` at target rank
`j` against the real (`b = true`, HMAC under a uniform key) or ideal (`b = false`, lazy random
function) oracle.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open RoKem

/-- The `PrfHmac` oracle of `prfHmacExp` for challenge bit `b` and key `k`. -/
noncomputable def prfEvalImpl (P : Primitives) (b : Bool) (k : Bytes) :
    QueryImpl prfHmacSpec (StateT (List (Bytes × Bytes)) ProbComp) :=
  fun (.eval msg) => do
    if b then
      return hmacSha256Ref P k msg
    else
      let cache ← get
      match cache.find? (fun (m, _) => m == msg) with
      | some (_, t) => return t
      | none =>
        let t ← liftM sampleBytes32
        set ((msg, t) :: cache)
        return t

noncomputable def prfFullImpl (P : Primitives) (b : Bool) (k : Bytes) :
    QueryImpl PrfHmacSimSpec (StateT (List (Bytes × Bytes)) ProbComp) :=
  (primBaseImpl P).liftTarget (StateT (List (Bytes × Bytes)) ProbComp) + prfEvalImpl P b k

theorem prfHmacExp_eq (P : Primitives) (A : PrfHmacAdv) :
    prfHmacExp P A = (do
      let b ← $ᵗ Bool
      let k ← sampleBytes32
      let (b', _) ← (simulateQ (prfFullImpl P b k) A.run).run []
      return (b' == b)) := rfl

def prfAfterRun (j : ℕ) (B : AeadMuIntCtxtAdv) : OracleComp PrfHmacSimSpec Bool := do
  let (_, st) ← prfHmacOfMuRunAt j B
  let hit ← prfHmacFinish j st.pending (st.pending.map (fun e => (e.1, e.2.1))).dedup
  return (st.bad || hit)

/-- Rank-`j` experiment against `PrfHmac` oracle `b`. -/
noncomputable def prfW (P : Primitives) (b : Bool) (B : AeadMuIntCtxtAdv) (j : ℕ) :
    ProbComp Bool := do
  let k ← sampleBytes32
  let (z, _) ← (simulateQ (prfFullImpl P b k) (prfAfterRun j B)).run []
  return z

theorem evalDist_prfHmacOfMu_branch (P : Primitives) (b : Bool) (B : AeadMuIntCtxtAdv) :
    𝒟[do
      let k ← sampleBytes32
      let (b', _) ← (simulateQ (prfFullImpl P b k) (prfHmacOfMu B).run).run []
      return b'] =
    𝒟[sampleIndexRange (B.q_enc + B.q_dec) >>= prfW P b B] := by
  change 𝒟[do
      let k ← sampleBytes32
      let (b', _) ← (simulateQ (prfFullImpl P b k)
        (prfHmacUnif (sampleIndexRange (B.q_enc + B.q_dec)) >>= fun j => prfAfterRun j B)).run []
      return b'] = _
  unfold prfW prfHmacUnif
  simp only [simulateQ_bind, StateT.run_bind, prfFullImpl, simulateQ_embedPrim_run,
    simulateQ_embedUnif, map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
  exact OracleComp.evalDist_bind_bind_swap _ _ _

theorem evalDist_bind_eq_of_evalDist_eq {mx my : ProbComp Bool} (h : 𝒟[mx] = 𝒟[my])
    (f : Bool → ProbComp Bool) : 𝒟[mx >>= f] = 𝒟[my >>= f] := by
  rw [evalDist_bind_of_discrete, h, ← evalDist_bind_of_discrete]

/-- Expresses `PrfHmacReal P (prfHmacOfMu B)` as the gap between the rank-averaged experiments. -/
theorem prfHmac_prfHmacOfMu_eq (P : Primitives) (B : AeadMuIntCtxtAdv) :
    PrfHmacReal P (prfHmacOfMu B) =
      |(𝒟[sampleIndexRange (B.q_enc + B.q_dec) >>= prfW P true B] {true}).toReal -
        (𝒟[sampleIndexRange (B.q_enc + B.q_dec) >>= prfW P false B] {true}).toReal| := by
  unfold PrfHmacReal PrfHmac
  rw [prfHmacExp_eq]
  have h : 𝒟[do
      let b ← $ᵗ Bool
      let k ← sampleBytes32
      let (b', _) ← (simulateQ (prfFullImpl P b k) (prfHmacOfMu B).run).run []
      return (b' == b)] =
    𝒟[do
      let b ← $ᵗ Bool
      if b = true then do
        let z ← sampleIndexRange (B.q_enc + B.q_dec) >>= prfW P true B
        pure (b == z)
      else do
        let z ← sampleIndexRange (B.q_enc + B.q_dec) >>= prfW P false B
        pure (b == z)] := by
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun b _ => ?_)
    have hb := evalDist_prfHmacOfMu_branch P b B
    have hL : 𝒟[do
        let k ← sampleBytes32
        let (b', _) ← (simulateQ (prfFullImpl P b k) (prfHmacOfMu B).run).run []
        return (b' == b)] =
      𝒟[(do
        let k ← sampleBytes32
        let (b', _) ← (simulateQ (prfFullImpl P b k) (prfHmacOfMu B).run).run []
        return b') >>= fun z => pure (b == z)] := by
      simp only [bind_assoc, pure_bind, Bool.beq_comm]
    rw [hL, evalDist_bind_eq_of_evalDist_eq hb]
    cases b <;> simp
  rw [h, evalDist_boolBias_bind_uniformBool, MeasureTheory.Measure.toReal_boolDist]

theorem prf_telescope (T F : ℕ → ℝ) : ∀ n : ℕ, (∀ j, j < n → F j ≤ T (j + 1)) →
    T 0 - F n ≤ ∑ j ∈ Finset.range (n + 1), (T j - F j)
  | 0, _ => by simp
  | n + 1, h => by
    have ih := prf_telescope T F n (fun j hj => h j (by omega))
    have hn := h n (by omega)
    rw [Finset.sum_range_succ]
    linarith

/-- Bounds the multi-key INT-CTXT advantage of `B` via telescoping over the rank-`j` experiments. -/
theorem aeadMuIntCtxt_le_of_hybrids (P : Primitives) (B : AeadMuIntCtxtAdv) (q : ℝ)
    (hzero : B.q_enc + B.q_dec = 0 → AeadMuIntCtxt P B ≤ q)
    (h0 : 0 < B.q_enc + B.q_dec → AeadMuIntCtxt P B ≤ (𝒟[prfW P true B 0] {true}).toReal)
    (hstep : ∀ j, j + 1 < B.q_enc + B.q_dec →
      (𝒟[prfW P false B j] {true}).toReal ≤ (𝒟[prfW P true B (j + 1)] {true}).toReal)
    (hlast : 0 < B.q_enc + B.q_dec →
      (𝒟[prfW P false B (B.q_enc + B.q_dec - 1)] {true}).toReal ≤ q) :
    AeadMuIntCtxt P B ≤ ((B.q_enc + B.q_dec : ℕ) : ℝ) * PrfHmacReal P (prfHmacOfMu B) + q := by
  have hP : 0 ≤ PrfHmacReal P (prfHmacOfMu B) := by
    rw [prfHmac_prfHmacOfMu_eq]; exact abs_nonneg _
  rcases Nat.eq_zero_or_pos (B.q_enc + B.q_dec) with hN | hN
  · rw [hN]; simpa using hzero hN
  obtain ⟨n, hn⟩ : ∃ n, B.q_enc + B.q_dec = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hN).symm⟩
  set T : ℕ → ℝ := fun j => (𝒟[prfW P true B j] {true}).toReal
  set F : ℕ → ℝ := fun j => (𝒟[prfW P false B j] {true}).toReal
  have htel := prf_telescope T F n (fun j hj => hstep j (by omega))
  have hT := _root_.Proofs.SignalPqxdh.Security.mul_toReal_sampleIndexRange_bind_eq_sum (B.q_enc + B.q_dec) (prfW P true B)
  have hF := _root_.Proofs.SignalPqxdh.Security.mul_toReal_sampleIndexRange_bind_eq_sum (B.q_enc + B.q_dec) (prfW P false B)
  rw [hn] at hT hF
  have hsum : ∑ j ∈ Finset.range (n + 1), (T j - F j) ≤
      ((n + 1 : ℕ) : ℝ) * PrfHmacReal P (prfHmacOfMu B) := by
    rw [Finset.sum_sub_distrib, prfHmac_prfHmacOfMu_eq, hn]
    rw [← abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n + 1)), ← abs_mul, mul_sub, hT, hF]
    exact le_abs_self _
  have hl := hlast hN
  rw [hn, Nat.add_sub_cancel] at hl
  have h0' := h0 hN
  rw [hn]
  linarith

end SignalPqxdh.Security
