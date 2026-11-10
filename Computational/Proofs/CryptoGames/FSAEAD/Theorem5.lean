/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith
public import Computational.Proofs.CryptoGames.AEAD.PrimitivesProofDefs
public import Computational.Proofs.CryptoGames.FSAEAD.HybridWithProofDefs
import Computational.Proofs.CryptoGames.FSAEAD.HybridLazy
import Computational.Proofs.CryptoGames.FSAEAD.HybridOTReal

/-!
# Hybrid Runner Unfolding and Even/Odd Sum Split for ACD19 Theorem 5

**Checked by Lean.**

Provides `hRun_eq` and the even/odd range split `sum_range_two_mul` separating main-chain and
lookahead-forgery (`la = true`, DEV-FS14) hybrid hops in the FS-AEAD proof for `fromAEADPRG`.

**DEV-FS16 (formalization): perfect AEAD correctness.** ACD19 Definition 1 leaves AEAD decryption
correctness implicit, whereas the Theorem 5 formalization takes `ae.Correct` as an explicit
hypothesis.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy

namespace CryptoGames.FSAEAD.Thm5

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

section OTCCA

end OTCCA

section Hops

variable (A : RatchetAdversary CK MK AD M C)

theorem hRun_eq (P : Params) (D : ℕ → ProbComp (CK × MK)) (sl : Slot CK MK) :
    hRunWith ideal ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) A sl =
      ($ᵗ Bool : ProbComp Bool) >>= fun b =>
        hOut P.la <$> (simulateQ (implWith ideal ae G maxSkip P D none) A).run (hInit b sl) := by
  simp only [hRunWith, map_eq_bind_pure_comp]
  rfl

end Hops

section Ends

variable (A : RatchetAdversary CK MK AD M C)

end Ends

/-- Splits a sum over `Finset.range (2 * N)` into even and odd indices. -/
theorem sum_range_two_mul (f : ℕ → ℝ≥0∞) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N), f j =
      ∑ k ∈ Finset.range N, f (2 * k) + ∑ k ∈ Finset.range N, f (2 * k + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

end CryptoGames.FSAEAD.Thm5
