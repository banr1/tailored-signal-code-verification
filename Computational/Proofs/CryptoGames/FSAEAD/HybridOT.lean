/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Lazy
public import Computational.Proofs.CryptoGames.FSAEAD.HybridProofDefs
public import Computational.Proofs.CryptoGames.FSAEAD.HybridWithProofDefs
import Computational.Proofs.CryptoGames.FSAEAD.HybridLazy

/-!
# Joint State for OT-CCA Hybrid Steps

**Checked by Lean.**

Defines the joint hybrid and indexed OT-CCA state `JSt` and support-guarded `DEq` bind congruence.
-/

@[expose] public section

open OracleComp OracleSpec CryptoGames.Lazy

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoGames.FSAEAD.Thm5

variable {CK MK AD M C : Type}

/-- Joint state pairing the hybrid state with an indexed OT-CCA state. -/
abbrev JSt (CK MK AD M C : Type) := HSt CK MK AD M C × IndexedOtccaState MK AD C

local notation "St" => HSt CK MK AD M C
local notation "HS" => HState CK MK AD M C
local notation "SP" => StateT (HSt CK MK AD M C) ProbComp
local notation "SO" => StateT (HSt CK MK AD M C) (OracleComp (IndexedOtccaSpec AD M C))

theorem DEq.bind_right_supp {α β : Type} (x : ProbComp α) {f g : α → ProbComp β}
    (h : ∀ a ∈ support x, DEq (f a) (g a)) : DEq (x >>= f) (x >>= g) := fun F => by
  simp only [bind_assoc]
  exact evalDist_bind_congr_of_support x _ _ fun a ha => h a ha F

section Frame

variable [DecidableEq AD] [DecidableEq C] (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C)

end Frame

section Judgment

variable [DecidableEq AD] [DecidableEq C] (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C)
  (f : JSt CK MK AD M C → HSt CK MK AD M C)

variable {ideal ae f}

end Judgment

section Ideal

variable [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) (k : ℕ) (la : Bool)

end Ideal

section Runs

variable [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
  (A : RatchetAdversary CK MK AD M C)

end Runs

end CryptoGames.FSAEAD.Thm5
