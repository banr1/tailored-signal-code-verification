/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.FSAEAD.HybridOT
import Computational.Proofs.CryptoGames.FSAEAD.HybridLazy

/-!
# Helper Lemmas for the OT-CCA Real World

**Checked by Lean.**

Auxiliary lemmas on compromise predicates (`isCompromised_withKeys`, `isCompromised_congr`) and
skipped-key ranges (`mem_newSkipped`) used in the OT-CCA real-world hybrid step.
-/

@[expose] public section

open OracleComp OracleSpec CryptoGames.Lazy

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoGames.FSAEAD.Thm5

variable {CK MK AD M C : Type}

local notation "St" => HSt CK MK AD M C
local notation "HS" => HState CK MK AD M C
local notation "SP" => StateT (HSt CK MK AD M C) ProbComp
local notation "SO" => StateT (HSt CK MK AD M C) (OracleComp (IndexedOtccaSpec AD M C))

section Proj

variable (k : ℕ)

variable {k} (κ : MK) (h : HState CK MK AD M C)

@[simp] theorem isCompromised_withKeys (ks : List MK) (i : ℕ) :
    ({ h with keys := ks } : HState CK MK AD M C).isCompromised i = h.isCompromised i := rfl

end Proj

section Inv

variable (k : ℕ)

variable {k}

end Inv

section Gen

variable [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (k : ℕ) (la : Bool)

end Gen

section Ops

variable [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (k : ℕ) (la : Bool)

end Ops

section Transfer

variable {k : ℕ}

theorem isCompromised_congr {h h' : HState CK MK AD M C}
    (hc : h'.senderCorruptedAt = h.senderCorruptedAt) (i : ℕ) :
    h'.isCompromised i = h.isCompromised i := by
  simp only [HState.isCompromised, hc]

end Transfer

section Oracles

variable [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) (k : ℕ) (la : Bool)

theorem mem_newSkipped {r i x : ℕ} (hx : x ∈ newSkipped r i) : r < x ∧ x < i := by
  simp only [newSkipped, List.mem_reverse, List.mem_range'_1] at hx
  omega

end Oracles

end CryptoGames.FSAEAD.Thm5
