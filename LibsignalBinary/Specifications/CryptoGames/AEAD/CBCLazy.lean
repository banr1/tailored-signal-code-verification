/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs

/-!
# Lazy random function for the CBC proof

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Restates the ideal branch of `MACScheme.prfEval` on an explicit lookup table (`lazyStep`, `cbcLazy`)
for the birthday-bound step of `cbc_indcpa` (`CBC.lean`).
-/

@[expose] public section

open OracleComp OracleSpec

namespace CryptoGames
namespace CBC

/-- One query to a lazily sampled random function `Block → Block` on its table, exactly as the
ideal branch of `MACScheme.prfEval`: reuse a recorded value, otherwise sample and record. -/
def lazyStep (x : Block) : StateT (List (Block × Block)) ProbComp Block := do
  let tbl ← get
  match tbl.lookup x with
  | some t => return t
  | none =>
    let t ← liftM ($ᵗ Block)
    set ((x, t) :: tbl)
    return t

/-- CBC of fixed blocks `P` under a uniform IV, with a fresh lazily sampled random function (empty
table) as the block function. -/
def cbcLazy {n : ℕ} (P : List.Vector Block n) : ProbComp (List.Vector Block n) := do
  let iv ← $ᵗ Block
  (cbcM lazyStep iv P).run' []

end CBC
end CryptoGames
