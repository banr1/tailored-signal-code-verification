/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import VCVio.CryptoFoundations.PRG

/-!
# PRG reduction tables

**Checked by Lean.** Polymorphic `ReductionDsl` generator operation table, coin-only target
interface, and source game codec for pseudorandom generators (`PRGScheme`).
-/

@[expose] public section

namespace CryptoGames.PRG.Costed

open ReductionDsl OracleSpec OracleComp

/-- Polymorphic PRG operation table evaluating `gen` at cost `k`. -/
@[reducible] def prgOps {S : Sig} (seedT outT : Ty S) (gen : seedT.denote → outT.denote)
    (k : ℕ) : Ops S where
  Op := Unit
  dom := fun _ => seedT
  cod := fun _ => outT
  eval := fun _ x => gen x
  cost := fun _ => k

/-- Coin-only target interface (`unifSpec`, `Tag = Empty`) for PRG reductions at unit coin cost. -/
def prgIface (S : Sig) : Iface S unifSpec where
  fwdU := fun n => query (spec := unifSpec) n
  uCost := 1
  Tag := Empty
  dom := Empty.elim
  cod := Empty.elim
  enc := fun g => g.elim
  dec := fun g => g.elim
  qCost := Empty.elim
  smp := Samplers.empty

end CryptoGames.PRG.Costed

set_option autoImplicit false

namespace CryptoGames.PRG.Costed

open ReductionDsl OracleSpec OracleComp

abbrev prgSpec : OracleSpec Empty := Empty.elim

/-- Lift a coin-only `PRGAdversary R` into `unifSpec + prgSpec` for `CostedReduction.eval`. -/
abbrev liftPRGAdv {R : Type} (B : PRGScheme.PRGAdversary R) :
    R → OracleComp (unifSpec + prgSpec) Bool :=
  fun r => liftM (B r)

/-- Trivial source game codec for a coin-only `PRGAdversary` (`codecCost = 1`). -/
def prgCodec (S : Sig) : GameCodec S prgSpec where
  Q := .unit
  R := .unit
  qenc := Empty.elim
  rdec := fun t => t.elim
  codecCost := 1

end CryptoGames.PRG.Costed
