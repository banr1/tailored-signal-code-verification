/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import Computational.Specifications.Reductions.ReductionDsl.Core

/-!
# PRF reduction tables

**Checked by Lean.** Shared `ReductionDsl` signature, constant-input operation table, target oracle
interface, and source game codec for pseudorandom functions (`MACScheme.prfSpec`).
-/

@[expose] public section

namespace Computational.Proofs.SpecLemmas.Reductions.Primitives.PRF.CostedTables

open ReductionDsl (GameCodec Iface Ops Sig Ty)

open OracleSpec OracleComp

inductive PrfSort | inp | tag

/-- Two-sort signature (`inp`, `tag`) with unit-sized sorts for standalone PRF reductions. -/
@[reducible] def prfSig (Input Tag : Type) : Sig where
  Base := PrfSort
  den := fun | .inp => Input | .tag => Tag
  sz := fun _ _ => 1

/-- Polymorphic operation table supplying named constant PRF inputs `c` at unit cost. -/
@[reducible] def prfConstantInputOps {S : Sig} (inpT : Ty S) {C : Type} (c : C → inpT.denote) : Ops S where
  Op := C
  dom := fun _ => .unit
  cod := fun _ => inpT
  eval := fun o _ => c o
  cost := fun _ => 1

/-- Target oracle interface for `unifSpec + MACScheme.prfSpec` at unit query and coin cost. -/
def prfIface {S : Sig} (inpT tagT : Ty S) :
    Iface S (unifSpec + CryptoGames.MACScheme.prfSpec inpT.denote tagT.denote) where
  fwdU := fun n =>
    query (spec := unifSpec + CryptoGames.MACScheme.prfSpec inpT.denote tagT.denote) (.inl n)
  uCost := 1
  Tag := Unit
  dom := fun _ => inpT
  cod := fun _ => tagT
  enc := fun _ x => .inr x
  dec := fun _ _ u => u
  qCost := fun _ => 1
  smp := ReductionDsl.Samplers.empty

/-- Source game codec for `MACScheme.prfSpec` (`codecCost = 1`). -/
def prfCodec {S : Sig} (inpT tagT : Ty S) :
    GameCodec S (CryptoGames.MACScheme.prfSpec inpT.denote tagT.denote) where
  Q := inpT
  R := tagT
  qenc := fun x => x
  rdec := fun _ r => r
  codecCost := 1

end Computational.Proofs.SpecLemmas.Reductions.Primitives.PRF.CostedTables

-- AUTO-BRIDGE BEGIN
namespace CryptoGames.PRF.Costed
export Computational.Proofs.SpecLemmas.Reductions.Primitives.PRF.CostedTables (
  PrfSort prfCodec prfConstantInputOps prfIface prfSig
)
end CryptoGames.PRF.Costed
namespace CryptoGames.PRF.Costed.PrfSort
export Computational.Proofs.SpecLemmas.Reductions.Primitives.PRF.CostedTables.PrfSort (
  inp tag
)
end CryptoGames.PRF.Costed.PrfSort
-- AUTO-BRIDGE END
