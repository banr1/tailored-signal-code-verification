/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core
public import LibsignalBinary.Specifications.CryptoGames.Primitives

/-!
# One-time CCA AEAD reduction tables

**Checked by Lean.** Polymorphic `ReductionDsl` operation table, ideal-ciphertext sampler, target
oracle interface, and source game codec for one-time chosen-ciphertext AEAD (`AEADScheme.otccaSpec`).
-/

@[expose] public section

namespace Computational.Proofs.SpecLemmas.Reductions.Primitives.OTCCA.CostedTables

open CryptoGames (AEADScheme)
open ReductionDsl (GameCodec Iface Ops Samplers Sig Ty)

open OracleSpec OracleComp

inductive OtccaOp | enc | dec | saltOf | eqAD | eqM | eqC | eqSalt

/-- Polymorphic AEAD operation table over `S`: `enc`, `dec`, and `saltOf` at cost `k`, and equality
tests at cost `1`. -/
@[reducible] def otccaOps {S : Sig} (keyT aeadAdT adT msgT ctT : Ty S)
    [DecidableEq adT.denote] [DecidableEq msgT.denote] [DecidableEq ctT.denote]
    (ae : AEADScheme keyT.denote aeadAdT.denote msgT.denote ctT.denote) (k : ℕ)
    (saltT : Ty S) [DecidableEq saltT.denote]
    (saltOf : aeadAdT.denote → saltT.denote) : Ops S where
  Op := OtccaOp
  dom := fun
    | .enc => .prod keyT (.prod aeadAdT msgT)
    | .dec => .prod keyT (.prod aeadAdT ctT)
    | .saltOf => aeadAdT
    | .eqAD => .prod adT adT
    | .eqM => .prod msgT msgT
    | .eqC => .prod ctT ctT
    | .eqSalt => .prod saltT saltT
  cod := fun
    | .enc => ctT
    | .dec => .opt msgT
    | .saltOf => saltT
    | .eqAD | .eqM | .eqC | .eqSalt => .bool
  eval := fun
    | .enc, (key, a, m) => ae.enc key a m
    | .dec, (key, a, c) => ae.dec key a c
    | .saltOf, a => saltOf a
    | .eqAD, (a₁, a₂) => a₁ == a₂
    | .eqM, (m₁, m₂) => m₁ == m₂
    | .eqC, (c₁, c₂) => c₁ == c₂
    | .eqSalt, (s₁, s₂) => s₁ == s₂
  cost := fun
    | .enc | .dec | .saltOf => k
    | .eqAD | .eqM | .eqC | .eqSalt => 1

/-- Sampler table drawing from the game's AD-dependent ideal ciphertext distribution `ideal` at
cost `kIdeal`. -/
@[reducible] def idealSamplers {S : Sig} (adT ctT : Ty S)
    (ideal : adT.denote → ProbComp ctT.denote) (kIdeal : ℕ) : Samplers S where
  Samp := Unit
  sDom := fun _ => adT
  sTy := fun _ => ctT
  samp := fun _ a => ideal a
  sCost := fun _ => kIdeal

inductive OtccaTag | enc | dec

/-- Target oracle interface for `unifSpec + AEADScheme.otccaSpec` with unit query cost and
`idealSamplers`. -/
def otccaIface {S : Sig} (adT msgT ctT : Ty S) (ideal : adT.denote → ProbComp ctT.denote)
    (kIdeal : ℕ) :
    Iface S (unifSpec + CryptoGames.AEADScheme.otccaSpec adT.denote msgT.denote ctT.denote) where
  fwdU := fun n =>
    query (spec := unifSpec + CryptoGames.AEADScheme.otccaSpec adT.denote msgT.denote ctT.denote) (.inl n)
  uCost := 1
  Tag := OtccaTag
  dom := fun
    | .enc => .prod adT msgT
    | .dec => .prod adT ctT
  cod := fun
    | .enc => .opt ctT
    | .dec => .opt msgT
  enc := fun
    | .enc, x => .inr (.inl x)
    | .dec, x => .inr (.inr x)
  dec := fun
    | .enc, _, u => u
    | .dec, _, u => u
  qCost := fun _ => 1
  smp := idealSamplers adT ctT ideal kIdeal

/-- Source game codec for `AEADScheme.otccaSpec` (`codecCost = 2`). -/
def otccaCodec {S : Sig} (adT msgT ctT : Ty S) :
    GameCodec S (CryptoGames.AEADScheme.otccaSpec adT.denote msgT.denote ctT.denote) where
  Q := .sum (.prod adT msgT) (.prod adT ctT)
  R := .sum (.opt ctT) (.opt msgT)
  qenc := fun
    | .inl x => .inl x
    | .inr x => .inr x
  rdec := fun
    | .inl _, r => match r with | .inl c => c | .inr _ => none
    | .inr _, r => match r with | .inr m => m | .inl _ => none
  codecCost := 2

end Computational.Proofs.SpecLemmas.Reductions.Primitives.OTCCA.CostedTables

-- AUTO-BRIDGE BEGIN
namespace CryptoGames.OTCCA.Costed
export Computational.Proofs.SpecLemmas.Reductions.Primitives.OTCCA.CostedTables (
  OtccaOp OtccaTag idealSamplers otccaCodec otccaIface otccaOps
)
end CryptoGames.OTCCA.Costed
namespace CryptoGames.OTCCA.Costed.OtccaOp
export Computational.Proofs.SpecLemmas.Reductions.Primitives.OTCCA.CostedTables.OtccaOp (
  dec enc eqAD eqC eqM eqSalt
  saltOf
)
end CryptoGames.OTCCA.Costed.OtccaOp
namespace CryptoGames.OTCCA.Costed.OtccaTag
export Computational.Proofs.SpecLemmas.Reductions.Primitives.OTCCA.CostedTables.OtccaTag (
  dec enc
)
end CryptoGames.OTCCA.Costed.OtccaTag
-- AUTO-BRIDGE END
