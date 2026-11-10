/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Shared uniform samplers for ReductionDsl reductions

**Trusted in part.** The theorems of `Computational/Theorems/` use every definition in this file
except `unifSamplers0`, which is checked by Lean; the ones they use are part of what you must read
to trust the result. See `Computational/docs/TRUSTED_BASE.md`.

Coin-only uniform sampler templates attached to target interfaces via `Iface.withSamp`, providing
uniform bits (`$ᵗ Bool`, cost `1`), bounded indices in `{0, …, N - 1}` (cost `bits N + 1`), and
uniform values on designated sampleable base sorts `f : B → S.Base` at declared block costs `w`
(at least each sort's block size).
-/

@[expose] public section

namespace ReductionDsl

open OracleComp

/-- Uniform index in `{0, …, N - 1}`, returning `0` when `N = 0`. -/
def sampleIndex (N : ℕ) : ProbComp ℕ :=
  if h : 0 < N then
    letI : NeZero N := ⟨Nat.ne_of_gt h⟩
    do let x ← $ᵗ (Fin N); return x.val
  else return 0

/-- Tags for coin-only uniform samplers: a bit, an index `< N`, or a sampleable base sort in `B`. -/
inductive UniformSamplerTag (B : Type) where
  | bool
  | index (N : ℕ)
  | base (b : B)

/-- Shared uniform samplers over `S` for bits (cost `1`), indices `< N` (cost `bits N + 1`), and
base sorts `f : B → S.Base` at declared block costs `w : B → ℕ`. -/
@[reducible] def unifSamplers {S : Sig} {B : Type} (f : B → S.Base) (w : B → ℕ)
    [∀ b, SampleableType (S.den (f b))] : Samplers S where
  Samp := UniformSamplerTag B
  sDom := fun _ => .unit
  sTy := fun
    | .bool => .bool
    | .index _ => .nat
    | .base b => .base (f b)
  samp := fun s _ => match s with
    | .bool => $ᵗ Bool
    | .index N => sampleIndex N
    | .base b => $ᵗ (S.den (f b))
  sCost := fun
    | .bool => 1
    | .index N => bits N + 1
    | .base b => w b

/-- Uniform bit and bounded-index samplers over `S`, with no base-sort samplers (`B = Empty`). -/
abbrev unifSamplers0 (S : Sig) : Samplers S :=
  @unifSamplers S Empty Empty.elim Empty.elim (fun b => b.elim)

end ReductionDsl
