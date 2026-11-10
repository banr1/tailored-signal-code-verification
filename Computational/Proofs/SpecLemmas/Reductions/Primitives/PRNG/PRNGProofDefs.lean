/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
import VCVio.EvalDist.Monad.Bool
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# PRF-PRNG query helpers and branch decomposition

Oracle query wrappers for `PRFPRNG.spec` and fixed-bit game branch decomposition for
`PRFPRNG.advantage`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
namespace CryptoGames
namespace PRFPRNG
variable {Key State Input Output : Type}
section Queries
local notation "Comp" => AdversaryComp State Input Output

def processQuery (I : Option Input) : Comp (Option Output) :=
  query (spec := unifSpec + spec State Input Output) (.inr (.inl (.inl (.inl I))))

def challPrngQuery (I : Option Input) : Comp (Option Output) :=
  query (spec := unifSpec + spec State Input Output) (.inr (.inl (.inl (.inr I))))

def challPrfQuery (I : Input) : Comp (Option (State × Output)) :=
  query (spec := unifSpec + spec State Input Output) (.inr (.inl (.inr I)))

def corrQuery : Comp (Option State) :=
  query (spec := unifSpec + spec State Input Output) (.inr (.inr ()))

end Queries
section Game
variable (P : PRFPRNG Key State Input Output) [DecidableEq Input]
  [SampleableType Key] [SampleableType Input] [SampleableType Output]

/-- The PRF-PRNG game with a fixed challenge bit `b`. -/
def branch (b : Bool) (A : Adversary State Input Output) : ProbComp Bool := do
  let k ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState State Input Output) ProbComp) + oracleImpl P
  (simulateQ impl A).run' { σ := P.init k, b }

/-- `PRFPRNG.advantage` equals the boolean distance between `branch P true A` and
`branch P false A`. -/
theorem advantage_eq_boolDist (A : Adversary State Input Output) :
    advantage P A = 𝒟[branch P true A].boolDist 𝒟[branch P false A] := by
  have hcoin : ∀ x : Bool, 𝒟[($ᵗ Bool : ProbComp Bool)] {x} = 1 / 2 := by
    intro x
    simp
  rw [← evalDist_boolBias_bind_coin ($ᵗ Bool) _ _ (hcoin true) (hcoin false)]
  unfold advantage game
  congr 2
  refine bind_congr fun b => ?_
  cases b <;> simp [branch]

end Game
end PRFPRNG
end CryptoGames
