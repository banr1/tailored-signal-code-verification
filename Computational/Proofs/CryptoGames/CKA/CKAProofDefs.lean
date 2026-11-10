/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.CKA.Defs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Party
import VCVio.EvalDist.Monad.Bool
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# CKA Correctness and Game Helpers

Correctness predicate (`AgreesFrom`, `Correct`), oracle query shorthands, and fixed-bit game branch
for continuous key agreement (`CKAScheme`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
namespace CryptoGames
namespace CKAScheme
variable {Key State Coins Msg CKey : Type}

/-- Honest alternating execution from states `(γS, γR)` with sender coins `rs` yields matching keys in every round. -/
def AgreesFrom (cka : CKAScheme Key State Coins Msg CKey) : State → State → List Coins → Prop
  | _, _, [] => True
  | γS, γR, r :: rs =>
    (cka.send γS r).2.2 = (cka.receive γR (cka.send γS r).2.1).2 ∧
      cka.AgreesFrom (cka.receive γR (cka.send γS r).2.1).1 (cka.send γS r).1 rs

/-- CKA correctness: from initialized states `(initA k, initB k)`, honest alternating rounds always agree on the output key. -/
def Correct (cka : CKAScheme Key State Coins Msg CKey) : Prop :=
  ∀ (k : Key) (rs : List Coins), cka.AgreesFrom (cka.initA k) (cka.initB k) rs

end CKAScheme
namespace CKA
variable {Key State Coins Msg CKey : Type}
section Queries
local notation "Comp" => AdversaryComp State Coins Msg CKey

/-- Query `send-P`. -/
def sendQuery (P : Party) : Comp (Option (Msg × CKey)) :=
  query (spec := unifSpec + spec State Coins Msg CKey) (.inr (.inl (.inl (.inl (.inl P)))))

/-- Query `send-P'(r)`. -/
def sendWithAdversaryCoinsQuery (P : Party) (r : Coins) : Comp (Option (Msg × CKey)) :=
  query (spec := unifSpec + spec State Coins Msg CKey) (.inr (.inl (.inl (.inl (.inr (P, r))))))

/-- Query `chall-P`. -/
def challQuery (P : Party) : Comp (Option (Msg × CKey)) :=
  query (spec := unifSpec + spec State Coins Msg CKey) (.inr (.inl (.inl (.inr P))))

/-- Query `receive-P`. -/
def receiveQuery (P : Party) : Comp (Option Unit) :=
  query (spec := unifSpec + spec State Coins Msg CKey) (.inr (.inl (.inr P)))

/-- Query `corr-P`. -/
def corrQuery (P : Party) : Comp (Option State) :=
  query (spec := unifSpec + spec State Coins Msg CKey) (.inr (.inr P))

end Queries
section Game
variable (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ)
  [SampleableType Key] [SampleableType Coins] [SampleableType CKey]

/-- Runs the CKA game with fixed hidden bit `b` and returns the adversary's guess. -/
def branch (b : Bool) (A : Adversary State Coins Msg CKey) : ProbComp Bool := do
  let k ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState State Msg) ProbComp) + oracleImpl cka Δ tStar
  (simulateQ impl A).run' (initState cka k b)

/-- Expresses CKA advantage as the Boolean distance between the `b = true` and `b = false` branches. -/
theorem advantage_eq_boolDist (A : Adversary State Coins Msg CKey) :
    advantage cka Δ tStar A =
      𝒟[branch cka Δ tStar true A].boolDist 𝒟[branch cka Δ tStar false A] := by
  have hcoin : ∀ x : Bool, 𝒟[($ᵗ Bool : ProbComp Bool)] {x} = 1 / 2 := by
    intro x
    simp
  rw [← evalDist_boolBias_bind_coin ($ᵗ Bool) _ _ (hcoin true) (hcoin false)]
  unfold advantage game
  congr 2
  refine bind_congr fun b => ?_
  cases b <;> simp [branch]

end Game
end CKA
end CryptoGames
