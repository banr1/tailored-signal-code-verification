/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.SimSemantics.Append.Core
import VCVio.EvalDist.Monad.Bool
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# PRF-PRNGs: syntax and security game

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use every
definition in this file: read them. The theorems here are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Defines PRF-PRNGs (`PRFPRNG`, ACD19 §4.3.1 Def. 16) and their combined PRNG/PRF hidden-bit security
game (`PRFPRNG.game`, `PRFPRNG.advantage`, Def. 17 and Fig. 7). In PRNG mode (`processImpl`,
`challPrngImpl`), outputs are pseudorandom whenever the state is uncorrupted or healed by a uniform
input (`none`); in PRF mode (`challPrfImpl`), `up σ ·` on an uncorrupted state without state update
is indistinguishable from a lazily sampled random function.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames

/-- ACD19 Def. 16: a PRF-PRNG with initialization keys `Key`, states `State`, inputs `Input`, and
outputs `Output`. -/
structure PRFPRNG (Key State Input Output : Type) where
  /-- `P-Init(k)`: initial state. -/
  init : Key → State
  /-- `P-Up(σ, I)`: absorb input `I`, returning the new state and output. -/
  up : State → Input → State × Output

namespace PRFPRNG

/-- ACD19 Fig. 7 oracle interface (`none` = refused; `Option Input = none` denotes uniform input
sampling `⊥`). -/
abbrev spec (State Input Output : Type) :=
  (Option Input →ₒ Option Output)        -- process(I)
  + (Option Input →ₒ Option Output)      -- chall-prng(I)
  + (Input →ₒ Option (State × Output))   -- chall-prf(I)
  + (Unit →ₒ Option State)               -- corr

/-- Computations with own coins plus the Fig. 7 PRF-PRNG oracles. -/
abbrev AdversaryComp (State Input Output : Type) :=
  OracleComp (unifSpec + spec State Input Output)

/-- A PRF-PRNG adversary outputting a hidden-bit guess. -/
abbrev Adversary (State Input Output : Type) := AdversaryComp State Input Output Bool

variable {Key State Input Output : Type}

section Queries

local notation "Comp" => AdversaryComp State Input Output

end Queries

/-- ACD19 Fig. 7 game state. -/
structure GameState (State Input Output : Type) where
  /-- Current state `σ`. -/
  σ : State
  /-- Hidden bit (`true` = random outputs).

  **DEV-PRNG5 (formalization): `b = true` means random.** ACD19 Fig. 7's `b = 1` is `true`.
  Effect: none. -/
  b : Bool
  /-- Whether the current state is known to the adversary. -/
  corr : Bool := false
  /-- Whether a PRNG challenge has been issued. -/
  prng : Bool := false
  /-- Whether a PRF challenge has been issued. -/
  prf : Bool := false
  /-- Lookup table of the lazily sampled random function `F`.

  **DEV-PRNG4 (formalization): `F` is sampled lazily.** ACD19 Fig. 7 samples a random function
  `F`. Here its table is part of the game state and filled on demand. Effect: none. -/
  table : List (Input × Output) := []

section Oracles

variable (P : PRFPRNG Key State Input Output) [SampleableType Input] [SampleableType Output]

local notation "GameM" => StateT (GameState State Input Output) ProbComp

/-- Fig. 7 `sam-if-nec(I)`: return `(I, false)` if `I` is provided, or sample a uniform `I` and
return `(I, true)`. -/
def samIfNec (I : Option Input) : ProbComp (Input × Bool) :=
  match I with
  | some I => pure (I, false)
  | none => do
    let I ← ($ᵗ Input : ProbComp Input)
    pure (I, true)

/-- Fig. 7 `process(I)`: absorb `I` (healing `corr` if `I = none`) and return `R`; refused once
`prf` is set.

**DEV-PRNG2 (paper fix): PRF mode freezes the state.** In ACD19 Fig. 7, `process` stays available
after `chall-prf`. Then the game is trivially insecure: `chall-prf(I)` returns the real next state
`σ'`, `process(I)` moves the game to `σ'`, and `chall-prf(I₂)` on `σ'` is answered with `F(I₂)` or
`P-Up(σ', I₂).2`, which the adversary can compute. Here `process` is refused once `prf` is set.
Effect: none for the SM proof: ACD19 Lemma 10 continues from the returned `σ'` by itself. -/
def processImpl : QueryImpl (Option Input →ₒ Option Output) GameM := fun I => do
  let s ← get
  if s.prf then return none
  let (I, fresh) ← (samIfNec I : ProbComp (Input × Bool))
  let (σ', R) := P.up s.σ I
  set { s with σ := σ', corr := s.corr && !fresh }
  return some R

/-- Fig. 7 `chall-prng(I)`: require an uncorrupted state (after `samIfNec`) and `¬prf`; update `σ`
and return `R` (`b = false`) or a uniform output (`b = true`). -/
def challPrngImpl : QueryImpl (Option Input →ₒ Option Output) GameM := fun I => do
  let s ← get
  let (I, fresh) ← (samIfNec I : ProbComp (Input × Bool))
  if (s.corr && !fresh) || s.prf then return none
  let (σ', R) := P.up s.σ I
  set { s with σ := σ', corr := false, prng := true }
  if s.b then
    let R' ← ($ᵗ Output : ProbComp Output)
    return some R'
  else
    return some R

/-- Fig. 7 `chall-prf(I)`: require `¬corr` and `¬prng`; evaluate `(σ', R) = P.up σ I` without
updating `σ`, returning `(σ', R)` (`b = false`) or `(σ', F(I))` (`b = true`). -/
def challPrfImpl [DecidableEq Input] :
    QueryImpl (Input →ₒ Option (State × Output)) GameM := fun I => do
  let s ← get
  if s.corr || s.prng then return none
  let (σ', R) := P.up s.σ I
  set { s with prf := true }
  if s.b then
    match s.table.lookup I with
    | some R' => return some (σ', R')
    | none =>
      let R' ← ($ᵗ Output : ProbComp Output)
      modify fun s => { s with table := (I, R') :: s.table }
      return some (σ', R')
  else
    return some (σ', R)

/-- Fig. 7 `corr`: reveal `σ` and mark `corr := true`; refused once `prf` is set.

**DEV-PRNG1 (paper fix): `corr` sets the flag `corr`.** ACD19 Fig. 7's `corr` never sets `corr ←
true` (only `init` and `sam-if-nec` assign it), so `req ¬corr` in the challenge oracles would be
vacuous and the game trivially insecure (corrupt, then compute `P-Up` yourself). Here `corr` sets
it, as the text intends ("the attacker may obtain the state"). Effect: none (it repairs the game). -/
def corrImpl : QueryImpl (Unit →ₒ Option State) GameM := fun _ => do
  let s ← get
  if s.prf then return none
  set { s with corr := true }
  return some s.σ

/-- Combined Fig. 7 oracle implementation.

**DEV-PRNG3 (formalization): `req`, as in ACD19 §2.1.** A failing `req` returns `none` and leaves
the state unchanged, including the sampling of `I` by `sam-if-nec` (whose effect `corr ← false` is
then not applied). This is ACD19 §2.1's convention ("all actions by it are undone"). Effect: none. -/
def oracleImpl [DecidableEq Input] : QueryImpl (spec State Input Output) GameM :=
  processImpl P + challPrngImpl P + challPrfImpl P + (corrImpl : QueryImpl _ GameM)

end Oracles

/-! ### The game -/

section Game

variable (P : PRFPRNG Key State Input Output) [DecidableEq Input]
  [SampleableType Key] [SampleableType Input] [SampleableType Output]

/-- ACD19 Fig. 7 hidden-bit game. -/
def game (A : Adversary State Input Output) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState State Input Output) ProbComp) + oracleImpl P
  let b' ← (simulateQ impl A).run' { σ := P.init k, b }
  return b == b'

/-- `Adv^{PP}_P(A)` (ACD19 Def. 17): the bias `2·|Pr[b = b'] − 1/2|` (DEV-SM10). -/
noncomputable def advantage (A : Adversary State Input Output) : ℝ≥0∞ :=
  𝒟[game P A].boolBias

end Game

end PRFPRNG

end CryptoGames
