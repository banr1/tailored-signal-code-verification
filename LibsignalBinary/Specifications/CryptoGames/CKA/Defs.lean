/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Party
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.SimSemantics.Append.Core
import VCVio.EvalDist.Monad.Bool
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Continuous key agreement (CKA): syntax and security game

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use every
definition in this file: read them. The theorems here are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Defines continuous key agreement (`CKAScheme`) and its synchronous ping-pong real-or-random
security game (`CKA.game`, `CKA.advantage`), following ACD19 §4.1.1, Defs. 12–13 and Fig. 3.
Odd epochs have `A` send and `B` receive; even epochs swap roles. A passive adversary may supply
sender coins (`sendWithAdversaryCoinsImpl`) or corrupt states (`corrImpl`) outside the healing
window around challenge epoch `t*` (`allowCorr` for `max(t_A, t_B) ≤ t* − 2`, or `finished` once
`t_P ≥ t* + Δ`). Related CKA deviations appear in `CKA/DDHDefs.lean` (DEV-CKA9),
`Computational/Proofs/CryptoGames/CKA/DDH.lean` (DEV-CKA8), and `CKA/LibsignalCKA.lean`
(DEV-CKA10, DEV-CKA17).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames

/-- ACD19 Def. 12: a continuous-key-agreement (CKA) scheme with initialization keys `Key`, states
`State`, sender coins `Coins`, messages `Msg`, and output keys `CKey`. -/
structure CKAScheme (Key State Coins Msg CKey : Type) where
  /-- `CKA-Init-A`: `A`'s initial state `γ_A` from shared key `k`. -/
  initA : Key → State
  /-- `CKA-Init-B`: `B`'s initial state `γ_B` from shared key `k`. -/
  initB : Key → State
  /-- `CKA-S(γ; r)`: send with coins `r`, returning `(γ', T, I)`.

  **DEV-CKA1 (formalization): explicit sender coins.** ACD19 Fig. 3 writes `CKA-S(γ; r)` for a
  randomized algorithm. Here `send` is a deterministic function of the state and explicit coins
  `r : Coins`. The game samples `r` uniformly for `send-P` and `chall-P`, and takes it from the
  adversary for `send-P'`. Effect: none. -/
  send : State → Coins → State × Msg × CKey
  /-- `CKA-R(γ, T)`: receive `T`, returning `(γ', I)`. -/
  receive : State → Msg → State × CKey

namespace CKAScheme

variable {Key State Coins Msg CKey : Type}

end CKAScheme

namespace CKA

/-- ACD19 Fig. 3 oracle interface (`none` = refused). -/
abbrev spec (State Coins Msg CKey : Type) :=
  (Party →ₒ Option (Msg × CKey))              -- send-P
  + ((Party × Coins) →ₒ Option (Msg × CKey))  -- send-P' (r)
  + (Party →ₒ Option (Msg × CKey))            -- chall-P
  + (Party →ₒ Option Unit)                    -- receive-P
  + (Party →ₒ Option State)                   -- corr-P

/-- Computations with own coins plus the Fig. 3 CKA oracles. -/
abbrev AdversaryComp (State Coins Msg CKey : Type) :=
  OracleComp (unifSpec + spec State Coins Msg CKey)

/-- A CKA adversary outputting a hidden-bit guess. -/
abbrev Adversary (State Coins Msg CKey : Type) := AdversaryComp State Coins Msg CKey Bool

variable {Key State Coins Msg CKey : Type}

section Queries

local notation "Comp" => AdversaryComp State Coins Msg CKey

end Queries

/-- ACD19 Fig. 3 game state. -/
structure GameState (State Msg : Type) where
  /-- Party CKA states `(γ_A, γ_B)`.

  **DEV-CKA6 (formalization): one state type.** ACD19 Fig. 3 names the states `γ_A` and `γ_B`
  without fixing their types. Here both parties' states have the same type `State`. Effect: none
  (a scheme with two state types uses their sum). -/
  st : Party → State
  /-- Epoch counters `(t_A, t_B)`. -/
  epoch : Party → ℕ := fun _ => 0
  /-- Hidden bit (`true` = random challenge key). -/
  b : Bool
  /-- Latest message `T_t` in transit to the receiving party. -/
  lastMsg : Option Msg := none

namespace GameState

variable (s : GameState State Msg)

/-- Ping-pong send condition: both parties are at the same epoch and `P` sends in the next epoch.

**DEV-CKA2 (formalization): `req` and ping-pong order.** ACD19 states the ping-pong order in prose
(§4.1.1) and aborts on a failing `req`. Here a call out of order, or with a failing `req`, returns
`none` and leaves the state unchanged; the epoch counter grows only on success. Effect: none. -/
def canSend (P : Party) : Bool :=
  s.epoch P == s.epoch P.other && P.sendsIn (s.epoch P + 1)

/-- Ping-pong receive condition: `P.other` is one epoch ahead of `P`. -/
def canReceive (P : Party) : Bool :=
  s.epoch P.other == s.epoch P + 1

/-- `allow-corr :⇔ max(t_A, t_B) ≤ t* − 2`. -/
def allowCorr (tStar : ℕ) : Bool :=
  decide (max (s.epoch .A) (s.epoch .B) + 2 ≤ tStar)

/-- `finished_P :⇔ t_P ≥ t* + Δ`. -/
def finished (Δ tStar : ℕ) (P : Party) : Bool :=
  decide (tStar + Δ ≤ s.epoch P)

/-- Update `s` after `P` sends `T` and transitions to state `γ`. -/
def afterSend (P : Party) (γ : State) (T : Msg) : GameState State Msg :=
  { s with st := Function.update s.st P γ,
           epoch := Function.update s.epoch P (s.epoch P + 1),
           lastMsg := some T }

/-- Update `s` after `P` receives and transitions to state `γ`. -/
def afterReceive (P : Party) (γ : State) : GameState State Msg :=
  { s with st := Function.update s.st P γ,
           epoch := Function.update s.epoch P (s.epoch P + 1) }

end GameState

/-! ### Oracles -/

section Oracles

variable (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ)
  [SampleableType Coins] [SampleableType CKey]

local notation "GameM" => StateT (GameState State Msg) ProbComp

/-- ACD19 Fig. 3 `send-P`: outside epoch `t*`, run `CKA-S` with fresh coins and return `(T, I)`.

**DEV-CKA3 (formalization): no plain send in the challenge epoch.** ACD19 Fig. 3 lets the
adversary call `send-P` instead of `chall-P` in epoch `t*` (it then gets no challenge). Here
`send-P` is refused in epoch `t*`, so that the DDH reduction can embed its challenge there.
Effect: w.l.o.g., proved: `CKA.advantagePaper_eq` (`Computational/Tests/Deviations/PaperFaithfulSendProof.lean`) shows that
every adversary of the paper's game has the same advantage as a converted adversary here. -/
def sendImpl : QueryImpl (Party →ₒ Option (Msg × CKey)) GameM := fun P => do
  let s ← get
  if !(s.canSend P) || s.epoch P + 1 == tStar then return none
  let r ← ($ᵗ Coins : ProbComp Coins)
  let out := cka.send (s.st P) r
  set (s.afterSend P out.1 out.2.1)
  return some out.2

/-- ACD19 Fig. 3 `send-P'(r)`: run `CKA-S` with adversarial coins `r` while `t_P + 1 ≤ t* − 2`. -/
def sendWithAdversaryCoinsImpl : QueryImpl ((Party × Coins) →ₒ Option (Msg × CKey)) GameM := fun ⟨P, r⟩ => do
  let s ← get
  if !(s.canSend P) || !decide (s.epoch P + 1 + 2 ≤ tStar) then return none
  let out := cka.send (s.st P) r
  set (s.afterSend P out.1 out.2.1)
  return some out.2

/-- ACD19 Fig. 3 `chall-P`: in epoch `t*`, run `CKA-S` with fresh coins and return `(T, I)` if
`b = false` or `(T, I')` for uniform `I'` if `b = true`. -/
def challImpl : QueryImpl (Party →ₒ Option (Msg × CKey)) GameM := fun P => do
  let s ← get
  if !(s.canSend P) || s.epoch P + 1 != tStar then return none
  let r ← ($ᵗ Coins : ProbComp Coins)
  let out := cka.send (s.st P) r
  set (s.afterSend P out.1 out.2.1)
  if s.b then
    let I' ← ($ᵗ CKey : ProbComp CKey)
    return some (out.2.1, I')
  else
    return some out.2

/-- ACD19 Fig. 3 `receive-P`: run `CKA-R` on `lastMsg` without revealing the derived key.

**DEV-CKA4 (formalization): `receive-P` outputs nothing, and the game does not end.** As in
ACD19 Fig. 3, the receiver's key is not given to the adversary. ACD19 §4.1.1 ends the game once
both states are revealed after the challenge phase ("not made explicit"); here it continues, which
cannot help the adversary. Effect: none. -/
def receiveImpl : QueryImpl (Party →ₒ Option Unit) GameM := fun P => do
  let s ← get
  if !(s.canReceive P) then return none
  match s.lastMsg with
  | none => return none
  | some T =>
    set (s.afterReceive P (cka.receive (s.st P) T).1)
    return some ()

/-- ACD19 Fig. 3 `corr-P`: reveal `γ_P` if `allowCorr` or `finished` holds. -/
def corrImpl : QueryImpl (Party →ₒ Option State) GameM := fun P => do
  let s ← get
  if s.allowCorr tStar || s.finished Δ tStar P then return some (s.st P) else return none

/-- Combined Fig. 3 oracle implementation. -/
def oracleImpl : QueryImpl (spec State Coins Msg CKey) GameM :=
  sendImpl cka tStar + sendWithAdversaryCoinsImpl cka tStar + challImpl cka tStar + receiveImpl cka
    + (corrImpl Δ tStar : QueryImpl _ GameM)

end Oracles

/-! ### The game -/

section Game

variable (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ)
  [SampleableType Key] [SampleableType Coins] [SampleableType CKey]

/-- Initial state after Fig. 3 `init` for key `k` and hidden bit `b`. -/
def initState (k : Key) (b : Bool) : GameState State Msg :=
  { st := fun P => match P with
      | .A => cka.initA k
      | .B => cka.initB k,
    b }

/-- ACD19 Fig. 3 hidden-bit game for challenge epoch `t*` and healing parameter `Δ`.

**DEV-CKA5 (formalization): `t*` and `b`.** ACD19 Fig. 3 starts with `init(t*)`. Here `t*` is a
parameter of the game, and security quantifies over all `t*`. The hidden bit `b = true` means
*random* (Fig. 3's `b = 1`). Effect: none. -/
def game (A : Adversary State Coins Msg CKey) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState State Msg) ProbComp) + oracleImpl cka Δ tStar
  let b' ← (simulateQ impl A).run' (initState cka k b)
  return b == b'

/-- `Adv^{CKA}_{ror,Δ}(A)` (ACD19 Def. 13): the bias `2·|Pr[b = b'] − 1/2|`.

**DEV-CKA7 (formalization): advantage as a bias.** ACD19 §2.1 prints the advantage as
`2·P[A wins] − 1/2`, a typo. Lean uses the intended bias `2·|Pr[b = b'] − 1/2|`, VCVio's
`boolBias`. Effect: none. -/
noncomputable def advantage (A : Adversary State Coins Msg CKey) : ℝ≥0∞ :=
  𝒟[game cka Δ tStar A].boolBias

end Game

end CKA

end CryptoGames
