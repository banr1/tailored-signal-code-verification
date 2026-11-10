/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.Game
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Party
public import Computational.Proofs.CryptoGames.SM.PartyProofDefs

/-!
# Proof-side definitions for the secure-messaging game

Defines hybrid game configurations (`Config.full`, `corr`, `priv`, `h2`, `h3`), oracle implementations (`deliverImpl`, `injectImpl`, `corrImpl`, `oracleImpl`), and game/advantage wrappers over `LibsignalBinary/Specifications/CryptoGames/SM/Game.lean`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
namespace CryptoGames
namespace SM
variable {Key St Msg Coins C : Type}
namespace Config

/-- Full Fig. 2 game (`H0`): correctness win, full injections, and challenges in every epoch. -/
def full : Config Msg :=
  { deliverWin := true, injectFull := fun _ => true, challAllowedIn := fun _ => true,
    challMsg := fun _ => none }

/-- Correctness game: no challenges and reduced injections. -/
def corr : Config Msg :=
  { deliverWin := true, injectFull := fun _ => false, challAllowedIn := fun _ => false,
    challMsg := fun _ => none }

/-- Privacy game for epoch `t*`: no correctness win, reduced injections, and challenges only in `t*`. -/
def priv (tStar : ℕ) : Config Msg :=
  { deliverWin := false, injectFull := fun _ => false, challAllowedIn := fun t => t == tStar,
    challMsg := fun _ => none }

/-- Hybrid `H2`: `H1` with reduced injections. -/
def h2 : Config Msg :=
  { deliverWin := false, injectFull := fun _ => false, challAllowedIn := fun _ => true,
    challMsg := fun _ => none }

/-- Hybrid `H3,i`: `H2` with challenges in epochs `t < i` encrypting `mbar` (index shifted by one from ACD19 so `h3 0 mbar` is `H2`; DEV-SM19). -/
def h3 (i : ℕ) (mbar : Msg) : Config Msg :=
  { deliverWin := false, injectFull := fun _ => false, challAllowedIn := fun _ => true,
    challMsg := fun t => if t < i then some mbar else none }

end Config

def ltOpt (tL : Option ℕ) (t : ℕ) : Bool :=
  match tL with
  | none => true
  | some l => decide (l < t)

namespace GameState
variable (s : GameState St Msg C) (Δ qep : ℕ)

/-- **DEV-SM5 (libsignal): correctness only inside the skip window.** `deliver` demands correctness only for uncompromised records with index at most `maxAcc + maxSkip + 1`, matching libsignal's bounded forward skipping (`MAX_FORWARD_JUMPS`) and exempting positions where an accepted injection may have altered receiver state. -/
def mustBeCorrect (maxSkip : ℕ) (P : Party) (r : Record Msg C) : Bool :=
  !(s.comp.contains r.pos) && decide (r.pos.idx ≤ s.maxAcc P r.pos.epoch + maxSkip + 1)

end GameState
section Oracles
variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg)
  [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
local notation "GameM" => StateT (GameState St Msg C) ProbComp

/-- **DEV-SM4 (formalization): rejected ciphertexts change nothing.** In `deliver` (and `injectImpl`), a rejected `receive` leaves party states, epoch counters, and in-transit records unchanged (matching DEV-FS5; see also DEV-SM5). -/
def deliverImpl : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) GameM :=
  fun ⟨P, c⟩ => do
    let s ← get
    if s.win then return none
    match s.inTransit P.other c with
    | none => return none
    | some r =>
      let must := cfg.deliverWin && s.mustBeCorrect sm.maxSkip P r
      match sm.receive (s.st P) c with
      | none =>
        if must then set { s with win := true }
        return some .rejected
      | some (st', t', i', m') =>
        let s₁ := s.accept P st' r.pos
        if must && !(decide ((t', i', m') = (r.pos.epoch, r.pos.idx, r.msg))) then
          set { s₁ with win := true }
        else
          set s₁
        return some (.accepted t' i' (if s.chall.contains r.pos then none else some m'))

/-- Fig. 2 `inject-P(c)`: processes trivial accepted ciphertexts and sets `win` on non-trivial forgeries when `cfg.injectFull` holds. -/
def injectImpl : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) GameM :=
  fun ⟨P, c⟩ => do
    let s ← get
    if s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) then return none
    match sm.receive (s.st P) c with
    | none => return some .rejected
    | some (st', t', i', m') =>
      if qep + 1 < t' then return some .rejected
      let pos : Pos := ⟨P.other, t', i'⟩
      if s.trivial Δ pos then
        set (s.accept P st' pos)
        return some (.accepted t' i' (some m'))
      else
        if cfg.injectFull t' then set { s with win := true }
        return some .rejected

/-- Fig. 2 `corr-P`: refused while a challenge or any uncompromised record from `P.other` (DEV-SM6) is in transit. -/
def corrImpl : QueryImpl (Party →ₒ Option St) GameM := fun P => do
  let s ← get
  if s.win || !(s.corrAllowed P) then return none
  set (s.afterCorr P)
  return some (s.st P)

/-- **DEV-SM1 (formalization): `req` and `win`, as in ACD19 §2.1.** Failed `req` checks return `none` without mutating game state (undoing any `ep-mgmt` step), and once `win` is set every oracle returns `none`. -/
def oracleImpl : QueryImpl (spec St Msg Coins C) GameM :=
  transmitImpl sm Δ qep + challImpl sm Δ qep cfg + deliverImpl sm cfg + injectImpl sm Δ qep cfg
    + (corrImpl : QueryImpl _ GameM)

end Oracles
section Game
variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
  [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]

def run (cfg : Config Msg) (b : Bool) (A : Adversary St Msg Coins C) :
    ProbComp (Bool × GameState St Msg C) := do
  let k ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) ProbComp) + oracleImpl sm Δ qep cfg
  (simulateQ impl A).run (initState sm k b)

/-- Hidden-bit game for variant `cfg`: the adversary wins by guessing `b` or setting `win`. -/
def game (cfg : Config Msg) (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', s) ← run sm Δ qep cfg b A
  return (b == b' || s.win)

/-- **DEV-SM10 (formalization): advantages are biases.** Indistinguishability advantages use VCVio's `boolBias` (`2 · |Pr[win] − 1/2|`) with `b = true` selecting `m₁`, while correctness and authenticity advantages are winning probabilities (inducing the constant factors tracked in DEV-SM20). -/
noncomputable def hybridAdvantage (cfg : Config Msg) (A : Adversary St Msg Coins C) : ℝ≥0∞ :=
  𝒟[game sm Δ qep cfg A].boolBias

noncomputable def advantage (A : Adversary St Msg Coins C) : ℝ≥0∞ :=
  hybridAdvantage sm Δ qep Config.full A

/-- Correctness game: the adversary wins by setting `win`. -/
def corrGame (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let (_, s) ← run sm Δ qep Config.corr false A
  return s.win

noncomputable def corrAdvantage (A : Adversary St Msg Coins C) : ℝ≥0∞ :=
  𝒟[corrGame sm Δ qep A] {true}

def lastLeakGuessAdmissible (tLStar : Option ℕ) (tStar : ℕ) : Bool := healedBy tLStar Δ tStar

/-- **DEV-SM9 (formalization): simplified games are evaluated at the end, with an exact `t*_L`.** Returns the largest leak time below `t*` (`none` if none), used at the end of `authGame` and `privGame` so admissible guesses `t*_L` partition the runs. -/
def canon (tStar : ℕ) (s : GameState St Msg C) : Option ℕ :=
  (s.leaks.filter (· < tStar)).max?

/-- Checks that the authenticity losing conditions did not occur and `t*_L = canon t* s` (DEV-SM9). -/
def authLosingConditionsAvoided (tLStar : Option ℕ) (tStar : ℕ) (s : GameState St Msg C) : Bool :=
  lastLeakGuessAdmissible Δ tLStar tStar
    && canon tStar s == tLStar
    && s.leaks.all (fun l => !(ltOpt tLStar l && decide (l < tStar)))
    && s.corrs.all (fun pe => !(pe.1 == Party.receiverOf tStar && ltOpt tLStar pe.2))

/-- Authenticity game with guesses `t*_L` and `t*`. -/
def authGame (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let (_, s) ← run sm Δ qep (Config.auth tStar) false A
  return (s.win && authLosingConditionsAvoided Δ tLStar tStar s)

noncomputable def authAdvantage (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) :
    ℝ≥0∞ :=
  𝒟[authGame sm Δ qep tLStar tStar A] {true}

/-- Privacy game with guesses `t*_L` and `t*`, returning a fresh bit unless `t*_L` is admissible and equals `canon t* s` (DEV-SM9). -/
def privGame (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', s) ← run sm Δ qep (Config.priv tStar) b A
  if lastLeakGuessAdmissible Δ tLStar tStar && canon tStar s == tLStar then return (b == b')
  else $ᵗ Bool

noncomputable def privAdvantage (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) :
    ℝ≥0∞ :=
  𝒟[privGame sm Δ qep tLStar tStar A].boolBias

end Game
end SM
end CryptoGames
