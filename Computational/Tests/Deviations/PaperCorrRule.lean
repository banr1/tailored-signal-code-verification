/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.Game
public import Computational.Proofs.CryptoGames.SM.GameProofDefs
import Computational.Tests.Deviations.PaperCorrRuleProof

/-!
# ACD19 Paper Corruption Rule (DEV-SM6)

**Checked by Lean.** Defines the Secure Messaging game using the corruption predicate of ACD19
Fig. 2 (`corrAllowedPaperDev6`: `corr-P` is refused only while a challenge from `P.other` is in
transit, whereas `GameState.corrAllowed` under DEV-SM6 refuses `corr-P` while any uncompromised
record from `P.other` is in transit) and proves the identical-until-`bad` bounds `dev6_priv_le`
and `dev6_auth_le`.

No generic black-box reduction eliminates `Pr[bad]`: when `A` queries `corr-P` while an
uncompromised non-challenge record from `Q` is in transit, `corrAllowed` blocks `corr-P` until
that record is delivered (mutating `P`'s state) or compromised, and corrupting `P` speculatively
before `Q` sends alters both leak adaptivity and the leak timestamp `max(t_A, t_B)`.

For the ACD19 Fig. 8 construction (`SM/Construction.lean`), authenticity (Theorem 8) does not rely
on DEV-SM6 because non-doomed runs corrupt the epoch-`t*` receiver `R` only while `t_R ≤ t*_L <
t* - 1`, before `R` holds epoch-`t*` FS-AEAD state. Privacy (Theorem 12) relies on DEV-SM6: paper
`corr-R` after delivering the epoch-`t*` challenge with other epoch-`t*` records still in transit
exposes `R`'s epoch-`t*` FS-AEAD receiver state, requiring an FS-AEAD game without DEV-FS6
(`FSAEAD/Defs.lean`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM

variable {Key St Msg Coins C : Type}

/-- ACD19 Fig. 2 `corr-P` guard: allowed iff no challenge from `P.other` is in transit. -/
def GameState.corrAllowedPaperDev6 (s : GameState St Msg C) (P : Party) : Bool :=
  !(s.chall.any (fun pos => pos.sender == P.other))

section Oracles

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg)
  [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]

local notation "GameM" => StateT (GameState St Msg C) ProbComp

/-- State monad pairing `GameState` with the monotone `bad` flag. -/
local notation "BadM" => StateT (GameState St Msg C × Bool) ProbComp

def liftBad {ι : Type} {spec' : OracleSpec.{0, 0} ι} (impl : QueryImpl spec' GameM) :
    QueryImpl spec' BadM := fun q sb =>
  (fun p => (p.1, (p.2, sb.2))) <$> impl q sb.1

/-- ACD19 Fig. 2 `corr-P` oracle, setting `bad` whenever `corrAllowed` would have refused the
query (DEV-SM6). -/
def corrImplPaper : QueryImpl (Party →ₒ Option St) BadM := fun P => do
  let (s, bad) ← get
  if s.win || !(s.corrAllowedPaperDev6 P) then return none
  set (s.afterCorr P, bad || !(s.corrAllowed P))
  return some (s.st P)

def oracleImplPaper : QueryImpl (spec St Msg Coins C) BadM :=
  liftBad (transmitImpl sm Δ qep + challImpl sm Δ qep cfg + deliverImpl sm cfg
    + injectImpl sm Δ qep cfg) + (corrImplPaper : QueryImpl (Party →ₒ Option St) BadM)

end Oracles

section Game

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
  [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]

/-- Executes adversary `A` under `oracleImplPaper` with hidden bit `b`, returning
`(guess, finalState, bad)`. -/
def runPaper (cfg : Config Msg) (b : Bool) (A : Adversary St Msg Coins C) :
    ProbComp (Bool × GameState St Msg C × Bool) := do
  let k ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C × Bool) ProbComp) + oracleImplPaper sm Δ qep cfg
  (simulateQ impl A).run (initState sm k b, false)

def authGamePaper (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) :
    ProbComp Bool := do
  let (_, s, _) ← runPaper sm Δ qep (Config.auth tStar) false A
  return (s.win && authLosingConditionsAvoided Δ tLStar tStar s)

noncomputable def authAdvantagePaper (tLStar : Option ℕ) (tStar : ℕ)
    (A : Adversary St Msg Coins C) : ℝ≥0∞ :=
  𝒟[authGamePaper sm Δ qep tLStar tStar A] {true}

def authBadPaper (tStar : ℕ) (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let (_, _, bad) ← runPaper sm Δ qep (Config.auth tStar) false A
  return bad

def privGamePaper (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', s, _) ← runPaper sm Δ qep (Config.priv tStar) b A
  if lastLeakGuessAdmissible Δ tLStar tStar && canon tStar s == tLStar then return (b == b')
  else $ᵗ Bool

noncomputable def privAdvantagePaper (tLStar : Option ℕ) (tStar : ℕ)
    (A : Adversary St Msg Coins C) : ℝ≥0∞ :=
  𝒟[privGamePaper sm Δ qep tLStar tStar A].boolBias

def privBadPaper (tStar : ℕ) (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (_, _, bad) ← runPaper sm Δ qep (Config.priv tStar) b A
  return bad

/-- Identical-until-`bad` privacy bound (DEV-SM6): `privAdvantagePaper` exceeds `privAdvantage`
by at most `2 · Pr[bad]`, since both games agree until `bad` is set and `boolBias` scales point
probability differences by `2`. -/
theorem dev6_priv_le (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) :
    privAdvantagePaper sm Δ qep tLStar tStar A ≤
      privAdvantage sm Δ qep tLStar tStar A + 2 * 𝒟[privBadPaper sm Δ qep tStar A] {true} := by
  exact Dev6Proof.dev6_priv_le_proof sm Δ qep tLStar tStar A

/-- Identical-until-`bad` authenticity bound (DEV-SM6): `authAdvantagePaper` exceeds
`authAdvantage` by at most `Pr[bad]`. -/
theorem dev6_auth_le (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) :
    authAdvantagePaper sm Δ qep tLStar tStar A ≤
      authAdvantage sm Δ qep tLStar tStar A + 𝒟[authBadPaper sm Δ qep tStar A] {true} := by
  exact Dev6Proof.dev6_auth_le_proof sm Δ qep tLStar tStar A

end Game

end CryptoGames.SM
