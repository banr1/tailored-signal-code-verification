/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForge

/-!
# `DeliverForgePaper` Game and Engine

**Checked by Lean.** Variant of the `DeliverForge` game, engine, reductions, and authenticity
simulators where party corruption uses ACD19 Fig. 2's `corrAllowedPaper` guard.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17

/-! ## Paper `corr` oracles -/

section OraclesDFPaper

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]

/-- Fig. 2 `corr-P` guard from ACD19: allowed while no challenge from `P.other` is in transit. -/
def _root_.CryptoGames.SM.GameState.corrAllowedPaper {St Msg C : Type}
    (s : GameState St Msg C) (P : Party) : Bool :=
  !(s.chall.any (fun pos => pos.sender == P.other))

def corrImplPaper : QueryImpl (Party →ₒ Option St) (StateT (GameState St Msg C) ProbComp) :=
  fun P => do
    let s ← get
    if s.win || !(s.corrAllowedPaper P) then return none
    set (s.afterCorr P)
    return some (s.st P)

def oracleImplPaper (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) [SampleableType Coins]
    (cfg : Config Msg) :
    QueryImpl (spec St Msg Coins C) (StateT (GameState St Msg C) ProbComp) :=
  transmitImpl sm Δ qep + challImpl sm Δ qep cfg + deliverImpl sm cfg +
    injectImpl sm Δ qep cfg +
    (DeliverForge.corrImplPaper : QueryImpl _ (StateT (GameState St Msg C) ProbComp))

def oracleImplBaseDFPaper (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) [SampleableType Coins]
    (sameHdr : C → C → Bool) (cfg : Config Msg) :
    QueryImpl (specDF St Msg Coins C) (StateT (GameState St Msg C) ProbComp) :=
  oracleImplPaper sm Δ qep cfg + deliverForgeBaseImpl sm Δ qep sameHdr cfg

abbrev fullImplBaseDFPaper (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) [SampleableType Coins]
    (sameHdr : C → C → Bool) (cfg : Config Msg) :
    QueryImpl (unifSpec + specDF St Msg Coins C) (StateT (GameState St Msg C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (GameState St Msg C) ProbComp) + oracleImplBaseDFPaper sm Δ qep sameHdr cfg

end OraclesDFPaper

/-! ## Paper engine and reductions -/

section EngineDFPaper

variable {ι : Type} {tspec : OracleSpec.{0, 0} ι}
  {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
  [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]

local notation "EMt" => EM tspec Γv T Sv SSv RSv M E HS

/-- Engine `corr-P` handler using `corrAllowedPaper`. -/
def corrEPaper (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv) (π : Policy) :
    QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS)) EMt := fun P => do
  let es ← get
  if es.abort || es.g.win || !(es.g.corrAllowedPaper P) then return none
  let s₁ := es.g.afterCorr P
  if π.leakDoom es.g s₁ || π.corrDoom es.g P then
    abortE
    return none
  match ← liftH (hk.reveal es.g P (es.g.st P)) with
  | none =>
    abortE
    return none
  | some st =>
    modify fun es => { es with g := s₁ }
    return some st

def implEDFPaper (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) :
    QueryImpl (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) EMt :=
  let i₀ : QueryImpl unifSpec EMt := coinsE
  let i₁ : QueryImpl (spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) EMt :=
    HAdd.hAdd
      (HAdd.hAdd
        (HAdd.hAdd
          (HAdd.hAdd (transmitE hk Δ qep π) (challE hk Δ qep cfg π))
          (deliverE hk maxSkip cfg))
        (injectE hk Δ qep cfg))
      (corrEPaper hk π)
  let i₂ : QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (RecvResult M)) EMt :=
    deliverForgeE hk Δ qep cfg
  HAdd.hAdd i₀ (HAdd.hAdd i₁ i₂)

def engRunDFPaper (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (b : Bool) (A : AdversaryDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) :
    TComp tspec (Option (Bool × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)) := do
  let (vs, h) ← init.run h₀
  match vs with
  | none => return none
  | some (vA, vB) =>
    let g : Ctx Γv T Sv SSv RSv M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := b }
    let (b', es) ← (simulateQ (implEDFPaper hk Δ qep maxSkip cfg π) A).run { g := g, h := h }
    return some (b', es)

end EngineDFPaper

section ReductionsDFPaper

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

def authSimDFPaper {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS Γv Sv SSv RSv : Type}
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (tL : Option ℕ) (tStar : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    TComp tspec Bool := do
  let π : Policy := ⟨true, tL, tStar⟩
  let r ← engRunDFPaper hk (2 + Δcka) qep fs.maxSkip (Config.auth tStar) π init h₀ false A
  return match r with
    | none => false
    | some (_, es) => authOut (2 + Δcka) π es

def redCKAAuthDFPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (tStar : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    CKA.Adversary Γ CCoins T I :=
  show CKA.AdversaryComp Γ CCoins T I Bool from
  authSimDFPaper fs Δcka qep (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
    (initCKA cka prng fs lam ⟨true, tL, tStar⟩) {} tL tStar A

def redPRNGAuthDFPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (tStar : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from
  authSimDFPaper fs Δcka qep (hooksPRNG cka prng fs ⟨true, tL, tStar⟩)
    (initPRNG cka prng fs lam ⟨true, tL, tStar⟩) {} tL tStar A

def redFSAuthDFPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (j : ℕ) (tL : Option ℕ) (tStar : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    FSAEAD.Adversary SS RS (Header T) M E :=
  show FSAEAD.AdversaryComp SS RS (Header T) M E Bool from do
  let _ ← engRunDFPaper (hooksFS cka prng fs Δcka ⟨true, tL, tStar⟩ j) (2 + Δcka) qep fs.maxSkip
    (Config.auth tStar) ⟨true, tL, tStar⟩ (initFS cka prng fs lam ⟨true, tL, tStar⟩ j) {} false A
  sampleT Bool

end ReductionsDFPaper

/-! ## Simulators `challSimDFPaper` and `challSimDF'Paper` -/

section SimDFPaper

variable {St Msg Coins C : Type}

local notation "CompDF" => AdversaryCompDF St Msg Coins C
local notation "RedMDF" => StateT (Mirror Msg C) (AdversaryCompDF St Msg Coins C)

def simCorrDFPaper : QueryImpl (Party →ₒ Option St) RedMDF := fun P => do
  let s ← get
  if !(s.corrAllowedPaper P) then return none
  let res ← StateT.lift (corrQueryDF (Msg := Msg) (Coins := Coins) (C := C) P)
  if res.isSome then set (s.afterCorr P)
  return res

def simOraclesDFPaper [DecidableEq C] (Δ qep : ℕ) : QueryImpl (specDF St Msg Coins C) RedMDF :=
  let i₁ : QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) RedMDF := simTransmitDF Δ qep
  let i₂ : QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) RedMDF := simChallDF Δ qep
  let i₃ : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) RedMDF := simDeliverDF
  let i₄ : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) RedMDF := simInjectDF
  let i₅ : QueryImpl (Party →ₒ Option St) RedMDF := simCorrDFPaper
  let i₆ : QueryImpl ((Party × C × C) →ₒ Option (RecvResult Msg)) RedMDF := simDeliverForgeDF
  HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅) i₆

def simImplDFPaper [DecidableEq C] (Δ qep : ℕ) :
    QueryImpl (unifSpec + specDF St Msg Coins C) RedMDF :=
  let c : QueryImpl unifSpec RedMDF := simCoinsDF
  let o : QueryImpl (specDF St Msg Coins C) RedMDF := simOraclesDFPaper Δ qep
  HAdd.hAdd c o

/-- Authenticity simulator `challSimDF` adapted to `corrAllowedPaper`. -/
def challSimDFPaper [DecidableEq C] (Δ qep : ℕ) (A : AdversaryDF St Msg Coins C) :
    AdversaryDF St Msg Coins C :=
  show AdversaryCompDF St Msg Coins C Bool from do
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : AdversaryCompDF St Msg Coins C Bool)
  (simulateQ (simImplDFPaper Δ qep) A).run' ({ st := fun _ => (), b } : Mirror Msg C)

def simTransmitDF'Paper (Δ qep : ℕ) :
    QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) RedMDF :=
  fun ⟨P, m, _r⟩ => do
    let s ← get
    let res ← StateT.lift (transmitQueryDF (St := St) P m none)
    match res, s.epMgmt Δ qep P false with
    | some c, some s₁ => set (s₁.record Δ P () ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ false)
    | _, _ => pure ()
    return res

def simChallDF'Paper (Δ qep : ℕ) :
    QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) RedMDF :=
  fun ⟨P, m₀, m₁, _r⟩ => do
    let s ← get
    match s.epMgmt Δ qep P false with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) then return none
      let mb := if s.b then m₁ else m₀
      let res ← StateT.lift (transmitQueryDF (St := St) P mb none)
      match res with
      | none => return none
      | some c =>
        set (s₁.record Δ P () ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, mb, c⟩ true)
        return some c

def simOraclesDF'Paper [DecidableEq C] (Δ qep : ℕ) : QueryImpl (specDF St Msg Coins C) RedMDF :=
  let i₁ : QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) RedMDF := simTransmitDF'Paper Δ qep
  let i₂ : QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) RedMDF :=
    simChallDF'Paper Δ qep
  let i₃ : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) RedMDF := simDeliverDF
  let i₄ : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) RedMDF := simInjectDF
  let i₅ : QueryImpl (Party →ₒ Option St) RedMDF := simCorrDFPaper
  let i₆ : QueryImpl ((Party × C × C) →ₒ Option (RecvResult Msg)) RedMDF := simDeliverForgeDF
  HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅) i₆

def simImplDF'Paper [DecidableEq C] (Δ qep : ℕ) :
    QueryImpl (unifSpec + specDF St Msg Coins C) RedMDF :=
  let c : QueryImpl unifSpec RedMDF := simCoinsDF
  let o : QueryImpl (specDF St Msg Coins C) RedMDF := simOraclesDF'Paper Δ qep
  HAdd.hAdd c o

/-- Coin-stripping authenticity simulator under `corrAllowedPaper`, replacing adversary-supplied
coins on `transmit` and `chall` with `none`. -/
def challSimDF'Paper [DecidableEq C] (Δ qep : ℕ) (A : AdversaryDF St Msg Coins C) :
    AdversaryDF St Msg Coins C :=
  show AdversaryCompDF St Msg Coins C Bool from do
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : AdversaryCompDF St Msg Coins C Bool)
  (simulateQ (simImplDF'Paper Δ qep) A).run' ({ st := fun _ => (), b } : Mirror Msg C)

end SimDFPaper

/-! ## Authenticity games -/

section GamesDFPaper

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]

def runBaseDFPaper (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : C → C → Bool) (cfg : Config Msg) (b : Bool)
    (B : AdversaryDF St Msg Coins C) : ProbComp (Bool × GameState St Msg C) := do
  let k ← $ᵗ Key
  (simulateQ (fullImplBaseDFPaper sm Δ qep sameHdr cfg) B).run (initState sm k b)

/-- Unguessed `DeliverForgePaper` win game returning `s.win` at `Config.h1`. -/
def forgeGameWinPaper (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : C → C → Bool) (B : AdversaryDF St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (_, s) ← runBaseDFPaper sm Δ qep sameHdr Config.h1 b B
  return s.win

/-- Guessed `DeliverForgePaper` authenticity game for target `(tLStar, tStar)`. -/
def forgeGameGuessedPaper (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : C → C → Bool) (tLStar : Option ℕ) (tStar : ℕ)
    (B : AdversaryDF St Msg Coins C) : ProbComp Bool := do
  let (_, s) ← runBaseDFPaper sm Δ qep sameHdr (Config.auth tStar) false B
  return s.win && authLosingConditionsAvoided Δ tLStar tStar s

noncomputable def forgeGuessedAdvantagePaper (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : C → C → Bool) (tLStar : Option ℕ) (tStar : ℕ)
    (B : AdversaryDF St Msg Coins C) : ℝ≥0∞ :=
  𝒟[forgeGameGuessedPaper sm Δ qep sameHdr tLStar tStar B] {true}

private theorem evalDist_bind_mono_paper {α : Type} (p : ProbComp α) (f g : α → ProbComp Bool)
    (h : ∀ a, 𝒟[f a] {true} ≤ 𝒟[g a] {true}) :
    𝒟[p >>= f] {true} ≤ 𝒟[p >>= g] {true} := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a
  | query_bind t k ih =>
    simp only [bind_assoc]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
        Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
        Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    exact lintegral_mono ih

theorem corr_step_h_paper (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] (sameHdr : C → C → Bool) (cfg : Config Msg)
    (P : Party) (s : GameState St Msg C) (hwin : s.win = false) :
    (fullImplBaseDFPaper sm Δ qep sameHdr cfg (.inr (.inl (.inr P)))).run s =
      if !(s.corrAllowedPaper P) then pure (none, s)
      else pure (some (s.st P), s.afterCorr P) := by
  change (DeliverForge.corrImplPaper P).run s = _
  unfold DeliverForge.corrImplPaper
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_or]
  split <;> simp [StateT.run_set]

private theorem card_targetsL_le_df_paper {Δ n t : ℕ} (hΔ : 0 < Δ) (ht : t < n) :
    (admissibleLastLeakGuesses Δ t).card ≤ n := by
  unfold admissibleLastLeakGuesses
  refine (Finset.card_insert_le _ _).trans ?_
  have h := Finset.card_image_le (s := Finset.range (t + 1 - Δ)) (f := (some : ℕ → Option ℕ))
  simp only [Finset.card_range] at h
  omega

end GamesDFPaper

end CryptoGames.SM.Construction.DeliverForge
