/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.DeliverForgeShifted
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperDefs
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS
import ProofLib.SepLogic.WP.StateNorm
/-!
# Shifted-Paper Definitions and Hop 3

Defines `trivB1`, the shifted-paper base games, engines, and reductions, and proves
`lemma11_df_shifted_paper`.
-/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory OracleComp OracleSpec
namespace CryptoGames.SM.Construction.DeliverForge
open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Construction
open CryptoGames.LibsignalSM.Proofs.Refinement
/-- `Dir2` (`B1(tStar)`) triviality predicate. -/
def trivB1 {St Msg C : Type} (tStar : ℕ) (s : SM.GameState St Msg C) (pos : SM.Pos) : Bool :=
  s.trivial 2 pos ||
    (pos.epoch != tStar && decide (pos.epoch < min (s.epoch .A) (s.epoch .B)))
@[simp] theorem trivB1_self_epoch {St Msg C : Type} (tStar : ℕ)
    (s : SM.GameState St Msg C) (pos : SM.Pos) (h : pos.epoch = tStar) :
    trivB1 tStar s pos = s.trivial 2 pos := by simp [trivB1, h]
theorem trivB1_of_not_lt_min {St Msg C : Type} (tStar : ℕ)
    (s : SM.GameState St Msg C) (pos : SM.Pos) (h : ¬ pos.epoch < min (s.epoch .A) (s.epoch .B)) :
    trivB1 tStar s pos = s.trivial 2 pos := by simp [trivB1, h]
theorem trivB1_eq_trivial_of_new_epoch {St Msg C : Type} (tStar : ℕ)
    (s : SM.GameState St Msg C) (P : Party) (pos : SM.Pos) (h : pos.epoch = s.epoch P + 1) :
    trivB1 tStar s pos = s.trivial 2 pos := by
  apply trivB1_of_not_lt_min
  have : min (s.epoch .A) (s.epoch .B) ≤ s.epoch P := by cases P <;> simp
  omega
theorem trivB1_of_trivial {St Msg C : Type} {tStar : ℕ}
    {s : SM.GameState St Msg C} {pos : SM.Pos} (h : s.trivial 2 pos = true) :
    trivB1 tStar s pos = true := by simp [trivB1, h]
def injectImplB1 {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep tStar : ℕ) (cfg : SM.Config Msg) :
    QueryImpl ((Party × C) →ₒ Option (SM.RecvResult Msg))
      (StateT (SM.GameState St Msg C) ProbComp) := fun ⟨P, c⟩ => do
  let s ← get
  if s.win || (s.inTransit P.other c).isSome || !(s.safeInj 2) then return none
  match sm.receive (s.st P) c with
  | none => return some .rejected
  | some (st', t', i', m') =>
    if qep + 1 < t' then return some .rejected
    let pos : SM.Pos := ⟨P.other, t', i'⟩
    if trivB1 tStar s pos then
      set (s.accept P st' pos); return some (.accepted t' i' (some m'))
    else
      if cfg.injectFull t' then set { s with win := true }
      return some .rejected
def deliverForgeBaseImplB1 {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep tStar : ℕ) (sameHdr : C → C → Bool)
    (cfg : SM.Config Msg) :
    QueryImpl ((Party × C × C) →ₒ Option (SM.RecvResult Msg))
      (StateT (SM.GameState St Msg C) ProbComp) := fun ⟨P, c, c'⟩ => do
  let s ← get
  if s.win then return none
  match s.inTransit P.other c with
  | none => return none
  | some r =>
    if (s.inTransit P.other c').isSome || s.comp.contains r.pos || !(sameHdr c c') then return none
    match sm.receive (s.st P) c' with
    | none => return some .rejected
    | some (st', t', i', m') =>
      if qep + 1 < t' || t' != r.pos.epoch then return some .rejected
      let pos : SM.Pos := ⟨P.other, t', i'⟩
      if trivB1 tStar s pos then
        set (s.accept P st' pos); return some (.accepted t' i' (some m'))
      else
        if cfg.injectFull t' then set { s with win := true }
        return some .rejected
def corrImplShiftedPaper {St Msg C : Type} (l : ℕ) :
    QueryImpl (Party →ₒ Option St) (StateT (SM.GameState St Msg C) ProbComp) := fun P => do
  let s ← get
  if s.win || !(s.corrAllowedPaper P) then return none
  set (DeliverForge.afterCorrShifted l s P)
  return some (s.st P)
def oracleImplShiftedPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Coins] (sm : SMScheme Key St Msg Coins C) (Δ l qep : ℕ) (cfg : SM.Config Msg) :
    QueryImpl (SM.spec St Msg Coins C) (StateT (SM.GameState St Msg C) ProbComp) :=
  SM.transmitImpl sm Δ qep + SM.challImpl sm Δ qep cfg + SM.deliverImpl sm cfg +
    SM.injectImpl sm Δ qep cfg + corrImplShiftedPaper (St := St) (Msg := Msg) (C := C) l
def oracleImplShiftedDir2Paper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Coins] (sm : SMScheme Key St Msg Coins C) (l qep tStar : ℕ)
    (cfg : SM.Config Msg) :
    QueryImpl (SM.spec St Msg Coins C) (StateT (SM.GameState St Msg C) ProbComp) :=
  SM.transmitImpl sm 2 qep + SM.challImpl sm 2 qep cfg + SM.deliverImpl sm cfg +
    injectImplB1 sm qep tStar cfg + corrImplShiftedPaper (St := St) (Msg := Msg) (C := C) l
def oracleImplBaseDFShiftedPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Coins] (sm : SMScheme Key St Msg Coins C) (Δ l qep : ℕ)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    QueryImpl (DeliverForge.specDF St Msg Coins C) (StateT (SM.GameState St Msg C) ProbComp) :=
  oracleImplShiftedPaper sm Δ l qep cfg + DeliverForge.deliverForgeBaseImpl sm Δ qep sameHdr cfg
def oracleImplBaseDFShiftedDir2Paper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Coins] (sm : SMScheme Key St Msg Coins C) (l qep tStar : ℕ)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    QueryImpl (DeliverForge.specDF St Msg Coins C) (StateT (SM.GameState St Msg C) ProbComp) :=
  oracleImplShiftedDir2Paper sm l qep tStar cfg + deliverForgeBaseImplB1 sm qep tStar sameHdr cfg
abbrev fullImplBaseDFShiftedPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Coins] (sm : SMScheme Key St Msg Coins C) (Δ l qep : ℕ)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    QueryImpl (unifSpec + DeliverForge.specDF St Msg Coins C)
      (StateT (SM.GameState St Msg C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (SM.GameState St Msg C) ProbComp) +
    oracleImplBaseDFShiftedPaper sm Δ l qep sameHdr cfg
abbrev fullImplBaseDFShiftedDir2Paper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Coins] (sm : SMScheme Key St Msg Coins C) (l qep tStar : ℕ)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    QueryImpl (unifSpec + DeliverForge.specDF St Msg Coins C)
      (StateT (SM.GameState St Msg C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (SM.GameState St Msg C) ProbComp) +
    oracleImplBaseDFShiftedDir2Paper sm l qep tStar sameHdr cfg
def runBaseDFShiftedPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ l qep : ℕ)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) (b : Bool)
    (B : DeliverForge.AdversaryDF St Msg Coins C) : ProbComp (Bool × SM.GameState St Msg C) := do
  let k ← $ᵗ Key
  (simulateQ (fullImplBaseDFShiftedPaper sm Δ l qep sameHdr cfg) B).run (SM.initState sm k b)
def runBaseDFShiftedDir2Paper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (l qep tStar : ℕ)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) (b : Bool)
    (B : DeliverForge.AdversaryDF St Msg Coins C) : ProbComp (Bool × SM.GameState St Msg C) := do
  let k ← $ᵗ Key
  (simulateQ (fullImplBaseDFShiftedDir2Paper sm l qep tStar sameHdr cfg) B).run
    (SM.initState sm k b)
/-- `Δ = 2` shifted paper game at `l = tStar - 1`. -/
def forgeGameGuessedShiftedDir2Paper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (l tStar : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) : ProbComp Bool := do
  let (_, s') ← runBaseDFShiftedDir2Paper sm l qep tStar sameHdr (SM.Config.auth tStar) false B
  return s'.win && authOKDir2 (some (l - 1)) tStar s'
noncomputable def forgeGuessedAdvantageShiftedDir2Paper {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (l tStar : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) : ℝ≥0∞ :=
  𝒟[forgeGameGuessedShiftedDir2Paper sm qep sameHdr l tStar B] {true}
/-- `Δ`-parametric shifted paper game at `l = tStar - 2`. -/
def forgeGameGuessedShiftedPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (sameHdr : C → C → Bool)
    (l tStar : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) : ProbComp Bool := do
  let (_, s') ← runBaseDFShiftedPaper sm Δ l qep sameHdr (SM.Config.auth tStar) false B
  return s'.win && SM.authLosingConditionsAvoided Δ (some (l - 1)) tStar s'
noncomputable def forgeGuessedAdvantageShiftedPaper {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (sameHdr : C → C → Bool)
    (l tStar : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) : ℝ≥0∞ :=
  𝒟[forgeGameGuessedShiftedPaper sm Δ qep sameHdr l tStar B] {true}
variable {ι : Type} {tspec : OracleSpec.{0, 0} ι}
  {HS KC Γ CCoins T I KR Sig K SS RS M E Γv Sv SSv RSv : Type}
def injectEB1 [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (qep tStar : ℕ) (cfg : SM.Config M) :
    QueryImpl ((Party × (Header T × E)) →ₒ Option (SM.RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) := fun ⟨P, c⟩ => do
  let es ← get; let s := es.g
  if es.abort || s.win || (s.inTransit P.other c).isSome || !(s.safeInj 2) then return none
  match ← liftH (vRecv hk s P (s.st P) c none) with
  | none => abortE; return none
  | some none => return some .rejected
  | some (some (st', t', i', m')) =>
    if qep + 1 < t' then return some .rejected
    let pos : SM.Pos := ⟨P.other, t', i'⟩
    if trivB1 tStar s pos then
      match ← commitE hk s P (s.st P) st' pos with
      | none => return none
      | some s₁ => modify fun es => { es with g := s₁ }; return some (.accepted t' i' (some m'))
    else
      if cfg.injectFull t' then modify fun es => { es with g := { es.g with win := true } }
      return some .rejected
def deliverForgeEB1 [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (qep tStar : ℕ) (cfg : SM.Config M) :
    QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (SM.RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) := fun ⟨P, c, c'⟩ => do
  let es ← get; let s := es.g
  if es.abort || s.win then return none
  match s.inTransit P.other c with
  | none => return none
  | some r =>
    if (s.inTransit P.other c').isSome || s.comp.contains r.pos || c.1 != c'.1 then return none
    match ← liftH (vRecv hk s P (s.st P) c' none) with
    | none => abortE; return none
    | some none => return some .rejected
    | some (some (st', t', i', m')) =>
      if qep + 1 < t' || t' != r.pos.epoch then return some .rejected
      let pos : SM.Pos := ⟨P.other, t', i'⟩
      if trivB1 tStar s pos then
        match ← commitE hk s P (s.st P) st' pos with
        | none => return none
        | some s₁ => modify fun es => { es with g := s₁ }; return some (.accepted t' i' (some m'))
      else
        if cfg.injectFull t' then modify fun es => { es with g := { es.g with win := true } }
        return some .rejected
def corrEShiftedPaper (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (π : Policy) :
    QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS))
      (EM tspec Γv T Sv SSv RSv M E HS) := fun P => do
  let es ← get
  if es.abort || es.g.win || !(es.g.corrAllowedPaper P) then return none
  let s₁ := DeliverForge.afterCorrShifted l es.g P
  if π.leakDoom es.g s₁ || π.corrDoom es.g P then abortE; return none
  else
    let stOpt ← liftH (hk.reveal es.g P (es.g.st P))
    match stOpt with
    | none => abortE; return none
    | some st => modify fun es => { es with g := s₁ }; return some st
def implEDFShiftedPaper [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : SM.Config M) (π : Policy) :
    QueryImpl (unifSpec + DeliverForge.specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  let i₀ : QueryImpl unifSpec (EM tspec Γv T Sv SSv RSv M E HS) := coinsE
  let i₁ : QueryImpl (SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
    HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (transmitE hk Δ qep π) (challE hk Δ qep cfg π))
      (deliverE hk maxSkip cfg)) (injectE hk Δ qep cfg)) (corrEShiftedPaper l hk π)
  let i₂ : QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (SM.RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) := DeliverForge.deliverForgeE hk Δ qep cfg
  HAdd.hAdd i₀ (HAdd.hAdd i₁ i₂)
def implEDFShiftedDir2Paper [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (qep maxSkip tStar : ℕ) (cfg : SM.Config M) (π : Policy) :
    QueryImpl (unifSpec + DeliverForge.specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  let i₀ : QueryImpl unifSpec (EM tspec Γv T Sv SSv RSv M E HS) := coinsE
  let i₁ : QueryImpl (SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
    HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (transmitE hk 2 qep π) (challE hk 2 qep cfg π))
      (deliverE hk maxSkip cfg)) (injectEB1 hk qep tStar cfg)) (corrEShiftedPaper l hk π)
  let i₂ : QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (SM.RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) := deliverForgeEB1 hk qep tStar cfg
  HAdd.hAdd i₀ (HAdd.hAdd i₁ i₂)
def engRunDFShiftedPaper [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : SM.Config M) (π : Policy)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS) (b : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    TComp tspec (Option (Bool × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)) := do
  let (vpOpt, h₁) ← init.run h₀
  match vpOpt with
  | none => return none
  | some (vpA, vpB) =>
    let g₀ : SM.GameState (VP Γv T Sv SSv RSv) M (Header T × E) :=
      { st := fun | .A => vpA | .B => vpB, b := b }
    let es₀ : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS :=
      { g := g₀, h := h₁, abort := false }
    let res ← (simulateQ (implEDFShiftedPaper l hk Δ qep maxSkip cfg π) A).run es₀
    return some res
def engRunDFShiftedDir2Paper [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (qep maxSkip tStar : ℕ) (cfg : SM.Config M) (π : Policy)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS) (b : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    TComp tspec (Option (Bool × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)) := do
  let (vpOpt, h₁) ← init.run h₀
  match vpOpt with
  | none => return none
  | some (vpA, vpB) =>
    let g₀ : SM.GameState (VP Γv T Sv SSv RSv) M (Header T × E) :=
      { st := fun | .A => vpA | .B => vpB, b := b }
    let es₀ : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS :=
      { g := g₀, h := h₁, abort := false }
    let res ← (simulateQ (implEDFShiftedDir2Paper l hk qep maxSkip tStar cfg π) A).run es₀
    return some res
def authSimDFShiftedPaper [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (l : ℕ) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (tL : Option ℕ) (tStar : ℕ) (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    TComp tspec Bool := do
  let π : Policy := ⟨true, tL, tStar⟩
  let r ← engRunDFShiftedPaper l hk (2 + Δcka) qep fs.maxSkip (SM.Config.auth tStar) π
    init h₀ false A
  match r with
  | none => return false
  | some (_, es) => return authOut (2 + Δcka) π es
def authSimDFShiftedDir2Paper [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (l : ℕ) (fs : FSAEADScheme K SS RS (Header T) M E) (qep : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (tL : Option ℕ) (tStar : ℕ) (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    TComp tspec Bool := do
  let π : Policy := ⟨true, tL, tStar⟩
  let r ← engRunDFShiftedDir2Paper l hk qep fs.maxSkip tStar (SM.Config.auth tStar) π
    init h₀ false A
  match r with
  | none => return false
  | some (_, es) => return authOut 2 π es
def redCKAAuthDFShiftedPaper [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l tStar : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    CKA.Adversary Γ CCoins T I :=
  show CKA.AdversaryComp Γ CCoins T I Bool from
  authSimDFShiftedPaper l fs Δcka qep
    (DeliverForge.hooksCKAShifted cka prng fs l tStar)
    (DeliverForge.initCKAShifted cka prng fs lam l) {} (some (l - 1)) tStar A
def redCKAAuthDFShiftedDir2Paper [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l tStar : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    CKA.Adversary Γ CCoins T I :=
  show CKA.AdversaryComp Γ CCoins T I Bool from
  authSimDFShiftedDir2Paper l fs qep
    (DeliverForge.hooksCKAShifted cka prng fs l 0)
    (DeliverForge.initCKAShifted cka prng fs lam l) {} (some (l - 1)) tStar A
def redPRNGAuthDFShiftedPaper [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l tStar : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from
  authSimDFShiftedPaper l fs Δcka qep
    (hooksPRNG cka prng fs ⟨true, some (l - 1), tStar⟩)
    (initPRNG cka prng fs lam ⟨true, some (l - 1), tStar⟩) {} (some (l - 1)) tStar A
def redPRNGAuthDFShiftedDir2Paper [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l tStar : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from
  authSimDFShiftedDir2Paper l fs qep
    (hooksPRNG cka prng fs ⟨false, some (l - 1), tStar⟩)
    (initPRNG cka prng fs lam ⟨false, some (l - 1), tStar⟩) {} (some (l - 1)) tStar A
def redFSAuthDFShiftedPaper [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j l tStar : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    FSAEAD.Adversary SS RS (Header T) M E :=
  show FSAEAD.AdversaryComp SS RS (Header T) M E Bool from do
  let _ ← engRunDFShiftedPaper l (hooksFS cka prng fs Δcka ⟨true, some (l - 1), tStar⟩ j)
    (2 + Δcka) qep fs.maxSkip (SM.Config.auth tStar) ⟨true, some (l - 1), tStar⟩
    (initFS cka prng fs lam ⟨true, some (l - 1), tStar⟩ j) {} false A
  sampleT Bool
def redFSAuthDFShiftedDir2Paper [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep j l tStar : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    FSAEAD.Adversary SS RS (Header T) M E :=
  show FSAEAD.AdversaryComp SS RS (Header T) M E Bool from do
  let _ ← engRunDFShiftedDir2Paper l (hooksFS cka prng fs 0 ⟨false, some (l - 1), tStar⟩ j)
    qep fs.maxSkip tStar (SM.Config.auth tStar) ⟨true, some (l - 1), tStar⟩
    (initFS cka prng fs lam ⟨false, some (l - 1), tStar⟩ j) {} false A
  sampleT Bool
/-! ## Shifted-paper Lemma 11 -/
section AuthL11ShiftedPaper
open AuthL11
variable [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]
omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
theorem implEDFShiftedPaper_eq_implEDF_of_ne_corr {tspec : OracleSpec.{0, 0} ι}
    {Γv Sv SSv RSv HS : Type}
    (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (hq : ∀ P, q ≠ .inr (.inl (.inr P))) :
    implEDFShiftedPaper l hk Δ qep maxSkip cfg π q = implEDF hk Δ qep maxSkip cfg π q := by
  rcases q with n | (((((q1 | q2) | q3) | q4) | P) | df)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (hq P rfl)
  · rfl
def stepPDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateP Γ T Sig SS RS M E K) ×
      PRFPRNG.GameState Sig I K) :=
  (simulateQ (pImpl prng)
    ((implEDFShiftedPaper l (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip
      mo.cfg mo.policy q).run esP)).run sp
def stepLDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    ProbComp ((SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I) :=
  simulateQ lImpl
    ((implEDFShiftedPaper l (hooksLocal cka prng fs mo) (2 + Δcka) qep fs.maxSkip
      mo.cfg mo.policy q).run esL)
def runPDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (pImpl prng)
    ((simulateQ (implEDFShiftedPaper l (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip
      mo.cfg mo.policy) oa).run esP)).run sp
  pure (authOut (2 + Δcka) mo.policy r.1.2)
def runLocDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implEDFShiftedPaper l (hooksLocal cka prng fs mo) (2 + Δcka) qep fs.maxSkip
      mo.cfg mo.policy) oa).run esL)
  pure (authOut (2 + Δcka) mo.policy r.2)
def runLocAtDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implEDFShiftedPaper l (hooksLocal cka prng fs mo) (2 + Δcka) qep fs.maxSkip
      mo.cfg mo.policy) oa).run esL)
  pure (authOut (2 + Δcka) mo.policy r.2 && (r.2.h.lastIdx == some j))
def localAuthDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocal cka prng fs lam mo).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocDFShiftedPaper cka prng fs Δcka qep l mo A { g, h }
def localAuthAtDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j l : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocal cka prng fs lam mo).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocAtDFShiftedPaper cka prng fs Δcka qep l mo j A { g, h }
def stepLFixedDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    ProbComp ((SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I) :=
  simulateQ lImpl
    ((implEDFShiftedPaper l (hooksLocalFixed cka prng fs mo j k_fs)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run esL)
def runLocAtFixedDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implEDFShiftedPaper l (hooksLocalFixed cka prng fs mo j k_fs)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esL)
  pure (authOut (2 + Δcka) mo.policy r.2 && (r.2.h.lastIdx == some j))
def localAuthAtFixedDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j l : ℕ) (k_fs : K)
    (tL : Option ℕ) (t : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocalFixed cka prng fs lam mo j k_fs).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocAtFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs A { g, h }
def stepFDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      EStateF Γ T Sig SS RS M E K I) × FSGameState SS RS T M E) :=
  (simulateQ (implFS fs)
    ((implEDFShiftedPaper l (hooksFS cka prng fs Δcka mo j)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run esF)).run st
def runFDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) : ProbComp Bool := do
  let r ← (simulateQ (implFS fs)
    ((simulateQ (implEDFShiftedPaper l (hooksFS cka prng fs Δcka mo j)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esF)).run st
  pure r.2.win
omit [SampleableType KR] [SampleableType KC] in
theorem runPDFShiftedPaper_pure (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (b' : Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    runPDFShiftedPaper cka prng fs Δcka qep l mo (pure b') esP sp =
      pure (authOut (2 + Δcka) mo.policy esP) := by simp [runPDFShiftedPaper, map_eq_bind_pure_comp]
omit [SampleableType KR] [SampleableType KC] in
theorem runLocDFShiftedPaper_pure (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (b' : Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocDFShiftedPaper cka prng fs Δcka qep l mo (pure b') esL =
      pure (authOut (2 + Δcka) mo.policy esL) := by
  simp [runLocDFShiftedPaper, map_eq_bind_pure_comp]
omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtDFShiftedPaper_pure (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (b' : Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtDFShiftedPaper cka prng fs Δcka qep l mo j (pure b') esL =
      pure (authOut (2 + Δcka) mo.policy esL && (esL.h.lastIdx == some j)) := by
  simp [runLocAtDFShiftedPaper, map_eq_bind_pure_comp]
omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtFixedDFShiftedPaper_pure (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (b' : Bool) (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs (pure b') esL =
      pure (authOut (2 + Δcka) mo.policy esL && (esL.h.lastIdx == some j)) := by
  simp [runLocAtFixedDFShiftedPaper, map_eq_bind_pure_comp]
omit [SampleableType KR] [SampleableType KC] in
theorem runPDFShiftedPaper_query_bind (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    runPDFShiftedPaper cka prng fs Δcka qep l mo (liftM (OracleSpec.query q) >>= k) esP sp =
      stepPDFShiftedPaper cka prng fs Δcka qep l mo q esP sp >>= fun r =>
        runPDFShiftedPaper cka prng fs Δcka qep l mo (k r.1.1) r.1.2 r.2 := by
  simp [runPDFShiftedPaper, stepPDFShiftedPaper, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]
omit [SampleableType KR] [SampleableType KC] in
theorem runLocDFShiftedPaper_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocDFShiftedPaper cka prng fs Δcka qep l mo (liftM (OracleSpec.query q) >>= k) esL =
      stepLDFShiftedPaper cka prng fs Δcka qep l mo q esL >>= fun r =>
        runLocDFShiftedPaper cka prng fs Δcka qep l mo (k r.1) r.2 := by
  simp [runLocDFShiftedPaper, stepLDFShiftedPaper, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]
omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtDFShiftedPaper_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (j : ℕ) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtDFShiftedPaper cka prng fs Δcka qep l mo j (liftM (OracleSpec.query q) >>= k) esL =
      stepLDFShiftedPaper cka prng fs Δcka qep l mo q esL >>= fun r =>
        runLocAtDFShiftedPaper cka prng fs Δcka qep l mo j (k r.1) r.2 := by
  simp [runLocAtDFShiftedPaper, stepLDFShiftedPaper, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]
omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtFixedDFShiftedPaper_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (j : ℕ) (k_fs : K) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs
        (liftM (OracleSpec.query q) >>= k) esL =
      stepLFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs q esL >>= fun r =>
        runLocAtFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs (k r.1) r.2 := by
  simp [runLocAtFixedDFShiftedPaper, stepLFixedDFShiftedPaper, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]
omit [SampleableType KR] [SampleableType KC] in
theorem runFDFShiftedPaper_query_bind (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) :
    runFDFShiftedPaper cka prng fs Δcka qep l mo j (liftM (OracleSpec.query q) >>= k) esF st =
      stepFDFShiftedPaper cka prng fs Δcka qep l mo j q esF st >>= fun r =>
        runFDFShiftedPaper cka prng fs Δcka qep l mo j (k r.1.1) r.1.2 r.2 := by
  simp [runFDFShiftedPaper, stepFDFShiftedPaper, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]
theorem stepPDFShiftedPaper_abort (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) (hab : esP.abort = true) :
    ∀ r ∈ support (stepPDFShiftedPaper cka prng fs Δcka qep l mo q esP sp), r.1.2.abort = true := by
  intro r hr
  by_cases hcorr : ∃ P, q = .inr (.inl (.inr P))
  · rcases hcorr with ⟨P, rfl⟩
    simp only [stepPDFShiftedPaper, implEDFShiftedPaper, QueryImpl.add_apply, corrEShiftedPaper,
      StateT.run_bind, StateT.run_get, pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · have hne : ∀ P, q ≠ .inr (.inl (.inr P)) := fun P h => hcorr ⟨P, h⟩
    rw [stepPDFShiftedPaper, implEDFShiftedPaper_eq_implEDF_of_ne_corr _ _ _ _ _ _ _ _ hne] at hr
    exact stepPDF_abort cka prng fs Δcka qep mo q esP sp hab r hr
theorem runPDFShiftedPaper_abort (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K} (hab : esP.abort = true) :
    𝒟[runPDFShiftedPaper cka prng fs Δcka qep l mo oa esP sp] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing esP sp with
  | pure b' => rw [runPDFShiftedPaper_pure]; simp [authOut, hab]
  | query_bind q k ih =>
    rw [runPDFShiftedPaper_query_bind]
    exact evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepPDFShiftedPaper_abort cka prng fs Δcka qep l mo q esP sp hab r hr)
theorem runPDFShiftedPaper_abort_le (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K} (hab : esP.abort = true)
    (rhs : ℝ≥0∞) :
    𝒟[runPDFShiftedPaper cka prng fs Δcka qep l mo oa esP sp] {true} ≤ rhs := by
  rw [runPDFShiftedPaper_abort cka prng fs Δcka qep l mo oa hab]; exact zero_le
omit [Inhabited E] [SampleableType KR] [SampleableType KC] in
theorem leComp_corrEShiftedPaper_PRNG_local (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka l : ℕ) (mo : Mode)
    (P : Party)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      ((simulateQ (pImpl prng)
        ((corrEShiftedPaper l (hooksPRNG cka prng fs mo) mo.policy P).run esP)).run sp)
      (simulateQ lImpl
        ((corrEShiftedPaper l (hooksLocal cka prng fs mo) mo.policy P).run esL)) := by
  unfold corrEShiftedPaper
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abort_eq, eraseSt_win hsync.g_eq, eraseSt_corrAllowedPaper hsync.g_eq]
  by_cases hguard : (esL.abort || esL.g.win || !esL.g.corrAllowedPaper P) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    have hac_er := eraseSt_afterCorrShifted hsync.g_eq l P
    rw [eraseSt_leakDoom hsync.g_eq hac_er mo.policy, eraseSt_corrDoom hsync.g_eq mo.policy P]
    by_cases hdoom : (mo.policy.leakDoom esL.g (afterCorrShifted l esL.g P) ||
        mo.policy.corrDoom esL.g P) = true
    · simp only [hdoom, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
        StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inl rfl)
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, run_liftH, hooksPRNG, hooksLocal]
      have hvp := hsync.vp_rel P
      rcases hrootP : (esP.g.st P).root with _ | σ
      · simp only [StateT.run_pure, pure_bind, abortE, StateT.run_bind, StateT.run_modify,
          simulateQ_pure]
        exact LeComp.pure (Or.inl rfl)
      · have hσ_eq : σ = (esL.g.st P).root := hvp.root_eq σ hrootP
        subst hσ_eq
        simp only [StateT.run_pure, pure_bind]
        refine LeComp.pure (Or.inr ⟨?_, ?_⟩)
        · dsimp only [realParty]
          rw [hvp.id_P, hvp.id_L, hvp.γ_eq, hvp.Tcur_eq, hvp.tcur_P, hvp.tcur_L, hvp.vS_eq]
          congr 3; funext t'; exact hvp.vR_eq t'
        · refine ⟨hsync.abort_eq, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.sp_b,
            hsync.table_eq, hsync.corr_tH,
            comp_inv_afterCorrShifted esL.g l (2 + Δcka) (by omega) P
              (fun r hr => (hsync.trans_epoch r hr).1) hsync.comp_inv,
            hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends, hsync.root_max,
            hsync.root_pred, hsync.cache_max⟩
theorem leComp_stepPDFShiftedPaper_stepLDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (hauth : mo.auth = true)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I} (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      (stepPDFShiftedPaper cka prng fs Δcka qep l mo q esP sp)
      (stepLDFShiftedPaper cka prng fs Δcka qep l mo q esL) := by
  by_cases hcorr : ∃ P, q = .inr (.inl (.inr P))
  · rcases hcorr with ⟨P, rfl⟩
    exact leComp_corrEShiftedPaper_PRNG_local cka prng fs Δcka l mo P hsync
  · have hne : ∀ P, q ≠ .inr (.inl (.inr P)) := fun P h => hcorr ⟨P, h⟩
    rw [stepPDFShiftedPaper, stepLDFShiftedPaper,
      implEDFShiftedPaper_eq_implEDF_of_ne_corr _ _ _ _ _ _ _ _ hne,
      implEDFShiftedPaper_eq_implEDF_of_ne_corr _ _ _ _ _ _ _ _ hne]
    exact leComp_stepPDF_stepLDF cka prng fs Δcka qep mo hauth q hsync
theorem runPDFShiftedPaper_le_runLocDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (hauth : mo.auth = true) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I} (hsync : SyncPL Δcka mo esP sp esL) :
    𝒟[runPDFShiftedPaper cka prng fs Δcka qep l mo oa esP sp] {true} ≤
      𝒟[runLocDFShiftedPaper cka prng fs Δcka qep l mo oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing esP sp esL with
  | pure b' =>
    rw [runPDFShiftedPaper_pure, runLocDFShiftedPaper_pure]
    have hout : authOut (2 + Δcka) mo.policy esP = authOut (2 + Δcka) mo.policy esL := by
      unfold authOut
      rw [hsync.abort_eq, eraseSt_win hsync.g_eq,
        eraseSt_authOK hsync.g_eq (2 + Δcka) mo.policy.tL mo.policy.tStar]
    rw [hout]
  | query_bind q k ih =>
    rw [runPDFShiftedPaper_query_bind, runLocDFShiftedPaper_query_bind]
    refine leComp_stepPDFShiftedPaper_stepLDFShiftedPaper cka prng fs Δcka qep l mo hauth q hsync
      _ _ ?_
    rintro ⟨⟨uP, esP'⟩, sp'⟩ ⟨uL, esL'⟩ (hab | ⟨rfl, hsync'⟩)
    · exact runPDFShiftedPaper_abort_le cka prng fs Δcka qep l mo (k uP) hab _
    · exact ih uP hsync'
omit [SampleableType KR] [SampleableType KC] in
theorem evalDist_runPDFShiftedPaper_eq (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (tL : Option ℕ) (t : ℕ)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    𝒟[do
      let x ← (simulateQ (pImpl prng)
        ((simulateQ (implEDFShiftedPaper l (hooksPRNG cka prng fs ⟨true, tL, t⟩)
          (2 + Δcka) qep fs.maxSkip (Config.auth t) ⟨true, tL, t⟩) oa).run esP)).run sp
      pure (authOut (2 + Δcka) ⟨true, tL, t⟩ x.1.2)] =
    𝒟[runPDFShiftedPaper cka prng fs Δcka qep l ⟨true, tL, t⟩ oa esP sp] := by
  simp [runPDFShiftedPaper, Mode.cfg, Mode.policy, map_eq_bind_pure_comp]
theorem branch_redPRNGAuthDFShiftedPaper_le_localAuthDFShiftedPaper
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep l t : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true (redPRNGAuthDFShiftedPaper cka prng fs lam Δcka qep l t A)] {true} ≤
      𝒟[localAuthDFShiftedPaper cka prng fs lam Δcka qep l (some (l - 1)) t A] {true} := by
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = pImpl prng := rfl
  let tL : Option ℕ := some (l - 1)
  unfold PRFPRNG.branch redPRNGAuthDFShiftedPaper authSimDFShiftedPaper engRunDFShiftedPaper
    localAuthDFShiftedPaper initPRNG initLocal
  simp only [hpImpl, StateT.run'_eq, map_eq_bind_pure_comp, StateT.run_bind, simulateQ_bind,
    bind_assoc, simulateQ_pImpl_run_lift_sampleT, simulateQ_lImpl_run_lift_sampleT, pure_bind]
  refine evalDist_bind_mono ($ᵗ KR) _ _ fun kr _ => evalDist_bind_mono ($ᵗ KC) _ _ fun kc _ => ?_
  have hroot0 := leComp_rootPRNG_rootL prng ⟨true, tL, t⟩
    (t := 0) (Ik := lam) (σv := none) (σ := prng.init kr)
    (hP := ({} : PRNGState T Sig K)) (sp := { σ := prng.init kr, b := true })
    (hL := ({} : LState T Sig K I))
    rfl rfl (fun h1 _ => Or.inr (by simp [tL, Mode.tH, healEpoch] at h1 ⊢)) (by omega)
    (fun _ => rfl)
  refine hroot0 _ _ ?_
  rintro ⟨⟨res0, hP0⟩, sp0⟩ ⟨⟨σL, kL, sid0⟩, hL0⟩ hrel0
  rcases hrel0 with hnone | ⟨σP, hres_eq, hhP0, hb0, htab0, hcorr0', hc0, _, hσ_rel, hlt0, _⟩
  · dsimp only at hnone; subst hnone; simp
  · dsimp only at hres_eq hhP0; subst hres_eq hhP0
    have hreg_det : ∃ (idx? : Option ℕ) (hL1 : LState T Sig K I),
        simulateQ lImpl ((regSessOf (T := T) (Sig := Sig) (K := K) sid0).run hL0) =
          pure (idx?, hL1) ∧ hL1.table = hL0.table ∧ hL1.cache = hL0.cache := by
      cases sid0 with
      | none => exact ⟨none, hL0, rfl, rfl, rfl⟩
      | some Ik =>
        unfold regSessOf regSess
        simp only [StateT.run_map, StateT.run_bind, StateT.run_get, pure_bind]
        split
        · exact ⟨some (hL0.sessions.idxOf Ik), hL0, rfl, rfl, rfl⟩
        · exact ⟨some hL0.sessions.length, { hL0 with sessions := hL0.sessions ++ [Ik] },
            rfl, rfl, rfl⟩
    obtain ⟨idx?, hL1, hreg_eq, htab1, hc1⟩ := hreg_det
    simp only [StateT.run_pure, simulateQ_pure, StateT.run_bind, simulateQ_bind, hreg_eq,
      pure_bind, bind_assoc, Function.comp_apply]
    rw [evalDist_runPDFShiftedPaper_eq]
    refine runPDFShiftedPaper_le_runLocDFShiftedPaper cka prng fs Δcka qep l ⟨true, tL, t⟩ rfl A ?_
    refine ⟨rfl, rfl, ?_, ?_, hb0, htab0.trans htab1.symm, hcorr0', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro P; cases P
      · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun t' => ?_, hσ_rel⟩
        dsimp only [mkParties]; split <;> rfl
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, hσ_rel⟩
    · intro t'; rw [hc1, hc0]; exact Or.inl ⟨rfl, rfl⟩
    · intro _ h; cases h
    · intro _ h; cases h
    · intro P; simp
    · intro P h; simp at h
    · intro P _ h; cases P <;> exact (hlt0 h).symm
    · intro h P _ _; cases P <;> exact (hlt0 h).symm
    · intro Tc σc k idx' hc_eq _; rw [hc1, hc0] at hc_eq; cases hc_eq
theorem stepLDFShiftedPaper_sessInv (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (hauth : mo.auth = true) {q rem : ℕ}
    (q_sm : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) (hS : SessInv mo q rem esL) :
    (∀ t, q_sm = .inl t →
      ∀ r ∈ support (stepLDFShiftedPaper cka prng fs Δcka qep l mo (.inl t) esL),
        SessInv mo q rem r.2) ∧
    (∀ q_inr, q_sm = .inr q_inr → 0 < rem →
      ∀ r ∈ support (stepLDFShiftedPaper cka prng fs Δcka qep l mo (.inr q_inr) esL),
        SessInv mo q (rem - 1) r.2) := by
  constructor
  · intro t ht r hr
    have hne : ∀ P, (.inl t : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain) ≠
        .inr (.inl (.inr P)) := fun _ h => by cases h
    rw [stepLDFShiftedPaper, implEDFShiftedPaper_eq_implEDF_of_ne_corr _ _ _ _ _ _ _ _ hne] at hr
    exact (stepLDF_sessInv cka prng fs Δcka qep mo hauth (.inl t) esL hS).1 t rfl r hr
  · intro q_inr hq_sm hrem r hr
    by_cases hcorr : ∃ P, (.inr q_inr : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain) =
        .inr (.inl (.inr P))
    · rcases hcorr with ⟨P, hP⟩; injection hP with hP; subst hP
      have hrem_mono :
          (esL.g.win = true ∧ ∃ j, j < q ∧ esL.h.lastIdx = some j) ∨
          (esL.g.win = false ∧
            ((mo.tStar = 0 ∧ esL.h.sessions.length ≤ 1 ∧ rem - 1 ≤ q) ∨
             (0 < mo.tStar ∧ esL.h.sessions.length + (rem - 1) ≤ q))) := by
        rcases hS.bound with hwin | ⟨hnw, ⟨ht0, hle1, _⟩ | hpos⟩
        · exact Or.inl hwin
        · exact Or.inr ⟨hnw, Or.inl ⟨ht0, hle1, by omega⟩⟩
        · exact Or.inr ⟨hnw, Or.inr ⟨hpos.1, by omega⟩⟩
      have hS_noop : SessInv mo q (rem - 1) esL := ⟨hS.vR_idx, hS.cache_idx, hrem_mono⟩
      simp only [stepLDFShiftedPaper, implEDFShiftedPaper, QueryImpl.add_apply, corrEShiftedPaper,
        StateT.run_bind, StateT.run_get, pure_bind] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hS_noop
      · split at hr
        · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact ⟨hS_noop.vR_idx, hS_noop.cache_idx, hS_noop.bound⟩
        · simp only [hooksLocal, run_liftH, pure_bind, StateT.run_bind, StateT.run_pure,
            StateT.run_modify, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact ⟨hS_noop.vR_idx, hS_noop.cache_idx, hS_noop.bound⟩
    · have hne : ∀ P, (.inr q_inr : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain) ≠
          .inr (.inl (.inr P)) := fun P h => hcorr ⟨P, h⟩
      rw [stepLDFShiftedPaper, implEDFShiftedPaper_eq_implEDF_of_ne_corr _ _ _ _ _ _ _ _ hne] at hr
      exact (stepLDF_sessInv cka prng fs Δcka qep mo hauth (.inr q_inr) esL hS).2 q_inr rfl
        hrem r hr
theorem runLocDFShiftedPaper_le_sum_runLocAtDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (hauth : mo.auth = true) {q rem : ℕ}
    {p : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain → Prop} [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool) (hq : oa.IsQueryBoundP p rem)
    (esL : EStateL Γ T Sig SS RS M E K I) (hS : SessInv mo q rem esL) :
    𝒟[runLocDFShiftedPaper cka prng fs Δcka qep l mo oa esL] {true} ≤
      ∑ j ∈ Finset.range q,
        𝒟[runLocAtDFShiftedPaper cka prng fs Δcka qep l mo j oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing rem esL with
  | pure a =>
    simp only [runLocDFShiftedPaper, runLocAtDFShiftedPaper, simulateQ_pure, StateT.run_pure,
      pure_bind, evalDist_pure]
    by_cases hwin : authOut (2 + Δcka) mo.policy esL = true
    · rw [hwin]; simp only [Bool.true_and]
      have hwin_g : esL.g.win = true := by
        unfold authOut at hwin; simp only [Bool.and_eq_true] at hwin; exact hwin.1.2
      rcases hS.bound with ⟨_, j, hj, hlast⟩ | ⟨hnw, _⟩
      · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_range.mpr hj))
        simp [hlast]
      · rw [hwin_g] at hnw; cases hnw
    · simp [Bool.eq_false_iff.mpr hwin]
  | query_bind t r ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    dsimp only [runLocDFShiftedPaper, runLocAtDFShiftedPaper]
    rw [simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind,
      simulateQ_bind, bind_assoc]
    change 𝒟[stepLDFShiftedPaper cka prng fs Δcka qep l mo t esL >>= fun x =>
        runLocDFShiftedPaper cka prng fs Δcka qep l mo (r x.1) x.2] {true} ≤
      ∑ j ∈ Finset.range q, 𝒟[stepLDFShiftedPaper cka prng fs Δcka qep l mo t esL >>= fun x =>
        runLocAtDFShiftedPaper cka prng fs Δcka qep l mo j (r x.1) x.2] {true}
    refine evalDist_bind_le_sum _ _ _ _ (fun x hx => ?_)
    have hstep := stepLDFShiftedPaper_sessInv cka prng fs Δcka qep l mo hauth t esL hS
    cases t with
    | inl c => exact ih x.1 (by simpa [hp_inl c] using hq.2 x.1) x.2 (hstep.1 c rfl x hx)
    | inr q_sm =>
      have hpos : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
      exact ih x.1 (by simpa [hp_inr q_sm] using hq.2 x.1) x.2 (hstep.2 q_sm rfl hpos x hx)
theorem localAuthDFShiftedPaper_le_sum_localAuthAtDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep l : ℕ) (tL : Option ℕ) (t q : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) (hq : MakesAtMostQueriesDF A q) :
    𝒟[localAuthDFShiftedPaper cka prng fs lam Δcka qep l tL t A] {true} ≤
      ∑ j ∈ Finset.range q,
        𝒟[localAuthAtDFShiftedPaper cka prng fs lam Δcka qep j l tL t A] {true} := by
  rw [MakesAtMostQueriesDF] at hq
  dsimp only [localAuthDFShiftedPaper, localAuthAtDFShiftedPaper]
  refine evalDist_bind_le_sum
    (simulateQ lImpl ((initLocal cka prng fs lam ⟨true, tL, t⟩).run {})) q
    (fun x => match x.1 with
      | none => pure false
      | some (vA, vB) => runLocDFShiftedPaper cka prng fs Δcka qep l ⟨true, tL, t⟩ A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := x.2 })
    (fun j x => match x.1 with
      | none => pure false
      | some (vA, vB) => runLocAtDFShiftedPaper cka prng fs Δcka qep l ⟨true, tL, t⟩ j A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := x.2 })
    (fun x hx => ?_)
  rcases x with ⟨vs, h⟩; cases vs with
  | none => simp
  | some vAB =>
    rcases vAB with ⟨vA, vB⟩
    let mo : Mode := ⟨true, tL, t⟩
    have hS : SessInv mo q q
        ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h } :
          EStateL Γ T Sig SS RS M E K I) := by
      simp only [initLocal, StateT.run_bind, simulateQ_bind, simulateQ_lImpl_run_lift_sampleT,
        MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨⟨kr, s1⟩, ⟨_, _, hs1⟩, ⟨kc, s2⟩, ⟨_, _, hs2⟩,
        ⟨⟨σ, k, sid⟩, s3⟩, hroot, ⟨idx?, s4⟩, hreg, hpure⟩
      injection hs1 with _ hs1; subst hs1; injection hs2 with _ hs2; subst hs2
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hpure
      injection hpure with hvAB hh; injection hvAB with hvAB; injection hvAB with hvA hvB
      subst hvA hvB hh
      obtain ⟨hl_r, hc_r, _, hsid_r1, hsid_r2⟩ := mem_support_rootL prng mo hroot
      obtain ⟨hnone_reg, hsome_reg⟩ := mem_support_regSessOf hreg
      refine ⟨?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
      · intro P rsv hrsv; cases P <;> dsimp only [mkParties] at hrsv
        · split at hrsv
          · rename_i ht0; injection hrsv with hrsv; subst hrsv
            obtain ⟨I', hsid_some⟩ := hsid_r1 ht0.symm
            obtain ⟨⟨idx, hlt, heq⟩, _⟩ := hsome_reg I' hsid_some
            exact ⟨idx, hlt, heq⟩
          · cases hrsv
        · cases hrsv
      · intro Tc σ' k' idx' hc; rcases sid with _ | Ik
        · obtain ⟨_, hs4⟩ := hnone_reg rfl; rw [hs4, hc_r] at hc; cases hc
        · obtain ⟨_, _, _, hc_reg, _⟩ := hsome_reg Ik rfl; rw [hc_reg, hc_r] at hc; cases hc
      · by_cases ht0 : mo.tStar = 0
        · refine Or.inl ⟨ht0, ?_, le_rfl⟩
          obtain ⟨I', hsid_some⟩ := hsid_r1 ht0.symm
          obtain ⟨_, _, hl2, _, _⟩ := hsome_reg I' hsid_some
          have : h.sessions.length ≤ ({} : LState T Sig K I).sessions.length + 1 := by
            rw [← hl_r]; exact hl2
          exact this
        · obtain ⟨_, hs4⟩ := hnone_reg (hsid_r2 (Ne.symm ht0))
          have hlen0 : h.sessions.length = 0 := by rw [hs4, hl_r]; rfl
          exact Or.inr ⟨Nat.pos_of_ne_zero ht0, by rw [hlen0, Nat.zero_add]⟩
    exact runLocDFShiftedPaper_le_sum_runLocAtDFShiftedPaper cka prng fs Δcka qep l mo rfl
      (fun _ => by simp) (fun _ => by simp) A hq _ hS
theorem stepLFixedDFShiftedPaper_eq_of_lt (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep l : ℕ) (mo : Mode) {j : ℕ} (k_fs : K)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I} (hlt : j < esL.h.sessions.length) :
    stepLFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs q esL =
      stepLDFShiftedPaper cka prng fs Δcka qep l mo q esL := by
  by_cases hcorr : ∃ P, q = .inr (.inl (.inr P))
  · rcases hcorr with ⟨P, rfl⟩
    simp [stepLFixedDFShiftedPaper, stepLDFShiftedPaper, implEDFShiftedPaper, QueryImpl.add_apply,
      corrEShiftedPaper, hooksLocalFixed, hooksLocal, StateT.run_bind, StateT.run_get, pure_bind]
  · have hne : ∀ P, q ≠ .inr (.inl (.inr P)) := fun P h => hcorr ⟨P, h⟩
    rw [stepLFixedDFShiftedPaper, stepLDFShiftedPaper,
      implEDFShiftedPaper_eq_implEDF_of_ne_corr _ _ _ _ _ _ _ _ hne,
      implEDFShiftedPaper_eq_implEDF_of_ne_corr _ _ _ _ _ _ _ _ hne]
    exact stepLFixedDF_eq_of_lt cka prng fs Δcka qep mo k_fs q hlt
theorem mem_support_stepLDFShiftedPaper_sessions_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I)
    {r : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I}
    (hr : r ∈ support (stepLDFShiftedPaper cka prng fs Δcka qep l mo q esL)) :
    esL.h.sessions.length ≤ r.2.h.sessions.length := by
  by_cases hcorr : ∃ P, q = .inr (.inl (.inr P))
  · rcases hcorr with ⟨P, rfl⟩
    simp only [stepLDFShiftedPaper, implEDFShiftedPaper, QueryImpl.add_apply, corrEShiftedPaper,
      StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact le_rfl
    · split at hr
      · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact le_rfl
      · simp only [hooksLocal, run_liftH, pure_bind, StateT.run_bind, StateT.run_pure,
          StateT.run_modify, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact le_rfl
  · have hne : ∀ P, q ≠ .inr (.inl (.inr P)) := fun P h => hcorr ⟨P, h⟩
    rw [stepLDFShiftedPaper, implEDFShiftedPaper_eq_implEDF_of_ne_corr _ _ _ _ _ _ _ _ hne] at hr
    exact mem_support_stepLDF_sessions_le cka prng fs Δcka qep mo q esL hr
theorem evalDist_runLocAtDFShiftedPaper_eq_fixed_of_lt (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) {j : ℕ} (k_fs : K) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esL : EStateL Γ T Sig SS RS M E K I} (hlt : j < esL.h.sessions.length) :
    𝒟[runLocAtDFShiftedPaper cka prng fs Δcka qep l mo j oa esL] {true} =
      𝒟[runLocAtFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b' => rw [runLocAtDFShiftedPaper_pure, runLocAtFixedDFShiftedPaper_pure]
  | query_bind q k ih =>
    rw [runLocAtDFShiftedPaper_query_bind, runLocAtFixedDFShiftedPaper_query_bind,
      stepLFixedDFShiftedPaper_eq_of_lt cka prng fs Δcka qep l mo k_fs q hlt]
    refine evalDist_bind_congr_true _ _ _ fun r hr => ih r.1 (lt_of_lt_of_le hlt
      (mem_support_stepLDFShiftedPaper_sessions_le cka prng fs Δcka qep l mo q esL hr))
theorem shiftLe_stepLDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) {j : ℕ}
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain) {esL : EStateL Γ T Sig SS RS M E K I}
    (hle : esL.h.sessions.length ≤ j) (hinv : TabSessInv mo esL.h) :
    ShiftLe mo j (fun r => r.2.h)
      (stepLDFShiftedPaper cka prng fs Δcka qep l mo q esL)
      (fun k_fs => stepLFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs q esL) := by
  by_cases hcorr : ∃ P, q = .inr (.inl (.inr P))
  · rcases hcorr with ⟨P, rfl⟩
    simp only [stepLDFShiftedPaper, stepLFixedDFShiftedPaper, implEDFShiftedPaper,
      QueryImpl.add_apply, corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind,
      hooksLocal, hooksLocalFixed]
    split
    · simp only [StateT.run_pure, simulateQ_pure]; exact ShiftLe.pure mo _ hle hinv
    · split
      · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
          simulateQ_pure]
        exact ShiftLe.pure mo _ hle hinv
      · exact ShiftLe.pure mo _ hle hinv
  · have hne : ∀ P, q ≠ .inr (.inl (.inr P)) := fun P h => hcorr ⟨P, h⟩
    simp only [stepLDFShiftedPaper, stepLFixedDFShiftedPaper,
      implEDFShiftedPaper_eq_implEDF_of_ne_corr _ _ _ _ _ _ _ _ hne]
    exact shiftLe_stepLDF cka prng fs Δcka qep mo q hle hinv
theorem evalDist_runLocAtDFShiftedPaper_le_fixed (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) {j : ℕ} (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hle : esL.h.sessions.length ≤ j) (hinv : TabSessInv mo esL.h) :
    𝒟[runLocAtDFShiftedPaper cka prng fs Δcka qep l mo j oa esL] {true} ≤
      𝒟[($ᵗ K : ProbComp K) >>= fun k_fs =>
        runLocAtFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b' =>
    simp only [runLocAtDFShiftedPaper_pure, runLocAtFixedDFShiftedPaper_pure,
      OracleComp.evalDist_bind_const, le_rfl]
  | query_bind q k ih =>
    simp only [runLocAtDFShiftedPaper_query_bind, runLocAtFixedDFShiftedPaper_query_bind]
    refine shiftLe_stepLDFShiftedPaper cka prng fs Δcka qep l mo q hle hinv
      (fun r => runLocAtDFShiftedPaper cka prng fs Δcka qep l mo j (k r.1) r.2)
      (fun k_fs r => runLocAtFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs (k r.1) r.2)
      (fun r hlt k_fs => (evalDist_runLocAtDFShiftedPaper_eq_fixed_of_lt cka prng fs Δcka qep l mo
        k_fs (k r.1) hlt).le)
      (fun r hle' hinv' => ih r.1 hle' hinv')
theorem localAuthAtDFShiftedPaper_le_localAuthAtFixedDFShiftedPaper
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep j l : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthAtDFShiftedPaper cka prng fs lam Δcka qep j l tL t A] {true} ≤
      𝒟[($ᵗ K : ProbComp K) >>= fun k_fs =>
        localAuthAtFixedDFShiftedPaper cka prng fs lam Δcka qep j l k_fs tL t A] {true} := by
  let mo : Mode := ⟨true, tL, t⟩
  dsimp only [localAuthAtDFShiftedPaper, localAuthAtFixedDFShiftedPaper]
  refine shiftLe_initLocal cka prng fs lam mo (Nat.zero_le j) (fun _ _ => rfl)
    (fun r => match r.1 with
      | none => pure false
      | some (vA, vB) => runLocAtDFShiftedPaper cka prng fs Δcka qep l mo j A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := r.2 })
    (fun k_fs r => match r.1 with
      | none => pure false
      | some (vA, vB) => runLocAtFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := r.2 })
    ?_ ?_
  · rintro ⟨_ | ⟨vA, vB⟩, h⟩ hlt k_fs
    · exact le_rfl
    · exact (evalDist_runLocAtDFShiftedPaper_eq_fixed_of_lt cka prng fs Δcka qep l mo k_fs A hlt).le
  · rintro ⟨_ | ⟨vA, vB⟩, h⟩ hle hinv
    · simp
    · exact evalDist_runLocAtDFShiftedPaper_le_fixed cka prng fs Δcka qep l mo A hle hinv
omit [SampleableType KR] [SampleableType KC] in
theorem evalDist_runFDFShiftedPaper_eq_one_of_win (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (j : ℕ) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) (hwin : st.win = true) :
    𝒟[runFDFShiftedPaper cka prng fs Δcka qep l mo j oa esF st] {true} = 1 := by
  unfold runFDFShiftedPaper
  refine evalDist_bind_eq_one _ _ fun r hr => ?_
  rw [simulateQ_implFS_preserves_win fs _ st hwin r hr]; simp
theorem stepLFixedDFShiftedPaper_preserves_LHSDead (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (hmo : mo.auth = true) (j : ℕ) (k_fs : K)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) (hdead : LHSDead Δcka mo j esL) :
    ∀ r ∈ support (stepLFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs q esL),
      LHSDead Δcka mo j r.2 := by
  intro r hr
  by_cases hcorr : ∃ P, q = .inr (.inl (.inr P))
  · rcases hcorr with ⟨P, rfl⟩
    rcases hdead with ⟨habw, hout⟩ | ⟨hab, hwin, hid, hR⟩
    · simp only [stepLFixedDFShiftedPaper, implEDFShiftedPaper, QueryImpl.add_apply,
        corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind, habw, Bool.true_or,
        ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact Or.inl ⟨habw, hout⟩
    · simp only [stepLFixedDFShiftedPaper, implEDFShiftedPaper, QueryImpl.add_apply,
        corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind, hab, hwin,
        Bool.false_or] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
      · split at hr
        · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact LHSDead.of_abort Δcka mo j rfl
        · simp only [run_liftH, hooksLocalFixed, StateT.run_bind, StateT.run_pure, pure_bind,
            StateT.run_modify, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
  · have hne : ∀ P, q ≠ .inr (.inl (.inr P)) := fun P h => hcorr ⟨P, h⟩
    rw [stepLFixedDFShiftedPaper, implEDFShiftedPaper_eq_implEDF_of_ne_corr _ _ _ _ _ _ _ _ hne]
      at hr
    exact stepLFixedDF_preserves_LHSDead cka prng fs Δcka qep mo hmo j k_fs q esL hdead r hr
theorem evalDist_runLocAtFixedDFShiftedPaper_eq_zero_of_dead (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (hmo : mo.auth = true) (j : ℕ) (k_fs : K)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) (hdead : LHSDead Δcka mo j esL) :
    𝒟[runLocAtFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs oa esL] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b' =>
    rw [runLocAtFixedDFShiftedPaper_pure]
    rcases hdead with ⟨_, hout⟩ | ⟨_, hwin, _, _⟩
    · simp [hout]
    · simp [authOut, hwin]
  | query_bind q k ih =>
    rw [runLocAtFixedDFShiftedPaper_query_bind]
    exact evalDist_bind_eq_zero _ _ fun r hr => ih r.1 r.2
      (stepLFixedDFShiftedPaper_preserves_LHSDead cka prng fs Δcka qep l mo hmo j k_fs q esL
        hdead r hr)
omit [SampleableType KR] [SampleableType KC] in
theorem evalDist_runLocAtFixedDFShiftedPaper_eq_zero_of_not_validGuess
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = false)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool) (esL : EStateL Γ T Sig SS RS M E K I) :
    𝒟[runLocAtFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs oa esL] {true} = 0 := by
  unfold runLocAtFixedDFShiftedPaper
  refine evalDist_bind_eq_zero _ _ fun r _ => ?_
  have h : authOut (2 + Δcka) mo.policy r.2 = false := by simp [authOut, Mode.policy, authLosingConditionsAvoided, hvg]
  simp [h]
omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem syncLFS_corrDoom_true_of_vR_eq_some_none (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true) (P : Party)
    {esL : EStateL Γ T Sig SS RS M E K I} {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E} (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (hvR : (esF.g.st P).vR mo.tStar = some none) :
    P = Party.receiverOf mo.tStar ∧ mo.tStar ≤ esF.g.epoch P ∧
      ({ auth := true, tL := mo.tL, tStar := mo.tStar } : Policy).corrDoom esF.g P = true := by
  have hP : P = Party.receiverOf mo.tStar := by
    by_contra hP
    have hne : (P, mo.tStar) ≠ (Party.receiverOf mo.tStar, mo.tStar) :=
      fun h => hP (Prod.ext_iff.mp h).1
    rcases hs.hvR_other P mo.tStar hne with ⟨_, hF⟩ | ⟨rs, idx?, _, hF, _⟩ <;>
      (rw [hF] at hvR; cases hvR)
  subst hP
  have hge : mo.tStar ≤ esF.g.epoch (Party.receiverOf mo.tStar) := by
    rw [← hs.hepoch, ← hs.htcur_epoch]; by_contra hlt
    rw [(hs.hvR_target_lt (Nat.lt_of_not_le hlt)).2.1] at hvR; cases hvR
  exact ⟨rfl, hge, corrDoom_true_of_ge Δcka ⟨true, mo.tL, mo.tStar⟩ rfl hvg esF.g hge⟩
omit [SampleableType KR] [SampleableType KC] in
theorem leComp_corrEShiftedPaper_LFS (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (hauth : mo.auth = true) (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true) (P : Party)
    {esL : EStateL Γ T Sig SS RS M E K I} {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E} (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (simulateQ lImpl
        ((corrEShiftedPaper l (hooksLocalFixed cka prng fs mo j k_fs) mo.policy P).run esL))
      ((simulateQ (implFS fs)
        ((corrEShiftedPaper l (hooksFS cka prng fs Δcka mo j) mo.policy P).run esF)).run st) := by
  have hcorrAll : esF.g.corrAllowedPaper P = esL.g.corrAllowedPaper P := by
    simp only [GameState.corrAllowedPaper, ← hs.hchallF, hs.hchall]
  unfold corrEShiftedPaper
  simp only [StateT.run_bind, StateT.run_get, pure_bind,
    hs.habortL, hs.habortF, hs.hwinL, hs.hwinF, Bool.false_or, hcorrAll]
  by_cases hallow : esL.g.corrAllowedPaper P = true
  · simp only [hallow, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hdoom_eq :
        (mo.policy.leakDoom esF.g (afterCorrShifted l esF.g P) || mo.policy.corrDoom esF.g P) =
        (mo.policy.leakDoom esL.g (afterCorrShifted l esL.g P) || mo.policy.corrDoom esL.g P) := by
      simp only [Policy.leakDoom, Policy.corrDoom, afterCorrShifted, GameState.leak,
        ← hs.hepoch, ← hs.htL, ← hs.hleaks]
    rw [hdoom_eq]
    by_cases hdoom :
        (mo.policy.leakDoom esL.g (afterCorrShifted l esL.g P) ||
          mo.policy.corrDoom esL.g P) = true
    · simp only [hdoom, ↓reduceIte, abortE]
      exact LeComp.pure (Or.inl (lhsDead_of_abort Δcka mo j esL))
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
      have hnot_cdoom : mo.policy.corrDoom esL.g P = false := by
        cases h : mo.policy.corrDoom esL.g P <;> simp_all
      have hvR_tStar : (esF.g.st P).vR mo.tStar ≠ some none := by
        intro hvR
        have hc := (syncLFS_corrDoom_true_of_vR_eq_some_none fs Δcka qep mo j k_fs hvg P hs hvR).2.2
        simp only [Policy.corrDoom, ← hs.hepoch] at hc
        simp only [Mode.policy, Policy.corrDoom, hauth, hc] at hnot_cdoom; cases hnot_cdoom
      have hvR_eq : ∀ t,
          (match (esF.g.st P).vR t with
            | some (some rs) => some rs | some none => none | none => none) =
          ((esL.g.st P).vR t).map Prod.fst := by
        intro t
        by_cases hPt : (P, t) = (Party.receiverOf mo.tStar, mo.tStar)
        · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hPt
          have hlt : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
            rw [hs.htcur_epoch]; by_contra hge
            have := corrDoom_true_of_ge Δcka mo hauth hvg esL.g (Nat.le_of_not_lt hge)
            rw [this] at hnot_cdoom; cases hnot_cdoom
          obtain ⟨hL, hF, _⟩ := hs.hvR_target_lt hlt; rw [hL, hF]; rfl
        · rcases hs.hvR_other P t hPt with ⟨hL, hF⟩ | ⟨rs, idx?, hL, hF, _⟩ <;> (rw [hL, hF]; rfl)
      have hcorr_pres :
          ∀ corrAt, st.senderCorruptedAt = some corrAt →
            SenderIsJ mo j esL ∧ mo.tStar ≤ qep ∧
            healedBy (afterCorrShifted l esL.g P).tL (2 + Δcka) mo.tStar = false ∧
            (∀ r ∈ (afterCorrShifted l esL.g P).trans,
              r.pos.epoch = mo.tStar → corrAt < r.pos.idx →
                r.pos ∈ (afterCorrShifted l esL.g P).comp) := by
        intro corrAt hcorr
        obtain ⟨hsJ, hqep, hheal, hcomp_mem⟩ := hs.hcorr_sync corrAt hcorr
        refine ⟨hsJ, hqep, healedBy_leak_false_of_false hheal, fun r hr hepoch_r hlt_r => ?_⟩
        dsimp only [afterCorrShifted, GameState.leak] at hr ⊢
        exact List.mem_append_right _ (hcomp_mem r hr hepoch_r hlt_r)
      have hcomp_inv' :
          ∀ pos ∈ (afterCorrShifted l esL.g P).comp,
            healedBy (afterCorrShifted l esL.g P).tL (2 + Δcka) pos.epoch = false :=
        comp_inv_afterCorrShifted esL.g l (2 + Δcka) (by omega) P
          (fun r hr => by rw [← hs.htcur_epoch r.pos.sender]; exact (hs.htrans_wf r hr).2.2.1)
          hs.hcomp_inv
      rcases hs.hvS P with ⟨hvSL, hvSF⟩ | ⟨ss, idx?, hvSL, hvSF, _, _⟩ |
          ⟨hP_s, hle_tcur, hqep_s, hsend_s, hsJ, hvSL, hvSF⟩
      · simp only [run_liftH, hooksLocalFixed, hooksFS, hvSL, hvSF,
          StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
        refine LeComp.pure (Or.inr (Or.inr ⟨?_,
          { hs with
            htL := by simp [afterCorrShifted, GameState.leak, hs.htL, hs.hepoch]
            hcomp := by simp [afterCorrShifted, GameState.leak, hs.htrans, hs.hcomp]
            hcomp_inv := hcomp_inv'
            hleaks := by simp [afterCorrShifted, GameState.leak, hs.htL, hs.hepoch, hs.hleaks]
            hcorrs := by simp [afterCorrShifted, GameState.leak, hs.hepoch, hs.hcorrs]
            hcorr_sync := hcorr_pres }⟩))
        dsimp only [realParty, Option.map]
        congr 2 <;> first | exact (hs.hidL P).trans (hs.hidF P).symm |
          exact hs.hroot P | exact hs.hγ P |
          exact hs.hTcur P | exact hs.htcur P | (funext t; exact (hvR_eq t).symm)
      · simp only [run_liftH, hooksLocalFixed, hooksFS, hvSL, hvSF,
          StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
        refine LeComp.pure (Or.inr (Or.inr ⟨?_,
          { hs with
            htL := by simp [afterCorrShifted, GameState.leak, hs.htL, hs.hepoch]
            hcomp := by simp [afterCorrShifted, GameState.leak, hs.htrans, hs.hcomp]
            hcomp_inv := hcomp_inv'
            hleaks := by simp [afterCorrShifted, GameState.leak, hs.htL, hs.hepoch, hs.hleaks]
            hcorrs := by simp [afterCorrShifted, GameState.leak, hs.hepoch, hs.hcorrs]
            hcorr_sync := hcorr_pres }⟩))
        dsimp only [realParty, Option.map]
        congr 2 <;> first | exact (hs.hidL P).trans (hs.hidF P).symm |
          exact hs.hroot P | exact hs.hγ P |
          exact hs.hTcur P | exact hs.htcur P | (funext t; exact (hvR_eq t).symm)
      · simp only [run_liftH, hooksLocalFixed, hooksFS, hvSL, hvSF,
          StateT.run_bind, StateT.run_get, hs.hextF, pure_bind,
          simulateQ_bind, simulateQ_implFS_corruptSenderQuery, bind_assoc,
          FSAEAD.corruptSender, hs.hendedFS, Bool.false_eq_true, ↓reduceIte,
          StateT.run_modify, StateT.run_pure, simulateQ_pure]
        refine LeComp.pure (Or.inr (Or.inr ⟨?_, ?_⟩))
        · dsimp only [realParty, Option.map]
          congr 2 <;> first | exact (hs.hidL P).trans (hs.hidF P).symm |
            exact hs.hroot P | exact hs.hγ P |
            exact hs.hTcur P | exact hs.htcur P | (funext t; exact (hvR_eq t).symm)
        · refine { hs with
            hendedFS := rfl, hextF := rfl
            htL := by simp [afterCorrShifted, GameState.leak, hs.htL, hs.hepoch]
            hcomp := by simp [afterCorrShifted, GameState.leak, hs.htrans, hs.hcomp]
            hcomp_inv := hcomp_inv'
            hleaks := by simp [afterCorrShifted, GameState.leak, hs.htL, hs.hepoch, hs.hleaks]
            hcorrs := by simp [afterCorrShifted, GameState.leak, hs.hepoch, hs.hcorrs]
            hfsSCorr := rfl, hnot_senderJ := fun hnot => False.elim (hnot hsJ)
            hcorr_sync := ?_ }
          intro corrAt hcorr; dsimp only at hcorr; injection hcorr with hcorr_eq; subst hcorr_eq
          have hheal : healedBy (afterCorrShifted l esL.g P).tL (2 + Δcka) mo.tStar = false := by
            dsimp only [afterCorrShifted, GameState.leak]
            have hep : mo.tStar ≤ esL.g.epoch P := by rwa [← hs.htcur_epoch P]
            have hle_leak : mo.tStar ≤
                (if max (esL.g.epoch .A) (esL.g.epoch .B) = l ∧ esL.g.epoch P + 1 ≤ l then l - 1
                else max (esL.g.epoch .A) (esL.g.epoch .B)) := by
              split_ifs <;> cases P <;> omega
            exact healedBy_leak_false_of_le (by omega) hle_leak
          refine ⟨hsJ, hqep_s, hheal, fun r hr hepoch_r hlt_r => ?_⟩
          cases hsc : st.senderCorruptedAt with
          | none =>
            rw [hsc, Option.getD_none] at hlt_r
            have hle_idx := (hs.htrans_wf r hr).2.2.2.2 hepoch_r hsJ; omega
          | some c₀ =>
            rw [hsc, Option.getD_some] at hlt_r
            exact (hcorr_pres c₀ hsc).2.2.2 r hr hepoch_r hlt_r
  · simp only [hallow, Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
theorem leComp_stepLFixedDFShiftedPaper_stepFDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (j : ℕ) (k_fs : K) (hauth : mo.auth = true)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I} {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E} (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (stepLFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs q esL)
      (stepFDFShiftedPaper cka prng fs Δcka qep l mo j q esF st) := by
  by_cases hcorr : ∃ P, q = .inr (.inl (.inr P))
  · rcases hcorr with ⟨P, rfl⟩
    exact leComp_corrEShiftedPaper_LFS cka prng fs Δcka qep l mo j k_fs hauth hvg P hs
  · have hne : ∀ P, q ≠ .inr (.inl (.inr P)) := fun P h => hcorr ⟨P, h⟩
    rw [stepLFixedDFShiftedPaper, stepFDFShiftedPaper,
      implEDFShiftedPaper_eq_implEDF_of_ne_corr _ _ _ _ _ _ _ _ hne,
      implEDFShiftedPaper_eq_implEDF_of_ne_corr _ _ _ _ _ _ _ _ hne]
    exact leComp_stepLFixedDF_stepFDF cka prng fs Δcka qep mo j k_fs hauth hvg q hs
theorem runLocAtFixedDFShiftedPaper_le_runFDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (j : ℕ) (k_fs : K) (hauth : mo.auth = true)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esL : EStateL Γ T Sig SS RS M E K I} {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E} (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    𝒟[runLocAtFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs oa esL] {true} ≤
      𝒟[runFDFShiftedPaper cka prng fs Δcka qep l mo j oa esF st] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL esF st with
  | pure b' =>
    have hout : (authOut (2 + Δcka) mo.policy esL && (esL.h.lastIdx == some j)) = false := by
      simp [authOut, hs.hwinL]
    simp only [runLocAtFixedDFShiftedPaper, simulateQ_pure, StateT.run_pure, pure_bind, hout]
    have hzero : 𝒟[(pure false : ProbComp Bool)] {true} = 0 := by simp
    rw [hzero]; exact zero_le
  | query_bind q k ih =>
    rw [runLocAtFixedDFShiftedPaper_query_bind, runFDFShiftedPaper_query_bind]
    refine leComp_stepLFixedDFShiftedPaper_stepFDFShiftedPaper cka prng fs Δcka qep l mo j k_fs
      hauth hvg q hs
      (fun rL => runLocAtFixedDFShiftedPaper cka prng fs Δcka qep l mo j k_fs (k rL.1) rL.2)
      (fun rF => runFDFShiftedPaper cka prng fs Δcka qep l mo j (k rF.1.1) rF.1.2 rF.2) ?_
    rintro rL rF (hdead | hwin | ⟨heq_ans, hs'⟩)
    · rw [evalDist_runLocAtFixedDFShiftedPaper_eq_zero_of_dead cka prng fs Δcka qep l mo hauth j
        k_fs (k rL.1) rL.2 hdead]; exact zero_le
    · rw [evalDist_runFDFShiftedPaper_eq_one_of_win cka prng fs Δcka qep l mo j (k rF.1.1) rF.1.2
        rF.2 hwin]; exact prob_le_one
    · rw [heq_ans]; exact ih rF.1.1 hs'
def runFSDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l : ℕ) (mo : Mode)
    (j : ℕ) (b : Bool) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    FSAEAD.AdversaryComp SS RS (Header T) M E
      (Option (Bool × EState (PartyState Γ T Sig (Option SS) (Option RS)) M (Header T × E)
        (FSState T Sig K I SS RS E))) :=
  engRunDFShiftedPaper l (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy
    (initFS cka prng fs lam mo j) {} b A
theorem localAuthAtFixedDFShiftedPaper_le_runFSDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep j l : ℕ) (k_fs : K) (b_fs : Bool) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthAtFixedDFShiftedPaper cka prng fs lam Δcka qep j l k_fs tL t A] {true} ≤
      𝒟[(simulateQ (implFS fs)
        (runFSDFShiftedPaper cka prng fs lam Δcka qep l ⟨true, tL, t⟩ j false A)).run
          (FSAEAD.initState fs k_fs b_fs) >>= fun z => pure z.2.win] {true} := by
  by_cases hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true
  · unfold localAuthAtFixedDFShiftedPaper runFSDFShiftedPaper engRunDFShiftedPaper
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    refine leComp_init cka prng fs lam Δcka qep ⟨true, tL, t⟩ j k_fs b_fs _ _ ?_
    rintro ⟨vsL, hL⟩ ⟨⟨vsF, hF⟩, stF⟩ ⟨vAL, vBL, vAF, vBF, rfl, rfl, hdead | hs⟩
    · exact le_of_eq_of_le (evalDist_runLocAtFixedDFShiftedPaper_eq_zero_of_dead cka prng fs Δcka
        qep l ⟨true, tL, t⟩ rfl j k_fs A _ hdead) zero_le
    · refine le_trans (runLocAtFixedDFShiftedPaper_le_runFDFShiftedPaper cka prng fs Δcka qep l
        ⟨true, tL, t⟩ j k_fs rfl hvg A hs) (le_of_eq (congrArg (fun p => 𝒟[p] {true}) ?_))
      simp only [runFDFShiftedPaper, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, bind_assoc, pure_bind]; rfl
  · have hvg_f : lastLeakGuessAdmissible (2 + Δcka) tL t = false := Bool.eq_false_iff.mpr hvg
    have hzero :
        𝒟[localAuthAtFixedDFShiftedPaper cka prng fs lam Δcka qep j l k_fs tL t A] {true} = 0 := by
      unfold localAuthAtFixedDFShiftedPaper
      refine evalDist_bind_eq_zero _ _ fun r _ => ?_
      rcases r with ⟨_ | ⟨vA, vB⟩, h⟩
      · simp
      · exact evalDist_runLocAtFixedDFShiftedPaper_eq_zero_of_not_validGuess cka prng fs Δcka qep l
          ⟨true, tL, t⟩ j k_fs hvg_f A _
    rw [hzero]; exact zero_le
theorem localAuthAtDFShiftedPaper_le_fsWinDFShiftedPaper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep j l t : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthAtDFShiftedPaper cka prng fs lam Δcka qep j l (some (l - 1)) t A] {true} ≤
      FSAEAD.advantage fs (redFSAuthDFShiftedPaper cka prng fs lam Δcka qep j l t A) := by
  have hred : redFSAuthDFShiftedPaper cka prng fs lam Δcka qep j l t A =
      (runFSDFShiftedPaper cka prng fs lam Δcka qep l ⟨true, some (l - 1), t⟩ j false A >>=
        fun _ => sampleT Bool) := rfl
  rw [hred, advantage_bind_sampleT_bool]
  refine le_trans (localAuthAtDFShiftedPaper_le_localAuthAtFixedDFShiftedPaper cka prng fs lam Δcka
    qep j l (some (l - 1)) t A) ?_
  unfold fsWin
  rw [← OracleComp.evalDist_bind_const ($ᵗ Bool)
        (($ᵗ K : ProbComp K) >>= fun k_fs =>
          localAuthAtFixedDFShiftedPaper cka prng fs lam Δcka qep j l k_fs (some (l - 1)) t A)]
  refine evalDist_bind_mono ($ᵗ Bool) _ _ fun b_fs _ =>
    evalDist_bind_mono ($ᵗ K) _ _ fun k_fs _ =>
      localAuthAtFixedDFShiftedPaper_le_runFSDFShiftedPaper cka prng fs lam Δcka qep j l k_fs b_fs
        (some (l - 1)) t A
end AuthL11ShiftedPaper
/-- Shifted-paper Lemma 11 for `DeliverForge`: the PRF-PRNG branch of `redPRNGAuthDFShiftedPaper`
is bounded by the sum over `j < q` of the FS-AEAD advantages of `redFSAuthDFShiftedPaper j`. -/
theorem lemma11_df_shifted_paper [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l t q : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) (hq : MakesAtMostQueriesDF A q) :
    𝒟[PRFPRNG.branch prng true (redPRNGAuthDFShiftedPaper cka prng fs lam Δcka qep l t A)] {true} ≤
      ∑ j ∈ Finset.range q,
        FSAEAD.advantage fs (redFSAuthDFShiftedPaper cka prng fs lam Δcka qep j l t A) := by
  refine le_trans (branch_redPRNGAuthDFShiftedPaper_le_localAuthDFShiftedPaper cka prng fs lam Δcka
    qep l t A) ?_
  refine le_trans (localAuthDFShiftedPaper_le_sum_localAuthAtDFShiftedPaper cka prng fs lam Δcka qep
    l (some (l - 1)) t q A hq) ?_
  exact Finset.sum_le_sum fun j _ =>
    localAuthAtDFShiftedPaper_le_fsWinDFShiftedPaper cka prng fs lam Δcka qep j l t A
end CryptoGames.SM.Construction.DeliverForge
