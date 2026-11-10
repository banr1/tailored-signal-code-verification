/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions
public import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma17
import VCVio.OracleComp.EvalDist.Measure

/-!
# `DeliverForge` Game and Epoch-Guessing Reduction

**Checked by Lean.** Extends the SM game, engine, and authenticity simulator with the proof-side
`deliverForge` oracle, which tests same-header ciphertext modifications against uncompromised
in-transit records without requiring `safeInj`. Proves the epoch-guessing bound `forgeGame_le_sum`
attributing every non-trivial `deliverForge` win to its canonical `(t*_L, t*)` guess.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17

/-! ## Extended oracle specification and game state -/

/-- Extended SM oracle specification adding `deliverForge` to `SM.spec`. -/
abbrev specDF (St Msg Coins C : Type) :=
  SM.spec St Msg Coins C + ((Party × C × C) →ₒ Option (RecvResult Msg))

abbrev AdversaryCompDF (St Msg Coins C : Type) :=
  OracleComp (unifSpec + specDF St Msg Coins C)

instance (priority := high) {St Msg Coins C : Type} :
    MonadLift ProbComp (AdversaryCompDF St Msg Coins C) :=
  inferInstanceAs (MonadLift ProbComp (TComp _))

abbrev AdversaryDF (St Msg Coins C : Type) :=
  AdversaryCompDF St Msg Coins C Bool

/-- `A` makes at most `q` `specDF` oracle queries on every execution path. -/
def MakesAtMostQueriesDF {St Msg Coins C α : Type}
    (A : AdversaryCompDF St Msg Coins C α) (q : ℕ) : Prop :=
  A.IsQueryBoundP (· matches .inr _) q

/-- Extended SM game state tracking the `deliverForge` win flag and forged epoch. -/
structure GameStateDF (St Msg C : Type) where
  base : GameState St Msg C
  forgeWin : Bool := false
  forgeEpoch : Option ℕ := none

def initStateDF {Key St Msg Coins C : Type} (sm : SMScheme Key St Msg Coins C)
    (k : Key) (b : Bool) : GameStateDF St Msg C :=
  { base := initState sm k b }

section QueriesDF

variable {St Msg Coins C : Type}

def transmitQueryDF (P : Party) (m : Msg) (r : Option Coins) :
    AdversaryCompDF St Msg Coins C (Option C) :=
  query (spec := unifSpec + specDF St Msg Coins C)
    (.inr (.inl (.inl (.inl (.inl (.inl (P, m, r)))))))

def challQueryDF (P : Party) (m₀ m₁ : Msg) (r : Option Coins) :
    AdversaryCompDF St Msg Coins C (Option C) :=
  query (spec := unifSpec + specDF St Msg Coins C)
    (.inr (.inl (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))))

def deliverQueryDF (P : Party) (c : C) :
    AdversaryCompDF St Msg Coins C (Option (RecvResult Msg)) :=
  query (spec := unifSpec + specDF St Msg Coins C)
    (.inr (.inl (.inl (.inl (.inr (P, c))))))

def injectQueryDF (P : Party) (c : C) :
    AdversaryCompDF St Msg Coins C (Option (RecvResult Msg)) :=
  query (spec := unifSpec + specDF St Msg Coins C)
    (.inr (.inl (.inl (.inr (P, c)))))

def corrQueryDF (P : Party) :
    AdversaryCompDF St Msg Coins C (Option St) :=
  query (spec := unifSpec + specDF St Msg Coins C)
    (.inr (.inl (.inr P)))

def deliverForgeQuery (P : Party) (c c' : C) :
    AdversaryCompDF St Msg Coins C (Option (RecvResult Msg)) :=
  query (spec := unifSpec + specDF St Msg Coins C)
    (.inr (.inr (P, c, c')))

end QueriesDF

/-! ## Oracle implementations -/

section OraclesDF

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]

/-- `deliverForge-P(c, c')` on `GameState`, evaluating `c'` against an uncompromised in-transit `c`
with matching header without requiring `safeInj`. -/
def deliverForgeBaseImpl (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    (sameHdr : C → C → Bool) (cfg : Config Msg) :
    QueryImpl ((Party × C × C) →ₒ Option (RecvResult Msg))
      (StateT (GameState St Msg C) ProbComp) := fun ⟨P, c, c'⟩ => do
  let s ← get
  if s.win then return none
  match s.inTransit P.other c with
  | none => return none
  | some r =>
    if (s.inTransit P.other c').isSome || s.comp.contains r.pos || !sameHdr c c' then
      return none
    match sm.receive (s.st P) c' with
    | none => return some .rejected
    | some (st', t', i', m') =>
      if qep + 1 < t' || t' != r.pos.epoch then return some .rejected
      let pos : Pos := ⟨P.other, t', i'⟩
      if s.trivial Δ pos then
        set (s.accept P st' pos)
        return some (.accepted t' i' (some m'))
      else
        if cfg.injectFull t' then set { s with win := true }
        return some .rejected

def oracleImplBaseDF (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) [SampleableType Coins]
    (sameHdr : C → C → Bool) (cfg : Config Msg) :
    QueryImpl (specDF St Msg Coins C) (StateT (GameState St Msg C) ProbComp) :=
  oracleImpl sm Δ qep cfg + deliverForgeBaseImpl sm Δ qep sameHdr cfg

abbrev fullImplBaseDF (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) [SampleableType Coins]
    (sameHdr : C → C → Bool) (cfg : Config Msg) :
    QueryImpl (unifSpec + specDF St Msg Coins C) (StateT (GameState St Msg C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (GameState St Msg C) ProbComp) + oracleImplBaseDF sm Δ qep sameHdr cfg

def liftBaseImpl {ι : Type} {ospec : OracleSpec.{0, 0} ι}
    (impl : QueryImpl ospec (StateT (GameState St Msg C) ProbComp))
    (noneOut : (t : ι) → ospec.Range t) :
    QueryImpl ospec (StateT (GameStateDF St Msg C) ProbComp) := fun t => do
  let s ← get
  if s.forgeWin then return noneOut t
  let (res, base') ← StateT.lift ((impl t).run s.base)
  set { s with base := base' }
  return res

def deliverForgeImpl (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    (sameHdr : C → C → Bool) (cfg : Config Msg) :
    QueryImpl ((Party × C × C) →ₒ Option (RecvResult Msg))
      (StateT (GameStateDF St Msg C) ProbComp) := fun ⟨P, c, c'⟩ => do
  let s ← get
  if s.forgeWin || s.base.win then return none
  match s.base.inTransit P.other c with
  | none => return none
  | some r =>
    if (s.base.inTransit P.other c').isSome || s.base.comp.contains r.pos || !sameHdr c c' then
      return none
    match sm.receive (s.base.st P) c' with
    | none => return some .rejected
    | some (st', t', i', m') =>
      if qep + 1 < t' || t' != r.pos.epoch then return some .rejected
      let pos : Pos := ⟨P.other, t', i'⟩
      if s.base.trivial Δ pos then
        set { s with base := s.base.accept P st' pos }
        return some (.accepted t' i' (some m'))
      else
        if cfg.injectFull t' then
          set { s with base := { s.base with win := true }
                       forgeWin := true
                       forgeEpoch := some t' }
        return some .rejected

def noneOutBase : (q : (spec St Msg Coins C).Domain) → (spec St Msg Coins C).Range q
  | .inl (.inl (.inl (.inl _))) => none
  | .inl (.inl (.inl (.inr _))) => none
  | .inl (.inl (.inr _)) => none
  | .inl (.inr _) => none
  | .inr _ => none

def oracleImplDF (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) [SampleableType Coins]
    (sameHdr : C → C → Bool) (cfg : Config Msg) :
    QueryImpl (specDF St Msg Coins C) (StateT (GameStateDF St Msg C) ProbComp) :=
  liftBaseImpl (oracleImpl sm Δ qep cfg) noneOutBase +
    deliverForgeImpl sm Δ qep sameHdr cfg

abbrev fullImplDF (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) [SampleableType Coins]
    (sameHdr : C → C → Bool) (cfg : Config Msg) :
    QueryImpl (unifSpec + specDF St Msg Coins C) (StateT (GameStateDF St Msg C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (GameStateDF St Msg C) ProbComp) + oracleImplDF sm Δ qep sameHdr cfg

end OraclesDF

/-! ## Engine wrapper -/

section EngineDF

variable {ι : Type} {tspec : OracleSpec.{0, 0} ι}
  {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
  [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]

local notation "EMt" => EM tspec Γv T Sv SSv RSv M E HS

/-- Engine implementation of `deliverForge-P(c, c')` via `vRecv` and `commitE`. -/
def deliverForgeE (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep : ℕ) (cfg : Config M) :
    QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (RecvResult M)) EMt :=
  fun ⟨P, c, c'⟩ => do
    let es ← get
    let s := es.g
    if es.abort || s.win then return none
    match s.inTransit P.other c with
    | none => return none
    | some r =>
      if (s.inTransit P.other c').isSome || s.comp.contains r.pos || c.1 != c'.1 then
        return none
      match ← liftH (vRecv hk s P (s.st P) c' none) with
      | none =>
        abortE
        return none
      | some none => return some .rejected
      | some (some (st', t', i', m')) =>
        if qep + 1 < t' || t' != r.pos.epoch then return some .rejected
        let pos : Pos := ⟨P.other, t', i'⟩
        if s.trivial Δ pos then
          match ← commitE hk s P (s.st P) st' pos with
          | none => return none
          | some s₁ =>
            modify fun es => { es with g := s₁ }
            return some (.accepted t' i' (some m'))
        else
          if cfg.injectFull t' then modify fun es => { es with g := { es.g with win := true } }
          return some .rejected

def implEDF (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
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
      (corrE hk π)
  let i₂ : QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (RecvResult M)) EMt :=
    deliverForgeE hk Δ qep cfg
  HAdd.hAdd i₀ (HAdd.hAdd i₁ i₂)

def engRunDF (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
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
    let (b', es) ← (simulateQ (implEDF hk Δ qep maxSkip cfg π) A).run { g := g, h := h }
    return some (b', es)

end EngineDF

/-! ## Authenticity reductions -/

section ReductionsDF

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

abbrev SchemeAdversaryDF (Γ T Sig SS RS M CCoins E : Type) :=
  AdversaryDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

def authSimDF {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS Γv Sv SSv RSv : Type}
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (tL : Option ℕ) (tStar : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    TComp tspec Bool := do
  let π : Policy := ⟨true, tL, tStar⟩
  let r ← engRunDF hk (2 + Δcka) qep fs.maxSkip (Config.auth tStar) π init h₀ false A
  return match r with
    | none => false
    | some (_, es) => authOut (2 + Δcka) π es

def redCKAAuthDF (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (tStar : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    CKA.Adversary Γ CCoins T I :=
  show CKA.AdversaryComp Γ CCoins T I Bool from
  authSimDF fs Δcka qep (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩)
    (initCKA cka prng fs lam ⟨true, tL, tStar⟩) {} tL tStar A

def redPRNGAuthDF (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (tStar : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from
  authSimDF fs Δcka qep (hooksPRNG cka prng fs ⟨true, tL, tStar⟩)
    (initPRNG cka prng fs lam ⟨true, tL, tStar⟩) {} tL tStar A

def redFSAuthDF (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (j : ℕ) (tL : Option ℕ) (tStar : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    FSAEAD.Adversary SS RS (Header T) M E :=
  show FSAEAD.AdversaryComp SS RS (Header T) M E Bool from do
  let _ ← engRunDF (hooksFS cka prng fs Δcka ⟨true, tL, tStar⟩ j) (2 + Δcka) qep fs.maxSkip
    (Config.auth tStar) ⟨true, tL, tStar⟩ (initFS cka prng fs lam ⟨true, tL, tStar⟩ j) {} false A
  sampleT Bool

end ReductionsDF

/-! ## Authenticity simulator `challSimDF` -/

section SimDF

variable {St Msg Coins C : Type}

local notation "CompDF" => AdversaryCompDF St Msg Coins C
local notation "RedMDF" => StateT (Mirror Msg C) (AdversaryCompDF St Msg Coins C)

def simTransmitDF (Δ qep : ℕ) :
    QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) RedMDF :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    let res ← StateT.lift (transmitQueryDF (St := St) P m r)
    match res, s.epMgmt Δ qep P r.isSome with
    | some c, some s₁ => set (s₁.record Δ P () ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ false)
    | _, _ => pure ()
    return res

def simChallDF (Δ qep : ℕ) :
    QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) RedMDF :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    match s.epMgmt Δ qep P r.isSome with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) then return none
      let mb := if s.b then m₁ else m₀
      let res ← StateT.lift (transmitQueryDF (St := St) P mb r)
      match res with
      | none => return none
      | some c =>
        set (s₁.record Δ P () ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, mb, c⟩ true)
        return some c

def simDeliverDF [DecidableEq C] : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) RedMDF :=
  fun ⟨P, c⟩ => do
    let s ← get
    let res ← StateT.lift (deliverQueryDF (St := St) (Coins := Coins) P c)
    match res, s.inTransit P.other c with
    | some (.accepted t' i' m), some r =>
      set (s.accept P () r.pos)
      return some (.accepted t' i' (if s.chall.contains r.pos then none else m))
    | _, _ => return res

def simInjectDF : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) RedMDF :=
  fun ⟨P, c⟩ => do
    let s ← get
    let res ← StateT.lift (injectQueryDF (St := St) (Coins := Coins) P c)
    match res with
    | some (.accepted t' i' _) => set (s.accept P () ⟨P.other, t', i'⟩)
    | _ => pure ()
    return res

def simCorrDF : QueryImpl (Party →ₒ Option St) RedMDF := fun P => do
  let s ← get
  let res ← StateT.lift (corrQueryDF (Msg := Msg) (Coins := Coins) (C := C) P)
  if res.isSome then set (s.afterCorr P)
  return res

def simDeliverForgeDF :
    QueryImpl ((Party × C × C) →ₒ Option (RecvResult Msg)) RedMDF :=
  fun ⟨P, c, c'⟩ => do
    let s ← get
    let res ← StateT.lift (deliverForgeQuery (St := St) (Coins := Coins) P c c')
    match res with
    | some (.accepted t' i' _) => set (s.accept P () ⟨P.other, t', i'⟩)
    | _ => pure ()
    return res

def simCoinsDF : QueryImpl unifSpec RedMDF := fun n =>
  StateT.lift (query (spec := unifSpec + specDF St Msg Coins C) (.inl n))

def simOraclesDF [DecidableEq C] (Δ qep : ℕ) : QueryImpl (specDF St Msg Coins C) RedMDF :=
  let i₁ : QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) RedMDF := simTransmitDF Δ qep
  let i₂ : QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) RedMDF := simChallDF Δ qep
  let i₃ : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) RedMDF := simDeliverDF
  let i₄ : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) RedMDF := simInjectDF
  let i₅ : QueryImpl (Party →ₒ Option St) RedMDF := simCorrDF
  let i₆ : QueryImpl ((Party × C × C) →ₒ Option (RecvResult Msg)) RedMDF := simDeliverForgeDF
  HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅) i₆

def simImplDF [DecidableEq C] (Δ qep : ℕ) :
    QueryImpl (unifSpec + specDF St Msg Coins C) RedMDF :=
  let c : QueryImpl unifSpec RedMDF := simCoinsDF
  let o : QueryImpl (specDF St Msg Coins C) RedMDF := simOraclesDF Δ qep
  HAdd.hAdd c o

/-- Authenticity simulator lifting `Thm1.challSim` to `specDF`. -/
def challSimDF [DecidableEq C] (Δ qep : ℕ) (A : AdversaryDF St Msg Coins C) :
    AdversaryDF St Msg Coins C :=
  show AdversaryCompDF St Msg Coins C Bool from do
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : AdversaryCompDF St Msg Coins C Bool)
  (simulateQ (simImplDF Δ qep) A).run' ({ st := fun _ => (), b } : Mirror Msg C)

end SimDF

/-! ## Games and epoch-guessing reduction -/

section GamesDF

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]

def runBaseDF (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : C → C → Bool) (cfg : Config Msg) (b : Bool)
    (B : AdversaryDF St Msg Coins C) : ProbComp (Bool × GameState St Msg C) := do
  let k ← $ᵗ Key
  (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg) B).run (initState sm k b)

def runDF (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : C → C → Bool) (cfg : Config Msg) (b : Bool)
    (B : AdversaryDF St Msg Coins C) : ProbComp (Bool × GameStateDF St Msg C) := do
  let k ← $ᵗ Key
  (simulateQ (fullImplDF sm Δ qep sameHdr cfg) B).run (initStateDF sm k b)

/-- Unguessed `DeliverForge` game returning `s.forgeWin` at `Config.h1`. -/
def forgeGame (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : C → C → Bool) (B : AdversaryDF St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (_, s) ← runDF sm Δ qep sameHdr Config.h1 b B
  return s.forgeWin

def forgeGameWin (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : C → C → Bool) (B : AdversaryDF St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (_, s) ← runBaseDF sm Δ qep sameHdr Config.h1 b B
  return s.win

/-- Guessed `DeliverForge` authenticity game for target `(tLStar, tStar)`. -/
def forgeGameGuessed (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : C → C → Bool) (tLStar : Option ℕ) (tStar : ℕ)
    (B : AdversaryDF St Msg Coins C) : ProbComp Bool := do
  let (_, s) ← runBaseDF sm Δ qep sameHdr (Config.auth tStar) false B
  return s.win && authLosingConditionsAvoided Δ tLStar tStar s

noncomputable def forgeAdvantage (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : C → C → Bool) (B : AdversaryDF St Msg Coins C) : ℝ≥0∞ :=
  𝒟[forgeGame sm Δ qep sameHdr B] {true}

noncomputable def forgeGuessedAdvantage (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : C → C → Bool) (tLStar : Option ℕ) (tStar : ℕ)
    (B : AdversaryDF St Msg Coins C) : ℝ≥0∞ :=
  𝒟[forgeGameGuessed sm Δ qep sameHdr tLStar tStar B] {true}

private theorem evalDist_bind_mono {α : Type} (p : ProbComp α) (f g : α → ProbComp Bool)
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

theorem simulateQ_fullImplDF_forgeWin_le_base_win (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] (sameHdr : C → C → Bool) (cfg : Config Msg)
    {α : Type} (oa : AdversaryCompDF St Msg Coins C α) :
    ∀ (s : GameStateDF St Msg C),
      (s.forgeWin = true → s.base.win = true) →
      𝒟[(simulateQ (fullImplDF sm Δ qep sameHdr cfg) oa).run s >>= fun z => pure z.2.forgeWin]
        {true} ≤
      𝒟[(simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg) oa).run s.base >>=
        fun z => pure z.2.win] {true} := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s himp
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    cases hfw : s.forgeWin
    · simp
    · simp [himp hfw]
  | query_bind t r ih =>
    intro s himp
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self, bind_assoc]
    have hor : (s.forgeWin || s.base.win) = s.base.win := by
      cases hfw : s.forgeWin
      · simp
      · simp [himp hfw]
    rcases t with n | (q | ⟨P, c, c'⟩)
    · change 𝒟[((liftM (OracleSpec.query (spec := unifSpec) n) :
          StateT (GameStateDF St Msg C) ProbComp _).run s) >>= _] {true} ≤
        𝒟[((liftM (OracleSpec.query (spec := unifSpec) n) :
          StateT (GameState St Msg C) ProbComp _).run s.base) >>= _] {true}
      simp only [StateT.run_monadLift, bind_assoc, pure_bind]
      exact evalDist_bind_mono _ _ _ fun u => ih u s himp
    · change 𝒟[(liftBaseImpl (oracleImpl sm Δ qep cfg) noneOutBase q).run s >>= _] {true} ≤
        𝒟[(oracleImpl sm Δ qep cfg q).run s.base >>= _] {true}
      unfold liftBaseImpl
      by_cases hfw : s.forgeWin = true
      · have hwin : s.base.win = true := himp hfw
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hfw, ↓reduceIte]
        rcases q with (((⟨P, m, ro⟩ | ⟨P, m0, m1, ro⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
        · change _ ≤ 𝒟[(transmitImpl sm Δ qep ⟨P, m, ro⟩).run s.base >>= _] {true}
          unfold transmitImpl noneOutBase
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hwin, ↓reduceIte]
          exact ih none s himp
        · change _ ≤ 𝒟[(challImpl sm Δ qep cfg ⟨P, m0, m1, ro⟩).run s.base >>= _] {true}
          unfold challImpl noneOutBase
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hwin, ↓reduceIte]
          exact ih none s himp
        · change _ ≤ 𝒟[(deliverImpl sm cfg ⟨P, c⟩).run s.base >>= _] {true}
          unfold deliverImpl noneOutBase
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hwin, ↓reduceIte]
          exact ih none s himp
        · change _ ≤ 𝒟[(injectImpl sm Δ qep cfg ⟨P, c⟩).run s.base >>= _] {true}
          unfold injectImpl noneOutBase
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hwin,
            Bool.true_or, ↓reduceIte]
          exact ih none s himp
        · change _ ≤ 𝒟[(corrImpl P).run s.base >>= _] {true}
          unfold corrImpl noneOutBase
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hwin,
            Bool.true_or, ↓reduceIte]
          exact ih none s himp
      · have hfwF : s.forgeWin = false := Bool.eq_false_iff.mpr hfw
        simp only [StateT.run_bind, StateT.run_get, pure_bind]
        rw [ite_eq_right_iff.mpr (fun h => absurd h hfw)]
        simp only [StateT_run_lift, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, bind_assoc]
        exact evalDist_bind_mono _ _ _ fun z => ih z.1 { s with base := z.2 } (by simp [hfwF])
    · change 𝒟[(deliverForgeImpl sm Δ qep sameHdr cfg ⟨P, c, c'⟩).run s >>= _] {true} ≤
        𝒟[(deliverForgeBaseImpl sm Δ qep sameHdr cfg ⟨P, c, c'⟩).run s.base >>= _] {true}
      unfold deliverForgeImpl deliverForgeBaseImpl
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      rw [hor]
      split
      · simp only [StateT.run_pure, pure_bind]; exact ih none s himp
      · cases s.base.inTransit P.other c with
        | none => simp only [StateT.run_pure, pure_bind]; exact ih none s himp
        | some rec_r =>
          dsimp only
          split
          · simp only [StateT.run_pure, pure_bind]; exact ih none s himp
          · cases sm.receive (s.base.st P) c' with
            | none => simp only [StateT.run_pure, pure_bind]; exact ih (some .rejected) s himp
            | some res =>
              rcases res with ⟨st', t', i', m'⟩
              dsimp only
              split
              · simp only [StateT.run_pure, pure_bind]; exact ih (some .rejected) s himp
              · split
                · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
                  exact ih (some (.accepted t' i' (some m')))
                    { s with base := s.base.accept P st' ⟨P.other, t', i'⟩ }
                    (fun h => by
                      have hwin := himp h
                      simpa [GameState.accept, GameState.delete] using hwin)
                · split
                  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
                    exact ih (some .rejected)
                      { s with base := { s.base with win := true }
                               forgeWin := true
                               forgeEpoch := some t' }
                      (fun _ => rfl)
                  · simp only [StateT.run_pure, pure_bind]; exact ih (some .rejected) s himp

theorem forgeGame_le_forgeGameWin (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins]
    (sameHdr : C → C → Bool) (B : AdversaryDF St Msg Coins C) :
    𝒟[forgeGame sm Δ qep sameHdr B] {true} ≤
      𝒟[forgeGameWin sm Δ qep sameHdr B] {true} := by
  unfold forgeGame forgeGameWin runDF runBaseDF
  simp only [bind_assoc]
  refine evalDist_bind_mono ($ᵗ Bool) _ _ fun b => ?_
  refine evalDist_bind_mono ($ᵗ Key) _ _ fun k => ?_
  exact simulateQ_fullImplDF_forgeWin_le_base_win sm Δ qep sameHdr Config.h1 B
    (initStateDF sm k b) (by simp [initStateDF])

theorem eq_of_mem_support_fullImplBaseDF_of_win_true (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] (sameHdr : C → C → Bool) (cfg : Config Msg)
    (t : (unifSpec + specDF St Msg Coins C).Domain)
    {sa : GameState St Msg C} (hwin : sa.win = true)
    {z : (unifSpec + specDF St Msg Coins C).Range t × GameState St Msg C}
    (hz : z ∈ support ((fullImplBaseDF sm Δ qep sameHdr cfg t).run sa)) :
    z.2 = sa := by
  rcases t with n | (q | ⟨P, c, c'⟩)
  · exact eq_of_mem_support_fullImpl_of_win_true sm Δ qep cfg (.inl n) hwin hz
  · exact eq_of_mem_support_fullImpl_of_win_true sm Δ qep cfg (.inr q) hwin hz
  · change z ∈ support ((deliverForgeBaseImpl sm Δ qep sameHdr cfg ⟨P, c, c'⟩).run sa) at hz
    unfold deliverForgeBaseImpl at hz
    simp [hwin] at hz
    rw [hz]

theorem eq_of_mem_support_simulateQ_DF_of_win_true (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] (sameHdr : C → C → Bool) (cfg : Config Msg)
    {β : Type} (c : AdversaryCompDF St Msg Coins C β) :
    ∀ {sa : GameState St Msg C} {z : β × GameState St Msg C},
      sa.win = true →
      z ∈ support ((simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg) c).run sa) →
      z.2 = sa := by
  induction c using OracleComp.inductionOn with
  | pure a =>
    intro sa z _ hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t r ih =>
    intro sa z hwin hz
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u, sa₁⟩, h₁, h₂⟩
    have hsa₁ : sa₁ = sa :=
      eq_of_mem_support_fullImplBaseDF_of_win_true sm Δ qep sameHdr cfg t hwin h₁
    subst hsa₁
    exact ih u hwin h₂

theorem evalDist_simulateQ_DF_eq_one_of_win_true (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] (sameHdr : C → C → Bool) (cfg : Config Msg)
    {β : Type} (c : AdversaryCompDF St Msg Coins C β)
    (f : β × GameState St Msg C → ProbComp Bool)
    {sa : GameState St Msg C} (hwin : sa.win = true)
    (hf : ∀ z : β × GameState St Msg C, z.2 = sa → f z = pure true) :
    𝒟[(simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg) c).run sa >>= f] {true} = 1 := by
  have hcongr : 𝒟[(simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg) c).run sa >>= f] =
      𝒟[(simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg) c).run sa >>=
        fun _ => (pure true : ProbComp Bool)] := by
    refine evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
    rw [hf z (eq_of_mem_support_simulateQ_DF_of_win_true sm Δ qep sameHdr cfg c hwin hz)]
  rw [hcongr, OracleComp.evalDist_bind_const]
  simp

theorem simulateQ_fullImplBaseDF_liftM_run {α : Type} (sm : SMScheme Key St Msg Coins C)
    (Δ qep : ℕ) [SampleableType Coins] (sameHdr : C → C → Bool) (cfg : Config Msg)
    (p : ProbComp α) (s : GameState St Msg C) :
    (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
      (liftM p : AdversaryCompDF St Msg Coins C α)).run s =
      p >>= fun a => pure (a, s) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    change (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
      ((liftM (OracleSpec.query (spec := unifSpec + specDF St Msg Coins C) (.inl t)) :
          AdversaryCompDF St Msg Coins C _) >>=
        fun u => (liftM (k u) : AdversaryCompDF St Msg Coins C α))).run s = _
    rw [simulateQ_query_bind, StateT.run_bind]
    change ((liftM (OracleSpec.query (spec := unifSpec) t) :
        StateT (GameState St Msg C) ProbComp _).run s >>=
      fun z => (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg) (liftM (k z.1))).run z.2) = _
    simp only [StateT.run_monadLift, bind_assoc, pure_bind, ih]

theorem simulateQ_simDF_query_bind {α : Type} (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] (sameHdr : C → C → Bool) (cfg : Config Msg)
    (q : (unifSpec + specDF St Msg Coins C).Domain)
    (r : (unifSpec + specDF St Msg Coins C).Range q → AdversaryCompDF St Msg Coins C α)
    (m : Mirror Msg C) (sa : GameState St Msg C) :
    (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
      ((simulateQ (simImplDF Δ qep)
        ((liftM (OracleSpec.query q) : AdversaryCompDF St Msg Coins C _) >>= r)).run m)).run sa =
    (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
      ((simImplDF Δ qep q).run m)).run sa >>=
      fun z => (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
        ((simulateQ (simImplDF Δ qep) (r z.1.1)).run z.1.2)).run z.2 := by
  rw [simulateQ_query_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self]

theorem fullImplBaseDF_inl (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] (sameHdr : C → C → Bool) (cfg : Config Msg)
    (n : unifSpec.Domain) (s : GameState St Msg C) :
    (fullImplBaseDF sm Δ qep sameHdr cfg (.inl n)).run s =
      (fullImpl sm Δ qep cfg (.inl n)).run s := rfl

theorem fullImplBaseDF_inr_inl (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] (sameHdr : C → C → Bool) (cfg : Config Msg)
    (q : (spec St Msg Coins C).Domain) (s : GameState St Msg C) :
    (fullImplBaseDF sm Δ qep sameHdr cfg (.inr (.inl q))).run s =
      (fullImpl sm Δ qep cfg (.inr q)).run s := rfl

theorem simImplDF_coins_eq (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] (sameHdr : C → C → Bool) (cfg : Config Msg)
    (n : unifSpec.Domain) (m : Mirror Msg C) (sa : GameState St Msg C) :
    (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
      ((simImplDF Δ qep (.inl n)).run m)).run sa =
    (simulateQ (fullImpl sm Δ qep cfg)
      ((simImpl Δ qep (fun _ => none) none (.inl n)).run m)).run sa := by
  change (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg) ((simCoinsDF n).run m)).run sa =
    (simulateQ (fullImpl sm Δ qep cfg) ((simCoins n).run m)).run sa
  unfold simCoinsDF simCoins
  simp

theorem simImplDF_oracle_eq (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] (sameHdr : C → C → Bool) (cfg : Config Msg)
    (q : (spec St Msg Coins C).Domain) (m : Mirror Msg C) (sa : GameState St Msg C) :
    (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
      ((simImplDF Δ qep (.inr (.inl q))).run m)).run sa =
    (simulateQ (fullImpl sm Δ qep cfg)
      ((simImpl Δ qep (fun _ => none) none (.inr q)).run m)).run sa := by
  rcases q with (((⟨P, m_msg, r_opt⟩ | ⟨P, m₀, m₁, r_opt⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
        ((simTransmitDF Δ qep ⟨P, m_msg, r_opt⟩).run m)).run sa =
      (simulateQ (fullImpl sm Δ qep cfg)
        ((simTransmit Δ qep ⟨P, m_msg, r_opt⟩).run m)).run sa
    unfold simTransmitDF simTransmit transmitQueryDF transmitQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
      simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure, StateT.run_pure]
    refine congrArg (_ >>= ·) (funext fun p => ?_)
    rcases p with ⟨⟨res, m'⟩, sa'⟩
    cases res <;> cases m.epMgmt Δ qep P r_opt.isSome <;> simp [StateT.run_set]
  · change (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
        ((simChallDF Δ qep ⟨P, m₀, m₁, r_opt⟩).run m)).run sa =
      (simulateQ (fullImpl sm Δ qep cfg)
        ((simChall Δ qep (fun _ => none) none ⟨P, m₀, m₁, r_opt⟩).run m)).run sa
    unfold simChallDF simChall simSend transmitQueryDF transmitQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, Option.getD_none]
    cases m.epMgmt Δ qep P r_opt.isSome with
    | none => simp
    | some s₁ =>
      dsimp only
      split
      · simp
      · simp only [StateT.run_bind, StateT_run_lift, simulateQ_bind,
          simulateQ_HasQuery_query, simulateQ_pure, StateT.run_pure]
        refine congrArg (_ >>= ·) (funext fun p => ?_)
        rcases p with ⟨⟨res, m'⟩, sa'⟩
        cases res <;> simp [StateT.run_set]
  · change (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
        ((simDeliverDF ⟨P, c⟩).run m)).run sa =
      (simulateQ (fullImpl sm Δ qep cfg)
        ((simDeliver ⟨P, c⟩).run m)).run sa
    unfold simDeliverDF simDeliver deliverQueryDF deliverQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
      simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure, StateT.run_pure]
    refine congrArg (_ >>= ·) (funext fun p => ?_)
    rcases p with ⟨⟨res, m'⟩, sa'⟩
    cases res with
    | none => simp
    | some r => cases r <;> cases m.inTransit P.other c <;> simp [StateT.run_set]
  · change (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
        ((simInjectDF ⟨P, c⟩).run m)).run sa =
      (simulateQ (fullImpl sm Δ qep cfg)
        ((simInject ⟨P, c⟩).run m)).run sa
    unfold simInjectDF simInject injectQueryDF injectQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
      simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure, StateT.run_pure]
    refine congrArg (_ >>= ·) (funext fun p => ?_)
    rcases p with ⟨⟨res, m'⟩, sa'⟩
    cases res with
    | none => simp
    | some r => cases r <;> simp [StateT.run_set]
  · change (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
        ((simCorrDF P).run m)).run sa =
      (simulateQ (fullImpl sm Δ qep cfg)
        ((simCorr P).run m)).run sa
    unfold simCorrDF simCorr corrQueryDF corrQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
      simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure, StateT.run_pure]
    refine congrArg (_ >>= ·) (funext fun p => ?_)
    rcases p with ⟨⟨res, m'⟩, sa'⟩
    cases res <;> simp [StateT.run_set]

theorem deliverForge_step_h (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] (sameHdr : C → C → Bool) (cfg : Config Msg)
    (P : Party) (c c' : C) (s : GameState St Msg C) (hwin : s.win = false) :
    (fullImplBaseDF sm Δ qep sameHdr cfg (.inr (.inr ⟨P, c, c'⟩))).run s =
      match s.inTransit P.other c with
      | none => pure (none, s)
      | some r =>
        if (s.inTransit P.other c').isSome || s.comp.contains r.pos || !sameHdr c c' then
          pure (none, s)
        else
          match sm.receive (s.st P) c' with
          | none => pure (some .rejected, s)
          | some (st', t', i', m') =>
            if qep + 1 < t' || t' != r.pos.epoch then pure (some .rejected, s)
            else
              let pos : Pos := ⟨P.other, t', i'⟩
              if s.trivial Δ pos then
                pure (some (.accepted t' i' (some m')), s.accept P st' pos)
              else
                pure (some .rejected, if cfg.injectFull t' then { s with win := true } else s) := by
  change (deliverForgeBaseImpl sm Δ qep sameHdr cfg ⟨P, c, c'⟩).run s = _
  unfold deliverForgeBaseImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_eq_true, ↓reduceIte]
  cases s.inTransit P.other c with
  | none => simp
  | some r =>
    dsimp only
    split
    · simp
    · cases sm.receive (s.st P) c' with
      | none => simp
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        dsimp only
        split
        · simp
        · split
          · simp [StateT.run_set]
          · split <;> simp [StateT.run_set]

theorem deliverForge_step_auth (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] (sameHdr : C → C → Bool) (cfg : Config Msg)
    (P : Party) (c c' : C) (s : GameState St Msg C) (hwin : s.win = false) :
    (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
      ((simImplDF Δ qep (.inr (.inr ⟨P, c, c'⟩))).run (toMirror s))).run (toAuth s) =
      match s.inTransit P.other c with
      | none => pure ((none, toMirror s), toAuth s)
      | some r =>
        if (s.inTransit P.other c').isSome || s.comp.contains r.pos || !sameHdr c c' then
          pure ((none, toMirror s), toAuth s)
        else
          match sm.receive (s.st P) c' with
          | none => pure ((some .rejected, toMirror s), toAuth s)
          | some (st', t', i', m') =>
            if qep + 1 < t' || t' != r.pos.epoch then
              pure ((some .rejected, toMirror s), toAuth s)
            else
              let pos : Pos := ⟨P.other, t', i'⟩
              if s.trivial Δ pos then
                let s' := s.accept P st' pos
                pure ((some (.accepted t' i' (some m')), toMirror s'), toAuth s')
              else
                pure ((some .rejected, toMirror s),
                  if cfg.injectFull t' then { toAuth s with win := true } else toAuth s) := by
  change (simulateQ (fullImplBaseDF sm Δ qep sameHdr cfg)
    ((simDeliverForgeDF ⟨P, c, c'⟩).run (toMirror s))).run (toAuth s) = _
  unfold simDeliverForgeDF deliverForgeQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
    simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [deliverForge_step_h sm Δ qep sameHdr cfg P c c' (toAuth s) hwin]
  have hcomp : (toAuth s).comp = s.comp := rfl
  rw [toAuth_inTransit, toAuth_inTransit, hcomp, toAuth_st]
  cases s.inTransit P.other c with
  | none => simp
  | some r =>
    dsimp only
    split
    · simp
    · cases sm.receive (s.st P) c' with
      | none => simp
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        dsimp only
        split
        · simp
        · rw [toAuth_trivial]
          split
          · simp [StateT.run_set, toAuth_accept]
            exact toMirror_accept _ _ _ _
          · simp

theorem closeBySum_simulateQ_DF (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] (sameHdr : C → C → Bool) (hΔ : 0 < Δ) {α : Type}
    (oa : AdversaryCompDF St Msg Coins C α)
    (f1 f2 : α × GameState St Msg C → ProbComp Bool)
    (fAuth : ℕ → Option ℕ → (α × Mirror Msg C) × GameState St Msg C → ProbComp Bool)
    (hf12 : ∀ a s, s.win = false → f1 (a, s) = f2 (a, s))
    (hfAuth : ∀ t tL (z : (α × Mirror Msg C) × GameState St Msg C),
      z.2.win = true → authLosingConditionsAvoided Δ tL t z.2 = true → fAuth t tL z = pure true) :
    ∀ {s : GameState St Msg C},
      WFState Δ s → s.win = false →
      CloseBySum Δ qep
        ((simulateQ (fullImplBaseDF sm Δ qep sameHdr Config.h1) oa).run s >>= f1)
        ((simulateQ (fullImplBaseDF sm Δ qep sameHdr Config.h2) oa).run s >>= f2)
        (fun t tL =>
          (simulateQ (fullImplBaseDF sm Δ qep sameHdr (Config.auth t))
            ((simulateQ (simImplDF Δ qep) oa).run (toMirror s))).run
              (toAuth s) >>= fAuth t tL) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s _ hwin
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact closeBySum_of_eq Δ qep (hf12 a s hwin)
  | query_bind q r ih =>
    intro s hwf hwin
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self]
    simp_rw [simulateQ_simDF_query_bind sm Δ qep sameHdr]
    rcases q with n | (((((⟨P, m_msg, r_opt⟩ | ⟨P, m₀, m₁, r_opt⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) |
      ⟨P, c, c'⟩)
    ·
      rw [fullImplBaseDF_inl, fullImplBaseDF_inl, coins_step_h, coins_step_h]
      simp_rw [simImplDF_coins_eq sm Δ qep sameHdr (Config.auth _) n,
        coins_step_auth, bind_assoc, pure_bind]
      exact closeBySum_bind Δ qep (liftM (OracleSpec.query n)) fun u => ih u hwf hwin
    ·
      rw [fullImplBaseDF_inr_inl, fullImplBaseDF_inr_inl,
          transmit_step_h sm Δ qep Config.h1 P m_msg r_opt s hwin,
          transmit_step_h sm Δ qep Config.h2 P m_msg r_opt s hwin]
      simp_rw [simImplDF_oracle_eq sm Δ qep sameHdr (Config.auth _)
        (.inl (.inl (.inl (.inl ⟨P, m_msg, r_opt⟩)))),
        transmit_step_auth sm Δ qep _ P m_msg r_opt s hwin, bind_assoc]
      refine closeBySum_bind Δ qep (samCoins r_opt) fun coins => ?_
      cases hep : s.epMgmt Δ qep P r_opt.isSome with
      | none =>
        simp only [pure_bind]
        exact ih none hwf hwin
      | some s₁ =>
        simp only [pure_bind]
        have ⟨hwf₁, hsends₁⟩ := epMgmt_wf hwf hep
        have hs₁_win : s₁.win = false := (epMgmt_win Δ qep hep).trans hwin
        have hwf' : WFState Δ (s₁.record Δ P (sm.send (s₁.st P) m_msg coins).1
            ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m_msg, (sm.send (s₁.st P) m_msg coins).2⟩ false) :=
          record_wf hΔ hwf₁ rfl rfl rfl hsends₁ (by intro h; cases h)
        exact ih (some (sm.send (s₁.st P) m_msg coins).2) hwf' hs₁_win
    ·
      rw [fullImplBaseDF_inr_inl, fullImplBaseDF_inr_inl,
          chall_step_h sm Δ qep Config.h1 rfl rfl P m₀ m₁ r_opt s hwin,
          chall_step_h sm Δ qep Config.h2 rfl rfl P m₀ m₁ r_opt s hwin]
      simp_rw [simImplDF_oracle_eq sm Δ qep sameHdr (Config.auth _)
        (.inl (.inl (.inl (.inr ⟨P, m₀, m₁, r_opt⟩))))]
      cases hep : s.epMgmt Δ qep P r_opt.isSome with
      | none =>
        simp_rw [chall_step_auth_none sm Δ qep _ P m₀ m₁ r_opt s hep, bind_assoc, pure_bind]
        exact closeBySum_of_samCoins_const Δ qep r_opt (ih none hwf hwin)
      | some s₁ =>
        by_cases hsafe : s₁.safeCh Δ P = true
        · simp_rw [chall_step_auth_safe sm Δ qep _ P m₀ m₁ r_opt s s₁ hwin hep hsafe]
          simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
          refine closeBySum_bind Δ qep (samCoins r_opt) fun coins => ?_
          have ⟨hwf₁, hsends₁⟩ := epMgmt_wf hwf hep
          have hs₁_win : s₁.win = false := (epMgmt_win Δ qep hep).trans hwin
          have hwf' : WFState Δ (s₁.record Δ P
              (sm.send (s₁.st P) (if s.b then m₁ else m₀) coins).1
              ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, if s.b then m₁ else m₀,
                (sm.send (s₁.st P) (if s.b then m₁ else m₀) coins).2⟩ true) :=
            record_wf hΔ hwf₁ rfl rfl rfl hsends₁ (fun _ => hsafe)
          exact ih (some (sm.send (s₁.st P) (if s.b then m₁ else m₀) coins).2) hwf' hs₁_win
        · have hsafeF : s₁.safeCh Δ P = false := Bool.eq_false_iff.mpr hsafe
          simp_rw [chall_step_auth_unsafe sm Δ qep _ P m₀ m₁ r_opt s s₁ hep hsafeF]
          simp only [hsafeF, Bool.not_false, ↓reduceIte, bind_assoc, pure_bind]
          exact closeBySum_of_samCoins_const Δ qep r_opt (ih none hwf hwin)
    ·
      rw [fullImplBaseDF_inr_inl, fullImplBaseDF_inr_inl,
          deliver_step_h sm Δ qep Config.h1 rfl P c s hwin,
          deliver_step_h sm Δ qep Config.h2 rfl P c s hwin]
      simp_rw [simImplDF_oracle_eq sm Δ qep sameHdr (Config.auth _)
        (.inl (.inl (.inr ⟨P, c⟩))),
        deliver_step_auth sm Δ qep (Config.auth _) rfl P c s hwin]
      cases htr : s.inTransit P.other c with
      | none =>
        simp only [pure_bind]
        exact ih none hwf hwin
      | some rec_r =>
        cases hrcv : sm.receive (s.st P) c with
        | none =>
          simp only [pure_bind]
          exact ih (some .rejected) hwf hwin
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          simp only [pure_bind]
          have hwf' : WFState Δ (s.accept P st' rec_r.pos) :=
            accept_wf hwf (inTransit_epoch_le_max Δ hwf htr)
          exact ih (some (.accepted t' i' (if s.chall.contains rec_r.pos then none else some m')))
            hwf' hwin
    ·
      rw [fullImplBaseDF_inr_inl, fullImplBaseDF_inr_inl,
          inject_step_h sm Δ qep Config.h1 P c s hwin,
          inject_step_h sm Δ qep Config.h2 P c s hwin]
      simp_rw [simImplDF_oracle_eq sm Δ qep sameHdr (Config.auth _) (.inl (.inr ⟨P, c⟩)),
        inject_step_auth sm Δ qep (Config.auth _) P c s hwin]
      by_cases hguard : ((s.inTransit P.other c).isSome || !(s.safeInj Δ)) = true
      · simp only [hguard, ↓reduceIte, pure_bind]
        exact ih none hwf hwin
      · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
        have hsafe : s.safeInj Δ = true := by
          revert hguard; cases (s.inTransit P.other c).isSome <;> cases s.safeInj Δ <;> simp
        cases hrcv : sm.receive (s.st P) c with
        | none =>
          simp only [pure_bind]
          exact ih (some .rejected) hwf hwin
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          dsimp only
          by_cases hqep : qep + 1 < t'
          · simp only [hqep, ↓reduceIte, pure_bind]
            exact ih (some .rejected) hwf hwin
          · simp only [hqep, ↓reduceIte]
            by_cases htriv : s.trivial Δ ⟨P.other, t', i'⟩ = true
            · simp only [htriv, ↓reduceIte, pure_bind]
              have hwf' : WFState Δ (s.accept P st' ⟨P.other, t', i'⟩) :=
                accept_wf hwf (pos_epoch_le_of_trivial hwf hsafe htriv)
              exact ih (some (.accepted t' i' (some m'))) hwf' hwin
            · have htrivF : s.trivial Δ ⟨P.other, t', i'⟩ = false := Bool.eq_false_iff.mpr htriv
              simp only [htrivF, Bool.false_eq_true, ↓reduceIte, pure_bind]
              have ht' : t' ∈ Finset.range (qep + 2) := by
                rw [Finset.mem_range]; omega
              have ⟨hok, htL⟩ := authOK_of_nontrivial_inject hΔ hwf htrivF
              refine closeBySum_of_evalDist_eq_one Δ qep ht' htL ?_
              have hinj : (Config.auth (Msg := Msg) t').injectFull t' = true := by
                simp [Config.auth]
              rw [hinj]
              simp only [↓reduceIte]
              refine evalDist_simulateQ_DF_eq_one_of_win_true sm Δ qep sameHdr (Config.auth t')
                ((simulateQ (simImplDF Δ qep) (r (some .rejected))).run (toMirror s))
                (fAuth t' (canon t' s)) rfl ?_
              intro z hz
              apply hfAuth t' (canon t' s) z
              · rw [hz]
              · rw [hz, authOK_with_win, authOK_toAuth]
                exact hok
    ·
      rw [fullImplBaseDF_inr_inl, fullImplBaseDF_inr_inl,
          corr_step_h sm Δ qep Config.h1 P s hwin,
          corr_step_h sm Δ qep Config.h2 P s hwin]
      simp_rw [simImplDF_oracle_eq sm Δ qep sameHdr (Config.auth _) (.inr P),
        corr_step_auth sm Δ qep (Config.auth _) P s hwf hwin]
      by_cases hallow : s.corrAllowed P = true
      · simp only [hallow, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
        exact ih (some (s.st P)) (afterCorr_wf hΔ hwf hallow) hwin
      · have hallowF : s.corrAllowed P = false := Bool.eq_false_iff.mpr hallow
        simp only [hallowF, Bool.not_false, ↓reduceIte, pure_bind]
        exact ih none hwf hwin
    ·
      rw [deliverForge_step_h sm Δ qep sameHdr Config.h1 P c c' s hwin,
          deliverForge_step_h sm Δ qep sameHdr Config.h2 P c c' s hwin]
      simp_rw [deliverForge_step_auth sm Δ qep sameHdr (Config.auth _) P c c' s hwin]
      cases htr : s.inTransit P.other c with
      | none =>
        simp only [pure_bind]
        exact ih none hwf hwin
      | some rec_r =>
        dsimp only
        by_cases hguard :
            ((s.inTransit P.other c').isSome || s.comp.contains rec_r.pos || !sameHdr c c') = true
        · simp only [hguard, ↓reduceIte, pure_bind]
          exact ih none hwf hwin
        · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
          cases hrcv : sm.receive (s.st P) c' with
          | none =>
            simp only [pure_bind]
            exact ih (some .rejected) hwf hwin
          | some res =>
            rcases res with ⟨st', t', i', m'⟩
            dsimp only
            by_cases hqep : (decide (qep + 1 < t') || t' != rec_r.pos.epoch) = true
            · simp only [hqep, ↓reduceIte, pure_bind]
              exact ih (some .rejected) hwf hwin
            · simp only [hqep, Bool.false_eq_true, ↓reduceIte]
              have hqepF : decide (qep + 1 < t') = false ∧ (t' != rec_r.pos.epoch) = false :=
                Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hqep)
              have ht'_le : ¬ (qep + 1 < t') := of_decide_eq_false hqepF.1
              have ht'_eq : t' = rec_r.pos.epoch := by
                simpa [bne_eq_false_iff_eq] using hqepF.2
              by_cases htriv : s.trivial Δ ⟨P.other, t', i'⟩ = true
              · simp only [htriv, ↓reduceIte, pure_bind]
                have hpos_le : (⟨P.other, t', i'⟩ : Pos).epoch ≤
                    max (s.epoch P) (s.epoch P.other) := by
                  dsimp only
                  rw [ht'_eq]
                  exact inTransit_epoch_le_max Δ hwf htr
                have hwf' : WFState Δ (s.accept P st' ⟨P.other, t', i'⟩) :=
                  accept_wf hwf hpos_le
                exact ih (some (.accepted t' i' (some m'))) hwf' hwin
              · have htrivF : s.trivial Δ ⟨P.other, t', i'⟩ = false := Bool.eq_false_iff.mpr htriv
                simp only [htrivF, Bool.false_eq_true, ↓reduceIte, pure_bind]
                have ht' : t' ∈ Finset.range (qep + 2) := by
                  rw [Finset.mem_range]; omega
                have ⟨hok, htL⟩ := authOK_of_nontrivial_inject hΔ hwf htrivF
                refine closeBySum_of_evalDist_eq_one Δ qep ht' htL ?_
                have hinj : (Config.auth (Msg := Msg) t').injectFull t' = true := by
                  simp [Config.auth]
                rw [hinj]
                simp only [↓reduceIte]
                refine evalDist_simulateQ_DF_eq_one_of_win_true sm Δ qep sameHdr (Config.auth t')
                  ((simulateQ (simImplDF Δ qep) (r (some .rejected))).run (toMirror s))
                  (fAuth t' (canon t' s)) rfl ?_
                intro z hz
                apply hfAuth t' (canon t' s) z
                · rw [hz]
                · rw [hz, authOK_with_win, authOK_toAuth]
                  exact hok

theorem forgeGameGuessed_challSimDF_evalDist (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins] (sameHdr : C → C → Bool)
    (tLStar : Option ℕ) (tStar : ℕ) (A : AdversaryDF St Msg Coins C) :
    𝒟[forgeGameGuessed sm Δ qep sameHdr tLStar tStar (challSimDF Δ qep A)] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => ($ᵗ Key : ProbComp Key) >>= fun k =>
        (simulateQ (fullImplBaseDF sm Δ qep sameHdr (Config.auth tStar))
          ((simulateQ (simImplDF Δ qep) A).run
            (toMirror (initState sm k b)))).run (toAuth (initState sm k b)) >>=
          fun z => pure (z.2.win && authLosingConditionsAvoided Δ tLStar tStar z.2)] := by
  unfold forgeGameGuessed runBaseDF challSimDF
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_bind_swap (γ := Bool)
    ($ᵗ Bool : ProbComp Bool) ($ᵗ Key : ProbComp Key)]
  refine congrArg evalDist (congrArg (($ᵗ Key : ProbComp Key) >>= ·) (funext fun k => ?_))
  simp only [StateT.run', map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
    simulateQ_bind, StateT.run_bind]
  rw [simulateQ_fullImplBaseDF_liftM_run]
  simp only [bind_assoc, pure_bind]
  refine congrArg (($ᵗ Bool : ProbComp Bool) >>= ·) (funext fun b => ?_)
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, toMirror_initState, toAuth_initState]
  rfl

theorem forgeGameWin_le_sum (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins] (sameHdr : C → C → Bool)
    (hΔ : 0 < Δ) (B : AdversaryDF St Msg Coins C) :
    𝒟[forgeGameWin sm Δ qep sameHdr B] {true} ≤
      ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
        forgeGuessedAdvantage sm Δ qep sameHdr tL t (challSimDF Δ qep B) := by
  let f1 : Bool × GameState St Msg C → ProbComp Bool := fun z => pure z.2.win
  let f2 : Bool × GameState St Msg C → ProbComp Bool := fun _ => pure false
  let fAuth (t : ℕ) (tL : Option ℕ) :
      (Bool × Mirror Msg C) × GameState St Msg C → ProbComp Bool :=
    fun z => pure (z.2.win && authLosingConditionsAvoided Δ tL t z.2)
  have hclose : CloseBySum Δ qep
      (forgeGameWin sm Δ qep sameHdr B)
      (($ᵗ Bool : ProbComp Bool) >>= fun b => ($ᵗ Key : ProbComp Key) >>= fun k =>
        (simulateQ (fullImplBaseDF sm Δ qep sameHdr Config.h2) B).run
          (initState sm k b) >>= f2)
      (fun t tL =>
        ($ᵗ Bool : ProbComp Bool) >>= fun b => ($ᵗ Key : ProbComp Key) >>= fun k =>
          (simulateQ (fullImplBaseDF sm Δ qep sameHdr (Config.auth t))
            ((simulateQ (simImplDF Δ qep) B).run
              (toMirror (initState sm k b)))).run
            (toAuth (initState sm k b)) >>= fAuth t tL) := by
    unfold forgeGameWin runBaseDF
    simp only [bind_assoc]
    refine closeBySum_bind Δ qep ($ᵗ Bool : ProbComp Bool) fun b =>
      closeBySum_bind Δ qep ($ᵗ Key : ProbComp Key) fun k => ?_
    exact closeBySum_simulateQ_DF sm Δ qep sameHdr hΔ B f1 f2 fAuth
      (fun _ _ hwin => by simp [f1, f2, hwin])
      (fun t tL z hwin hok => by simp [fAuth, hwin, hok])
      (wfState_init sm Δ k b) rfl
  have htr := (hclose {true}).1
  dsimp only [fAuth] at htr
  simp_rw [← forgeGameGuessed_challSimDF_evalDist sm Δ qep sameHdr _ _ B] at htr
  have hzero :
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => ($ᵗ Key : ProbComp Key) >>= fun k =>
        (simulateQ (fullImplBaseDF sm Δ qep sameHdr Config.h2) B).run
          (initState sm k b) >>= f2] {true} = 0 := by
    dsimp only [f2]
    rw [evalDist_bind_congr ($ᵗ Bool) _ (fun _ => pure false) fun b => by
      rw [evalDist_bind_congr ($ᵗ Key) _ (fun _ => pure false) fun k =>
        OracleComp.evalDist_bind_const _ _]
      exact OracleComp.evalDist_bind_const _ _]
    rw [OracleComp.evalDist_bind_const]
    simp
  rw [hzero, zero_add] at htr
  exact htr

/-- Bounds `forgeAdvantage` by summing `forgeGuessedAdvantage` on `challSimDF Δ qep B` over all
target epochs and admissible last-leak guesses. -/
theorem forgeGame_le_sum (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Key] [SampleableType Coins] (sameHdr : C → C → Bool)
    (hΔ : 0 < Δ) (B : AdversaryDF St Msg Coins C) :
    forgeAdvantage sm Δ qep sameHdr B ≤
      ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
        forgeGuessedAdvantage sm Δ qep sameHdr tL t (challSimDF Δ qep B) :=
  (forgeGame_le_forgeGameWin sm Δ qep sameHdr B).trans
    (forgeGameWin_le_sum sm Δ qep sameHdr hΔ B)

private theorem card_targetsL_le_df {Δ n t : ℕ} (hΔ : 0 < Δ) (ht : t < n) :
    (admissibleLastLeakGuesses Δ t).card ≤ n := by
  unfold admissibleLastLeakGuesses
  refine (Finset.card_insert_le _ _).trans ?_
  have h := Finset.card_image_le (s := Finset.range (t + 1 - Δ)) (f := (some : ℕ → Option ℕ))
  simp only [Finset.card_range] at h
  omega

end GamesDF

/-! ## Triviality of in-transit records -/

section BoundaryA

theorem inTransit_mem_trans {St Msg C : Type} [DecidableEq C]
    {s : GameState St Msg C} {Q : Party} {c : C} {r : Record Msg C}
    (h : s.inTransit Q c = some r) :
    r ∈ s.trans ∧ r.pos.sender = Q ∧ r.ct = c := by
  unfold GameState.inTransit at h
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  exact ⟨hmem, hp.1, hp.2⟩

theorem trans_any_pos_eq_true_of_inTransit {St Msg C : Type} [DecidableEq C]
    {s : GameState St Msg C} {Q : Party} {c : C} {r : Record Msg C}
    (h : s.inTransit Q c = some r) :
    s.trans.any (fun r' => r'.pos == r.pos) = true :=
  List.any_eq_true.mpr ⟨r, (inTransit_mem_trans h).1, by simp⟩

theorem trivial_eq_contains_comp_of_inTransit {St Msg C : Type} [DecidableEq C]
    (Δ : ℕ) {s : GameState St Msg C} {Q : Party} {c : C} {r : Record Msg C}
    (h : s.inTransit Q c = some r) :
    s.trivial Δ r.pos = s.comp.contains r.pos := by
  unfold GameState.trivial
  rw [trans_any_pos_eq_true_of_inTransit h]
  simp

theorem trivial_false_of_inTransit_uncomp {St Msg C : Type} [DecidableEq C]
    (Δ : ℕ) {s : GameState St Msg C} {Q : Party} {c : C} {r : Record Msg C}
    (h : s.inTransit Q c = some r) (hcomp : s.comp.contains r.pos = false) :
    s.trivial Δ r.pos = false := by
  rw [trivial_eq_contains_comp_of_inTransit Δ h, hcomp]

theorem deliverForgeImpl_eq_of_inTransit_uncomp {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (sameHdr : C → C → Bool) (cfg : Config Msg)
    (s : GameStateDF St Msg C) (P : Party) (c c' : C) (r : Record Msg C)
    (st' : St) (t' i' : ℕ) (m' : Msg)
    (hnwin : s.forgeWin = false) (hbwin : s.base.win = false)
    (htr : s.base.inTransit P.other c = some r)
    (htr' : (s.base.inTransit P.other c').isSome = false)
    (hcomp : s.base.comp.contains r.pos = false) (hhdr : sameHdr c c' = true)
    (hrec : sm.receive (s.base.st P) c' = some (st', t', i', m'))
    (hqep : ¬ qep + 1 < t') (hrpos : r.pos = ⟨P.other, t', i'⟩)
    (hcfg : cfg.injectFull t' = true) :
    (deliverForgeImpl sm Δ qep sameHdr cfg (P, c, c')).run s =
      pure (some .rejected,
        { s with base := { s.base with win := true }
                 forgeWin := true
                 forgeEpoch := some t' }) := by
  have htriv : s.base.trivial Δ ⟨P.other, t', i'⟩ = false := by
    rw [← hrpos]
    exact trivial_false_of_inTransit_uncomp Δ htr hcomp
  have hmem_f : r.pos ∉ s.base.comp := by simpa using hcomp
  have hepoch_eq : r.pos.epoch = t' := by rw [hrpos]
  unfold deliverForgeImpl
  simp [hnwin, hbwin, htr, htr', hmem_f, hhdr, hrec, hqep, hepoch_eq, htriv, hcfg]

end BoundaryA

end CryptoGames.SM.Construction.DeliverForge
