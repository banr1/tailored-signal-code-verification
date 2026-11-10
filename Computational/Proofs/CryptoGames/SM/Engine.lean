/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.Construction
public import Computational.Proofs.CryptoGames.SM.GameProofDefs

/-!
# Simulation engine for the reductions of Theorems 8 and 12

**Checked by Lean.** Factors out the shared Fig. 2 / Fig. 8 simulation used by the CKA, PRF-PRNG, and FS-AEAD reductions of ACD19 §5.3. Reductions supply primitive `Hooks` over virtual party states and bookkeeping `HS`, while the engine aborts doomed runs that violate the guessed `(t*_L, t*)` window (DEV-SM9).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM.Engine

open Construction

set_option linter.unusedSectionVars false

variable {Γ T Sig SS RS M E CCoins : Type} {Γv Sv SSv RSv HS : Type} {ι : Type}
  {tspec : OracleSpec.{0, 0} ι}

abbrev VP (Γv T Sv SSv RSv : Type) := PartyState Γv T Sv SSv RSv

abbrev Ctx (Γv T Sv SSv RSv M E : Type) :=
  GameState (PartyState Γv T Sv SSv RSv) M (Header T × E)

abbrev TComp (tspec : OracleSpec.{0, 0} ι) := OracleComp (unifSpec + tspec)

abbrev HM (tspec : OracleSpec.{0, 0} ι) (HS : Type) := StateT HS (TComp tspec)

/-- Primitive reduction hooks over the virtual game state; returning `none` aborts the simulation. -/
structure Hooks (tspec : OracleSpec.{0, 0} ι) (HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type)
    where
  /-- Starts sending epoch `t` for `P` from CKA state `γ`, root state `σ`, and coins `r`. -/
  startSend : Ctx Γv T Sv SSv RSv M E → Party → ℕ → Γv → Sv → Option CCoins →
    HM tspec HS (Option (Γv × T × Sv × SSv))
  /-- Starts receiving epoch `t` for `P` on CKA message `T'` (inner `none` rejects). -/
  startRecv : Ctx Γv T Sv SSv RSv M E → Party → ℕ → Γv → Sv → T →
    HM tspec HS (Option (Option (Γv × Sv × RSv)))
  /-- Sends `m` in epoch `t` under header `h` (`pair = some (m₀, m₁)` for a challenge). -/
  fsSend : Ctx Γv T Sv SSv RSv M E → Party → ℕ → SSv → Header T → M → Option (M × M) →
    HM tspec HS (Option (SSv × E))
  /-- Receives `(h, e)` in epoch `t` (`rec = some r` on `deliver`; inner `none` rejects). -/
  fsRecv : Ctx Γv T Sv SSv RSv M E → Party → ℕ → RSv → Header T → E →
    Option (Record M (Header T × E)) → HM tspec HS (Option (Option (RSv × ℕ × M)))
  /-- Commits an accepted receive by `P` from `old` to `new`. -/
  commit : Ctx Γv T Sv SSv RSv M E → Party → VP Γv T Sv SSv RSv → VP Γv T Sv SSv RSv →
    HM tspec HS (Option (VP Γv T Sv SSv RSv))
  /-- Reconstructs the real state of `P` on corruption. -/
  reveal : Ctx Γv T Sv SSv RSv M E → Party → VP Γv T Sv SSv RSv →
    HM tspec HS (Option (PartyState Γ T Sig SS RS))

section Fig8

variable [Inhabited E]
  (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)

/-- Fig. 8 `Send` over virtual party states using `hk`. -/
def vSend (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s : VP Γv T Sv SSv RSv) (m : M)
    (pair : Option (M × M)) (r : Option CCoins) :
    HM tspec HS (Option (VP Γv T Sv SSv RSv × (Header T × E))) := do
  let s₁? : Option (VP Γv T Sv SSv RSv) ←
    if s.id.sendsIn (s.tcur + 1) then do
      match ← hk.startSend ctx P (s.tcur + 1) s.γ s.root r with
      | none => pure none
      | some (γ', T', σ', ss) =>
        pure (some { s with tcur := s.tcur + 1, γ := γ', curCkaMsg := some T', root := σ',
                            vS := some ss })
    else pure (some s)
  match s₁? with
  | none => return none
  | some s₁ =>
    let h : Header T := (s₁.tcur, s₁.curCkaMsg)
    match s₁.vS with
    | none => return some (s₁, (h, default))
    | some v =>
      match ← hk.fsSend ctx P s₁.tcur v h m pair with
      | none => return none
      | some (v', e) => return some ({ s₁ with vS := some v' }, (h, e))

/-- Fig. 8 `Rcv` over virtual party states using `hk` (outer `none` aborts, inner `none` rejects). -/
def vRecv (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s : VP Γv T Sv SSv RSv)
    (c : Header T × E) (rec : Option (Record M (Header T × E))) :
    HM tspec HS (Option (Option (VP Γv T Sv SSv RSv × ℕ × ℕ × M))) := do
  let t := c.1.1
  if s.id.sendsIn t || s.tcur + 1 < t then return some none
  let s₁? : Option (Option (VP Γv T Sv SSv RSv)) ←
    if t = s.tcur + 1 then
      match c.1.2 with
      | none => pure (some none)
      | some Tn => do
        match ← hk.startRecv ctx P t s.γ s.root Tn with
        | none => pure none
        | some none => pure (some none)
        | some (some (γ', σ', rs)) =>
          pure (some (some { s with tcur := t, γ := γ', root := σ',
                                    vR := Function.update s.vR t (some rs) }))
    else pure (some (some s))
  match s₁? with
  | none => return none
  | some none => return some none
  | some (some s₁) =>
    match s₁.vR t with
    | none => return some none
    | some v =>
      match ← hk.fsRecv ctx P t v c.1 c.2 rec with
      | none => return none
      | some none => return some none
      | some (some (v', i, m)) =>
        return some (some ({ s₁ with vR := Function.update s₁.vR t (some v') }, t, i, m))

end Fig8

/-! ### Doomed runs -/

/-- Target game mode and `(t*_L, t*)` guesses simulated by the engine (DEV-SM9). -/
structure Policy where
  /-- Authenticity (`true`) or privacy (`false`). -/
  auth : Bool
  /-- The guess `t*_L`. -/
  tL : Option ℕ
  /-- The guess `t*`. -/
  tStar : ℕ

namespace Policy

variable (π : Policy) {St Msg C : Type}

/-- Checks whether a leak in `g → g'` dooms the `(t*_L, t*)` guess window. -/
def leakDoom (g g' : GameState St Msg C) : Bool :=
  g'.leaks.any (fun l => ltOpt π.tL l && decide (l < π.tStar))
    || (g'.leaks.any (fun l => decide (π.tStar ≤ l))
        && decide (g.epoch (Party.senderOf π.tStar) < π.tStar))

/-- Checks whether corrupting `P` in state `g` dooms the `(t*_L, t*)` guess window. -/
def corrDoom (g : GameState St Msg C) (P : Party) : Bool :=
  P == Party.receiverOf π.tStar &&
    (if π.auth then ltOpt π.tL (g.epoch P)
     else decide (g.epoch P < π.tStar)
       && decide (π.tStar ≤ max (g.epoch .A) (g.epoch .B)))

end Policy

/-! ### Engine oracles -/

/-- Engine state bundling the virtual Fig. 2 game state, reduction bookkeeping, and abort flag. -/
structure EState (VPt M C HS : Type) where
  /-- The (virtual) Fig. 2 game state. -/
  g : GameState VPt M C
  /-- The reduction's bookkeeping. -/
  h : HS
  /-- The simulation was aborted. -/
  abort : Bool := false

abbrev EM (tspec : OracleSpec.{0, 0} ι) (Γv T Sv SSv RSv M E HS : Type) :=
  StateT (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (TComp tspec)

section Oracles

variable [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
  (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
  (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)

local notation "EMt" => EM tspec Γv T Sv SSv RSv M E HS

def liftH {α : Type} (x : HM tspec HS α) : EMt α := fun es => do
  let (a, h') ← x.run es.h
  pure (a, { es with h := h' })

def abortE : EMt Unit := modify fun es => { es with abort := true }

def transmitE : QueryImpl ((Party × M × Option CCoins) →ₒ Option (Header T × E)) EMt :=
  fun ⟨P, m, r⟩ => do
    let es ← get
    if es.abort || es.g.win then return none
    match es.g.epMgmt Δ qep P r.isSome with
    | none => return none
    | some s₁ =>
      if π.leakDoom es.g s₁ then
        abortE
        return none
      match ← liftH (vSend hk s₁ P (s₁.st P) m none r) with
      | none =>
        abortE
        return none
      | some (st', c) =>
        modify fun es =>
          { es with g := s₁.record Δ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ false }
        return some c

def challE : QueryImpl ((Party × M × M × Option CCoins) →ₒ Option (Header T × E)) EMt :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let es ← get
    if es.abort || es.g.win then return none
    match es.g.epMgmt Δ qep P r.isSome with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P)) then return none
      if π.leakDoom es.g s₁ then
        abortE
        return none
      let m := (cfg.challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀)
      match ← liftH (vSend hk s₁ P (s₁.st P) m (some (m₀, m₁)) r) with
      | none =>
        abortE
        return none
      | some (st', c) =>
        modify fun es =>
          { es with g := s₁.record Δ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ true }
        return some c

def commitE (s : Ctx Γv T Sv SSv RSv M E) (P : Party) (old new : VP Γv T Sv SSv RSv) (pos : Pos) :
    EMt (Option (Ctx Γv T Sv SSv RSv M E)) := do
  let s₁ := s.accept P new pos
  match ← liftH (hk.commit s₁ P old new) with
  | none =>
    abortE
    return none
  | some new' => return some { s₁ with st := Function.update s₁.st P new' }

def deliverE : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M)) EMt :=
  fun ⟨P, c⟩ => do
    let es ← get
    if es.abort || es.g.win then return none
    let s := es.g
    match s.inTransit P.other c with
    | none => return none
    | some r =>
      let must := cfg.deliverWin && s.mustBeCorrect maxSkip P r
      match ← liftH (vRecv hk s P (s.st P) c (some r)) with
      | none =>
        abortE
        return none
      | some none =>
        if must then modify fun es => { es with g := { es.g with win := true } }
        return some .rejected
      | some (some (st', t', i', m')) =>
        match ← commitE hk s P (s.st P) st' r.pos with
        | none => return none
        | some s₁ =>
          let bad := must && !(decide ((t', i', m') = (r.pos.epoch, r.pos.idx, r.msg)))
          modify fun es => { es with g := if bad then { s₁ with win := true } else s₁ }
          return some (.accepted t' i' (if s.chall.contains r.pos then none else some m'))

def injectE : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M)) EMt :=
  fun ⟨P, c⟩ => do
    let es ← get
    let s := es.g
    if es.abort || s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) then return none
    match ← liftH (vRecv hk s P (s.st P) c none) with
    | none =>
      abortE
      return none
    | some none => return some .rejected
    | some (some (st', t', i', m')) =>
      if qep + 1 < t' then return some .rejected
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

def corrE : QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS)) EMt := fun P => do
  let es ← get
  if es.abort || es.g.win || !(es.g.corrAllowed P) then return none
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

def coinsE : QueryImpl unifSpec EMt := fun n =>
  StateT.lift (query (spec := unifSpec + tspec) (.inl n))

def implE : QueryImpl (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) EMt :=
  let i₀ : QueryImpl unifSpec EMt := coinsE
  let i₁ : QueryImpl ((Party × M × Option CCoins) →ₒ Option (Header T × E)) EMt :=
    transmitE hk Δ qep π
  let i₂ : QueryImpl ((Party × M × M × Option CCoins) →ₒ Option (Header T × E)) EMt :=
    challE hk Δ qep cfg π
  let i₃ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M)) EMt :=
    deliverE hk maxSkip cfg
  let i₄ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M)) EMt :=
    injectE hk Δ qep cfg
  let i₅ : QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS)) EMt := corrE hk π
  HAdd.hAdd i₀ (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

/-- Runs SM adversary `A` against the engine from initial virtual states built by `init` and hidden bit `b`. -/
def engRun (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (b : Bool) (A : Adversary (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) :
    TComp tspec (Option (Bool × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)) := do
  let (vs, h) ← init.run h₀
  match vs with
  | none => return none
  | some (vA, vB) =>
    let g : Ctx Γv T Sv SSv RSv M E :=
      { st := fun P => match P with
          | .A => vA
          | .B => vB,
        b }
    let res ← (simulateQ (implE hk Δ qep maxSkip cfg π) A).run { g, h }
    return some res

end Oracles

/-! ### Outcomes -/

section Outcomes

variable {VPt M C HS : Type} [DecidableEq M] (Δ : ℕ) (π : Policy)

/-- Authenticity outcome: a non-aborted win avoiding the losing conditions. -/
def authOut (es : EState VPt M C HS) : Bool :=
  !es.abort && es.g.win && authLosingConditionsAvoided Δ π.tL π.tStar es.g

/-- Privacy outcome: `b == b'` on a valid non-aborted run, and a fresh coin otherwise. -/
def privOut (b b' : Bool) (es : EState VPt M C HS) : TComp tspec Bool :=
  if !es.abort && lastLeakGuessAdmissible Δ π.tL π.tStar && canon π.tStar es.g == π.tL then pure (b == b')
  else (liftM ($ᵗ Bool : ProbComp Bool) : TComp tspec Bool)

def privValid (es : EState VPt M C HS) : Bool :=
  !es.abort && lastLeakGuessAdmissible Δ π.tL π.tStar && canon π.tStar es.g == π.tL

end Outcomes

end CryptoGames.SM.Engine
