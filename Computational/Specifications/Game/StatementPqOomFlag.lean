/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Control.Monad.Writer
public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame

/-!
# Monadic lifting and SM game oracles for shared CLI / `WriterT` execution

**Trusted: the statement.** Defines the monadic secure-messaging scheme `SMSchemeRM` and its
R-game oracle handler `oracleImplRM` over `[Monad M] [MonadLiftT ProbComp M]`. `StatementPq.lean`
instantiates `M := ProbComp` for `cliPqExp`, and `StatementPqOomGame.lean` instantiates
`M := WriterT (List Inputs) ProbComp` for the input-logged game `cliPqxdhExpFlagged`; both share
one driver and avoid classical `decide` inside `ProbComp`. See
`Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false
open OracleComp OracleSpec

namespace CryptoVerification.E2E

open CryptoGames

/-- Lift a `StateT σ m` computation along `[MonadLiftT m n]` (definitionally `id` at `m = n`). -/
def liftStateT {σ : Type} {m n : Type → Type} [MonadLiftT m n] {α : Type}
    (x : StateT σ m α) : StateT σ n α :=
  fun s => liftM (x s)

/-- Lift an oracle handler on `StateT σ₁ (StateT σ₂ m)` along `[MonadLiftT m n]` (definitionally
`id` at `m = n`). -/
def liftQueryImplStateT2 {ι σ₁ σ₂ : Type} {spec : OracleSpec ι} {m n : Type → Type}
    [MonadLiftT m n] (h : QueryImpl spec (StateT σ₁ (StateT σ₂ m))) :
    QueryImpl spec (StateT σ₁ (StateT σ₂ n)) :=
  fun q s₁ s₂ => liftM (h q s₁ s₂)

/-- Secure-messaging scheme with receive coins (`SMSchemeR`, DEV-LS1) whose `send` and `receive`
run in a monad `M`. -/
structure SMSchemeRM (M : Type → Type) (Key St Msg Coins RCoins C : Type) where
  initA : Key → St
  initB : Key → St
  send : St → Msg → Coins → M (St × C)
  /-- Returns the updated state, epoch, message index, and plaintext, or `none` on rejection. -/
  receive : St → C → RCoins → M (Option (St × ℕ × ℕ × Msg))

/-- Initial `SM.GameState` for key `k` and challenge bit `b`. -/
def SMSchemeRM.initState {M : Type → Type} {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeRM M Key St Msg Coins RCoins C) (k : Key) (b : Bool) : SM.GameState St Msg C :=
  { st := fun P => match P with
      | .A => sm.initA k
      | .B => sm.initB k,
    b }

section Oracles

variable {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
  {Key St Msg Coins RCoins C : Type}
  [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]

/-- Monadic counterpart of `SM.transmitR` over `StateT (SM.GameState St Msg C) M`. -/
def transmitRM (sm : SMSchemeRM M Key St Msg Coins RCoins C) (Δ qep : ℕ)
    (cfg : SM.ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Option Coins) →ₒ Option C)
      (StateT (SM.GameState St Msg C) M) :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (SM.samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      let out ← StateT.lift (sm.send (s₁.st P) m coins)
      set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
      return some out.2

/-- Monadic counterpart of `SM.challR` over `StateT (SM.GameState St Msg C) M`. -/
def challRM (sm : SMSchemeRM M Key St Msg Coins RCoins C) (Δ qep : ℕ)
    (cfg : SM.ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C)
      (StateT (SM.GameState St Msg C) M) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (SM.samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
      let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
      let out ← StateT.lift (sm.send (s₁.st P) m coins)
      set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
      return some out.2

/-- Monadic counterpart of `SM.deliverR` over `StateT (SM.GameState St Msg C) M`. -/
def deliverRM (sm : SMSchemeRM M Key St Msg Coins RCoins C)
    (cfg : SM.ConfigR St Msg C) :
    QueryImpl ((Party × C) →ₒ Option (SM.RecvResult Msg))
      (StateT (SM.GameState St Msg C) M) :=
  fun ⟨P, c⟩ => do
    let s ← get
    if s.win then return none
    match s.inTransit P.other c with
    | none => return none
    | some r =>
      let rc ← StateT.lift (liftM ($ᵗ RCoins : ProbComp RCoins))
      let must := cfg.base.deliverWin && cfg.must s P r
      match ← StateT.lift (sm.receive (s.st P) c rc) with
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

/-- Monadic counterpart of `SM.injectR` over `StateT (SM.GameState St Msg C) M`. -/
def injectRM (sm : SMSchemeRM M Key St Msg Coins RCoins C) (Δ qep : ℕ)
    (cfg : SM.ConfigR St Msg C) :
    QueryImpl ((Party × C) →ₒ Option (SM.RecvResult Msg))
      (StateT (SM.GameState St Msg C) M) :=
  fun ⟨P, c⟩ => do
    let s ← get
    if s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c) then
      return none
    let rc ← StateT.lift (liftM ($ᵗ RCoins : ProbComp RCoins))
    match ← StateT.lift (sm.receive (s.st P) c rc) with
    | none => return some .rejected
    | some (st', t', i', m') =>
      if qep + 1 < t' then return some .rejected
      let pos : SM.Pos := ⟨P.other, t', i'⟩
      if s.trivial Δ pos then
        set (s.accept P st' pos)
        return some (.accepted t' i' (some m'))
      else
        if cfg.base.injectFull t' then set { s with win := true }
        return some .rejected

/-- Combined R-game oracle handler (`SM.oracleImplR`) over `StateT (SM.GameState St Msg C) M`. -/
def oracleImplRM (sm : SMSchemeRM M Key St Msg Coins RCoins C) (Δ qep : ℕ)
    (cfg : SM.ConfigR St Msg C) :
    QueryImpl (SM.spec St Msg Coins C) (StateT (SM.GameState St Msg C) M) :=
  transmitRM sm Δ qep cfg + challRM sm Δ qep cfg + deliverRM sm cfg +
    injectRM sm Δ qep cfg +
    ((fun P => liftStateT (SM.corrR cfg P)) :
      QueryImpl (Party →ₒ Option St) (StateT (SM.GameState St Msg C) M))

end Oracles

/-- Monadic counterpart of `cliOracleImplR`: runs the R-game oracles on internal party state `St'`
while projecting `corr-P` leakage along `proj : St' → St` (DEV-CLI18). -/
def cliOracleImplRM {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    {Key St' St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (proj : St' → St) (sm : SMSchemeRM M Key St' Msg Coins RCoins C) (Δ qep : ℕ)
    (cfg : SM.ConfigR St' Msg C) :
    QueryImpl (SM.spec St Msg Coins C) (StateT (SM.GameState St' Msg C) M) :=
  transmitRM sm Δ qep cfg + challRM sm Δ qep cfg + deliverRM sm cfg +
    injectRM sm Δ qep cfg +
    ((fun P => liftStateT (Option.map proj <$> SM.corrR cfg P)) :
      QueryImpl (Party →ₒ Option St) (StateT (SM.GameState St' Msg C) M))

end CryptoVerification.E2E
