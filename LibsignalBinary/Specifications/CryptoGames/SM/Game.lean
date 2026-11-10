/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Party
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Secure messaging (SM): syntax and the two-way security game

**Trusted in part.** The theorems of `Computational/Theorems/` use every definition in this file
except `Config.auth` (the authenticity variant of Def. 10): read the others. Everything else here is
checked by Lean. See `Computational/docs/TRUSTED_BASE.md`. They include the scheme syntax
`SMScheme`, the adversary interface `Adversary` and `spec`, the game variants `Config` (`auth`,
`h1`), the game state `GameState` (`initState`, `safeCh`, `safeInj`, `leak`, `epMgmt`, `record`,
`accept`, `trivial`, `corrAllowed`, `afterCorr`), the oracles `transmitImpl` and `challImpl`,
`admissibleLastLeakGuesses`, and `MakesAtMostQueries`.

Syntax and two-way security game of ACD19 §3, Definitions 6–11 and Fig. 2 (Alwen, Coretti, Dodis,
ePrint 2018/1037), together with the simplified game variants of §3.3 and the Appendix A hybrids.
The remaining oracles and proof-side advantage definitions (`deliverImpl`, `injectImpl`, `corrImpl`,
`oracleImpl`, `canon`, `hybridAdvantage`) live in
`Computational/Proofs/CryptoGames/SM/GameProofDefs.lean` (covering DEV-SM1 to DEV-SM10 and DEV-SM16
to DEV-SM19; see `SM/LibsignalGame.lean` for the receive-coins R1 variant).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames

/-- ACD19 Def. 6: secure-messaging scheme with keys `Key`, party states `St`, messages `Msg`,
sender coins `Coins`, and ciphertexts `C`.

**DEV-SM16 (formalization): algorithms with explicit coins.** ACD19 Def. 6 has randomized `Send`
and a `Rcv` outputting `(s', t, i, m)` or `⊥`. Here `send` takes explicit coins and `receive`
returns `Option`, so Def. 7 (A) (rejection leaves state unchanged) holds by construction (DEV-SM4,
DEV-SM17). The scheme also declares its skip window `maxSkip` (DEV-SM5). -/
structure SMScheme (Key St Msg Coins C : Type) where
  /-- `Init-A`: `A`'s initial state from the shared key. -/
  initA : Key → St
  /-- `Init-B`: `B`'s initial state from the shared key. -/
  initB : Key → St
  /-- `Send(s, m; r)`: encrypt `m` with coins `r`, returning the updated state and ciphertext. -/
  send : St → Msg → Coins → St × C
  /-- `Rcv(s, c)`: returns `(s', t, i, m)` on acceptance, or `none` on rejection. -/
  receive : St → C → Option (St × ℕ × ℕ × Msg)
  /-- Receiver skip window: correctness holds up to `maxSkip + 1` beyond the highest accepted index
  in the epoch (DEV-SM5). -/
  maxSkip : ℕ

namespace SM

/-- Outcome of a receive oracle (`Rcv` in ACD19 Fig. 2). -/
inductive RecvResult (Msg : Type) where
  /-- `Rcv` rejected. -/
  | rejected
  /-- `Rcv` accepted at epoch `t`, index `i`; `m = none` masks challenge plaintexts. -/
  | accepted (t i : ℕ) (m : Option Msg)

/-- Position `(sender, epoch, idx)` of a ciphertext in ACD19 Fig. 2. -/
structure Pos where
  sender : Party
  epoch : ℕ
  idx : ℕ
  deriving DecidableEq

/-- In-transit record `(pos, msg, ct)` of ACD19 Fig. 2. -/
structure Record (Msg C : Type) where
  pos : Pos
  msg : Msg
  ct : C

/-- ACD19 Fig. 2 oracle signature (`transmit-P`, `chall-P`, `deliver-P`, `inject-P`, `corr-P`;
`none` indicates a refused query, DEV-SM1). -/
abbrev spec (St Msg Coins C : Type) :=
  ((Party × Msg × Option Coins) →ₒ Option C)
  + ((Party × Msg × Msg × Option Coins) →ₒ Option C)
  + ((Party × C) →ₒ Option (RecvResult Msg))
  + ((Party × C) →ₒ Option (RecvResult Msg))
  + (Party →ₒ Option St)

/-- Computations with uniform sampling plus the ACD19 Fig. 2 oracles. -/
abbrev AdversaryComp (St Msg Coins C : Type) := OracleComp (unifSpec + spec St Msg Coins C)

/-- SM adversary outputting a hidden-bit guess (ACD19 Def. 8). -/
abbrev Adversary (St Msg Coins C : Type) := AdversaryComp St Msg Coins C Bool

variable {Key St Msg Coins C : Type}

section Queries

local notation "Comp" => AdversaryComp St Msg Coins C

def transmitQuery (P : Party) (m : Msg) (r : Option Coins) : Comp (Option C) :=
  query (spec := unifSpec + spec St Msg Coins C) (.inr (.inl (.inl (.inl (.inl (P, m, r))))))

def challQuery (P : Party) (m₀ m₁ : Msg) (r : Option Coins) : Comp (Option C) :=
  query (spec := unifSpec + spec St Msg Coins C) (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))

def deliverQuery (P : Party) (c : C) : Comp (Option (RecvResult Msg)) :=
  query (spec := unifSpec + spec St Msg Coins C) (.inr (.inl (.inl (.inr (P, c)))))

def injectQuery (P : Party) (c : C) : Comp (Option (RecvResult Msg)) :=
  query (spec := unifSpec + spec St Msg Coins C) (.inr (.inl (.inr (P, c))))

def corrQuery (P : Party) : Comp (Option St) :=
  query (spec := unifSpec + spec St Msg Coins C) (.inr (.inr P))

end Queries

/-- Configuration selecting a variant of the ACD19 Fig. 2 game (§3.3 and App. A). -/
structure Config (Msg : Type) where
  /-- Whether `deliver` sets `win` on a correctness violation. -/
  deliverWin : Bool
  /-- Whether `inject` sets `win` on a non-trivial forgery in epoch `t` (versus reduced `inject`). -/
  injectFull : ℕ → Bool
  /-- Whether `chall-P` is permitted when `P` sends in epoch `t`. -/
  challAllowedIn : ℕ → Bool
  /-- Optional fixed plaintext encrypted by challenges in epoch `t` (for hybrids `H3,i`). -/
  challMsg : ℕ → Option Msg

namespace Config

/-- Authenticity game for target epoch `t*` (ACD19 §3.3, Def. 10): no challenges, no correctness
win, and reduced injections outside epoch `t*`. -/
def auth (tStar : ℕ) : Config Msg :=
  { deliverWin := false, injectFull := fun t => t == tStar, challAllowedIn := fun _ => false,
    challMsg := fun _ => none }

/-- Hybrid `H1` (ACD19 App. A.1): Fig. 2 game without the correctness win. -/
def h1 : Config Msg :=
  { deliverWin := false, injectFull := fun _ => true, challAllowedIn := fun _ => true,
    challMsg := fun _ => none }

end Config

/-- Healing predicate `tL + Δ ≤ t`, with `tL = none` representing `−∞`. -/
def healedBy (tL : Option ℕ) (Δ t : ℕ) : Bool :=
  match tL with
  | none => true
  | some l => decide (l + Δ ≤ t)

/-- `max(tL, t)` with `tL = none` representing `−∞`. -/
def maxOpt (tL : Option ℕ) (t : ℕ) : ℕ :=
  match tL with
  | none => t
  | some l => max l t

/-- State of the ACD19 Fig. 2 security game. -/
structure GameState (St Msg C : Type) where
  /-- Per-party protocol states (`s_A`, `s_B`). -/
  st : Party → St
  /-- Per-party epoch counters (`t_A`, `t_B`). -/
  epoch : Party → ℕ := fun _ => 0
  /-- Per-party message index counters (`i_A`, `i_B`) in the current epoch. -/
  idx : Party → ℕ := fun _ => 0
  /-- Last leak epoch `tL` (`none` = `−∞`). -/
  tL : Option ℕ := none
  /-- In-transit records, newest first (`deliver` matches the newest duplicate, matching
  `FSAEAD/Defs.lean`). -/
  trans : List (Record Msg C) := []
  /-- In-transit challenge positions. -/
  chall : List Pos := []
  /-- In-transit compromised positions. -/
  comp : List Pos := []
  /-- Highest 1-based message index accepted by party `P` in epoch `t` (`0` if none; DEV-SM5). -/
  maxAcc : Party → ℕ → ℕ := fun _ _ => 0
  /-- Challenge bit (`true` selects `m₁`; DEV-SM10). -/
  b : Bool
  /-- Whether the adversary has triggered a correctness or authenticity win. -/
  win : Bool := false
  /-- History of `tL` updates, newest first (DEV-SM9). -/
  leaks : List ℕ := []
  /-- History of corruptions `(P, t_P)`, newest first (DEV-SM9). -/
  corrs : List (Party × ℕ) := []

namespace GameState

variable (s : GameState St Msg C) (Δ qep : ℕ)

/-- `safe-ch_P :⇔ t_P ≥ tL + Δ`. -/
def safeCh (P : Party) : Bool := healedBy s.tL Δ (s.epoch P)

/-- `safe-inj :⇔ min(t_A, t_B) ≥ tL + Δ`. -/
def safeInj : Bool := healedBy s.tL Δ (min (s.epoch .A) (s.epoch .B))

/-- Record a leak at epoch `l`: updates `tL ← max(tL, l)` and prepends to `leaks`.

**DEV-SM3 (formalization): `tL` only grows.** ACD19 Fig. 2 assigns `tL ← t_P + 1` in `ep-mgmt` and
`tL ← max(t_A, t_B)` in `corr-P`; taking the maximum with the prior `tL` prevents an earlier-epoch
leak after an accepted injection from lowering `tL`. -/
def leak (l : ℕ) : GameState St Msg C :=
  { s with tL := some (maxOpt s.tL l), leaks := maxOpt s.tL l :: s.leaks }

/-- ACD19 Fig. 2 `ep-mgmt(P, bad)`: advances `P` into a new sending epoch when due (recording a leak
if `bad` coins are used while unhealed) and resets `idx P`, refusing epochs above `qep`.

**DEV-SM2 (formalization): epoch cap `qep`.** `qep` is a game parameter: `ep-mgmt` refuses sending
epochs `> qep` and `inject` rejects ciphertexts for epochs `> qep + 1`, keeping hybrid sums over
`t* ≤ qep + 1` finite (DEV-SM19). -/
def epMgmt (P : Party) (bad : Bool) : Option (GameState St Msg C) :=
  if P.sendsIn (s.epoch P + 1) then
    if qep < s.epoch P + 1 then none
    else
      let s₁ := if bad && !(s.safeCh Δ P) then s.leak (s.epoch P + 1) else s
      some { s₁ with epoch := Function.update s₁.epoch P (s₁.epoch P + 1),
                     idx := Function.update s₁.idx P 0 }
  else if qep < s.epoch P then none
  else some s

/-- ACD19 Fig. 2 `record`: updates `P`'s state and index, adds `r` to `trans`, and marks `r.pos` in
`comp` (if unhealed) and `chall` (if `isChall`). -/
def record (P : Party) (st' : St) (r : Record Msg C) (isChall : Bool) : GameState St Msg C :=
  { s with st := Function.update s.st P st',
           idx := Function.update s.idx P r.pos.idx,
           trans := r :: s.trans,
           comp := if s.safeCh Δ P then s.comp else r.pos :: s.comp,
           chall := if isChall then r.pos :: s.chall else s.chall }

/-- Latest in-transit record from sender `Q` carrying ciphertext `c`, if any. -/
def inTransit [DecidableEq C] (Q : Party) (c : C) : Option (Record Msg C) :=
  s.trans.find? fun r => r.pos.sender == Q && decide (r.ct = c)

/-- ACD19 Fig. 2 `delete`: removes `pos` from `trans`, `chall`, and `comp`. -/
def delete (pos : Pos) : GameState St Msg C :=
  { s with trans := s.trans.filter (fun r => r.pos != pos),
           chall := s.chall.filter (· != pos),
           comp := s.comp.filter (· != pos) }

/-- State transition when `P` accepts a ciphertext at `pos` with new state `st'`. -/
def accept (P : Party) (st' : St) (pos : Pos) : GameState St Msg C :=
  let s₁ := s.delete pos
  { s₁ with st := Function.update s₁.st P st',
            epoch := Function.update s₁.epoch P (max (s₁.epoch P) pos.epoch),
            maxAcc := fun Q t =>
              if Q = P ∧ t = pos.epoch then max (s₁.maxAcc Q t) pos.idx else s₁.maxAcc Q t }

/-- Whether `pos` is trivially forgeable: either in `comp`, or absent from `trans` with an epoch not
yet healed at `tL`.

**DEV-SM7 (formalization): position-based trivial forgeries.** Because old receiving sessions are
retained rather than erased via `FS-Max`/`FS-Stop` (DEV-SM11), positions not in transit from
unhealed epochs (`t < tL + Δ`) are also treated as trivial forgeries. -/
def trivial (pos : Pos) : Bool :=
  s.comp.contains pos || (!(s.trans.any (fun r => r.pos == pos)) && !(healedBy s.tL Δ pos.epoch))

/-- Whether `corr-P` is permitted: neither a challenge nor an uncompromised record from `P.other`
is in transit.

**DEV-SM6 (paper fix): `corr-P` waits for uncompromised records.** ACD19 Fig. 2 blocks `corr-P` only
while a challenge from `P.other` is in transit; here any uncompromised in-transit record from
`P.other` also blocks `corr-P`, matching the FS-AEAD corruption rule needed for Thm 12 / Thm 5
(DEV-FS6; see `Computational/Tests/Deviations/PaperCorrRule.lean`). -/
def corrAllowed (P : Party) : Bool :=
  !(s.chall.any (fun pos => pos.sender == P.other))
    && !(s.trans.any (fun r => r.pos.sender == P.other && !(s.comp.contains r.pos)))

/-- State update for `corr-P`: marks `P.other`'s in-transit records compromised and records a leak
at `max(t_A, t_B)`. -/
def afterCorr (P : Party) : GameState St Msg C :=
  let s₁ : GameState St Msg C :=
    { s with comp := (s.trans.filter (fun r : Record Msg C => r.pos.sender == P.other)).map
                       (fun r : Record Msg C => r.pos) ++ s.comp }
  { s₁.leak (max (s.epoch .A) (s.epoch .B)) with corrs := (P, s.epoch P) :: s.corrs }

end GameState

section Oracles

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg)
  [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]

local notation "GameM" => StateT (GameState St Msg C) ProbComp

/-- ACD19 Fig. 2 `sam-if-nec(r)`: samples fresh coins when `r = none` and flags adversarial coins. -/
def samIfNec (r : Option Coins) : ProbComp (Coins × Bool) :=
  match r with
  | none => do
    let r ← ($ᵗ Coins : ProbComp Coins)
    return (r, false)
  | some r => return (r, true)

/-- ACD19 Fig. 2 `transmit-P(m, r)`. -/
def transmitImpl : QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) GameM :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    if s.win then return none
    let (coins, bad) ← (samIfNec r : ProbComp _)
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      let out := sm.send (s₁.st P) m coins
      set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
      return some out.2

/-- ACD19 Fig. 2 `chall-P(m₀, m₁, r)`: requires `safe-ch_P` after `ep-mgmt` and
`cfg.challAllowedIn t_P`, then encrypts `m_b` (or `cfg.challMsg t_P`).

**DEV-SM8 (formalization): equal lengths are not checked.** `Msg` is a single type with no explicit
`|m₀| = |m₁|` check; fixed-length message types suffer no gap, while variable-length leakage must be
reflected in `Msg`. -/
def challImpl : QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) GameM :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if s.win then return none
    let (coins, bad) ← (samIfNec r : ProbComp _)
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P)) then return none
      let m := (cfg.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
      let out := sm.send (s₁.st P) m coins
      set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
      return some out.2

end Oracles

section Game

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
  [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]

/-- Initial `GameState` from shared key `k` and challenge bit `b` (ACD19 Fig. 2 `init`). -/
def initState (k : Key) (b : Bool) : GameState St Msg C :=
  { st := fun P => match P with
      | .A => sm.initA k
      | .B => sm.initB k,
    b }

/-- Predicate stating that `A` makes at most `q` queries to the Fig. 2 game oracles.

**DEV-SM18 (formalization): running time is not modelled.** Query count `q` and epoch bound `qep`
(DEV-SM2) are tracked, whereas adversaries are arbitrary `OracleComp`s and theorems state explicit
reductions rather than time bounds. -/
def MakesAtMostQueries (A : Adversary St Msg Coins C) (q : ℕ) : Prop :=
  A.IsQueryBoundP (· matches .inr _) q

/-- Admissible last-leak guesses `t*_L ∈ {−∞, 0, …, t* − Δ}` for target epoch `t*`.

**DEV-SM19 (paper fix): the guesses include `t*_L = −∞` and epoch `0`.** ACD19 App. A writes
`t* ∈ [q_ep]` and `t*_L ∈ [t* − Δ_SM]` with `H3,0 = H2`, omitting `t*_L = −∞` (no leak) and epoch
`0` (where `B` sends); here `t*` ranges over `{0, …, qep + 1}`, `admissibleLastLeakGuesses` includes
`none` and `0`, and `H3,i` replaces epochs `< i`. -/
def admissibleLastLeakGuesses (tStar : ℕ) : Finset (Option ℕ) :=
  insert none ((Finset.range (tStar + 1 - Δ)).image some)

end Game

end SM

end CryptoGames
