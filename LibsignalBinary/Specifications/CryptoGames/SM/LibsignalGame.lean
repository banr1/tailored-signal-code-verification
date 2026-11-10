/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.Game

/-!
# The SM security game with receive coins and the R1 restriction (libsignal headline game)

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use every
definition in this file: read them. The theorems here are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Variant of the ACD19 Fig. 2 SM security game (`SM/Game.lean`, including DEV-SM1 to DEV-SM10; see
`FSAEAD/PubDefs.lean` for DEV-LS13) adapting ACD19 §5.2 to libsignal's eager `dh_ratchet_step`:
`receive` takes honest coins (`SMSchemeR`, DEV-LS1), `ConfigR` adds the R1 window restriction
(`inWindow`, DEV-LS2) and send/corruption/injection admissibility filters (DEV-LS3, DEV-LS4,
DEV-LS5), and `configR1` instantiates Appendix A's hybrid `H1` without an in-game correctness win
(DEV-LS6; standalone bounded-receiver correctness and advantages live in
`Computational/Proofs/CryptoGames/SM/LibsignalGameProofDefs.lean`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames

/-- SM scheme whose receive algorithm takes honest coins `RCoins` (libsignal's eager ratchet step;
see DEV-SM16).

**DEV-LS1 (libsignal): receive takes coins, and they are always honest.** ACD19 Fig. 8 draws next-epoch
CKA randomness in `Send`, whereas libsignal draws `P`'s next ratchet key pair during `receive`
(`dh_ratchet_step`; ACD19 §5.2). `deliverR` and `injectR` sample `RCoins` uniformly, so randomness
compromise covers send coins only. -/
structure SMSchemeR (Key St Msg Coins RCoins C : Type) where
  /-- `Init-A`. -/
  initA : Key → St
  /-- `Init-B`. -/
  initB : Key → St
  /-- `Send(s, m; r)`. -/
  send : St → Msg → Coins → St × C
  /-- `Rcv(s, c; rc)`: returns `(s', t, i, m)` on acceptance, or `none` on rejection. -/
  receive : St → C → RCoins → Option (St × ℕ × ℕ × Msg)

namespace SMSchemeR

variable {Key St Msg Coins RCoins C : Type}

/-- Send projection as an `SMScheme` (`receive` and `maxSkip` unused), allowing `transmitImpl`,
`challImpl`, and `initState` from `SM/Game.lean` to be reused verbatim. -/
def sendPart (sm : SMSchemeR Key St Msg Coins RCoins C) : SMScheme Key St Msg Coins C :=
  { initA := sm.initA, initB := sm.initB, send := sm.send, receive := fun _ _ => none,
    maxSkip := 0 }

end SMSchemeR

namespace SM

variable {Key St Msg Coins RCoins C : Type}

/-- R-game configuration extending `Config` (`SM/Game.lean`) with the R1 window flag, the `deliver`
correctness predicate `must`, and admissibility filters `sendOK`, `corrOK`, and `injOK`. -/
structure ConfigR (St Msg C : Type) where
  /-- Underlying `SM/Game.lean` configuration (`deliverWin`, `injectFull`, `challAllowedIn`,
  `challMsg`). -/
  base : Config Msg
  /-- R1 flag: refuse `corr-P` while `P` is inside its window (`inWindow`). -/
  r1 : Bool
  /-- Correctness predicate checked by `deliverR` when `base.deliverWin` holds. -/
  must : GameState St Msg C → Party → Record Msg C → Bool
  /-- Pre-`ep-mgmt` admissibility check for `transmit-P` and `chall-P`. -/
  sendOK : GameState St Msg C → Party → Bool := fun _ _ => true
  /-- Additional admissibility check for `corr-P` beyond `corrAllowed` and R1. -/
  corrOK : GameState St Msg C → Party → Bool := fun _ _ => true
  /-- Ciphertext admissibility check for `inject-P(c)` (e.g. valid curve point, DEV-LS5). -/
  injOK : C → Bool := fun _ => true

/-- Whether `P` is inside its eager-ratchet window (`!(P.sendsIn (s.epoch P))`, including `A` at
initialization).

**DEV-LS2 (libsignal): no corruption inside the window.** Under `r1`, `corr-P` is refused after `P`
accepts a new receiving epoch until `P`'s next send, when libsignal's state already holds `P`'s next
sending key and root key (which ACD19 Fig. 8 defers to `Send`; §5.2). -/
def inWindow (s : GameState St Msg C) (P : Party) : Bool := !(P.sendsIn (s.epoch P))

section Oracles

variable (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
  [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]

local notation "GameM" => StateT (GameState St Msg C) ProbComp

/-- `deliver-P(c)` sampling fresh receive coins `RCoins` (DEV-LS1, DEV-SM4) and checking `cfg.must`. -/
def deliverR : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) GameM :=
  fun ⟨P, c⟩ => do
    let s ← get
    if s.win then return none
    match s.inTransit P.other c with
    | none => return none
    | some r =>
      let rc ← ($ᵗ RCoins : ProbComp RCoins)
      let must := cfg.base.deliverWin && cfg.must s P r
      match sm.receive (s.st P) c rc with
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

/-- `inject-P(c)` sampling fresh receive coins `RCoins` and requiring `cfg.injOK c` (DEV-LS1,
DEV-LS5, DEV-SM2, DEV-SM4, DEV-SM7). -/
def injectR : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) GameM :=
  fun ⟨P, c⟩ => do
    let s ← get
    if s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c) then return none
    let rc ← ($ᵗ RCoins : ProbComp RCoins)
    match sm.receive (s.st P) c rc with
    | none => return some .rejected
    | some (st', t', i', m') =>
      if qep + 1 < t' then return some .rejected
      let pos : Pos := ⟨P.other, t', i'⟩
      if s.trivial Δ pos then
        set (s.accept P st' pos)
        return some (.accepted t' i' (some m'))
      else
        if cfg.base.injectFull t' then set { s with win := true }
        return some .rejected

/-- `corr-P` refusing queries inside the R1 window (`cfg.r1 && inWindow s P`, DEV-LS2) or failing
`cfg.corrOK` (DEV-LS4), in addition to `corrAllowed` (DEV-SM6). -/
def corrR : QueryImpl (Party →ₒ Option St) GameM := fun P => do
  let s ← get
  if s.win || !(s.corrAllowed P) || (cfg.r1 && inWindow s P) || !(cfg.corrOK s P) then
    return none
  set (s.afterCorr P)
  return some (s.st P)

/-- `transmit-P` gated by `cfg.sendOK s P` before `ep-mgmt` (DEV-LS3, DEV-SM1, DEV-SM2). -/
def transmitR : QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) GameM :=
  fun x => do
    let s ← get
    if !(cfg.sendOK s x.1) then return none
    transmitImpl sm.sendPart Δ qep x

/-- `chall-P` gated by `cfg.sendOK s P` before `ep-mgmt` (DEV-LS3, DEV-SM1, DEV-SM8). -/
def challR : QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) GameM :=
  fun x => do
    let s ← get
    if !(cfg.sendOK s x.1) then return none
    challImpl sm.sendPart Δ qep cfg.base x

/-- Combined oracle implementation for `SM.spec` in the R-game. -/
def oracleImplR : QueryImpl (spec St Msg Coins C) GameM :=
  transmitR sm Δ qep cfg + challR sm Δ qep cfg + deliverR sm cfg
    + injectR sm Δ qep cfg + (corrR cfg : QueryImpl _ GameM)

end Oracles

section Game

variable (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ)
  [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
  [SampleableType RCoins]

/-- Execute adversary `A` in R-game configuration `cfg` with challenge bit `b`. -/
def runR (cfg : ConfigR St Msg C) (b : Bool) (A : Adversary St Msg Coins C) :
    ProbComp (Bool × GameState St Msg C) := do
  let k ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) ProbComp) + oracleImplR sm Δ qep cfg
  (simulateQ impl A).run (initState sm.sendPart k b)

/-- Hidden-bit R-game: the adversary wins by guessing `b` or setting `win`. -/
def gameR (cfg : ConfigR St Msg C) (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', s) ← runR sm Δ qep cfg b A
  return (b == b' || s.win)

/-- Send filter forbidding `B` from sending in epoch `0`.

**DEV-LS3 (libsignal): Bob never sends in epoch 0.** libsignal's epoch-0 header carries Bob's signed
pre-key public key, which is secret in the model (DEV-LS22); in libsignal's public API Bob's session
is created inside `message_decrypt_prekey` after decrypting Alice's epoch-1 message
(`session_management.rs:224-289`). -/
def noBobSendInEpoch0 (s : GameState St Msg C) (P : Party) : Bool := !(P == .B && s.epoch .B == 0)

/-- Corruption filter forbidding `corr-A` while `epoch A < 10` (`2 · MAX_RECEIVER_CHAINS`).

**DEV-LS4 (formalization): no corruption of Alice before epoch 10.** Until Alice accepts 5 new
receiving epochs, her state may still retain the receiver chain for Bob's signed pre-key, whose
public key is unknown to the reduction (DEV-LS22). -/
def noAliceCorrWhileAliceBelowEpoch10 (s : GameState St Msg C) (P : Party) : Bool := !(P == .A && decide (s.epoch .A < 10))

/-- Headline R1 configuration: hybrid `H1` (`Config.h1`) with `r1 = true`, `noBobSendInEpoch0`, and
`noAliceCorrWhileAliceBelowEpoch10`.

**DEV-LS6 (formalization): the game is ACD19 App. A's hybrid H1; correctness is proved
separately.** Security is stated in `Config.h1` (privacy and authenticity, without an in-game
`deliver` correctness win); bounded-window correctness (DEV-SM5, DEV-LS10) is proved separately in
`Corr.libsignal_corr` and `libsignal_corr_proto`. -/
def configR1 : ConfigR St Msg C :=
  { base := Config.h1, r1 := true, must := fun _ _ _ => false, sendOK := noBobSendInEpoch0,
    corrOK := noAliceCorrWhileAliceBelowEpoch10 }

end Game

end SM

end CryptoGames
