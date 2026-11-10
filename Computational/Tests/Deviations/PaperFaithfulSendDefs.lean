/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.CKA.Defs
public import Computational.Proofs.CryptoGames.CKA.CKAProofDefs

/-!
# Paper-Faithful CKA Game Definitions

**Checked by Lean.** Defines the paper-faithful continuous-key-agreement game (`gamePaper`,
`advantagePaper`) from Alwen, Coretti, and Dodis (ePrint 2018/1037, Fig. 3), where `send-P` is
permitted in the challenge epoch `t*`, unlike `CKA.game` (`DEV-CKA3`). Also defines the adversary
conversion `fromPaperRed`, which tracks shadow epoch counters and aborts with a uniform bit if the
adversary queries plain `send-P` in epoch `t*` (where no challenge can ever occur, leaving the
paper game's view independent of the hidden bit). Exact advantage preservation
(`CKA.advantagePaper_eq`) is proved in `PaperFaithfulSendProof.lean`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.CKA

variable {Key State Coins Msg CKey : Type}

section Paper

variable (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ)
  [SampleableType Coins] [SampleableType CKey]

local notation "GameM" => StateT (GameState State Msg) ProbComp

/-- Paper-faithful `send-P` oracle (ACD19, Fig. 3), permitted in every ping-pong epoch including
`t*`. -/
def sendImplPaper : QueryImpl (Party →ₒ Option (Msg × CKey)) GameM := fun P => do
  let s ← get
  if !(s.canSend P) then return none
  let r ← ($ᵗ Coins : ProbComp Coins)
  let out := cka.send (s.st P) r
  set (s.afterSend P out.1 out.2.1)
  return some out.2

def oracleImplPaper : QueryImpl (spec State Coins Msg CKey) GameM :=
  sendImplPaper cka + sendWithAdversaryCoinsImpl cka tStar + challImpl cka tStar + receiveImpl cka
    + (corrImpl Δ tStar : QueryImpl _ GameM)

variable [SampleableType Key]

def gamePaper (A : Adversary State Coins Msg CKey) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState State Msg) ProbComp) + oracleImplPaper cka Δ tStar
  let b' ← (simulateQ impl A).run' (initState cka k b)
  return b == b'

noncomputable def advantagePaper (A : Adversary State Coins Msg CKey) : ℝ≥0∞ :=
  𝒟[gamePaper cka Δ tStar A].boolBias

end Paper

section Conversion

variable (tStar : ℕ)

local notation "Comp" => AdversaryComp State Coins Msg CKey

/-- Shadow epoch counters, or `none` once the reduction has aborted. -/
local notation "RedM" => StateT (Option (Party → ℕ)) Comp

def fromPaperStep {α : Type} (P : Party) (res : Option α) : RedM Unit :=
  modify fun e? => match e?, res with
    | some e, some _ => some (Function.update e P (e P + 1))
    | e?, _ => e?

def fromPaperFwd {α : Type} (P : Party) (q : Comp (Option α)) : RedM (Option α) := do
  if (← get).isNone then return none
  let res ← StateT.lift q
  fromPaperStep P res
  return res

/-- Aborts if `send-P` would succeed in epoch `t*` (where `CKA.game` refuses it); otherwise
forwards. -/
def fromPaperSend : QueryImpl (Party →ₒ Option (Msg × CKey)) RedM := fun P => do
  match (← get) with
  | none => return none
  | some e =>
    if (e P == e P.other && P.sendsIn (e P + 1)) && e P + 1 == tStar then
      set (none : Option (Party → ℕ))
      return none
    else
      fromPaperFwd P (sendQuery (State := State) (Coins := Coins) P)

def fromPaperImpl : QueryImpl (unifSpec + spec State Coins Msg CKey) RedM :=
  let c : QueryImpl unifSpec RedM := fun n =>
    StateT.lift (query (spec := unifSpec + spec State Coins Msg CKey) (.inl n))
  let i₁ : QueryImpl (Party →ₒ Option (Msg × CKey)) RedM := fromPaperSend tStar
  let i₂ : QueryImpl ((Party × Coins) →ₒ Option (Msg × CKey)) RedM := fun ⟨P, r⟩ =>
    fromPaperFwd P (sendWithAdversaryCoinsQuery (State := State) P r)
  let i₃ : QueryImpl (Party →ₒ Option (Msg × CKey)) RedM := fun P =>
    fromPaperFwd P (challQuery (State := State) (Coins := Coins) P)
  let i₄ : QueryImpl (Party →ₒ Option Unit) RedM := fun P =>
    fromPaperFwd P (receiveQuery (State := State) (Coins := Coins) (Msg := Msg) (CKey := CKey) P)
  let i₅ : QueryImpl (Party →ₒ Option State) RedM := fun P => do
    if (← get).isNone then return none
    StateT.lift (corrQuery (Coins := Coins) (Msg := Msg) (CKey := CKey) P)
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

/-- Converts a `gamePaper` adversary into a `CKA.game` adversary by tracking shadow epoch counters
and returning a uniform bit after aborting on plain `send-P` in epoch `t*`. -/
def fromPaperRed (A : Adversary State Coins Msg CKey) : Adversary State Coins Msg CKey :=
  (do
    let (b', e?) ← (simulateQ (fromPaperImpl tStar) A).run (some fun _ => 0)
    match e? with
    | some _ => return b'
    | none => (liftM ($ᵗ Bool : ProbComp Bool) : Comp Bool) : Comp Bool)

end Conversion

end CryptoGames.CKA
