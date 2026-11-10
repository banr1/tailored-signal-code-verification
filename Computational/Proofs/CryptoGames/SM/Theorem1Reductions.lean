/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.Game

/-!
# Simulator and reductions for Theorem 1

**Checked by Lean.** Defines the concrete reductions `challSim` (`B1`, `B2`) and `privRed` (`B3,i`)
of ACD19 Appendix A and their shared game-bookkeeping simulator (`Mirror`, `simRun`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM.Thm1

set_option linter.unusedSectionVars false

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]

/-- Game-bookkeeping mirror with erased (`Unit`) party states. -/
abbrev Mirror (Msg C : Type) := GameState Unit Msg C

local notation "Comp" => AdversaryComp St Msg Coins C
local notation "RedM" => StateT (Mirror Msg C) (AdversaryComp St Msg Coins C)

section Sim

variable (Δ qep : ℕ) (challMsg : ℕ → Option Msg) (real : Option (ℕ × Msg))

/-- Sends a challenge in epoch `t` via `challQuery` when `real = some (t, m̄)`, or via
`transmitQuery` otherwise. -/
def simSend (P : Party) (t : ℕ) (mb : Msg) (r : Option Coins) : Comp (Option C) :=
  match real with
  | some (i, mbar) =>
    if t = i then challQuery P mbar mb r else transmitQuery P ((challMsg t).getD mb) r
  | none => transmitQuery P ((challMsg t).getD mb) r

def simTransmit : QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) RedM :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    let res ← StateT.lift (transmitQuery (St := St) P m r)
    match res, s.epMgmt Δ qep P r.isSome with
    | some c, some s₁ => set (s₁.record Δ P () ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ false)
    | _, _ => pure ()
    return res

def simChall : QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) RedM :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    match s.epMgmt Δ qep P r.isSome with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) then return none
      let mb := if s.b then m₁ else m₀
      let res ← StateT.lift (simSend (St := St) challMsg real P (s₁.epoch P) mb r)
      match res with
      | none => return none
      | some c =>
        set (s₁.record Δ P () ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, mb, c⟩ true)
        return some c

def simDeliver : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) RedM :=
  fun ⟨P, c⟩ => do
    let s ← get
    let res ← StateT.lift (deliverQuery (St := St) (Coins := Coins) P c)
    match res, s.inTransit P.other c with
    | some (.accepted t' i' m), some r =>
      set (s.accept P () r.pos)
      return some (.accepted t' i' (if s.chall.contains r.pos then none else m))
    | _, _ => return res

def simInject : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) RedM :=
  fun ⟨P, c⟩ => do
    let s ← get
    let res ← StateT.lift (injectQuery (St := St) (Coins := Coins) P c)
    match res with
    | some (.accepted t' i' _) => set (s.accept P () ⟨P.other, t', i'⟩)
    | _ => pure ()
    return res

def simCorr : QueryImpl (Party →ₒ Option St) RedM := fun P => do
  let s ← get
  let res ← StateT.lift (corrQuery (Msg := Msg) (Coins := Coins) (C := C) P)
  if res.isSome then set (s.afterCorr P)
  return res

def simCoins : QueryImpl unifSpec RedM := fun n =>
  StateT.lift (query (spec := unifSpec + spec St Msg Coins C) (.inl n))

def simOracles : QueryImpl (spec St Msg Coins C) RedM :=
  let i₁ : QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) RedM := simTransmit Δ qep
  let i₂ : QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) RedM :=
    simChall Δ qep challMsg real
  let i₃ : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) RedM := simDeliver
  let i₄ : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) RedM := simInject
  let i₅ : QueryImpl (Party →ₒ Option St) RedM := simCorr
  HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅

def simImpl : QueryImpl (unifSpec + spec St Msg Coins C) RedM :=
  let c : QueryImpl unifSpec RedM := simCoins
  let o : QueryImpl (spec St Msg Coins C) RedM := simOracles Δ qep challMsg real
  HAdd.hAdd c o

/-- Runs `A` against `simImpl` with a fresh bit `b`, returning `(b, b')`. -/
def simRun (A : Adversary St Msg Coins C) : Comp (Bool × Bool) := do
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : Comp Bool)
  let b' ← (simulateQ (simImpl Δ qep challMsg real) A).run'
    ({ st := fun _ => (), b } : Mirror Msg C)
  return (b, b')

end Sim

/-- Reduction `B1`/`B2` of ACD19 Lemmas 16–17, simulating challenges via `transmit` (DEV-SM19). -/
def challSim (Δ qep : ℕ) (A : Adversary St Msg Coins C) : Adversary St Msg Coins C :=
  show AdversaryComp St Msg Coins C Bool from do
  let (_, b') ← simRun Δ qep (fun _ => none) none A
  return b'

/-- Reduction `B3,i` of ACD19 Lemma 18, interpolating between `H3,i` and `H3,i+1`. -/
def privRed (Δ qep i : ℕ) (mbar : Msg) (A : Adversary St Msg Coins C) :
    Adversary St Msg Coins C :=
  show AdversaryComp St Msg Coins C Bool from do
  let (b, b') ← simRun Δ qep (fun t => if t < i then some mbar else none) (some (i, mbar)) A
  return (b == b')

/-- Erase party states from a `GameState` to obtain its `Mirror` state. -/
def toMirror (s : GameState St Msg C) : Mirror Msg C :=
  { st := fun _ => ()
    epoch := s.epoch
    idx := s.idx
    tL := s.tL
    trans := s.trans
    chall := s.chall
    comp := s.comp
    maxAcc := s.maxAcc
    b := s.b
    win := s.win
    leaks := s.leaks
    corrs := s.corrs }

end CryptoGames.SM.Thm1
