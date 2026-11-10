/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem1Reductions

/-!
# Privacy reduction with a blanking map (`privRedB`)

**Checked by Lean.** Adapts ACD19's hybrid privacy reduction `Thm1.privRed` (`B3,i`) to messages with a public component (DEV-LS13) via a blanking map `blank : Msg → Msg` that preserves the public part so equal-public-part FS-AEAD bounds apply.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM.ThmB

set_option linter.unusedSectionVars false

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]

open Thm1 in
local notation "Comp" => AdversaryComp St Msg Coins C
open Thm1 in
local notation "RedM" => StateT (Thm1.Mirror Msg C) (AdversaryComp St Msg Coins C)

section Sim

variable (Δ qep : ℕ) (challMsg : ℕ → Option (Msg → Msg)) (real : Option (ℕ × (Msg → Msg)))

/-- Sends a challenge in epoch `t` via `chall (blank mb) mb` when `real = some (t, blank)`, or via `transmit` otherwise. -/
def simSend (P : Party) (t : ℕ) (mb : Msg) (r : Option Coins) : Comp (Option C) :=
  match real with
  | some (i, blank) =>
    if t = i then challQuery P (blank mb) mb r else transmitQuery P (((challMsg t).map (· mb)).getD mb) r
  | none => transmitQuery P (((challMsg t).map (· mb)).getD mb) r

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

def simRun (A : Adversary St Msg Coins C) : Comp (Bool × Bool) := do
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : Comp Bool)
  let b' ← (simulateQ (simImpl Δ qep challMsg real) A).run'
    ({ st := fun _ => (), b } : Thm1.Mirror Msg C)
  return (b, b')

end Sim

/-- Blanking-map privacy reduction `B3,i` (DEV-LS13, DEV-SM19): challenges `(blank m_b, m_b)` in epoch `i` and encrypts `blank m_b` in epochs `< i`. -/
def privRedB (Δ qep i : ℕ) (blank : Msg → Msg) (A : Adversary St Msg Coins C) :
    Adversary St Msg Coins C :=
  show AdversaryComp St Msg Coins C Bool from do
  let (b, b') ← simRun Δ qep (fun t => if t < i then some blank else none) (some (i, blank)) A
  return (b == b')

end CryptoGames.SM.ThmB
