/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Hybrid
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security

/-!
# Hybrid Receiver Oracles and Uniform Pair Distribution

Defines the hybrid receiver operations (`receiveH`, `deliverH`, `injectH`), the uniform
chain/message-key pair sampler `DU`, and the OT-CCA reduction oracle spec `RSpec`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
namespace CryptoGames.FSAEAD.Thm5
variable {CK MK AD M C : Type}
section Oracles
variable {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
  [SampleableType MK] [SampleableType CK] [SampleableType C]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
  (P : Params) (D : ℕ → ProbComp (CK × MK)) (ops : Option (SpecialOps AD M C m))
local notation "St" => HSt CK MK AD M C
local notation "HS" => HState CK MK AD M C

/-- Hybrid receiver step (`FS-Rcv` on hybrid keys), updating skipped keys and advancing chain positions. -/
def receiveH (hint : Option M) (a : AD) (c : ℕ × C) : StateT St m (Option (ℕ × M)) := do
  let (i, e) := c
  let st ← getH
  if st.skipped.contains i then
    match ← decIdx ae P ops hint i a e with
    | some msg =>
      modifyH fun st => { st with skipped := st.skipped.filter (· != i) }
      pure (some (i, msg))
    | none => pure none
  else if i ≤ st.receiverIdx ∨ maxSkip < i - st.receiverIdx - 1 then pure none
  else if !P.la && st.lastSentIdx < i && !st.isCompromised i then pure none
  else do
    genUpTo G P D i
    match ← decIdx ae P ops hint i a e with
    | some msg =>
      modifyH fun st' => { st' with skipped := newSkipped st.receiverIdx i ++ st'.skipped }
      pure (some (i, msg))
    | none => pure none

variable [DecidableEq AD] [DecidableEq M] [DecidableEq C]

/-- Hybrid `deliver` oracle. -/
def deliverH (q : AD × (ℕ × C)) : StateT St m (Option (ReceiveResult M)) := do
  let st ← getH
  if st.ended then pure none else
  match st.inTransit.find? (fun r => r.ad == q.1 && r.ct == q.2) with
  | none => pure none
  | some r =>
    let inWindow := decide (r.idx ≤ st.receiverIdx + maxSkip + 1)
    let mustBeCorrect := !st.isCompromised r.idx && inWindow
    match ← receiveH ae G maxSkip P D ops (some r.msg) q.1 q.2 with
    | none =>
      modifyH fun st' => { st' with win := st'.win || mustBeCorrect }
      pure (some .rejected)
    | some (i', m') =>
      let incorrect := mustBeCorrect && (i' != r.idx || m' != r.msg)
      let out := if st.challengesInTransit.contains r.idx then none else some m'
      modifyH fun st' => ({ st' with receiverIdx := max st'.receiverIdx i',
                                     win := st'.win || incorrect }).removeFromTransit r.idx
      pure (some (.accepted i' out))

/-- Hybrid `inject` oracle, recording lookahead forgeries in `lf` and halting in lookahead mode. -/
def injectH (q : AD × (ℕ × C)) : StateT St m (Option (ReceiveResult M)) := do
  let st ← getH
  if st.ended || st.inTransit.any (fun r => r.ad == q.1 && r.ct == q.2) then pure none else
  match ← receiveH ae G maxSkip P D ops none q.1 q.2 with
  | none => pure (some .rejected)
  | some (i', m') =>
    let forged := !st.isCompromised i'
    let lfNow := forged && decide (st.lastSentIdx < i')
    modifyH fun st' => ({ st' with receiverIdx := max st'.receiverIdx i',
                                   win := st'.win || forged, lf := st'.lf || lfNow,
                                   ended := st'.ended || (P.la && lfNow) }).removeFromTransit i'
    pure (some (.accepted i' (some m')))

end Oracles
section Games
variable [SampleableType MK] [SampleableType CK] [SampleableType C]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

/-- Samples a uniform `(CK, MK)` pair independently of the chain position. -/
def DU (_ : ℕ) : ProbComp (CK × MK) := do
  let w ← $ᵗ CK
  let K ← $ᵗ MK
  pure (w, K)

end Games

/-- Oracle specification combining uniform coin queries with indexed OT-CCA `encrypt`/`decrypt`. -/
abbrev RSpec (AD M C : Type) := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C

end CryptoGames.FSAEAD.Thm5
