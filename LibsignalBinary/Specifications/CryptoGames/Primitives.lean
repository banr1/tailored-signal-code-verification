/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.SimSemantics.Append.Core

/-!
# Deterministic AEAD and its one-time CCA game

**Trusted in part.** The theorems of `Computational/Theorems/` use only `AEADScheme`, `otccaSpec`,
`OTCCAState` from this file: read them. Everything else here is checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Defines deterministic AEAD (`AEADScheme`, ACD19 §2.2 Def. 1) and its one-time chosen-ciphertext
hidden-bit game (`OTCCAAdversary`, `otccaEncrypt`, `otccaDecrypt`, `otccaGame`, `otccaAdvantage`,
Def. 2 and Fig. 1).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames

/-- ACD19 Def. 1: a deterministic AEAD scheme whose randomness comes solely from the key. -/
structure AEADScheme (Key AssocData Message Ciphertext : Type) where
  /-- `Enc(k, a, m)`: encrypt message `m` with associated data `a` under key `k`. -/
  enc : Key → AssocData → Message → Ciphertext
  /-- `Dec(k, a, e)`: decrypt `e` with associated data `a`, returning `none` on rejection. -/
  dec : Key → AssocData → Ciphertext → Option Message

namespace AEADScheme

variable {Key AssocData Message Ciphertext : Type}

/-- Fig. 1 OT-CCA oracle interface: one-time `encrypt` and unbounded `decrypt`. -/
abbrev otccaSpec (AssocData Message Ciphertext : Type) :=
  ((AssocData × Message) →ₒ Option Ciphertext) + ((AssocData × Ciphertext) →ₒ Option Message)

/-- Fig. 1 OT-CCA game state: key, hidden bit, and optional challenge `(a*, e*)`. -/
structure OTCCAState (Key AssocData Ciphertext : Type) where
  key : Key
  b : Bool
  chal : Option (AssocData × Ciphertext) := none

/-- An OT-CCA adversary with own coins (`unifSpec`) and the Fig. 1 oracles. -/
abbrev OTCCAAdversary (AssocData Message Ciphertext : Type) :=
  OracleComp (unifSpec + otccaSpec AssocData Message Ciphertext) Bool

variable [DecidableEq AssocData] [DecidableEq Ciphertext] [SampleableType Ciphertext]

/-- Fig. 1 `encrypt(a, m)`: one-time; returns `ae.enc key a m` (`b = false`) or a uniform
ciphertext (`b = true`). -/
def otccaEncrypt (ae : AEADScheme Key AssocData Message Ciphertext) :
    QueryImpl ((AssocData × Message) →ₒ Option Ciphertext)
      (StateT (OTCCAState Key AssocData Ciphertext) ProbComp) := fun ⟨a, m⟩ => do
  let st ← get
  if st.chal.isSome then return none
  let e ← if st.b then liftM ($ᵗ Ciphertext) else pure (ae.enc st.key a m)
  set { st with chal := some (a, e) }
  return some e

/-- Fig. 1 `decrypt(a, e)`: rejects `(a*, e*)` and always rejects when `b = true`.

**DEV-AEAD1 (formalization): decryption refuses only the challenge pair.** ACD19 Fig. 1 refuses
every query with `e = e*`. Here only `(a*, e*)` is refused, so the adversary may also ask
`(a', e*)`. Effect: constants: this OT-CCA notion is stronger than Fig. 1's, so every OT-CCA term
assumes more of the AEAD than ACD19 does. For an encrypt-then-MAC AEAD whose MAC covers `a`, the gap
is one MAC forgery per such query. -/
def otccaDecrypt (ae : AEADScheme Key AssocData Message Ciphertext) :
    QueryImpl ((AssocData × Ciphertext) →ₒ Option Message)
      (StateT (OTCCAState Key AssocData Ciphertext) ProbComp) := fun ⟨a, e⟩ => do
  let st ← get
  if st.b || st.chal == some (a, e) then return none
  return ae.dec st.key a e

/-- The Fig. 1 OT-CCA hidden-bit game: sample `b` and a key, run the adversary with the oracles,
and return whether its guess equals `b`. -/
def otccaGame [SampleableType Key] (ae : AEADScheme Key AssocData Message Ciphertext)
    (A : OTCCAAdversary AssocData Message Ciphertext) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let key ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (OTCCAState Key AssocData Ciphertext) ProbComp)
    + (otccaEncrypt ae + otccaDecrypt ae)
  let b' ← (simulateQ impl A).run' { key, b }
  return b == b'

/-- `Adv^{ot-cca}_{AE}(A)`: the OT-CCA advantage, the `boolBias` of `otccaGame`. -/
noncomputable def otccaAdvantage [SampleableType Key]
    (ae : AEADScheme Key AssocData Message Ciphertext)
    (A : OTCCAAdversary AssocData Message Ciphertext) : ℝ≥0∞ :=
  𝒟[ae.otccaGame A].boolBias

end AEADScheme

end CryptoGames
