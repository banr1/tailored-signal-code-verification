/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs

/-!
# Proof-Side Definitions for `RootKdfDefs`

One-step `rootKdf` PRG game (`rootStepPRG`) and its HMAC-PRF reduction (`rootStepRed`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
namespace CryptoGames
namespace Ratchet
open HMAC HKDF CBC MACScheme

/-- One `rootKdf` step on a uniform root key and fixed public input `I`, viewed as a PRG. -/
def rootStepPRG (F : ShaState → List (BitVec 8) → ShaState) {Pt : Type}
    (enc : Pt → List (BitVec 8)) (I : Pt) : PRGScheme RootKey (RootKey × ChainKey) :=
  ⟨fun σ => rootKdf F σ (enc I)⟩

/-- PRF reduction for `rootStepPRG`: queries `extractPRF` at `I`, expands the output, and runs `B`. -/
def rootStepRed (F : ShaState → List (BitVec 8) → ShaState) {Pt : Type} (I : Pt)
    (B : PRGScheme.PRGAdversary (RootKey × ChainKey)) : PRFAdversary Pt (BitVec 256) :=
  show OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool from do
  let prk ← evalQuery (Input := Pt) (Tag := BitVec 256) I
  (liftM (B ((expandPRG F).gen prk)) : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool)

end Ratchet
end CryptoGames
