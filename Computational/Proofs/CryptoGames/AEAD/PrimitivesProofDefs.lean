/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import VCVio.CryptoFoundations.PRG
public import VCVio.CryptoFoundations.SecExp
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.QueryTracking.QueryBound
public import ToMathlib.Control.StateT

/-!
# AEAD Correctness Predicate

Defines perfect decryption correctness `AEADScheme.Correct`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
namespace CryptoGames
namespace AEADScheme
variable {Key AssocData Message Ciphertext : Type}

/-- Perfect decryption correctness: `ae.dec k a (ae.enc k a m) = some m`. -/
def Correct (ae : AEADScheme Key AssocData Message Ciphertext) : Prop :=
  ∀ k a m, ae.dec k a (ae.enc k a m) = some m

end AEADScheme
end CryptoGames
