/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.Primitives

/-!
# FS-AEAD Restricted Associated-Data Predicates

Predicates restricting an FS-AEAD adversary's encryption associated data (`encBadAD`, `EncADsOk`)
and AEAD correctness to valid associated data (`CorrectOn`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
namespace CryptoGames
namespace FSAEAD
variable {Key SenderState ReceiverState AssocData Message Ciphertext : Type}
section RestrictedAD
variable {SS RS AD Msg C : Type}

/-- Whether the FS-AEAD query `t` is a `transmit` or `challenge` whose AD fails `ok`. -/
def encBadAD (ok : AD → Bool) : (unifSpec + spec SS RS AD Msg C).Domain → Bool
  | .inr (.inl (.inl (.inl (.inl (.inl ⟨a, _⟩))))) => !ok a
  | .inr (.inl (.inl (.inl (.inl (.inr ⟨a, _, _⟩))))) => !ok a
  | _ => false

/-- Every `transmit` and `challenge` query of `A` carries an AD satisfying `ok`. -/
def EncADsOk (ok : AD → Bool) (A : Adversary SS RS AD Msg C) : Prop :=
  A.IsQueryBoundP (fun t => encBadAD (SS := SS) (RS := RS) (Msg := Msg) (C := C) ok t = true) 0

end RestrictedAD
end FSAEAD
namespace AEADScheme
variable {K AD M C : Type}

/-- `ae` is correct on the ADs `a` with `ok a = true`. -/
def CorrectOn (ae : AEADScheme K AD M C) (ok : AD → Bool) : Prop :=
  ∀ k a m, ok a = true → ae.dec k a (ae.enc k a m) = some m

end AEADScheme
end CryptoGames
