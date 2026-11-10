/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr

/-!
# Raw `InvalidSessionStructure("invalid receiver chain message keys")` Result

Defines `iscmkStr`, `iscmkBodyAt`, `iscmkErrAt`, and the relaxed decrypt postcondition
`decResultAtR` allowing `iscmkErrAt` on `BadCiphertext` errors.
-/

@[expose] public section

namespace Proofs.libsignal.SR.DecX

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchetRepr

/-- `"invalid receiver chain message keys"` (35 bytes; `try_decrypt_with_state` `0x3500c`). -/
def iscmkStr : List (BitVec 8) := utf8 "invalid receiver chain message keys"

theorem iscmkStr_length : iscmkStr.length = 35 := by decide +kernel

/-- Payload (40 bytes at `p = a + 8`) of the raw `InvalidSessionStructure(iscmkStr)`. -/
def iscmkBodyAt (p : BitVec 64) : SepProp :=
  strRefAt p iscmkStr ∗ memRegion (p + 16#64) 24

/-- The raw `SignalProtocolError::InvalidSessionStructure("invalid receiver chain message keys")`
at `a` (48 bytes): tag `speWord 20`, `&'static str` at `+8`, 24 bytes unspecified. -/
def iscmkErrAt (a : BitVec 64) : SepProp :=
  (a ↦₆₄ speWord 20) ∗ iscmkBodyAt (a + 8#64)

/-- Relaxed `vecResultAt`: holds when either `vecResultAt A r res` holds or `res` is a
`BadCiphertext` error and `iscmkErrAt r` holds at `r`. -/
def decResultAtR (A : RustAlloc) (r : BitVec 64)
    (res : Except SignalProtocolError (List (BitVec 8))) : SepProp :=
  ∃∗ raw : Bool,
    match raw with
    | false => vecResultAt A r res
    | true => ⌜∃ t, res = .error (.invalidMessage t .badCiphertext)⌝ ∗ iscmkErrAt r

theorem decResultAt_entails_R (A : RustAlloc) (r : BitVec 64)
    (res : Except SignalProtocolError (List (BitVec 8))) :
    vecResultAt A r res ⊢ decResultAtR A r res :=
  Entails.sepExists_intro (P := fun raw : Bool =>
    match raw with
    | false => vecResultAt A r res
    | true => ⌜∃ t, res = .error (.invalidMessage t .badCiphertext)⌝ ∗ iscmkErrAt r) false

theorem iscmkErrAt_entails_R (A : RustAlloc) (r : BitVec 64)
    {res : Except SignalProtocolError (List (BitVec 8))} {t : MessageType}
    (h : res = .error (.invalidMessage t .badCiphertext)) :
    iscmkErrAt r ⊢ decResultAtR A r res := by
  refine Entails.trans ?_ (Entails.sepExists_intro (P := fun raw : Bool =>
    match raw with
    | false => vecResultAt A r res
    | true => ⌜∃ t, res = .error (.invalidMessage t .badCiphertext)⌝ ∗ iscmkErrAt r) true)
  exact Entails.pure_right ⟨t, h⟩ (Entails.refl _)

/-- `Satisfies` form of `decResultAt_entails_R` under a frame. -/
theorem Satisfies.decResultAtR_of {A : RustAlloc} {r : BitVec 64}
    {res : Except SignalProtocolError (List (BitVec 8))} {F : SepProp} {m : Memory}
    (h : m ⊨ vecResultAt A r res ∗ F) : m ⊨ decResultAtR A r res ∗ F :=
  Satisfies.mono (sepConj_mono_left (decResultAt_entails_R A r res)) h

end Proofs.libsignal.SR.DecX
