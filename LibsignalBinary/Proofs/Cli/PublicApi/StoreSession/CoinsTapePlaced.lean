/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Coins.CoinsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable CLI Coins Tape Predicates (`cliTapeAt`, `cliTapeAfter`)

Wraps `Coins.coinsAtPlaced` and `Coins.coinsAfterPlaced` as `semireducible` definitions with a
phantom `_ctl` parameter so relocatable `<Coins>` proofs preserve the arity and `SepProp` opacity of
`tapeAt` / `tapeAfter` while reducing definitionally at the CLI slot boundary.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.CoinsTape

open Arm64 ProofLib
open CryptoVerification
open CryptoVerification.SignalSession.Coins

/-- Relocatable CLI coins tape predicate with phantom `_ctl` parameter matching `tapeAt`. -/
def cliTapeAt [LibsignalPlacement] (_ctl : BitVec 64) (cur : BitVec 64) (rest : List (BitVec 8)) :
    SepProp :=
  coinsAtPlaced cur rest

/-- Relocatable CLI coins tape predicate after `k` draws, matching `tapeAfter`. -/
def cliTapeAfter [LibsignalPlacement] (_ctl : BitVec 64) (cur : BitVec 64)
    (rest : List (BitVec 8)) (k : Nat) : SepProp :=
  coinsAfterPlaced cur rest k

theorem cliTapeAt_eq_coinsAtPlaced [LibsignalPlacement] (ctl cur : BitVec 64)
    (rest : List (BitVec 8)) :
    cliTapeAt ctl cur rest = coinsAtPlaced cur rest := rfl

theorem cliTapeAfter_eq_coinsAfterPlaced [LibsignalPlacement] (ctl cur : BitVec 64)
    (rest : List (BitVec 8)) (k : Nat) :
    cliTapeAfter ctl cur rest k = coinsAfterPlaced cur rest k := rfl

theorem cliTapeAt_eq_pure_sep_cliTapeAfter_zero [LibsignalPlacement] (ctl cur : BitVec 64)
    (rest : List (BitVec 8)) :
    cliTapeAt ctl cur rest = ⌜rest.length < 2 ^ 63⌝ ∗ cliTapeAfter ctl cur rest 0 := by
  unfold cliTapeAt cliTapeAfter coinsAtPlaced coinsAfterPlaced tapeAt2
  rw [tapeAfter2_zero_eq]

theorem cliTapeAfter_zero_entails_cliTapeAt [LibsignalPlacement] (ctl cur : BitVec 64)
    (rest : List (BitVec 8)) (hrest : rest.length < 2 ^ 63) :
    cliTapeAfter ctl cur rest 0 ⊢ cliTapeAt ctl cur rest := by
  rw [cliTapeAt_eq_pure_sep_cliTapeAfter_zero]
  exact Entails.pure_right hrest (Entails.refl _)

theorem cliTapeAt_entails_cliTapeAfter_zero [LibsignalPlacement] (ctl cur : BitVec 64)
    (rest : List (BitVec 8)) :
    cliTapeAt ctl cur rest ⊢ cliTapeAfter ctl cur rest 0 := by
  rw [cliTapeAt_eq_pure_sep_cliTapeAfter_zero]
  exact Entails.pure_left fun _ => Entails.refl _

end CryptoVerification.Cli.CoinsTape
