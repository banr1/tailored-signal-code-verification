/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout

/-!
# Bridge Between `coinsInstalled` and `Coins.coinsAt`

Identifies `coinsInstalled img p coins` (`NEXT` at `img.base + coinsNextOff`, `LEFT` at
`img.base + coinsLeftOff`) with `Coins.coinsAt img.base p coins` whenever `coins.length < 2^63`,
providing entry (`coinsInstalled_entails_coinsAt`) and exit (`coinsAfter_entails_anyHeap`)
entailments for the CLI wrapper slots.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib
open CryptoVerification.SignalSession.Coins
open CryptoVerification.SignalSession.Cli.MainHops

theorem coinsNext_eq (b : BitVec 64) : coinsNext b = b + coinsNextOff := by
  rfl

theorem coinsLeft_eq (b : BitVec 64) : coinsLeft b = b + coinsLeftOff := by
  rfl

/-- `coinsInstalled` coincides with `coinsAfter` at draw offset `0`. -/
theorem coinsInstalled_eq_coinsAfter_zero (img : Obj.Image) (p : BitVec 64)
    (coins : List (BitVec 8)) :
    coinsInstalled img p coins = coinsAfter img.base p coins 0 := by
  unfold coinsInstalled coinsAfter
  rw [tapeAfter2_zero_eq, coinsNext_eq, coinsLeft_eq]

/-- Under `coins.length < 2^63`, `coinsAt` equals `coinsInstalled`. -/
theorem coinsAt_eq_coinsInstalled (img : Obj.Image) (p : BitVec 64)
    (coins : List (BitVec 8)) (hlen : coins.length < 2 ^ 63) :
    coinsAt img.base p coins = coinsInstalled img p coins := by
  unfold coinsAt tapeAt2 coinsInstalled
  rw [pure_sepConj_of_true hlen, coinsNext_eq, coinsLeft_eq]

/-- Entry entailment from `coinsInstalled` to `coinsAt` under `coins.length < 2^63`. -/
theorem coinsInstalled_entails_coinsAt (img : Obj.Image) (p : BitVec 64)
    (coins : List (BitVec 8)) (hlen : coins.length < 2 ^ 63) :
    coinsInstalled img p coins ⊢ coinsAt img.base p coins := by
  exact Entails.of_eq (coinsAt_eq_coinsInstalled img p coins hlen).symm

theorem coinsAfter_entails_anyHeap (b cur : BitVec 64) (rest : List (BitVec 8)) (k : Nat) :
    coinsAfter b cur rest k ⊢ anyHeap := by
  exact entails_anyHeap _

end CryptoVerification.SignalSession.Cli.Slots
