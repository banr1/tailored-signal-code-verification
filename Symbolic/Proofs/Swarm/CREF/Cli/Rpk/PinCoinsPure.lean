/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs

/-!
# Coin Pinning for Session Steps

Defines `pureCoinsOf` and `pinCoins`, converting an optional drawn byte slice into a 256-bit coin
vector.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.RpkCli

/-- Extracts a 256-bit key from the first 32 bytes of `rest`, zero-padding if shorter. -/
def pureCoinsOf (rest : List (BitVec 8)) : BitVec 256 :=
  CryptoGames.HKDF.bytesToKey32 ((rest ++ List.replicate 32 0#8).take 32)

/-- Maps `none` to `0#256` and `some bs` to `pureCoinsOf bs`. -/
def pinCoins : Option (List (BitVec 8)) → BitVec 256
  | none => 0#256
  | some bs => pureCoinsOf bs

end Symbolic.Swarm.CREF.CliPure.RpkCli
