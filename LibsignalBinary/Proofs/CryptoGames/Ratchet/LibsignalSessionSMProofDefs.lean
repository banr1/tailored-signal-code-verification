/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Party

/-!
# Proof-Side Definitions for `LibsignalSessionSM`

Ghost-epoch alignment predicate and tuple equivalence for `InitKeys`.
-/

@[expose] public section

namespace CryptoGames
namespace LibsignalSession

def GhostState.Aligned {PQ : Type} (g : GhostState PQ) : Prop :=
  g.chainEpochs.length = g.session.receiverChains.length

def InitKeys.equiv : (BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256) ≃ InitKeys where
  toFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
  invFun k := (k.rootKey, k.chainKey, k.bobSpkCoins, k.aliceRatchetCoins, k.pqrKey)
  left_inv _ := rfl
  right_inv _ := rfl

end LibsignalSession
end CryptoGames
