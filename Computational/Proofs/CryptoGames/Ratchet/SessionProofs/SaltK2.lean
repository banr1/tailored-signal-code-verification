/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimC

/-!
# Next-epoch receiver-chain seed extraction (`k2Seed`)

**Checked by Lean.** Defines `k2Seed` for branch K2 of `LibsignalSimC.snapshotMessageKeySeed` (DEV-LS37), computing the next receiving chain from a snapshot's root key and sender private key.
-/

@[expose] public section

open CryptoGames.Ratchet CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC (chainKeyAfter chainSeedAt snapshotMessageKeySeed decryptWithKnownSeed)

namespace CryptoGames.LibsignalSM.Proofs.SaltMismatch

/-- Seed extracted by branch K2 of `snapshotMessageKeySeed` from root key `rk` and sender chain `sc?`. -/
def k2Seed (C : Crypto) (rk : LibsignalSession.RootKey) (sc? : Option SenderChain) (Y : PublicKey)
    (n : BitVec 32) : Option (List (BitVec 8)) :=
  sc?.bind fun sc =>
    match rootCreateChain C rk Y sc.ratchetKey.privateKey with
    | .ok (_, ck) => chainSeedAt C.F ck n
    | .error _ => none

end CryptoGames.LibsignalSM.Proofs.SaltMismatch
