/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Chains
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SaltK1

/-!
# Sender-chain seed extraction (`k3Seed`)

**Checked by Lean.** Defines `k3Seed` for branch K3 of `LibsignalSimC.snapshotMessageKeySeed` (DEV-LS37) and proves `k3Seed_eq_msgSeedAt` on chains starting from `ck0`.
-/

@[expose] public section

open CryptoGames.Ratchet CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC (chainKeyAfter chainSeedAt snapshotMessageKeySeed decryptWithKnownSeed)

namespace CryptoGames.LibsignalSM.Proofs.SaltMismatch

open CryptoGames.LibsignalSM.Proofs.Correctness

/-- Seed extracted by branch K3 of `snapshotMessageKeySeed` from sender chain `sc`. -/
def k3Seed (F : ShaCompress) (sc : SenderChain) (Y : PublicKey) (n : BitVec 32) :
    Option (List (BitVec 8)) :=
  if sc.ratchetKey.publicKey = Y then chainSeedAt F sc.chainKey n else none

theorem k3Seed_eq_msgSeedAt {F : ShaCompress} {ck0 : BitVec 256} {j : ℕ} (hj : j < 2 ^ 32)
    {sc : SenderChain} (hsc : sc.chainKey = ⟨chainKeyValAt F ck0 j, BitVec.ofNat 32 j⟩)
    {Y : PublicKey} {n : BitVec 32} {seed : List (BitVec 8)} (h : k3Seed F sc Y n = some seed) :
    seed = msgSeedAt F ck0 n.toNat := by
  unfold k3Seed at h
  split at h
  · rw [hsc] at h
    by_cases hle : j ≤ n.toNat
    · rw [chainSeedAt_chainKeyValAt F ck0 hj n hle] at h
      exact (Option.some.inj h).symm
    · unfold chainSeedAt at h
      have hidx : (BitVec.ofNat 32 j).toNat = j := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
      simp [hidx, show n.toNat < j by omega] at h
  · cases h

end CryptoGames.LibsignalSM.Proofs.SaltMismatch
