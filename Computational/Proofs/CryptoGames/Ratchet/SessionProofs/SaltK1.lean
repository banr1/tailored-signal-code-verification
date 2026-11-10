/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Chains
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimC

/-!
# Receiver-chain seed extraction (`k1Seed`)

**Checked by Lean.** Defines `k1Seed` for branch K1 of `LibsignalSimC.snapshotMessageKeySeed` (DEV-LS37) and proves forward chain-stepping agreement with `chainKeyValAt` and `msgSeedAt`.
-/

@[expose] public section

open CryptoGames.Ratchet CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC (chainKeyAfter chainSeedAt snapshotMessageKeySeed decryptWithKnownSeed)

namespace CryptoGames.LibsignalSM.Proofs.SaltMismatch

open CryptoGames.LibsignalSM.Proofs.Correctness

theorem chainKeyAfter_chainKeyValAt (F : ShaCompress) (ck0 : BitVec 256) :
    ∀ n m : ℕ, chainKeyAfter F n (chainKeyValAt F ck0 m) = chainKeyValAt F ck0 (m + n)
  | 0, m => rfl
  | n + 1, m => by
    rw [chainKeyAfter]
    have h := chainKeyAfter_chainKeyValAt F ck0 n (m + 1)
    rw [show m + 1 + n = m + (n + 1) by omega] at h
    exact h

theorem chainSeedAt_chainKeyValAt (F : ShaCompress) (ck0 : BitVec 256) {m : ℕ} (hm : m < 2 ^ 32)
    (counter : BitVec 32) (hle : m ≤ counter.toNat) :
    chainSeedAt F ⟨chainKeyValAt F ck0 m, BitVec.ofNat 32 m⟩ counter =
      some (msgSeedAt F ck0 counter.toNat) := by
  have hidx : (BitVec.ofNat 32 m).toNat = m := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  unfold chainSeedAt
  simp only [hidx, show ¬ counter.toNat < m by omega, ↓reduceIte, chainKeyAfter_chainKeyValAt,
    show m + (counter.toNat - m) = counter.toNat by omega]
  rfl

/-- Per-chain seed extracted by branch K1 of `snapshotMessageKeySeed` at counter `n`. -/
def k1Seed (F : ShaCompress) (rc : ReceiverChain) (n : BitVec 32) : Option (List (BitVec 8)) :=
  match rc.messageKeys.find? (·.counter == n) with
  | some mk => some mk.seed
  | none => rc.chainKey.bind fun ck => chainSeedAt F ck n

end CryptoGames.LibsignalSM.Proofs.SaltMismatch
