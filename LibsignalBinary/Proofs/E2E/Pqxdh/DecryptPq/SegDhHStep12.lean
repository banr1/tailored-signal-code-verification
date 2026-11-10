/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHPack
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHEvict
import ProofLib.SepLogic.WPp

/-!
# `ChainKey` Cell and 32-Byte Region Helpers for `S3CommitSpec`

Decomposition lemmas between 32-byte `ChainKey` byte slices, four 64-bit cells, and `memRegion`
blocks for sub-segments 1 and 2 of `S3CommitSpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem pointsToBytes_chainKey_eq_cells (a : BitVec 64) (ck : ChainKey) :
    let bs := chainKeyBytes ck
    (a ↦ₛ bs) =
      (a ↦₆₄ pack64 (bs.take 8)) ∗
      ((a + 8#64) ↦₆₄ pack64 ((bs.drop 8).take 8)) ∗
      ((a + 16#64) ↦₃₂ pack32 ((bs.drop 16).take 4)) ∗
      ((a + 20#64) ↦₆₄ pack64 ((bs.drop 20).take 8)) ∗
      ((a + 28#64) ↦₆₄ pack64 (bs.drop 28)) := by
  intro bs
  have hlen : bs.length = 36 := chainKeyBytes_length ck
  have h16 : (bs.take 16).length = 16 := by simp [hlen]
  have h4 : ((bs.drop 16).take 4).length = 4 := by simp [hlen]
  have h20 : (bs.drop 20).length = 16 := by simp [hlen]
  rw [pointsToBytes_chainKey_split a ck,
      pointsToBytes_16_eq_pointsTo64 a h16,
      pointsToBytes_4_eq_pointsTo32 (a + 16#64) h4,
      pointsToBytes_16_eq_pointsTo64 (a + 20#64) h20]
  have ht1 : (bs.take 16).take 8 = bs.take 8 := by rw [List.take_take]; rfl
  have ht2 : (bs.take 16).drop 8 = (bs.drop 8).take 8 := by
    rw [List.drop_take]
  have ht3 : (bs.drop 20).drop 8 = bs.drop 28 := by simp [List.drop_drop]
  have ha28 := add_assoc_const a 20#64 8#64 28#64
  rw [ht1, ht2, ht3, ha28]
  ac_rfl

theorem elim_memRegion_4 {m : Memory} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion a 4 ∗ R) :
    ∃ v : BitVec 32, m ⊨ (a ↦₃₂ v) ∗ R := by
  rw [memRegion_four, sepExists_sepConj_left, satisfies_sepExists] at h
  exact h

theorem cell32_to_memRegion_4 (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) ⊢ memRegion a 4 := by
  rw [memRegion_four]
  exact Entails.sepExists_right v (Entails.refl _)

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH
