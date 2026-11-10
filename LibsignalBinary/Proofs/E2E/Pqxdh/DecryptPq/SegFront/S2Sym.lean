/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import ProofLib.SepLogic.WPp

/-!
# Receiver-Chain Lookup Segment Helpers (`S2Spec`)

Framing and branch-dispatch helpers around `RatchetState::find_receiver_chain_key`
(`+0x2a4 → +0x3e4 / +0x500 / +0x30c`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Segment S2 (`+0x2a4 → +0x3e4 / +0x500 / +0x30c`) -/

theorem exists_words20_of_length_20 {bs : List (BitVec 8)} (h : bs.length = 20) :
    ∃ (w0 : BitVec 32) (w1 w2 : BitVec 64),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) = (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₆₄ w1) ∗ ((a + 12#64) ↦₆₄ w2) := by
  have h0 : (bs.take 4).length = 4 := by simp [h]
  have h1 : (bs.drop 4).length = 16 := by simp [h]
  obtain ⟨w0, hw0⟩ := exists_word32_of_length_4 h0
  obtain ⟨w1, w2, hw12⟩ := exists_words16_of_length_16 h1
  refine ⟨w0, w1, w2, fun a => ?_⟩
  have hsplit : bs = bs.take 4 ++ bs.drop 4 := (List.take_append_drop 4 bs).symm
  rw [hsplit, pointsToBytes_append, h0, hw0 a, hw12 (a + 4#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem chainKeyBytes_length (ck : ChainKey) : (chainKeyBytes ck).length = 36 := by
  simp [chainKeyBytes, keyToBytes32, leBytes]

theorem realign_20_bytes (a : BitVec 64) (u : BitVec 32) (x y : BitVec 64) :
    ((a ↦₃₂ u) ∗ ((a + 4#64) ↦₆₄ x) ∗ ((a + 12#64) ↦₆₄ y)) =
      ((a ↦₆₄ (x.extractLsb' 0 32 ++ u)) ∗
       ((a + 8#64) ↦₆₄ (y.extractLsb' 0 32 ++ x.extractLsb' 32 32)) ∗
       ((a + 16#64) ↦₃₂ y.extractLsb' 32 32)) := by
  rw [pointsTo64_split32 (a + 4#64) x, pointsTo64_split32 (a + 12#64) y,
      ← pointsTo32_pair a u (x.extractLsb' 0 32),
      ← pointsTo32_pair (a + 8#64) (x.extractLsb' 32 32) (y.extractLsb' 0 32)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

def trRestAt (A : RustAlloc) (t : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  ⌜∀ sc, tr.ratchet.senderChain = some sc →
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
    vecU8At A (t + 0xb0#64) G.pq.cap G.pq.ptr tr.pqrState ∗
    ((t + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
    ((t + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)

theorem trAt_eq_ratchetAt_trRestAt (A : RustAlloc) (t : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A t G tr = ratchetAt A t G.ratchet tr.ratchet ∗ trRestAt A t G tr := by
  unfold trAt trRestAt; ac_rfl

def signalMessageRestAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

theorem signalMessageAt_eq_srk_rest (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗ signalMessageRestAt A g a m := by
  unfold signalMessageAt signalMessageRestAt; ac_rfl

theorem memRegion_0x140_split_findReceiverChainKey (sp : BitVec 64) :
    memRegion (sp + 0x140#64) 0x440 =
      memRegion (sp + 0x140#64) 0x50 ∗
      memRegion (sp + 0x190#64) 40 ∗
      memRegion (sp + 0x1b8#64) 0x3c8 := by
  rw [memRegion_split (sp + 0x140#64) 0x50 0x3f0 (by decide),
      show sp + 0x140#64 + BitVec.ofNat 64 0x50 = sp + 0x190#64 by bv_omega,
      memRegion_split (sp + 0x190#64) 40 0x3c8 (by decide),
      show sp + 0x190#64 + BitVec.ofNat 64 40 = sp + 0x1b8#64 by bv_omega]

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
