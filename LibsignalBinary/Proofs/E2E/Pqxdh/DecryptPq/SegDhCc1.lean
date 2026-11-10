/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhErr
import ProofLib.SepLogic.WPp

/-!
# Receiving Chain-Creation Helpers for `S3Spec`

Byte-packing and stack-splitting helpers around the first `RootKey::create_chain` call in `S3Spec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB

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

private theorem extractLsb'_shiftLeft8_or_zero (w : Nat) (hw : 8 ≤ w) (acc : BitVec w) (b : BitVec
    8) :
    ((acc <<< 8) ||| b.zeroExtend w).extractLsb' 0 8 = b := by
  ext i hi
  simp [hi]
  omega

private theorem extractLsb'_shiftLeft8_or_succ (w : Nat) (acc : BitVec w) (b : BitVec 8) (k : Nat)
    (hk : 8 * (k + 1) + 8 ≤ w) :
    ((acc <<< 8) ||| b.zeroExtend w).extractLsb' (8 * (k + 1)) 8 =
      acc.extractLsb' (8 * k) 8 := by
  ext i hi
  have h1 : ¬ (8 * (k + 1) + i < 8) := by omega
  have hltw : 8 * (k + 1) + i < w := by omega
  have hsub : 8 * (k + 1) + i - 8 = 8 * k + i := by omega
  have hb : b.getLsbD (8 * (k + 1) + i) = false := BitVec.getLsbD_of_ge b _ (by omega)
  simp [h1, hltw, hsub, hb]
  rfl

private def bytesOfBV {w : Nat} (n : Nat) (v : BitVec w) : List (BitVec 8) :=
  (List.range n).map fun j => v.extractLsb' (8 * j) 8

protected def packBV (w : Nat) (bs : List (BitVec 8)) : BitVec w :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend w) 0

private theorem bytesOfBV_packBV (w : Nat) :
    ∀ (bs : List (BitVec 8)), 8 * bs.length ≤ w → bytesOfBV bs.length (SegB.packBV w bs) = bs
  | [], _ => rfl
  | b :: bs, hlen => by
    have hlen_cons : 8 * (bs.length + 1) ≤ w := hlen
    unfold bytesOfBV
    rw [SegB.packBV, List.foldr_cons, ← SegB.packBV]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.mul_zero, extractLsb'_shiftLeft8_or_zero w (by omega), List.cons.injEq]
    refine ⟨trivial, ?_⟩
    have hmap :
        List.map ((fun j =>
          ((SegB.packBV w bs <<< 8) ||| b.zeroExtend w).extractLsb' (8 * j) 8) ∘ Nat.succ)
          (List.range bs.length) =
        bytesOfBV bs.length (SegB.packBV w bs) := by
      unfold bytesOfBV
      apply List.map_congr_left
      intro k hk
      rw [List.mem_range] at hk
      exact extractLsb'_shiftLeft8_or_succ w (SegB.packBV w bs) b k (by omega)
    rw [hmap]
    exact bytesOfBV_packBV w bs (by omega)

def pack64 (bs : List (BitVec 8)) : BitVec 64 := SegB.packBV 64 bs

theorem unpack64_pack64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    unpack64 (pack64 bs) = bs := by
  have h1 : unpack64 (pack64 bs) = bytesOfBV bs.length (SegB.packBV 64 bs) := by
    rw [h]
    unfold unpack64 bytesOfBV pack64
    rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
    rfl
  rw [h1]
  exact bytesOfBV_packBV 64 bs (by omega)

theorem pointsToBytes_8_eq_pointsTo64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ pack64 bs) := by
  rw [pointsTo64_eq_pointsToBytes, unpack64_pack64 bs h]

/-- Split any 32-byte slice `a ↦ₛ bs` (`bs.length = 32`) into four 64-bit points-to assertions
so `ldur q0` / `ldur q1` and `stp q0, q1` can step through `wp_steps` and then fold back to
`a' ↦ₛ bs` at any destination `a'`. -/
theorem pointsTo_32_as_four_64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ pack64 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ pack64 ((bs.drop 8).take 8)) ∗
       ((a + 16#64) ↦₆₄ pack64 ((bs.drop 16).take 8)) ∗
       ((a + 24#64) ↦₆₄ pack64 (bs.drop 24))) := by
  have h1 : (bs.take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h3 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have h4 : (bs.drop 24).length = 8 := by simp [h]
  have hsplit : bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
    conv_lhs => rw [← List.take_append_drop 8 bs]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 8)]
    rw [List.drop_drop]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 16)]
    rw [List.drop_drop]
  conv_lhs => rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, h1, h2, h3,
      pointsToBytes_8_eq_pointsTo64 a (bs.take 8) h1,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64) ((bs.drop 8).take 8) h2,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64 + 8#64) ((bs.drop 16).take 8) h3,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64 + 8#64 + 8#64) (bs.drop 24) h4,
      show a + 8#64 + 8#64 = a + 16#64 by bv_arith,
      show a + 16#64 + 8#64 = a + 24#64 by bv_arith]

theorem pointsTo64_zero_32 (a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 0#64) ∗
     ((a + 16#64) ↦₆₄ 0#64) ∗ ((a + 24#64) ↦₆₄ 0#64)) =
      (a ↦ₛ keyToBytes32 (0 : RootKey)) := by
  have h1 := pointsTo64_pair_eq_pointsTo128 a 0#64 0#64
  have h2 := pointsTo64_pair_eq_pointsTo128 (a + 16#64) 0#64 0#64
  have h0 : (0#64 ++ 0#64 : BitVec 128) = 0#128 := by decide
  rw [h0] at h1 h2
  rw [show a + 16#64 + 8#64 = a + 24#64 by bv_arith] at h2
  rw [← pointsTo128_zero_32 a, ← h1, ← h2]
  ac_rfl

/-- Split `optSenderChainBytes (some sc) pad` at `sp + 0x50` into the `1#32` tag at `sp + 0x50`,
the 32-byte public key at `sp + 0x54`, the 32-byte private key at `sp + 0x74`, and the 36-byte
`chainKeyBytes sc.chainKey` at `sp + 0x94`. -/
theorem optSenderChainBytes_some_split (sp : BitVec 64) (sc : SenderChain) (pad : List (BitVec 8)) :
    ((sp + 0x50#64) ↦ₛ optSenderChainBytes (some sc) pad) =
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey)) := by
  unfold optSenderChainBytes senderChainBytes
  dsimp only
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  have h1 : (leBytes 4 1).length = 4 := by decide
  have h1_eq : leBytes 4 1 = unpack32 1#32 := by decide
  have h2 : sc.ratchetKey.publicKey.bytes.toList.length = 32 := sc.ratchetKey.publicKey.bytes.2
  have h3 : sc.ratchetKey.privateKey.bytes.toList.length = 32 := sc.ratchetKey.privateKey.bytes.2
  rw [h1, h2, h3, h1_eq, ← pointsTo32_eq_pointsToBytes]
  have ha1 : sp + 0x50#64 + 4#64 = sp + 0x54#64 := by bv_arith
  have ha2 : sp + 0x54#64 + 32#64 = sp + 0x74#64 := by bv_arith
  have ha3 : sp + 0x74#64 + 32#64 = sp + 0x94#64 := by bv_arith
  rw [ha1, ha2, ha3]

/-- Split `stackAt sp tryDecryptSubStack` into `stackAt sp createChainStack` and the remaining
stack region below it. -/
theorem stackAt_subStack_createChain (sp : BitVec 64) :
    stackAt sp tryDecryptSubStack =
      (stackAt (sp - BitVec.ofNat 64 createChainStack) (tryDecryptSubStack - createChainStack) ∗
       stackAt sp createChainStack) := by
  dsimp only [stackAt]
  have hadd : BitVec.ofNat 64 tryDecryptSubStack =
      BitVec.ofNat 64 createChainStack + BitVec.ofNat 64 (tryDecryptSubStack - createChainStack) :=
        by
    decide
  rw [show sp - BitVec.ofNat 64 createChainStack - BitVec.ofNat 64 (tryDecryptSubStack -
      createChainStack) =
        sp - BitVec.ofNat 64 tryDecryptSubStack by rw [hadd]; bv_arith]
  exact memRegion_split'
    (b := sp - BitVec.ofNat 64 tryDecryptSubStack)
    (b' := sp - BitVec.ofNat 64 createChainStack)
    (n := tryDecryptSubStack - createChainStack)
    (k := createChainStack)
    (by decide) (by rw [hadd]; bv_arith) (by decide)

/-- All fields of `signalMessageAt A g a m` except `((a + 0x38#64) ↦ₛ
  m.senderRatchetKey.bytes.toList)`. -/
def signalMessageRestAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64) (m :
    SignalMessage) :
    SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

theorem signalMessageAt_senderRatchetKey (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (msg : SignalMessage) :
    signalMessageAt A g a msg =
      (((a + 0x38#64) ↦ₛ msg.senderRatchetKey.bytes.toList) ∗
       signalMessageRestAt A g a msg) := by
  unfold signalMessageAt signalMessageRestAt
  ac_rfl

/-- Split `memRegion (sp + 0x140) 0x440` for the first `RootKey::create_chain` call (`+0x544`):
exposes `memRegion (sp + 0x190) 72` (`ret`), four 64-bit slots at `sp + 0x390..0x3b0` (`ourA`),
and four 64-bit slots at `sp + 0x3b0..0x3d0` (`rkA`). -/
theorem split_140_for_cc1 (sp : BitVec 64) :
    memRegion (sp + 0x140#64) 0x440 =
      (memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 72 ∗
       memRegion (sp + 0x1d8#64) 0x1b8 ∗
       (∃∗ u390 : BitVec 64, (sp + 0x390#64) ↦₆₄ u390) ∗
       (∃∗ u398 : BitVec 64, (sp + 0x398#64) ↦₆₄ u398) ∗
       (∃∗ u3a0 : BitVec 64, (sp + 0x3a0#64) ↦₆₄ u3a0) ∗
       (∃∗ u3a8 : BitVec 64, (sp + 0x3a8#64) ↦₆₄ u3a8) ∗
       (∃∗ u3b0 : BitVec 64, (sp + 0x3b0#64) ↦₆₄ u3b0) ∗
       (∃∗ u3b8 : BitVec 64, (sp + 0x3b8#64) ↦₆₄ u3b8) ∗
       (∃∗ u3c0 : BitVec 64, (sp + 0x3c0#64) ↦₆₄ u3c0) ∗
       (∃∗ u3c8 : BitVec 64, (sp + 0x3c8#64) ↦₆₄ u3c8) ∗
       memRegion (sp + 0x3d0#64) 0x1b0) := by
  rw [memRegion_split' (b := sp + 0x140#64) (b' := sp + 0x190#64) (n := 0x50) (k :=
      0x3f0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x190#64) (b' := sp + 0x1d8#64) (n := 72) (k :=
        0x3a8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1d8#64) (b' := sp + 0x390#64) (n := 0x1b8) (k :=
        0x1f0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x390#64) (b' := sp + 0x398#64) (n := 8) (k :=
        0x1e8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x398#64) (b' := sp + 0x3a0#64) (n := 8) (k :=
        0x1e0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3a0#64) (b' := sp + 0x3a8#64) (n := 8) (k :=
        0x1d8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3a8#64) (b' := sp + 0x3b0#64) (n := 8) (k :=
        0x1d0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3b0#64) (b' := sp + 0x3b8#64) (n := 8) (k :=
        0x1c8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3b8#64) (b' := sp + 0x3c0#64) (n := 8) (k :=
        0x1c0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3c0#64) (b' := sp + 0x3c8#64) (n := 8) (k :=
        0x1b8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3c8#64) (b' := sp + 0x3d0#64) (n := 8) (k :=
        0x1b0) rfl (by bv_arith) (by decide),
      memRegion_eight (sp + 0x390#64), memRegion_eight (sp + 0x398#64),
      memRegion_eight (sp + 0x3a0#64), memRegion_eight (sp + 0x3a8#64),
      memRegion_eight (sp + 0x3b0#64), memRegion_eight (sp + 0x3b8#64),
      memRegion_eight (sp + 0x3c0#64), memRegion_eight (sp + 0x3c8#64)]

/-- Fold the temporary 32-byte copies at `sp + 0x390..0x3b0` and `sp + 0x3b0..0x3d0` back into
`memRegion (sp + 0x1d8) 0x3a8` after `RootKey::create_chain` #1 returns. -/
theorem fold_390_3b0_to_memRegion (sp : BitVec 64) (bs1 bs2 : List (BitVec 8))
    (h1 : bs1.length = 32) (h2 : bs2.length = 32) :
    (memRegion (sp + 0x1d8#64) 0x1b8 ∗
     ((sp + 0x390#64) ↦ₛ bs1) ∗
     ((sp + 0x3b0#64) ↦ₛ bs2) ∗
     memRegion (sp + 0x3d0#64) 0x1b0) ⊢
    memRegion (sp + 0x1d8#64) 0x3a8 := by
  have e1 := pointsToBytes_entails_memRegion (sp + 0x390#64) bs1
  rw [h1] at e1
  have e2 := pointsToBytes_entails_memRegion (sp + 0x3b0#64) bs2
  rw [h2] at e2
  rw [memRegion_split' (b := sp + 0x1d8#64) (b' := sp + 0x390#64) (n := 0x1b8) (k :=
      0x1f0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x390#64) (b' := sp + 0x3b0#64) (n := 32) (k :=
        0x1d0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3b0#64) (b' := sp + 0x3d0#64) (n := 32) (k :=
        0x1b0) rfl (by bv_arith) (by decide)]
  exact sepConj_mono_right (sepConj_mono e1 (sepConj_mono_left e2))

theorem rk_ne_zero (sp0 sp : BitVec 64) (hsp : sp = sp0 - 1504#64) (hb : 2 ^ 18 ≤ sp0.toNat) :
    sp + 0x3b0#64 ≠ 0#64 ∧ sp + 0x4a0#64 ≠ 0#64 := by
  subst hsp; constructor <;> bv_omega

def pack32 (bs : List (BitVec 8)) : BitVec 32 := SegB.packBV 32 bs

theorem unpack32_pack32 (bs : List (BitVec 8)) (h : bs.length = 4) :
    unpack32 (pack32 bs) = bs := by
  have h1 : unpack32 (pack32 bs) = bytesOfBV bs.length (SegB.packBV 32 bs) := by
    rw [h]
    unfold unpack32 bytesOfBV pack32
    rw [show List.range 4 = [0, 1, 2, 3] from rfl]
    rfl
  rw [h1]
  exact bytesOfBV_packBV 32 bs (by omega)

theorem pointsToBytes_4_eq_pointsTo32 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 4) :
    (a ↦ₛ bs) = (a ↦₃₂ pack32 bs) := by
  rw [pointsTo32_eq_pointsToBytes, unpack32_pack32 bs h]

theorem pointsTo_16_as_two_64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 16) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ pack64 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ pack64 (bs.drop 8))) := by
  have h1 : (bs.take 8).length = 8 := by simp [h]
  have h2 : (bs.drop 8).length = 8 := by simp [h]
  conv_lhs => rw [← List.take_append_drop 8 bs]
  rw [pointsToBytes_append, h1,
      pointsToBytes_8_eq_pointsTo64 a (bs.take 8) h1,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64) (bs.drop 8) h2]

theorem pointsTo_32_as_4_8_8_8_4 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₃₂ pack32 (bs.take 4)) ∗
       ((a + 4#64) ↦₆₄ pack64 ((bs.drop 4).take 8)) ∗
       ((a + 12#64) ↦₆₄ pack64 ((bs.drop 12).take 8)) ∗
       ((a + 20#64) ↦₆₄ pack64 ((bs.drop 20).take 8)) ∗
       ((a + 28#64) ↦₃₂ pack32 (bs.drop 28))) := by
  have h1 : (bs.take 4).length = 4 := by simp [h]
  have h2 : ((bs.drop 4).take 8).length = 8 := by simp [h]
  have h3 : ((bs.drop 12).take 8).length = 8 := by simp [h]
  have h4 : ((bs.drop 20).take 8).length = 8 := by simp [h]
  have h5 : (bs.drop 28).length = 4 := by simp [h]
  have hsplit : bs =
      bs.take 4 ++ ((bs.drop 4).take 8 ++ ((bs.drop 12).take 8 ++ ((bs.drop 20).take 8 ++ bs.drop
      28))) := by
    conv_lhs => rw [← List.take_append_drop 4 bs]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 4)]
    rw [List.drop_drop]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 12)]
    rw [List.drop_drop]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 20)]
    rw [List.drop_drop]
  conv_lhs => rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      h1, h2, h3, h4,
      pointsToBytes_4_eq_pointsTo32 a (bs.take 4) h1,
      pointsToBytes_8_eq_pointsTo64 (a + 4#64) ((bs.drop 4).take 8) h2,
      pointsToBytes_8_eq_pointsTo64 (a + 4#64 + 8#64) ((bs.drop 12).take 8) h3,
      pointsToBytes_8_eq_pointsTo64 (a + 4#64 + 8#64 + 8#64) ((bs.drop 20).take 8) h4,
      pointsToBytes_4_eq_pointsTo32 (a + 4#64 + 8#64 + 8#64 + 8#64) (bs.drop 28) h5,
      show a + 4#64 + 8#64 = a + 12#64 by bv_arith,
      show a + 12#64 + 8#64 = a + 20#64 by bv_arith,
      show a + 20#64 + 8#64 = a + 28#64 by bv_arith]

theorem pointsTo_36_as_8_8_4_8_8 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 36) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ pack64 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ pack64 ((bs.drop 8).take 8)) ∗
       ((a + 16#64) ↦₃₂ pack32 ((bs.drop 16).take 4)) ∗
       ((a + 20#64) ↦₆₄ pack64 ((bs.drop 20).take 8)) ∗
       ((a + 28#64) ↦₆₄ pack64 (bs.drop 28))) := by
  have h1 : (bs.take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h3 : ((bs.drop 16).take 4).length = 4 := by simp [h]
  have h4 : ((bs.drop 20).take 8).length = 8 := by simp [h]
  have h5 : (bs.drop 28).length = 8 := by simp [h]
  have hsplit : bs =
      bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 4 ++ ((bs.drop 20).take 8 ++ bs.drop
      28))) := by
    conv_lhs => rw [← List.take_append_drop 8 bs]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 8)]
    rw [List.drop_drop]
    congr 1
    conv_lhs => rw [← List.take_append_drop 4 (bs.drop 16)]
    rw [List.drop_drop]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 20)]
    rw [List.drop_drop]
  conv_lhs => rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      h1, h2, h3, h4,
      pointsToBytes_8_eq_pointsTo64 a (bs.take 8) h1,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64) ((bs.drop 8).take 8) h2,
      pointsToBytes_4_eq_pointsTo32 (a + 8#64 + 8#64) ((bs.drop 16).take 4) h3,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64 + 8#64 + 4#64) ((bs.drop 20).take 8) h4,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64 + 8#64 + 4#64 + 8#64) (bs.drop 28) h5,
      show a + 8#64 + 8#64 = a + 16#64 by bv_arith,
      show a + 16#64 + 4#64 = a + 20#64 by bv_arith,
      show a + 20#64 + 8#64 = a + 28#64 by bv_arith]

theorem pointsTo8_eq_pointsToBytes1 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem vec32_toList_split_ends (v : List.Vector (BitVec 8) 32) :
    v.toList =
      [v.get ⟨0, by decide⟩] ++ ((v.toList.drop 1).take 30 ++ [v.get ⟨31, by decide⟩]) := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    first | (dsimp [List.Vector.toList, List.Vector.get]; rfl) | cases hl

theorem vec32_clampScalar_toList_eq (v : List.Vector (BitVec 8) 32) :
    (Ratchet.clampScalar v).toList =
      [v.get ⟨0, by decide⟩ &&& 0xf8#8] ++
        ((v.toList.drop 1).take 30 ++ [(v.get ⟨31, by decide⟩ &&& 0x7f#8) ||| 0x40#8]) := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    first | (dsimp [List.Vector.toList, List.Vector.get, Ratchet.clampScalar,
      List.Vector.set]; rfl) | cases hl

theorem pointsTo_vec32_split_ends (a : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    (a ↦ₛ v.toList) =
      ((a ↦₈ v.get ⟨0, by decide⟩) ∗
       ((a + 1#64) ↦ₛ (v.toList.drop 1).take 30) ∗
       ((a + 31#64) ↦₈ v.get ⟨31, by decide⟩)) := by
  have hmid : ((v.toList.drop 1).take 30).length = 30 := by simp
  conv_lhs => rw [vec32_toList_split_ends v]
  rw [pointsToBytes_append, pointsToBytes_append,
      show ([v.get ⟨0, by decide⟩] : List (BitVec 8)).length = 1 from rfl, hmid,
      ← pointsTo8_eq_pointsToBytes1 a,
      ← pointsTo8_eq_pointsToBytes1 (a + 1#64 + 30#64),
      show a + 1#64 + 30#64 = a + 31#64 by bv_arith]

theorem pointsTo_vec32_clamp_fold (a : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    ((a ↦₈ (v.get ⟨0, by decide⟩ &&& 0xf8#8)) ∗
     ((a + 1#64) ↦ₛ (v.toList.drop 1).take 30) ∗
     ((a + 31#64) ↦₈ ((v.get ⟨31, by decide⟩ &&& 0x7f#8) ||| 0x40#8))) =
      (a ↦ₛ (Ratchet.clampScalar v).toList) := by
  have hmid : ((v.toList.drop 1).take 30).length = 30 := by simp
  conv_rhs => rw [vec32_clampScalar_toList_eq v]
  rw [pointsToBytes_append, pointsToBytes_append,
      show ([v.get ⟨0, by decide⟩ &&& 0xf8#8] : List (BitVec 8)).length = 1 from rfl, hmid,
      ← pointsTo8_eq_pointsToBytes1 a,
      ← pointsTo8_eq_pointsToBytes1 (a + 1#64 + 30#64),
      show a + 1#64 + 30#64 = a + 31#64 by bv_arith]

theorem keyToBytes32_bytesToKey32_local (bs : List (BitVec 8)) (h : bs.length = 32) :
    keyToBytes32 (bytesToKey32 bs) = bs := by
  have h1 : keyToBytes32 (bytesToKey32 bs) = bytesOfBV bs.length (SegB.packBV 256 bs) := by
    rw [h]
    unfold keyToBytes32 bytesOfBV bytesToKey32 SegB.packBV
    rw [List.ofFn_eq_map]
    rfl
  rw [h1]
  exact bytesOfBV_packBV 256 bs (by omega)

theorem keyVec_coinsOf_toList (rest : List (BitVec 8)) :
    (Ratchet.keyToBytesVec32 (coinsOf rest)).toList = (rest ++ List.replicate 32 0#8).take 32 := by
  unfold Ratchet.keyToBytesVec32 coinsOf
  dsimp only [List.Vector.toList]
  apply keyToBytes32_bytesToKey32_local
  rw [List.length_take, List.length_append, List.length_replicate]
  omega

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB
