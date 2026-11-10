/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHChain
import ProofLib.SepLogic.WPp

/-!
# Byte Packing, Address Arithmetic, and `ReachesOrPanic` Combinators for `S3CommitSpec`

Little-endian byte/word packing lemmas, stack-region splitting helpers, and `ReachesOrPanic`
composition combinators for `S3CommitSpec`.
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

/-! ## 1. Byte/Word Packing and Layout Splitting Helpers -/

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
    ∀ (bs : List (BitVec 8)), 8 * bs.length ≤ w → bytesOfBV bs.length (SegBH.packBV w bs) = bs
  | [], _ => rfl
  | b :: bs, hlen => by
    have hlen_cons : 8 * (bs.length + 1) ≤ w := hlen
    unfold bytesOfBV
    rw [SegBH.packBV, List.foldr_cons, ← SegBH.packBV]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.mul_zero, extractLsb'_shiftLeft8_or_zero w (by omega), List.cons.injEq]
    refine ⟨trivial, ?_⟩
    have hmap :
        List.map ((fun j =>
          ((SegBH.packBV w bs <<< 8) ||| b.zeroExtend w).extractLsb' (8 * j) 8) ∘ Nat.succ)
          (List.range bs.length) =
        bytesOfBV bs.length (SegBH.packBV w bs) := by
      unfold bytesOfBV
      apply List.map_congr_left
      intro k hk
      rw [List.mem_range] at hk
      exact extractLsb'_shiftLeft8_or_succ w (SegBH.packBV w bs) b k (by omega)
    rw [hmap]
    exact bytesOfBV_packBV w bs (by omega)

def pack64 (bs : List (BitVec 8)) : BitVec 64 := SegBH.packBV 64 bs

def pack32 (bs : List (BitVec 8)) : BitVec 32 := SegBH.packBV 32 bs

theorem unpack64_pack64 {bs : List (BitVec 8)} (h : bs.length = 8) :
    unpack64 (pack64 bs) = bs := by
  have h1 : unpack64 (pack64 bs) = bytesOfBV bs.length (SegBH.packBV 64 bs) := by
    rw [h]
    unfold unpack64 bytesOfBV pack64
    rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
    rfl
  rw [h1]
  exact bytesOfBV_packBV 64 bs (by omega)

theorem unpack32_pack32 {bs : List (BitVec 8)} (h : bs.length = 4) :
    unpack32 (pack32 bs) = bs := by
  have h1 : unpack32 (pack32 bs) = bytesOfBV bs.length (SegBH.packBV 32 bs) := by
    rw [h]
    unfold unpack32 bytesOfBV pack32
    rw [show List.range 4 = [0, 1, 2, 3] from rfl]
    rfl
  rw [h1]
  exact bytesOfBV_packBV 32 bs (by omega)

theorem pointsToBytes_8_eq_pointsTo64 (a : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ pack64 bs) := by
  rw [pointsTo64_eq_pointsToBytes, unpack64_pack64 h]

theorem pointsToBytes_4_eq_pointsTo32 (a : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 4) :
    (a ↦ₛ bs) = (a ↦₃₂ pack32 bs) := by
  rw [pointsTo32_eq_pointsToBytes, unpack32_pack32 h]

theorem pointsToBytes_16_eq_pointsTo64 (a : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 16) :
    (a ↦ₛ bs) =
      (a ↦₆₄ pack64 (bs.take 8)) ∗
      ((a + 8#64) ↦₆₄ pack64 (bs.drop 8)) := by
  have hsplit : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  have h0 : (bs.take 8).length = 8 := by simp [h]
  have h1 : (bs.drop 8).length = 8 := by simp [h]
  conv_lhs => rw [hsplit]
  rw [pointsToBytes_append, h0,
      pointsToBytes_8_eq_pointsTo64 a h0,
      pointsToBytes_8_eq_pointsTo64 _ h1]

theorem pointsToBytes_32_eq_pointsTo64 (a : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    (a ↦ₛ bs) =
      (a ↦₆₄ pack64 (bs.take 8)) ∗
      ((a + 8#64) ↦₆₄ pack64 ((bs.drop 8).take 8)) ∗
      ((a + 16#64) ↦₆₄ pack64 ((bs.drop 16).take 8)) ∗
      ((a + 24#64) ↦₆₄ pack64 (bs.drop 24)) := by
  have hsplit :
      bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
    have h24 : bs.drop 24 = (bs.drop 16).drop 8 := by simp [List.drop_drop]
    have h16 : bs.drop 16 = (bs.drop 8).drop 8 := by simp [List.drop_drop]
    rw [h24, List.take_append_drop, h16, List.take_append_drop, List.take_append_drop]
  have h0 : (bs.take 8).length = 8 := by simp [h]
  have h1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have h3 : (bs.drop 24).length = 8 := by simp [h]
  conv_lhs => rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      h0, h1, h2,
      pointsToBytes_8_eq_pointsTo64 a h0,
      pointsToBytes_8_eq_pointsTo64 _ h1,
      pointsToBytes_8_eq_pointsTo64 _ h2,
      pointsToBytes_8_eq_pointsTo64 _ h3]
  have ha8 : a + BitVec.ofNat 64 8 = a + 8#64 := rfl
  have ha16 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 16#64 := by bv_omega
  have ha24 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 24#64 :=
      by bv_omega
  rw [ha24, ha16, ha8]

theorem pointsToBytes_32_eq_4_8_8_8_4 (a : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    (a ↦ₛ bs) =
      (a ↦₃₂ pack32 (bs.take 4)) ∗
      ((a + 4#64) ↦₆₄ pack64 ((bs.drop 4).take 8)) ∗
      ((a + 12#64) ↦₆₄ pack64 ((bs.drop 12).take 8)) ∗
      ((a + 20#64) ↦₆₄ pack64 ((bs.drop 20).take 8)) ∗
      ((a + 28#64) ↦₃₂ pack32 (bs.drop 28)) := by
  have hsplit :
      bs = bs.take 4 ++ (((bs.drop 4).take 8) ++ (((bs.drop 12).take 8) ++
        (((bs.drop 20).take 8) ++ bs.drop 28))) := by
    have h28 : bs.drop 28 = (bs.drop 20).drop 8 := by simp [List.drop_drop]
    have h20 : bs.drop 20 = (bs.drop 12).drop 8 := by simp [List.drop_drop]
    have h12 : bs.drop 12 = (bs.drop 4).drop 8 := by simp [List.drop_drop]
    rw [h28, List.take_append_drop, h20, List.take_append_drop, h12,
        List.take_append_drop, List.take_append_drop]
  have h0 : (bs.take 4).length = 4 := by simp [h]
  have h1 : ((bs.drop 4).take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 12).take 8).length = 8 := by simp [h]
  have h3 : ((bs.drop 20).take 8).length = 8 := by simp [h]
  have h4 : (bs.drop 28).length = 4 := by simp [h]
  conv_lhs => rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      h0, h1, h2, h3,
      pointsToBytes_4_eq_pointsTo32 a h0,
      pointsToBytes_8_eq_pointsTo64 _ h1,
      pointsToBytes_8_eq_pointsTo64 _ h2,
      pointsToBytes_8_eq_pointsTo64 _ h3,
      pointsToBytes_4_eq_pointsTo32 _ h4]
  have ha4 : a + BitVec.ofNat 64 4 = a + 4#64 := rfl
  have ha12 : a + BitVec.ofNat 64 4 + BitVec.ofNat 64 8 = a + 12#64 := by bv_omega
  have ha20 : a + BitVec.ofNat 64 4 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 20#64 :=
      by bv_omega
  have ha28 : a + BitVec.ofNat 64 4 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 =
      a + 28#64 := by bv_omega
  rw [ha28, ha20, ha12, ha4]

theorem chainKeyBytes_length (ck : ChainKey) : (chainKeyBytes ck).length = 36 := by
  simp [chainKeyBytes, keyToBytes32, leBytes]

theorem pointsToBytes_chainKey_split (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) =
      (a ↦ₛ (chainKeyBytes ck).take 16) ∗
      ((a + 16#64) ↦ₛ ((chainKeyBytes ck).drop 16).take 4) ∗
      ((a + 20#64) ↦ₛ (chainKeyBytes ck).drop 20) := by
  set bs := chainKeyBytes ck
  have h : bs.length = 36 := chainKeyBytes_length ck
  have hsplit : bs = bs.take 16 ++ ((bs.drop 16).take 4 ++ bs.drop 20) := by
    have h20 : bs.drop 20 = (bs.drop 16).drop 4 := by simp [List.drop_drop]
    rw [h20, List.take_append_drop, List.take_append_drop]
  have h0 : (bs.take 16).length = 16 := by simp [h]
  have h1 : ((bs.drop 16).take 4).length = 4 := by simp [h]
  conv_lhs => rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, h0, h1]
  have ha16 : a + BitVec.ofNat 64 16 = a + 16#64 := rfl
  have ha20 : a + BitVec.ofNat 64 16 + BitVec.ofNat 64 4 = a + 20#64 := by bv_omega
  rw [ha20, ha16]

theorem pointsToBytes_chainKey_take20 (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ (chainKeyBytes ck).take 20) =
      (a ↦ₛ (chainKeyBytes ck).take 16) ∗
      ((a + 16#64) ↦ₛ ((chainKeyBytes ck).drop 16).take 4) := by
  set bs := chainKeyBytes ck
  have h : bs.length = 36 := chainKeyBytes_length ck
  have hsplit : bs.take 20 = bs.take 16 ++ (bs.drop 16).take 4 := by
    have h16_4 : (20 : Nat) = 16 + 4 := rfl
    rw [h16_4, List.take_add]
  have h0 : (bs.take 16).length = 16 := by simp [h]
  rw [hsplit, pointsToBytes_append, h0]

theorem leBytes_four_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  unfold leBytes unpack32 BitVec.extractLsb'
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map, Nat.shiftRight_eq_div_pow]
  rfl

theorem chainKeyBytes_pointsTo (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) =
      (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [pointsToBytes_append, hlen, leBytes_four_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

theorem optSenderChainBytes_some_pointsTo (a : BitVec 64) (sc : SenderChain) (pad : List (BitVec
    8)) :
    (a ↦ₛ optSenderChainBytes (some sc) pad) =
      (a ↦₃₂ 1#32) ∗
      ((a + 4#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((a + 36#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((a + 68#64) ↦ₛ chainKeyBytes sc.chainKey) := by
  unfold optSenderChainBytes senderChainBytes
  dsimp only
  have h1 : leBytes 4 1 = unpack32 1#32 := leBytes_four_eq_unpack32 1#32
  have hlen0 : (leBytes 4 1).length = 4 := by simp [leBytes]
  have hlen1 : sc.ratchetKey.publicKey.bytes.toList.length = 32 :=
      sc.ratchetKey.publicKey.bytes.toList_length
  have hlen2 : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
      sc.ratchetKey.privateKey.bytes.toList_length
  rw [List.append_assoc,
      pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      hlen0, hlen1, hlen2, h1, ← pointsTo32_eq_pointsToBytes]
  have ha4 : a + BitVec.ofNat 64 4 = a + 4#64 := rfl
  have ha36 : a + BitVec.ofNat 64 4 + BitVec.ofNat 64 32 = a + 36#64 := by bv_omega
  have ha68 : a + BitVec.ofNat 64 4 + BitVec.ofNat 64 32 + BitVec.ofNat 64 32 = a + 68#64 :=
      by bv_omega
  rw [ha68, ha36, ha4]

theorem saturating_sub_one_u32 (idx : BitVec 32) :
    idx - (if idx == 0#32 then 0#32 else 1#32) = BitVec.ofNat 32 (idx.toNat - 1) := by
  by_cases h0 : idx = 0#32
  · subst h0; rfl
  · have hbeq : (idx == 0#32) = false := beq_false_of_ne h0
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    have hpos : 1 ≤ idx.toNat := by
      rcases Nat.eq_zero_or_pos idx.toNat with hz | hp
      · exfalso; exact h0 (BitVec.eq_of_toNat_eq hz)
      · exact hp
    apply BitVec.eq_of_toNat_eq
    have hlt : idx.toNat < 2 ^ 32 := idx.isLt
    rw [BitVec.toNat_sub_of_le hpos, BitVec.toNat_ofNat]
    change idx.toNat - 1 = (idx.toNat - 1) % 2 ^ 32
    omega

theorem publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [PublicKey.serialize]

theorem publicKey_serialize_ne_nil (pk : PublicKey) : pk.serialize ≠ [] := by
  simp [PublicKey.serialize]

theorem publicKey_deserialize_serialize (pk : PublicKey) :
    PublicKey.deserialize pk.serialize = .ok pk := by
  unfold PublicKey.serialize PublicKey.deserialize
  have hlen : pk.bytes.toList.length = 32 := pk.bytes.toList_length
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, hlen, Nat.le_refl, ↓reduceDIte,
    Except.ok.injEq]
  rcases pk with ⟨⟨bs, hbs⟩⟩
  simp [List.take_of_length_le (Nat.le_of_eq hbs)]

theorem pointsToBytes_chainBytes_eq_13_cells (a : BitVec 64)
    (gc : ChainGhost × ReceiverChain) {pad : List (BitVec 8)}
    (hpad : pad.length = optChainKeyPadLen gc.2.chainKey) :
    let tail := optChainKeyTailBytes gc.1.ck gc.2.chainKey pad
    (a ↦ₛ chainBytes gc pad) =
      (a ↦₆₄ gc.1.srk.cap) ∗
      ((a + 8#64) ↦₆₄ gc.1.srk.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
      ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
      ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
      ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length) ∗
      ((a + 72#64) ↦₆₄ pack64 (tail.take 8)) ∗
      ((a + 80#64) ↦₆₄ pack64 ((tail.drop 8).take 8)) ∗
      ((a + 88#64) ↦₆₄ pack64 ((tail.drop 16).take 8)) ∗
      ((a + 96#64) ↦₆₄ pack64 (tail.drop 24)) := by
  intro tail
  unfold chainBytes
  rw [pointsToBytes_append, chainHeaderBytes_length, pointsToBytes_chainHeaderBytes]
  have htail_len : tail.length = 32 := optChainKeyTailBytes_length gc.1.ck gc.2.chainKey hpad
  have ha72 : a + BitVec.ofNat 64 72 = a + 72#64 := rfl
  rw [ha72, show optChainKeyTailBytes gc.1.ck gc.2.chainKey pad = tail from rfl,
      pointsToBytes_32_eq_pointsTo64 (a + 72#64) htail_len]
  unfold vecHeader
  have h24_8 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have h24_16 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  have h48_8 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have h48_16 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  have h72_8 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
  have h72_16 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
  have h72_24 : a + 72#64 + 24#64 = a + 96#64 := by bv_omega
  rw [h24_8, h24_16, h48_8, h48_16, h72_8, h72_16, h72_24]
  ac_rfl

theorem vecU8Buf_cap_add_one_ne_zero (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap + 1#64 ≠ 0#64⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  apply Entails.pure_left
  rintro ⟨hlen, hlt, hptr⟩
  have hne : cap + 1#64 ≠ 0#64 := by
    have : cap.toNat < 2 ^ 63 := hlt
    bv_omega
  exact Entails.pure_right hne (Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _))

theorem chainHeap_srk_cap_ne_zero (A : RustAlloc) (gc : ChainGhost × ReceiverChain) :
    chainHeap A gc ⊢ ⌜gc.1.srk.cap + 1#64 ≠ 0#64⌝ ∗ chainHeap A gc := by
  unfold chainHeap
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (vecU8Buf_cap_add_one_ne_zero A gc.1.srk.cap
      gc.1.srk.ptr gc.1.srk.bytes))) ?_
  exact Entails.of_eq (by ac_rfl)

def newChainGhost (srkPtr ckPtr : BitVec 64) (srk : PublicKey) : ChainGhost :=
  { srk := ⟨33#64, srkPtr, srk.serialize⟩
    priv := ⟨0#64, 1#64, []⟩
    mkCap := 0#64
    mkPtr := 8#64
    keys := []
    ck := ⟨32#64, ckPtr⟩ }

def newReceiverChain (srk : PublicKey) (rck : ChainKey) : ReceiverChain :=
  { senderRatchetKey := srk
    chainKey := some rck
    messageKeys := [] }

theorem vecU8Buf_33_of_live (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hptr : ptr ≠ 0) (hlen : bs.length = 33) :
    (A.live ptr 33 1 ∗ (ptr ↦ₛ bs)) ⊢ vecU8Buf A 33#64 ptr bs := by
  change (A.live ptr 33 1 ∗ (ptr ↦ₛ bs)) ⊢
    ⌜bs.length ≤ 33 ∧ 33 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (A.live ptr 33 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (33 - bs.length))
  have hrem : 33 - bs.length = 0 := by omega
  rw [hrem, memRegion_zero, sepConj_emp]
  exact Entails.pure_right ⟨by omega, by decide, hptr⟩ (Entails.refl _)

theorem chainAt_newChain_of_cells (A : RustAlloc) (slot srkPtr ckPtr : BitVec 64)
    (srk : PublicKey) (rck : ChainKey) {pad : List (BitVec 8)}
    (hpad : pad.length = 4) (hsrk_ne : srkPtr ≠ 0) :
    let tail := optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad
    ((slot ↦₆₄ 33#64) ∗
     ((slot + 8#64) ↦₆₄ srkPtr) ∗
     ((slot + 16#64) ↦₆₄ 33#64) ∗
     ((slot + 24#64) ↦₆₄ 0#64) ∗
     ((slot + 32#64) ↦₆₄ 1#64) ∗
     ((slot + 40#64) ↦₆₄ 0#64) ∗
     ((slot + 48#64) ↦₆₄ 0#64) ∗
     ((slot + 56#64) ↦₆₄ 8#64) ∗
     ((slot + 64#64) ↦₆₄ 0#64) ∗
     ((slot + 72#64) ↦₆₄ pack64 (tail.take 8)) ∗
     ((slot + 80#64) ↦₆₄ pack64 ((tail.drop 8).take 8)) ∗
     ((slot + 88#64) ↦₆₄ pack64 ((tail.drop 16).take 8)) ∗
     ((slot + 96#64) ↦₆₄ pack64 (tail.drop 24)) ∗
     (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
     optChainKeyHeap A ⟨32#64, ckPtr⟩ (some rck)) ⊢
      chainAt A (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck) slot := by
  intro tail
  set gc := (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck)
  have hpad' : pad.length = optChainKeyPadLen gc.2.chainKey := hpad
  have hcells := pointsToBytes_chainBytes_eq_13_cells slot gc hpad'
  have hser_len : srk.serialize.length = 33 := publicKey_serialize_length srk
  dsimp only [gc, newChainGhost, newReceiverChain] at hcells
  rw [hser_len] at hcells
  change slot ↦ₛ chainBytes gc pad =
    ((slot ↦₆₄ 33#64) ∗
     ((slot + 8#64) ↦₆₄ srkPtr) ∗
     ((slot + 16#64) ↦₆₄ 33#64) ∗
     ((slot + 24#64) ↦₆₄ 0#64) ∗
     ((slot + 32#64) ↦₆₄ 1#64) ∗
     ((slot + 40#64) ↦₆₄ 0#64) ∗
     ((slot + 48#64) ↦₆₄ 0#64) ∗
     ((slot + 56#64) ↦₆₄ 8#64) ∗
     ((slot + 64#64) ↦₆₄ 0#64) ∗
     ((slot + 72#64) ↦₆₄ pack64 (tail.take 8)) ∗
     ((slot + 80#64) ↦₆₄ pack64 ((tail.drop 8).take 8)) ∗
     ((slot + 88#64) ↦₆₄ pack64 ((tail.drop 16).take 8)) ∗
     ((slot + 96#64) ↦₆₄ pack64 (tail.drop 24))) at hcells
  have hpull :
      ((slot ↦₆₄ 33#64) ∗
       ((slot + 8#64) ↦₆₄ srkPtr) ∗
       ((slot + 16#64) ↦₆₄ 33#64) ∗
       ((slot + 24#64) ↦₆₄ 0#64) ∗
       ((slot + 32#64) ↦₆₄ 1#64) ∗
       ((slot + 40#64) ↦₆₄ 0#64) ∗
       ((slot + 48#64) ↦₆₄ 0#64) ∗
       ((slot + 56#64) ↦₆₄ 8#64) ∗
       ((slot + 64#64) ↦₆₄ 0#64) ∗
       ((slot + 72#64) ↦₆₄ pack64 (tail.take 8)) ∗
       ((slot + 80#64) ↦₆₄ pack64 ((tail.drop 8).take 8)) ∗
       ((slot + 88#64) ↦₆₄ pack64 ((tail.drop 16).take 8)) ∗
       ((slot + 96#64) ↦₆₄ pack64 (tail.drop 24)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A ⟨32#64, ckPtr⟩ (some rck)) =
      (((slot ↦₆₄ 33#64) ∗
        ((slot + 8#64) ↦₆₄ srkPtr) ∗
        ((slot + 16#64) ↦₆₄ 33#64) ∗
        ((slot + 24#64) ↦₆₄ 0#64) ∗
        ((slot + 32#64) ↦₆₄ 1#64) ∗
        ((slot + 40#64) ↦₆₄ 0#64) ∗
        ((slot + 48#64) ↦₆₄ 0#64) ∗
        ((slot + 56#64) ↦₆₄ 8#64) ∗
        ((slot + 64#64) ↦₆₄ 0#64) ∗
        ((slot + 72#64) ↦₆₄ pack64 (tail.take 8)) ∗
        ((slot + 80#64) ↦₆₄ pack64 ((tail.drop 8).take 8)) ∗
        ((slot + 88#64) ↦₆₄ pack64 ((tail.drop 16).take 8)) ∗
        ((slot + 96#64) ↦₆₄ pack64 (tail.drop 24))) ∗
       ((A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
        optChainKeyHeap A ⟨32#64, ckPtr⟩ (some rck))) := by
    ac_rfl
  rw [hpull, ← hcells]
  refine Entails.trans (sepConj_mono_right ?_) (chainAt_of_bytes A gc slot hpad')
  unfold chainHeap
  dsimp only [gc, newChainGhost, newReceiverChain, List.zip_nil_left]
  have hzero1 : vecU8Buf A 0#64 1#64 [] = _ :=
    vecBuf_zero A 1 1 (fun b a => a ↦₈ b) 1#64 []
  have hzero2 : vecBuf A 104 8 (messageKeyAt A) 0#64 8#64 [] = _ :=
    vecBuf_zero A 104 8 (messageKeyAt A) 8#64 []
  rw [hzero1, hzero2]
  apply Entails.pure_right ⟨publicKey_deserialize_serialize srk, Nat.zero_le _, rfl, hser_len, rfl⟩
  rw [sepConj_pure_left_comm]
  apply Entails.pure_right ⟨rfl, by decide⟩
  rw [sepConj_pure_left_comm]
  apply Entails.pure_right ⟨rfl, by decide⟩
  exact sepConj_mono_left (vecU8Buf_33_of_live A srkPtr srk.serialize hsrk_ne hser_len)

theorem stackAt_split_from (sp : BitVec 64) (total sub : Nat)
    (h : sub ≤ total) (htotal : total < 2 ^ 64) :
    stackAt sp total =
      memRegion (sp - BitVec.ofNat 64 total) (total - sub) ∗ stackAt sp sub := by
  unfold stackAt
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 total) (total - sub) sub (by omega)
  rw [show total - sub + sub = total from by omega] at hsplit
  have haddr : sp - BitVec.ofNat 64 total + BitVec.ofNat 64 (total - sub) =
      sp - BitVec.ofNat 64 sub := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [haddr] at hsplit
  exact hsplit

/-! ## 2. Address Lemmas and `ReachesOrPanic` Combinators -/

theorem stackAt_sub_split (sp : BitVec 64) (n : Nat) (hn : n ≤ tryDecryptSubStack) :
    stackAt sp tryDecryptSubStack =
      memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - n) ∗
      stackAt sp n := by
  simp only [stackAt]
  have h1 : tryDecryptSubStack = (tryDecryptSubStack - n) + n := (Nat.sub_add_cancel hn).symm
  have h2 : (tryDecryptSubStack - n) + n ≤ 2 ^ 64 := by
    rw [← h1]; unfold tryDecryptSubStack rootStack tryDecryptFrameSize; decide
  conv_lhs => rw [h1]
  rw [memRegion_split _ (tryDecryptSubStack - n) n h2, ← h1]
  congr 2
  have e1 : sp - BitVec.ofNat 64 ((tryDecryptSubStack - n) + n) =
      sp - BitVec.ofNat 64 n - BitVec.ofNat 64 (tryDecryptSubStack - n) := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  rw [h1, e1, Nat.add_sub_cancel, BitVec.sub_add_cancel]

theorem satisfies_tryDecrypt_onPanic_of_allocFailed
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image) (x : TryDecryptGhost)
    {s0 sf : State} {P R : SepProp}
    (hfail : allocFailedIn s0 sf) (hpfx : s0.trace <+: sf.trace)
    (hmem : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [tryDecryptSpec, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨Or.inr (Or.inr hfail), hpfx⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap P)) hmem

def ReachesOrPanic (prog : Program) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State) (Post : State → Prop) : Prop :=
  ∃ s', Steps prog s s' ∧
    (Post s' ∨
     (s'.status = .Panicked ∧
       (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

theorem ReachesOrPanic.done {prog : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State} {Post : State → Prop}
    (h : Post s) :
    ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Post :=
  ⟨s, .refl s, Or.inl h⟩

theorem ReachesOrPanic.seq {prog : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State} {P Q : State → Prop}
    (h1 : ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s P)
    (h2 : ∀ s1, s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab → P s1 →
      ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 Q) :
    ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  obtain ⟨s1, hsteps1, hP | hPan⟩ := h1
  · obtain ⟨s2, hsteps2, hQ⟩ := h2 s1 hsteps1.keepsFrozen hsteps1.symtab_eq hP
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · exact ⟨s1, hsteps1, Or.inr hPan⟩

theorem ReachesOrPanic.of_sepWP {prog : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {Pre Frame : SepProp}
    {PostWP : State → SepProp → Prop} {Q : State → Prop}
    (hwp : SepWP prog target s Pre PostWP)
    (hmem : s.mem ⊨ Pre ∗ (Frame ∗ R))
    (hL : prog.CodeLoaded s.mem)
    (hcont : ∀ s1 P_out,
      s1.pc = target → s1.status = .Running →
      s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ P_out ∗ (Frame ∗ R)) →
      PostWP s1 P_out →
      ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 Q) :
    ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_out, hm1, hpost1⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hmem hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hkf1 := hsteps1.keepsFrozen
  have hsym1 := hsteps1.symtab_eq
  have hL1 := hL.of_keepsFrozen hkf1
  obtain ⟨s2, hsteps2, hQ⟩ := hcont s1 P_out hpc1 hrun1 hkf1 hsym1 hL1 hm1 hpost1
  exact ⟨s2, hsteps1.trans hsteps2, hQ⟩

theorem ReachesOrPanic.of_call_no_panic {α : Type} {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    {entry ret_pc : BitVec 64} {spec : Spec α} {arg : α} {Frame : SepProp}
    {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (hpre : s.mem ⊨ spec.pre arg s ∗ (Frame ∗ R))
    (hL : prog.CodeLoaded s.mem)
    (hpan_false : ∀ sf, spec.onPanic arg s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hcont : ∀ s1,
      s1.pc = ret_pc → s1.status = .Running →
      s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 →
      s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ (Frame ∗ R)) →
      ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 Q)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl) :
    ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  obtain ⟨s1, hsteps1, hout, _⟩ :=
    hcall.no_fault_before_outcome arg (Frame ∗ R) s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpc1, hsp1, hrun1⟩, ⟨_, hcs1⟩, hpost1⟩ | ⟨_, hpost1⟩ | ⟨code, _, hpost1⟩ | ⟨_, hpost1⟩
  · rw [show Reg.lr = Reg.x30 from rfl, hlr] at hpc1
    have hkf1 := hsteps1.keepsFrozen
    have hsym1 := hsteps1.symtab_eq
    have hL1 := hL.of_keepsFrozen hkf1
    have hsp_align1 : s1.spAligned = true := by
      unfold State.spAligned at hsp ⊢; rw [hsp1]; exact hsp
    obtain ⟨s2, hsteps2, hQ⟩ := hcont s1 hpc1 hrun1 hsp1 hsp_align1 hcs1 hkf1 hsym1 hL1 hpost1
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · rw [hpan_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hexit_false code s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hoom_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1

theorem ReachesOrPanic.of_call_alloc_panic {α : Type} {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    {entry ret_pc : BitVec 64} {spec : Spec α} {arg : α} {Frame : SepProp}
    {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : s.trace = s0.trace)
    (hpre : s.mem ⊨ spec.pre arg s ∗ (Frame ∗ R))
    (hL : prog.CodeLoaded s.mem)
    (hpan_eq : ∀ sf, spec.onPanic arg s sf =
      ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hcont : ∀ s1,
      s1.pc = ret_pc → s1.status = .Running →
      s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 →
      s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ (Frame ∗ R)) →
      ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 Q)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl) :
    ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  obtain ⟨s1, hsteps1, hout, _⟩ :=
    hcall.no_fault_before_outcome arg (Frame ∗ R) s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpc1, hsp1, hrun1⟩, ⟨_, hcs1⟩, hpost1⟩ | ⟨hpan1, hpost1⟩ | ⟨code, _, hpost1⟩ | ⟨_, hpost1⟩
  · rw [show Reg.lr = Reg.x30 from rfl, hlr] at hpc1
    have hkf1 := hsteps1.keepsFrozen
    have hsym1 := hsteps1.symtab_eq
    have hL1 := hL.of_keepsFrozen hkf1
    have hsp_align1 : s1.spAligned = true := by
      unfold State.spAligned at hsp ⊢; rw [hsp1]; exact hsp
    obtain ⟨s2, hsteps2, hQ⟩ := hcont s1 hpc1 hrun1 hsp1 hsp_align1 hcs1 hkf1 hsym1 hL1 hpost1
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · rw [hpan_eq s1, sepConj_assoc, satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨⟨hfail, hpfx⟩, hmem1⟩
    have hfail0 : allocFailedIn s0 s1 := by
      unfold allocFailedIn at hfail ⊢; rwa [← htrace]
    have hpfx0 : s0.trace <+: s1.trace := by rwa [← htrace]
    rw [← sepConj_assoc] at hmem1
    exact ⟨s1, hsteps1, Or.inr ⟨hpan1,
      satisfies_tryDecrypt_onPanic_of_allocFailed C A ctl S img x hfail0 hpfx0 hmem1⟩⟩
  · rw [hexit_false code s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hoom_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1

theorem ReachesOrPanic.of_panic_extern {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {P R : SepProp} {s0 s : State} {Q : State → Prop}
    (hrun : s.status = .Running)
    (hext : prog.externAt? s.pc = some Rust.panicked)
    (hfail : allocFailedIn s0 s) (hpfx : s0.trace <+: s.trace)
    (hmem : s.mem ⊨ P ∗ R) :
    ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  refine ⟨Rust.panicked s,
    Steps.step (Step.extern hrun hext (Memory.KeepsFrozen.refl _)) (Steps.refl _),
    Or.inr ⟨rfl, ?_⟩⟩
  have hfail' : allocFailedIn s0 (Rust.panicked s) := hfail
  have hpfx' : s0.trace <+: (Rust.panicked s).trace := hpfx
  have hmem' : (Rust.panicked s).mem ⊨ P ∗ R := hmem
  exact satisfies_tryDecrypt_onPanic_of_allocFailed C A ctl S img x hfail' hpfx' hmem'

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH
