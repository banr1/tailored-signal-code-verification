/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# DH Step Commit Sub-Segment: Layout Packing & `ReachesOrPanic` Combinators

Byte/word packing helpers, address arithmetic lemmas, and fixed-image / relocatable
`[LibsignalPlacement]` `ReachesOrPanic` stepping combinators for `DhCommit`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 5. Byte/Word Packing and Layout Splitting Helpers -/

private theorem extractLsb'_shiftLeft8_or_zero (w : Nat) (hw : 8 ≤ w) (acc : BitVec w) (b : BitVec 8) :
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
    ∀ (bs : List (BitVec 8)), 8 * bs.length ≤ w → bytesOfBV bs.length (DhCommit.packBV w bs) = bs
  | [], _ => rfl
  | b :: bs, hlen => by
    have hlen_cons : 8 * (bs.length + 1) ≤ w := hlen
    unfold bytesOfBV
    rw [DhCommit.packBV, List.foldr_cons, ← DhCommit.packBV]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.mul_zero, extractLsb'_shiftLeft8_or_zero w (by omega), List.cons.injEq]
    refine ⟨trivial, ?_⟩
    have hmap :
        List.map ((fun j => ((DhCommit.packBV w bs <<< 8) ||| b.zeroExtend w).extractLsb' (8 * j) 8) ∘ Nat.succ)
          (List.range bs.length) =
        bytesOfBV bs.length (DhCommit.packBV w bs) := by
      unfold bytesOfBV
      apply List.map_congr_left
      intro k hk
      rw [List.mem_range] at hk
      exact extractLsb'_shiftLeft8_or_succ w (DhCommit.packBV w bs) b k (by omega)
    rw [hmap]
    exact bytesOfBV_packBV w bs (by omega)

def pack64 (bs : List (BitVec 8)) : BitVec 64 := DhCommit.packBV 64 bs

def pack32 (bs : List (BitVec 8)) : BitVec 32 := DhCommit.packBV 32 bs

theorem unpack64_pack64 {bs : List (BitVec 8)} (h : bs.length = 8) :
    unpack64 (pack64 bs) = bs := by
  have h1 : unpack64 (pack64 bs) = bytesOfBV bs.length (DhCommit.packBV 64 bs) := by
    rw [h]
    unfold unpack64 bytesOfBV pack64
    rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
    rfl
  rw [h1]
  exact bytesOfBV_packBV 64 bs (by omega)

theorem unpack32_pack32 {bs : List (BitVec 8)} (h : bs.length = 4) :
    unpack32 (pack32 bs) = bs := by
  have h1 : unpack32 (pack32 bs) = bytesOfBV bs.length (DhCommit.packBV 32 bs) := by
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
  have ha24 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 24#64 := by bv_omega
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
  have ha20 : a + BitVec.ofNat 64 4 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 20#64 := by bv_omega
  have ha28 : a + BitVec.ofNat 64 4 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 28#64 := by bv_omega
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

theorem optSenderChainBytes_some_pointsTo (a : BitVec 64) (sc : SenderChain) (pad : List (BitVec 8)) :
    (a ↦ₛ optSenderChainBytes (some sc) pad) =
      (a ↦₃₂ 1#32) ∗
      ((a + 4#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((a + 36#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((a + 68#64) ↦ₛ chainKeyBytes sc.chainKey) := by
  unfold optSenderChainBytes senderChainBytes
  dsimp only
  have h1 : leBytes 4 1 = unpack32 1#32 := leBytes_four_eq_unpack32 1#32
  have hlen0 : (leBytes 4 1).length = 4 := by simp [leBytes]
  have hlen1 : sc.ratchetKey.publicKey.bytes.toList.length = 32 := sc.ratchetKey.publicKey.bytes.toList_length
  have hlen2 : sc.ratchetKey.privateKey.bytes.toList.length = 32 := sc.ratchetKey.privateKey.bytes.toList_length
  rw [List.append_assoc,
      pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      hlen0, hlen1, hlen2, h1, ← pointsTo32_eq_pointsToBytes]
  have ha4 : a + BitVec.ofNat 64 4 = a + 4#64 := rfl
  have ha36 : a + BitVec.ofNat 64 4 + BitVec.ofNat 64 32 = a + 36#64 := by bv_omega
  have ha68 : a + BitVec.ofNat 64 4 + BitVec.ofNat 64 32 + BitVec.ofNat 64 32 = a + 68#64 := by bv_omega
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
    (sepConj_mono_right (sepConj_mono_left (vecU8Buf_cap_add_one_ne_zero A gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes))) ?_
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
    ((slot ↦₆₄ 33#64) ∗ ((slot + 8#64) ↦₆₄ srkPtr) ∗ ((slot + 16#64) ↦₆₄ 33#64) ∗
     ((slot + 24#64) ↦₆₄ 0#64) ∗ ((slot + 32#64) ↦₆₄ 1#64) ∗ ((slot + 40#64) ↦₆₄ 0#64) ∗
     ((slot + 48#64) ↦₆₄ 0#64) ∗ ((slot + 56#64) ↦₆₄ 8#64) ∗ ((slot + 64#64) ↦₆₄ 0#64) ∗
     ((slot + 72#64) ↦₆₄ pack64 (tail.take 8)) ∗ ((slot + 80#64) ↦₆₄ pack64 ((tail.drop 8).take 8)) ∗
     ((slot + 88#64) ↦₆₄ pack64 ((tail.drop 16).take 8)) ∗ ((slot + 96#64) ↦₆₄ pack64 (tail.drop 24)) ∗
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
    ((slot ↦₆₄ 33#64) ∗ ((slot + 8#64) ↦₆₄ srkPtr) ∗ ((slot + 16#64) ↦₆₄ 33#64) ∗
     ((slot + 24#64) ↦₆₄ 0#64) ∗ ((slot + 32#64) ↦₆₄ 1#64) ∗ ((slot + 40#64) ↦₆₄ 0#64) ∗
     ((slot + 48#64) ↦₆₄ 0#64) ∗ ((slot + 56#64) ↦₆₄ 8#64) ∗ ((slot + 64#64) ↦₆₄ 0#64) ∗
     ((slot + 72#64) ↦₆₄ pack64 (tail.take 8)) ∗ ((slot + 80#64) ↦₆₄ pack64 ((tail.drop 8).take 8)) ∗
     ((slot + 88#64) ↦₆₄ pack64 ((tail.drop 16).take 8)) ∗ ((slot + 96#64) ↦₆₄ pack64 (tail.drop 24))) at hcells
  have hpull :
      ((slot ↦₆₄ 33#64) ∗ ((slot + 8#64) ↦₆₄ srkPtr) ∗ ((slot + 16#64) ↦₆₄ 33#64) ∗
       ((slot + 24#64) ↦₆₄ 0#64) ∗ ((slot + 32#64) ↦₆₄ 1#64) ∗ ((slot + 40#64) ↦₆₄ 0#64) ∗
       ((slot + 48#64) ↦₆₄ 0#64) ∗ ((slot + 56#64) ↦₆₄ 8#64) ∗ ((slot + 64#64) ↦₆₄ 0#64) ∗
       ((slot + 72#64) ↦₆₄ pack64 (tail.take 8)) ∗ ((slot + 80#64) ↦₆₄ pack64 ((tail.drop 8).take 8)) ∗
       ((slot + 88#64) ↦₆₄ pack64 ((tail.drop 16).take 8)) ∗ ((slot + 96#64) ↦₆₄ pack64 (tail.drop 24)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A ⟨32#64, ckPtr⟩ (some rck)) =
      (((slot ↦₆₄ 33#64) ∗ ((slot + 8#64) ↦₆₄ srkPtr) ∗ ((slot + 16#64) ↦₆₄ 33#64) ∗
        ((slot + 24#64) ↦₆₄ 0#64) ∗ ((slot + 32#64) ↦₆₄ 1#64) ∗ ((slot + 40#64) ↦₆₄ 0#64) ∗
        ((slot + 48#64) ↦₆₄ 0#64) ∗ ((slot + 56#64) ↦₆₄ 8#64) ∗ ((slot + 64#64) ↦₆₄ 0#64) ∗
        ((slot + 72#64) ↦₆₄ pack64 (tail.take 8)) ∗ ((slot + 80#64) ↦₆₄ pack64 ((tail.drop 8).take 8)) ∗
        ((slot + 88#64) ↦₆₄ pack64 ((tail.drop 16).take 8)) ∗ ((slot + 96#64) ↦₆₄ pack64 (tail.drop 24))) ∗
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

/-! ## 6. Address Lemmas and `ReachesOrPanic` Combinators -/

theorem tryDecryptEntry_eq_base {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    tryDecryptEntry img = img.base + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") := by
  unfold tryDecryptEntry entryOf
  rw [libsignalSessionCode_ofImage h, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")]

theorem fnAddr_tryDecrypt_eq_base (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName = b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")]

theorem tryDecryptEntry_eq_fnAddr {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    tryDecryptEntry img = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName := by
  rw [tryDecryptEntry_eq_base h, fnAddr_tryDecrypt_eq_base]

theorem segS3CommitPC_eq_fnAddr {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    segDhCommitPC img = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 0x8ac#64 := by
  unfold segDhCommitPC
  rw [tryDecryptEntry_eq_fnAddr h ext]

theorem segS4PC_eq_fnAddr {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    segConsumeMsgKeyPC img = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 0x3e4#64 := by
  unfold segConsumeMsgKeyPC
  rw [tryDecryptEntry_eq_fnAddr h ext]

theorem fnAddr_publicKeySerialize_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") =
      (tripleRatchetProgAtExt b ext).fnAddr publicKeySerializeName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"), (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::serialize")]
  bv_omega

theorem fnAddr_chainKeyToPb_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xfffffffffffd8944#64 =
      (tripleRatchetProgAtExt b ext).fnAddr chainKeyToPbName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"), (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")]
  bv_omega

theorem fnAddr_growOneChain_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xfffffffffffe1688#64 =
      (tripleRatchetProgAtExt b ext).fnAddr growOneChainName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"), (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")]
  bv_omega

theorem fnAddr_dropChain_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") =
      (tripleRatchetProgAtExt b ext).fnAddr dropChainName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"), (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]")]
  bv_omega

theorem shim_ok_at_0xe6a8 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) noAllocShimSpec :=
  hA.shim_ok_at tryDecryptName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem alloc_ok_at_0xe6ac {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (rustAllocSpec A) :=
  hA.alloc_ok_at tryDecryptName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem dealloc_ok_at_0xe6b8 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (rustDeallocSpec A) :=
  hA.dealloc_ok_at tryDecryptName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem memmove_ok_at_0xe6c0 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (stackSize : Nat := 4096) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "memmove" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (sessionMemmoveSpec stackSize) :=
  hA.session_memmove_ok_at tryDecryptName (num% (ls_off% "memmove" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) stackSize

theorem memcpy_ok_at_0xe6d8 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) framelessMemcpySpec :=
  hA.session_memcpy_region_ok_at tryDecryptName (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem panic_at_0xe6f4 {b : BitVec 64}
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext tryDecryptName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

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
  exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap P)) hmem

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
  obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_out, hm1, hpost1⟩ | ⟨_, hoom⟩⟩ := hwp.elim hmem hL
  · have hkf1 := hsteps1.keepsFrozen
    have hsym1 := hsteps1.symtab_eq
    have hL1 := hL.of_keepsFrozen hkf1
    obtain ⟨s2, hsteps2, hQ⟩ := hcont s1 P_out hpc1 hrun1 hkf1 hsym1 hL1 hm1 hpost1
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · exact (not_satisfies_false_sepConj hoom).elim

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
  obtain ⟨s1, hsteps1, hout, -⟩ :=
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
  obtain ⟨s1, hsteps1, hout, -⟩ :=
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

/-! ## 6b. Relocatable `[LibsignalPlacement]` `ReachesOrPanic` Combinators -/

theorem ReachesOrPanic.seq_placed [LibsignalPlacement] {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State} {P Q : State → Prop}
    (h1 : ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s P)
    (h2 : ∀ s1, s.mem.KeepsFrozen s1.mem → P s1 →
      ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s1 Q) :
    ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s Q := by
  obtain ⟨s1, hsteps1, hP | hPan⟩ := h1
  · obtain ⟨s2, hsteps2, hQ⟩ := h2 s1 hsteps1.keepsFrozen hP
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · exact ⟨s1, hsteps1, Or.inr hPan⟩

theorem ReachesOrPanic.of_sepWP_placed [LibsignalPlacement] {prog : Program} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {Pre Frame : SepProp}
    {PostWP : State → SepProp → Prop} {Q : State → Prop}
    (hwp : SepWP prog target s Pre PostWP)
    (hmem : s.mem ⊨ Pre ∗ (Frame ∗ R))
    (hL : prog.CodeLoaded s.mem)
    (hcont : ∀ s1 P_out,
      s1.pc = target → s1.status = .Running →
      s.mem.KeepsFrozen s1.mem →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ P_out ∗ (Frame ∗ R)) →
      PostWP s1 P_out →
      ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s1 Q) :
    ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s Q := by
  obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_out, hm1, hpost1⟩ | ⟨_, hoom⟩⟩ := hwp.elim hmem hL
  · have hkf1 := hsteps1.keepsFrozen
    have hL1 := hL.of_keepsFrozen hkf1
    obtain ⟨s2, hsteps2, hQ⟩ := hcont s1 P_out hpc1 hrun1 hkf1 hL1 hm1 hpost1
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem ReachesOrPanic.of_call_no_panic_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
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
      s.mem.KeepsFrozen s1.mem →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ (Frame ∗ R)) →
      ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s1 Q)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl) :
    ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s Q :=
  ReachesOrPanic.of_call_no_panic hcall hpc hrun hsp hlr hpre hL hpan_false hexit_false
    (fun s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hkf1 _ hL1 hm1 =>
      hcont s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hkf1 hL1 hm1)
    hoom_false

theorem ReachesOrPanic.of_call_alloc_panic_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
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
      s.mem.KeepsFrozen s1.mem →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ (Frame ∗ R)) →
      ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s1 Q)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl) :
    ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s Q :=
  ReachesOrPanic.of_call_alloc_panic hcall hpc hrun hsp hlr htrace hpre hL hpan_eq hexit_false
    (fun s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hkf1 _ hL1 hm1 =>
      hcont s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hkf1 hL1 hm1)
    hoom_false

abbrev CommitStep1Wp (prog : Program) (entry pkSerEntry : BitVec 64) : Prop :=
  ∀ (sp msgA : BitVec 64) (scIdx : BitVec 32)
    (oldRk0 oldRk28 rk0 rk28 sck16 prevCtr0 : BitVec 32)
    (oldRk4 oldRk12 oldRk20 rk4 rk12 rk20 sck0 sck1 sck2 sck3
     v440 v448 v4e0 v4e8 v4f0 v4f8 : BitVec 64) (s : State),
    s.pc = entry + 0x8ac#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x22 = msgA → s.readReg64 .x25 = sp + 0x190#64 →
    s.readReg64 .x27 = sp + 0x38#64 → s.readReg64 .x28 = sp + 0x3d0#64 →
    SepWP prog pkSerEntry s
      (((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦₃₂ oldRk0) ∗ ((sp + 0xbc#64) ↦₆₄ oldRk4) ∗
       ((sp + 0xc4#64) ↦₆₄ oldRk12) ∗ ((sp + 0xcc#64) ↦₆₄ oldRk20) ∗ ((sp + 0xd4#64) ↦₃₂ oldRk28) ∗
       ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗ ((sp + 0x194#64) ↦₃₂ rk0) ∗ ((sp + 0x198#64) ↦₆₄ rk4) ∗
       ((sp + 0x1a0#64) ↦₆₄ rk12) ∗ ((sp + 0x1a8#64) ↦₆₄ rk20) ∗ ((sp + 0x1b0#64) ↦₃₂ rk28) ∗
       ((sp + 0x1b4#64) ↦₆₄ sck0) ∗ ((sp + 0x1bc#64) ↦₆₄ sck1) ∗ ((sp + 0x1c4#64) ↦₃₂ sck16) ∗
       ((sp + 0x1c8#64) ↦₆₄ sck2) ∗ ((sp + 0x1d0#64) ↦₆₄ sck3) ∗ ((sp + 0x440#64) ↦₆₄ v440) ∗
       ((sp + 0x448#64) ↦₆₄ v448) ∗ ((sp + 0x4e0#64) ↦₆₄ v4e0) ∗ ((sp + 0x4e8#64) ↦₆₄ v4e8) ∗
       ((sp + 0x4f0#64) ↦₆₄ v4f0) ∗ ((sp + 0x4f8#64) ↦₆₄ v4f8))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = msgA + 0x38#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = msgA ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = sck16.zeroExtend 64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x27 = sp + 0x38#64 ∧
        sf.readReg64 .x28 = sp + 0x3d0#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = entry + 0x8fc#64 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦₃₂ rk0) ∗ ((sp + 0xbc#64) ↦₆₄ rk4) ∗
          ((sp + 0xc4#64) ↦₆₄ rk12) ∗ ((sp + 0xcc#64) ↦₆₄ rk20) ∗ ((sp + 0xd4#64) ↦₃₂ rk28) ∗
          ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
          ((sp + 0x194#64) ↦₃₂ rk0) ∗ ((sp + 0x198#64) ↦₆₄ rk4) ∗ ((sp + 0x1a0#64) ↦₆₄ rk12) ∗
          ((sp + 0x1a8#64) ↦₆₄ rk20) ∗ ((sp + 0x1b0#64) ↦₃₂ rk28) ∗ ((sp + 0x1b4#64) ↦₆₄ sck0) ∗
          ((sp + 0x1bc#64) ↦₆₄ sck1) ∗ ((sp + 0x1c4#64) ↦₃₂ sck16) ∗ ((sp + 0x1c8#64) ↦₆₄ sck2) ∗
          ((sp + 0x1d0#64) ↦₆₄ sck3) ∗ ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
          ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗ ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
          ((sp + 0x4f8#64) ↦₆₄ sck1)))

abbrev CommitStep2PreShimWp (prog : Program) (entry shimEntry : BitVec 64) : Prop :=
  ∀ (sp boxPtr vSp0 : BitVec 64) (vSp8 sck16 : BitVec 32) (s : State),
    s.pc = entry + 0x8fc#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x0 = boxPtr → s.readReg64 .x1 = 33#64 → s.readReg64 .x24 = sck16.zeroExtend 64 →
    SepWP prog shimEntry s ((sp ↦₆₄ vSp0) ∗ ((sp + 8#64) ↦₃₂ vSp8))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = sck16.zeroExtend 64 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = boxPtr ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0x9f0#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ (sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16)))

abbrev CommitStep2PreAllocWp (prog : Program) (entry allocEntry : BitVec 64) : Prop :=
  ∀ (sp : BitVec 64) (s : State),
    s.pc = entry + 0x9f0#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x26 = 33#64 →
    SepWP prog allocEntry s emp
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = 33#64 ∧ sf.readReg64 .x1 = 1#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = 1#64 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xa00#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧ (P_f ⊢ emp))

abbrev CommitStep2OomWp (prog : Program) (entry oomEntry : BitVec 64) : Prop :=
  ∀ (sp : BitVec 64) (s : State),
    s.pc = entry + 0xa00#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x0 = 0#64 →
    SepWP prog oomEntry s emp (fun sf P_f => sf.trace = s.trace ∧ (P_f ⊢ emp))

abbrev CommitStep2PostAllocWp (prog : Program) (entry memcpyEntry : BitVec 64) : Prop :=
  ∀ (sp srkPtr boxPtr : BitVec 64) (s : State),
    s.pc = entry + 0xa00#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x0 = srkPtr → srkPtr ≠ 0#64 → s.readReg64 .x26 = 33#64 →
    SepWP prog memcpyEntry s (sp ↦₆₄ boxPtr)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = srkPtr ∧ sf.readReg64 .x1 = boxPtr ∧ sf.readReg64 .x2 = 33#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = boxPtr ∧ sf.readReg64 .x28 = srkPtr ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xa18#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧ (P_f ⊢ (sp ↦₆₄ boxPtr)))

abbrev CommitStep2ToPbWp (prog : Program) (entry toPbEntry : BitVec 64) : Prop :=
  ∀ (sp : BitVec 64) (s : State),
    s.pc = entry + 0xa18#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x25 = sp + 0x190#64 →
    SepWP prog toPbEntry s emp
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = sp + 0x3d0#64 ∧ sf.readReg64 .x8 = sp + 0x190#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xa84#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧ (P_f ⊢ emp))

abbrev CommitStep3aNogrowWp (prog : Program) (entry : BitVec 64) : Prop :=
  ∀ (sp chainsCap rcLen : BitVec 64) (s : State),
    s.pc = entry + 0xa84#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    rcLen ≠ chainsCap →
    SepWP prog (entry + 0xa9c#64) s (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x48#64) ↦₆₄ rcLen))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = rcLen ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x48#64) ↦₆₄ rcLen)))

abbrev CommitStep3aGrowWp (prog : Program) (entry growOneEntry : BitVec 64) : Prop :=
  ∀ (sp rcLen : BitVec 64) (s : State),
    s.pc = entry + 0xa84#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    SepWP prog growOneEntry s (((sp + 0x38#64) ↦₆₄ rcLen) ∗ ((sp + 0x48#64) ↦₆₄ rcLen))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = sp + 0x38#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = rcLen ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xa9c#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x38#64) ↦₆₄ rcLen) ∗ ((sp + 0x48#64) ↦₆₄ rcLen)))

abbrev CommitStep3bWp (prog : Program) (entry deallocEntry : BitVec 64) : Prop :=
  ∀ (sp chainsPtr1 rcLen boxPtr srkPtr : BitVec 64)
    (ck0 ck1 ck2 ck3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64) (s : State),
    s.pc = entry + 0xa9c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x24 = rcLen → s.readReg64 .x25 = sp + 0x190#64 →
    s.readReg64 .x26 = 33#64 → s.readReg64 .x27 = boxPtr → s.readReg64 .x28 = srkPtr →
    SepWP prog deallocEntry s
      (((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗ ((sp + 0x48#64) ↦₆₄ rcLen) ∗
       ((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
       ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3) ∗
       ((chainsPtr1 + rcLen * 104#64) ↦₆₄ w0) ∗ ((chainsPtr1 + rcLen * 104#64 + 8#64) ↦₆₄ w1) ∗
       ((chainsPtr1 + rcLen * 104#64 + 16#64) ↦₆₄ w2) ∗ ((chainsPtr1 + rcLen * 104#64 + 24#64) ↦₆₄ w3) ∗
       ((chainsPtr1 + rcLen * 104#64 + 32#64) ↦₆₄ w4) ∗ ((chainsPtr1 + rcLen * 104#64 + 40#64) ↦₆₄ w5) ∗
       ((chainsPtr1 + rcLen * 104#64 + 48#64) ↦₆₄ w6) ∗ ((chainsPtr1 + rcLen * 104#64 + 56#64) ↦₆₄ w7) ∗
       ((chainsPtr1 + rcLen * 104#64 + 64#64) ↦₆₄ w8) ∗ ((chainsPtr1 + rcLen * 104#64 + 72#64) ↦₆₄ w9) ∗
       ((chainsPtr1 + rcLen * 104#64 + 80#64) ↦₆₄ w10) ∗ ((chainsPtr1 + rcLen * 104#64 + 88#64) ↦₆₄ w11) ∗
       ((chainsPtr1 + rcLen * 104#64 + 96#64) ↦₆₄ w12))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = boxPtr ∧ sf.readReg64 .x1 = 33#64 ∧ sf.readReg64 .x2 = 1#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = rcLen ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = boxPtr ∧ sf.readReg64 .x28 = rcLen + 1#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xaf0#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗ ((sp + 0x48#64) ↦₆₄ (rcLen + 1#64)) ∗
          ((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
          ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3) ∗
          ((chainsPtr1 + rcLen * 104#64) ↦₆₄ 33#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 8#64) ↦₆₄ srkPtr) ∗
          ((chainsPtr1 + rcLen * 104#64 + 16#64) ↦₆₄ 33#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 24#64) ↦₆₄ 0#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 32#64) ↦₆₄ 1#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 40#64) ↦₆₄ 0#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 48#64) ↦₆₄ 0#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 56#64) ↦₆₄ 8#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 64#64) ↦₆₄ 0#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 72#64) ↦₆₄ ck0) ∗
          ((chainsPtr1 + rcLen * 104#64 + 80#64) ↦₆₄ ck1) ∗ ((chainsPtr1 + rcLen * 104#64 + 88#64) ↦₆₄ ck2) ∗
          ((chainsPtr1 + rcLen * 104#64 + 96#64) ↦₆₄ ck3)))

abbrev CommitStep4aLoWp (prog : Program) (entry : BitVec 64) : Prop :=
  ∀ (sp newLen : BitVec 64) (s : State),
    s.pc = entry + 0xaf0#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    BitVec.ult newLen 6#64 = true →
    SepWP prog (entry + 0xb98#64) s ((sp + 0x48#64) ↦₆₄ newLen)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = newLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x48#64) ↦₆₄ newLen)))

abbrev CommitStep4aGeWp (prog : Program) (entry : BitVec 64) : Prop :=
  ∀ (sp newLen : BitVec 64) (s : State),
    s.pc = entry + 0xaf0#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x25 = sp + 0x190#64 → BitVec.ult newLen 6#64 = false →
    SepWP prog (entry + 0xb04#64) s ((sp + 0x48#64) ↦₆₄ newLen)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = sp + 0x190#64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧
        sf.readReg64 .x28 = newLen ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x48#64) ↦₆₄ newLen)))

abbrev CommitStep4bPreMemmoveWp (prog : Program) (entry memmoveEntry : BitVec 64) : Prop :=
  ∀ (sp chainsPtr curLen : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
     s500 s508 s510 s518 s520 s528 s530 s538 s540 s548 s550 s558 : BitVec 64) (s : State),
    s.pc = entry + 0xb04#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x24 = sp + 0x190#64 →
    s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x27 = 0xffffffffffffff98#64 →
    s.readReg64 .x28 = curLen →
    SepWP prog memmoveEntry s
      (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ (chainsPtr ↦₆₄ c0) ∗ ((chainsPtr + 8#64) ↦₆₄ c1) ∗
       ((chainsPtr + 16#64) ↦₆₄ c2) ∗ ((chainsPtr + 24#64) ↦₆₄ c3) ∗ ((chainsPtr + 32#64) ↦₆₄ c4) ∗
       ((chainsPtr + 40#64) ↦₆₄ c5) ∗ ((chainsPtr + 48#64) ↦₆₄ c6) ∗ ((chainsPtr + 56#64) ↦₆₄ c7) ∗
       ((chainsPtr + 64#64) ↦₆₄ c8) ∗ ((chainsPtr + 72#64) ↦₆₄ c9) ∗ ((chainsPtr + 80#64) ↦₆₄ c10) ∗
       ((chainsPtr + 88#64) ↦₆₄ c11) ∗ ((chainsPtr + 96#64) ↦₆₄ c12) ∗
       ((sp + 0x500#64) ↦₆₄ s500) ∗ ((sp + 0x508#64) ↦₆₄ s508) ∗ ((sp + 0x510#64) ↦₆₄ s510) ∗
       ((sp + 0x518#64) ↦₆₄ s518) ∗ ((sp + 0x520#64) ↦₆₄ s520) ∗ ((sp + 0x528#64) ↦₆₄ s528) ∗
       ((sp + 0x530#64) ↦₆₄ s530) ∗ ((sp + 0x538#64) ↦₆₄ s538) ∗ ((sp + 0x540#64) ↦₆₄ s540) ∗
       ((sp + 0x548#64) ↦₆₄ s548) ∗ ((sp + 0x550#64) ↦₆₄ s550) ∗ ((sp + 0x558#64) ↦₆₄ s558))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = chainsPtr ∧ sf.readReg64 .x1 = chainsPtr + 104#64 ∧
        sf.readReg64 .x2 = 0xffffffffffffff98#64 + curLen * 104#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 0x500#64 ∧ sf.readReg64 .x24 = sp + 0x190#64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x26 = c0 ∧
        sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧ sf.readReg64 .x28 = curLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xb4c#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ (chainsPtr ↦₆₄ c0) ∗ ((chainsPtr + 8#64) ↦₆₄ c1) ∗
          ((chainsPtr + 16#64) ↦₆₄ c2) ∗ ((chainsPtr + 24#64) ↦₆₄ c3) ∗ ((chainsPtr + 32#64) ↦₆₄ c4) ∗
          ((chainsPtr + 40#64) ↦₆₄ c5) ∗ ((chainsPtr + 48#64) ↦₆₄ c6) ∗ ((chainsPtr + 56#64) ↦₆₄ c7) ∗
          ((chainsPtr + 64#64) ↦₆₄ c8) ∗ ((chainsPtr + 72#64) ↦₆₄ c9) ∗ ((chainsPtr + 80#64) ↦₆₄ c10) ∗
          ((chainsPtr + 88#64) ↦₆₄ c11) ∗ ((chainsPtr + 96#64) ↦₆₄ c12) ∗
          ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
          ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
          ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
          ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12)))

abbrev CommitStep4bPostMemmoveWp (prog : Program) (entry dropChainEntry : BitVec 64) : Prop :=
  ∀ (sp curLen : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
     s190 s198 s1a0 s1a8 s1b0 s1b8 s1c0 s1c8 s1d0 s1d8 s1e0 s1e8 s1f0 : BitVec 64) (s : State),
    s.pc = entry + 0xb4c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x24 = sp + 0x190#64 →
    s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x26 = c0 →
    s.readReg64 .x27 = 0xffffffffffffff98#64 → s.readReg64 .x28 = curLen →
    c0 + 1#64 ≠ 0#64 →
    SepWP prog dropChainEntry s
      (((sp + 0x48#64) ↦₆₄ curLen) ∗
       ((sp + 0x190#64) ↦₆₄ s190) ∗ ((sp + 0x198#64) ↦₆₄ s198) ∗ ((sp + 0x1a0#64) ↦₆₄ s1a0) ∗
       ((sp + 0x1a8#64) ↦₆₄ s1a8) ∗ ((sp + 0x1b0#64) ↦₆₄ s1b0) ∗ ((sp + 0x1b8#64) ↦₆₄ s1b8) ∗
       ((sp + 0x1c0#64) ↦₆₄ s1c0) ∗ ((sp + 0x1c8#64) ↦₆₄ s1c8) ∗ ((sp + 0x1d0#64) ↦₆₄ s1d0) ∗
       ((sp + 0x1d8#64) ↦₆₄ s1d8) ∗ ((sp + 0x1e0#64) ↦₆₄ s1e0) ∗ ((sp + 0x1e8#64) ↦₆₄ s1e8) ∗
       ((sp + 0x1f0#64) ↦₆₄ s1f0) ∗
       ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
       ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
       ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
       ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = sp + 0x190#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 0x500#64 ∧ sf.readReg64 .x24 = sp + 0x190#64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x26 = c0 ∧
        sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧ sf.readReg64 .x28 = curLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xb8c#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x48#64) ↦₆₄ (curLen - 1#64)) ∗
          ((sp + 0x190#64) ↦₆₄ c0) ∗ ((sp + 0x198#64) ↦₆₄ c1) ∗ ((sp + 0x1a0#64) ↦₆₄ c2) ∗
          ((sp + 0x1a8#64) ↦₆₄ c3) ∗ ((sp + 0x1b0#64) ↦₆₄ c4) ∗ ((sp + 0x1b8#64) ↦₆₄ c5) ∗
          ((sp + 0x1c0#64) ↦₆₄ c6) ∗ ((sp + 0x1c8#64) ↦₆₄ c7) ∗ ((sp + 0x1d0#64) ↦₆₄ c8) ∗
          ((sp + 0x1d8#64) ↦₆₄ c9) ∗ ((sp + 0x1e0#64) ↦₆₄ c10) ∗ ((sp + 0x1e8#64) ↦₆₄ c11) ∗
          ((sp + 0x1f0#64) ↦₆₄ c12) ∗
          ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
          ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
          ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
          ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12)))

abbrev CommitStep4cHiWp (prog : Program) (entry : BitVec 64) : Prop :=
  ∀ (sp nextLen : BitVec 64) (s : State),
    s.pc = entry + 0xb8c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    BitVec.ult 5#64 nextLen = true →
    SepWP prog (entry + 0xb04#64) s ((sp + 0x48#64) ↦₆₄ nextLen)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = nextLen ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x48#64) ↦₆₄ nextLen)))

abbrev CommitStep4cLeWp (prog : Program) (entry : BitVec 64) : Prop :=
  ∀ (sp nextLen : BitVec 64) (s : State),
    s.pc = entry + 0xb8c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    BitVec.ult 5#64 nextLen = false →
    SepWP prog (entry + 0xb98#64) s ((sp + 0x48#64) ↦₆₄ nextLen)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = nextLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x48#64) ↦₆₄ nextLen)))

abbrev CommitStep5Wp (prog : Program) (entry : BitVec 64) : Prop :=
  ∀ (sp : BitVec 64) (sck16 rck16 msgW oldTag oldSck16 v2d0 : BitVec 32)
    (oldSpk0 oldSpk1 oldSpk2 oldSpk3 oldSk0 oldSk1 oldSk2 oldSk3
     oldSck0 oldSck1 oldSck2 oldSck3 spk0 spk1 spk2 spk3 sk0 sk1 sk2 sk3
     sck0 sck1 sck2 sck3 rck0 rck1 rck2 rck3 v2b0 v2b8 v2c0 v2c8
     v450 v458 v460 v468 v470 v478 v480 v488 v490 v498 : BitVec 64) (s : State),
    s.pc = entry + 0xb98#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x25 = sp + 0x190#64 →
    SepWP prog (entry + 0x3e4#64) s
      (((sp + 0x8#64) ↦₃₂ sck16) ∗ ((sp + 0x10#64) ↦₃₂ rck16) ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x50#64) ↦₃₂ oldTag) ∗ ((sp + 0x54#64) ↦₆₄ oldSpk0) ∗ ((sp + 0x5c#64) ↦₆₄ oldSpk1) ∗
       ((sp + 0x64#64) ↦₆₄ oldSpk2) ∗ ((sp + 0x6c#64) ↦₆₄ oldSpk3) ∗ ((sp + 0x74#64) ↦₆₄ oldSk0) ∗
       ((sp + 0x7c#64) ↦₆₄ oldSk1) ∗ ((sp + 0x84#64) ↦₆₄ oldSk2) ∗ ((sp + 0x8c#64) ↦₆₄ oldSk3) ∗
       ((sp + 0x94#64) ↦₆₄ oldSck0) ∗ ((sp + 0x9c#64) ↦₆₄ oldSck1) ∗ ((sp + 0xa4#64) ↦₃₂ oldSck16) ∗
       ((sp + 0xa8#64) ↦₆₄ oldSck2) ∗ ((sp + 0xb0#64) ↦₆₄ oldSck3) ∗ ((sp + 0x2b0#64) ↦₆₄ v2b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ v2b8) ∗ ((sp + 0x2c0#64) ↦₆₄ v2c0) ∗ ((sp + 0x2c8#64) ↦₆₄ v2c8) ∗
       ((sp + 0x2d0#64) ↦₃₂ v2d0) ∗ ((sp + 0x400#64) ↦₆₄ spk0) ∗ ((sp + 0x408#64) ↦₆₄ spk1) ∗
       ((sp + 0x410#64) ↦₆₄ spk2) ∗ ((sp + 0x418#64) ↦₆₄ spk3) ∗ ((sp + 0x420#64) ↦₆₄ sk0) ∗
       ((sp + 0x428#64) ↦₆₄ sk1) ∗ ((sp + 0x430#64) ↦₆₄ sk2) ∗ ((sp + 0x438#64) ↦₆₄ sk3) ∗
       ((sp + 0x450#64) ↦₆₄ v450) ∗ ((sp + 0x458#64) ↦₆₄ v458) ∗ ((sp + 0x460#64) ↦₆₄ v460) ∗
       ((sp + 0x468#64) ↦₆₄ v468) ∗ ((sp + 0x470#64) ↦₆₄ v470) ∗ ((sp + 0x478#64) ↦₆₄ v478) ∗
       ((sp + 0x480#64) ↦₆₄ v480) ∗ ((sp + 0x488#64) ↦₆₄ v488) ∗ ((sp + 0x490#64) ↦₆₄ v490) ∗
       ((sp + 0x498#64) ↦₆₄ v498) ∗ ((sp + 0x4c0#64) ↦₆₄ rck2) ∗ ((sp + 0x4c8#64) ↦₆₄ rck3) ∗
       ((sp + 0x4d0#64) ↦₆₄ rck0) ∗ ((sp + 0x4d8#64) ↦₆₄ rck1) ∗ ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
       ((sp + 0x4e8#64) ↦₆₄ sck3) ∗ ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = msgW.zeroExtend 64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = s.readReg64 .x30 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x8#64) ↦₃₂ sck16) ∗ ((sp + 0x10#64) ↦₃₂ rck16) ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗
          ((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦₆₄ spk0) ∗ ((sp + 0x5c#64) ↦₆₄ spk1) ∗
          ((sp + 0x64#64) ↦₆₄ spk2) ∗ ((sp + 0x6c#64) ↦₆₄ spk3) ∗ ((sp + 0x74#64) ↦₆₄ sk0) ∗
          ((sp + 0x7c#64) ↦₆₄ sk1) ∗ ((sp + 0x84#64) ↦₆₄ sk2) ∗ ((sp + 0x8c#64) ↦₆₄ sk3) ∗
          ((sp + 0x94#64) ↦₆₄ sck0) ∗ ((sp + 0x9c#64) ↦₆₄ sck1) ∗ ((sp + 0xa4#64) ↦₃₂ sck16) ∗
          ((sp + 0xa8#64) ↦₆₄ sck2) ∗ ((sp + 0xb0#64) ↦₆₄ sck3) ∗ ((sp + 0x2b0#64) ↦₆₄ rck2) ∗
          ((sp + 0x2b8#64) ↦₆₄ rck3) ∗ ((sp + 0x2c0#64) ↦₆₄ rck0) ∗ ((sp + 0x2c8#64) ↦₆₄ rck1) ∗
          ((sp + 0x2d0#64) ↦₃₂ rck16) ∗ ((sp + 0x400#64) ↦₆₄ spk0) ∗ ((sp + 0x408#64) ↦₆₄ spk1) ∗
          ((sp + 0x410#64) ↦₆₄ spk2) ∗ ((sp + 0x418#64) ↦₆₄ spk3) ∗ ((sp + 0x420#64) ↦₆₄ sk0) ∗
          ((sp + 0x428#64) ↦₆₄ sk1) ∗ ((sp + 0x430#64) ↦₆₄ sk2) ∗ ((sp + 0x438#64) ↦₆₄ sk3) ∗
          ((sp + 0x450#64) ↦₆₄ spk0) ∗ ((sp + 0x458#64) ↦₆₄ spk1) ∗ ((sp + 0x460#64) ↦₆₄ spk2) ∗
          ((sp + 0x468#64) ↦₆₄ spk3) ∗ ((sp + 0x470#64) ↦₆₄ sk0) ∗ ((sp + 0x478#64) ↦₆₄ sk1) ∗
          ((sp + 0x480#64) ↦₆₄ sk2) ∗ ((sp + 0x488#64) ↦₆₄ sk3) ∗ ((sp + 0x490#64) ↦₆₄ sck0) ∗
          ((sp + 0x498#64) ↦₆₄ sck1) ∗ ((sp + 0x4c0#64) ↦₆₄ rck2) ∗ ((sp + 0x4c8#64) ↦₆₄ rck3) ∗
          ((sp + 0x4d0#64) ↦₆₄ rck0) ∗ ((sp + 0x4d8#64) ↦₆₄ rck1) ∗ ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
          ((sp + 0x4e8#64) ↦₆₄ sck3) ∗ ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1)))

/-- Bundled basic-block `SepWP` stepping contracts for `DhCommit` (`+0x8ac .. +0xbfc → +0x3e4`),
shared between Block `130` (`try_decrypt_with_state::<HookRng>`, `dropChainEntry = lsmpl.base 142`)
and Block `433` (`try_decrypt_with_state::<Coins>`, `dropChainEntry = lsmpl.base 445`). -/
structure DhCommitBlockWp [LibsignalPlacement]
    (prog : Program) (entry dropChainEntry : BitVec 64) : Prop where
  step1 : CommitStep1Wp prog entry (lsmpl.base 205)
  step2_pre_shim : CommitStep2PreShimWp prog entry (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  step2_pre_alloc : CommitStep2PreAllocWp prog entry (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  step2_oom : CommitStep2OomWp prog entry (lsmpl.ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
  step2_post_alloc : CommitStep2PostAllocWp prog entry (lsmpl.ρ "memcpy")
  step2_to_pb : CommitStep2ToPbWp prog entry (lsmpl.base 22)
  step3a_nogrow : CommitStep3aNogrowWp prog entry
  step3a_grow : CommitStep3aGrowWp prog entry (lsmpl.base 43)
  step3b : CommitStep3bWp prog entry (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  step4a_lo : CommitStep4aLoWp prog entry
  step4a_ge : CommitStep4aGeWp prog entry
  step4b_pre_memmove : CommitStep4bPreMemmoveWp prog entry (lsmpl.ρ "memmove")
  step4b_post_memmove : CommitStep4bPostMemmoveWp prog entry dropChainEntry
  step4c_hi : CommitStep4cHiWp prog entry
  step4c_le : CommitStep4cLeWp prog entry
  step5 : CommitStep5Wp prog entry

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit
