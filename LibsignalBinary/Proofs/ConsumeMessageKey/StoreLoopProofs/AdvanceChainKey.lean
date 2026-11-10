/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Fetch
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `AdvanceChainKey` Sub-Segment of the `consume_message_key` Store Loop

Symbolic execution from `cmkAdvanceChainKeyPC` (`+0x474`) to the loop back-edge (`+0x334` or
`+0x4dc`): computes `hmac_sha256(ckc.key, [0x02])`, increments `ckc.index` (non-overflowing since
`ckc.index < x.counter`), writes the updated chain key to `x.ckA`, and branches on `ck'.index < x.counter`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession.StoreLoop

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel
open CryptoVerification.LibsignalSession
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

/-! ## Bit-Vector Byte Packing and Unpacking Lemmas -/

theorem extractLsb'_shiftLeft8_or_zero (w : Nat) (hw : 8 ≤ w) (acc : BitVec w) (b : BitVec 8) :
    ((acc <<< 8) ||| b.zeroExtend w).extractLsb' 0 8 = b := by
  ext i hi
  simp [hi]
  omega

theorem extractLsb'_shiftLeft8_or_succ (w : Nat) (acc : BitVec w) (b : BitVec 8) (k : Nat)
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

def bytesOfBV_shared_lb {w : Nat} (n : Nat) (v : BitVec w) : List (BitVec 8) :=
  (List.range n).map fun j => v.extractLsb' (8 * j) 8

def packBV_shared_lb (w : Nat) (bs : List (BitVec 8)) : BitVec w :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend w) 0

theorem bytesOfBV_packBV (w : Nat) :
    ∀ (bs : List (BitVec 8)), 8 * bs.length ≤ w → bytesOfBV_shared_lb bs.length (packBV_shared_lb w bs) = bs
  | [], _ => rfl
  | b :: bs, hlen => by
    have hlen_cons : 8 * (bs.length + 1) ≤ w := hlen
    unfold bytesOfBV_shared_lb
    rw [packBV_shared_lb, List.foldr_cons, ← packBV_shared_lb]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.mul_zero, extractLsb'_shiftLeft8_or_zero w (by omega), List.cons.injEq]
    refine ⟨trivial, ?_⟩
    have hmap :
        List.map ((fun j => ((packBV_shared_lb w bs <<< 8) ||| b.zeroExtend w).extractLsb' (8 * j) 8) ∘ Nat.succ)
          (List.range bs.length) =
        bytesOfBV_shared_lb bs.length (packBV_shared_lb w bs) := by
      unfold bytesOfBV_shared_lb
      apply List.map_congr_left
      intro k hk
      rw [List.mem_range] at hk
      exact extractLsb'_shiftLeft8_or_succ w (packBV_shared_lb w bs) b k (by omega)
    rw [hmap]
    exact bytesOfBV_packBV w bs (by omega)

theorem keyToBytes32_bytesToKey32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    keyToBytes32 (bytesToKey32 bs) = bs := by
  have h1 : keyToBytes32 (bytesToKey32 bs) = bytesOfBV_shared_lb bs.length (packBV_shared_lb 256 bs) := by
    rw [h]
    unfold keyToBytes32 bytesOfBV_shared_lb bytesToKey32 packBV_shared_lb
    rw [List.ofFn_eq_map]
    rfl
  rw [h1]
  exact bytesOfBV_packBV 256 bs (by omega)

def pack64 (bs : List (BitVec 8)) : BitVec 64 := packBV_shared_lb 64 bs

theorem unpack64_pack64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    unpack64 (pack64 bs) = bs := by
  have h1 : unpack64 (pack64 bs) = bytesOfBV_shared_lb bs.length (packBV_shared_lb 64 bs) := by
    rw [h]
    unfold unpack64 bytesOfBV_shared_lb pack64
    rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
    rfl
  rw [h1]
  exact bytesOfBV_packBV 64 bs (by omega)

theorem pointsToBytes_8_eq_pointsTo64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ pack64 bs) := by
  rw [pointsTo64_eq_pointsToBytes, unpack64_pack64 bs h]

theorem pointsToBytes_32_eq_pointsTo64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ pack64 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ pack64 ((bs.drop 8).take 8)) ∗
       ((a + 16#64) ↦₆₄ pack64 ((bs.drop 16).take 8)) ∗
       ((a + 24#64) ↦₆₄ pack64 (bs.drop 24))) := by
  have hsplit :
      bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
    have h24 : bs.drop 24 = (bs.drop 16).drop 8 := by simp [List.drop_drop]
    have h16 : bs.drop 16 = (bs.drop 8).drop 8 := by simp [List.drop_drop]
    rw [h24, List.take_append_drop, h16, List.take_append_drop, List.take_append_drop]
  have h0 : (bs.take 8).length = 8 := by simp [h]
  have h1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have h3 : (bs.drop 24).length = 8 := by simp [h]
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      h0, h1, h2,
      pointsToBytes_8_eq_pointsTo64 a (bs.take 8) h0,
      pointsToBytes_8_eq_pointsTo64 _ ((bs.drop 8).take 8) h1,
      pointsToBytes_8_eq_pointsTo64 _ ((bs.drop 16).take 8) h2,
      pointsToBytes_8_eq_pointsTo64 _ (bs.drop 24) h3]
  have ha8 : a + BitVec.ofNat 64 8 = a + 8#64 := rfl
  have ha16 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 16#64 := by bv_omega
  have ha24 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 24#64 := by bv_omega
  rw [ha24, ha16, ha8]

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

private theorem pointsTo8_eq_pointsToBytes_singleton (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem memRegion_one_eq_exists_pointsTo8 (a : BitVec 64) :
    memRegion a 1 = ∃∗ b : BitVec 8, (a ↦₈ b) :=
  IsBlock.eq_of_iff (IsBlock.memRegion a 1) (IsBlock.sepExists fun b => IsBlock.pointsTo8 a b) fun m =>
    { mp := fun _ => ⟨m.read8 a, rfl⟩, mpr := fun _ => trivial }

theorem pointsTo8_entails_memRegion_one (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ⊢ memRegion a 1 := by
  rw [pointsTo8_eq_pointsToBytes_singleton]
  exact pointsToBytes_entails_memRegion a [b]

/-! ## Stack and Frame Splitting Lemmas -/

private theorem stackAt_7712_split_2048 (sp0 : BitVec 64) :
    stackAt (sp0 - 480#64) 7712 =
      memRegion (sp0 - 8192#64) 5664 ∗ stackAt (sp0 - 480#64) 2048 := by
  simp only [stackAt]
  have h := memRegion_split (sp0 - 8192#64) 5664 2048 (by decide)
  have a1 : sp0 - 480#64 - 7712#64 = sp0 - 8192#64 := by bv_omega
  have a2 : sp0 - 8192#64 + 5664#64 = sp0 - 480#64 - 2048#64 := by bv_omega
  change memRegion (sp0 - 8192#64) 7712 =
    memRegion (sp0 - 8192#64) 5664 ∗ memRegion (sp0 - 8192#64 + 5664#64) 2048 at h
  rw [a2] at h
  change memRegion (sp0 - 480#64 - 7712#64) 7712 = _
  rw [a1]
  exact h

private theorem memRegion_256_advanceChainKey_split (sp0 : BitVec 64) :
    memRegion (sp0 - 352#64) 256 =
      ∃∗ b320 : BitVec 8,
        ((sp0 - 320#64) ↦₈ b320) ∗
        memRegion (sp0 - 319#64) 31 ∗
        memRegion (sp0 - 224#64) 32 ∗
        (memRegion (sp0 - 352#64) 32 ∗
         memRegion (sp0 - 288#64) 64 ∗
         memRegion (sp0 - 192#64) 96) := by
  rw [show (256 : Nat) = 32 + (1 + (31 + (64 + (32 + 96)))) from rfl,
      memRegion_split (sp0 - 352#64) 32 224 (by decide),
      memRegion_split (sp0 - 352#64 + 32#64) 1 223 (by decide),
      memRegion_split (sp0 - 352#64 + 32#64 + 1#64) 31 192 (by decide),
      memRegion_split (sp0 - 352#64 + 32#64 + 1#64 + 31#64) 64 128 (by decide),
      memRegion_split (sp0 - 352#64 + 32#64 + 1#64 + 31#64 + 64#64) 32 96 (by decide)]
  have ha1 : sp0 - 352#64 + 32#64 = sp0 - 320#64 := by bv_omega
  have ha2 : sp0 - 320#64 + 1#64 = sp0 - 319#64 := by bv_omega
  have ha3 : sp0 - 319#64 + 31#64 = sp0 - 288#64 := by bv_omega
  have ha4 : sp0 - 288#64 + 64#64 = sp0 - 224#64 := by bv_omega
  have ha5 : sp0 - 224#64 + 32#64 = sp0 - 192#64 := by bv_omega
  rw [ha1, ha2, ha3, ha4, ha5, memRegion_one_eq_exists_pointsTo8 (sp0 - 320#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext b320
  ac_rfl

private theorem memRegion_32_eq_exists_pointsTo64_4 (a : BitVec 64) :
    memRegion a 32 =
      ∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64,
        (a ↦₆₄ t0) ∗ ((a + 8#64) ↦₆₄ t1) ∗ ((a + 16#64) ↦₆₄ t2) ∗ ((a + 24#64) ↦₆₄ t3) := by
  rw [show (32 : Nat) = 8 + (8 + (8 + 8)) from rfl,
      memRegion_split a 8 24 (by decide),
      memRegion_split (a + 8#64) 8 16 (by decide),
      memRegion_split (a + 8#64 + 8#64) 8 8 (by decide)]
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  rw [ha16, ha24, memRegion_eight a, sepExists_sepConj_left]
  apply congrArg SepProp.sepExists; funext t0
  rw [memRegion_eight (a + 8#64), sepExists_sepConj_left, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext t1
  rw [memRegion_eight (a + 16#64), sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext t2
  rw [memRegion_eight (a + 24#64), sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]

theorem pointsTo64_4_entails_memRegion_32 (a : BitVec 64)
    (t0 t1 t2 t3 : BitVec 64) :
    ((a ↦₆₄ t0) ∗ ((a + 8#64) ↦₆₄ t1) ∗ ((a + 16#64) ↦₆₄ t2) ∗ ((a + 24#64) ↦₆₄ t3)) ⊢
      memRegion a 32 := by
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion a t0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) t1)
      (sepConj_mono (pointsTo64_entails_memRegion (a + 16#64) t2)
        (pointsTo64_entails_memRegion (a + 24#64) t3)))) ?_
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  rw [← ha24, ← memRegion_split (a + 16#64) 8 8 (by decide),
      ← ha16, ← memRegion_split (a + 8#64) 8 16 (by decide),
      ← memRegion_split a 8 24 (by decide)]
  exact Entails.refl _

private def advanceChainKeyFrame (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (s0 : State) : SepProp :=
  ratchetAt A x.self G' st' ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  memRegion (s0.sp - 8192#64) 5664 ∗
  memRegion (s0.sp - 480#64) 112 ∗
  ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
  memRegion (s0.sp - 360#64) 4 ∗
  memRegion (s0.sp - 352#64) 32 ∗
  memRegion (s0.sp - 288#64) 64 ∗
  memRegion (s0.sp - 192#64) 96 ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

private theorem cmkLoopHeap_advanceChainKey_split (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (ckc : ChainKey) (s0 : State) :
    cmkLoopHeap A img x G' st' ckc s0 =
      ∃∗ b320 : BitVec 8,
        ((s0.sp - 320#64) ↦₈ b320) ∗
        (memRegion (s0.sp - 224#64) 32 ∗
         (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
         stackAt (s0.sp - 480#64) 2048 ∗
         memRegion (s0.sp - 319#64) 31 ∗
         ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
         ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
         advanceChainKeyFrame A img x G' st' s0) := by
  unfold cmkLoopHeap cmkLoopFrame advanceChainKeyFrame
  rw [chainKeyBytes_pointsTo x.ckA ckc,
      stackAt_7712_split_2048 s0.sp,
      memRegion_256_advanceChainKey_split s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext b320
  ac_rfl

private theorem advanceChainKeyPost_entails_cmkLoopHeap (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (ckc : ChainKey)
    (q0_lo q0_hi q1_lo q1_hi : BitVec 64)
    (hq0_lo : q0_lo = pack64 ((hmacWith F (keyToBytes32 ckc.key) [2#8]).take 8))
    (hq0_hi : q0_hi = pack64 (((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 8).take 8))
    (hq1_lo : q1_lo = pack64 (((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 16).take 8))
    (hq1_hi : q1_hi = pack64 ((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 24))
    (s0 : State) :
    (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
     ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
     ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
     ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
     ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
     ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
     ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
     ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
     ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
     (x.ckA ↦₆₄ q0_lo) ∗
     ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
     ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
     ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
     ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32)) ∗
     stackAt (s0.sp - 480#64) 2048 ∗
     advanceChainKeyFrame A img x G' st' s0) ⊢
      cmkLoopHeap A img x G' st' (chainStepN F 1 ckc) s0 := by
  let bs := hmacWith F (keyToBytes32 ckc.key) [2#8]
  have hbs : bs.length = 32 := hmacWith_length F (keyToBytes32 ckc.key) [2#8]
  have hck'_key : keyToBytes32 (chainStepN F 1 ckc).key = bs := by
    change keyToBytes32 (bytesToKey32 bs) = bs
    exact keyToBytes32_bytesToKey32 bs hbs
  have hck'_idx : (chainStepN F 1 ckc).index = ckc.index + 1#32 := rfl
  have hckA_words :
      ((x.ckA ↦₆₄ q0_lo) ∗ ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
       ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗ ((x.ckA + 24#64) ↦₆₄ q1_hi)) =
      (x.ckA ↦ₛ bs) := by
    rw [hq0_lo, hq0_hi, hq1_lo, hq1_hi, ← pointsToBytes_32_eq_pointsTo64 x.ckA bs hbs]
  have hckA_full :
      ((x.ckA ↦₆₄ q0_lo) ∗ ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
       ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗ ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
       ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) =
      (x.ckA ↦ₛ chainKeyBytes (chainStepN F 1 ckc)) := by
    rw [chainKeyBytes_pointsTo x.ckA (chainStepN F 1 ckc), hck'_key, hck'_idx, ← hckA_words]
    ac_rfl
  have h224 := pointsTo64_4_entails_memRegion_32 (s0.sp - 224#64) q0_lo q0_hi q1_lo q1_hi
  have h320 := pointsTo64_4_entails_memRegion_32 (s0.sp - 320#64) q0_lo q0_hi q1_lo q1_hi
  have ha216 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_omega
  have ha208 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
  have ha200 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_omega
  have ha312 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_omega
  have ha304 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_omega
  have ha296 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_omega
  rw [ha216, ha208, ha200] at h224
  rw [ha312, ha304, ha296] at h320
  have h256 :
      (memRegion (s0.sp - 352#64) 32 ∗
       memRegion (s0.sp - 320#64) 32 ∗
       memRegion (s0.sp - 288#64) 64 ∗
       memRegion (s0.sp - 224#64) 32 ∗
       memRegion (s0.sp - 192#64) 96) =
      memRegion (s0.sp - 352#64) 256 := by
    have hb1 : s0.sp - 352#64 + 32#64 = s0.sp - 320#64 := by bv_omega
    have hb2 : s0.sp - 320#64 + 32#64 = s0.sp - 288#64 := by bv_omega
    have hb3 : s0.sp - 288#64 + 64#64 = s0.sp - 224#64 := by bv_omega
    have hb4 : s0.sp - 224#64 + 32#64 = s0.sp - 192#64 := by bv_omega
    rw [← hb4, ← memRegion_split (s0.sp - 224#64) 32 96 (by decide),
        ← hb3, ← memRegion_split (s0.sp - 288#64) 64 128 (by decide),
        ← hb2, ← memRegion_split (s0.sp - 320#64) 32 192 (by decide),
        ← hb1, ← memRegion_split (s0.sp - 352#64) 32 224 (by decide)]
  unfold cmkLoopHeap cmkLoopFrame advanceChainKeyFrame
  rw [stackAt_7712_split_2048 s0.sp]
  have hreord1 :
      (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
       (x.ckA ↦₆₄ q0_lo) ∗
       ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
       ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
       ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
       ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32)) ∗
       stackAt (s0.sp - 480#64) 2048 ∗
       (ratchetAt A x.self G' st' ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 8192#64) 5664 ∗
        memRegion (s0.sp - 480#64) 112 ∗
        ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
        memRegion (s0.sp - 360#64) 4 ∗
        memRegion (s0.sp - 352#64) 32 ∗
        memRegion (s0.sp - 288#64) 64 ∗
        memRegion (s0.sp - 192#64) 96 ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool)) =
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗ ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗ ((s0.sp - 200#64) ↦₆₄ q1_hi)) ∗
       (((s0.sp - 320#64) ↦₆₄ q0_lo) ∗ ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗ ((s0.sp - 296#64) ↦₆₄ q1_hi)) ∗
       ((x.ckA ↦₆₄ q0_lo) ∗ ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
        ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗ ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
        ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) ∗
       (ratchetAt A x.self G' st' ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        (memRegion (s0.sp - 8192#64) 5664 ∗ stackAt (s0.sp - 480#64) 2048) ∗
        memRegion (s0.sp - 480#64) 112 ∗
        ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
        memRegion (s0.sp - 360#64) 4 ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        memRegion (s0.sp - 352#64) 32 ∗
        memRegion (s0.sp - 288#64) 64 ∗
        memRegion (s0.sp - 192#64) 96 ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool)) := by ac_rfl
  rw [hreord1, hckA_full]
  refine Entails.trans (sepConj_mono h224 (sepConj_mono_left h320)) ?_
  rw [← h256]
  exact Entails.of_eq (by ac_rfl)

private def advanceChainKeyFrameAt (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (s0 : State) : SepProp :=
  ratchetAt A x.self G' st' ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  memRegion x.ret 88 ∗
  (logAddr ↦₆₄ 0#64) ∗
  memRegion (s0.sp - 8192#64) 5664 ∗
  memRegion (s0.sp - 480#64) 112 ∗
  ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
  memRegion (s0.sp - 360#64) 4 ∗
  memRegion (s0.sp - 352#64) 32 ∗
  memRegion (s0.sp - 288#64) 64 ∗
  memRegion (s0.sp - 192#64) 96 ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

private theorem cmkLoopHeapAt_advanceChainKey_split (A : RustAlloc) (logAddr : BitVec 64)
    (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (st' : RatchetState) (ckc : ChainKey) (s0 : State) :
    cmkLoopHeapAt A logAddr x G' st' ckc s0 =
      ∃∗ b320 : BitVec 8,
        ((s0.sp - 320#64) ↦₈ b320) ∗
        (memRegion (s0.sp - 224#64) 32 ∗
         (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
         stackAt (s0.sp - 480#64) 2048 ∗
         memRegion (s0.sp - 319#64) 31 ∗
         ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
         ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
         advanceChainKeyFrameAt A logAddr x G' st' s0) := by
  unfold cmkLoopHeapAt cmkLoopFrame advanceChainKeyFrameAt
  rw [chainKeyBytes_pointsTo x.ckA ckc,
      stackAt_7712_split_2048 s0.sp,
      memRegion_256_advanceChainKey_split s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext b320
  ac_rfl

private theorem advanceChainKeyPost_entails_cmkLoopHeapAt (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (ckc : ChainKey)
    (q0_lo q0_hi q1_lo q1_hi : BitVec 64)
    (hq0_lo : q0_lo = pack64 ((hmacWith F (keyToBytes32 ckc.key) [2#8]).take 8))
    (hq0_hi : q0_hi = pack64 (((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 8).take 8))
    (hq1_lo : q1_lo = pack64 (((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 16).take 8))
    (hq1_hi : q1_hi = pack64 ((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 24))
    (s0 : State) :
    (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
     ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
     ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
     ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
     ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
     ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
     ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
     ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
     ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
     (x.ckA ↦₆₄ q0_lo) ∗
     ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
     ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
     ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
     ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32)) ∗
     stackAt (s0.sp - 480#64) 2048 ∗
     advanceChainKeyFrameAt A logAddr x G' st' s0) ⊢
      cmkLoopHeapAt A logAddr x G' st' (chainStepN F 1 ckc) s0 := by
  let bs := hmacWith F (keyToBytes32 ckc.key) [2#8]
  have hbs : bs.length = 32 := hmacWith_length F (keyToBytes32 ckc.key) [2#8]
  have hck'_key : keyToBytes32 (chainStepN F 1 ckc).key = bs := by
    change keyToBytes32 (bytesToKey32 bs) = bs
    exact keyToBytes32_bytesToKey32 bs hbs
  have hck'_idx : (chainStepN F 1 ckc).index = ckc.index + 1#32 := rfl
  have hckA_words :
      ((x.ckA ↦₆₄ q0_lo) ∗ ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
       ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗ ((x.ckA + 24#64) ↦₆₄ q1_hi)) =
      (x.ckA ↦ₛ bs) := by
    rw [hq0_lo, hq0_hi, hq1_lo, hq1_hi, ← pointsToBytes_32_eq_pointsTo64 x.ckA bs hbs]
  have hckA_full :
      ((x.ckA ↦₆₄ q0_lo) ∗ ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
       ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗ ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
       ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) =
      (x.ckA ↦ₛ chainKeyBytes (chainStepN F 1 ckc)) := by
    rw [chainKeyBytes_pointsTo x.ckA (chainStepN F 1 ckc), hck'_key, hck'_idx, ← hckA_words]
    ac_rfl
  have h224 := pointsTo64_4_entails_memRegion_32 (s0.sp - 224#64) q0_lo q0_hi q1_lo q1_hi
  have h320 := pointsTo64_4_entails_memRegion_32 (s0.sp - 320#64) q0_lo q0_hi q1_lo q1_hi
  have ha216 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_omega
  have ha208 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
  have ha200 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_omega
  have ha312 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_omega
  have ha304 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_omega
  have ha296 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_omega
  rw [ha216, ha208, ha200] at h224
  rw [ha312, ha304, ha296] at h320
  have h256 :
      (memRegion (s0.sp - 352#64) 32 ∗
       memRegion (s0.sp - 320#64) 32 ∗
       memRegion (s0.sp - 288#64) 64 ∗
       memRegion (s0.sp - 224#64) 32 ∗
       memRegion (s0.sp - 192#64) 96) =
      memRegion (s0.sp - 352#64) 256 := by
    have hb1 : s0.sp - 352#64 + 32#64 = s0.sp - 320#64 := by bv_omega
    have hb2 : s0.sp - 320#64 + 32#64 = s0.sp - 288#64 := by bv_omega
    have hb3 : s0.sp - 288#64 + 64#64 = s0.sp - 224#64 := by bv_omega
    have hb4 : s0.sp - 224#64 + 32#64 = s0.sp - 192#64 := by bv_omega
    rw [← hb4, ← memRegion_split (s0.sp - 224#64) 32 96 (by decide),
        ← hb3, ← memRegion_split (s0.sp - 288#64) 64 128 (by decide),
        ← hb2, ← memRegion_split (s0.sp - 320#64) 32 192 (by decide),
        ← hb1, ← memRegion_split (s0.sp - 352#64) 32 224 (by decide)]
  unfold cmkLoopHeapAt cmkLoopFrame advanceChainKeyFrameAt
  rw [stackAt_7712_split_2048 s0.sp]
  have hreord1 :
      (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
       (x.ckA ↦₆₄ q0_lo) ∗
       ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
       ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
       ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
       ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32)) ∗
       stackAt (s0.sp - 480#64) 2048 ∗
       (ratchetAt A x.self G' st' ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        memRegion x.ret 88 ∗
        (logAddr ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 8192#64) 5664 ∗
        memRegion (s0.sp - 480#64) 112 ∗
        ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
        memRegion (s0.sp - 360#64) 4 ∗
        memRegion (s0.sp - 352#64) 32 ∗
        memRegion (s0.sp - 288#64) 64 ∗
        memRegion (s0.sp - 192#64) 96 ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool)) =
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗ ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗ ((s0.sp - 200#64) ↦₆₄ q1_hi)) ∗
       (((s0.sp - 320#64) ↦₆₄ q0_lo) ∗ ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗ ((s0.sp - 296#64) ↦₆₄ q1_hi)) ∗
       ((x.ckA ↦₆₄ q0_lo) ∗ ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
        ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗ ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
        ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) ∗
       (ratchetAt A x.self G' st' ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        memRegion x.ret 88 ∗
        (logAddr ↦₆₄ 0#64) ∗
        (memRegion (s0.sp - 8192#64) 5664 ∗ stackAt (s0.sp - 480#64) 2048) ∗
        memRegion (s0.sp - 480#64) 112 ∗
        ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
        memRegion (s0.sp - 360#64) 4 ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        memRegion (s0.sp - 352#64) 32 ∗
        memRegion (s0.sp - 288#64) 64 ∗
        memRegion (s0.sp - 192#64) 96 ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool)) := by ac_rfl
  rw [hreord1, hckA_full]
  refine Entails.trans (sepConj_mono h224 (sepConj_mono_left h320)) ?_
  rw [← h256]
  exact Entails.of_eq (by ac_rfl)

/-! ## Symbolic Execution of `AdvanceChainKey` -/

private theorem advanceChainKey_preHmac_wp (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (b320 : BitVec 8) (s0 s : State)
    (hstat : s.status = .Running)
    (hpc : s.pc = (SP b F alloc).fnAddr cmkSym + 1140#64)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (SP b F alloc) ((SP b F alloc).fnAddr cmkSym + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) s
      ((s0.sp - 320#64) ↦₈ b320)
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ((s0.sp - 320#64) ↦₈ 2#8) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x0 = s0.sp - 224#64 ∧
        sf.readReg64 .x1 = x.ckA ∧
        sf.readReg64 .x2 = 32#64 ∧
        sf.readReg64 .x3 = s0.sp - 320#64 ∧
        sf.readReg64 .x4 = 1#64 ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x22 = x.theirA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.readReg64 .x30 = (SP b F alloc).fnAddr cmkSym + 1172#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  cmk_fetches_range b (Rust.withPanics (sessionExterns F alloc)) hfn 285 293
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  unfold SP cmkSym at *
  generalize (libsignalSessionCode.rebase b (Rust.withPanics (sessionExterns F alloc))).fnAddr
    "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" = entry at *
  examples_hide_fetches
  wp_steps
  wp_done

private theorem advanceChainKey_hmac_wp (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hHmac : HmacOk img F alloc)
    (x : ConsumeMessageKeyGhost) (ckc : ChainKey) (s0 s : State)
    (hstat : s.status = .Running)
    (hpc : s.pc = (SP img.base F alloc).fnAddr cmkSym + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = s0.sp - 224#64)
    (hx1 : s.readReg64 .x1 = x.ckA)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hx3 : s.readReg64 .x3 = s0.sp - 320#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx30 : s.readReg64 .x30 = (SP img.base F alloc).fnAddr cmkSym + 1172#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hfrozen : img.FrozenLoaded s)
    (hsymtab : s.symtab = img.symtab) :
    SepWP (SP img.base F alloc) ((SP img.base F alloc).fnAddr cmkSym + 1172#64) s
      (memRegion (s0.sp - 224#64) 32 ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
       stackAt (s0.sp - 480#64) 2048)
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (((s0.sp - 224#64) ↦ₛ hmacWith F (keyToBytes32 ckc.key) [2#8]) ∗
             (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
             ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
             stackAt (s0.sp - 480#64) 2048) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x22 = x.theirA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hhmac := hmac_ok_at_cmk himg hHmac
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  unfold SP cmkSym at *
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics (sessionExterns F alloc))).fnAddr
    "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" = entry at *
  wp_apply
  wp_done

theorem add_one_ne_zero_of_lt {idx ctr : BitVec 32} (h : idx < ctr) :
    idx + 1#32 ≠ 0#32 := by
  intro heq
  have hlt_nat : idx.toNat < ctr.toNat := BitVec.lt_def.mp h
  have hctr : ctr.toNat < 2 ^ 32 := ctr.isLt
  have hadd : (idx + 1#32).toNat = idx.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0 : (idx + 1#32).toNat = 0 := by rw [heq]; rfl
  omega

private theorem advanceChainKey_postHmac_wp (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (ckc : ChainKey)
    (q0_lo q0_hi q1_lo q1_hi k0 k1 k2 k3 t0 t1 t2 t3 : BitVec 64)
    (s0 s : State)
    (hstat : s.status = .Running)
    (hpc : s.pc = (SP b F alloc).fnAddr cmkSym + 1172#64)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlt : ckc.index < x.counter) :
    SepWP (SP b F alloc)
      (if (ckc.index + 1#32) < x.counter
       then (SP b F alloc).fnAddr cmkSym + 820#64
       else (SP b F alloc).fnAddr cmkSym + 1244#64)
      s
      (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦₆₄ t0) ∗
       ((s0.sp - 312#64) ↦₆₄ t1) ∗
       ((s0.sp - 304#64) ↦₆₄ t2) ∗
       ((s0.sp - 296#64) ↦₆₄ t3) ∗
       (x.ckA ↦₆₄ k0) ∗
       ((x.ckA + 8#64) ↦₆₄ k1) ∗
       ((x.ckA + 16#64) ↦₆₄ k2) ∗
       ((x.ckA + 24#64) ↦₆₄ k3) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index))
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
             ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
             ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
             ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
             ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
             ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
             ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
             ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
             ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
             (x.ckA ↦₆₄ q0_lo) ∗
             ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
             ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
             ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
             ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x26 = x.theirA ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x28 = (ckc.index + 1#32).zeroExtend 64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  cmk_fetches_range b (Rust.withPanics (sessionExterns F alloc)) hfn 293 306
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have hne0 : ckc.index + 1#32 ≠ 0#32 := add_one_ne_zero_of_lt hlt
  unfold SP cmkSym at *
  generalize (libsignalSessionCode.rebase b (Rust.withPanics (sessionExterns F alloc))).fnAddr
    "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" = entry at *
  examples_hide_fetches
  wp_steps
  wp_if hloop
  · have hlt' : ckc.index + 1#32 < x.counter := BitVec.ult_iff_lt.mp hloop
    simp only [hlt', ↓reduceIte]
    wp_done
  · have hnlt' : ¬ (ckc.index + 1#32 < x.counter) := mt BitVec.ult_iff_lt.mpr hloop
    simp only [hnlt', ↓reduceIte]
    wp_steps
    wp_done

/-! ## Top-Level `AdvanceChainKeySpec` Proof -/

theorem advanceChainKey_ok (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) :
    AdvanceChainKeySpec F A alloc img := by
  intro himg hHmac x G' st' ckc R s0 sD hlt hD hL
  dsimp only
  rcases hD with
    ⟨hpc,
     ⟨hstat, hsp, hsp0_align, _hsp_align, hx29, htr, hfrozen, hsymtab, hvregs⟩,
     ⟨hx19, hx21, hx22, hx23, hx27⟩,
     hmem⟩
  have hprog : sessionProg img F alloc = SP img.base F alloc := sessionProg_eq_SP himg F alloc
  rw [hprog] at hL ⊢
  have hpc' : sD.pc = (SP img.base F alloc).fnAddr cmkSym + 1140#64 := by
    rw [hpc, cmkAdvanceChainKeyPC_eq_fnAddr himg F alloc]
  rw [cmkLoopHeap_advanceChainKey_split A img x G' st' ckc s0] at hmem
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmem
  rcases hmem with ⟨b320, hmem⟩
  rw [sepConj_assoc] at hmem
  let R1 : SepProp :=
    (memRegion (s0.sp - 224#64) 32 ∗
     (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
     stackAt (s0.sp - 480#64) 2048 ∗
     memRegion (s0.sp - 319#64) 31 ∗
     ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
     ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
     advanceChainKeyFrame A img x G' st' s0) ∗ R
  rcases (advanceChainKey_preHmac_wp img.base F alloc x b320 s0 sD hstat hpc' hsp hsp0_align
      hx19 hx21 hx22 hx23 hx27 hx29 ⟨htr, hvregs⟩).elim hmem hL with
    ⟨s1, hsteps1, ⟨_hpc1, hstat1, P_f1, hm1, hpost1,
      hsp1, _hsp1_align, htr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1,
      hx19_1, hx21_1, hx22_1, hx23_1, hx27_1, hx29_1, hx30_1⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem1 := hpost1 R1 hm1
  rw [pointsTo8_eq_pointsToBytes_singleton (s0.sp - 320#64) 2#8] at hmem1
  have hreord1 :
      (((s0.sp - 320#64) ↦ₛ [2#8]) ∗ R1) =
      ((memRegion (s0.sp - 224#64) 32 ∗
        (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
        ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
        stackAt (s0.sp - 480#64) 2048) ∗
       (memRegion (s0.sp - 319#64) 31 ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
        advanceChainKeyFrame A img x G' st' s0 ∗ R)) := by
    dsimp only [R1]
    ac_rfl
  rw [hreord1] at hmem1
  let R2 : SepProp :=
    memRegion (s0.sp - 319#64) 31 ∗
    ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
    ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
    advanceChainKeyFrame A img x G' st' s0 ∗ R
  have hfrozen1 : img.FrozenLoaded s1 := hfrozen.of_keepsFrozen hsteps1.keepsFrozen
  have hsymtab1 : s1.symtab = img.symtab := hsteps1.symtab_eq.trans hsymtab
  have hL1 : (SP img.base F alloc).CodeLoaded s1.mem := hsteps1.codeLoaded hL
  rcases (advanceChainKey_hmac_wp img F alloc himg hHmac x ckc s0 s1 hstat1 _hpc1 hsp1 hsp0_align
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx19_1 hx21_1 hx22_1 hx23_1 hx27_1 hx29_1 hx30_1
      htr1 hfrozen1 hsymtab1).elim hmem1 hL1 with
    ⟨s2, hsteps2, ⟨_hpc2, hstat2, P_f2, hm2, hpost2,
      hsp2, _hsp2_align, htr2, hx19_2, hx21_2, hx22_2, hx23_2, hx27_2, hx29_2⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem2 := hpost2 R2 hm2
  let bs := hmacWith F (keyToBytes32 ckc.key) [2#8]
  have hbs : bs.length = 32 := hmacWith_length F (keyToBytes32 ckc.key) [2#8]
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  have h320_combine :
      (((s0.sp - 320#64) ↦ₛ [2#8]) ∗ memRegion (s0.sp - 319#64) 31) ⊢
        memRegion (s0.sp - 320#64) 32 := by
    refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion (s0.sp - 320#64) [2#8])) ?_
    have ha319 : s0.sp - 320#64 + 1#64 = s0.sp - 319#64 := by bv_omega
    change (memRegion (s0.sp - 320#64) 1 ∗ memRegion (s0.sp - 319#64) 31) ⊢ _
    rw [← ha319, ← memRegion_split (s0.sp - 320#64) 1 31 (by decide)]
    exact Entails.refl _
  have hreord2 :
      ((((s0.sp - 224#64) ↦ₛ bs) ∗
        (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
        ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
        stackAt (s0.sp - 480#64) 2048) ∗ R2) =
      ((((s0.sp - 320#64) ↦ₛ [2#8]) ∗ memRegion (s0.sp - 319#64) 31) ∗
       ((s0.sp - 224#64) ↦ₛ bs) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       stackAt (s0.sp - 480#64) 2048 ∗
       advanceChainKeyFrame A img x G' st' s0 ∗ R) := by
    dsimp only [R2]
    ac_rfl
  rw [hreord2] at hmem2
  have hmem2' := Satisfies.mono (sepConj_mono_left h320_combine) hmem2
  rw [memRegion_32_eq_exists_pointsTo64_4 (s0.sp - 320#64),
      pointsToBytes_32_eq_pointsTo64 (s0.sp - 224#64) bs hbs,
      pointsToBytes_32_eq_pointsTo64 x.ckA (keyToBytes32 ckc.key) hkey_len] at hmem2'
  have ha216 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_omega
  have ha208 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
  have ha200 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_omega
  have ha312 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_omega
  have ha304 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_omega
  have ha296 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_omega
  rw [ha216, ha208, ha200, ha312, ha304, ha296] at hmem2'
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmem2'
  rcases hmem2' with ⟨t0, t1, t2, t3, hmem2'⟩
  let q0_lo := pack64 (bs.take 8)
  let q0_hi := pack64 ((bs.drop 8).take 8)
  let q1_lo := pack64 ((bs.drop 16).take 8)
  let q1_hi := pack64 (bs.drop 24)
  let k0 := pack64 ((keyToBytes32 ckc.key).take 8)
  let k1 := pack64 (((keyToBytes32 ckc.key).drop 8).take 8)
  let k2 := pack64 (((keyToBytes32 ckc.key).drop 16).take 8)
  let k3 := pack64 ((keyToBytes32 ckc.key).drop 24)
  have hreord3 :
      ((((s0.sp - 320#64) ↦₆₄ t0) ∗ ((s0.sp - 312#64) ↦₆₄ t1) ∗
        ((s0.sp - 304#64) ↦₆₄ t2) ∗ ((s0.sp - 296#64) ↦₆₄ t3)) ∗
       (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗ ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗ ((s0.sp - 200#64) ↦₆₄ q1_hi)) ∗
       ((x.ckA ↦₆₄ k0) ∗ ((x.ckA + 8#64) ↦₆₄ k1) ∗
        ((x.ckA + 16#64) ↦₆₄ k2) ∗ ((x.ckA + 24#64) ↦₆₄ k3)) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       stackAt (s0.sp - 480#64) 2048 ∗
       advanceChainKeyFrame A img x G' st' s0 ∗ R) =
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦₆₄ t0) ∗
        ((s0.sp - 312#64) ↦₆₄ t1) ∗
        ((s0.sp - 304#64) ↦₆₄ t2) ∗
        ((s0.sp - 296#64) ↦₆₄ t3) ∗
        (x.ckA ↦₆₄ k0) ∗
        ((x.ckA + 8#64) ↦₆₄ k1) ∗
        ((x.ckA + 16#64) ↦₆₄ k2) ∗
        ((x.ckA + 24#64) ↦₆₄ k3) ∗
        ((x.ckA + 32#64) ↦₃₂ ckc.index)) ∗
       (stackAt (s0.sp - 480#64) 2048 ∗ advanceChainKeyFrame A img x G' st' s0 ∗ R)) := by ac_rfl
  rw [hreord3] at hmem2'
  let R3 : SepProp := stackAt (s0.sp - 480#64) 2048 ∗ advanceChainKeyFrame A img x G' st' s0 ∗ R
  have hL2 : (SP img.base F alloc).CodeLoaded s2.mem := hsteps2.codeLoaded hL1
  rcases (advanceChainKey_postHmac_wp img.base F alloc x ckc q0_lo q0_hi q1_lo q1_hi k0 k1 k2 k3 t0 t1 t2 t3
      s0 s2 hstat2 _hpc2 hsp2 hsp0_align hx19_2 hx21_2 hx22_2 hx23_2 hx27_2 hx29_2
      htr2 hlt).elim hmem2' hL2 with
    ⟨s', hsteps3, ⟨hpc', hstat', P_f3, hm3, hpost3,
      hsp', hsp'_align, htr', hx19', hx21', hx23', hx26', hx27', hx28', hx29'⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem3 := hpost3 R3 hm3
  have hreord4 :
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
        (x.ckA ↦₆₄ q0_lo) ∗
        ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
        ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
        ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
        ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) ∗ R3) =
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
        (x.ckA ↦₆₄ q0_lo) ∗
        ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
        ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
        ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
        ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32)) ∗
        stackAt (s0.sp - 480#64) 2048 ∗
        advanceChainKeyFrame A img x G' st' s0) ∗ R) := by
    dsimp only [R3]
    ac_rfl
  rw [hreord4] at hmem3
  have hmem_final := Satisfies.mono
    (sepConj_mono_left
      (advanceChainKeyPost_entails_cmkLoopHeap F A img x G' st' ckc q0_lo q0_hi q1_lo q1_hi rfl rfl rfl rfl s0))
    hmem3
  have hsteps_all : Steps (SP img.base F alloc) sD s' :=
    (hsteps1.trans hsteps2).trans hsteps3
  have hnextPC_eq :
      (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC img else cmkEpiloguePC img) =
      (if (ckc.index + 1#32) < x.counter
       then (SP img.base F alloc).fnAddr cmkSym + 820#64
       else (SP img.base F alloc).fnAddr cmkSym + 1244#64) := by
    rw [cmkLoopPC_eq_fnAddr himg F alloc, cmkEpiloguePC_eq_fnAddr himg F alloc]
    rfl
  refine ⟨s', hsteps_all, ?_⟩
  refine ⟨by rw [hnextPC_eq]; exact hpc',
    ⟨hstat', hsp', hsp0_align, hsp'_align, hx29', htr'.1,
     hfrozen.of_keepsFrozen hsteps_all.keepsFrozen,
     hsteps_all.symtab_eq.trans hsymtab, htr'.2⟩,
    ⟨hx21', hx23', hx26', hx27', hx28'⟩,
    fun _ => hx19',
    hmem_final⟩

private theorem advanceChainKey_preHmac_placed_wp [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (b320 : BitVec 8) (s0 s : State)
    (hstat : s.status = .Running)
    (hpc : s.pc = (blkPl_24).base + 1140#64)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) s
      ((s0.sp - 320#64) ↦₈ b320)
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ((s0.sp - 320#64) ↦₈ 2#8) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x0 = s0.sp - 224#64 ∧
        sf.readReg64 .x1 = x.ckA ∧
        sf.readReg64 .x2 = 32#64 ∧
        sf.readReg64 .x3 = s0.sp - 320#64 ∧
        sf.readReg64 .x4 = 1#64 ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x22 = x.theirA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.readReg64 .x30 = (blkPl_24).base + 1172#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  wp_steps
  wp_done

private theorem advanceChainKey_hmac_placed_wp [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    (H : String → Option (State → State))
    (xg : ConsumeMessageKeyGhost) (ckc : ChainKey) (s0 s : State)
    (hhmac : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s))
    (hstat : s.status = .Running)
    (hpc : s.pc = lsmpl.base 73)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = s0.sp - 224#64)
    (hx1 : s.readReg64 .x1 = xg.ckA)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hx3 : s.readReg64 .x3 = s0.sp - 320#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = xg.ckA)
    (hx22 : s.readReg64 .x22 = xg.theirA)
    (hx23 : s.readReg64 .x23 = xg.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx30 : s.readReg64 .x30 = (blkPl_24).base + 1172#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1172#64) s
      (memRegion (s0.sp - 224#64) 32 ∗
       (xg.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
       stackAt (s0.sp - 480#64) 2048)
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (((s0.sp - 224#64) ↦ₛ hmacWith F (keyToBytes32 ckc.key) [2#8]) ∗
             (xg.ckA ↦ₛ keyToBytes32 ckc.key) ∗
             ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
             stackAt (s0.sp - 480#64) 2048) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = xg.ckA ∧
        sf.readReg64 .x22 = xg.theirA ∧
        sf.readReg64 .x23 = xg.self ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  wp_call hhmac (s0.sp - 224#64, xg.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [2#8])
  wp_done

private theorem advanceChainKey_postHmac_placed_wp [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (ckc : ChainKey)
    (q0_lo q0_hi q1_lo q1_hi k0 k1 k2 k3 t0 t1 t2 t3 : BitVec 64)
    (s0 s : State)
    (hstat : s.status = .Running)
    (hpc : s.pc = (blkPl_24).base + 1172#64)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlt : ckc.index < x.counter) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H)
      (if (ckc.index + 1#32) < x.counter
       then (blkPl_24).base + 820#64
       else (blkPl_24).base + 1244#64)
      s
      (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦₆₄ t0) ∗
       ((s0.sp - 312#64) ↦₆₄ t1) ∗
       ((s0.sp - 304#64) ↦₆₄ t2) ∗
       ((s0.sp - 296#64) ↦₆₄ t3) ∗
       (x.ckA ↦₆₄ k0) ∗
       ((x.ckA + 8#64) ↦₆₄ k1) ∗
       ((x.ckA + 16#64) ↦₆₄ k2) ∗
       ((x.ckA + 24#64) ↦₆₄ k3) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index))
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
             ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
             ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
             ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
             ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
             ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
             ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
             ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
             ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
             (x.ckA ↦₆₄ q0_lo) ∗
             ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
             ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
             ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
             ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x26 = x.theirA ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x28 = (ckc.index + 1#32).zeroExtend 64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have hne0 : ckc.index + 1#32 ≠ 0#32 := add_one_ne_zero_of_lt hlt
  wp_steps
  wp_if hloop
  · have hlt' : ckc.index + 1#32 < x.counter := BitVec.ult_iff_lt.mp hloop
    simp only [hlt', ↓reduceIte]
    wp_done
  · have hnlt' : ¬ (ckc.index + 1#32 < x.counter) := mt BitVec.ult_iff_lt.mpr hloop
    simp only [hnlt', ↓reduceIte]
    wp_steps
    wp_done

private theorem advanceChainKey_placed_ok_of_hmac [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    {Inv : Memory → Prop}
    (hinv_kf : ∀ m m', Inv m → m.KeepsFrozen m' → Inv m')
    (hhmac_at : ∀ {s1 : State}, Inv s1.mem →
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s1))
    (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (st' : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (R : SepProp) (s0 sD : State)
    (hlt : ckc.index < x.counter)
    (hD : AdvanceChainKeyState_placed A x G' st' ckc R s0 sD)
    (hL : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded sD.mem)
    (hinv : Inv sD.mem) :
    let ck' := chainStepN F 1 ckc
    let nextPC := if ck'.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
    ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) sD s' ∧
      CmkLoopState_placed A x G' st' ck' R nextPC s0 s' := by
  dsimp only
  rcases hD with
    ⟨hpc,
     ⟨hstat, hsp, hsp0_align, _hsp_align, hx29, htr, hcl, hvregs⟩,
     ⟨hx19, hx21, hx22, hx23, hx27⟩,
     hmem⟩
  have hpc' : sD.pc = (blkPl_24).base + 1140#64 := hpc
  rw [cmkLoopHeap_placed_eq_at, cmkLoopHeapAt_advanceChainKey_split A lsLogFilterAddr x G' st' ckc s0] at hmem
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmem
  rcases hmem with ⟨b320, hmem⟩
  rw [sepConj_assoc] at hmem
  let R1 : SepProp :=
    (memRegion (s0.sp - 224#64) 32 ∗
     (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
     stackAt (s0.sp - 480#64) 2048 ∗
     memRegion (s0.sp - 319#64) 31 ∗
     ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
     ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
     advanceChainKeyFrameAt A lsLogFilterAddr x G' st' s0) ∗ R
  rcases (advanceChainKey_preHmac_placed_wp H x b320 s0 sD hstat hpc' hsp hsp0_align
      hx19 hx21 hx22 hx23 hx27 hx29 ⟨htr, hvregs⟩).elim hmem hL with
    ⟨s1, hsteps1, ⟨_hpc1, hstat1, P_f1, hm1, hpost1,
      hsp1, _hsp1_align, htr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1,
      hx19_1, hx21_1, hx22_1, hx23_1, hx27_1, hx29_1, hx30_1⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem1 := hpost1 R1 hm1
  rw [pointsTo8_eq_pointsToBytes_singleton (s0.sp - 320#64) 2#8] at hmem1
  have hreord1 :
      (((s0.sp - 320#64) ↦ₛ [2#8]) ∗ R1) =
      ((memRegion (s0.sp - 224#64) 32 ∗
        (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
        ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
        stackAt (s0.sp - 480#64) 2048) ∗
       (memRegion (s0.sp - 319#64) 31 ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
        advanceChainKeyFrameAt A lsLogFilterAddr x G' st' s0 ∗ R)) := by
    dsimp only [R1]
    ac_rfl
  rw [hreord1] at hmem1
  let R2 : SepProp :=
    memRegion (s0.sp - 319#64) 31 ∗
    ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
    ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
    advanceChainKeyFrameAt A lsLogFilterAddr x G' st' s0 ∗ R
  have hinv1 : Inv s1.mem := hinv_kf _ _ hinv hsteps1.keepsFrozen
  have hL1 : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s1.mem := hsteps1.codeLoaded hL
  rcases (advanceChainKey_hmac_placed_wp F H (xg := x) ckc s0 s1 (hhmac_at hinv1) hstat1 _hpc1 hsp1 hsp0_align
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx19_1 hx21_1 hx22_1 hx23_1 hx27_1 hx29_1 hx30_1
      htr1).elim hmem1 hL1 with
    ⟨s2, hsteps2, ⟨_hpc2, hstat2, P_f2, hm2, hpost2,
      hsp2, _hsp2_align, htr2, hx19_2, hx21_2, hx22_2, hx23_2, hx27_2, hx29_2⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem2 := hpost2 R2 hm2
  let bs := hmacWith F (keyToBytes32 ckc.key) [2#8]
  have hbs : bs.length = 32 := hmacWith_length F (keyToBytes32 ckc.key) [2#8]
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  have h320_combine :
      (((s0.sp - 320#64) ↦ₛ [2#8]) ∗ memRegion (s0.sp - 319#64) 31) ⊢
        memRegion (s0.sp - 320#64) 32 := by
    refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion (s0.sp - 320#64) [2#8])) ?_
    have ha319 : s0.sp - 320#64 + 1#64 = s0.sp - 319#64 := by bv_omega
    change (memRegion (s0.sp - 320#64) 1 ∗ memRegion (s0.sp - 319#64) 31) ⊢ _
    rw [← ha319, ← memRegion_split (s0.sp - 320#64) 1 31 (by decide)]
    exact Entails.refl _
  have hreord2 :
      ((((s0.sp - 224#64) ↦ₛ bs) ∗
        (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
        ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
        stackAt (s0.sp - 480#64) 2048) ∗ R2) =
      ((((s0.sp - 320#64) ↦ₛ [2#8]) ∗ memRegion (s0.sp - 319#64) 31) ∗
       ((s0.sp - 224#64) ↦ₛ bs) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       stackAt (s0.sp - 480#64) 2048 ∗
       advanceChainKeyFrameAt A lsLogFilterAddr x G' st' s0 ∗ R) := by
    dsimp only [R2]
    ac_rfl
  rw [hreord2] at hmem2
  have hmem2' := Satisfies.mono (sepConj_mono_left h320_combine) hmem2
  rw [memRegion_32_eq_exists_pointsTo64_4 (s0.sp - 320#64),
      pointsToBytes_32_eq_pointsTo64 (s0.sp - 224#64) bs hbs,
      pointsToBytes_32_eq_pointsTo64 x.ckA (keyToBytes32 ckc.key) hkey_len] at hmem2'
  have ha216 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_omega
  have ha208 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
  have ha200 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_omega
  have ha312 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_omega
  have ha304 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_omega
  have ha296 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_omega
  rw [ha216, ha208, ha200, ha312, ha304, ha296] at hmem2'
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmem2'
  rcases hmem2' with ⟨t0, t1, t2, t3, hmem2'⟩
  let q0_lo := pack64 (bs.take 8)
  let q0_hi := pack64 ((bs.drop 8).take 8)
  let q1_lo := pack64 ((bs.drop 16).take 8)
  let q1_hi := pack64 (bs.drop 24)
  let k0 := pack64 ((keyToBytes32 ckc.key).take 8)
  let k1 := pack64 (((keyToBytes32 ckc.key).drop 8).take 8)
  let k2 := pack64 (((keyToBytes32 ckc.key).drop 16).take 8)
  let k3 := pack64 ((keyToBytes32 ckc.key).drop 24)
  have hreord3 :
      ((((s0.sp - 320#64) ↦₆₄ t0) ∗ ((s0.sp - 312#64) ↦₆₄ t1) ∗
        ((s0.sp - 304#64) ↦₆₄ t2) ∗ ((s0.sp - 296#64) ↦₆₄ t3)) ∗
       (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗ ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗ ((s0.sp - 200#64) ↦₆₄ q1_hi)) ∗
       ((x.ckA ↦₆₄ k0) ∗ ((x.ckA + 8#64) ↦₆₄ k1) ∗
        ((x.ckA + 16#64) ↦₆₄ k2) ∗ ((x.ckA + 24#64) ↦₆₄ k3)) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       stackAt (s0.sp - 480#64) 2048 ∗
       advanceChainKeyFrameAt A lsLogFilterAddr x G' st' s0 ∗ R) =
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦₆₄ t0) ∗
        ((s0.sp - 312#64) ↦₆₄ t1) ∗
        ((s0.sp - 304#64) ↦₆₄ t2) ∗
        ((s0.sp - 296#64) ↦₆₄ t3) ∗
        (x.ckA ↦₆₄ k0) ∗
        ((x.ckA + 8#64) ↦₆₄ k1) ∗
        ((x.ckA + 16#64) ↦₆₄ k2) ∗
        ((x.ckA + 24#64) ↦₆₄ k3) ∗
        ((x.ckA + 32#64) ↦₃₂ ckc.index)) ∗
       (stackAt (s0.sp - 480#64) 2048 ∗ advanceChainKeyFrameAt A lsLogFilterAddr x G' st' s0 ∗ R)) := by ac_rfl
  rw [hreord3] at hmem2'
  let R3 : SepProp := stackAt (s0.sp - 480#64) 2048 ∗ advanceChainKeyFrameAt A lsLogFilterAddr x G' st' s0 ∗ R
  have hL2 : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s2.mem := hsteps2.codeLoaded hL1
  rcases (advanceChainKey_postHmac_placed_wp H x ckc q0_lo q0_hi q1_lo q1_hi k0 k1 k2 k3 t0 t1 t2 t3
      s0 s2 hstat2 _hpc2 hsp2 hsp0_align hx19_2 hx21_2 hx22_2 hx23_2 hx27_2 hx29_2
      htr2 hlt).elim hmem2' hL2 with
    ⟨s', hsteps3, ⟨hpc', hstat', P_f3, hm3, hpost3,
      hsp', hsp'_align, htr', hx19', hx21', hx23', hx26', hx27', hx28', hx29'⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem3 := hpost3 R3 hm3
  have hreord4 :
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
        (x.ckA ↦₆₄ q0_lo) ∗
        ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
        ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
        ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
        ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) ∗ R3) =
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
        (x.ckA ↦₆₄ q0_lo) ∗
        ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
        ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
        ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
        ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32)) ∗
        stackAt (s0.sp - 480#64) 2048 ∗
        advanceChainKeyFrameAt A lsLogFilterAddr x G' st' s0) ∗ R) := by
    dsimp only [R3]
    ac_rfl
  rw [hreord4] at hmem3
  have hmem_final := Satisfies.mono
    (sepConj_mono_left
      (advanceChainKeyPost_entails_cmkLoopHeapAt F A lsLogFilterAddr x G' st' ckc q0_lo q0_hi q1_lo q1_hi rfl rfl rfl rfl s0))
    hmem3
  rw [← cmkLoopHeap_placed_eq_at] at hmem_final
  have hsteps_all : Steps ((blkPC_24).rebase (blkPl_24).base H) sD s' :=
    (hsteps1.trans hsteps2).trans hsteps3
  refine ⟨s', hsteps_all, ?_⟩
  refine ⟨hpc',
    ⟨hstat', hsp', hsp0_align, hsp'_align, hx29', htr'.1,
     hcl.of_keepsFrozen hsteps_all.keepsFrozen, htr'.2⟩,
    ⟨hx21', hx23', hx26', hx27', hx28'⟩,
    fun _ => hx19',
    hmem_final⟩

theorem advanceChainKey_placed_ok [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    AdvanceChainKeyPlacedSpec F A H := by
  intro hHmac x G' st' ckc R s0 sD hlt hD hL
  let ⟨_, ⟨_, _, _, _, _, _, hcl, _⟩, _⟩ := hD
  exact advanceChainKey_placed_ok_of_hmac F A H
    (Inv := LibsignalCodeLoaded lsmpl)
    (fun _ _ h hkf => h.of_keepsFrozen hkf)
    (fun h => hmac_placed_ok_at_state hHmac h)
    x G' st' ckc R s0 sD hlt hD hL hcl

theorem advanceChainKey_placed_ro_ok [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    AdvanceChainKeyPlacedRoSpec F A H := by
  intro hHmac x G' st' ckc R s0 sD hlt hD hL hro
  let ⟨_, ⟨_, _, _, _, _, _, hcl, _⟩, _⟩ := hD
  exact advanceChainKey_placed_ok_of_hmac F A H
    (Inv := fun m => LibsignalCodeLoaded lsmpl m ∧ LibsignalRoLoaded lsmpl m)
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen hr hkf⟩)
    (fun ⟨hc, hr⟩ => hmac_placed_ro_ok_at_state hHmac hc hr)
    x G' st' ckc R s0 sD hlt hD hL ⟨hcl, hro⟩

end CryptoVerification.LibsignalSession.StoreLoop
