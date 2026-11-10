/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneBase
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogue
import ProofLib.SepLogic.WPp

/-!
# `MessageKey` Clone Loop for `Chain::clone [local#3]` (`0x766c8`)

Proves the `message_keys` vector allocation, per-element `MessageKey` clone loop, and empty fast
path for `<session_structure::Chain as Clone>::clone [local#3]`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.ChainClone3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  fp_neg_48 fp_neg_40 fp_neg_32 fp_neg_24 fp_neg_12 fp_neg_8
  fp_neg_48_int fp_neg_40_int fp_neg_32_int fp_neg_24_int fp_neg_12_int fp_neg_8_int
attribute [local arm64_norm ↓, local wp_norm ↓]
  BS5.sp_setPC_pre BS5.sp_setMem_setPC_pre
  BS5.readReg64_setPC_pre BS5.readReg64_setMem_setPC_pre
  BS5.readReg32_setPC_pre BS5.readReg32_setMem_setPC_pre
  BS5.readReg_setPC_pre BS5.readReg_setMem_setPC_pre
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## 6. `MessageKey` Clone Loop (`0x38604 .. 0x38718` and `0x385c8 .. 0x38600`) -/

theorem mul104_ne_of_lt {doneLen total : Nat}
    (hlt : doneLen < total) (htot : total ≤ maxMessageKeys) :
    BitVec.ofNat 64 (104 * total) ≠ BitVec.ofNat 64 (104 * doneLen) := by
  intro heq
  have h1 : 104 * total < 2 ^ 64 := by unfold maxMessageKeys at htot; omega
  have h2 : 104 * doneLen < 2 ^ 64 := by unfold maxMessageKeys at htot; omega
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at ht
  omega

theorem mul104_beq_eq_false {doneLen total : Nat}
    (hlt : doneLen < total) (htot : total ≤ maxMessageKeys) :
    (BitVec.ofNat 64 (104 * total) == BitVec.ofNat 64 (104 * doneLen)) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul104_ne_of_lt hlt htot

theorem off_add_104 (doneLen : Nat) :
    BitVec.ofNat 64 (104 * doneLen) + 104#64 = BitVec.ofNat 64 (104 * (doneLen + 1)) := by
  simp [Nat.mul_add, BitVec.ofNat_add]

theorem ptr_off_add_104 (mkPtr' : BitVec 64) (doneLen : Nat) :
    mkPtr' + BitVec.ofNat 64 (104 * doneLen) + 104#64 =
      mkPtr' + BitVec.ofNat 64 (104 * (doneLen + 1)) := by
  rw [BitVec.add_assoc, off_add_104]

theorem memRegion_mk_cons (mkPtr' : BitVec 64) (doneLen n : Nat)
    (hn : n + 1 ≤ maxMessageKeys) :
    memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) (104 * (n + 1)) =
      memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) 104 ∗
      memRegion (mkPtr' + BitVec.ofNat 64 (104 * (doneLen + 1))) (104 * n) := by
  have hmul : 104 * (n + 1) = 104 + 104 * n := by omega
  have hle : 104 + 104 * n ≤ 2 ^ 64 := by unfold maxMessageKeys at hn; omega
  rw [hmul,
      ProofLib.memRegion_split (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) 104 (104 * n) hle,
      ptr_off_add_104]

theorem ofNat_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add]
  bv_omega

theorem fold_iter_messageKeys (A : RustAlloc)
    (gk : MessageKeyGhost) (mkg : MessageKeyGenerator)
    (srcCur dstCur seedPtr' : BitVec 64)
    (R0 R0b R1 R2 : SepProp)
    (hpos : 0 < mkg.seed.length)
    (hle : mkg.seed.length ≤ gk.seed.cap.toNat)
    (hlt : gk.seed.cap.toNat < 2 ^ 63)
    (hptr : gk.seed.ptr ≠ 0)
    (hptr' : seedPtr' ≠ 0#64) :
    ((seedPtr' ↦ₛ mkg.seed) ∗
      (gk.seed.ptr ↦ₛ mkg.seed) ∗
      R0 ∗
      R0b ∗
      A.live seedPtr' mkg.seed.length 1 ∗
      ((srcCur + 16#64) ↦₆₄ 0#64) ∗
      ((srcCur + 40#64) ↦₆₄ 0#64) ∗
      ((srcCur + 64#64) ↦₆₄ 0#64) ∗
      ((srcCur + 80#64) ↦₆₄ gk.seed.ptr) ∗
      ((srcCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((srcCur + 96#64) ↦₃₂ mkg.counter) ∗
      messageKeySourceFrame A gk mkg srcCur ∗
      R1 ∗
      (dstCur ↦₆₄ 0#64) ∗
      ((dstCur + 8#64) ↦₆₄ 1#64) ∗
      ((dstCur + 16#64) ↦₆₄ 0#64) ∗
      ((dstCur + 24#64) ↦₆₄ 0#64) ∗
      ((dstCur + 32#64) ↦₆₄ 1#64) ∗
      ((dstCur + 40#64) ↦₆₄ 0#64) ∗
      ((dstCur + 48#64) ↦₆₄ 0#64) ∗
      ((dstCur + 56#64) ↦₆₄ 1#64) ∗
      ((dstCur + 64#64) ↦₆₄ 0#64) ∗
      ((dstCur + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dstCur + 80#64) ↦₆₄ seedPtr') ∗
      ((dstCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dstCur + 96#64) ↦₃₂ mkg.counter) ∗
      memRegion (dstCur + 100#64) 4 ∗
      R2) ⊢
    (messageKeyAt A (gk, mkg) srcCur ∗
      messageKeyAt A
        (clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length) seedPtr', mkg) dstCur ∗
      R1 ∗ R0 ∗ R0b ∗ R2) := by
  have hlt_seed : mkg.seed.length < 2 ^ 63 := by omega
  rw [← fold_cloned_messageKeyAt A mkg seedPtr' dstCur hpos hlt_seed hptr',
      messageKeyAt_eq_source A gk mkg srcCur]
  have hgroup :
      ((seedPtr' ↦ₛ mkg.seed) ∗
        (gk.seed.ptr ↦ₛ mkg.seed) ∗
        R0 ∗
        R0b ∗
        A.live seedPtr' mkg.seed.length 1 ∗
        ((srcCur + 16#64) ↦₆₄ 0#64) ∗
        ((srcCur + 40#64) ↦₆₄ 0#64) ∗
        ((srcCur + 64#64) ↦₆₄ 0#64) ∗
        ((srcCur + 80#64) ↦₆₄ gk.seed.ptr) ∗
        ((srcCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((srcCur + 96#64) ↦₃₂ mkg.counter) ∗
        messageKeySourceFrame A gk mkg srcCur ∗
        R1 ∗
        (dstCur ↦₆₄ 0#64) ∗
        ((dstCur + 8#64) ↦₆₄ 1#64) ∗
        ((dstCur + 16#64) ↦₆₄ 0#64) ∗
        ((dstCur + 24#64) ↦₆₄ 0#64) ∗
        ((dstCur + 32#64) ↦₆₄ 1#64) ∗
        ((dstCur + 40#64) ↦₆₄ 0#64) ∗
        ((dstCur + 48#64) ↦₆₄ 0#64) ∗
        ((dstCur + 56#64) ↦₆₄ 1#64) ∗
        ((dstCur + 64#64) ↦₆₄ 0#64) ∗
        ((dstCur + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((dstCur + 80#64) ↦₆₄ seedPtr') ∗
        ((dstCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((dstCur + 96#64) ↦₃₂ mkg.counter) ∗
        memRegion (dstCur + 100#64) 4 ∗
        R2) =
      ((((srcCur + 16#64) ↦₆₄ 0#64) ∗
          ((srcCur + 40#64) ↦₆₄ 0#64) ∗
          ((srcCur + 64#64) ↦₆₄ 0#64) ∗
          ((srcCur + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((srcCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗
          ((srcCur + 96#64) ↦₃₂ mkg.counter) ∗
          messageKeySourceFrame A gk mkg srcCur) ∗
        ((dstCur ↦₆₄ 0#64) ∗
          ((dstCur + 8#64) ↦₆₄ 1#64) ∗
          ((dstCur + 16#64) ↦₆₄ 0#64) ∗
          ((dstCur + 24#64) ↦₆₄ 0#64) ∗
          ((dstCur + 32#64) ↦₆₄ 1#64) ∗
          ((dstCur + 40#64) ↦₆₄ 0#64) ∗
          ((dstCur + 48#64) ↦₆₄ 0#64) ∗
          ((dstCur + 56#64) ↦₆₄ 1#64) ∗
          ((dstCur + 64#64) ↦₆₄ 0#64) ∗
          ((dstCur + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dstCur + 80#64) ↦₆₄ seedPtr') ∗
          ((dstCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dstCur + 96#64) ↦₃₂ mkg.counter) ∗
          memRegion (dstCur + 100#64) 4 ∗
          A.live seedPtr' mkg.seed.length 1 ∗
          (seedPtr' ↦ₛ mkg.seed)) ∗
        R1 ∗ R0 ∗ R0b ∗ R2) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono_left (Entails.pure_right ⟨hpos, hle, hlt, hptr⟩ (Entails.refl _))

/-! ### `message_keys` Allocation, Loop Wrapper, and Empty Fast Path -/

theorem vecBuf_mk_nil_eq (A : RustAlloc) :
    vecBuf A 104 8 (messageKeyAt A) 0#64 8#64 [] = emp := by
  unfold vecBuf
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by decide, by decide, by decide⟩
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _

theorem vecBuf_mk_pos_eq (A : RustAlloc) (mkPtr' : BitVec 64)
    (xs : List (MessageKeyGhost × MessageKeyGenerator))
    (hpos : 0 < xs.length) (hmax : xs.length ≤ maxMessageKeys) (hptr' : mkPtr' ≠ 0#64) :
    vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 xs.length) mkPtr' xs =
      A.live mkPtr' (104 * xs.length) 8 ∗
      arrayAt (messageKeyAt A) 104 mkPtr' xs := by
  unfold vecBuf
  have hlt64 : xs.length < 2 ^ 64 := by unfold maxMessageKeys at hmax; omega
  have htoNat : (BitVec.ofNat 64 xs.length).toNat = xs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hne0 : BitVec.ofNat 64 xs.length ≠ 0 := ofNat_ne_zero_of_pos hpos hlt64
  have hptr_ne : mkPtr' ≠ 0 := hptr'
  have hcap_lt : xs.length * 104 < 2 ^ 63 := by unfold maxMessageKeys at hmax; omega
  have hmul_comm : xs.length * 104 = 104 * xs.length := Nat.mul_comm _ _
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, Nat.zero_mul,
      ProofLib.memRegion_zero, sepConj_emp, hmul_comm]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by rw [htoNat], by rw [htoNat]; exact hcap_lt, hptr_ne⟩
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, Nat.zero_mul,
      ProofLib.memRegion_zero, sepConj_emp, hmul_comm]
    exact Entails.refl _

def chainMkSourceFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
  A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
  memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
    ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_mk_source (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hpos : 0 < gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
        gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
      ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
      arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
      chainMkSourceFrame A gc a := by
  unfold protoChainAt chainMkSourceFrame vecAt vecHeader vecBuf
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  rw [hzip_len, ha56, ha64]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          (if gc.1.mkCap = 0 then emp
           else A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
             arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
             memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
               ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104)) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          (if gc.1.mkCap = 0 then emp
           else A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
             arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
             memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
               ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104)) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    have hne : gc.1.mkCap ≠ 0 := by
      intro h0; rw [h0] at hle; change gc.2.messageKeys.length ≤ 0 at hle; omega
    simp only [hne, ↓reduceIte]
    apply Entails.pure_right ⟨hle, hlt, hptr⟩
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    have hne : gc.1.mkCap ≠ 0 := by
      intro h0; rw [h0] at hle; change gc.2.messageKeys.length ≤ 0 at hle; omega
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [hne, ↓reduceIte, sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
          arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
            ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
          memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
            ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

structure SpillSlots where
  v0 : BitVec 64
  w1a : BitVec 32
  w1b : BitVec 32
  v2 : BitVec 64
  v3 : BitVec 64
  v4 : BitVec 64
  v5 : BitVec 64
  v6 : BitVec 64
  v7 : BitVec 64

theorem spillSlotsExist_eq_struct (sp : BitVec 64) :
    spillSlotsExist sp =
      ∃∗ s : SpillSlots,
        ((sp - 208#64) ↦₆₄ s.v0) ∗
        ((sp - 200#64) ↦₃₂ s.w1a) ∗
        ((sp - 196#64) ↦₃₂ s.w1b) ∗
        ((sp - 192#64) ↦₆₄ s.v2) ∗
        ((sp - 184#64) ↦₆₄ s.v3) ∗
        ((sp - 176#64) ↦₆₄ s.v4) ∗
        ((sp - 168#64) ↦₆₄ s.v5) ∗
        ((sp - 160#64) ↦₆₄ s.v6) ∗
        ((sp - 152#64) ↦₆₄ s.v7) := by
  unfold spillSlotsExist
  apply sepProp_eq_of_entails
  · refine entails_sepExists_sepConj_left fun v0 => ?_
    refine entails_pull_exists fun w1a => ?_
    refine entails_pull_exists fun w1b => ?_
    refine entails_pull_exists fun v2 => ?_
    refine entails_pull_exists fun v3 => ?_
    refine entails_pull_exists fun v4 => ?_
    refine entails_pull_exists fun v5 => ?_
    refine entails_pull_exists fun v6 => ?_
    rw [sepExists_sepConj_right]
    refine entails_sepExists_left fun v7 => ?_
    apply Entails.sepExists_right ⟨v0, w1a, w1b, v2, v3, v4, v5, v6, v7⟩
    dsimp only
    simp only [sepConj_assoc]
    exact Entails.refl _
  · refine entails_sepExists_left fun s => ?_
    exact sepConj_mono (Entails.sepExists_right s.v0 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.w1a (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.w1b (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v2 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v3 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v4 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v5 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v6 (Entails.refl _))
      (Entails.sepExists_right s.v7 (Entails.refl _)))))))))

def savedRegsCore (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
  (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a)

theorem savedRegsOnStack_eq_core (s0 : State) :
    savedRegsOnStack s0 =
      ∃∗ p : BitVec 64 × BitVec 32,
        ((s0.sp - 120#64) ↦₆₄ p.1) ∗
        ((s0.sp - 108#64) ↦₃₂ p.2) ∗
        savedRegsCore s0 := by
  unfold savedRegsOnStack savedRegsCore
  rw [show (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
        (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
        (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)) =
      ((∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
        (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b) ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
          (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a))) by ac_rfl]
  apply sepProp_eq_of_entails
  · refine entails_sepExists_sepConj_left fun v11 => ?_
    refine entails_pull_exists fun w12b => ?_
    apply Entails.sepExists_right (v11, w12b)
    rw [sepConj_assoc]
    exact Entails.refl _
  · refine entails_sepExists_left fun p => ?_
    exact sepConj_mono (Entails.sepExists_right p.1 (Entails.refl _))
      (sepConj_mono_left (Entails.sepExists_right p.2 (Entails.refl _)))

theorem map_snd_zip_of_length_eq {α β : Type} (xs : List α) (ys : List β)
    (hlen : xs.length = ys.length) :
    (xs.zip ys).map Prod.snd = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs' ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys' =>
      simp only [List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih ys' (Nat.succ.inj hlen)

theorem mul_104_eq (n : Nat) :
    BitVec.ofNat 64 n * 104#64 = BitVec.ofNat 64 (104 * n) := by
  rw [Nat.mul_comm, BitVec.ofNat_mul]

theorem toNat_mul_104 {n : Nat} (hmax : n ≤ maxMessageKeys) :
    (BitVec.ofNat 64 (104 * n)).toNat = 104 * n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold maxMessageKeys at hmax; omega)]

end CryptoVerification.LibsignalTripleRatchet.ChainClone3
