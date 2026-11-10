/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneBase
import ProofLib.SepLogic.WPp

/-!
# `chain_key` and `priv` Clone Branches for `Chain::clone [local#3]` (`0x766c8`)

Proves the `chain_key = None` and `chain_key = Some ck` cloning branches for
`<session_structure::Chain as Clone>::clone [local#3]`.
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

/-! ## 7. `chain_key`, `priv`, and Full `Chain::clone` Proof (`0x766c8`) -/

def chainMkLenFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
  vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_mk_len (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      chainMkLenFrame A gc a := by
  unfold protoChainAt chainMkLenFrame vecAt vecHeader
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  rw [hzip_len, ha56, ha64]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    exact Entails.of_eq (by ac_rfl)

def chainCkSomeFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
  vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
  ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
  A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
  memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
  memRegion (a + 100#64) 4

theorem chainAt_eq_ck_some (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hck : gc.2.chainKey = some ck) :
    protoChainAt A gc a =
      ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
      ((a + 88#64) ↦₆₄ 32#64) ∗
      ((a + 96#64) ↦₃₂ ck.index) ∗
      (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
      chainCkSomeFrame A gc a := by
  unfold protoChainAt chainCkSomeFrame vecAt vecHeader
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  have hck_len : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have hck_pos : 0 < (keyToBytes32 ck.key).length := by rw [hck_len]; decide
  have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  have ha80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
  have ha88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
  have ha96 : a + 72#64 + 24#64 = a + 96#64 := by bv_omega
  have ha100 : a + 72#64 + 28#64 = a + 100#64 := by bv_omega
  rw [hzip_len, hck]
  simp only [optChainKeyAt]
  rw [vecU8At_eq_of_pos A (a + 72#64) gc.1.ck.cap gc.1.ck.ptr (keyToBytes32 ck.key) hck_pos,
      hck_len, ha56, ha64, ha80, ha88, ha96, ha100]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          memRegion (a + 100#64) 4) =
        (⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    exact Entails.refl _
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          memRegion (a + 100#64) 4) =
        (⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

def chainCkNoneCapFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  memRegion (a + 72#64 + 8#64) 24

theorem chainAt_eq_ck_none_cap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hck : gc.2.chainKey = none) :
    protoChainAt A gc a =
      ((a + 72#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      chainCkNoneCapFrame A gc a := by
  unfold protoChainAt chainCkNoneCapFrame
  rw [hck]
  dsimp only [optChainKeyAt, optChainKeyNone]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    exact Entails.of_eq (by ac_rfl)

def chainCkSomeCapFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64) : SepProp :=
  ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.ptr ≠ 0⌝ ∗
  ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
  ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
  ((a + 88#64) ↦₆₄ 32#64) ∗
  ((a + 96#64) ↦₃₂ ck.index) ∗
  (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
  vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
  A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
  memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
  memRegion (a + 100#64) 4

theorem chainAt_eq_ck_some_cap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hck : gc.2.chainKey = some ck) :
    protoChainAt A gc a =
      ⌜gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
      ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
      chainCkSomeCapFrame A gc ck a := by
  rw [chainAt_eq_ck_some A gc ck a hsrk hmax hklen hck]
  unfold chainCkSomeFrame chainCkSomeCapFrame
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right hlt
    rw [show (((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) =
        (((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    exact sepConj_mono_right (Entails.pure_right ⟨hle, hptr⟩ (Entails.refl _))
  · apply Entails.pure_left; intro hlt
    rw [show (((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) =
        (⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    apply Entails.pure_left; rintro ⟨hle, hptr⟩
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

def chainPrivLenFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
  ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
  vecU8Buf A gc.1.priv.cap gc.1.priv.ptr gc.1.priv.bytes ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_priv_len (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      chainPrivLenFrame A gc a := by
  unfold protoChainAt chainPrivLenFrame
  dsimp only [vecGhostAt, vecU8At, vecU8Buf, vecAt, vecHeader]
  have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  rw [ha32, ha40]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    exact Entails.of_eq (by ac_rfl)

def chainPrivPosFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
  A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
  memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
    (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_priv_pos (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hpos : 0 < gc.1.priv.bytes.length) :
    protoChainAt A gc a =
      ⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
        gc.1.priv.cap.toNat < 2 ^ 63 ∧
        gc.1.priv.ptr ≠ 0⌝ ∗
      ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
      chainPrivPosFrame A gc a := by
  unfold protoChainAt chainPrivPosFrame
  dsimp only [vecGhostAt]
  have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  rw [vecU8At_eq_of_pos A (a + 24#64) gc.1.priv.cap gc.1.priv.ptr gc.1.priv.bytes hpos,
      ha32, ha40]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [sepConj_assoc]
    rw [show (vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    exact Entails.refl _
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [sepConj_assoc]
    rw [show (vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

end CryptoVerification.LibsignalTripleRatchet.ChainClone3
