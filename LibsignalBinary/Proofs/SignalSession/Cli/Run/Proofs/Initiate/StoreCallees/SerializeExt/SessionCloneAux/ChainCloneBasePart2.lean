/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ChainCloneBasePart1

/-!
# `Chain::clone [local#1]`: Saved-Register Stack Bundles and Epilogue Helpers
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

theorem messageKeyAt_eq_source (A : RustAlloc) (gk : MessageKeyGhost)
    (mkg : MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A (gk, mkg) a =
      ⌜0 < mkg.seed.length ∧ mkg.seed.length ≤ gk.seed.cap.toNat ∧
        gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
      ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 40#64) ↦₆₄ 0#64) ∗
      ((a + 64#64) ↦₆₄ 0#64) ∗
      ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
      ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      (gk.seed.ptr ↦ₛ mkg.seed) ∗
      ((a + 96#64) ↦₃₂ mkg.counter) ∗
      messageKeySourceFrame A gk mkg a := by
  unfold messageKeyAt messageKeySourceFrame
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro hseed_ne
    have hpos : 0 < mkg.seed.length := List.length_pos_of_ne_nil hseed_ne
    rw [vecU8At_eq_of_nil A a, vecU8At_eq_of_nil A (a + 24#64),
        vecU8At_eq_of_nil A (a + 48#64),
        vecU8At_eq_of_pos A (a + 72#64) gk.seed.cap gk.seed.ptr mkg.seed hpos]
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
    have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
    have ha80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
    have ha88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
    rw [ha32, ha40, ha56, ha64, ha80, ha88]
    have hpure_comm :
        (((a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.cipher.cap gk.cipher.ptr []) ∗
         (((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.mac.cap gk.mac.ptr []) ∗
         (((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.iv.cap gk.iv.ptr []) ∗
         (⌜mkg.seed.length ≤ gk.seed.cap.toNat ∧ gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
          memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length)
            (gk.seed.cap.toNat - mkg.seed.length)) ∗
         ((a + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (a + 100#64) 4) =
        (⌜mkg.seed.length ≤ gk.seed.cap.toNat ∧ gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
          ((a + 16#64) ↦₆₄ 0#64) ∗
          ((a + 40#64) ↦₆₄ 0#64) ∗
          ((a + 64#64) ↦₆₄ 0#64) ∗
          ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗
          ((a + 96#64) ↦₃₂ mkg.counter) ∗
          ((a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗
           vecU8Buf A gk.cipher.cap gk.cipher.ptr [] ∗
           ((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗
           vecU8Buf A gk.mac.cap gk.mac.ptr [] ∗
           ((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗
           vecU8Buf A gk.iv.cap gk.iv.ptr [] ∗
           ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
           memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length)
             (gk.seed.cap.toNat - mkg.seed.length) ∗
           memRegion (a + 100#64) 4)) := by
      ac_rfl
    rw [hpure_comm]
    apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
    exact Entails.pure_right ⟨hpos, hlen, hlt, hptr⟩ (Entails.refl _)
  · apply Entails.pure_left; rintro ⟨hpos, hlen, hlt, hptr⟩
    have hseed_ne : mkg.seed ≠ [] := List.ne_nil_of_length_pos hpos
    apply Entails.pure_right hseed_ne
    rw [vecU8At_eq_of_nil A a, vecU8At_eq_of_nil A (a + 24#64),
        vecU8At_eq_of_nil A (a + 48#64),
        vecU8At_eq_of_pos A (a + 72#64) gk.seed.cap gk.seed.ptr mkg.seed hpos]
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
    have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
    have ha80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
    have ha88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
    rw [ha32, ha40, ha56, ha64, ha80, ha88]
    have hpure_comm :
        (((a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.cipher.cap gk.cipher.ptr []) ∗
         (((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.mac.cap gk.mac.ptr []) ∗
         (((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.iv.cap gk.iv.ptr []) ∗
         (⌜mkg.seed.length ≤ gk.seed.cap.toNat ∧ gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
          memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length)
            (gk.seed.cap.toNat - mkg.seed.length)) ∗
         ((a + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (a + 100#64) 4) =
        (⌜mkg.seed.length ≤ gk.seed.cap.toNat ∧ gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
          ((a + 16#64) ↦₆₄ 0#64) ∗
          ((a + 40#64) ↦₆₄ 0#64) ∗
          ((a + 64#64) ↦₆₄ 0#64) ∗
          ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗
          ((a + 96#64) ↦₃₂ mkg.counter) ∗
          ((a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗
           vecU8Buf A gk.cipher.cap gk.cipher.ptr [] ∗
           ((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗
           vecU8Buf A gk.mac.cap gk.mac.ptr [] ∗
           ((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗
           vecU8Buf A gk.iv.cap gk.iv.ptr [] ∗
           ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
           memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length)
             (gk.seed.cap.toNat - mkg.seed.length) ∗
           memRegion (a + 100#64) 4)) := by
      ac_rfl
    rw [hpure_comm]
    exact Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _)

def clonedMessageKeyGhost (seedLen seedPtr' : BitVec 64) : MessageKeyGhost :=
  { cipher := ⟨0#64, 1#64⟩
    mac    := ⟨0#64, 1#64⟩
    iv     := ⟨0#64, 1#64⟩
    seed   := ⟨seedLen, seedPtr'⟩ }

theorem fold_cloned_messageKeyAt (A : RustAlloc) (mkg : MessageKeyGenerator)
    (seedPtr' dst : BitVec 64)
    (hpos : 0 < mkg.seed.length) (hlt : mkg.seed.length < 2 ^ 63) (hptr' : seedPtr' ≠ 0#64) :
    ((dst ↦₆₄ 0#64) ∗
      ((dst + 8#64) ↦₆₄ 1#64) ∗
      ((dst + 16#64) ↦₆₄ 0#64) ∗
      ((dst + 24#64) ↦₆₄ 0#64) ∗
      ((dst + 32#64) ↦₆₄ 1#64) ∗
      ((dst + 40#64) ↦₆₄ 0#64) ∗
      ((dst + 48#64) ↦₆₄ 0#64) ∗
      ((dst + 56#64) ↦₆₄ 1#64) ∗
      ((dst + 64#64) ↦₆₄ 0#64) ∗
      ((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dst + 80#64) ↦₆₄ seedPtr') ∗
      ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dst + 96#64) ↦₃₂ mkg.counter) ∗
      memRegion (dst + 100#64) 4 ∗
      A.live seedPtr' mkg.seed.length 1 ∗
      (seedPtr' ↦ₛ mkg.seed)) =
      messageKeyAt A (clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length) seedPtr', mkg) dst := by
  unfold messageKeyAt clonedMessageKeyGhost
  have hseed_ne : mkg.seed ≠ [] := List.ne_nil_of_length_pos hpos
  rw [vecU8At_eq_of_nil A dst, vecU8At_eq_of_nil A (dst + 24#64),
      vecU8At_eq_of_nil A (dst + 48#64),
      vecU8At_eq_header_sep_buf A (dst + 72#64),
      vecU8Buf_nil_eq A,
      vecU8Buf_pos_eq A seedPtr' mkg.seed hpos hlt hptr']
  unfold vecHeader
  have hd32 : dst + 24#64 + 8#64 = dst + 32#64 := by bv_omega
  have hd40 : dst + 24#64 + 16#64 = dst + 40#64 := by bv_omega
  have hd56 : dst + 48#64 + 8#64 = dst + 56#64 := by bv_omega
  have hd64 : dst + 48#64 + 16#64 = dst + 64#64 := by bv_omega
  have hd80 : dst + 72#64 + 8#64 = dst + 80#64 := by bv_omega
  have hd88 : dst + 72#64 + 16#64 = dst + 88#64 := by bv_omega
  rw [hd32, hd40, hd56, hd64, hd80, hd88]
  simp only [sepConj_emp]
  apply sepProp_eq_of_entails
  · apply Entails.pure_right hseed_ne
    have hcomm :
        ((dst ↦₆₄ 0#64) ∗ ((dst + 8#64) ↦₆₄ 1#64) ∗ ((dst + 16#64) ↦₆₄ 0#64) ∗
          ((dst + 24#64) ↦₆₄ 0#64) ∗ ((dst + 32#64) ↦₆₄ 1#64) ∗ ((dst + 40#64) ↦₆₄ 0#64) ∗
          ((dst + 48#64) ↦₆₄ 0#64) ∗ ((dst + 56#64) ↦₆₄ 1#64) ∗ ((dst + 64#64) ↦₆₄ 0#64) ∗
          ((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗ ((dst + 80#64) ↦₆₄ seedPtr') ∗
          ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dst + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (dst + 100#64) 4 ∗
          A.live seedPtr' mkg.seed.length 1 ∗ (seedPtr' ↦ₛ mkg.seed)) =
        (((dst ↦₆₄ 0#64) ∗ ((dst + 8#64) ↦₆₄ 1#64) ∗ ((dst + 16#64) ↦₆₄ 0#64)) ∗
         (((dst + 24#64) ↦₆₄ 0#64) ∗ ((dst + 32#64) ↦₆₄ 1#64) ∗ ((dst + 40#64) ↦₆₄ 0#64)) ∗
         (((dst + 48#64) ↦₆₄ 0#64) ∗ ((dst + 56#64) ↦₆₄ 1#64) ∗ ((dst + 64#64) ↦₆₄ 0#64)) ∗
         ((((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗ ((dst + 80#64) ↦₆₄ seedPtr') ∗
           ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length)) ∗
          A.live seedPtr' mkg.seed.length 1 ∗ (seedPtr' ↦ₛ mkg.seed)) ∗
         ((dst + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (dst + 100#64) 4) := by
      ac_rfl
    rw [hcomm]; exact Entails.refl _
  · apply Entails.pure_left; intro _
    have hcomm :
        (((dst ↦₆₄ 0#64) ∗ ((dst + 8#64) ↦₆₄ 1#64) ∗ ((dst + 16#64) ↦₆₄ 0#64)) ∗
         (((dst + 24#64) ↦₆₄ 0#64) ∗ ((dst + 32#64) ↦₆₄ 1#64) ∗ ((dst + 40#64) ↦₆₄ 0#64)) ∗
         (((dst + 48#64) ↦₆₄ 0#64) ∗ ((dst + 56#64) ↦₆₄ 1#64) ∗ ((dst + 64#64) ↦₆₄ 0#64)) ∗
         ((((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗ ((dst + 80#64) ↦₆₄ seedPtr') ∗
           ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length)) ∗
          A.live seedPtr' mkg.seed.length 1 ∗ (seedPtr' ↦ₛ mkg.seed)) ∗
         ((dst + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (dst + 100#64) 4) =
        ((dst ↦₆₄ 0#64) ∗ ((dst + 8#64) ↦₆₄ 1#64) ∗ ((dst + 16#64) ↦₆₄ 0#64) ∗
          ((dst + 24#64) ↦₆₄ 0#64) ∗ ((dst + 32#64) ↦₆₄ 1#64) ∗ ((dst + 40#64) ↦₆₄ 0#64) ∗
          ((dst + 48#64) ↦₆₄ 0#64) ∗ ((dst + 56#64) ↦₆₄ 1#64) ∗ ((dst + 64#64) ↦₆₄ 0#64) ∗
          ((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗ ((dst + 80#64) ↦₆₄ seedPtr') ∗
          ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dst + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (dst + 100#64) 4 ∗
          A.live seedPtr' mkg.seed.length 1 ∗ (seedPtr' ↦ₛ mkg.seed)) := by
      ac_rfl
    rw [hcomm]; exact Entails.refl _

def clonedChainGhost (gc : ChainGhost × ReceiverChain)
    (srkPtr' privPtr' mkCap' mkPtr' : BitVec 64)
    (keys' : List MessageKeyGhost) (ckPin' : VecPin) : ChainGhost :=
  { srk   := ⟨BitVec.ofNat 64 gc.1.srk.bytes.length, srkPtr', gc.1.srk.bytes⟩
    priv  := ⟨BitVec.ofNat 64 gc.1.priv.bytes.length, privPtr', gc.1.priv.bytes⟩
    mkCap := mkCap'
    mkPtr := mkPtr'
    keys  := keys'
    ck    := ckPin' }

theorem fold_chainAt_dst (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (dst srkPtr' privPtr' mkPtr' x25 x28 : BitVec 64) (w27 : BitVec 32)
    (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = gc.2.messageKeys.length) :
    ((dst ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
      ((dst + 8#64) ↦₆₄ srkPtr') ∗
      ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
      ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      ((dst + 32#64) ↦₆₄ privPtr') ∗
      ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      ((dst + 48#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      ((dst + 56#64) ↦₆₄ mkPtr') ∗
      ((dst + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      ((dst + 72#64) ↦₆₄ x25) ∗
      ((dst + 80#64) ↦₆₄ x28) ∗
      ((dst + 88#64) ↦₆₄ x25) ∗
      ((dst + 96#64) ↦₃₂ w27) ∗
      memRegion (dst + 100#64) 4 ∗
      vecU8Buf A (BitVec.ofNat 64 gc.1.srk.bytes.length) srkPtr' gc.1.srk.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 gc.1.priv.bytes.length) privPtr' gc.1.priv.bytes ∗
      vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 gc.2.messageKeys.length) mkPtr'
        (keys'.zip gc.2.messageKeys) ∗
      clonedOptChainKeyBuf A ckPin' x25 x28 w27 gc.2.chainKey) ⊢
      protoChainAt A
        (clonedChainGhost gc srkPtr' privPtr' (BitVec.ofNat 64 gc.2.messageKeys.length)
          mkPtr' keys' ckPin', gc.2) dst := by
  unfold protoChainAt clonedChainGhost vecGhostAt vecAt
  apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
  rw [vecU8At_eq_header_sep_buf A dst, vecU8At_eq_header_sep_buf A (dst + 24#64)]
  unfold vecHeader
  have hzip_len : (keys'.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  rw [hzip_len]
  have hd32 : dst + 24#64 + 8#64 = dst + 32#64 := by bv_omega
  have hd40 : dst + 24#64 + 16#64 = dst + 40#64 := by bv_omega
  have hd56 : dst + 48#64 + 8#64 = dst + 56#64 := by bv_omega
  have hd64 : dst + 48#64 + 16#64 = dst + 64#64 := by bv_omega
  have hd80 : dst + 72#64 + 8#64 = dst + 80#64 := by bv_omega
  have hd88 : dst + 72#64 + 16#64 = dst + 88#64 := by bv_omega
  have hd96 : dst + 72#64 + 24#64 = dst + 96#64 := by bv_omega
  have hd100 : dst + 72#64 + 28#64 = dst + 100#64 := by bv_omega
  rw [hd32, hd40, hd56, hd64]
  have hcomm :
      ((dst ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        ((dst + 8#64) ↦₆₄ srkPtr') ∗
        ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
        ((dst + 32#64) ↦₆₄ privPtr') ∗
        ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
        ((dst + 48#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
        ((dst + 56#64) ↦₆₄ mkPtr') ∗
        ((dst + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
        ((dst + 72#64) ↦₆₄ x25) ∗
        ((dst + 80#64) ↦₆₄ x28) ∗
        ((dst + 88#64) ↦₆₄ x25) ∗
        ((dst + 96#64) ↦₃₂ w27) ∗
        memRegion (dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 gc.1.srk.bytes.length) srkPtr' gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 gc.1.priv.bytes.length) privPtr' gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 gc.2.messageKeys.length) mkPtr'
          (keys'.zip gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 gc.2.chainKey) =
      ((((dst ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
         ((dst + 8#64) ↦₆₄ srkPtr') ∗
         ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length)) ∗
        vecU8Buf A (BitVec.ofNat 64 gc.1.srk.bytes.length) srkPtr' gc.1.srk.bytes) ∗
       ((((dst + 24#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
         ((dst + 32#64) ↦₆₄ privPtr') ∗
         ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length)) ∗
        vecU8Buf A (BitVec.ofNat 64 gc.1.priv.bytes.length) privPtr' gc.1.priv.bytes) ∗
       ((((dst + 48#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
         ((dst + 56#64) ↦₆₄ mkPtr') ∗
         ((dst + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length)) ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 gc.2.messageKeys.length) mkPtr'
          (keys'.zip gc.2.messageKeys)) ∗
       ((((dst + 72#64) ↦₆₄ x25) ∗
         ((dst + 80#64) ↦₆₄ x28) ∗
         ((dst + 88#64) ↦₆₄ x25) ∗
         ((dst + 96#64) ↦₃₂ w27) ∗
         memRegion (dst + 100#64) 4) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 gc.2.chainKey)) := by
    ac_rfl
  rw [hcomm]
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  have hck := fold_optChainKeyAt A ckPin' x25 x28 w27 gc.2.chainKey (dst + 72#64)
  rwa [hd80, hd88, hd96, hd100] at hck

/-! ## Stack Bundles and Epilogue (`+0x2e0..+0x31c`) -/

/-- Callee-saved register save area `[s0.sp - 96#64 .. s0.sp - 8#64]` plus the two stack slots
`[s0.sp - 120#64 .. s0.sp - 108#64]` that are only referenced in dead code paths. -/
def savedRegsOnStack (s0 : State) : SepProp :=
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
  (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
  (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
  (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)

/-- The 8 spill slots `[sp - 208#64 .. sp - 152#64]` when existentially quantified. -/
def spillSlotsExist (sp : BitVec 64) : SepProp :=
  (∃∗ v0 : BitVec 64, (sp - 208#64) ↦₆₄ v0) ∗
  (∃∗ w1a : BitVec 32, (sp - 200#64) ↦₃₂ w1a) ∗
  (∃∗ w1b : BitVec 32, (sp - 196#64) ↦₃₂ w1b) ∗
  (∃∗ v2 : BitVec 64, (sp - 192#64) ↦₆₄ v2) ∗
  (∃∗ v3 : BitVec 64, (sp - 184#64) ↦₆₄ v3) ∗
  (∃∗ v4 : BitVec 64, (sp - 176#64) ↦₆₄ v4) ∗
  (∃∗ v5 : BitVec 64, (sp - 168#64) ↦₆₄ v5) ∗
  (∃∗ v6 : BitVec 64, (sp - 160#64) ↦₆₄ v6) ∗
  (∃∗ v7 : BitVec 64, (sp - 152#64) ↦₆₄ v7)

theorem fold_stackAt_chainClone (s0 : State) (v8 v9 v10 v13 : BitVec 64) :
    (stackAt (s0.sp - 208#64) extHookStack ∗
      spillSlotsExist s0.sp ∗
      ((s0.sp - 144#64) ↦₆₄ v8) ∗
      ((s0.sp - 136#64) ↦₆₄ v9) ∗
      ((s0.sp - 128#64) ↦₆₄ v10) ∗
      ((s0.sp - 104#64) ↦₆₄ v13) ∗
      savedRegsOnStack s0) ⊢
      stackAt s0.sp chainCloneStackX := by
  rw [stackAt_chainClone_eq s0.sp]
  unfold spillSlotsExist savedRegsOnStack
  have h8 : ((s0.sp - 144#64) ↦₆₄ v8) ⊢ ∃∗ x : BitVec 64, (s0.sp - 144#64) ↦₆₄ x :=
    Entails.sepExists_right v8 (Entails.refl _)
  have h9 : ((s0.sp - 136#64) ↦₆₄ v9) ⊢ ∃∗ x : BitVec 64, (s0.sp - 136#64) ↦₆₄ x :=
    Entails.sepExists_right v9 (Entails.refl _)
  have h10 : ((s0.sp - 128#64) ↦₆₄ v10) ⊢ ∃∗ x : BitVec 64, (s0.sp - 128#64) ↦₆₄ x :=
    Entails.sepExists_right v10 (Entails.refl _)
  have h13 : ((s0.sp - 104#64) ↦₆₄ v13) ⊢ ∃∗ x : BitVec 64, (s0.sp - 104#64) ↦₆₄ x :=
    Entails.sepExists_right v13 (Entails.refl _)
  have h14 : ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 96#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 29#5)) (Entails.refl _)
  have h15 : ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 88#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 30#5)) (Entails.refl _)
  have h16 : ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 80#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 28#5)) (Entails.refl _)
  have h17 : ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 72#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 27#5)) (Entails.refl _)
  have h18 : ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 64#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 26#5)) (Entails.refl _)
  have h19 : ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 56#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 25#5)) (Entails.refl _)
  have h20 : ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 48#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 24#5)) (Entails.refl _)
  have h21 : ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 40#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 23#5)) (Entails.refl _)
  have h22 : ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 32#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 22#5)) (Entails.refl _)
  have h23 : ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 24#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 21#5)) (Entails.refl _)
  have h24 : ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 16#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 20#5)) (Entails.refl _)
  have h25 : ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 8#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 19#5)) (Entails.refl _)
  have hstep :
      (stackAt (s0.sp - 208#64) extHookStack ∗
        ((∃∗ v0 : BitVec 64, (s0.sp - 208#64) ↦₆₄ v0) ∗
         (∃∗ w1a : BitVec 32, (s0.sp - 200#64) ↦₃₂ w1a) ∗
         (∃∗ w1b : BitVec 32, (s0.sp - 196#64) ↦₃₂ w1b) ∗
         (∃∗ v2 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v2) ∗
         (∃∗ v3 : BitVec 64, (s0.sp - 184#64) ↦₆₄ v3) ∗
         (∃∗ v4 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v4) ∗
         (∃∗ v5 : BitVec 64, (s0.sp - 168#64) ↦₆₄ v5) ∗
         (∃∗ v6 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v6) ∗
         (∃∗ v7 : BitVec 64, (s0.sp - 152#64) ↦₆₄ v7)) ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
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
         (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
         (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
         (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) ⊢
      (stackAt (s0.sp - 208#64) extHookStack ∗
        ((∃∗ v0 : BitVec 64, (s0.sp - 208#64) ↦₆₄ v0) ∗
         (∃∗ w1a : BitVec 32, (s0.sp - 200#64) ↦₃₂ w1a) ∗
         (∃∗ w1b : BitVec 32, (s0.sp - 196#64) ↦₃₂ w1b) ∗
         (∃∗ v2 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v2) ∗
         (∃∗ v3 : BitVec 64, (s0.sp - 184#64) ↦₆₄ v3) ∗
         (∃∗ v4 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v4) ∗
         (∃∗ v5 : BitVec 64, (s0.sp - 168#64) ↦₆₄ v5) ∗
         (∃∗ v6 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v6) ∗
         (∃∗ v7 : BitVec 64, (s0.sp - 152#64) ↦₆₄ v7)) ∗
        (∃∗ v8 : BitVec 64, (s0.sp - 144#64) ↦₆₄ v8) ∗
        (∃∗ v9 : BitVec 64, (s0.sp - 136#64) ↦₆₄ v9) ∗
        (∃∗ v10 : BitVec 64, (s0.sp - 128#64) ↦₆₄ v10) ∗
        (∃∗ v13 : BitVec 64, (s0.sp - 104#64) ↦₆₄ v13) ∗
        ((∃∗ v14 : BitVec 64, (s0.sp - 96#64) ↦₆₄ v14) ∗
         (∃∗ v15 : BitVec 64, (s0.sp - 88#64) ↦₆₄ v15) ∗
         (∃∗ v16 : BitVec 64, (s0.sp - 80#64) ↦₆₄ v16) ∗
         (∃∗ v17 : BitVec 64, (s0.sp - 72#64) ↦₆₄ v17) ∗
         (∃∗ v18 : BitVec 64, (s0.sp - 64#64) ↦₆₄ v18) ∗
         (∃∗ v19 : BitVec 64, (s0.sp - 56#64) ↦₆₄ v19) ∗
         (∃∗ v20 : BitVec 64, (s0.sp - 48#64) ↦₆₄ v20) ∗
         (∃∗ v21 : BitVec 64, (s0.sp - 40#64) ↦₆₄ v21) ∗
         (∃∗ v22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ v22) ∗
         (∃∗ v23 : BitVec 64, (s0.sp - 24#64) ↦₆₄ v23) ∗
         (∃∗ v24 : BitVec 64, (s0.sp - 16#64) ↦₆₄ v24) ∗
         (∃∗ v25 : BitVec 64, (s0.sp - 8#64) ↦₆₄ v25) ∗
         (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
         (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
         (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) :=
    sepConj_mono_right (sepConj_mono_right
      (sepConj_mono h8 (sepConj_mono h9 (sepConj_mono h10 (sepConj_mono h13
        (sepConj_mono h14 (sepConj_mono h15 (sepConj_mono h16 (sepConj_mono h17
          (sepConj_mono h18 (sepConj_mono h19 (sepConj_mono h20 (sepConj_mono h21
            (sepConj_mono h22 (sepConj_mono h23 (sepConj_mono h24
              (sepConj_mono_left h25)))))))))))))))))
  refine Entails.trans hstep ?_
  have hcomm :
      (stackAt (s0.sp - 208#64) extHookStack ∗
        ((∃∗ v0 : BitVec 64, (s0.sp - 208#64) ↦₆₄ v0) ∗
         (∃∗ w1a : BitVec 32, (s0.sp - 200#64) ↦₃₂ w1a) ∗
         (∃∗ w1b : BitVec 32, (s0.sp - 196#64) ↦₃₂ w1b) ∗
         (∃∗ v2 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v2) ∗
         (∃∗ v3 : BitVec 64, (s0.sp - 184#64) ↦₆₄ v3) ∗
         (∃∗ v4 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v4) ∗
         (∃∗ v5 : BitVec 64, (s0.sp - 168#64) ↦₆₄ v5) ∗
         (∃∗ v6 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v6) ∗
         (∃∗ v7 : BitVec 64, (s0.sp - 152#64) ↦₆₄ v7)) ∗
        (∃∗ v8 : BitVec 64, (s0.sp - 144#64) ↦₆₄ v8) ∗
        (∃∗ v9 : BitVec 64, (s0.sp - 136#64) ↦₆₄ v9) ∗
        (∃∗ v10 : BitVec 64, (s0.sp - 128#64) ↦₆₄ v10) ∗
        (∃∗ v13 : BitVec 64, (s0.sp - 104#64) ↦₆₄ v13) ∗
        ((∃∗ v14 : BitVec 64, (s0.sp - 96#64) ↦₆₄ v14) ∗
         (∃∗ v15 : BitVec 64, (s0.sp - 88#64) ↦₆₄ v15) ∗
         (∃∗ v16 : BitVec 64, (s0.sp - 80#64) ↦₆₄ v16) ∗
         (∃∗ v17 : BitVec 64, (s0.sp - 72#64) ↦₆₄ v17) ∗
         (∃∗ v18 : BitVec 64, (s0.sp - 64#64) ↦₆₄ v18) ∗
         (∃∗ v19 : BitVec 64, (s0.sp - 56#64) ↦₆₄ v19) ∗
         (∃∗ v20 : BitVec 64, (s0.sp - 48#64) ↦₆₄ v20) ∗
         (∃∗ v21 : BitVec 64, (s0.sp - 40#64) ↦₆₄ v21) ∗
         (∃∗ v22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ v22) ∗
         (∃∗ v23 : BitVec 64, (s0.sp - 24#64) ↦₆₄ v23) ∗
         (∃∗ v24 : BitVec 64, (s0.sp - 16#64) ↦₆₄ v24) ∗
         (∃∗ v25 : BitVec 64, (s0.sp - 8#64) ↦₆₄ v25) ∗
         (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
         (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
         (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) =
      (stackAt (s0.sp - 208#64) extHookStack ∗
        (∃∗ v0 : BitVec 64, (s0.sp - 208#64) ↦₆₄ v0) ∗
        (∃∗ w1a : BitVec 32, (s0.sp - 200#64) ↦₃₂ w1a) ∗
        (∃∗ w1b : BitVec 32, (s0.sp - 196#64) ↦₃₂ w1b) ∗
        (∃∗ v2 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v2) ∗
        (∃∗ v3 : BitVec 64, (s0.sp - 184#64) ↦₆₄ v3) ∗
        (∃∗ v4 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v4) ∗
        (∃∗ v5 : BitVec 64, (s0.sp - 168#64) ↦₆₄ v5) ∗
        (∃∗ v6 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v6) ∗
        (∃∗ v7 : BitVec 64, (s0.sp - 152#64) ↦₆₄ v7) ∗
        (∃∗ v8 : BitVec 64, (s0.sp - 144#64) ↦₆₄ v8) ∗
        (∃∗ v9 : BitVec 64, (s0.sp - 136#64) ↦₆₄ v9) ∗
        (∃∗ v10 : BitVec 64, (s0.sp - 128#64) ↦₆₄ v10) ∗
        (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
        (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
        (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b) ∗
        (∃∗ v13 : BitVec 64, (s0.sp - 104#64) ↦₆₄ v13) ∗
        (∃∗ v14 : BitVec 64, (s0.sp - 96#64) ↦₆₄ v14) ∗
        (∃∗ v15 : BitVec 64, (s0.sp - 88#64) ↦₆₄ v15) ∗
        (∃∗ v16 : BitVec 64, (s0.sp - 80#64) ↦₆₄ v16) ∗
        (∃∗ v17 : BitVec 64, (s0.sp - 72#64) ↦₆₄ v17) ∗
        (∃∗ v18 : BitVec 64, (s0.sp - 64#64) ↦₆₄ v18) ∗
        (∃∗ v19 : BitVec 64, (s0.sp - 56#64) ↦₆₄ v19) ∗
        (∃∗ v20 : BitVec 64, (s0.sp - 48#64) ↦₆₄ v20) ∗
        (∃∗ v21 : BitVec 64, (s0.sp - 40#64) ↦₆₄ v21) ∗
        (∃∗ v22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ v22) ∗
        (∃∗ v23 : BitVec 64, (s0.sp - 24#64) ↦₆₄ v23) ∗
        (∃∗ v24 : BitVec 64, (s0.sp - 16#64) ↦₆₄ v24) ∗
        (∃∗ v25 : BitVec 64, (s0.sp - 8#64) ↦₆₄ v25)) := by
    ac_rfl
  rw [hcomm]
  exact Entails.refl _

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1
