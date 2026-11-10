/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled1
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>`: Inlined `.keysUnsampled` Sub-Step (`+684..+2588`)

**Checked by Lean.**

Verifies `step_keysUnsampled_684_to_2588`: calls `Authenticator::mac_hdr`, sets up
`ekSentInlineWordsAt`, reserves 32 bytes via `do_reserve_and_handle [local#2]`, and
appends the 32-byte MAC to `hdr`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local arm64_norm ↓, local wp_norm ↓]
  DoReserveNorm.sp_setPC_pre DoReserveNorm.sp_setMem_setPC_pre
  DoReserveNorm.readReg64_setPC_pre DoReserveNorm.readReg64_setMem_setPC_pre
  DoReserveNorm.readReg32_setPC_pre DoReserveNorm.readReg32_setMem_setPC_pre
  DoReserveNorm.readReg_setPC_pre DoReserveNorm.readReg_setMem_setPC_pre

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::send::<libsignal_session::HookRng>")
  (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::mac_hdr")
  (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes")
  (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "core::panicking::panic")

theorem vecU8_len32_expose {A : RustAlloc} (a : BitVec 64) (mac : Bytes) (hlen : mac.length = 32) :
    vecU8 A a mac ⊢
    ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 ∧ (cap == 0#64) = false⌝ ∗
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ mac) ∗
      memRegion (ptr + 32#64) (cap.toNat - 32) := by
  unfold vecU8 vecU8At vecHeader
  apply ProofLib.Entails.sepExists_elim; intro cap
  apply ProofLib.Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  by_cases hc : cap = 0#64
  · subst hc
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte, sepConj_emp, hlen,
      show BitVec.ofNat 64 32 = 32#64 from rfl, sepConj_assoc]
    have hcomm0 :
        ((a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
         ⌜32 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝) =
        (⌜32 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
         (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64)) := by ac_rfl
    rw [hcomm0]
    exact Entails.pure_left fun h => nomatch h.1
  · have hc0 : ¬ (cap = 0) := hc
    have hcb : (cap == 0#64) = false := beq_false_of_ne hc
    simp only [hc0, ↓reduceIte, hlen, show BitVec.ofNat 64 32 = 32#64 from rfl, sepConj_assoc]
    have hcomm :
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
         ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
         A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ mac) ∗ memRegion (ptr + 32#64) (cap.toNat - 32)) =
        (⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
         (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
         A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ mac) ∗ memRegion (ptr + 32#64) (cap.toNat - 32)) := by ac_rfl
    rw [hcomm]
    refine Entails.pure_left fun ⟨hle, hlt, hp⟩ => ?_
    exact Entails.pure_right ⟨hle, hlt, hp, hcb⟩ (Entails.refl _)

/-- Four consecutive 64-bit words (`32` bytes) at `a`. -/
def words4At (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)

theorem memRegion_32_eq_words4 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64)]

theorem words4At_entails_memRegion (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    words4At a w0 w1 w2 w3 ⊢ memRegion a 32 := by
  unfold words4At
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8) (b' := a + 24#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (ProofLib.pointsTo64_entails_memRegion _ _)))

theorem memRegion_24_eq_words3 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64)]

theorem words3_entails_memRegion (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (ProofLib.pointsTo64_entails_memRegion _ _))

/-- Inline 13-word (104-byte) layout of `unchunkedEkSentCt1ReceivedAt` at `a`:
    - `+0..+48`: `auth` (`48`B)
    - `+48..+72`: `ek` Vec header (`cap, ptr, len`)
    - `+72..+96`: `dk` Vec header (`cap, ptr, len`)
    - `+96..+104`: `epoch` (`8`B) -/
def ekSentInlineWordsAt (a : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (ekCap ekPtr ekLen dkCap dkPtr dkLen epoch : BitVec 64) : SepProp :=
  authInlineWordsAt g a auth ∗
  ((a + 48#64) ↦₆₄ ekCap) ∗ ((a + 56#64) ↦₆₄ ekPtr) ∗ ((a + 64#64) ↦₆₄ ekLen) ∗
  ((a + 72#64) ↦₆₄ dkCap) ∗ ((a + 80#64) ↦₆₄ dkPtr) ∗ ((a + 88#64) ↦₆₄ dkLen) ∗
  ((a + 96#64) ↦₆₄ epoch)

theorem memRegion_104_eq_words13 (a : BitVec 64) :
    memRegion a 104 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (a + 32#64) ↦₆₄ d4) ∗
      (∃∗ d5 : BitVec 64, (a + 40#64) ↦₆₄ d5) ∗
      (∃∗ d6 : BitVec 64, (a + 48#64) ↦₆₄ d6) ∗
      (∃∗ d7 : BitVec 64, (a + 56#64) ↦₆₄ d7) ∗
      (∃∗ d8 : BitVec 64, (a + 64#64) ↦₆₄ d8) ∗
      (∃∗ d9 : BitVec 64, (a + 72#64) ↦₆₄ d9) ∗
      (∃∗ d10 : BitVec 64, (a + 80#64) ↦₆₄ d10) ∗
      (∃∗ d11 : BitVec 64, (a + 88#64) ↦₆₄ d11) ∗
      (∃∗ d12 : BitVec 64, (a + 96#64) ↦₆₄ d12) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 56) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 48) (k := 8) (b' := a + 96#64) rfl (by bv_omega) (by decide),
      memRegion_48_eq_words6 a,
      memRegion_48_eq_words6 (a + 48#64),
      ProofLib.memRegion_eight (a + 96#64),
      show (a + 48#64) + 8#64 = a + 56#64 by bv_omega,
      show (a + 48#64) + 16#64 = a + 64#64 by bv_omega,
      show (a + 48#64) + 24#64 = a + 72#64 by bv_omega,
      show (a + 48#64) + 32#64 = a + 80#64 by bv_omega,
      show (a + 48#64) + 40#64 = a + 88#64 by bv_omega]
  ac_rfl

theorem ekSentInlineWordsAt_entails_memRegion (a : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (ekCap ekPtr ekLen dkCap dkPtr dkLen epoch : BitVec 64) :
    ekSentInlineWordsAt a g auth ekCap ekPtr ekLen dkCap dkPtr dkLen epoch ⊢
    memRegion a 104 := by
  unfold ekSentInlineWordsAt
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 56) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 48) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 40) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 64#64) (n := 8) (k := 32) (b' := a + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 72#64) (n := 8) (k := 24) (b' := a + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 80#64) (n := 8) (k := 16) (b' := a + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 88#64) (n := 8) (k := 8) (b' := a + 96#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (authInlineWordsAt_entails_memRegion g a auth)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
              (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                (ProofLib.pointsTo64_entails_memRegion _ _)))))))

/-- Sixteen consecutive 64-bit words (`128` bytes) at `a`. -/
def words16At (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) : SepProp :=
  words8At a w0 w1 w2 w3 w4 w5 w6 w7 ∗
  words8At (a + 64#64) w8 w9 w10 w11 w12 w13 w14 w15

theorem memRegion_128_eq_words16 (a : BitVec 64) :
    memRegion a 128 =
      ((∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
       (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
       (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
       (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗
       (∃∗ d4 : BitVec 64, (a + 32#64) ↦₆₄ d4) ∗
       (∃∗ d5 : BitVec 64, (a + 40#64) ↦₆₄ d5) ∗
       (∃∗ d6 : BitVec 64, (a + 48#64) ↦₆₄ d6) ∗
       (∃∗ d7 : BitVec 64, (a + 56#64) ↦₆₄ d7)) ∗
      ((∃∗ d8 : BitVec 64, (a + 64#64) ↦₆₄ d8) ∗
       (∃∗ d9 : BitVec 64, ((a + 64#64) + 8#64) ↦₆₄ d9) ∗
       (∃∗ d10 : BitVec 64, ((a + 64#64) + 16#64) ↦₆₄ d10) ∗
       (∃∗ d11 : BitVec 64, ((a + 64#64) + 24#64) ↦₆₄ d11) ∗
       (∃∗ d12 : BitVec 64, ((a + 64#64) + 32#64) ↦₆₄ d12) ∗
       (∃∗ d13 : BitVec 64, ((a + 64#64) + 40#64) ↦₆₄ d13) ∗
       (∃∗ d14 : BitVec 64, ((a + 64#64) + 48#64) ↦₆₄ d14) ∗
       (∃∗ d15 : BitVec 64, ((a + 64#64) + 56#64) ↦₆₄ d15)) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 64) (k := 64) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      memRegion_64_eq_words8 a,
      memRegion_64_eq_words8 (a + 64#64)]

theorem words16At_entails_memRegion (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    words16At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ⊢
    memRegion a 128 := by
  unfold words16At
  rw [ProofLib.memRegion_split' (b := a) (n := 64) (k := 64) (b' := a + 64#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono
    (words8At_entails_memRegion a w0 w1 w2 w3 w4 w5 w6 w7)
    (words8At_entails_memRegion (a + 64#64) w8 w9 w10 w11 w12 w13 w14 w15)

@[simp]
theorem reserveCap_64_64_32 : reserveCap 64 64 32 = 128 := by decide

@[simp]
theorem bytesAt_false_eq (a : BitVec 64) (bs : Bytes) :
    bytesAt false a bs = (a ↦ₛ bs) := rfl

/-! ## Tail Layout Lemmas -/

theorem chunkedStatesTail920At_keysSampled_eq {F : ShaCompress} (A : RustAlloc) (a : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesTail920At A a (.keysSampled st) =
      chunkedKeysSampledAt A a st ∗ memRegion (a + 504#64) 416 :=
  rfl

theorem authInlineWordsAt_352_entails_memRegion_400
    (g : AuthenticatorGhost) (a : BitVec 64) (auth : Authenticator) :
    authInlineWordsAt g a auth ∗ memRegion (a + 48#64) 352 ⊢ memRegion a 400 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 352) (b' := a + 48#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (authInlineWordsAt_entails_memRegion g a auth)

theorem hdr_mac_len_96 (K : MlKem) (seed : List.Vector (BitVec 8) 64) {mac : Bytes}
    (hmac_len : mac.length = 32) :
    ((K.fromSeed seed).1.toList ++ mac).length = 96 := by
  rw [List.length_append, List.Vector.toList_length, hmac_len]

theorem encodeBytesResult_hdr_mac (K : MlKem) (seed : List.Vector (BitVec 8) 64) {mac : Bytes}
    (hmac_len : mac.length = 32) :
    ∃ enc : PolyEncoder,
      encodeBytesResult ((K.fromSeed seed).1.toList ++ mac) = .ok enc ∧
      expectEncodeBytes spqrPolyApi "v1/chunked/send_ek.rs:63"
        ((K.fromSeed seed).1.toList ++ mac) = .ok enc := by
  have h96 := hdr_mac_len_96 K seed hmac_len
  obtain ⟨enc, h1, h2, _⟩ := encodeBytesResult_of_len_even_le
    (msg := (K.fromSeed seed).1.toList ++ mac) (by omega) (by omega)
  exact ⟨enc, h1, h2⟩

/-! ## Sub-Step 1c (`+684 -> +2588`) -/

@[simp]
theorem macHdrUnchecked_length (F : ShaCompress) (auth : Authenticator) (ep : Epoch) (hdr : Bytes) :
    (auth.macHdrUnchecked F ep hdr).length = 32 := by
  rw [MacHdrFacts.macHdrUnchecked_eq_hmacWith, LibsignalSpqrV1.length_hmacWith]

theorem hdr_data_len_105 (K : MlKem) (seed : List.Vector (BitVec 8) 64) (ep : Epoch) :
    (Authenticator.hdrLabel ++ CryptoGames.HMAC.toBEBytes 8 ep ++ (K.fromSeed seed).1.toList).length = 105 := by
  simp only [List.length_append, MacHdrFacts.hdrLabel_length,
    toBEBytes_8_length, List.Vector.toList_length]

theorem memRegion_504_expose_chunk_slot (sp : BitVec 64) :
    memRegion (sp + 4192#64) 504 =
      (∃∗ d0 : BitVec 64, (sp + 4192#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp + 4200#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 4208#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (sp + 4216#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 16, (sp + 4224#64) ↦₁₆ d4) ∗
      memRegion (sp + 4226#64) 470 := by
  rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 8) (k := 496) (b' := sp + 4200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4200#64) (n := 8) (k := 488) (b' := sp + 4208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4208#64) (n := 8) (k := 480) (b' := sp + 4216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4216#64) (n := 8) (k := 472) (b' := sp + 4224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4224#64) (n := 2) (k := 470) (b' := sp + 4226#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 4192#64),
      ProofLib.memRegion_eight (sp + 4200#64),
      ProofLib.memRegion_eight (sp + 4208#64),
      ProofLib.memRegion_eight (sp + 4216#64),
      ProofLib.memRegion_two (sp + 4224#64)]

theorem chunkAt_and_470_entails_memRegion_504 (sp : BitVec 64) (c : Chunk) :
    chunkAt (sp + 4192#64) c ∗ memRegion (sp + 4226#64) 470 ⊢ memRegion (sp + 4192#64) 504 := by
  rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 34) (k := 470) (b' := sp + 4226#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (chunkAt_entails_memRegion (sp + 4192#64) c)

theorem memRegion_4704_2400_split_macHdr (sp : BitVec 64) :
    memRegion (sp + 4704#64) 2400 =
      memRegion (sp + 4704#64) 128 ∗
      memRegion (sp + 4832#64) 24 ∗
      memRegion (sp + 4856#64) 2248 := by
  rw [ProofLib.memRegion_split' (b := sp + 4704#64) (n := 128) (k := 2272) (b' := sp + 4832#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4832#64) (n := 24) (k := 2248) (b' := sp + 4856#64) rfl (by bv_omega) (by decide)]

theorem macHdr_ok_elim {F : ShaCompress} {auth : Authenticator} {ep : Epoch} {hdr mac : Bytes}
    (h : auth.macHdr F ep hdr = .ok mac) :
    mac = auth.macHdrUnchecked F ep hdr ∧
    auth.macKey.length < 2 ^ 32 ∧
    (Authenticator.hdrLabel ++ CryptoGames.HMAC.toBEBytes 8 ep ++ hdr).length < 2 ^ 32 := by
  unfold Authenticator.macHdr at h
  dsimp only at h
  split_ifs at h with hlt
  exact ⟨(Except.ok.inj h).symm, hlt.1, hlt.2⟩

theorem authMacHdrPinned_onPanic_of_ok {F : ShaCompress} {A : RustAlloc}
    (x : AuthMacHdrPinnedGhost) {mac : Bytes}
    (h : x.auth.macHdr F x.ep x.hdr = .ok mac) (s0 sf : State) :
    (authMacHdrPinnedSpec F A).onPanic x s0 sf =
      (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) := by
  obtain ⟨_, hk, hd⟩ := macHdr_ok_elim h
  dsimp only [authMacHdrPinnedSpec]
  have h1 : ¬ (2 ^ 32 ≤ x.auth.macKey.length) := by omega
  have h2 : ¬ (2 ^ 32 ≤ (Authenticator.hdrLabel ++ CryptoGames.HMAC.toBEBytes 8 x.ep ++ x.hdr).length) := by omega
  simp only [h1, h2, or_false]

theorem send_hdr_chunk_ok_elim {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F))
    {tape tape' : Bytes}
    {outSt : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)}
    {chunk : Chunk}
    (hsend : st.send_hdr_chunk K spqrPolyApi tape = .ok (outSt, chunk, tape')) :
    ∃ (h64 : 64 ≤ tape.length) (sending_hdr : PolyEncoder),
      let seed : List.Vector (BitVec 8) 64 := ⟨tape.take 64, by rw [List.length_take]; omega⟩
      let mac := st.uc.auth.macHdrUnchecked F st.uc.epoch (K.fromSeed seed).1.toList
      st.uc.auth.macHdr F st.uc.epoch (K.fromSeed seed).1.toList = .ok mac ∧
      encodeBytesResult ((K.fromSeed seed).1.toList ++ mac) = .ok sending_hdr ∧
      sending_hdr.nextChunk = .ok (outSt.sending_hdr, chunk) ∧
      outSt.uc = { epoch := st.uc.epoch, auth := st.uc.auth,
                   ek := (K.fromSeed seed).2.1.toList, dk := (K.fromSeed seed).2.2.toList } ∧
      tape' = tape.drop 64 := by
  have h64 : 64 ≤ tape.length := by
    by_contra hlt
    rw [send_hdr_chunk_of_lt_64 K st (by omega)] at hsend
    cases hsend
  refine ⟨h64, ?_⟩
  let seed : List.Vector (BitVec 8) 64 := ⟨tape.take 64, by rw [List.length_take]; omega⟩
  cases hmac : st.uc.auth.macHdr F st.uc.epoch (K.fromSeed seed).1.toList with
  | error p =>
    rw [send_hdr_chunk_of_macHdr_err K st h64 hmac] at hsend
    cases hsend
  | ok mac =>
    obtain ⟨rfl, _, _⟩ := macHdr_ok_elim hmac
    obtain ⟨sending_hdr, henc_res, henc_exp⟩ :=
      encodeBytesResult_hdr_mac K seed (macHdrUnchecked_length F st.uc.auth st.uc.epoch _)
    refine ⟨sending_hdr, hmac, henc_res, ?_⟩
    cases hnc : sending_hdr.nextChunk with
    | error p =>
      rw [send_hdr_chunk_of_nextChunk_err K st h64 hmac henc_exp hnc] at hsend
      cases hsend
    | ok pair =>
      rcases pair with ⟨sending_hdr', chunk'⟩
      have hok := send_hdr_chunk_of_ok K st h64 hmac henc_exp hnc
      dsimp only at hok
      rw [hok] at hsend
      injection hsend with htuple
      injection htuple with hout hrest
      injection hrest with hch htp
      have hsnd : sending_hdr' = outSt.sending_hdr :=
        congrArg Chunked.SendEk.KeysSampled.sending_hdr hout
      have huc : { epoch := st.uc.epoch, auth := st.uc.auth,
                   ek := (K.fromSeed seed).2.1.toList, dk := (K.fromSeed seed).2.2.toList } = outSt.uc :=
        congrArg Chunked.SendEk.KeysSampled.uc hout
      rw [← hsnd, ← huc, ← hch, ← htp]
      exact ⟨rfl, rfl, rfl⟩

theorem fnAddr_adrp_31380 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr spqrSendName + 2852#64) &&&
      0xfffffffffffff000#64) = b + page% ((ls_off% "spqr::send::<libsignal_session::HookRng>") + 2852) := by
  rw [Program.fnAddr_rebase, spqrSend_fnOff]
  revert hb; bv_bits

theorem fold_vecU8_of_inline {A : RustAlloc} (a cap ptr len : BitVec 64) (bs : Bytes)
    (hlen : BitVec.ofNat 64 bs.length = len) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len) ∗
    RustHeap.vecU8Buf A cap ptr bs ⊢
    vecU8 A a bs := by
  unfold vecU8 vecU8At vecHeader RustHeap.vecU8Buf
  rw [hlen]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

theorem fold_authenticatorAt_of_inline {A : RustAlloc} (g : AuthenticatorGhost)
    (a : BitVec 64) (auth : Authenticator) :
    authInlineWordsAt g a auth ∗ authHeapBufs A g auth ⊢
    authenticatorAt A a auth := by
  rw [← authenticatorPinAt_eq_inline_heap A g a auth]
  unfold authenticatorAt authenticatorPinAt vecU8
  exact sepConj_mono
    (Entails.sepExists_right g.rootKey.cap (Entails.sepExists_right g.rootKey.ptr (Entails.refl _)))
    (Entails.sepExists_right g.macKey.cap (Entails.sepExists_right g.macKey.ptr (Entails.refl _)))

theorem fold_chunkedKeysSampledAt {F : ShaCompress} {A : RustAlloc}
    (a : BitVec 64) (g : AuthenticatorGhost)
    (outSt : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (auth : Authenticator) (epoch : Epoch) (ek dk : Bytes)
    (ek_ptr dk_ptr : BitVec 64)
    (huc : outSt.uc = { epoch := epoch, auth := auth, ek := ek, dk := dk })
    (hek : BitVec.ofNat 64 ek.length = 1152#64)
    (hdk : BitVec.ofNat 64 dk.length = 2400#64) :
    polyEncoderAt A a outSt.sending_hdr ∗
    ekSentInlineWordsAt (a + 400#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
    authHeapBufs A g auth ∗
    RustHeap.vecU8Buf A 1152#64 ek_ptr ek ∗
    RustHeap.vecU8Buf A 2400#64 dk_ptr dk ⊢
    chunkedKeysSampledAt A a outSt := by
  unfold chunkedKeysSampledAt unchunkedHeaderSentAt
  rw [huc]
  dsimp only [ekSentInlineWordsAt]
  have h1 := fold_authenticatorAt_of_inline (A := A) g (a + 400#64) auth
  have h2 := fold_vecU8_of_inline (A := A) ((a + 400#64) + 48#64) 1152#64 ek_ptr 1152#64 ek hek
  have h3 := fold_vecU8_of_inline (A := A) ((a + 400#64) + 72#64) 2400#64 dk_ptr 2400#64 dk hdk
  rw [show ((a + 400#64) + 48#64) + 8#64 = (a + 400#64) + 56#64 by bv_omega,
      show ((a + 400#64) + 48#64) + 16#64 = (a + 400#64) + 64#64 by bv_omega] at h2
  rw [show ((a + 400#64) + 72#64) + 8#64 = (a + 400#64) + 80#64 by bv_omega,
      show ((a + 400#64) + 72#64) + 16#64 = (a + 400#64) + 88#64 by bv_omega] at h3
  have hlhs :
      polyEncoderAt A a outSt.sending_hdr ∗
      (authInlineWordsAt g (a + 400#64) auth ∗
       ((a + 400#64 + 48#64) ↦₆₄ 1152#64) ∗ ((a + 400#64 + 56#64) ↦₆₄ ek_ptr) ∗ ((a + 400#64 + 64#64) ↦₆₄ 1152#64) ∗
       ((a + 400#64 + 72#64) ↦₆₄ 2400#64) ∗ ((a + 400#64 + 80#64) ↦₆₄ dk_ptr) ∗ ((a + 400#64 + 88#64) ↦₆₄ 2400#64) ∗
       ((a + 400#64 + 96#64) ↦₆₄ epoch)) ∗
      authHeapBufs A g auth ∗
      RustHeap.vecU8Buf A 1152#64 ek_ptr ek ∗
      RustHeap.vecU8Buf A 2400#64 dk_ptr dk =
      polyEncoderAt A a outSt.sending_hdr ∗
      ((authInlineWordsAt g (a + 400#64) auth ∗ authHeapBufs A g auth) ∗
       (((a + 400#64 + 48#64) ↦₆₄ 1152#64) ∗ ((a + 400#64 + 56#64) ↦₆₄ ek_ptr) ∗
        ((a + 400#64 + 64#64) ↦₆₄ 1152#64) ∗ RustHeap.vecU8Buf A 1152#64 ek_ptr ek) ∗
       (((a + 400#64 + 72#64) ↦₆₄ 2400#64) ∗ ((a + 400#64 + 80#64) ↦₆₄ dk_ptr) ∗
        ((a + 400#64 + 88#64) ↦₆₄ 2400#64) ∗ RustHeap.vecU8Buf A 2400#64 dk_ptr dk) ∗
       ((a + 400#64 + 96#64) ↦₆₄ epoch)) := by ac_rfl
  rw [hlhs]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (Entails.refl _))))

/-- Sub-step 1c (`entry + 684#64 -> entry + 2588#64`):
    calls `Authenticator::mac_hdr`, sets up `ekSentInlineWordsAt` at `sp + 4080#64`,
    reserves 32 additional bytes in the `hdr` Vec via `do_reserve_and_handle [local#2]`,
    and copies the 32-byte `mac` into `hdr_ptr' + 64#64`. -/
theorem step_keysUnsampled_684_to_2588 {F : ShaCompress}
    {img : Obj.Image} {K : MlKem} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hmac_call : AuthMacHdrPinnedOkX img F A ext)
    (hres_call : DoReserve2OkX img A ext)
    (sp epoch hdr_ptr ek_ptr dk_ptr : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (seed : List.Vector (BitVec 8) 64)
    (mac : Bytes)
    (hmac : auth.macHdr F epoch (K.fromSeed seed).1.toList = .ok mac)
    (hhdr_ne : hdr_ptr ≠ 0)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 684#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx0 : s.readReg64 .x0 = sp + 7136#64)
    (hx1 : s.readReg64 .x1 = epoch)
    (hx2 : s.readReg64 .x2 = hdr_ptr)
    (hx3 : s.readReg64 .x3 = 64#64)
    (hx8 : s.readReg64 .x8 = sp + 4832#64)
    (hx20 : s.readReg64 .x20 = hdr_ptr)
    (hx21 : s.readReg64 .x21 = ek_ptr)
    (hx22 : s.readReg64 .x22 = epoch)
    (hx23 : s.readReg64 .x23 = dk_ptr)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx25 : s.readReg64 .x25 = 2400#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx27 : s.readReg64 .x27 = 64#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authenticatorPinAt A g (sp + 7136#64) auth ∗
      ((sp + 4056#64) ↦₆₄ epoch) ∗
      memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗
      A.live hdr_ptr 64 1 ∗
      (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
      RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
      RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
      A.pool ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (hdr_ptr' mac_cap mac_ptr : BitVec 64),
      ImgCallInv img sf →
      hdr_ptr' ≠ 0 →
      mac_ptr ≠ 0 → (mac_cap == 0#64) = false →
      32 ≤ mac_cap.toNat → mac_cap.toNat < 2 ^ 63 →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 2588#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x0 = hdr_ptr' + 64#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = mac_cap →
      sf.readReg64 .x21 = mac_ptr →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = hdr_ptr' →
      sf.readReg64 .x24 = 64#64 →
      sf.readReg64 .x25 = 32#64 →
      sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        ((authInlineWordsAt g (sp + 2392#64) auth ∗
          authInlineWordsAt g (sp + 7136#64) auth ∗
          authHeapBufs A g auth ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
          memRegion (sp + 4704#64) 2400 ∗
          ((sp + 7104#64) ↦₆₄ 128#64) ∗
          ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗
          ((sp + 7120#64) ↦₆₄ 64#64) ∗
          A.live hdr_ptr' 128 1 ∗
          (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
          memRegion (hdr_ptr' + 96#64) 32 ∗
          A.live mac_ptr mac_cap.toNat 1 ∗
          (mac_ptr ↦ₛ mac) ∗
          memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
          RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
          RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
          A.pool ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hmac_at := spqrSend_macHdr_ok hmac_call
  have hres_at := spqrSend_doReserve2_ok hres_call
  have hmemcpy := spqrSend_memcpy_region_ok hA
  have hhdr_len : (K.fromSeed seed).1.toList.length = 64 := List.Vector.toList_length _
  obtain ⟨rfl, _, _⟩ := macHdr_ok_elim hmac
  have hmac_len : (auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList).length = 32 :=
    macHdrUnchecked_length F auth epoch _
  spqr_send_fetches_range img.base (Rust.withPanics ext) 684 188
  spqr_send_fetches_range img.base (Rust.withPanics ext) 11880 28
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName = entry
  examples_hide_fetches; subst hP
  simp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x8,
    Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27]
    at hx0 hx1 hx2 hx3 hx8 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27
  rw [memRegion_4704_2400_split_macHdr sp]
  apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::authenticator::Authenticator>::mac_hdr")) img hinv; wp_steps
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro hinv_1
  refine call_inImage_calleeStack (x := ({
      outVec := sp + 4832#64, selfA := sp + 7136#64, g := g, auth := auth,
      ep := epoch, hdrRO := false, hdrA := hdr_ptr, hdr := (K.fromSeed seed).1.toList } : AuthMacHdrPinnedGhost))
    (s0 := s0) sp authMacHdrStackX (by decide)
    (T_pre := memRegion (sp + 4832#64) 24 ∗ authenticatorPinAt A g (sp + 7136#64) auth ∗
      (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗ A.pool)
    (T_post := fun _ => vecU8 A (sp + 4832#64) (auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList) ∗
      authenticatorPinAt A g (sp + 7136#64) auth ∗ (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗ A.pool)
    (F := authInlineWordsAt g (sp + 2392#64) auth ∗ ((sp + 4056#64) ↦₆₄ epoch) ∗ memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4704#64) 128 ∗ memRegion (sp + 4856#64) 2248 ∗
      memRegion (sp + 7104#64) 24 ∗ A.live hdr_ptr 64 1 ∗
      RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
      RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗ Frame)
    (φ_pre := _) (φ_post := _) hmac_at hinv_1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
    hsp_align (by simp only [arm64_norm, *]) (ret_pc := entry + 688#64) (by simp only [Reg.lr, arm64_norm, *])
    (by dsimp only [authMacHdrPinnedSpec]; rw [ChainProofs.bytesAt_false]; ac_rfl)
    (by simp only [hhdr_len, Reg.x8, Reg.x0, Reg.x1, Reg.x2, Reg.x3, wp_norm, arm64_norm, *])
    (by ac_rfl) (fun _ _ => rfl)
    (fun sf => authMacHdrPinned_onPanic_of_ok _ hmac _ sf)
    (by intro sf; dsimp only [authMacHdrPinnedSpec]; rw [ChainProofs.bytesAt_false]; ac_rfl) ?_
  intro sm1 hpc_sm1 hrun_sm1 hsp_sm1 ⟨htr_sm1, _⟩ hinv_sm1
    hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
  simp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x8,
    Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
    wp_norm, arm64_norm, *] at htr_sm1 hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
  apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]")) img hinv_sm1
  refine SepWP.fold (vecU8_len32_expose (sp + 4832#64) _ hmac_len) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro mac_cap
  apply SepWP.exists_elim; intro mac_ptr
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun ⟨hmac_cap_ge, hmac_cap_lt, hmac_ptr_ne, hmac_cap_b⟩ => ?_
  rw [authenticatorPinAt_eq_inline_heap A g (sp + 7136#64) auth,
      memRegion_104_eq_words13 (sp + 4080#64),
      memRegion_128_eq_words16 (sp + 4704#64),
      memRegion_24_eq_words3 (sp + 7104#64)]
  wp_conv_pre =>
    dsimp only [authInlineWordsAt, words16At, words8At]
    simp only [BitVec.add_assoc, arm64_norm, sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 32 (apply SepWP.exists_elim; intro _)
  wp_steps
  have hfold_pre_res :
      authInlineWordsAt g (sp + 4080#64) auth ∗
      ((sp + 4128#64) ↦₆₄ 1152#64) ∗ ((sp + 4136#64) ↦₆₄ ek_ptr) ∗ ((sp + 4144#64) ↦₆₄ 1152#64) ∗
      ((sp + 4152#64) ↦₆₄ 2400#64) ∗ ((sp + 4160#64) ↦₆₄ dk_ptr) ∗ ((sp + 4168#64) ↦₆₄ 2400#64) ∗
      ((sp + 4176#64) ↦₆₄ epoch) ∗
      words16At (sp + 4704#64)
        g.rootKey.cap g.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
        g.macKey.cap g.macKey.ptr (BitVec.ofNat 64 auth.macKey.length)
        1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch 64#64 hdr_ptr 64#64 ∗
      (((sp + 4832#64) ↦₆₄ mac_cap) ∗ ((sp + 4840#64) ↦₆₄ mac_ptr) ∗ ((sp + 4848#64) ↦₆₄ 32#64)) ∗
      memRegion (sp + 4856#64) 2248 ⊢
      ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
      memRegion (sp + 4704#64) 2400 := by
    have h128 := words16At_entails_memRegion (sp + 4704#64)
      g.rootKey.cap g.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
      g.macKey.cap g.macKey.ptr (BitVec.ofNat 64 auth.macKey.length)
      1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch 64#64 hdr_ptr 64#64
    have h24 := words3_entails_memRegion (sp + 4832#64) mac_cap mac_ptr 32#64
    rw [show (sp + 4832#64) + 8#64 = sp + 4840#64 by bv_omega,
        show (sp + 4832#64) + 16#64 = sp + 4848#64 by bv_omega] at h24
    have hlhs :
        authInlineWordsAt g (sp + 4080#64) auth ∗
        ((sp + 4128#64) ↦₆₄ 1152#64) ∗ ((sp + 4136#64) ↦₆₄ ek_ptr) ∗ ((sp + 4144#64) ↦₆₄ 1152#64) ∗
        ((sp + 4152#64) ↦₆₄ 2400#64) ∗ ((sp + 4160#64) ↦₆₄ dk_ptr) ∗ ((sp + 4168#64) ↦₆₄ 2400#64) ∗
        ((sp + 4176#64) ↦₆₄ epoch) ∗
        words16At (sp + 4704#64)
          g.rootKey.cap g.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
          g.macKey.cap g.macKey.ptr (BitVec.ofNat 64 auth.macKey.length)
          1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch 64#64 hdr_ptr 64#64 ∗
        (((sp + 4832#64) ↦₆₄ mac_cap) ∗ ((sp + 4840#64) ↦₆₄ mac_ptr) ∗ ((sp + 4848#64) ↦₆₄ 32#64)) ∗
        memRegion (sp + 4856#64) 2248 =
        ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
        words16At (sp + 4704#64)
          g.rootKey.cap g.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
          g.macKey.cap g.macKey.ptr (BitVec.ofNat 64 auth.macKey.length)
          1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch 64#64 hdr_ptr 64#64 ∗
        (((sp + 4832#64) ↦₆₄ mac_cap) ∗ ((sp + 4840#64) ↦₆₄ mac_ptr) ∗ ((sp + 4848#64) ↦₆₄ 32#64)) ∗
        memRegion (sp + 4856#64) 2248 := by
      dsimp only [ekSentInlineWordsAt]
      simp only [BitVec.add_assoc, arm64_norm]
    rw [hlhs, memRegion_4704_2400_split_macHdr sp]
    exact sepConj_mono (Entails.refl _) (sepConj_mono h128 (sepConj_mono h24 (Entails.refl _)))
  refine SepWP.fold hfold_pre_res
    (by
      (conv => rhs; arg 1; dsimp only [authInlineWordsAt, words16At, words8At]; simp only [BitVec.add_assoc, arm64_norm])
      sep_focus) ?_
  clear hfold_pre_res
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro hinv_2
  refine call_inImage_calleeStack (x := ({
      v := sp + 7104#64, cap := 64#64, ptr := hdr_ptr,
      bs := (K.fromSeed seed).1.toList, additional := 32 } : DoReserveCall))
    (s0 := s0) sp doReserve32Stack (by decide)
    (T_pre := ((sp + 7104#64) ↦₆₄ 64#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr) ∗
      A.live hdr_ptr 64 1 ∗ (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗ A.pool)
    (T_post := fun _ => (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ p') ∗
      A.live p' 128 1 ∗ (p' ↦ₛ (K.fromSeed seed).1.toList) ∗
      memRegion (p' + 64#64) 64) ∗ A.pool)
    (F := authInlineWordsAt g (sp + 2392#64) auth ∗ authInlineWordsAt g (sp + 7136#64) auth ∗ authHeapBufs A g auth ∗
      ((sp + 4056#64) ↦₆₄ epoch) ∗
      ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
      memRegion (sp + 4704#64) 2400 ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
      A.live mac_ptr mac_cap.toNat 1 ∗
      (mac_ptr ↦ₛ auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList) ∗
      memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
      RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
      RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗ Frame)
    (φ_pre := _) (φ_post := _) hres_at hinv_2
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
    hsp_align (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := entry + 11900#64) (by simp only [Reg.lr, wp_norm, arm64_norm, *])
    (by
      dsimp only [doReserve1Raw32Spec]
      have h64_ne : ((64#64 : BitVec 64) = 0#64) = False := propext (by decide)
      have h64_toNat : (64#64 : BitVec 64).toNat = 64 := rfl
      simp only [hhdr_len, h64_ne, h64_toNat, ↓reduceIte, Nat.sub_self,
        ProofLib.memRegion_zero, sepConj_emp,
        show (sp + 7104#64) + 8#64 = sp + 7112#64 by bv_omega, sepConj_assoc]
      ac_rfl)
    (by
      have h64_toNat : (64#64 : BitVec 64).toNat = 64 := rfl
      have hhdr_ne' : hdr_ptr ≠ 0#64 := hhdr_ne
      simp only [hhdr_len, h64_toNat, reserveCap_64_64_32,
        Reg.x0, Reg.x1, Reg.x2, hhdr_ne', ne_eq, not_false_eq_true, wp_norm, arm64_norm, *])
    (by dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]; ac_rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (by
      intro sf
      dsimp only [doReserve1Raw32Spec]
      have h64_toNat : (64#64 : BitVec 64).toNat = 64 := rfl
      simp only [hhdr_len, h64_toNat, reserveCap_64_64_32,
        show BitVec.ofNat 64 128 = 128#64 from rfl,
        show BitVec.ofNat 64 64 = 64#64 from rfl,
        show 128 - 64 = 64 from rfl,
        show (sp + 7104#64) + 8#64 = sp + 7112#64 by bv_omega, sepConj_assoc]
      ac_rfl) ?_
  intro sm2 hpc_sm2 hrun_sm2 hsp_sm2 htr_sm2 hinv_sm2
    hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
  simp only [wp_norm, arm64_norm, *] at htr_sm2 hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
  apply of_sepWP_inImage (mid := entry + 2588#64) img hinv_sm2
  wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro hdr_ptr'
  refine SepWP.fold (Entails.refl ⌜hdr_ptr' ≠ 0#64⌝) (by sep_focus) ?_
  refine SepWP.pure_elim fun hhdr_ptr'_ne => ?_
  have hsplit_64 :
      memRegion (hdr_ptr' + 64#64) 64 =
      memRegion (hdr_ptr' + 64#64) (auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList).length ∗
      memRegion (hdr_ptr' + 96#64) 32 := by
    rw [hmac_len,
        ProofLib.memRegion_split' (b := hdr_ptr' + 64#64) (n := 32) (k := 32)
          (b' := hdr_ptr' + 96#64) rfl (by bv_omega) (by decide)]
  wp_conv_pre => rw [hsplit_64]
  wp_steps; wp_apply; wp_steps
  have hjoin_hdr_mac :
      (hdr_ptr' ↦ₛ (K.fromSeed seed).1.toList) ∗
      ((hdr_ptr' + 64#64) ↦ₛ auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList) ⊢
      (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList)) := by
    rw [pointsToBytes_append, hhdr_len]
    exact Entails.refl _
  refine SepWP.fold hjoin_hdr_mac (by sep_focus) ?_
  refine finish_sepWP_inImage (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (fun hinv_3 => hnext _ hdr_ptr' mac_cap mac_ptr hinv_3
      hhdr_ptr'_ne hmac_ptr_ne hmac_cap_b hmac_cap_ge hmac_cap_lt
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *])
      (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x19, arm64_norm, *])
      (by simp only [Reg.x20, arm64_norm, *])
      (by simp only [Reg.x21, arm64_norm, *])
      (by simp only [Reg.x22, arm64_norm, *])
      (by simp only [Reg.x23, arm64_norm, *])
      (by simp only [Reg.x24, arm64_norm, *])
      (by simp only [Reg.x25, arm64_norm, *])
      (by simp only [Reg.x26, arm64_norm, *])
      (by simp only [Reg.x28, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))
    (Entails.of_eq (by ac_rfl))

theorem memRegion_4704_2400_split_nextChunk (sp : BitVec 64) :
    memRegion (sp + 4704#64) 2400 =
      memRegion (sp + 4704#64) 504 ∗
      memRegion (sp + 5208#64) 34 ∗
      memRegion (sp + 5242#64) 1862 := by
  rw [ProofLib.memRegion_split' (b := sp + 4704#64) (n := 504) (k := 1896) (b' := sp + 5208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 5208#64) (n := 34) (k := 1862) (b' := sp + 5242#64) rfl (by bv_omega) (by decide)]

theorem encodeBytes_onPanic_of_ok {A : RustAlloc} (x : EncodeBytesGhost) {enc : PolyEncoder}
    (_h : encodeBytesResult x.msg = .ok enc) (s0 sf : State) :
    (encodeBytesSpecX A).onPanic x s0 sf =
      (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) := by
  dsimp only [encodeBytesSpecX, encodeBytesSpec]

theorem polyNextChunk_onPanic_of_ok {A : RustAlloc} (b : BitVec 64) (x : PolyNextChunkGhost)
    (_h : x.enc.nextChunk = .ok (x.enc', x.chunk)) (s0 sf : State) :
    (polyNextChunkSpec A b).onPanic x s0 sf =
      (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) := by
  dsimp only [polyNextChunkSpec]

theorem pointsToBytes_and_tail_entails_memRegion (ptr : BitVec 64) (bs : Bytes)
    (len cap : Nat) (hlen : bs.length = len) (hle : len ≤ cap) (hlt : cap < 2 ^ 64) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 len) (cap - len) ⊢
    memRegion ptr cap := by
  have h1 := pointsToBytes_entails_memRegion ptr bs
  rw [hlen] at h1
  rw [ProofLib.memRegion_split' (b := ptr) (n := len) (k := cap - len)
      (b' := ptr + BitVec.ofNat 64 len) (by omega) rfl (by omega)]
  exact sepConj_mono_left h1

end CryptoVerification.SpqrV1.Top.Send


















