/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.Defs
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalSession.CryptoHmacSha256

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.CBC
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds

/-! ## BitVec, Alignment, and XOR Helpers -/

@[scoped simp, arm64_norm]
theorem zero8_concat8 :
    (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl

@[scoped simp, arm64_norm]
theorem zero64_concat2 : (0#64 ++ 0#64 : BitVec 128) = 0#128 := rfl

@[scoped simp, arm64_norm]
theorem adrp_177112_mask : (177112#64 &&& bv% (2 ^ 64 - 4096) : BitVec 64) = 176128#64 := rfl

/-- Stack pointer of `new_from_slice` after the prologue (`s₀.sp - 544`). -/
def nfsSp (s₀ : State) : BitVec 64 := s₀.sp - 544#64

theorem nfs_sp_eq_add (s₀ : State) :
    s₀.sp = nfsSp s₀ + 544#64 := by
  unfold nfsSp; bv_omega

theorem nfs_sp_align {s₀ : State} (h : (s₀.sp &&& 0b1111#64) = 0#64) :
    (nfsSp s₀ &&& 0b1111#64) = 0#64 := by
  unfold nfsSp; bv_bits

theorem nfs_sp_add_464_align {s₀ : State} (h : (s₀.sp &&& 0b1111#64) = 0#64) :
    ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := by
  unfold nfsSp; bv_bits

theorem nfs_sp_add_544_align {s₀ : State} (h : (s₀.sp &&& 0b1111#64) = 0#64) :
    ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := by
  rw [← nfs_sp_eq_add]; exact h

@[scoped simp, arm64_norm]
theorem nfsSp_add_464_sub_464 (s₀ : State) :
    (nfsSp s₀ + 464#64) - 464#64 = nfsSp s₀ := by
  bv_omega

theorem nfs_adrp_x22_0x2b3d8 {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    ((b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 40)) &&& 0xfffffffffffff000#64) + bv% (ls_str% "kyber_pre_key_pu" + 256 - page% (ls_off% "<libsignal_protocol::protocol::SenderKeyMessage as core::convert::TryFrom<&[u8]>>::try_from" + 312)) = b + bv% (ls_str% "kyber_pre_key_pu" + 256) := by
  bv_bits

theorem nfs_adrp_x22_0x2b3d8_assoc {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    (((b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 40)) &&& 0xfffffffffffff000#64) + bv% (page% (ls_str% "kyber_pre_key_pu" + 256) - page% (ls_off% "<libsignal_protocol::protocol::SenderKeyMessage as core::convert::TryFrom<&[u8]>>::try_from" + 312))) + bv% ((ls_str% "kyber_pre_key_pu" + 256) % 4096) = b + bv% (ls_str% "kyber_pre_key_pu" + 256) := by
  bv_bits

theorem nfs_ule_65_false {len : BitVec 64} (h : len.toNat ≤ 64) :
    BitVec.ule 0x41#64 len = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; simp; omega

@[scoped simp, arm64_norm]
theorem xor_0x36_norm64 (a : BitVec 8) :
    (((a.zeroExtend 64 ^^^ 0x36#64).truncate 32).zeroExtend 64) = (a ^^^ 0x36#8).zeroExtend 64 := by
  bv_bits

@[scoped simp, arm64_norm]
theorem xor_0x36_norm32 (a : BitVec 8) :
    ((a.zeroExtend 32 ^^^ 0x36#32).zeroExtend 64) = (a ^^^ 0x36#8).zeroExtend 64 := by
  bv_bits

@[scoped simp, arm64_norm]
theorem xor_0x6a_norm64 (a : BitVec 8) :
    (((a.zeroExtend 64 ^^^ 0x6a#64).truncate 32).zeroExtend 64) = (a ^^^ 0x6a#8).zeroExtend 64 := by
  bv_bits

@[scoped simp, arm64_norm]
theorem xor_0x6a_norm32 (a : BitVec 8) :
    ((a.zeroExtend 32 ^^^ 0x6a#32).zeroExtend 64) = (a ^^^ 0x6a#8).zeroExtend 64 := by
  bv_bits

@[scoped simp, arm64_norm]
theorem xor_0x36_0x6a_byte (a : BitVec 8) :
    (a ^^^ 0x36#8) ^^^ 0x6a#8 = a ^^^ 0x5c#8 := by
  rw [BitVec.xor_assoc]; rfl

/-! ## Memory Copy and `keyBlock` Helpers -/

private theorem toLEBytes_8_concat8 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    toLEBytes 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) =
      [b0, b1, b2, b3, b4, b5, b6, b7] := by
  rw [toLEBytes_8_eq_list]
  simp only [List.cons.injEq, and_true]
  refine ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits,
          by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

theorem toLEBytes_8_read64_eq (m : Memory) (a : BitVec 64) :
    toLEBytes 8 (m.read64 a) = m.readBytes a 8 := by
  rw [readBytes_8_eq]
  dsimp only [Memory.read64]
  rw [toLEBytes_8_concat8, BitVec.add_zero]

theorem write64_pair_read64_eq_writeBytes_16 (m₁ m₂ : Memory) (dst src : BitVec 64) :
    (m₁.write64 dst (m₂.read64 src)).write64 (dst + 8#64) (m₂.read64 (src + 8#64)) =
      m₁.writeBytes dst (m₂.readBytes src 16) := by
  rw [write64_eq_writeBytes, write64_eq_writeBytes]
  have happ := (writeBytes_append m₁ dst
    (toLEBytes 8 (m₂.read64 src)) (toLEBytes 8 (m₂.read64 (src + 8#64)))).symm
  rw [toLEBytes_length] at happ
  rw [happ, toLEBytes_8_read64_eq, toLEBytes_8_read64_eq, ← LibsignalAesCbc.Run.Bytes.readBytes_add m₂ src 8 8]

theorem write64_quad_zero_eq_writeBytes_32 (m : Memory) (a : BitVec 64) :
    ((((m.write64 a 0#64).write64 (a + 8#64) 0#64).write64 (a + 16#64) 0#64).write64 (a + 24#64) 0#64) =
      m.writeBytes a (List.replicate 32 0#8) := by
  have h16 : a + 24#64 = (a + 16#64) + 8#64 := by bv_omega
  rw [h16, write64_zero_pair_eq_writeBytes, write64_zero_pair_eq_writeBytes]
  have happ := (writeBytes_append m a (List.replicate 16 0#8) (List.replicate 16 0#8)).symm
  simp only [List.length_replicate] at happ
  rw [happ]
  rfl

theorem write64_oct_zero_eq_writeBytes_64 (m : Memory) (sp : BitVec 64) :
    ((((((((m.write64 (sp + 112#64) 0#64).write64 (sp + 120#64) 0#64).write64
      (sp + 128#64) 0#64).write64 (sp + 136#64) 0#64).write64
      (sp + 144#64) 0#64).write64 (sp + 152#64) 0#64).write64
      (sp + 160#64) 0#64).write64 (sp + 168#64) 0#64) =
      m.writeBytes (sp + 112#64) (List.replicate 64 0#8) := by
  have h1 : sp + 120#64 = (sp + 112#64) + 8#64 := by bv_omega
  have h2 : sp + 128#64 = (sp + 112#64) + 16#64 := by bv_omega
  have h3 : sp + 136#64 = (sp + 112#64) + 24#64 := by bv_omega
  have h5 : sp + 152#64 = (sp + 144#64) + 8#64 := by bv_omega
  have h6 : sp + 160#64 = (sp + 144#64) + 16#64 := by bv_omega
  have h7 : sp + 168#64 = (sp + 144#64) + 24#64 := by bv_omega
  rw [h1, h2, h3, h5, h6, h7,
      write64_quad_zero_eq_writeBytes_32, write64_quad_zero_eq_writeBytes_32]
  have h4 : sp + 144#64 = (sp + 112#64) + BitVec.ofNat 64 (List.replicate 32 0#8).length := by
    simp only [List.length_replicate]; bv_omega
  rw [h4, ← writeBytes_append]
  rfl

theorem writeBytes_key_over_zero64 (m : Memory) (a : BitVec 64) (key : List (BitVec 8)) :
    (m.writeBytes a (List.replicate 64 0#8)).writeBytes a key =
      m.writeBytes a (keyBlock key) := by
  rw [ProofLib.writeBytes_writeBytes_overwrite m a (List.replicate 64 0#8) key (by simp),
      List.drop_replicate]
  rfl

@[scoped simp]
theorem keyBlock_length {key : List (BitVec 8)} (hk : key.length ≤ 64) :
    (keyBlock key).length = 64 := by
  simp [keyBlock]; omega

theorem write64_quad_read64_eq_writeBytes_32 (m₁ m₂ : Memory) (dst src : BitVec 64) :
    ((((m₁.write64 dst (m₂.read64 src)).write64 (dst + 8#64) (m₂.read64 (src + 8#64))).write64
      (dst + 16#64) (m₂.read64 (src + 16#64))).write64
      (dst + 24#64) (m₂.read64 (src + 24#64))) =
      m₁.writeBytes dst (m₂.readBytes src 32) := by
  have hd24 : dst + 24#64 = (dst + 16#64) + 8#64 := by bv_omega
  have hs24 : src + 24#64 = (src + 16#64) + 8#64 := by bv_omega
  rw [hd24, hs24, write64_pair_read64_eq_writeBytes_16, write64_pair_read64_eq_writeBytes_16]
  have happ := (writeBytes_append m₁ dst (m₂.readBytes src 16) (m₂.readBytes (src + 16#64) 16)).symm
  rw [Memory.readBytes_length] at happ
  rw [happ, ← LibsignalAesCbc.Run.Bytes.readBytes_add m₂ src 16 16]

/-! ## 16-Byte XOR Chunk Helpers -/

def byteAt (l : List (BitVec 8)) (i : ℕ) : BitVec 8 :=
  l.getD i 0#8

def slice16 (l : List (BitVec 8)) (k : ℕ) : List (BitVec 8) :=
  [byteAt l (k + 0), byteAt l (k + 1), byteAt l (k + 2), byteAt l (k + 3),
   byteAt l (k + 4), byteAt l (k + 5), byteAt l (k + 6), byteAt l (k + 7),
   byteAt l (k + 8), byteAt l (k + 9), byteAt l (k + 10), byteAt l (k + 11),
   byteAt l (k + 12), byteAt l (k + 13), byteAt l (k + 14), byteAt l (k + 15)]

@[scoped simp]
theorem slice16_length (l : List (BitVec 8)) (k : ℕ) :
    (slice16 l k).length = 16 := rfl

theorem byteAt_map_xor (l : List (BitVec 8)) (c : BitVec 8) (i : ℕ) (hi : i < l.length) :
    byteAt (l.map (· ^^^ c)) i = byteAt l i ^^^ c := by
  simp [byteAt, List.getD, List.getElem?_eq_getElem hi]

theorem slice16_map_xor (l : List (BitVec 8)) (hl : l.length = 64) (c : BitVec 8) (k : ℕ)
    (hk : k + 16 ≤ 64) :
    [byteAt l (k + 0) ^^^ c, byteAt l (k + 1) ^^^ c,
     byteAt l (k + 2) ^^^ c, byteAt l (k + 3) ^^^ c,
     byteAt l (k + 4) ^^^ c, byteAt l (k + 5) ^^^ c,
     byteAt l (k + 6) ^^^ c, byteAt l (k + 7) ^^^ c,
     byteAt l (k + 8) ^^^ c, byteAt l (k + 9) ^^^ c,
     byteAt l (k + 10) ^^^ c, byteAt l (k + 11) ^^^ c,
     byteAt l (k + 12) ^^^ c, byteAt l (k + 13) ^^^ c,
     byteAt l (k + 14) ^^^ c, byteAt l (k + 15) ^^^ c] =
      slice16 (l.map (· ^^^ c)) k := by
  unfold slice16
  repeat' rw [byteAt_map_xor l c _ (by omega)]

theorem getElem?_getD_eq_getElem (l : List (BitVec 8)) (i : ℕ) (h : i < l.length) :
    l[i]?.getD 0#8 = l[i] := by
  rw [List.getElem?_eq_getElem h, Option.getD_some]

theorem slice16_0_16_eq_take_32 (l : List (BitVec 8)) (hl : l.length = 64) :
    l.take 32 = slice16 l 0 ++ slice16 l 16 := by
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  have hi : i < 32 := by simpa [hl] using h1
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
    i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
    i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
    i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    { simp [slice16, byteAt]
      exact (getElem?_getD_eq_getElem l _ (by omega)).symm }

theorem slice16_32_48_eq_drop_32 (l : List (BitVec 8)) (hl : l.length = 64) :
    l.drop 32 = slice16 l 32 ++ slice16 l 48 := by
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  have hi : i < 32 := by simpa [hl] using h1
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
    i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
    i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
    i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    { simp [slice16, byteAt]
      exact (getElem?_getD_eq_getElem l _ (by omega)).symm }

theorem slice16_append_64 (l : List (BitVec 8)) (hl : l.length = 64) :
    slice16 l 0 ++ slice16 l 16 ++ slice16 l 32 ++ slice16 l 48 = l := by
  have h1 := slice16_0_16_eq_take_32 l hl
  have h2 := slice16_32_48_eq_drop_32 l hl
  have h3 : (slice16 l 0 ++ slice16 l 16) ++ (slice16 l 32 ++ slice16 l 48) = l := by
    rw [← h1, ← h2, List.take_append_drop]
  simpa [List.append_assoc] using h3

theorem read8_16_of_readBytes_slice16 (m : Memory) (sp off : BitVec 64) (l : List (BitVec 8)) (k : ℕ)
    (h : m.readBytes (sp + off) 16 = slice16 l k) :
    m.read8 (sp + off) = byteAt l (k + 0) ∧
    m.read8 (sp + (off + 1#64)) = byteAt l (k + 1) ∧
    m.read8 (sp + (off + 2#64)) = byteAt l (k + 2) ∧
    m.read8 (sp + (off + 3#64)) = byteAt l (k + 3) ∧
    m.read8 (sp + (off + 4#64)) = byteAt l (k + 4) ∧
    m.read8 (sp + (off + 5#64)) = byteAt l (k + 5) ∧
    m.read8 (sp + (off + 6#64)) = byteAt l (k + 6) ∧
    m.read8 (sp + (off + 7#64)) = byteAt l (k + 7) ∧
    m.read8 (sp + (off + 8#64)) = byteAt l (k + 8) ∧
    m.read8 (sp + (off + 9#64)) = byteAt l (k + 9) ∧
    m.read8 (sp + (off + 10#64)) = byteAt l (k + 10) ∧
    m.read8 (sp + (off + 11#64)) = byteAt l (k + 11) ∧
    m.read8 (sp + (off + 12#64)) = byteAt l (k + 12) ∧
    m.read8 (sp + (off + 13#64)) = byteAt l (k + 13) ∧
    m.read8 (sp + (off + 14#64)) = byteAt l (k + 14) ∧
    m.read8 (sp + (off + 15#64)) = byteAt l (k + 15) := by
  rw [readBytes_16_eq, slice16] at h
  simp only [BitVec.add_assoc, List.cons.injEq, and_true] at h
  exact h

theorem readBytes_writeBytes_16_self (m : Memory) (sp off : BitVec 64) (l : List (BitVec 8))
    (hl : l.length = 16) :
    (m.writeBytes (sp + off) l).readBytes (sp + off) 16 = l :=
  Layout.readBytes_writeBytes_eq m (sp + off) l 16 hl (by decide)

theorem readBytes_writeBytes_16_other (m : Memory) (sp off1 off2 : BitVec 64)
    (l : List (BitVec 8)) (n : ℕ)
    (hl : l.length = 16)
    (hd : 16 ≤ (off2 - off1).toNat ∧ n ≤ (off1 - off2).toNat := by decide)
    (hn : n ≤ 64 := by decide) :
    (m.writeBytes (sp + off1) l).readBytes (sp + off2) n = m.readBytes (sp + off2) n := by
  refine Layout.readBytes_writeBytes_of_disjoint m (sp + off1) l (sp + off2) n ?_ (by omega)
  rw [hl]
  rcases hd with ⟨_, _⟩
  simp only [DisjointRegions]
  bv_omega

theorem write8_16_stack_eq_writeBytes (m : Memory) (sp off : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (((((((((((((((m.write8 (sp + off) b0).write8 (sp + (off + 1#64)) b1).write8
      (sp + (off + 2#64)) b2).write8 (sp + (off + 3#64)) b3).write8
      (sp + (off + 4#64)) b4).write8 (sp + (off + 5#64)) b5).write8
      (sp + (off + 6#64)) b6).write8 (sp + (off + 7#64)) b7).write8
      (sp + (off + 8#64)) b8).write8 (sp + (off + 9#64)) b9).write8
      (sp + (off + 10#64)) b10).write8 (sp + (off + 11#64)) b11).write8
      (sp + (off + 12#64)) b12).write8 (sp + (off + 13#64)) b13).write8
      (sp + (off + 14#64)) b14).write8 (sp + (off + 15#64)) b15 =
    m.writeBytes (sp + off) [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
  have h := write8_16_eq_writeBytes m (sp + off) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  simpa only [BitVec.add_assoc] using h

theorem write8_16_stack_288_xor (m : Memory) (sp : BitVec 64) (l : List (BitVec 8)) (c : BitVec 8)
    (hl : l.length = 64) :
    (((((((((((((((m.write8 (sp + 288#64) (byteAt l 0 ^^^ c)).write8
      (sp + 289#64) (byteAt l 1 ^^^ c)).write8
      (sp + 290#64) (byteAt l 2 ^^^ c)).write8
      (sp + 291#64) (byteAt l 3 ^^^ c)).write8
      (sp + 292#64) (byteAt l 4 ^^^ c)).write8
      (sp + 293#64) (byteAt l 5 ^^^ c)).write8
      (sp + 294#64) (byteAt l 6 ^^^ c)).write8
      (sp + 295#64) (byteAt l 7 ^^^ c)).write8
      (sp + 296#64) (byteAt l 8 ^^^ c)).write8
      (sp + 297#64) (byteAt l 9 ^^^ c)).write8
      (sp + 298#64) (byteAt l 10 ^^^ c)).write8
      (sp + 299#64) (byteAt l 11 ^^^ c)).write8
      (sp + 300#64) (byteAt l 12 ^^^ c)).write8
      (sp + 301#64) (byteAt l 13 ^^^ c)).write8
      (sp + 302#64) (byteAt l 14 ^^^ c)).write8
      (sp + 303#64) (byteAt l 15 ^^^ c) =
    m.writeBytes (sp + 288#64) (slice16 (l.map (· ^^^ c)) 0) := by
  rw [← slice16_map_xor l hl c 0 (by omega)]
  exact write8_16_stack_eq_writeBytes m sp 288#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem write8_16_stack_304_xor (m : Memory) (sp : BitVec 64) (l : List (BitVec 8)) (c : BitVec 8)
    (hl : l.length = 64) :
    (((((((((((((((m.write8 (sp + 304#64) (byteAt l 16 ^^^ c)).write8
      (sp + 305#64) (byteAt l 17 ^^^ c)).write8
      (sp + 306#64) (byteAt l 18 ^^^ c)).write8
      (sp + 307#64) (byteAt l 19 ^^^ c)).write8
      (sp + 308#64) (byteAt l 20 ^^^ c)).write8
      (sp + 309#64) (byteAt l 21 ^^^ c)).write8
      (sp + 310#64) (byteAt l 22 ^^^ c)).write8
      (sp + 311#64) (byteAt l 23 ^^^ c)).write8
      (sp + 312#64) (byteAt l 24 ^^^ c)).write8
      (sp + 313#64) (byteAt l 25 ^^^ c)).write8
      (sp + 314#64) (byteAt l 26 ^^^ c)).write8
      (sp + 315#64) (byteAt l 27 ^^^ c)).write8
      (sp + 316#64) (byteAt l 28 ^^^ c)).write8
      (sp + 317#64) (byteAt l 29 ^^^ c)).write8
      (sp + 318#64) (byteAt l 30 ^^^ c)).write8
      (sp + 319#64) (byteAt l 31 ^^^ c) =
    m.writeBytes (sp + 304#64) (slice16 (l.map (· ^^^ c)) 16) := by
  rw [← slice16_map_xor l hl c 16 (by omega)]
  exact write8_16_stack_eq_writeBytes m sp 304#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem write8_16_stack_320_xor (m : Memory) (sp : BitVec 64) (l : List (BitVec 8)) (c : BitVec 8)
    (hl : l.length = 64) :
    (((((((((((((((m.write8 (sp + 320#64) (byteAt l 32 ^^^ c)).write8
      (sp + 321#64) (byteAt l 33 ^^^ c)).write8
      (sp + 322#64) (byteAt l 34 ^^^ c)).write8
      (sp + 323#64) (byteAt l 35 ^^^ c)).write8
      (sp + 324#64) (byteAt l 36 ^^^ c)).write8
      (sp + 325#64) (byteAt l 37 ^^^ c)).write8
      (sp + 326#64) (byteAt l 38 ^^^ c)).write8
      (sp + 327#64) (byteAt l 39 ^^^ c)).write8
      (sp + 328#64) (byteAt l 40 ^^^ c)).write8
      (sp + 329#64) (byteAt l 41 ^^^ c)).write8
      (sp + 330#64) (byteAt l 42 ^^^ c)).write8
      (sp + 331#64) (byteAt l 43 ^^^ c)).write8
      (sp + 332#64) (byteAt l 44 ^^^ c)).write8
      (sp + 333#64) (byteAt l 45 ^^^ c)).write8
      (sp + 334#64) (byteAt l 46 ^^^ c)).write8
      (sp + 335#64) (byteAt l 47 ^^^ c) =
    m.writeBytes (sp + 320#64) (slice16 (l.map (· ^^^ c)) 32) := by
  rw [← slice16_map_xor l hl c 32 (by omega)]
  exact write8_16_stack_eq_writeBytes m sp 320#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem write8_16_stack_336_xor (m : Memory) (sp : BitVec 64) (l : List (BitVec 8)) (c : BitVec 8)
    (hl : l.length = 64) :
    (((((((((((((((m.write8 (sp + 336#64) (byteAt l 48 ^^^ c)).write8
      (sp + 337#64) (byteAt l 49 ^^^ c)).write8
      (sp + 338#64) (byteAt l 50 ^^^ c)).write8
      (sp + 339#64) (byteAt l 51 ^^^ c)).write8
      (sp + 340#64) (byteAt l 52 ^^^ c)).write8
      (sp + 341#64) (byteAt l 53 ^^^ c)).write8
      (sp + 342#64) (byteAt l 54 ^^^ c)).write8
      (sp + 343#64) (byteAt l 55 ^^^ c)).write8
      (sp + 344#64) (byteAt l 56 ^^^ c)).write8
      (sp + 345#64) (byteAt l 57 ^^^ c)).write8
      (sp + 346#64) (byteAt l 58 ^^^ c)).write8
      (sp + 347#64) (byteAt l 59 ^^^ c)).write8
      (sp + 348#64) (byteAt l 60 ^^^ c)).write8
      (sp + 349#64) (byteAt l 61 ^^^ c)).write8
      (sp + 350#64) (byteAt l 62 ^^^ c)).write8
      (sp + 351#64) (byteAt l 63 ^^^ c) =
    m.writeBytes (sp + 336#64) (slice16 (l.map (· ^^^ c)) 48) := by
  rw [← slice16_map_xor l hl c 48 (by omega)]
  exact write8_16_stack_eq_writeBytes m sp 336#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ## Stack Frame, `NfsMemInv`, and `NfsRegInv` -/

/-- The high stack slots `[nfsSp s₀ + 432, nfsSp s₀ + 544)` holding inner block_len = 1
and the saved callee-saved registers `x29, lr, x28, x24, x23, x22, x21, x20, x19`. -/
structure NfsSavedStack (s₀ : State) (m : Memory) : Prop where
  m432 : m.read64 (nfsSp s₀ + 432#64) = 1#64
  m464 : m.read64 (nfsSp s₀ + 464#64) = s₀.readReg64 .x29
  m472 : m.read64 (nfsSp s₀ + 472#64) = s₀.readReg64 .lr
  m480 : m.read64 (nfsSp s₀ + 480#64) = s₀.readReg64 .x28
  m496 : m.read64 (nfsSp s₀ + 496#64) = s₀.readReg64 .x24
  m504 : m.read64 (nfsSp s₀ + 504#64) = s₀.readReg64 .x23
  m512 : m.read64 (nfsSp s₀ + 512#64) = s₀.readReg64 .x22
  m520 : m.read64 (nfsSp s₀ + 520#64) = s₀.readReg64 .x21
  m528 : m.read64 (nfsSp s₀ + 528#64) = s₀.readReg64 .x20
  m536 : m.read64 (nfsSp s₀ + 536#64) = s₀.readReg64 .x19

/-- Memory invariant across chunks 1..8 of `new_from_slice`. -/
structure NfsMemInv (b : BitVec 64) (s₀ : State) (m : Memory) : Prop where
  rw_stack : m.RW (nfsSp s₀) 544
  rw_out : m.RW (s₀.readReg64 .x0) 0x98
  readable_iv : m.Readable (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32
  iv_bytes : m.readBytes (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 = shaStateBytes sha256IV
  disj_iv_stack : DisjointRegions (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (nfsSp s₀) 544
  disj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (nfsSp s₀) 544
  saved : NfsSavedStack s₀ m
  frame : Frame s₀.mem m [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)]

/-- Register invariant across chunks 1..8 of `new_from_slice`. -/
structure NfsRegInv (b : BitVec 64) (s₀ s : State) : Prop where
  sp_eq : s.sp = nfsSp s₀
  sp_align : (nfsSp s₀ &&& 0b1111#64) = 0#64
  x29_eq : s.readReg64 .x29 = nfsSp s₀ + 464#64
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = 1#64
  x22_eq : s.readReg64 .x22 = b + bv% (ls_str% "kyber_pre_key_pu" + 256)
  x25_eq : s.readReg64 .x25 = s₀.readReg64 .x25
  x26_eq : s.readReg64 .x26 = s₀.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27

theorem agreesOutside_toFrame {m m' : Memory} {a : BitVec 64} {sz : ℕ}
    (hA : AgreesOutside m m' a sz) : Frame m m' [(a, sz)] :=
  (Frame.refl m []).trans_agreesOutside hA

theorem AgreesOutside.write8_self (m : Memory) (a : BitVec 64) (v : BitVec 8) :
    AgreesOutside m (m.write8 a v) a 1 :=
  (AgreesOutside.rfl' m a 1).write8 (by simp [InRegion])

theorem AgreesOutside.write64_self (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    AgreesOutside m (m.write64 a v) a 8 :=
  (AgreesOutside.rfl' m a 8).write64 (by simp) (by decide)

theorem AgreesOutside.write128_self (m : Memory) (a : BitVec 64) (v : BitVec 128) :
    AgreesOutside m (m.write128 a v) a 16 :=
  (AgreesOutside.rfl' m a 16).write128 (by simp) (by decide)

theorem Frame.of_agreesOutside_stack {out sp : BitVec 64} {m₀ m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hf : Frame m₀ m [(out, 0x98), (sp, 544)])
    (hA : AgreesOutside m m' (sp + off) sz)
    (hoff : off.toNat + sz ≤ 544) :
    Frame m₀ m' [(out, 0x98), (sp, 544)] :=
  hf.trans_agreesOutside_sub (b := sp) (n := 544) (by simp) (by clear * - hoff; bv_omega) hA

theorem Frame.of_agreesOutside_out {out sp : BitVec 64} {m₀ m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hf : Frame m₀ m [(out, 0x98), (sp, 544)])
    (hA : AgreesOutside m m' (out + off) sz)
    (hoff : off.toNat + sz ≤ 0x98) :
    Frame m₀ m' [(out, 0x98), (sp, 544)] :=
  hf.trans_agreesOutside_sub (b := out) (n := 0x98) (by simp) (by clear * - hoff; bv_omega) hA

private theorem disj_stack_low_high {sp off k : BitVec 64} {sz : ℕ}
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 432)
    (hk : 432 ≤ k.toNat ∧ k.toNat + 8 ≤ 544) :
    DisjointRegions (sp + off) sz (sp + k) 8 := by
  rcases hoff with ⟨_, _⟩
  rcases hk with ⟨_, _⟩
  simp only [DisjointRegions]
  bv_omega

theorem NfsSavedStack.of_agreesOutside_low {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hs : NfsSavedStack s₀ m)
    (hA : AgreesOutside m m' (nfsSp s₀ + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 432) :
    NfsSavedStack s₀ m' := by
  have hf := agreesOutside_toFrame hA
  have hread (k : BitVec 64) (hk : 432 ≤ k.toNat ∧ k.toNat + 8 ≤ 544) :
      m'.read64 (nfsSp s₀ + k) = m.read64 (nfsSp s₀ + k) :=
    Frame.read64_eq hf (by simp [disj_stack_low_high hoff hk])
  exact {
    m432 := (hread 432#64 (by decide)).trans hs.m432
    m464 := (hread 464#64 (by decide)).trans hs.m464
    m472 := (hread 472#64 (by decide)).trans hs.m472
    m480 := (hread 480#64 (by decide)).trans hs.m480
    m496 := (hread 496#64 (by decide)).trans hs.m496
    m504 := (hread 504#64 (by decide)).trans hs.m504
    m512 := (hread 512#64 (by decide)).trans hs.m512
    m520 := (hread 520#64 (by decide)).trans hs.m520
    m528 := (hread 528#64 (by decide)).trans hs.m528
    m536 := (hread 536#64 (by decide)).trans hs.m536
  }

theorem NfsMemInv.of_agreesOutside_low {b : BitVec 64} {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hM : NfsMemInv b s₀ m)
    (hA : AgreesOutside m m' (nfsSp s₀ + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 432) :
    NfsMemInv b s₀ m' := by
  have hf := agreesOutside_toFrame hA
  have hdisj_iv : DisjointRegions (nfsSp s₀ + off) sz (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 := by
    refine hM.disj_iv_stack.symm.sub_left (nfsSp s₀ + off) ⟨hoff.1, ?_⟩
    rcases hoff with ⟨_, _⟩
    bv_omega
  exact {
    rw_stack := (Frame.rw_iff hf _ _).mpr hM.rw_stack
    rw_out := (Frame.rw_iff hf _ _).mpr hM.rw_out
    readable_iv := (Frame.readable_iff hf _ _).mpr hM.readable_iv
    iv_bytes := (Frame.readBytes_eq hf (by simp [hdisj_iv]) (by decide)).trans hM.iv_bytes
    disj_iv_stack := hM.disj_iv_stack
    disj_out_stack := hM.disj_out_stack
    saved := hM.saved.of_agreesOutside_low hA hoff
    frame := Frame.of_agreesOutside_stack hM.frame hA (by omega)
  }

theorem NfsMemInv.writeBytes_low {b : BitVec 64} {s₀ : State} {m : Memory}
    (hM : NfsMemInv b s₀ m) (off : BitVec 64) (bs : List (BitVec 8))
    (hoff : 0 < bs.length ∧ off.toNat + bs.length ≤ 432) :
    NfsMemInv b s₀ (m.writeBytes (nfsSp s₀ + off) bs) :=
  hM.of_agreesOutside_low (AgreesOutside.writeBytes_self m (nfsSp s₀ + off) bs) hoff

theorem NfsMemInv.write64_low {b : BitVec 64} {s₀ : State} {m : Memory}
    (hM : NfsMemInv b s₀ m) (off : BitVec 64) (v : BitVec 64)
    (hoff : off.toNat + 8 ≤ 432 := by decide) :
    NfsMemInv b s₀ (m.write64 (nfsSp s₀ + off) v) :=
  hM.of_agreesOutside_low (AgreesOutside.write64_self m (nfsSp s₀ + off) v) ⟨by decide, hoff⟩

theorem NfsMemInv.write128_low {b : BitVec 64} {s₀ : State} {m : Memory}
    (hM : NfsMemInv b s₀ m) (off : BitVec 64) (v : BitVec 128)
    (hoff : off.toNat + 16 ≤ 432 := by decide) :
    NfsMemInv b s₀ (m.write128 (nfsSp s₀ + off) v) :=
  hM.of_agreesOutside_low (AgreesOutside.write128_self m (nfsSp s₀ + off) v) ⟨by decide, hoff⟩

theorem slice16_getElem (l : List (BitVec 8)) (k i : ℕ) (hi : i < 16) :
    (slice16 l k)[i]'(by rw [slice16_length]; exact hi) = byteAt l (k + i) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
    i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[scoped simp, arm64_norm]
theorem read8_writeBytes_slice16_stack_same (m : Memory) (sp off1 : BitVec 64)
    (l : List (BitVec 8)) (k : ℕ) :
    (m.writeBytes (sp + off1) (slice16 l k)).read8 (sp + off1) = byteAt l k := by
  have h := ProofLib.read8_writeBytes_inbounds m (sp + off1) (slice16 l k) 0
    (by rw [slice16_length]; decide) (by rw [slice16_length]; decide)
  simpa [slice16] using h

@[scoped simp, arm64_norm]
theorem read8_writeBytes_slice16_stack_inbounds (m : Memory) (sp off1 off2 : BitVec 64)
    (l : List (BitVec 8)) (k : ℕ)
    (hd : decide ((off2 - off1).toNat < 16) = true) :
    (m.writeBytes (sp + off1) (slice16 l k)).read8 (sp + off2) =
      byteAt l (k + (off2 - off1).toNat) := by
  have hd' : (off2 - off1).toNat < 16 := of_decide_eq_true hd
  have hadd : (sp + off1) + BitVec.ofNat 64 (off2 - off1).toNat = sp + off2 := by bv_omega
  rw [← hadd, ProofLib.read8_writeBytes_inbounds m (sp + off1) (slice16 l k) (off2 - off1).toNat
    (by rw [slice16_length]; exact hd') (by rw [slice16_length]; decide)]
  exact slice16_getElem l k (off2 - off1).toNat hd'

@[scoped simp, arm64_norm]
theorem read8_writeBytes_slice16_stack_other (m : Memory) (sp off1 off2 : BitVec 64)
    (l : List (BitVec 8)) (k : ℕ)
    (hd : decide (16 ≤ (off2 - off1).toNat ∧ 1 ≤ (off1 - off2).toNat) = true) :
    (m.writeBytes (sp + off1) (slice16 l k)).read8 (sp + off2) = m.read8 (sp + off2) := by
  refine ProofLib.read8_writeBytes_outside m (sp + off1) (sp + off2) (slice16 l k) ?_
  rw [slice16_length]
  have hd' : 16 ≤ (off2 - off1).toNat ∧ 1 ≤ (off1 - off2).toNat := of_decide_eq_true hd
  rcases hd' with ⟨_, _⟩
  simp only [OutsideRegion]
  bv_omega

theorem writeBytes_16_write8_comm (m : Memory) (sp off1 off2 : BitVec 64)
    (l : List (BitVec 8)) (v : BitVec 8)
    (hl : l.length = 16)
    (hd : 16 ≤ (off2 - off1).toNat ∧ 1 ≤ (off1 - off2).toNat := by decide) :
    (m.writeBytes (sp + off1) l).write8 (sp + off2) v =
      (m.write8 (sp + off2) v).writeBytes (sp + off1) l := by
  refine ProofLib.write8_writeBytes_comm m (sp + off2) v (sp + off1) l ?_
  rw [hl]
  rcases hd with ⟨_, _⟩
  simp only [OutsideRegion]
  bv_omega

@[scoped simp]
theorem writeBytes_slice16_write8_comm (m : Memory) (sp off1 off2 : BitVec 64)
    (l : List (BitVec 8)) (k : ℕ) (v : BitVec 8)
    (hd : decide (16 ≤ (off2 - off1).toNat ∧ 1 ≤ (off1 - off2).toNat) = true) :
    (m.writeBytes (sp + off1) (slice16 l k)).write8 (sp + off2) v =
      (m.write8 (sp + off2) v).writeBytes (sp + off1) (slice16 l k) :=
  writeBytes_16_write8_comm m sp off1 off2 (slice16 l k) v (slice16_length l k) (of_decide_eq_true hd)

theorem write64_quad_288_eq_writeBytes_slice16 (m₁ m₂ : Memory) (sp : BitVec 64)
    (l : List (BitVec 8)) (hl : l.length = 64)
    (hread : m₂.readBytes (sp + 112#64) 32 = l.take 32) :
    ((((m₁.write64 (sp + 288#64) (m₂.read64 (sp + 112#64))).write64
      (sp + 296#64) (m₂.read64 (sp + 120#64))).write64
      (sp + 304#64) (m₂.read64 (sp + 128#64))).write64
      (sp + 312#64) (m₂.read64 (sp + 136#64))) =
    (m₁.writeBytes (sp + 288#64) (slice16 l 0)).writeBytes (sp + 304#64) (slice16 l 16) := by
  have hd1 : sp + 296#64 = (sp + 288#64) + 8#64 := by bv_omega
  have hd2 : sp + 304#64 = (sp + 288#64) + 16#64 := by bv_omega
  have hd3 : sp + 312#64 = (sp + 288#64) + 24#64 := by bv_omega
  have hs1 : sp + 120#64 = (sp + 112#64) + 8#64 := by bv_omega
  have hs2 : sp + 128#64 = (sp + 112#64) + 16#64 := by bv_omega
  have hs3 : sp + 136#64 = (sp + 112#64) + 24#64 := by bv_omega
  rw [hd1, hd2, hd3, hs1, hs2, hs3, write64_quad_read64_eq_writeBytes_32,
      hread, slice16_0_16_eq_take_32 l hl, writeBytes_append]
  rfl

theorem write64_quad_320_eq_writeBytes_slice16 (m₁ m₂ : Memory) (sp : BitVec 64)
    (l : List (BitVec 8)) (hl : l.length = 64)
    (hread : m₂.readBytes (sp + 144#64) 32 = l.drop 32) :
    ((((m₁.write64 (sp + 320#64) (m₂.read64 (sp + 144#64))).write64
      (sp + 328#64) (m₂.read64 (sp + 152#64))).write64
      (sp + 336#64) (m₂.read64 (sp + 160#64))).write64
      (sp + 344#64) (m₂.read64 (sp + 168#64))) =
    (m₁.writeBytes (sp + 320#64) (slice16 l 32)).writeBytes (sp + 336#64) (slice16 l 48) := by
  have hd1 : sp + 328#64 = (sp + 320#64) + 8#64 := by bv_omega
  have hd2 : sp + 336#64 = (sp + 320#64) + 16#64 := by bv_omega
  have hd3 : sp + 344#64 = (sp + 320#64) + 24#64 := by bv_omega
  have hs1 : sp + 152#64 = (sp + 144#64) + 8#64 := by bv_omega
  have hs2 : sp + 160#64 = (sp + 144#64) + 16#64 := by bv_omega
  have hs3 : sp + 168#64 = (sp + 144#64) + 24#64 := by bv_omega
  rw [hd1, hd2, hd3, hs1, hs2, hs3, write64_quad_read64_eq_writeBytes_32,
      hread, slice16_32_48_eq_drop_32 l hl, writeBytes_append]
  rfl

def nfsPrologueMem (s₀ : State) : Memory :=
  ((((((((s₀.mem.write64 (nfsSp s₀ + 464#64) (s₀.readReg64 .x29)).write64
    (nfsSp s₀ + 472#64) (s₀.readReg64 .lr)).write64
    (nfsSp s₀ + 480#64) (s₀.readReg64 .x28)).write64
    (nfsSp s₀ + 496#64) (s₀.readReg64 .x24)).write64
    (nfsSp s₀ + 504#64) (s₀.readReg64 .x23)).write64
    (nfsSp s₀ + 512#64) (s₀.readReg64 .x22)).write64
    (nfsSp s₀ + 520#64) (s₀.readReg64 .x21)).write64
    (nfsSp s₀ + 528#64) (s₀.readReg64 .x20)).write64
    (nfsSp s₀ + 536#64) (s₀.readReg64 .x19)

theorem agreesOutside_nfsPrologueMem (s₀ : State) :
    AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 := by
  unfold nfsPrologueMem
  agrees_outside_writes

theorem nfsSavedStack_prologue_432 (s₀ : State) (m : Memory)
    (hA : AgreesOutside (nfsPrologueMem s₀) m (nfsSp s₀ + 112#64) 64) :
    NfsSavedStack s₀ (m.write64 (nfsSp s₀ + 432#64) 1#64) := by
  have hf := agreesOutside_toFrame hA
  have hread (k : BitVec 64) (hk : 464 ≤ k.toNat ∧ k.toNat + 8 ≤ 544) :
      m.read64 (nfsSp s₀ + k) = (nfsPrologueMem s₀).read64 (nfsSp s₀ + k) := by
    refine Frame.read64_eq hf ?_
    clear * - hk
    simp only [List.mem_singleton, forall_eq, DisjointRegions]
    rcases hk with ⟨_, _⟩
    bv_omega
  refine {
    m432 := by simp (config := { decide := true }) only [arm64_norm]
    m464 := by simp (config := { decide := true }) only [arm64_norm, hread 464#64 (by decide), nfsPrologueMem]
    m472 := by simp (config := { decide := true }) only [arm64_norm, hread 472#64 (by decide), nfsPrologueMem]
    m480 := by simp (config := { decide := true }) only [arm64_norm, hread 480#64 (by decide), nfsPrologueMem]
    m496 := by simp (config := { decide := true }) only [arm64_norm, hread 496#64 (by decide), nfsPrologueMem]
    m504 := by simp (config := { decide := true }) only [arm64_norm, hread 504#64 (by decide), nfsPrologueMem]
    m512 := by simp (config := { decide := true }) only [arm64_norm, hread 512#64 (by decide), nfsPrologueMem]
    m520 := by simp (config := { decide := true }) only [arm64_norm, hread 520#64 (by decide), nfsPrologueMem]
    m528 := by simp (config := { decide := true }) only [arm64_norm, hread 528#64 (by decide), nfsPrologueMem]
    m536 := by simp (config := { decide := true }) only [arm64_norm, hread 536#64 (by decide), nfsPrologueMem]
  }

/-! ## Prologue, Key Copy, and First XOR Chunk (`0x2b3b0 → 0x2b654`) -/

set_option maxHeartbeats 3200000 in
theorem nfs_seg0 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ : State}
    (hpc : s₀.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]"))
    (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 = shaStateBytes sha256IV)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hread_iv : s₀.mem.Readable (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (P b F alloc) s₀ (fun s' =>
      s'.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 476) ∧
      s'.status = .Running ∧
      NfsRegInv b s₀ s' ∧
      NfsMemInv b s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  intro key
  generalize hPost : (fun s' : State => _) = Post
  have hkey_len : key.length ≤ 64 := by
    dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hkey_len
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = false := nfs_ule_65_false hlen
  have hadrp1 : (((b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 40)) &&& 0xfffffffffffff000#64) + bv% (page% (ls_str% "kyber_pre_key_pu" + 256) - page% (ls_off% "<libsignal_protocol::protocol::SenderKeyMessage as core::convert::TryFrom<&[u8]>>::try_from" + 312))) + bv% ((ls_str% "kyber_pre_key_pu" + 256) % 4096) = b + bv% (ls_str% "kyber_pre_key_pu" + 256) :=
    nfs_adrp_x22_0x2b3d8_assoc hb
  have hadrp2 : ((b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 40)) &&& 0xfffffffffffff000#64) + bv% (ls_str% "kyber_pre_key_pu" + 256 - page% (ls_off% "<libsignal_protocol::protocol::SenderKeyMessage as core::convert::TryFrom<&[u8]>>::try_from" + 312)) = b + bv% (ls_str% "kyber_pre_key_pu" + 256) :=
    nfs_adrp_x22_0x2b3d8 hb
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 :=
    agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8))
      (nfsSp s₀ + 112#64) 64 := by
    simpa using AgreesOutside.writeBytes_self (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (List.replicate 64 0#8)
  have hread_key : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).readBytes
      (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · simp only [key, h0, Memory.readBytes]
    have hdisj_key_pro : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
    have hdisj_key_112 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
    rw [(agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hdisj_key_112]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdisj_key_pro]) (by omega)]
  have hrw_memcpy : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW
      (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat := by
    have hrw0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW (nfsSp s₀) 544 :=
      (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr
        ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
    exact hrw0.sub (by clear * - hlen; bv_omega)
  refine RunsTo.sess_memcpy_step
    (hrun := by simp only [arm64_norm, hstat])
    (hpc := rfl)
    (hx0 := by simp only [arm64_norm])
    (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm])
    (hlr := by simp only [arm64_norm]; rfl)
    (hmem := write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀))
    (hread := hread_key)
    (hrw := hrw_memcpy)
    ?_
  rw [writeBytes_key_over_zero64]
  have hA_k0 : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)) (nfsSp s₀ + 112#64) 64 := by
    have h := AgreesOutside.writeBytes_self (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key)
    rwa [hkb_len] at h
  have hRW_k0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_k0) _ _).mpr
      ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  set m_k0 := (nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)
  have hk0_64 : m_k0.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key :=
    Layout.readBytes_writeBytes_eq (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key) 64 hkb_len (by decide)
  have hk0_take32 : m_k0.readBytes (nfsSp s₀ + 112#64) 32 = (keyBlock key).take 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 0 32 (by omega)
    simpa using h
  have hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 32 32 (by omega)
    have hadd : (nfsSp s₀ + 112#64) + BitVec.ofNat 64 32 = nfsSp s₀ + 144#64 := by clear * -; bv_omega
    rw [hadd, List.take_of_length_le (by simp [hkb_len])] at h
    exact h
  have hA_432 : AgreesOutside m_k0 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self m_k0 (nfsSp s₀ + 432#64) 1#64
  have hf_k0 : Frame s₀.mem (m_k0.write64 (nfsSp s₀ + 432#64) 1#64)
      [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := by
    have hf0 : Frame s₀.mem s₀.mem [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := Frame.refl _ _
    have hf1 := Frame.of_agreesOutside_stack hf0 hA_pro (by decide)
    have hf2 := Frame.of_agreesOutside_stack hf1 hA_k0 (by decide)
    exact Frame.of_agreesOutside_stack hf2 hA_432 (by decide)
  have hM_432 : NfsMemInv b s₀ (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf_k0 _ _).mpr hrw_stack
    rw_out := (Frame.rw_iff hf_k0 _ _).mpr hrw_out
    readable_iv := (Frame.readable_iff hf_k0 _ _).mpr hread_iv
    iv_bytes := by
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8 (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdk0 : DisjointRegions (nfsSp s₀ + 112#64) 64 (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdpro : DisjointRegions (nfsSp s₀ + 464#64) 80 (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      rw [(agreesOutside_toFrame hA_432).readBytes_eq (by simp [hd432]) (by decide),
          (agreesOutside_toFrame hA_k0).readBytes_eq (by simp [hdk0]) (by decide),
          (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdpro]) (by decide), hiv]
    disj_iv_stack := hdisj_iv_stack
    disj_out_stack := hdisj_out_stack
    saved := nfsSavedStack_prologue_432 s₀ m_k0 hA_k0
    frame := hf_k0
  }
  have hM_final : NfsMemInv b s₀
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)) :=
    (hM_432.writeBytes_low 288#64 _ (by simp [slice16_length])).writeBytes_low
      304#64 _ (by simp [slice16_length])
  have h144_eq :
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)).readBytes (nfsSp s₀ + 144#64) 32 =
      (keyBlock key).drop 32 := by
    rw [readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        (agreesOutside_toFrame hA_432).readBytes_eq
          (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
        hk0_drop32]
  refine ⟨by simp only [arm64_norm], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm], hal_nfs, by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩,
    ?_,
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact h144_eq
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

theorem nfs_chunk1 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hpc : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 476))
    (hstat : s.status = .Running)
    (hR : NfsRegInv b s₀ s)
    (hM : NfsMemInv b s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (P b F alloc) s (fun s' =>
      s'.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 676) ∧
      s'.status = .Running ∧
      NfsRegInv b s₀ s' ∧
      NfsMemInv b s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x10 = (byteAt (keyBlock key) 16).zeroExtend 64 ∧
      s'.readReg64 .x11 = (byteAt (keyBlock key) 17).zeroExtend 64 ∧
      s'.readVReg128 2#5 = s.readVReg128 2#5 ∧
      s'.readVReg128 0#5 = s.readVReg128 0#5 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
          hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 288#64 (keyBlock key) 0 hs0
  obtain ⟨hb16, hb17, -⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 304#64 (keyBlock key) 16 hs16
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14 hb15 hb16 hb17
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm, hx8], by simp only [arm64_norm, hx0],
    by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx2],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_288_xor _ _ _ _ (keyBlock_length hlen)]
    exact hM.writeBytes_low 288#64 _ (by simp [slice16_length])
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_288_xor _ _ _ _ (keyBlock_length hlen)]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_288_xor _ _ _ _ (keyBlock_length hlen)]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs16

/-! ## Relocatable `[LibsignalPlacement]` Prologue and First Chunk (Block 114) -/

set_option maxHeartbeats 3200000 in
theorem nfs_seg0_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    {s₀ : State}
    (hpc : s₀.pc = (blkPl_114).base)
    (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable lsSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_114 H) s₀ (fun s' =>
      s'.pc = (blkPl_114).base + 476#64 ∧
      s'.status = .Running ∧
      NfsRegInv nfsPlacedFakeB s₀ s' ∧
      NfsMemInv nfsPlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  intro key
  generalize hPost : (fun s' : State => _) = Post
  have hkey_len : key.length ≤ 64 := by
    dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hkey_len
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = false := nfs_ule_65_false hlen
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  refine RunsTo.pairStep_114_0x28 (by simp only [arm64_norm, hpc]) (by simp only [arm64_norm, hstat]) ?_
  sess_step; sess_step; sess_step; sess_step; sess_step
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 :=
    agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8))
      (nfsSp s₀ + 112#64) 64 := by
    simpa using AgreesOutside.writeBytes_self (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (List.replicate 64 0#8)
  have hread_key : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).readBytes
      (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · simp only [key, h0, Memory.readBytes]
    have hdisj_key_pro : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
    have hdisj_key_112 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
    rw [(agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hdisj_key_112]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdisj_key_pro]) (by omega)]
  have hrw_memcpy : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW
      (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat := by
    have hrw0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW (nfsSp s₀) 544 :=
      (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr
        ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
    exact hrw0.sub (by clear * - hlen; bv_omega)
  refine RunsTo.placed_memcpy_step h_memcpy
    (hrun := by simp only [arm64_norm, hstat])
    (hpc := by simp only [arm64_norm, lsMemcpySym])
    (hx0 := by simp only [arm64_norm])
    (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm])
    (hlr := by simp only [arm64_norm]; rfl)
    (hmem := write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀))
    (hread := hread_key)
    (hrw := hrw_memcpy)
    ?_
  rw [writeBytes_key_over_zero64]
  have hA_k0 : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)) (nfsSp s₀ + 112#64) 64 := by
    have h := AgreesOutside.writeBytes_self (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key)
    rwa [hkb_len] at h
  have hRW_k0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_k0) _ _).mpr
      ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  set m_k0 := (nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)
  have hk0_64 : m_k0.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key :=
    Layout.readBytes_writeBytes_eq (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key) 64 hkb_len (by decide)
  have hk0_take32 : m_k0.readBytes (nfsSp s₀ + 112#64) 32 = (keyBlock key).take 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 0 32 (by omega)
    simpa using h
  have hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 32 32 (by omega)
    have hadd : (nfsSp s₀ + 112#64) + BitVec.ofNat 64 32 = nfsSp s₀ + 144#64 := by clear * -; bv_omega
    rw [hadd, List.take_of_length_le (by simp [hkb_len])] at h
    exact h
  have hA_432 : AgreesOutside m_k0 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self m_k0 (nfsSp s₀ + 432#64) 1#64
  have hf_k0 : Frame s₀.mem (m_k0.write64 (nfsSp s₀ + 432#64) 1#64)
      [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := by
    have hf0 : Frame s₀.mem s₀.mem [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := Frame.refl _ _
    have hf1 := Frame.of_agreesOutside_stack hf0 hA_pro (by decide)
    have hf2 := Frame.of_agreesOutside_stack hf1 hA_k0 (by decide)
    exact Frame.of_agreesOutside_stack hf2 hA_432 (by decide)
  have hM_432 : NfsMemInv nfsPlacedFakeB s₀ (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf_k0 _ _).mpr hrw_stack
    rw_out := (Frame.rw_iff hf_k0 _ _).mpr hrw_out
    readable_iv := by
      rw [nfsPlacedFakeB_add_iv]
      exact (Frame.readable_iff hf_k0 _ _).mpr hread_iv
    iv_bytes := by
      rw [nfsPlacedFakeB_add_iv]
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdk0 : DisjointRegions (nfsSp s₀ + 112#64) 64 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdpro : DisjointRegions (nfsSp s₀ + 464#64) 80 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      rw [(agreesOutside_toFrame hA_432).readBytes_eq (by simp [hd432]) (by decide),
          (agreesOutside_toFrame hA_k0).readBytes_eq (by simp [hdk0]) (by decide),
          (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdpro]) (by decide), hiv]
    disj_iv_stack := by rw [nfsPlacedFakeB_add_iv]; exact hdisj_iv_stack
    disj_out_stack := hdisj_out_stack
    saved := nfsSavedStack_prologue_432 s₀ m_k0 hA_k0
    frame := hf_k0
  }
  have hM_final : NfsMemInv nfsPlacedFakeB s₀
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)) :=
    (hM_432.writeBytes_low 288#64 _ (by simp [slice16_length])).writeBytes_low
      304#64 _ (by simp [slice16_length])
  have h144_eq :
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)).readBytes (nfsSp s₀ + 144#64) 32 =
      (keyBlock key).drop 32 := by
    rw [readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        (agreesOutside_toFrame hA_432).readBytes_eq
          (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
        hk0_drop32]
  refine ⟨by simp only [arm64_norm], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm], hal_nfs, by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩,
    ?_,
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact h144_eq
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

theorem nfs_chunk1_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hpc : s.pc = (blkPl_114).base + 476#64)
    (hstat : s.status = .Running)
    (hR : NfsRegInv nfsPlacedFakeB s₀ s)
    (hM : NfsMemInv nfsPlacedFakeB s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (lsProg_114 H) s (fun s' =>
      s'.pc = (blkPl_114).base + 676#64 ∧
      s'.status = .Running ∧
      NfsRegInv nfsPlacedFakeB s₀ s' ∧
      NfsMemInv nfsPlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x10 = (byteAt (keyBlock key) 16).zeroExtend 64 ∧
      s'.readReg64 .x11 = (byteAt (keyBlock key) 17).zeroExtend 64 ∧
      s'.readVReg128 2#5 = s.readVReg128 2#5 ∧
      s'.readVReg128 0#5 = s.readVReg128 0#5 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
          hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 288#64 (keyBlock key) 0 hs0
  obtain ⟨hb16, hb17, -⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 304#64 (keyBlock key) 16 hs16
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14 hb15 hb16 hb17
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm, hx8], by simp only [arm64_norm, hx0],
    by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx2],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_288_xor _ _ _ _ (keyBlock_length hlen)]
    exact hM.writeBytes_low 288#64 _ (by simp [slice16_length])
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_288_xor _ _ _ _ (keyBlock_length hlen)]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_288_xor _ _ _ _ (keyBlock_length hlen)]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs16

end CryptoVerification.LibsignalSession.CryptoHmacSha256
