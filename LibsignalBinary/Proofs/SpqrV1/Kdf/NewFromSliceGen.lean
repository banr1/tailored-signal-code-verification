/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGt64
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon

/-!
# Generalized `Hmac<Sha256>::new_from_slice [local#3]`

Finalization of `SHA-256(key)` on the `key.length > 64` branch (`0x6707c → 0x6717c`) and assembly
of the arbitrary-length (`key.length < 2 ^ 63`) contracts for `new_from_slice [local#3]`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.SpqrV1.Kdf.NewFromSlice3GenProof

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.CBC CryptoGames.LibsignalSession
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet (
  zeroExtend64_truncate32_ofNat64 zeroExtend64_ofNat8 xor_63_of_lt_64
  ult_7_of_lt_56 toLEBytes_8_read64 readBytes_56_eq_append_8 readBytes_56_of_buf_eq
  read32_words_at_104_of_shaStateBytes readBytes_write32_8_digestBytes
  toLEBytes_4_rev32)
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof
open ProofLib.ProgramReflection
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

@[local simp, local arm64_norm]
private theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
private theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
private theorem zero8_append_8 :
    (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl

@[local simp, local arm64_norm]
private theorem zero64_append_2 : (0#64 ++ 0#64 : BitVec 128) = 0#128 := rfl

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint Memory.read8_write8_base_zero_off Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint Memory.read8_write64_base_zero_off Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds Memory.read32_write8_base_off_disjoint Memory.read32_write8_base_zero_off
  Memory.read32_write8_base_off_zero Memory.read32_write64_base_off_disjoint Memory.read32_write64_base_zero_off
  Memory.read32_write64_base_off_zero Memory.read64_write8_base_off_disjoint Memory.read64_write8_base_zero_off
  Memory.read64_write8_base_off_zero Memory.read64_write32_base_off_disjoint Memory.read64_write32_base_zero_off
  Memory.read64_write32_base_off_zero Memory.read64_write64_base_off_disjoint Memory.read64_write64_base_zero_off
  Memory.read64_write64_base_off_zero

@[simp, arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [0x61c84 → 0x61d88]

/-! ## Sub-segment 0c (`0x6707c → 0x670e4`): One-Block vs Two-Block Finalization of `SHA-256(key)` -/

structure StateG3 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) (b_iv : BitVec 64 := b) : Prop where
  pc_eq : s.pc = b + 0x61cec#64
  common : NfsGt64Common b_iv s₀ s
  st_fin : ∃ st_f : ShaState,
    s.mem.readBytes (nfsSp s₀ + 352#64) 32 = shaStateBytes st_f ∧
    digestBytes st_f = sha256With F key

set_option hygiene false in
macro "nfs_seg0c_gt64_one_pre" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx20, hx21, hx23, hx24, hbuf, hst0_bytes⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hag_zero⟩
  set pfx := key.take (64 * (key.length / 64))
  set tail := key.drop (64 * (key.length / 64))
  set st0 := (chunks64 pfx).foldl F sha256IV
  have htail_len : key.length - 64 * (key.length / 64) = tail.length := by simp [tail]
  rw [htail_len] at hx23 hx24
  clear htail_len
  have hpfx_len : pfx.length = 64 * (key.length / 64) := by simp [pfx]; omega
  have hpfx_mod : pfx.length % 64 = 0 := by rw [hpfx_len]; omega
  have hpfx_div : pfx.length / 64 = key.length / 64 := by rw [hpfx_len]; omega
  have hkey_split : pfx ++ tail = key := List.take_append_drop (64 * (key.length / 64)) key
  have htail_lt : tail.length < 64 := by simp [tail]; omega
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_innerN_eq_lt64 (b := key.length / 64) htail_lt
  have hRW_zero : (nfsZeroMem s₀).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame (agreesOutside_nfsZeroMem s₀)) _ _).mpr
      ((Frame.rw_iff (agreesOutside_toFrame (agreesOutside_nfsPrologueMem s₀)) _ _).mpr hrw_stack)
  have hult_7 : (7#64).ult (BitVec.ofNat 64 (63 - tail.length)) = true := ult_7_of_lt_56 hlt56
  iterate 14 sess_step
  set w56 := rev64 (BitVec.ofNat 64 (8 * (64 * (key.length / 64) + tail.length)))
  set m_pre_c := ((((((((s.mem.write64 (nfsSp s₀ + 400#64) (s.mem.read64 (nfsSp s₀ + 288#64))).write64
    (nfsSp s₀ + 408#64) (s.mem.read64 (nfsSp s₀ + 296#64))).write64
    (nfsSp s₀ + 416#64) (s.mem.read64 (nfsSp s₀ + 304#64))).write64
    (nfsSp s₀ + 424#64) (s.mem.read64 (nfsSp s₀ + 312#64))).write64 (nfsSp s₀ + 344#64) w56).write64
    (nfsSp s₀ + 432#64) (s.mem.read64 (nfsSp s₀ + 320#64))).write64
    (nfsSp s₀ + 440#64) (s.mem.read64 (nfsSp s₀ + 328#64))).write64
    (nfsSp s₀ + 448#64) (s.mem.read64 (nfsSp s₀ + 336#64))).write64 (nfsSp s₀ + 456#64) w56
  have hag_pre_c : AgreesOutside s.mem m_pre_c (nfsSp s₀ + 344#64) 120 := by
    dsimp only [m_pre_c]; agrees_outside_writes
  have hag_zero_pre_c : AgreesOutside (nfsZeroMem s₀) m_pre_c (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 hag_zero hag_pre_c (by bv_omega)
  have hst0_pre_c : m_pre_c.readBytes (nfsSp s₀ + 352#64) 32 = shaStateBytes st0 := by
    set m_lo := ((((s.mem.write64 (nfsSp s₀ + 400#64) (s.mem.read64 (nfsSp s₀ + 288#64))).write64
      (nfsSp s₀ + 408#64) (s.mem.read64 (nfsSp s₀ + 296#64))).write64
      (nfsSp s₀ + 416#64) (s.mem.read64 (nfsSp s₀ + 304#64))).write64
      (nfsSp s₀ + 424#64) (s.mem.read64 (nfsSp s₀ + 312#64))).write64 (nfsSp s₀ + 344#64) w56
    have hag_hi : AgreesOutside m_lo m_pre_c (nfsSp s₀ + 432#64) 32 := by
      dsimp only [m_pre_c]; agrees_outside_writes
    have hag_344 : AgreesOutside
        ((((s.mem.write64 (nfsSp s₀ + 400#64) (s.mem.read64 (nfsSp s₀ + 288#64))).write64
          (nfsSp s₀ + 408#64) (s.mem.read64 (nfsSp s₀ + 296#64))).write64
          (nfsSp s₀ + 416#64) (s.mem.read64 (nfsSp s₀ + 304#64))).write64
          (nfsSp s₀ + 424#64) (s.mem.read64 (nfsSp s₀ + 312#64)))
        m_lo (nfsSp s₀ + 344#64) 8 := by dsimp only [m_lo]; agrees_outside_writes
    have hag_400 : AgreesOutside s.mem
        ((((s.mem.write64 (nfsSp s₀ + 400#64) (s.mem.read64 (nfsSp s₀ + 288#64))).write64
          (nfsSp s₀ + 408#64) (s.mem.read64 (nfsSp s₀ + 296#64))).write64
          (nfsSp s₀ + 416#64) (s.mem.read64 (nfsSp s₀ + 304#64))).write64
          (nfsSp s₀ + 424#64) (s.mem.read64 (nfsSp s₀ + 312#64)))
        (nfsSp s₀ + 400#64) 32 := by agrees_outside_writes
    have hd1 : DisjointRegions (nfsSp s₀ + 432#64) 32 (nfsSp s₀ + 352#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    have hd2 : DisjointRegions (nfsSp s₀ + 344#64) 8 (nfsSp s₀ + 352#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    have hd3 : DisjointRegions (nfsSp s₀ + 400#64) 32 (nfsSp s₀ + 352#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    rw [(agreesOutside_toFrame hag_hi).readBytes_eq (by simp [hd1]) (by decide),
        (agreesOutside_toFrame hag_344).readBytes_eq (by simp [hd2]) (by decide),
        (agreesOutside_toFrame hag_400).readBytes_eq (by simp [hd3]) (by decide), hst0_bytes]
  have hblk_pre_c : m_pre_c.readBytes (nfsSp s₀ + 400#64) 64 = sha256PadBlock1 (key.length / 64) tail := by
    dsimp only [m_pre_c]
    rw [readBytes_400_seg2, toLEBytes_read64_288_56 s.mem (nfsSp s₀),
        readBytes_56_of_buf_eq s.mem (nfsSp s₀ + 288#64) tail hbuf hlt56, toLEBytes_8_rev64]
    rfl
  have hrw_st : m_pre_c.RW (nfsSp s₀ + 352#64) 32 :=
    ((Frame.rw_iff (agreesOutside_toFrame hag_zero_pre_c) _ _).mpr hRW_zero).sub (by bv_omega)))

set_option hygiene false in
macro "nfs_seg0c_gt64_one_post" : tactic => `(tactic| (
  refine RunsTo.refl ?_
  set st_f := F st0 (sha256PadBlock1 (key.length / 64) tail)
  set m_end := m_pre_c.writeBytes (nfsSp s₀ + 352#64) (shaStateBytes st_f)
  have hag_c : AgreesOutside m_pre_c m_end (nfsSp s₀ + 352#64) 32 := by
    have hlen : (shaStateBytes st_f).length = 32 := shaStateBytes_length st_f
    rw [← hlen]
    exact ProofLib.agreesOutside_writeBytes m_pre_c (nfsSp s₀ + 352#64) (shaStateBytes st_f)
  have hag_end : AgreesOutside (nfsZeroMem s₀) m_end (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 hag_zero_pre_c hag_c (by bv_omega)
  refine
    { pc_eq := rfl
      common :=
        { status := by simp only [arm64_norm, hstat]
          sp_eq := by simp only [arm64_norm, hsp], sp_align := hal_nfs
          x29_eq := by simp only [arm64_norm, hx29], x19_eq := by simp only [arm64_norm, hx19]
          x22_eq := by simp only [arm64_norm, hx22], x25_eq := by simp only [arm64_norm, hx25]
          x26_eq := by simp only [arm64_norm, hx26], x27_eq := by simp only [arm64_norm, hx27]
          agrees_zero := by rw [State.mem_setPC, State.mem_setMem]; exact hag_end }
      st_fin := ⟨st_f,
        by
          rw [State.mem_setPC, State.mem_setMem]
          exact Run.Layout.readBytes_writeBytes_eq m_pre_c (nfsSp s₀ + 352#64)
            (shaStateBytes st_f) 32 (shaStateBytes_length st_f) (by decide),
        by
          have hsha := sha256With_pfx_one_block F pfx tail hpfx_mod hlt56
          rw [hkey_split, hpfx_div] at hsha; exact hsha.symm⟩ }))

set_option maxHeartbeats 1600000 in
theorem nfs_seg0c_gt64_one {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2 b F key s₀ s)
    (hkey_gt : 64 < key.length) (hkey_lt : key.length < 2 ^ 63)
    (hlt56 : (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (P b F alloc) s (StateG3 b F key s₀) := by
  nfs_seg0c_gt64_one_pre
  refine RunsTo.sess_compress256_step (m₀ := m_pre_c) (lr := b + 0x61cec#64)
    (st := st0) (blk := sha256PadBlock1 (key.length / 64) tail)
    (hrun := by simp only [arm64_norm, hstat]) (hpc := rfl)
    (hx0 := by simp only [arm64_norm]) (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm]) (hlr := by simp only [arm64_norm])
    (hmem := State.mem_setMem _ _) (hst := hst0_pre_c) (hblk := hblk_pre_c) (hrw := hrw_st) ?_
  nfs_seg0c_gt64_one_post

structure StateG2b (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) (b_iv : BitVec 64 := b) : Prop where
  pc_eq : s.pc = b + 0x61cac#64
  common : NfsGt64Common b_iv s₀ s
  x20_eq : s.readReg64 .x20 = nfsSp s₀ + 352#64
  x21_eq : s.readReg64 .x21 = BitVec.ofNat 64 (key.length / 64)
  x23_eq : s.readReg64 .x23 = BitVec.ofNat 64 (key.length - 64 * (key.length / 64))
  st1_bytes : s.mem.readBytes (nfsSp s₀ + 352#64) 32 =
    shaStateBytes (F ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV)
      (innerPadBlock1 (key.drop (64 * (key.length / 64)))))

structure StateG2c (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) (b_iv : BitVec 64 := b)
    (pc_target : BitVec 64 := b + bv% (ls_off% "sha2::sha256::compress256")) : Prop where
  pc_eq : s.pc = pc_target
  common : NfsGt64Common b_iv s₀ s
  x0_eq : s.readReg64 .x0 = nfsSp s₀ + 352#64
  x1_eq : s.readReg64 .x1 = nfsSp s₀ + 400#64
  x2_eq : s.readReg64 .x2 = 1#64
  lr_eq : s.readReg64 .lr = b + 0x61cec#64
  st1_bytes : s.mem.readBytes (nfsSp s₀ + 352#64) 32 =
    shaStateBytes (F ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV)
      (innerPadBlock1 (key.drop (64 * (key.length / 64)))))
  blk2_bytes : s.mem.readBytes (nfsSp s₀ + 400#64) 64 =
    innerPadBlock2 (key.length / 64) (key.drop (64 * (key.length / 64)))

set_option hygiene false in
macro "nfs_seg0c_gt64_two_a_pre" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx20, hx21, hx23, hx24, hbuf, hst0_bytes⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hag_zero⟩
  set pfx := key.take (64 * (key.length / 64))
  set tail := key.drop (64 * (key.length / 64))
  set st0 := (chunks64 pfx).foldl F sha256IV
  have htail_len : key.length - 64 * (key.length / 64) = tail.length := by simp [tail]
  rw [htail_len] at hx23 hx24
  clear htail_len
  have htail_lt : tail.length < 64 := by simp [tail]; omega
  have hRW_zero : (nfsZeroMem s₀).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame (agreesOutside_nfsZeroMem s₀)) _ _).mpr
      ((Frame.rw_iff (agreesOutside_toFrame (agreesOutside_nfsPrologueMem s₀)) _ _).mpr hrw_stack)
  have hge56 : 56 ≤ tail.length := by omega
  have hult_7 : (7#64).ult (BitVec.ofNat 64 (63 - tail.length)) = false :=
    ult_7_of_ge_56 hge56 htail_lt
  iterate 10 sess_step
  set m_pre_c1 := (((((((s.mem.write64 (nfsSp s₀ + 400#64) (s.mem.read64 (nfsSp s₀ + 288#64))).write64
    (nfsSp s₀ + 408#64) (s.mem.read64 (nfsSp s₀ + 296#64))).write64
    (nfsSp s₀ + 416#64) (s.mem.read64 (nfsSp s₀ + 304#64))).write64
    (nfsSp s₀ + 424#64) (s.mem.read64 (nfsSp s₀ + 312#64))).write64
    (nfsSp s₀ + 432#64) (s.mem.read64 (nfsSp s₀ + 320#64))).write64
    (nfsSp s₀ + 440#64) (s.mem.read64 (nfsSp s₀ + 328#64))).write64
    (nfsSp s₀ + 448#64) (s.mem.read64 (nfsSp s₀ + 336#64))).write64
    (nfsSp s₀ + 456#64) (s.mem.read64 (nfsSp s₀ + 344#64))
  have hag_pre_c1 : AgreesOutside s.mem m_pre_c1 (nfsSp s₀ + 400#64) 64 := by
    dsimp only [m_pre_c1]; agrees_outside_writes
  have hag_zero_pre_c1 : AgreesOutside (nfsZeroMem s₀) m_pre_c1 (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 hag_zero hag_pre_c1 (by bv_omega)
  have hst0_pre_c1 : m_pre_c1.readBytes (nfsSp s₀ + 352#64) 32 = shaStateBytes st0 := by
    have hd1 : DisjointRegions (nfsSp s₀ + 400#64) 64 (nfsSp s₀ + 352#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    rw [(agreesOutside_toFrame hag_pre_c1).readBytes_eq (by simp [hd1]) (by decide), hst0_bytes]
  have hblk_pre_c1 : m_pre_c1.readBytes (nfsSp s₀ + 400#64) 64 = innerPadBlock1 tail := by
    dsimp only [m_pre_c1]
    rw [readBytes_400_copy, toLEBytes_read64_288_64 s.mem (nfsSp s₀), hbuf]
  have hrw_st1 : m_pre_c1.RW (nfsSp s₀ + 352#64) 32 :=
    ((Frame.rw_iff (agreesOutside_toFrame hag_zero_pre_c1) _ _).mpr hRW_zero).sub (by bv_omega)))

set_option hygiene false in
macro "nfs_seg0c_gt64_two_a_post" : tactic => `(tactic| (
  refine RunsTo.refl ?_
  set st1 := F st0 (innerPadBlock1 tail)
  set m_post_c1 := m_pre_c1.writeBytes (nfsSp s₀ + 352#64) (shaStateBytes st1)
  have hag_c1 : AgreesOutside m_pre_c1 m_post_c1 (nfsSp s₀ + 352#64) 32 := by
    have hlen : (shaStateBytes st1).length = 32 := shaStateBytes_length st1
    rw [← hlen]
    exact ProofLib.agreesOutside_writeBytes m_pre_c1 (nfsSp s₀ + 352#64) (shaStateBytes st1)
  have hag_zero_post_c1 : AgreesOutside (nfsZeroMem s₀) m_post_c1 (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 hag_zero_pre_c1 hag_c1 (by bv_omega)
  have htail_len' : tail.length = key.length - 64 * (key.length / 64) := by simp [tail]
  refine
    { pc_eq := rfl
      common :=
        { status := by simp only [arm64_norm, hstat]
          sp_eq := by simp only [arm64_norm, hsp], sp_align := hal_nfs
          x29_eq := by simp only [arm64_norm, hx29], x19_eq := by simp only [arm64_norm, hx19]
          x22_eq := by simp only [arm64_norm, hx22], x25_eq := by simp only [arm64_norm, hx25]
          x26_eq := by simp only [arm64_norm, hx26], x27_eq := by simp only [arm64_norm, hx27]
          agrees_zero := by rw [State.mem_setPC, State.mem_setMem]; exact hag_zero_post_c1 }
      x20_eq := by simp only [arm64_norm, hx20], x21_eq := by simp only [arm64_norm, hx21]
      x23_eq := by simp only [arm64_norm, hx23, htail_len']
      st1_bytes := by
        rw [State.mem_setPC, State.mem_setMem]
        exact Run.Layout.readBytes_writeBytes_eq m_pre_c1 (nfsSp s₀ + 352#64)
          (shaStateBytes st1) 32 (shaStateBytes_length st1) (by decide) }))

set_option maxHeartbeats 1600000 in
theorem nfs_seg0c_gt64_two_a {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2 b F key s₀ s)
    (hnlt56 : ¬ (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (P b F alloc) s (StateG2b b F key s₀) := by
  nfs_seg0c_gt64_two_a_pre
  refine RunsTo.sess_compress256_step (m₀ := m_pre_c1) (lr := b + 0x61cac#64)
    (st := st0) (blk := innerPadBlock1 tail)
    (hrun := by simp only [arm64_norm, hstat]) (hpc := rfl)
    (hx0 := by simp only [arm64_norm]) (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm]) (hlr := by simp only [arm64_norm])
    (hmem := State.mem_setMem _ _) (hst := hst0_pre_c1) (hblk := hblk_pre_c1) (hrw := hrw_st1) ?_
  nfs_seg0c_gt64_two_a_post

set_option hygiene false in
macro "nfs_seg0c_gt64_two_b_body" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx20, hx21, hx23, hst1_bytes⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hag_zero⟩
  set pfx := key.take (64 * (key.length / 64))
  set tail := key.drop (64 * (key.length / 64))
  set st0 := (chunks64 pfx).foldl F sha256IV
  set st1 := F st0 (innerPadBlock1 tail)
  have htail_len : key.length - 64 * (key.length / 64) = tail.length := by simp [tail]
  rw [htail_len] at hx23
  clear htail_len
  have htail_lt : tail.length < 64 := by simp [tail]; omega
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_innerN_eq_lt64 (b := key.length / 64) htail_lt
  iterate 16 sess_step
  refine RunsTo.refl ?_
  set w56 := rev64 (BitVec.ofNat 64 (8 * (64 * (key.length / 64) + tail.length)))
  set m_z := ((((((s.mem.write64 (nfsSp s₀ + 336#64) 0#64).write64 (nfsSp s₀ + 288#64) 0#64).write64
    (nfsSp s₀ + 296#64) 0#64).write64 (nfsSp s₀ + 304#64) 0#64).write64
    (nfsSp s₀ + 312#64) 0#64).write64 (nfsSp s₀ + 320#64) 0#64).write64 (nfsSp s₀ + 328#64) 0#64
  set m_pre_c2 := ((((((((m_z.write64 (nfsSp s₀ + 400#64) 0#64).write64 (nfsSp s₀ + 408#64) 0#64).write64
    (nfsSp s₀ + 416#64) 0#64).write64 (nfsSp s₀ + 424#64) 0#64).write64
    (nfsSp s₀ + 344#64) w56).write64 (nfsSp s₀ + 432#64) 0#64).write64
    (nfsSp s₀ + 440#64) 0#64).write64 (nfsSp s₀ + 448#64) 0#64).write64 (nfsSp s₀ + 456#64) w56
  have hag_z : AgreesOutside s.mem m_z (nfsSp s₀ + 288#64) 56 := by
    dsimp only [m_z]; agrees_outside_writes
  have hag_c2_400 : AgreesOutside m_z m_pre_c2 (nfsSp s₀ + 344#64) 120 := by
    dsimp only [m_pre_c2]; agrees_outside_writes
  have hag_zero_z : AgreesOutside (nfsZeroMem s₀) m_z (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 hag_zero hag_z (by bv_omega)
  have hag_zero_pre_c2 : AgreesOutside (nfsZeroMem s₀) m_pre_c2 (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 hag_zero_z hag_c2_400 (by bv_omega)
  have hst1_pre_c2 : m_pre_c2.readBytes (nfsSp s₀ + 352#64) 32 = shaStateBytes st1 := by
    set m_lo2 := ((((m_z.write64 (nfsSp s₀ + 400#64) 0#64).write64 (nfsSp s₀ + 408#64) 0#64).write64
      (nfsSp s₀ + 416#64) 0#64).write64 (nfsSp s₀ + 424#64) 0#64).write64 (nfsSp s₀ + 344#64) w56
    have hag_hi2 : AgreesOutside m_lo2 m_pre_c2 (nfsSp s₀ + 432#64) 32 := by
      dsimp only [m_pre_c2]; agrees_outside_writes
    have hag_344_2 : AgreesOutside
        ((((m_z.write64 (nfsSp s₀ + 400#64) 0#64).write64 (nfsSp s₀ + 408#64) 0#64).write64
          (nfsSp s₀ + 416#64) 0#64).write64 (nfsSp s₀ + 424#64) 0#64)
        m_lo2 (nfsSp s₀ + 344#64) 8 := by dsimp only [m_lo2]; agrees_outside_writes
    have hag_400_2 : AgreesOutside m_z
        ((((m_z.write64 (nfsSp s₀ + 400#64) 0#64).write64 (nfsSp s₀ + 408#64) 0#64).write64
          (nfsSp s₀ + 416#64) 0#64).write64 (nfsSp s₀ + 424#64) 0#64)
        (nfsSp s₀ + 400#64) 32 := by agrees_outside_writes
    have hd1 : DisjointRegions (nfsSp s₀ + 432#64) 32 (nfsSp s₀ + 352#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    have hd2 : DisjointRegions (nfsSp s₀ + 344#64) 8 (nfsSp s₀ + 352#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    have hd3 : DisjointRegions (nfsSp s₀ + 400#64) 32 (nfsSp s₀ + 352#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    have hd4 : DisjointRegions (nfsSp s₀ + 288#64) 56 (nfsSp s₀ + 352#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    rw [(agreesOutside_toFrame hag_hi2).readBytes_eq (by simp [hd1]) (by decide),
        (agreesOutside_toFrame hag_344_2).readBytes_eq (by simp [hd2]) (by decide),
        (agreesOutside_toFrame hag_400_2).readBytes_eq (by simp [hd3]) (by decide),
        (agreesOutside_toFrame hag_z).readBytes_eq (by simp [hd4]) (by decide), hst1_bytes]
  have hblk_pre_c2 : m_pre_c2.readBytes (nfsSp s₀ + 400#64) 64 = innerPadBlock2 (key.length / 64) tail := by
    dsimp only [m_pre_c2]
    rw [readBytes_400_seg2, toLEBytes_8_zero_7, toLEBytes_8_rev64]; rfl
  refine
    { pc_eq := rfl
      common :=
        { status := by simp only [arm64_norm, hstat]
          sp_eq := by simp only [arm64_norm, hsp], sp_align := hal_nfs
          x29_eq := by simp only [arm64_norm, hx29], x19_eq := by simp only [arm64_norm, hx19]
          x22_eq := by simp only [arm64_norm, hx22], x25_eq := by simp only [arm64_norm, hx25]
          x26_eq := by simp only [arm64_norm, hx26], x27_eq := by simp only [arm64_norm, hx27]
          agrees_zero := by rw [State.mem_setMem]; exact hag_zero_pre_c2 }
      x0_eq := by simp only [arm64_norm, hx20], x1_eq := by simp only [arm64_norm]
      x2_eq := by simp only [arm64_norm], lr_eq := by simp only [arm64_norm]
      st1_bytes := by rw [State.mem_setMem]; exact hst1_pre_c2
      blk2_bytes := by rw [State.mem_setMem]; exact hblk_pre_c2 }))

set_option maxHeartbeats 1600000 in
theorem nfs_seg0c_gt64_two_b {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2b b F key s₀ s)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (P b F alloc) s (StateG2c b F key s₀) := by
  nfs_seg0c_gt64_two_b_body

set_option hygiene false in
macro "nfs_seg0c_gt64_two_c_pre" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hlr, hst1_bytes, hblk2_bytes⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hag_zero⟩
  set pfx := key.take (64 * (key.length / 64))
  set tail := key.drop (64 * (key.length / 64))
  set st0 := (chunks64 pfx).foldl F sha256IV
  set st1 := F st0 (innerPadBlock1 tail)
  have hpfx_len : pfx.length = 64 * (key.length / 64) := by simp [pfx]; omega
  have hpfx_mod : pfx.length % 64 = 0 := by rw [hpfx_len]; omega
  have hpfx_div : pfx.length / 64 = key.length / 64 := by rw [hpfx_len]; omega
  have hkey_split : pfx ++ tail = key := List.take_append_drop (64 * (key.length / 64)) key
  have htail_lt : tail.length < 64 := by simp [tail]; omega
  have hge56 : 56 ≤ tail.length := by omega
  have hrw_st2 : s.mem.RW (nfsSp s₀ + 352#64) 32 := hRW_s.sub (by bv_omega)))

set_option hygiene false in
macro "nfs_seg0c_gt64_two_c_post" : tactic => `(tactic| (
  refine RunsTo.refl ?_
  set st_f := F st1 (innerPadBlock2 (key.length / 64) tail)
  set m_end := s.mem.writeBytes (nfsSp s₀ + 352#64) (shaStateBytes st_f)
  have hag_c2 : AgreesOutside s.mem m_end (nfsSp s₀ + 352#64) 32 := by
    have hlen : (shaStateBytes st_f).length = 32 := shaStateBytes_length st_f
    rw [← hlen]
    exact ProofLib.agreesOutside_writeBytes s.mem (nfsSp s₀ + 352#64) (shaStateBytes st_f)
  have hag_end : AgreesOutside (nfsZeroMem s₀) m_end (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 hag_zero hag_c2 (by bv_omega)
  refine
    { pc_eq := rfl
      common :=
        { status := by simp only [arm64_norm, hstat]
          sp_eq := by simp only [arm64_norm, hsp], sp_align := hal_nfs
          x29_eq := by simp only [arm64_norm, hx29], x19_eq := by simp only [arm64_norm, hx19]
          x22_eq := by simp only [arm64_norm, hx22], x25_eq := by simp only [arm64_norm, hx25]
          x26_eq := by simp only [arm64_norm, hx26], x27_eq := by simp only [arm64_norm, hx27]
          agrees_zero := by rw [State.mem_setPC, State.mem_setMem]; exact hag_end }
      st_fin := ⟨st_f,
        by
          rw [State.mem_setPC, State.mem_setMem]
          exact Run.Layout.readBytes_writeBytes_eq s.mem (nfsSp s₀ + 352#64)
            (shaStateBytes st_f) 32 (shaStateBytes_length st_f) (by decide),
        by
          have hsha := sha256With_pfx_two_blocks F pfx tail hpfx_mod hge56 htail_lt
          rw [hkey_split, hpfx_div] at hsha; exact hsha.symm⟩ }))

theorem nfs_seg0c_gt64_two_c {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2c b F key s₀ s)
    (hnlt56 : ¬ (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (P b F alloc) s (StateG3 b F key s₀) := by
  nfs_seg0c_gt64_two_c_pre
  refine RunsTo.sess_compress256_step (m₀ := s.mem) (lr := b + 0x61cec#64)
    (st := st1) (blk := innerPadBlock2 (key.length / 64) tail)
    (hrun := hstat) (hpc := hpc) (hx0 := hx0) (hx1 := hx1) (hx2 := hx2) (hlr := hlr)
    (hmem := rfl) (hst := hst1_bytes) (hblk := hblk2_bytes) (hrw := hrw_st2) ?_
  nfs_seg0c_gt64_two_c_post

theorem nfs_seg0c_gt64_two {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2 b F key s₀ s)
    (hnlt56 : ¬ (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (P b F alloc) s (StateG3 b F key s₀) :=
  (nfs_seg0c_gt64_two_a hs hnlt56 hrw_stack).trans fun _ h2b =>
    (nfs_seg0c_gt64_two_b h2b hrw_stack).trans fun _ h2c =>
      nfs_seg0c_gt64_two_c h2c hnlt56 hrw_stack

theorem nfs_seg0c_gt64 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2 b F key s₀ s)
    (hkey_gt : 64 < key.length)
    (hkey_lt : key.length < 2 ^ 63)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (P b F alloc) s (StateG3 b F key s₀) := by
  by_cases hlt56 : (key.drop (64 * (key.length / 64))).length < 56
  · exact nfs_seg0c_gt64_one hs hkey_gt hkey_lt hlt56 hrw_stack
  · exact nfs_seg0c_gt64_two hs hlt56 hrw_stack

/-! ## Sub-segment 0d (`0x670e4 → 0x6717c`): Writing Digest to `sp + 112..144` and Joining `0x67158` -/

theorem nfsSavedStack_prologue_352 (s₀ : State) (m : Memory)
    (hA : AgreesOutside (nfsPrologueMem s₀) m (nfsSp s₀ + 112#64) 352) :
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

theorem agreesOutside_112_352_of_zero {s₀ : State} {m : Memory}
    (h : AgreesOutside (nfsZeroMem s₀) m (nfsSp s₀ + 176#64) 288) :
    AgreesOutside (nfsPrologueMem s₀) m (nfsSp s₀ + 112#64) 352 := by
  have h0 := agreesOutside_nfsZeroMem s₀
  have hx1 (x : BitVec 64) (hx : OutsideRegion (nfsSp s₀ + 112#64) 352 x) :
      OutsideRegion (nfsSp s₀ + 176#64) 288 x := by
    clear * - hx; simp only [OutsideRegion] at hx ⊢; bv_omega
  have hx0 (x : BitVec 64) (hx : OutsideRegion (nfsSp s₀ + 112#64) 352 x) :
      OutsideRegion (nfsSp s₀ + 112#64) 64 x := by
    clear * - hx; simp only [OutsideRegion] at hx ⊢; bv_omega
  exact ⟨fun x hx => (h.1 x (hx1 x hx)).trans (h0.1 x (hx0 x hx)),
    h.2.1.trans h0.2.1,
    fun x hx => (h.2.2.1 x (hx1 x hx)).trans (h0.2.2.1 x (hx0 x hx)),
    fun x hlf => h.2.2.2.1 x (h0.2.2.2.1 x hlf),
    fun x han => h.2.2.2.2 x (h0.2.2.2.2 x han)⟩

theorem agreesOutside_sub_112_352 {m₀ m₁ m₂ : Memory} {sp off : BitVec 64} {sz : ℕ}
    (h1 : AgreesOutside m₀ m₁ (sp + 112#64) 352)
    (h2 : AgreesOutside m₁ m₂ (sp + off) sz)
    (hoff : 112 ≤ off.toNat ∧ off.toNat + sz ≤ 464) :
    AgreesOutside m₀ m₂ (sp + 112#64) 352 := by
  have hx' (x : BitVec 64) (hx : OutsideRegion (sp + 112#64) 352 x) :
      OutsideRegion (sp + off) sz x := by
    rcases hoff with ⟨_, _⟩; simp only [OutsideRegion] at hx ⊢; bv_omega
  exact ⟨fun x hx => (h2.1 x (hx' x hx)).trans (h1.1 x hx),
    h2.2.1.trans h1.2.1,
    fun x hx => (h2.2.2.1 x (hx' x hx)).trans (h1.2.2.1 x hx),
    fun x hlf => h2.2.2.2.1 x (h1.2.2.2.1 x hlf),
    fun x han => h2.2.2.2.2 x (h1.2.2.2.2 x han)⟩

theorem readBytes_write32_8_112_eq_digest (m : Memory) (sp : BitVec 64) (st : ShaState) :
    ((((((((m.write32 (sp + 112#64) ((rev32_64 ((st.get 0).zeroExtend 64)).truncate 32)).write32
      (sp + 116#64) ((rev32_64 ((st.get 1).zeroExtend 64)).truncate 32)).write32
      (sp + 120#64) ((rev32_64 ((st.get 2).zeroExtend 64)).truncate 32)).write32
      (sp + 124#64) ((rev32_64 ((st.get 3).zeroExtend 64)).truncate 32)).write32
      (sp + 128#64) ((rev32_64 ((st.get 4).zeroExtend 64)).truncate 32)).write32
      (sp + 132#64) ((rev32_64 ((st.get 5).zeroExtend 64)).truncate 32)).write32
      (sp + 136#64) ((rev32_64 ((st.get 6).zeroExtend 64)).truncate 32)).write32
      (sp + 140#64) ((rev32_64 ((st.get 7).zeroExtend 64)).truncate 32)).readBytes (sp + 112#64) 32 =
    digestBytes st := by
  have h1 : sp + 116#64 = (sp + 112#64) + 4#64 := by bv_omega
  have h2 : sp + 120#64 = (sp + 112#64) + 8#64 := by bv_omega
  have h3 : sp + 124#64 = (sp + 112#64) + 12#64 := by bv_omega
  have h4 : sp + 128#64 = (sp + 112#64) + 16#64 := by bv_omega
  have h5 : sp + 132#64 = (sp + 112#64) + 20#64 := by bv_omega
  have h6 : sp + 136#64 = (sp + 112#64) + 24#64 := by bv_omega
  have h7 : sp + 140#64 = (sp + 112#64) + 28#64 := by bv_omega
  rw [h1, h2, h3, h4, h5, h6, h7]
  exact readBytes_write32_8_digestBytes m (sp + 112#64) st _ _ _ _ _ _ _ _
    (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
    (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)

theorem keyBlock_take32_of_len32 {k : List (BitVec 8)} (hk : k.length = 32) :
    (keyBlock k).take 32 = k := by
  unfold keyBlock
  rw [List.take_left' hk]

theorem keyBlock_drop32_of_len32 {k : List (BitVec 8)} (hk : k.length = 32) :
    (keyBlock k).drop 32 = List.replicate 32 0#8 := by
  unfold keyBlock
  rw [List.drop_left' hk, hk]
  rfl

structure StateG4 (b : BitVec 64) (k : List (BitVec 8)) (s₀ s : State)
    (b_iv : BitVec 64 := b) : Prop where
  pc_eq : s.pc = b + 0x61d60#64
  status : s.status = .Running
  sp_eq : s.sp = nfsSp s₀
  sp_align : (nfsSp s₀ &&& 0b1111#64) = 0#64
  x29_eq : s.readReg64 .x29 = nfsSp s₀ + 464#64
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x22_eq : s.readReg64 .x22 = b_iv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)
  x25_eq : s.readReg64 .x25 = s₀.readReg64 .x25
  x26_eq : s.readReg64 .x26 = s₀.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27
  agrees_pro_112 : AgreesOutside (nfsPrologueMem s₀) s.mem (nfsSp s₀ + 112#64) 352
  k_take32 : s.mem.readBytes (nfsSp s₀ + 112#64) 32 = (keyBlock k).take 32
  k_drop32 : s.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock k).drop 32

set_option hygiene false in
macro "nfs_seg0d1_gt64_body" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, ⟨st_f, hst_f, hdig_f⟩⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hag_zero⟩
  have h352 : nfsSp s₀ + 248#64 + 0x68#64 = nfsSp s₀ + 352#64 := by bv_omega
  have hst_words := read32_words_at_104_of_shaStateBytes s.mem (nfsSp s₀ + 248#64) st_f
    (by rw [h352]; exact hst_f)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hst_words
  rcases hst_words with ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩
  iterate 29 sess_step
  refine RunsTo.refl ?_
  set m_mid := (((((((((s.mem.write8 (nfsSp s₀ + 351#64) 0#8).write64 (nfsSp s₀ + 400#64) 0#64).write64
    (nfsSp s₀ + 408#64) 0#64).write64 (nfsSp s₀ + 416#64) 0#64).write64
    (nfsSp s₀ + 424#64) 0#64).write64 (nfsSp s₀ + 432#64) 0#64).write64
    (nfsSp s₀ + 440#64) 0#64).write64 (nfsSp s₀ + 448#64) 0#64).write64
    (nfsSp s₀ + 456#64) 0#64).write64 (nfsSp s₀ + 336#64) 0#64
  set m_mid2 := (((((((m_mid.write64 (nfsSp s₀ + 344#64) 0#64).write64 (nfsSp s₀ + 320#64) 0#64).write64
    (nfsSp s₀ + 328#64) 0#64).write64 (nfsSp s₀ + 304#64) 0#64).write64
    (nfsSp s₀ + 312#64) 0#64).write64 (nfsSp s₀ + 288#64) 0#64).write64 (nfsSp s₀ + 296#64) 0#64)
  have hag_mid1 : AgreesOutside s.mem m_mid (nfsSp s₀ + 320#64) 144 := by dsimp only [m_mid]; agrees_outside_writes
  have hag_mid2 : AgreesOutside m_mid m_mid2 (nfsSp s₀ + 288#64) 64 := by dsimp only [m_mid2]; agrees_outside_writes
  have hag_zero_mid2 : AgreesOutside (nfsZeroMem s₀) m_mid2 (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 (agreesOutside_sub_176_288 hag_zero hag_mid1 (by bv_omega)) hag_mid2 (by bv_omega)
  set m_end := ((((((((m_mid2.write32 (nfsSp s₀ + 112#64) ((rev32_64 ((st_f.get 0).zeroExtend 64)).truncate 32)).write32
    (nfsSp s₀ + 116#64) ((rev32_64 ((st_f.get 1).zeroExtend 64)).truncate 32)).write32
    (nfsSp s₀ + 120#64) ((rev32_64 ((st_f.get 2).zeroExtend 64)).truncate 32)).write32
    (nfsSp s₀ + 124#64) ((rev32_64 ((st_f.get 3).zeroExtend 64)).truncate 32)).write32
    (nfsSp s₀ + 128#64) ((rev32_64 ((st_f.get 4).zeroExtend 64)).truncate 32)).write32
    (nfsSp s₀ + 132#64) ((rev32_64 ((st_f.get 5).zeroExtend 64)).truncate 32)).write32
    (nfsSp s₀ + 136#64) ((rev32_64 ((st_f.get 6).zeroExtend 64)).truncate 32)).write32
    (nfsSp s₀ + 140#64) ((rev32_64 ((st_f.get 7).zeroExtend 64)).truncate 32))
  have hag_dig : AgreesOutside m_mid2 m_end (nfsSp s₀ + 112#64) 32 := by dsimp only [m_end]; agrees_outside_writes
  have hag_pro_end : AgreesOutside (nfsPrologueMem s₀) m_end (nfsSp s₀ + 112#64) 352 :=
    agreesOutside_sub_112_352 (agreesOutside_112_352_of_zero hag_zero_mid2) hag_dig (by decide)
  have hk_len : (sha256With F key).length = 32 := sha256With_length F key
  have h144_zero : (nfsZeroMem s₀).readBytes (nfsSp s₀ + 144#64) 32 = List.replicate 32 0#8 := by
    unfold nfsZeroMem
    have h64 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).readBytes
        (nfsSp s₀ + 112#64) 64 = List.replicate 64 0#8 :=
      Run.Layout.readBytes_writeBytes_eq _ _ _ 64 List.length_replicate (by decide)
    have hslice := readBytes_slice_of_readBytes_eq
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8))
      (nfsSp s₀ + 112#64) (List.replicate 64 0#8) (by rw [List.length_replicate]; exact h64) 32 32 (by decide)
    have hadd : (nfsSp s₀ + 112#64) + BitVec.ofNat 64 32 = nfsSp s₀ + 144#64 := by bv_omega
    rw [hadd] at hslice; simpa using hslice
  refine
    { pc_eq := by simp only [arm64_norm, hpc]
      status := by simp only [arm64_norm, hstat]
      sp_eq := by simp only [arm64_norm, hsp], sp_align := hal_nfs
      x29_eq := by simp only [arm64_norm, hx29], x19_eq := by simp only [arm64_norm, hx19]
      x22_eq := by simp only [arm64_norm, hx22], x25_eq := by simp only [arm64_norm, hx25]
      x26_eq := by simp only [arm64_norm, hx26], x27_eq := by simp only [arm64_norm, hx27]
      agrees_pro_112 := by rw [State.mem_setMem]; exact hag_pro_end
      k_take32 := by
        rw [State.mem_setMem]
        exact (readBytes_write32_8_112_eq_digest m_mid2 (nfsSp s₀) st_f).trans
          (hdig_f.trans (keyBlock_take32_of_len32 hk_len).symm)
      k_drop32 := by
        rw [State.mem_setMem]
        have hd1 : DisjointRegions (nfsSp s₀ + 112#64) 32 (nfsSp s₀ + 144#64) 32 := by
          clear * -; simp only [DisjointRegions]; bv_omega
        have hd2 : DisjointRegions (nfsSp s₀ + 176#64) 288 (nfsSp s₀ + 144#64) 32 := by
          clear * -; simp only [DisjointRegions]; bv_omega
        rw [(agreesOutside_toFrame hag_dig).readBytes_eq (by simp [hd1]) (by decide),
            (agreesOutside_toFrame hag_zero_mid2).readBytes_eq (by simp [hd2]) (by decide),
            h144_zero, keyBlock_drop32_of_len32 hk_len] }))

set_option maxHeartbeats 1600000 in
theorem nfs_seg0d1_gt64 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG3 b F key s₀ s)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (P b F alloc) s (StateG4 b (sha256With F key) s₀) := by
  nfs_seg0d1_gt64_body

set_option hygiene false in
macro "nfs_seg0d2_gt64_body " bIv:term:max : tactic => `(tactic| (
  generalize hPost : (fun s' : State => _) = Post
  rcases hs with ⟨hpc, hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hA_k0, hk0_take32, hk0_drop32⟩
  have hkb_len : (keyBlock k).length = 64 := keyBlock_length hk_len
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 := agreesOutside_nfsPrologueMem s₀
  have hRW_k0 : s.mem.RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_k0) _ _).mpr ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
  iterate 9 sess_step
  subst hPost
  refine RunsTo.refl ?_
  set m_k0 := s.mem
  have hA_432 : AgreesOutside m_k0 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self m_k0 (nfsSp s₀ + 432#64) 1#64
  have hf_k0 : Frame s₀.mem (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := by
    have hf0 : Frame s₀.mem s₀.mem [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := Frame.refl _ _
    have hf1 := Frame.of_agreesOutside_stack hf0 hA_pro (by decide)
    have hf2 := Frame.of_agreesOutside_stack hf1 hA_k0 (by decide)
    exact Frame.of_agreesOutside_stack hf2 hA_432 (by decide)
  have hM_432 : NfsMemInv3 $bIv s₀ (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf_k0 _ _).mpr hrw_stack
    rw_out := (Frame.rw_iff hf_k0 _ _).mpr hrw_out
    readable_iv := (Frame.readable_iff hf_k0 _ _).mpr hread_iv
    iv_bytes := by
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8 ($bIv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdk0 : DisjointRegions (nfsSp s₀ + 112#64) 352 ($bIv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdpro : DisjointRegions (nfsSp s₀ + 464#64) 80 ($bIv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      rw [(agreesOutside_toFrame hA_432).readBytes_eq (by simp only [List.mem_singleton, forall_eq]; exact hd432) (by decide),
          (agreesOutside_toFrame hA_k0).readBytes_eq (by simp only [List.mem_singleton, forall_eq]; exact hdk0) (by decide),
          (agreesOutside_toFrame hA_pro).readBytes_eq (by simp only [List.mem_singleton, forall_eq]; exact hdpro) (by decide), hiv]
    disj_iv_stack := hdisj_iv_stack, disj_out_stack := hdisj_out_stack
    saved := nfsSavedStack_prologue_352 s₀ m_k0 hA_k0, frame := hf_k0 }
  have hM_final :=
    (hM_432.writeBytes_low 288#64 (slice16 (keyBlock k) 0) (by simp [slice16_length])).writeBytes_low
      304#64 (slice16 (keyBlock k) 16) (by simp [slice16_length])
  have h144_eq :
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock k) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock k) 16)).readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock k).drop 32 := by
    rw [readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        (agreesOutside_toFrame hA_432).readBytes_eq
          (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
        hk0_drop32]
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hal_nfs, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_, ?_⟩
  · rw [State.mem_setMem, write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock k) hkb_len hk0_take32]; exact hM_final
  · rw [State.mem_setMem, write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock k) hkb_len hk0_take32]; exact h144_eq
  · rw [State.mem_setMem, write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock k) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · rw [State.mem_setMem, write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock k) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)))

set_option maxHeartbeats 1600000 in
theorem nfs_seg0d2_gt64 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {k : List (BitVec 8)} {s₀ s : State}
    (hs : StateG4 b k s₀ s) (hk_len : k.length ≤ 64)
    (hiv : s₀.mem.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544) :
    RunsTo (P b F alloc) s (fun s' =>
      s'.pc = b + 0x61d84#64 ∧ s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧ NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧ s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock k).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock k) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock k) 16) := by
  nfs_seg0d2_gt64_body b

/-! ## Full `> 64` Execution (`nfs_gt64_run`) and Generalized `new_from_slice3_gen_runsTo_ext` -/

theorem nfs_chunks_1_to_4_of_G4 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {k : List (BitVec 8)} {s₀ s : State}
    (hs : StateG4 b k s₀ s) (hk_le : k.length ≤ 64)
    (hiv : s₀.mem.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hread_iv : s₀.mem.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    RunsTo (P b F alloc) s (fun s' =>
      s'.pc = b + 0x62094#64 ∧ s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧ NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧ s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock k).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 = (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  refine (nfs_seg0d2_gt64 hs hk_le hiv hread_iv hdisj_iv_stack hrw_out hrw_stack hdisj_out_stack).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1, hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩
  refine (NewFromSlice3Proof.nfs_chunk1 hk_le hpc1 hstat1 hR1 hM1 hx8_1 hx0_1 hx1_1 hx2_1 hs0_1 hs16_1).trans fun s2 h2 => ?_
  rcases h2 with ⟨hpc2, hstat2, hR2, hM2, hx8_2, hx0_2, hx1_2, hx2_2, hx10_2, hx11_2, hq2_2, hq0_2, hs0_2, hs16_2⟩
  refine (NewFromSlice3Proof.nfs_chunk2 hk_le hal hpc2 hstat2 hR2 hM2 hx8_2 hx0_2 hx1_2 hx2_2 hx10_2 hx11_2
    (hq2_2.trans hq2_1) (hq0_2.trans hq0_1) hk0_1 hs0_2 hs16_2).trans fun s3 h3 => ?_
  rcases h3 with ⟨hpc3, hstat3, hR3, hM3, hx8_3, hx0_3, hx1_3, hx2_3, hx11_3, hx9_3, hs0_3, hs16_3, hs32_3, hs48_3⟩
  refine (NewFromSlice3Proof.nfs_chunk3 hk_le hpc3 hstat3 hR3 hM3 hx8_3 hx0_3 hx1_3 hx2_3 hx11_3 hx9_3
    hs0_3 hs16_3 hs32_3 hs48_3).trans fun s4 h4 => ?_
  rcases h4 with ⟨hpc4, hstat4, hR4, hM4, hx8_4, hx0_4, hx1_4, hx2_4, hx9_4, hx10_4, hs0_4, hs16_4, hs32_4, hs48_4⟩
  exact NewFromSlice3Proof.nfs_chunk4 hk_le hal hb hpc4 hstat4 hR4 hM4 hx8_4 hx0_4 hx1_4 hx2_4 hx9_4 hx10_4
    hs0_4 hs16_4 hs32_4 hs48_4

theorem nfs_first_half_gt64 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ : State}
    (hpc : s₀.pc = b + 0x61ba8#64) (hstat : s₀.status = .Running)
    (hgt : 64 < (s₀.readReg64 .x2).toNat) (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hread_iv : s₀.mem.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (P b F alloc) s₀ (fun s' =>
      s'.pc = b + 0x62094#64 ∧ s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧ NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧ s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock (sha256With F key)).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 = (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  intro key
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_gt : 64 < key.length := by omega
  have hkey_lt : key.length < 2 ^ 63 := by omega
  have hk_le : (sha256With F key).length ≤ 64 := by have : (sha256With F key).length = 32 := sha256With_length F key; omega
  refine (nfs_seg0_pro_gt64 hpc hstat hgt hb hrw_stack hal).trans fun s_g0 hg0 => ?_
  refine (nfs_seg0a_gt64 hg0 hgt hlt hiv hread_iv hdisj_iv_stack hrw_stack hdisj_key_stack).trans fun s_g1 hg1 => ?_
  refine (nfs_seg0b_gt64 hg1 hkey_gt hkey_lt hrw_stack).trans fun s_g2 hg2 => ?_
  refine (nfs_seg0c_gt64 hg2 hkey_gt hkey_lt hrw_stack).trans fun s_g3 hg3 => ?_
  refine (nfs_seg0d1_gt64 hg3 hrw_stack).trans fun s_g4 hg4 => ?_
  exact nfs_chunks_1_to_4_of_G4 hg4 hk_le hiv hb hread_iv hdisj_iv_stack hrw_out hrw_stack hdisj_out_stack hal

theorem nfs_second_half_of_mid {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {k : List (BitVec 8)} {s₀ s1 : State}
    (hk_le : k.length ≤ 64) (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (h1 : s1.pc = b + 0x62094#64 ∧ s1.status = .Running ∧
      NfsRegInv3 b s₀ s1 ∧ NfsMemInv3 b s₀ s1.mem ∧
      s1.readReg64 .x0 = nfsSp s₀ + 400#64 ∧ s1.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s1.readReg64 .x2 = 1#64 ∧
      s1.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s1.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock k).map (· ^^^ 0x36#8) ∧
      s1.mem.readBytes (nfsSp s₀) 32 = (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (P b F alloc) s1 (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F k [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx0_1, hx1_1, hx2_1, hist1, hblk1, hivsw1⟩
  exact NewFromSlice3Proof.nfs_second_half hk_le hal hpc1 hstat1 hR1 hM1 hx0_1 hx1_1 hx2_1 hist1 hblk1 hivsw1

theorem new_from_slice3_gt64_run {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ : State}
    (hpc : s₀.pc = b + 0x61ba8#64) (hstat : s₀.status = .Running)
    (hgt : 64 < (s₀.readReg64 .x2).toNat) (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hread_iv : s₀.mem.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (P b F alloc) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F (sha256With F key) [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  intro key
  have hk_le : (sha256With F key).length ≤ 64 := by have : (sha256With F key).length = 32 := sha256With_length F key; omega
  refine (nfs_first_half_gt64 hpc hstat hgt hlt hiv hb hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hdisj_key_stack hal).trans fun s1 h1 => ?_
  exact nfs_second_half_of_mid hk_le hal h1

theorem new_from_slice3_gen_run {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ : State}
    (hpc : s₀.pc = b + 0x61ba8#64) (hstat : s₀.status = .Running)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hread_iv : s₀.mem.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (P b F alloc) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F (effectiveHmacKey F key) [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  intro key
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  by_cases hle : (s₀.readReg64 .x2).toNat ≤ 64
  · have heff : effectiveHmacKey F key = key := effectiveHmacKey_of_le F (by omega)
    rw [heff]
    exact NewFromSlice3Proof.new_from_slice3_run hpc hstat hle hiv hb hread_iv hdisj_iv_stack hrw_out hrw_stack
      hdisj_out_stack hdisj_key_stack hal
  · have hgt : 64 < (s₀.readReg64 .x2).toNat := by omega
    have hgt' : 64 < key.length := by omega
    have heff : effectiveHmacKey F key = sha256With F key := by
      unfold effectiveHmacKey
      simp [hgt']
    rw [heff]
    have hdisj_k : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544 :=
      hdisj_key_stack.resolve_left (by omega)
    exact new_from_slice3_gt64_run hpc hstat hgt hlt hiv hb hread_iv hdisj_iv_stack hrw_out hrw_stack
      hdisj_out_stack hdisj_k hal

/-! ## Placed (`[LibsignalPlacement]`) Generalized `new_from_slice [local#3]` (Block `402`) -/

set_option maxHeartbeats 1600000 in
theorem nfs_seg0c_gt64_one_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2 nfs3CodeFakeB F key s₀ s nfs3PlacedFakeB)
    (hkey_gt : 64 < key.length) (hkey_lt : key.length < 2 ^ 63)
    (hlt56 : (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (lsProg_402 H) s (StateG3 nfs3CodeFakeB F key s₀ · nfs3PlacedFakeB) := by
  nfs_seg0c_gt64_one_pre
  refine RunsTo.placed_compress256_step h_compress (m₀ := m_pre_c) (lr := nfs3CodeFakeB + 0x61cec#64)
    (st := st0) (blk := sha256PadBlock1 (key.length / 64) tail)
    (hrun := by simp only [arm64_norm, hstat]) (hpc := rfl)
    (hx0 := by simp only [arm64_norm]) (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm]) (hlr := by simp only [arm64_norm])
    (hmem := State.mem_setMem _ _) (hst := hst0_pre_c) (hblk := hblk_pre_c) (hrw := hrw_st) ?_
  nfs_seg0c_gt64_one_post

set_option maxHeartbeats 1600000 in
theorem nfs_seg0c_gt64_two_a_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2 nfs3CodeFakeB F key s₀ s nfs3PlacedFakeB)
    (hnlt56 : ¬ (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (lsProg_402 H) s (StateG2b nfs3CodeFakeB F key s₀ · nfs3PlacedFakeB) := by
  nfs_seg0c_gt64_two_a_pre
  refine RunsTo.placed_compress256_step h_compress (m₀ := m_pre_c1) (lr := nfs3CodeFakeB + 0x61cac#64)
    (st := st0) (blk := innerPadBlock1 tail)
    (hrun := by simp only [arm64_norm, hstat]) (hpc := rfl)
    (hx0 := by simp only [arm64_norm]) (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm]) (hlr := by simp only [arm64_norm])
    (hmem := State.mem_setMem _ _) (hst := hst0_pre_c1) (hblk := hblk_pre_c1) (hrw := hrw_st1) ?_
  nfs_seg0c_gt64_two_a_post

set_option maxHeartbeats 1600000 in
theorem nfs_seg0c_gt64_two_b_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2b nfs3CodeFakeB F key s₀ s nfs3PlacedFakeB)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (lsProg_402 H) s (StateG2c nfs3CodeFakeB F key s₀ · nfs3PlacedFakeB (lsmpl.ρ lsCompress256Sym)) := by
  nfs_seg0c_gt64_two_b_body

theorem nfs_seg0c_gt64_two_c_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2c nfs3CodeFakeB F key s₀ s nfs3PlacedFakeB (lsmpl.ρ lsCompress256Sym))
    (hnlt56 : ¬ (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (lsProg_402 H) s (StateG3 nfs3CodeFakeB F key s₀ · nfs3PlacedFakeB) := by
  nfs_seg0c_gt64_two_c_pre
  refine RunsTo.placed_compress256_step h_compress (m₀ := s.mem) (lr := nfs3CodeFakeB + 0x61cec#64)
    (st := st1) (blk := innerPadBlock2 (key.length / 64) tail)
    (hrun := hstat) (hpc := hpc) (hx0 := hx0) (hx1 := hx1) (hx2 := hx2) (hlr := hlr)
    (hmem := rfl) (hst := hst1_bytes) (hblk := hblk2_bytes) (hrw := hrw_st2) ?_
  nfs_seg0c_gt64_two_c_post

theorem nfs_seg0c_gt64_two_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2 nfs3CodeFakeB F key s₀ s nfs3PlacedFakeB)
    (hnlt56 : ¬ (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (lsProg_402 H) s (StateG3 nfs3CodeFakeB F key s₀ · nfs3PlacedFakeB) :=
  (nfs_seg0c_gt64_two_a_placed h_compress hs hnlt56 hrw_stack).trans fun _ h2b =>
    (nfs_seg0c_gt64_two_b_placed h2b hrw_stack).trans fun _ h2c =>
      nfs_seg0c_gt64_two_c_placed h_compress h2c hnlt56 hrw_stack

theorem nfs_seg0c_gt64_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2 nfs3CodeFakeB F key s₀ s nfs3PlacedFakeB)
    (hkey_gt : 64 < key.length) (hkey_lt : key.length < 2 ^ 63)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (lsProg_402 H) s (StateG3 nfs3CodeFakeB F key s₀ · nfs3PlacedFakeB) := by
  by_cases hlt56 : (key.drop (64 * (key.length / 64))).length < 56
  · exact nfs_seg0c_gt64_one_placed h_compress hs hkey_gt hkey_lt hlt56 hrw_stack
  · exact nfs_seg0c_gt64_two_placed h_compress hs hlt56 hrw_stack

set_option maxHeartbeats 1600000 in
theorem nfs_seg0d1_gt64_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG3 nfs3CodeFakeB F key s₀ s nfs3PlacedFakeB)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (lsProg_402 H) s (StateG4 nfs3CodeFakeB (sha256With F key) s₀ · nfs3PlacedFakeB) := by
  nfs_seg0d1_gt64_body

set_option maxHeartbeats 1600000 in
theorem nfs_seg0d2_gt64_placed [LibsignalPlacement]
    {H : LibsignalHooks} {k : List (BitVec 8)} {s₀ s : State}
    (hs : StateG4 nfs3CodeFakeB k s₀ s nfs3PlacedFakeB) (hk_len : k.length ≤ 64)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544) :
    RunsTo (lsProg_402 H) s (fun s' =>
      s'.pc = (blkPl_402).base + 476#64 ∧ s'.status = .Running ∧
      NfsRegInv3 nfs3PlacedFakeB s₀ s' ∧ NfsMemInv3 nfs3PlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧ s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock k).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock k) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock k) 16) := by
  rw [← nfs3PlacedFakeB_add_iv] at hiv hread_iv hdisj_iv_stack
  nfs_seg0d2_gt64_body nfs3PlacedFakeB

theorem nfs_chunks_1_to_4_of_G4_placed [LibsignalPlacement]
    {H : LibsignalHooks} {k : List (BitVec 8)} {s₀ s : State}
    (hs : StateG4 nfs3CodeFakeB k s₀ s nfs3PlacedFakeB) (hk_le : k.length ≤ 64)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    RunsTo (lsProg_402 H) s (fun s' =>
      s'.pc = (blkPl_402).base + 1260#64 ∧ s'.status = .Running ∧
      NfsRegInv3 nfs3PlacedFakeB s₀ s' ∧ NfsMemInv3 nfs3PlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧ s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock k).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 = (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  refine (nfs_seg0d2_gt64_placed hs hk_le hiv hread_iv hdisj_iv_stack hrw_out hrw_stack hdisj_out_stack).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1, hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩
  refine (NewFromSlice3Proof.nfs_chunk1_placed hk_le hpc1 hstat1 hR1 hM1 hx8_1 hx0_1 hx1_1 hx2_1 hs0_1 hs16_1).trans fun s2 h2 => ?_
  rcases h2 with ⟨hpc2, hstat2, hR2, hM2, hx8_2, hx0_2, hx1_2, hx2_2, hx10_2, hx11_2, hq2_2, hq0_2, hs0_2, hs16_2⟩
  refine (NewFromSlice3Proof.nfs_chunk2_placed hk_le hal hpc2 hstat2 hR2 hM2 hx8_2 hx0_2 hx1_2 hx2_2 hx10_2 hx11_2
    (hq2_2.trans hq2_1) (hq0_2.trans hq0_1) hk0_1 hs0_2 hs16_2).trans fun s3 h3 => ?_
  rcases h3 with ⟨hpc3, hstat3, hR3, hM3, hx8_3, hx0_3, hx1_3, hx2_3, hx11_3, hx9_3, hs0_3, hs16_3, hs32_3, hs48_3⟩
  refine (NewFromSlice3Proof.nfs_chunk3_placed hk_le hpc3 hstat3 hR3 hM3 hx8_3 hx0_3 hx1_3 hx2_3 hx11_3 hx9_3
    hs0_3 hs16_3 hs32_3 hs48_3).trans fun s4 h4 => ?_
  rcases h4 with ⟨hpc4, hstat4, hR4, hM4, hx8_4, hx0_4, hx1_4, hx2_4, hx9_4, hx10_4, hs0_4, hs16_4, hs32_4, hs48_4⟩
  exact NewFromSlice3Proof.nfs_chunk4_placed hk_le hal hpc4 hstat4 hR4 hM4 hx8_4 hx0_4 hx1_4 hx2_4 hx9_4 hx10_4
    hs0_4 hs16_4 hs32_4 hs48_4

theorem nfs_first_half_gt64_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hgt : 64 < (s₀.readReg64 .x2).toNat) (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = (blkPl_402).base + 1260#64 ∧ s'.status = .Running ∧
      NfsRegInv3 nfs3PlacedFakeB s₀ s' ∧ NfsMemInv3 nfs3PlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧ s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock (sha256With F key)).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 = (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  intro key
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_gt : 64 < key.length := by omega
  have hkey_lt : key.length < 2 ^ 63 := by omega
  have hk_le : (sha256With F key).length ≤ 64 := by have : (sha256With F key).length = 32 := sha256With_length F key; omega
  have hiv' : s₀.mem.readBytes (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV := by rwa [nfs3PlacedFakeB_add_iv]
  have hread_iv' : s₀.mem.Readable (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by rwa [nfs3PlacedFakeB_add_iv]
  have hdisj_iv_stack' : DisjointRegions (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544 := by rwa [nfs3PlacedFakeB_add_iv]
  refine (nfs_seg0_pro_gt64_placed hpc hstat hgt hrw_stack hal).trans fun s_g0 hg0 => ?_
  refine (nfs_seg0a_gt64_placed h_memcpy h_compress hg0 hgt hlt hiv' hread_iv' hdisj_iv_stack' hrw_stack hdisj_key_stack).trans fun s_g1 hg1 => ?_
  refine (nfs_seg0b_gt64_placed h_memset hg1 hkey_gt hkey_lt hrw_stack).trans fun s_g2 hg2 => ?_
  refine (nfs_seg0c_gt64_placed h_compress hg2 hkey_gt hkey_lt hrw_stack).trans fun s_g3 hg3 => ?_
  refine (nfs_seg0d1_gt64_placed hg3 hrw_stack).trans fun s_g4 hg4 => ?_
  exact nfs_chunks_1_to_4_of_G4_placed hg4 hk_le hiv hread_iv hdisj_iv_stack hrw_out hrw_stack hdisj_out_stack hal

theorem new_from_slice3_gt64_placed_run [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hgt : 64 < (s₀.readReg64 .x2).toNat) (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F (sha256With F key) [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  intro key
  have hk_le : (sha256With F key).length ≤ 64 := by have : (sha256With F key).length = 32 := sha256With_length F key; omega
  refine (nfs_first_half_gt64_placed h_memcpy h_memset h_compress hpc hstat hgt hlt hiv hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hdisj_key_stack hal).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx0_1, hx1_1, hx2_1, hist1, hblk1, hivsw1⟩
  exact NewFromSlice3Proof.nfs_second_half_placed h_compress hk_le hal hpc1 hstat1 hR1 hM1 hx0_1 hx1_1 hx2_1 hist1 hblk1 hivsw1

theorem new_from_slice3_gen_placed_run [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F (effectiveHmacKey F key) [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  intro key
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  by_cases hle : (s₀.readReg64 .x2).toNat ≤ 64
  · have heff : effectiveHmacKey F key = key := effectiveHmacKey_of_le F (by omega)
    rw [heff]
    exact NewFromSlice3Proof.new_from_slice3_placed_run h_memcpy h_compress hpc hstat hle hiv hread_iv hdisj_iv_stack
      hrw_out hrw_stack hdisj_out_stack hdisj_key_stack hal
  · have hgt : 64 < (s₀.readReg64 .x2).toNat := by omega
    have hgt' : 64 < key.length := by omega
    have heff : effectiveHmacKey F key = sha256With F key := by
      unfold effectiveHmacKey
      simp [hgt']
    rw [heff]
    have hdisj_k : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544 :=
      hdisj_key_stack.resolve_left (by omega)
    exact new_from_slice3_gt64_placed_run h_memcpy h_memset h_compress hpc hstat hgt hlt hiv hread_iv hdisj_iv_stack
      hrw_out hrw_stack hdisj_out_stack hdisj_k hal

end CryptoVerification.SpqrV1.Kdf.NewFromSlice3GenProof

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer

theorem new_from_slice3_gen_runsTo_ext {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc ext : String → Option (State → State)}
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F alloc) n = some f →
      Rust.withPanics ext n = some f) :
    Nfs3GenRunsToExt b F ext := by
  intro s₀ hpc hstat hlt hiv hb hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hdisj_key_stack _hdisj_key_out hal hL2
  have hL1 : (LibsignalSession.CryptoHmacSha256.P b F alloc).CodeLoaded s₀.mem := by
    rw [Program.codeLoaded_iff] at hL2 ⊢
    dsimp only [LibsignalSession.CryptoHmacSha256.P, tripleRatchetProgAtExt, Program.rebase] at hL2 ⊢
    exact hL2
  obtain ⟨s', hs, htr, hvregs, hpost, hL1'⟩ :=
    NewFromSlice3GenProof.new_from_slice3_gen_run (F := F) (alloc := alloc)
      hpc hstat hlt hiv hb hread_iv hdisj_iv_stack hrw_out hrw_stack
      hdisj_out_stack hdisj_key_stack hal hL1
  have hL2' : (tripleRatchetProgAtExt b ext).CodeLoaded s'.mem := by
    rw [Program.codeLoaded_iff] at hL1' ⊢
    dsimp only [LibsignalSession.CryptoHmacSha256.P, tripleRatchetProgAtExt, Program.rebase] at hL1' ⊢
    exact hL1'
  have hnh : s'.status ≠ .Halted := by rw [hpost.2.1]; decide
  exact ⟨s', steps_mono libsignalSessionCode_stubs_offsets_fresh libsignalSessionCode_stubsDead
    hle hs hL1 hnh, ⟨htr, hvregs⟩, hpost, hL2'⟩

theorem new_from_slice3_gen_placed_runsTo [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks)
    [hH : HkdfPlacedHooks C.F H] {s₀ : State}
    (hpc : s₀.pc = lsmpl.base 402) (hstat : s₀.status = .Running)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes NewFromSlice3Proof.spqrSha256IVAddr 32 = LibsignalHmac.shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable NewFromSlice3Proof.spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions NewFromSlice3Proof.spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) C.F (effectiveHmacKey C.F key) [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  intro key hL
  obtain ⟨s', hs, htr, hvregs, hpost, hL'⟩ :=
    NewFromSlice3GenProof.new_from_slice3_gen_placed_run
      hH.memcpy hH.memset hH.compress256
      hpc hstat hlt hiv hread_iv hdisj_iv_stack hrw_out hrw_stack hdisj_out_stack hdisj_key_stack hal hL
  exact ⟨s', hs, ⟨htr, hvregs⟩, hpost, hL'⟩

theorem new_from_slice3_gen_placed_runsTo_of_other_block [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks)
    [HkdfPlacedHooks C.F H] {callerProg : Program} {i : Nat} [hcaller : IsLsBlockProg callerProg i H]
    {s₀ : State} (hcl : LibsignalCodeLoaded lsmpl s₀.mem)
    (hpc : s₀.pc = lsmpl.base 402) (hstat : s₀.status = .Running)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes NewFromSlice3Proof.spqrSha256IVAddr 32 = LibsignalHmac.shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable NewFromSlice3Proof.spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions NewFromSlice3Proof.spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hi : i < 619 := by decide) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo callerProg s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) C.F (effectiveHmacKey C.F key) [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) :=
  RunsTo.of_other_block hcl
    (new_from_slice3_gen_placed_runsTo C H hpc hstat hlt hiv hread_iv hdisj_iv_stack hrw_out hrw_stack
      hdisj_out_stack hdisj_key_stack hal)
    hi (by decide) (by decide)

end CryptoVerification.SpqrV1.Kdf

