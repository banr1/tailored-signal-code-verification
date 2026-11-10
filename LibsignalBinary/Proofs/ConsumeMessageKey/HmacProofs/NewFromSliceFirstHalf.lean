/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
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

@[scoped simp, arm64_norm]
theorem extractLsb'_read64_0 (m : Memory) (a : BitVec 64) :
    (m.read64 a).extractLsb' 0 8 = m.read8 a := by
  have h := toLEBytes_8_read64_eq m a
  rw [toLEBytes_8_eq_list, readBytes_8_eq] at h
  exact (List.cons.inj h).1

@[scoped simp, arm64_norm]
theorem extractLsb'_read64_8 (m : Memory) (sp off : BitVec 64) :
    (m.read64 (sp + off)).extractLsb' 8 8 = m.read8 (sp + (off + 1#64)) := by
  have h := toLEBytes_8_read64_eq m (sp + off)
  rw [toLEBytes_8_eq_list, readBytes_8_eq, BitVec.add_assoc] at h
  exact (List.cons.inj (List.cons.inj h).2).1

theorem readBytes_16_of_drop_32 (m : Memory) (sp : BitVec 64) (l : List (BitVec 8))
    (hl : l.length = 64)
    (h : m.readBytes (sp + 144#64) 32 = l.drop 32) :
    m.readBytes (sp + 144#64) 16 = slice16 l 32 := by
  have hlen : (l.drop 32).length = 32 := by simp [hl]
  have h1 := readBytes_slice_of_readBytes_eq m (sp + 144#64) (l.drop 32)
    (by rw [hlen]; exact h) 0 16 (by omega)
  rw [BitVec.add_zero, List.drop_zero, slice16_32_48_eq_drop_32 l hl,
      List.take_left' (slice16_length l 32)] at h1
  exact h1

@[scoped simp, arm64_norm]
theorem read64_write8_stack_iv {b : BitVec 64} {s₀ : State}
    (hdisj : DisjointRegions (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (nfsSp s₀) 544)
    (m : Memory) (off c : BitVec 64) (v : BitVec 8)
    (hc : decide (c.toNat < 544) = true)
    (hoff : decide (num% (ls_str% "kyber_pre_key_pu" + 256) ≤ off.toNat ∧ off.toNat + 8 ≤ num% (ls_str% "kyber_pre_key_signature is required")) = true) :
    (m.write8 (nfsSp s₀ + c) v).read64 (b + off) = m.read64 (b + off) := by
  have hc' : c.toNat < 544 := of_decide_eq_true hc
  have ⟨hoff1, hoff2⟩ : num% (ls_str% "kyber_pre_key_pu" + 256) ≤ off.toNat ∧ off.toNat + 8 ≤ num% (ls_str% "kyber_pre_key_signature is required") := of_decide_eq_true hoff
  refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write8_self m (nfsSp s₀ + c) v)) ?_
  clear * - hdisj hc' hoff1 hoff2
  simp only [List.mem_singleton, forall_eq, DisjointRegions] at hdisj ⊢
  bv_omega

theorem write64_quad_400_iv (b : BitVec 64) (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 (sp + 400#64) (m₂.read64 (b + bv% (ls_str% "kyber_pre_key_pu" + 256)))).write64
      (sp + 408#64) (m₂.read64 (b + bv% (ls_str% "kyber_pre_key_pu" + 264)))).write64
      (sp + 416#64) (m₂.read64 (b + bv% (ls_str% "kyber_pre_key_pu" + 272)))).write64
      (sp + 424#64) (m₂.read64 (b + bv% (ls_str% "kyber_pre_key_pu" + 280)))) =
    m₁.writeBytes (sp + 400#64) (shaStateBytes sha256IV) := by
  have hd1 : sp + 408#64 = (sp + 400#64) + 8#64 := by bv_omega
  have hd2 : sp + 416#64 = (sp + 400#64) + 16#64 := by bv_omega
  have hd3 : sp + 424#64 = (sp + 400#64) + 24#64 := by bv_omega
  have hs1 : b + bv% (ls_str% "kyber_pre_key_pu" + 264) = (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) + 8#64 := by bv_omega
  have hs2 : b + bv% (ls_str% "kyber_pre_key_pu" + 272) = (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) + 16#64 := by bv_omega
  have hs3 : b + bv% (ls_str% "kyber_pre_key_pu" + 280) = (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) + 24#64 := by bv_omega
  rw [hd1, hd2, hd3, hs1, hs2, hs3, write64_quad_read64_eq_writeBytes_32, hiv]

theorem write64_quad_0_ivsw (b : BitVec 64) (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 sp (m₂.read64 (b + bv% (ls_str% "kyber_pre_key_pu" + 272)))).write64
      (sp + 8#64) (m₂.read64 (b + bv% (ls_str% "kyber_pre_key_pu" + 280)))).write64
      (sp + 16#64) (m₂.read64 (b + bv% (ls_str% "kyber_pre_key_pu" + 256)))).write64
      (sp + 24#64) (m₂.read64 (b + bv% (ls_str% "kyber_pre_key_pu" + 264)))) =
    m₁.writeBytes sp ((shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  have hd3 : sp + 24#64 = (sp + 16#64) + 8#64 := by bv_omega
  have hs1 : b + bv% (ls_str% "kyber_pre_key_pu" + 280) = (b + bv% (ls_str% "kyber_pre_key_pu" + 272)) + 8#64 := by bv_omega
  have hs2 : b + bv% (ls_str% "kyber_pre_key_pu" + 264) = (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) + 8#64 := by bv_omega
  have hlen : (shaStateBytes sha256IV).length = 32 := shaStateBytes_length sha256IV
  have htake : m₂.readBytes (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 16 = (shaStateBytes sha256IV).take 16 := by
    have h := readBytes_slice_of_readBytes_eq m₂ (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) (shaStateBytes sha256IV)
      (by rw [hlen]; exact hiv) 0 16 (by omega)
    simpa using h
  have hdrop : m₂.readBytes (b + bv% (ls_str% "kyber_pre_key_pu" + 272)) 16 = (shaStateBytes sha256IV).drop 16 := by
    have h := readBytes_slice_of_readBytes_eq m₂ (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) (shaStateBytes sha256IV)
      (by rw [hlen]; exact hiv) 16 16 (by omega)
    have hadd : (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) + BitVec.ofNat 64 16 = b + bv% (ls_str% "kyber_pre_key_pu" + 272) := by bv_omega
    rw [hadd, List.take_of_length_le (by simp [hlen])] at h
    exact h
  rw [hd3, hs1, hs2, write64_pair_read64_eq_writeBytes_16, write64_pair_read64_eq_writeBytes_16,
      hdrop, htake, writeBytes_append]
  have hlen_drop : ((shaStateBytes sha256IV).drop 16).length = 16 := by simp [hlen]
  rw [hlen_drop]

theorem writeBytes_ivsw_write8_351_comm (m : Memory) (sp : BitVec 64) (v : BitVec 8) :
    (m.writeBytes sp ((shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16)).write8
      (sp + 351#64) v =
    (m.write8 (sp + 351#64) v).writeBytes
      sp ((shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  refine ProofLib.write8_writeBytes_comm m (sp + 351#64) v sp _ ?_
  have hlen : ((shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16).length = 32 := by
    simp [shaStateBytes_length]
  rw [hlen]
  clear * -
  simp only [OutsideRegion]
  bv_omega

theorem NfsMemInv.writeBytes_zero {b : BitVec 64} {s₀ : State} {m : Memory}
    (hM : NfsMemInv b s₀ m) (bs : List (BitVec 8))
    (hbs : 0 < bs.length ∧ bs.length ≤ 432) :
    NfsMemInv b s₀ (m.writeBytes (nfsSp s₀) bs) := by
  rw [← BitVec.add_zero (nfsSp s₀)]
  exact hM.writeBytes_low 0#64 bs (by simpa using hbs)

theorem readBytes_16_writeBytes_0_400 (m : Memory) (sp off : BitVec 64)
    (bs0 bs400 : List (BitVec 8)) (h0 : bs0.length = 32) (h400 : bs400.length = 32)
    (hoff : 32 ≤ off.toNat ∧ off.toNat + 16 ≤ 400 := by decide) :
    ((m.writeBytes sp bs0).writeBytes (sp + 400#64) bs400).readBytes (sp + off) 16 =
      m.readBytes (sp + off) 16 := by
  rcases hoff with ⟨h1, h2⟩
  rw [Layout.readBytes_writeBytes_of_disjoint _ (sp + 400#64) bs400 (sp + off) 16
        (by rw [h400]; clear * - h1 h2; simp only [DisjointRegions]; bv_omega) (by decide),
      Layout.readBytes_writeBytes_of_disjoint m sp bs0 (sp + off) 16
        (by rw [h0]; clear * - h1 h2; simp only [DisjointRegions]; bv_omega) (by decide)]

theorem readBytes_64_of_four_slice16 (m : Memory) (sp : BitVec 64) (l : List (BitVec 8))
    (hl : l.length = 64)
    (h0 : m.readBytes (sp + 288#64) 16 = slice16 l 0)
    (h16 : m.readBytes (sp + 304#64) 16 = slice16 l 16)
    (h32 : m.readBytes (sp + 320#64) 16 = slice16 l 32)
    (h48 : m.readBytes (sp + 336#64) 16 = slice16 l 48) :
    m.readBytes (sp + 288#64) 64 = l := by
  have ha1 : (sp + 288#64) + BitVec.ofNat 64 32 = sp + 320#64 := by clear * -; bv_omega
  have ha2 : (sp + 288#64) + BitVec.ofNat 64 16 = sp + 304#64 := by clear * -; bv_omega
  have ha3 : (sp + 320#64) + BitVec.ofNat 64 16 = sp + 336#64 := by clear * -; bv_omega
  rw [LibsignalAesCbc.Run.Bytes.readBytes_add m (sp + 288#64) 32 32, ha1,
      LibsignalAesCbc.Run.Bytes.readBytes_add m (sp + 288#64) 16 16, ha2,
      LibsignalAesCbc.Run.Bytes.readBytes_add m (sp + 320#64) 16 16, ha3,
      h0, h16, h32, h48,
      ← slice16_0_16_eq_take_32 l hl, ← slice16_32_48_eq_drop_32 l hl,
      List.take_append_drop]

theorem nfs_chunk2 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ s : State} {m_k0 : Memory}
    {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 676))
    (hstat : s.status = .Running)
    (hR : NfsRegInv b s₀ s)
    (hM : NfsMemInv b s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx10 : s.readReg64 .x10 = (byteAt (keyBlock key) 16).zeroExtend 64)
    (hx11 : s.readReg64 .x11 = (byteAt (keyBlock key) 17).zeroExtend 64)
    (hq2 : s.readVReg128 2#5 = m_k0.read64 (nfsSp s₀ + 152#64) ++ m_k0.read64 (nfsSp s₀ + 144#64))
    (hq0 : s.readVReg128 0#5 = m_k0.read64 (nfsSp s₀ + 168#64) ++ m_k0.read64 (nfsSp s₀ + 160#64))
    (hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (P b F alloc) s (fun s' =>
      s'.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 876) ∧
      s'.status = .Running ∧
      NfsRegInv b s₀ s' ∧
      NfsMemInv b s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x11 = (byteAt (keyBlock key) 32 ^^^ 0x36#8).zeroExtend 64 ∧
      s'.readReg64 .x9 = (byteAt (keyBlock key) 33).zeroExtend 64 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16 ∧
      s'.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 (keyBlock key) 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  obtain ⟨hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23,
          hb24, hb25, hb26, hb27, hb28, hb29, hb30, hb31⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 304#64 (keyBlock key) 16 hs16
  obtain ⟨hb32, hb33, -⟩ :=
    read8_16_of_readBytes_slice16 m_k0 (nfsSp s₀) 144#64 (keyBlock key) 32
      (readBytes_16_of_drop_32 m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32)
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb16 hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb24 hb25 hb26 hb27 hb28 hb29 hb30 hb31 hb32 hb33
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  have hM_final : NfsMemInv b s₀
      (((s.mem.writeBytes (nfsSp s₀ + 304#64) (slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)).writeBytes
        (nfsSp s₀ + 320#64) (slice16 (keyBlock key) 32)).writeBytes
        (nfsSp s₀ + 336#64) (slice16 (keyBlock key) 48)) :=
    (((hM.writeBytes_low 304#64 _ (by simp [slice16_length])).writeBytes_low
      320#64 _ (by simp [slice16_length])).writeBytes_low
      336#64 _ (by simp [slice16_length]))
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm, hx8], by simp only [arm64_norm, hx0],
    by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx2],
    by simp only [arm64_norm], by simp only [arm64_norm],
    ?_, ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      ((readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
        ((readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs0))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      ((readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
        (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

theorem nfs_chunk3 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hpc : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 876))
    (hstat : s.status = .Running)
    (hR : NfsRegInv b s₀ s)
    (hM : NfsMemInv b s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx11 : s.readReg64 .x11 = (byteAt (keyBlock key) 32 ^^^ 0x36#8).zeroExtend 64)
    (hx9 : s.readReg64 .x9 = (byteAt (keyBlock key) 33).zeroExtend 64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)
    (hs32 : s.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 (keyBlock key) 32)
    (hs48 : s.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) :
    RunsTo (P b F alloc) s (fun s' =>
      s'.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1068) ∧
      s'.status = .Running ∧
      NfsRegInv b s₀ s' ∧
      NfsMemInv b s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x9 = (byteAt (keyBlock key) 48 ^^^ 0x36#8).zeroExtend 64 ∧
      s'.readReg64 .x10 = (byteAt (keyBlock key) 49).zeroExtend 64 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16 ∧
      s'.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  obtain ⟨-, -, hb34, hb35, hb36, hb37, hb38, hb39,
          hb40, hb41, hb42, hb43, hb44, hb45, hb46, hb47⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 320#64 (keyBlock key) 32 hs32
  obtain ⟨hb48, hb49, -⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 336#64 (keyBlock key) 48 hs48
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb34 hb35 hb36 hb37 hb38 hb39 hb40 hb41 hb42 hb43 hb44 hb45 hb46 hb47 hb48 hb49
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
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
    ?_, ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact hM.writeBytes_low 320#64 _ (by simp [slice16_length])
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs0
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs16
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs48

theorem nfs_chunk4 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hpc : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1068))
    (hstat : s.status = .Running)
    (hR : NfsRegInv b s₀ s)
    (hM : NfsMemInv b s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx9 : s.readReg64 .x9 = (byteAt (keyBlock key) 48 ^^^ 0x36#8).zeroExtend 64)
    (hx10 : s.readReg64 .x10 = (byteAt (keyBlock key) 49).zeroExtend 64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)
    (hs32 : s.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 32)
    (hs48 : s.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) :
    RunsTo (P b F alloc) s (fun s' =>
      s'.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1260) ∧
      s'.status = .Running ∧
      NfsRegInv b s₀ s' ∧
      NfsMemInv b s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 =
        (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hread_iv : s.mem.Readable (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 := hM.readable_iv
  have hdisj_iv : DisjointRegions (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (nfsSp s₀) 544 := hM.disj_iv_stack
  have hread_iv_eq := read64_write8_stack_iv hM.disj_iv_stack
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  obtain ⟨-, -, hb50, hb51, hb52, hb53, hb54, hb55,
          hb56, hb57, hb58, hb59, hb60, hb61, hb62, hb63⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 336#64 (keyBlock key) 48 hs48
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb50 hb51 hb52 hb53 hb54 hb55 hb56 hb57 hb58 hb59 hb60 hb61 hb62 hb63
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  set ivsw := (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16
  set iv := shaStateBytes sha256IV
  have hivsw_len : ivsw.length = 32 := by simp [ivsw, shaStateBytes_length]
  have hiv_len : iv.length = 32 := shaStateBytes_length sha256IV
  set m_xor := s.mem.writeBytes (nfsSp s₀ + 336#64) (slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 48)
  set m_final := (m_xor.writeBytes (nfsSp s₀) ivsw).writeBytes (nfsSp s₀ + 400#64) iv
  have hM_final : NfsMemInv b s₀ m_final :=
    ((hM.writeBytes_low 336#64 _ (by simp [slice16_length])).writeBytes_zero
      ivsw (by simp [hivsw_len])).writeBytes_low
      400#64 iv (by simp [hiv_len])
  have hist_final : m_final.readBytes (nfsSp s₀ + 400#64) 32 = iv :=
    Layout.readBytes_writeBytes_eq _ (nfsSp s₀ + 400#64) iv 32 hiv_len (by decide)
  have hivsw_final : m_final.readBytes (nfsSp s₀) 32 = ivsw := by
    rw [Layout.readBytes_writeBytes_of_disjoint _ (nfsSp s₀ + 400#64) iv (nfsSp s₀) 32
          (by rw [hiv_len]; clear * -; simp only [DisjointRegions]; bv_omega) (by decide),
        Layout.readBytes_writeBytes_eq m_xor (nfsSp s₀) ivsw 32 hivsw_len (by decide)]
  have hblk_final : m_final.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) := by
    refine readBytes_64_of_four_slice16 m_final (nfsSp s₀) ((keyBlock key).map (· ^^^ 0x36#8))
      (by simp [hkb_len]) ?_ ?_ ?_ ?_
    · rw [readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 288#64 ivsw iv hivsw_len hiv_len]
      exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs0
    · rw [readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 304#64 ivsw iv hivsw_len hiv_len]
      exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs16
    · rw [readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 320#64 ivsw iv hivsw_len hiv_len]
      exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs32
    · rw [readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 336#64 ivsw iv hivsw_len hiv_len]
      exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm, hx0],
    by simp only [arm64_norm, hx1],
    by simp only [arm64_norm, hx2],
    ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv b _ s.mem (nfsSp s₀) hM.iv_bytes,
        write64_quad_0_ivsw b _ s.mem (nfsSp s₀) hM.iv_bytes,
        writeBytes_ivsw_write8_351_comm,
        write8_16_stack_336_xor _ _ _ _ hkb_len]
    exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv b _ s.mem (nfsSp s₀) hM.iv_bytes,
        write64_quad_0_ivsw b _ s.mem (nfsSp s₀) hM.iv_bytes,
        writeBytes_ivsw_write8_351_comm,
        write8_16_stack_336_xor _ _ _ _ hkb_len]
    exact hist_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv b _ s.mem (nfsSp s₀) hM.iv_bytes,
        write64_quad_0_ivsw b _ s.mem (nfsSp s₀) hM.iv_bytes,
        writeBytes_ivsw_write8_351_comm,
        write8_16_stack_336_xor _ _ _ _ hkb_len]
    exact hblk_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv b _ s.mem (nfsSp s₀) hM.iv_bytes,
        write64_quad_0_ivsw b _ s.mem (nfsSp s₀) hM.iv_bytes,
        writeBytes_ivsw_write8_351_comm,
        write8_16_stack_336_xor _ _ _ _ hkb_len]
    exact hivsw_final

/-- First half of `new_from_slice` (`0x2b3b0 → 0x2b89c`, up to the first `compress256` call). -/
theorem nfs_first_half {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
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
      s'.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1260) ∧
      s'.status = .Running ∧
      NfsRegInv b s₀ s' ∧
      NfsMemInv b s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 =
        (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  intro key
  have hkey_len : key.length ≤ 64 := by
    dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  refine (nfs_seg0 hpc hstat hlen hiv hb hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hdisj_key_stack hal).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1, hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩
  refine (nfs_chunk1 hkey_len hpc1 hstat1 hR1 hM1 hx8_1 hx0_1 hx1_1 hx2_1 hs0_1 hs16_1).trans fun s2 h2 => ?_
  rcases h2 with ⟨hpc2, hstat2, hR2, hM2, hx8_2, hx0_2, hx1_2, hx2_2, hx10_2, hx11_2, hq2_2, hq0_2, hs0_2, hs16_2⟩
  refine (nfs_chunk2 hkey_len hal hpc2 hstat2 hR2 hM2 hx8_2 hx0_2 hx1_2 hx2_2 hx10_2 hx11_2
    (hq2_2.trans hq2_1) (hq0_2.trans hq0_1) hk0_1 hs0_2 hs16_2).trans fun s3 h3 => ?_
  rcases h3 with ⟨hpc3, hstat3, hR3, hM3, hx8_3, hx0_3, hx1_3, hx2_3, hx11_3, hx9_3, hs0_3, hs16_3, hs32_3, hs48_3⟩
  refine (nfs_chunk3 hkey_len hpc3 hstat3 hR3 hM3 hx8_3 hx0_3 hx1_3 hx2_3 hx11_3 hx9_3
    hs0_3 hs16_3 hs32_3 hs48_3).trans fun s4 h4 => ?_
  rcases h4 with ⟨hpc4, hstat4, hR4, hM4, hx8_4, hx0_4, hx1_4, hx2_4, hx9_4, hx10_4, hs0_4, hs16_4, hs32_4, hs48_4⟩
  exact nfs_chunk4 hkey_len hal hb hpc4 hstat4 hR4 hM4 hx8_4 hx0_4 hx1_4 hx2_4 hx9_4 hx10_4
    hs0_4 hs16_4 hs32_4 hs48_4

/-! ## Relocatable `[LibsignalPlacement]` First Half of `new_from_slice` (Block 114) -/

@[scoped simp, arm64_norm]
theorem read64_write8_stack_iv_placed_zero [LibsignalPlacement] {s₀ : State}
    (hdisj : DisjointRegions lsSha256IVAddr 32 (nfsSp s₀) 544)
    (m : Memory) (c : BitVec 64) (v : BitVec 8)
    (hc : decide (c.toNat < 544) = true) :
    (m.write8 (nfsSp s₀ + c) v).read64 lsSha256IVAddr = m.read64 lsSha256IVAddr := by
  have hc' : c.toNat < 544 := of_decide_eq_true hc
  refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write8_self m (nfsSp s₀ + c) v)) ?_
  clear * - hdisj hc'
  simp only [List.mem_singleton, forall_eq, DisjointRegions] at hdisj ⊢
  bv_omega

@[scoped simp, arm64_norm]
theorem read64_write8_stack_iv_placed_off [LibsignalPlacement] {s₀ : State}
    (hdisj : DisjointRegions lsSha256IVAddr 32 (nfsSp s₀) 544)
    (m : Memory) (off c : BitVec 64) (v : BitVec 8)
    (hc : decide (c.toNat < 544) = true)
    (hoff : decide (off.toNat + 8 ≤ 32) = true) :
    (m.write8 (nfsSp s₀ + c) v).read64 (lsSha256IVAddr + off) = m.read64 (lsSha256IVAddr + off) := by
  have hc' : c.toNat < 544 := of_decide_eq_true hc
  have hoff' : off.toNat + 8 ≤ 32 := of_decide_eq_true hoff
  refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write8_self m (nfsSp s₀ + c) v)) ?_
  clear * - hdisj hc' hoff'
  simp only [List.mem_singleton, forall_eq, DisjointRegions] at hdisj ⊢
  bv_omega

theorem write64_quad_400_iv_placed [LibsignalPlacement] (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 (sp + 400#64) (m₂.read64 lsSha256IVAddr)).write64
      (sp + 408#64) (m₂.read64 (lsSha256IVAddr + 8#64))).write64
      (sp + 416#64) (m₂.read64 (lsSha256IVAddr + 16#64))).write64
      (sp + 424#64) (m₂.read64 (lsSha256IVAddr + 24#64))) =
    m₁.writeBytes (sp + 400#64) (shaStateBytes sha256IV) := by
  have hd1 : sp + 408#64 = (sp + 400#64) + 8#64 := by bv_omega
  have hd2 : sp + 416#64 = (sp + 400#64) + 16#64 := by bv_omega
  have hd3 : sp + 424#64 = (sp + 400#64) + 24#64 := by bv_omega
  rw [hd1, hd2, hd3, write64_quad_read64_eq_writeBytes_32, hiv]

theorem write64_quad_0_ivsw_placed [LibsignalPlacement] (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 sp (m₂.read64 (lsSha256IVAddr + 16#64))).write64
      (sp + 8#64) (m₂.read64 (lsSha256IVAddr + 24#64))).write64
      (sp + 16#64) (m₂.read64 lsSha256IVAddr)).write64
      (sp + 24#64) (m₂.read64 (lsSha256IVAddr + 8#64))) =
    m₁.writeBytes sp ((shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  have hd3 : sp + 24#64 = (sp + 16#64) + 8#64 := by bv_omega
  have hs1 : lsSha256IVAddr + 24#64 = (lsSha256IVAddr + 16#64) + 8#64 := by bv_omega
  have hlen : (shaStateBytes sha256IV).length = 32 := shaStateBytes_length sha256IV
  have htake : m₂.readBytes lsSha256IVAddr 16 = (shaStateBytes sha256IV).take 16 := by
    have h := readBytes_slice_of_readBytes_eq m₂ lsSha256IVAddr (shaStateBytes sha256IV)
      (by rw [hlen]; exact hiv) 0 16 (by omega)
    simpa using h
  have hdrop : m₂.readBytes (lsSha256IVAddr + 16#64) 16 = (shaStateBytes sha256IV).drop 16 := by
    have h := readBytes_slice_of_readBytes_eq m₂ lsSha256IVAddr (shaStateBytes sha256IV)
      (by rw [hlen]; exact hiv) 16 16 (by omega)
    have hadd : lsSha256IVAddr + BitVec.ofNat 64 16 = lsSha256IVAddr + 16#64 := rfl
    rw [hadd, List.take_of_length_le (by simp [hlen])] at h
    exact h
  rw [hd3, hs1, write64_pair_read64_eq_writeBytes_16, write64_pair_read64_eq_writeBytes_16,
      hdrop, htake, writeBytes_append]
  have hlen_drop : ((shaStateBytes sha256IV).drop 16).length = 16 := by simp [hlen]
  rw [hlen_drop]

theorem nfs_chunk2_placed [LibsignalPlacement]
    {H : LibsignalHooks} {s₀ s : State} {m_k0 : Memory}
    {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc : s.pc = (blkPl_114).base + 676#64)
    (hstat : s.status = .Running)
    (hR : NfsRegInv nfsPlacedFakeB s₀ s)
    (hM : NfsMemInv nfsPlacedFakeB s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx10 : s.readReg64 .x10 = (byteAt (keyBlock key) 16).zeroExtend 64)
    (hx11 : s.readReg64 .x11 = (byteAt (keyBlock key) 17).zeroExtend 64)
    (hq2 : s.readVReg128 2#5 = m_k0.read64 (nfsSp s₀ + 152#64) ++ m_k0.read64 (nfsSp s₀ + 144#64))
    (hq0 : s.readVReg128 0#5 = m_k0.read64 (nfsSp s₀ + 168#64) ++ m_k0.read64 (nfsSp s₀ + 160#64))
    (hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (lsProg_114 H) s (fun s' =>
      s'.pc = (blkPl_114).base + 876#64 ∧
      s'.status = .Running ∧
      NfsRegInv nfsPlacedFakeB s₀ s' ∧
      NfsMemInv nfsPlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x11 = (byteAt (keyBlock key) 32 ^^^ 0x36#8).zeroExtend 64 ∧
      s'.readReg64 .x9 = (byteAt (keyBlock key) 33).zeroExtend 64 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16 ∧
      s'.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 (keyBlock key) 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  obtain ⟨hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23,
          hb24, hb25, hb26, hb27, hb28, hb29, hb30, hb31⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 304#64 (keyBlock key) 16 hs16
  obtain ⟨hb32, hb33, -⟩ :=
    read8_16_of_readBytes_slice16 m_k0 (nfsSp s₀) 144#64 (keyBlock key) 32
      (readBytes_16_of_drop_32 m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32)
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb16 hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb24 hb25 hb26 hb27 hb28 hb29 hb30 hb31 hb32 hb33
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  have hM_final : NfsMemInv nfsPlacedFakeB s₀
      (((s.mem.writeBytes (nfsSp s₀ + 304#64) (slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)).writeBytes
        (nfsSp s₀ + 320#64) (slice16 (keyBlock key) 32)).writeBytes
        (nfsSp s₀ + 336#64) (slice16 (keyBlock key) 48)) :=
    (((hM.writeBytes_low 304#64 _ (by simp [slice16_length])).writeBytes_low
      320#64 _ (by simp [slice16_length])).writeBytes_low
      336#64 _ (by simp [slice16_length]))
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm, hx8], by simp only [arm64_norm, hx0],
    by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx2],
    by simp only [arm64_norm], by simp only [arm64_norm],
    ?_, ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      ((readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
        ((readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs0))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      ((readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
        (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

theorem nfs_chunk3_placed [LibsignalPlacement]
    {H : LibsignalHooks} {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hpc : s.pc = (blkPl_114).base + 876#64)
    (hstat : s.status = .Running)
    (hR : NfsRegInv nfsPlacedFakeB s₀ s)
    (hM : NfsMemInv nfsPlacedFakeB s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx11 : s.readReg64 .x11 = (byteAt (keyBlock key) 32 ^^^ 0x36#8).zeroExtend 64)
    (hx9 : s.readReg64 .x9 = (byteAt (keyBlock key) 33).zeroExtend 64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)
    (hs32 : s.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 (keyBlock key) 32)
    (hs48 : s.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) :
    RunsTo (lsProg_114 H) s (fun s' =>
      s'.pc = (blkPl_114).base + 1068#64 ∧
      s'.status = .Running ∧
      NfsRegInv nfsPlacedFakeB s₀ s' ∧
      NfsMemInv nfsPlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x9 = (byteAt (keyBlock key) 48 ^^^ 0x36#8).zeroExtend 64 ∧
      s'.readReg64 .x10 = (byteAt (keyBlock key) 49).zeroExtend 64 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16 ∧
      s'.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  obtain ⟨-, -, hb34, hb35, hb36, hb37, hb38, hb39,
          hb40, hb41, hb42, hb43, hb44, hb45, hb46, hb47⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 320#64 (keyBlock key) 32 hs32
  obtain ⟨hb48, hb49, -⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 336#64 (keyBlock key) 48 hs48
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb34 hb35 hb36 hb37 hb38 hb39 hb40 hb41 hb42 hb43 hb44 hb45 hb46 hb47 hb48 hb49
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
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
    ?_, ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact hM.writeBytes_low 320#64 _ (by simp [slice16_length])
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs0
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs16
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs48

theorem nfs_chunk4_placed [LibsignalPlacement]
    {H : LibsignalHooks} {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc : s.pc = (blkPl_114).base + 1068#64)
    (hstat : s.status = .Running)
    (hR : NfsRegInv nfsPlacedFakeB s₀ s)
    (hM : NfsMemInv nfsPlacedFakeB s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx9 : s.readReg64 .x9 = (byteAt (keyBlock key) 48 ^^^ 0x36#8).zeroExtend 64)
    (hx10 : s.readReg64 .x10 = (byteAt (keyBlock key) 49).zeroExtend 64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)
    (hs32 : s.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 32)
    (hs48 : s.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) :
    RunsTo (lsProg_114 H) s (fun s' =>
      s'.pc = (blkPl_114).base + 1260#64 ∧
      s'.status = .Running ∧
      NfsRegInv nfsPlacedFakeB s₀ s' ∧
      NfsMemInv nfsPlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 =
        (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hread_iv : s.mem.Readable lsSha256IVAddr 32 := nfsPlacedFakeB_add_iv ▸ hM.readable_iv
  have hdisj_iv : DisjointRegions lsSha256IVAddr 32 (nfsSp s₀) 544 := nfsPlacedFakeB_add_iv ▸ hM.disj_iv_stack
  have hiv_bytes : s.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV := nfsPlacedFakeB_add_iv ▸ hM.iv_bytes
  have hread_iv_eq0 := read64_write8_stack_iv_placed_zero hdisj_iv
  have hread_iv_eq_off := read64_write8_stack_iv_placed_off hdisj_iv
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  obtain ⟨-, -, hb50, hb51, hb52, hb53, hb54, hb55,
          hb56, hb57, hb58, hb59, hb60, hb61, hb62, hb63⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 336#64 (keyBlock key) 48 hs48
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb50 hb51 hb52 hb53 hb54 hb55 hb56 hb57 hb58 hb59 hb60 hb61 hb62 hb63
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  set ivsw := (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16
  set iv := shaStateBytes sha256IV
  have hivsw_len : ivsw.length = 32 := by simp [ivsw, shaStateBytes_length]
  have hiv_len : iv.length = 32 := shaStateBytes_length sha256IV
  set m_xor := s.mem.writeBytes (nfsSp s₀ + 336#64) (slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 48)
  set m_final := (m_xor.writeBytes (nfsSp s₀) ivsw).writeBytes (nfsSp s₀ + 400#64) iv
  have hM_final : NfsMemInv nfsPlacedFakeB s₀ m_final :=
    ((hM.writeBytes_low 336#64 _ (by simp [slice16_length])).writeBytes_zero
      ivsw (by simp [hivsw_len])).writeBytes_low
      400#64 iv (by simp [hiv_len])
  have hist_final : m_final.readBytes (nfsSp s₀ + 400#64) 32 = iv :=
    Layout.readBytes_writeBytes_eq _ (nfsSp s₀ + 400#64) iv 32 hiv_len (by decide)
  have hivsw_final : m_final.readBytes (nfsSp s₀) 32 = ivsw := by
    rw [Layout.readBytes_writeBytes_of_disjoint _ (nfsSp s₀ + 400#64) iv (nfsSp s₀) 32
          (by rw [hiv_len]; clear * -; simp only [DisjointRegions]; bv_omega) (by decide),
        Layout.readBytes_writeBytes_eq m_xor (nfsSp s₀) ivsw 32 hivsw_len (by decide)]
  have hblk_final : m_final.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) := by
    refine readBytes_64_of_four_slice16 m_final (nfsSp s₀) ((keyBlock key).map (· ^^^ 0x36#8))
      (by simp [hkb_len]) ?_ ?_ ?_ ?_
    · rw [readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 288#64 ivsw iv hivsw_len hiv_len]
      exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs0
    · rw [readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 304#64 ivsw iv hivsw_len hiv_len]
      exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs16
    · rw [readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 320#64 ivsw iv hivsw_len hiv_len]
      exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs32
    · rw [readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 336#64 ivsw iv hivsw_len hiv_len]
      exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm, hx0],
    by simp only [arm64_norm, hx1],
    by simp only [arm64_norm, hx2],
    ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv_placed _ s.mem (nfsSp s₀) hiv_bytes,
        write64_quad_0_ivsw_placed _ s.mem (nfsSp s₀) hiv_bytes,
        writeBytes_ivsw_write8_351_comm,
        write8_16_stack_336_xor _ _ _ _ hkb_len]
    exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv_placed _ s.mem (nfsSp s₀) hiv_bytes,
        write64_quad_0_ivsw_placed _ s.mem (nfsSp s₀) hiv_bytes,
        writeBytes_ivsw_write8_351_comm,
        write8_16_stack_336_xor _ _ _ _ hkb_len]
    exact hist_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv_placed _ s.mem (nfsSp s₀) hiv_bytes,
        write64_quad_0_ivsw_placed _ s.mem (nfsSp s₀) hiv_bytes,
        writeBytes_ivsw_write8_351_comm,
        write8_16_stack_336_xor _ _ _ _ hkb_len]
    exact hblk_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv_placed _ s.mem (nfsSp s₀) hiv_bytes,
        write64_quad_0_ivsw_placed _ s.mem (nfsSp s₀) hiv_bytes,
        writeBytes_ivsw_write8_351_comm,
        write8_16_stack_336_xor _ _ _ _ hkb_len]
    exact hivsw_final

/-- Placed first half of `new_from_slice` (Block 114, `+0 → +1260`). -/
theorem nfs_first_half_placed [LibsignalPlacement]
    {H : LibsignalHooks} (h_memcpy : H lsMemcpySym = some memcpyHook)
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
      s'.pc = (blkPl_114).base + 1260#64 ∧
      s'.status = .Running ∧
      NfsRegInv nfsPlacedFakeB s₀ s' ∧
      NfsMemInv nfsPlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 =
        (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  intro key
  have hkey_len : key.length ≤ 64 := by
    dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  refine (nfs_seg0_placed h_memcpy hpc hstat hlen hiv hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hdisj_key_stack hal).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1, hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩
  refine (nfs_chunk1_placed hkey_len hpc1 hstat1 hR1 hM1 hx8_1 hx0_1 hx1_1 hx2_1 hs0_1 hs16_1).trans fun s2 h2 => ?_
  rcases h2 with ⟨hpc2, hstat2, hR2, hM2, hx8_2, hx0_2, hx1_2, hx2_2, hx10_2, hx11_2, hq2_2, hq0_2, hs0_2, hs16_2⟩
  refine (nfs_chunk2_placed hkey_len hal hpc2 hstat2 hR2 hM2 hx8_2 hx0_2 hx1_2 hx2_2 hx10_2 hx11_2
    (hq2_2.trans hq2_1) (hq0_2.trans hq0_1) hk0_1 hs0_2 hs16_2).trans fun s3 h3 => ?_
  rcases h3 with ⟨hpc3, hstat3, hR3, hM3, hx8_3, hx0_3, hx1_3, hx2_3, hx11_3, hx9_3, hs0_3, hs16_3, hs32_3, hs48_3⟩
  refine (nfs_chunk3_placed hkey_len hpc3 hstat3 hR3 hM3 hx8_3 hx0_3 hx1_3 hx2_3 hx11_3 hx9_3
    hs0_3 hs16_3 hs32_3 hs48_3).trans fun s4 h4 => ?_
  rcases h4 with ⟨hpc4, hstat4, hR4, hM4, hx8_4, hx0_4, hx1_4, hx2_4, hx9_4, hx10_4, hs0_4, hs16_4, hs32_4, hs48_4⟩
  exact nfs_chunk4_placed hkey_len hal hpc4 hstat4 hR4 hM4 hx8_4 hx0_4 hx1_4 hx2_4 hx9_4 hx10_4
    hs0_4 hs16_4 hs32_4 hs48_4

end CryptoVerification.LibsignalSession.CryptoHmacSha256
