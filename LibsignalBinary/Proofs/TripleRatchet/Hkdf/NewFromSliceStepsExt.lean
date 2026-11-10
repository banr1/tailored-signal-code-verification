/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf

/-!
# Straight-Line Segments of `Hmac<Sha256>::new_from_slice`

Proves the straight-line `RunsTo` segments of
`<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice` on
`tripleRatchetProgAtExt` for keys of length `≤ 64`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalTripleRatchet.HkdfExt.NfsSteps

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open ProofLib.ProgramReflection

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds
  Memory.read64_write64_base_off_disjoint
  Memory.read64_write64_base_zero_off
  Memory.read64_write64_base_off_zero
  Memory.read64_write8_base_off_disjoint
  Memory.read64_write8_base_zero_off
  Memory.read64_write8_base_off_zero
  truncate8_zeroExtend_xor_32
  truncate8_zeroExtend_xor_64

@[scoped simp, local arm64_norm]
theorem nfsSp_setMem (s₀ : State) (m : Memory) : nfsSp (s₀.setMem m) = nfsSp s₀ := rfl

theorem NfsSavedStack_setMem_iff {s₀ : State} {m₁ m : Memory} :
    NfsSavedStack (s₀.setMem m₁) m ↔ NfsSavedStack s₀ m := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ <;>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem NfsRegInv_setMem_iff {b : BitVec 64} {s₀ s : State} {m₁ : Memory} :
    NfsRegInv b (s₀.setMem m₁) s ↔ NfsRegInv b s₀ s := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ <;>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem nfsRegInv_of_cc {b : BitVec 64} {s₀ s s' : State}
    (hR : NfsRegInv b s₀ s) (hcc : CallingConventionPreserved s s') :
    NfsRegInv b s₀ s' :=
  ⟨hcc.1.trans hR.sp_eq,
   hR.sp_align,
   hcc.2.readReg64_x29.trans hR.x29_eq,
   hcc.2.1.trans hR.x19_eq,
   hcc.2.2.1.trans hR.x20_eq,
   hcc.2.2.2.2.1.trans hR.x22_eq,
   hcc.2.2.2.2.2.2.2.1.trans hR.x25_eq,
   hcc.2.2.2.2.2.2.2.2.1.trans hR.x26_eq,
   hcc.2.2.2.2.2.2.2.2.2.1.trans hR.x27_eq⟩

theorem Frame_of_agreesOutside_stack_only {sp : BitVec 64} {m₀ m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hf : Frame m₀ m [(sp, 544)])
    (hA : AgreesOutside m m' (sp + off) sz)
    (hoff : off.toNat + sz ≤ 544) :
    Frame m₀ m' [(sp, 544)] :=
  hf.trans_agreesOutside_sub (b := sp) (n := 544) (by simp) (by clear * - hoff; bv_omega) hA

set_option maxHeartbeats 1600000 in
/-- First 17 instructions of `new_from_slice` (entry to `memcpy` stub entry). -/
theorem nfs_seg0a_ext {b : BitVec 64} {ext : String → Option (State → State)} {s₀ : State}
    (hpc : s₀.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]"))
    (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hrw_stack : s₀.mem.RW (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    RunsTo (tripleRatchetProgAtExt b ext) s₀ (fun s1 =>
      s1.pc = b + bv% (ls_off% "memcpy") ∧
      s1.status = .Running ∧
      s1.sp = nfsSp s₀ ∧
      (nfsSp s₀ &&& 0b1111#64) = 0#64 ∧
      s1.readReg64 .x29 = nfsSp s₀ + 464#64 ∧
      s1.readReg64 .x19 = s₀.readReg64 .x0 ∧
      s1.readReg64 .x22 = b + bv% (ls_str% "kyber_pre_key_pu" + 256) ∧
      s1.readReg64 .x25 = s₀.readReg64 .x25 ∧
      s1.readReg64 .x26 = s₀.readReg64 .x26 ∧
      s1.readReg64 .x27 = s₀.readReg64 .x27 ∧
      s1.readReg64 .x0 = nfsSp s₀ + 112#64 ∧
      s1.readReg64 .x1 = s₀.readReg64 .x1 ∧
      s1.readReg64 .x2 = s₀.readReg64 .x2 ∧
      s1.readReg64 .lr = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 68) ∧
      s1.mem.readBytes (nfsSp s₀ + 112#64) 64 = List.replicate 64 0#8 ∧
      NfsSavedStack s₀ (s1.mem.write64 (nfsSp s₀ + 432#64) 1#64) ∧
      Frame s₀.mem s1.mem [(nfsSp s₀, 544)]) := by
  generalize hPost : (fun s1 : State => _) = Post
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = false := nfs_ule_65_false hlen
  have hadrp1 : (((b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 40)) &&& 0xfffffffffffff000#64) + bv% (page% (ls_str% "kyber_pre_key_pu" + 256) - page% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 40))) + bv% ((ls_str% "kyber_pre_key_pu" + 256) % 4096) = b + bv% (ls_str% "kyber_pre_key_pu" + 256) := by
    clear * - hb; bv_bits
  have hadrp2 : ((b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 40)) &&& 0xfffffffffffff000#64) + bv% (ls_str% "kyber_pre_key_pu" + 256 - page% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 40)) = b + bv% (ls_str% "kyber_pre_key_pu" + 256) := by
    clear * - hb; bv_bits
  iterate 17 sess_step
  subst hPost
  refine RunsTo.refl ?_
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 :=
    agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8))
      (nfsSp s₀ + 112#64) 64 := by
    simpa using CryptoHmacSha256.AgreesOutside.writeBytes_self (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (List.replicate 64 0#8)
  have hoct :
      ((((((((nfsPrologueMem s₀).write64 (nfsSp s₀ + 112#64) 0#64).write64
        (nfsSp s₀ + 120#64) 0#64).write64 (nfsSp s₀ + 128#64) 0#64).write64
        (nfsSp s₀ + 136#64) 0#64).write64 (nfsSp s₀ + 144#64) 0#64).write64
        (nfsSp s₀ + 152#64) 0#64).write64 (nfsSp s₀ + 160#64) 0#64).write64
        (nfsSp s₀ + 168#64) 0#64 =
      (nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8) :=
    write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀)
  dsimp only [nfsPrologueMem, Reg.x29, Reg.x30, Reg.x28, Reg.x24, Reg.x23,
    Reg.x22, Reg.x21, Reg.x20, Reg.x19] at hoct
  refine ⟨by simp only [arm64_norm], by simp only [arm64_norm, hstat],
    by simp only [arm64_norm], hal_nfs, by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC, State.setPC]
    rw [hoct]
    exact CryptoHmacSha256.Layout.readBytes_writeBytes_eq (nfsPrologueMem s₀) (nfsSp s₀ + 112#64)
      (List.replicate 64 0#8) 64 (by simp) (by decide)
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC, State.setPC]
    rw [hoct]
    exact nfsSavedStack_prologue_432 s₀ _ hA_zero
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC, State.setPC]
    rw [hoct]
    exact Frame_of_agreesOutside_stack_only
      (Frame_of_agreesOutside_stack_only (Frame.refl s₀.mem _) hA_pro (by decide))
      hA_zero (by decide)

set_option maxHeartbeats 1600000 in
/-- Next 10 instructions after `memcpy` returns (`entry + 68 → entry + 476`). -/
theorem nfs_seg0b_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 68))
    (hstat : s.status = .Running)
    (hsp : s.sp = nfsSp s₀)
    (hsp_align : (nfsSp s₀ &&& 0b1111#64) = 0#64)
    (hx29 : s.readReg64 .x29 = nfsSp s₀ + 464#64)
    (hx19 : s.readReg64 .x19 = s₀.readReg64 .x0)
    (hx22 : s.readReg64 .x22 = b + bv% (ls_str% "kyber_pre_key_pu" + 256))
    (hx25 : s.readReg64 .x25 = s₀.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s₀.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s₀.readReg64 .x27)
    (hM_432 : NfsMemInv b (s₀.setMem s.mem) (s.mem.write64 (nfsSp s₀ + 432#64) 1#64))
    (hk0_64 : s.mem.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 476) ∧
      s'.status = .Running ∧
      NfsRegInv b s₀ s' ∧
      NfsMemInv b (s₀.setMem s.mem) s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  generalize hPost : (fun s' : State => _) = Post
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  have hA_432 : AgreesOutside s.mem (s.mem.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self s.mem (nfsSp s₀ + 432#64) 1#64
  have hRW_low : s.mem.RW (nfsSp s₀) 432 := by
    intro a ha
    have hout : OutsideRegion (nfsSp s₀ + 432#64) 8 a := by
      clear * - ha; unfold InRegion OutsideRegion at *; bv_omega
    have ha544 : InRegion (nfsSp (s₀.setMem s.mem)) 544 a := by
      clear * - ha; dsimp only [InRegion, nfsSp, State.setMem] at *; omega
    have h432 := Memory.permNoLazy_eq_some_rw_iff.mp (hM_432.rw_stack a ha544)
    exact Memory.permNoLazy_eq_some_rw_iff.mpr
      ⟨(congrFun hA_432.2.1 a).symm.trans h432.1, (hA_432.2.2.1 a hout).symm.trans h432.2⟩
  have hcw_432 : s.mem.canWrite (nfsSp s₀ + 432#64) 8 = true := by
    rw [Memory.canWrite_congr hA_432.2.1.symm]
    exact hM_432.rw_stack.canWrite_sub (by clear * -; dsimp [nfsSp, State.setMem]; bv_omega) (by decide)
  iterate 10 sess_step
  subst hPost
  refine RunsTo.refl ?_
  set m_k0 := s.mem
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
  have hM_final : NfsMemInv b (s₀.setMem s.mem)
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
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm], by simp only [arm64_norm, hsp],
    by simp only [arm64_norm, hsp], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hsp],
    by simp (config := { decide := true }) only [arm64_norm, hsp],
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

set_option maxHeartbeats 1600000 in
theorem nfs_chunk1_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
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
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
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
  iterate 50 sess_step
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

set_option maxHeartbeats 1600000 in
theorem nfs_chunk2_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {m_k0 : Memory} {key : List (BitVec 8)}
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
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
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
  iterate 50 sess_step
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

set_option maxHeartbeats 1600000 in
theorem nfs_chunk3_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
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
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
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
  iterate 48 sess_step
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

set_option maxHeartbeats 1600000 in
theorem nfs_chunk4_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
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
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
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
  iterate 48 sess_step
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
    CryptoHmacSha256.Layout.readBytes_writeBytes_eq _ (nfsSp s₀ + 400#64) iv 32 hiv_len (by decide)
  have hivsw_final : m_final.readBytes (nfsSp s₀) 32 = ivsw := by
    rw [CryptoHmacSha256.Layout.readBytes_writeBytes_of_disjoint _ (nfsSp s₀ + 400#64) iv (nfsSp s₀) 32
          (by rw [hiv_len]; clear * -; simp only [DisjointRegions]; bv_omega) (by decide),
        CryptoHmacSha256.Layout.readBytes_writeBytes_eq m_xor (nfsSp s₀) ivsw 32 hivsw_len (by decide)]
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

theorem nfs_after_memcpy_to_compress1_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hpc : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 68))
    (hstat : s.status = .Running)
    (hsp : s.sp = nfsSp s₀)
    (hsp_align : (nfsSp s₀ &&& 0b1111#64) = 0#64)
    (hx29 : s.readReg64 .x29 = nfsSp s₀ + 464#64)
    (hx19 : s.readReg64 .x19 = s₀.readReg64 .x0)
    (hx22 : s.readReg64 .x22 = b + bv% (ls_str% "kyber_pre_key_pu" + 256))
    (hx25 : s.readReg64 .x25 = s₀.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s₀.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s₀.readReg64 .x27)
    (hM_432 : NfsMemInv b (s₀.setMem s.mem) (s.mem.write64 (nfsSp s₀ + 432#64) 1#64))
    (hk0_64 : s.mem.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1260) ∧
      s'.status = .Running ∧
      NfsRegInv b (s₀.setMem s.mem) s' ∧
      NfsMemInv b (s₀.setMem s.mem) s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 =
        (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  refine (nfs_seg0b_ext (s₀ := s₀.setMem s.mem) hlen hal hpc hstat hsp hsp_align
    hx29 hx19 hx22 hx25 hx26 hx27 hM_432 hk0_64).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1, hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩
  refine (nfs_chunk1_ext hlen hpc1 hstat1 hR1 hM1 hx8_1 hx0_1 hx1_1 hx2_1 hs0_1 hs16_1).trans fun s2 h2 => ?_
  rcases h2 with ⟨hpc2, hstat2, hR2, hM2, hx8_2, hx0_2, hx1_2, hx2_2, hx10_2, hx11_2, hq2_2, hq0_2, hs0_2, hs16_2⟩
  refine (nfs_chunk2_ext (s₀ := s₀.setMem s.mem) hlen hal hpc2 hstat2 hR2 hM2 hx8_2 hx0_2 hx1_2 hx2_2 hx10_2 hx11_2
    (hq2_2.trans hq2_1) (hq0_2.trans hq0_1) hk0_1 hs0_2 hs16_2).trans fun s3 h3 => ?_
  rcases h3 with ⟨hpc3, hstat3, hR3, hM3, hx8_3, hx0_3, hx1_3, hx2_3, hx11_3, hx9_3, hs0_3, hs16_3, hs32_3, hs48_3⟩
  refine (nfs_chunk3_ext hlen hpc3 hstat3 hR3 hM3 hx8_3 hx0_3 hx1_3 hx2_3 hx11_3 hx9_3
    hs0_3 hs16_3 hs32_3 hs48_3).trans fun s4 h4 => ?_
  rcases h4 with ⟨hpc4, hstat4, hR4, hM4, hx8_4, hx0_4, hx1_4, hx2_4, hx9_4, hx10_4, hs0_4, hs16_4, hs32_4, hs48_4⟩
  exact nfs_chunk4_ext (s₀ := s₀.setMem s.mem) hlen hal hb hpc4 hstat4 hR4 hM4 hx8_4 hx0_4 hx1_4 hx2_4 hx9_4 hx10_4
    hs0_4 hs16_4 hs32_4 hs48_4

set_option maxHeartbeats 1600000 in
theorem nfs_opad_chunk0_ext {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hs : NfsOpadPostHook b F s₀ key s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (NfsOpadMidState (bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1480)) 304#64 305#64 b s₀ s.mem (xorChunk s.mem (nfsSp s₀ + 288#64))) := by
  generalize hPost : (NfsOpadMidState _ _ _ _ _ _ _) = Post
  have hpc := hs.pc_eq
  have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hrw : s.mem.RW (nfsSp s₀) 544 := hs.memInv.rw_stack
  iterate 54 sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, Memory.read128, BitVec.add_assoc],
    by simp (config := { decide := true }) only [arm64_norm, Memory.read128, BitVec.add_assoc],
    by simp only [xorChunk, BitVec.add_assoc, arm64_norm]⟩

set_option maxHeartbeats 1600000 in
theorem nfs_opad_chunk1_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {m_init m_cur : Memory}
    (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : NfsOpadMidState (bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1480)) 304#64 305#64 b s₀ m_init m_cur s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (NfsOpadMidState (bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1672)) 320#64 321#64 b s₀ m_init (xorChunk s.mem (nfsSp s₀ + 304#64))) := by
  generalize hPost : (NfsOpadMidState _ _ _ _ _ _ _) = Post
  have hpc := hs.pc_eq
  have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hx0 := hs.x0_eq
  have hx1 := hs.x1_eq
  have hx8 := hs.x8_eq
  have hx10 := hs.x10_eq
  have hx11 := hs.x11_eq
  have hq0 := hs.q0_eq
  have hq1 := hs.q1_eq
  have hrw : s.mem.RW (nfsSp s₀) 544 := hs.mem_eq ▸ hrw_cur
  iterate 48 sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx8],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hq0],
    by simp (config := { decide := true }) only [arm64_norm, hq1],
    by simp only [xorChunk, BitVec.add_assoc, arm64_norm]⟩

set_option maxHeartbeats 1600000 in
theorem nfs_opad_chunk2_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {m_init m_cur : Memory}
    (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : NfsOpadMidState (bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1672)) 320#64 321#64 b s₀ m_init m_cur s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (NfsOpadMidState (bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1864)) 336#64 337#64 b s₀ m_init (xorChunk s.mem (nfsSp s₀ + 320#64))) := by
  generalize hPost : (NfsOpadMidState _ _ _ _ _ _ _) = Post
  have hpc := hs.pc_eq
  have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hx0 := hs.x0_eq
  have hx1 := hs.x1_eq
  have hx8 := hs.x8_eq
  have hx10 := hs.x10_eq
  have hx11 := hs.x11_eq
  have hq0 := hs.q0_eq
  have hq1 := hs.q1_eq
  have hrw : s.mem.RW (nfsSp s₀) 544 := hs.mem_eq ▸ hrw_cur
  iterate 48 sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx8],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hq0],
    by simp (config := { decide := true }) only [arm64_norm, hq1],
    by simp only [xorChunk, BitVec.add_assoc, arm64_norm]⟩

set_option maxHeartbeats 1600000 in
theorem nfs_opad_chunk3_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {m_init m_cur : Memory}
    (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : NfsOpadMidState (bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1864)) 336#64 337#64 b s₀ m_init m_cur s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (NfsOpadEndState b s₀ m_init (xorChunk s.mem (nfsSp s₀ + 336#64))) := by
  generalize hPost : (NfsOpadEndState _ _ _ _) = Post
  have hpc := hs.pc_eq
  have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hx0 := hs.x0_eq
  have hx1 := hs.x1_eq
  have hx8 := hs.x8_eq
  have hx10 := hs.x10_eq
  have hx11 := hs.x11_eq
  have hq0 := hs.q0_eq
  have hq1 := hs.q1_eq
  have hrw : s.mem.RW (nfsSp s₀) 544 := hs.mem_eq ▸ hrw_cur
  iterate 49 sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1], by simp only [arm64_norm],
    by simp only [xorChunk, Memory.write128, Memory.read128, BitVec.add_assoc, arm64_norm]⟩

theorem nfs_opad_after_compress1_ext {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {s₀ s1 : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (h1 : NfsOpadPostHook b F s₀ key s1) :
    RunsTo (tripleRatchetProgAtExt b ext) s1
      (NfsPreCompress2 b F s₀ key) := by
  have hopad_len : ((keyBlock key).map (· ^^^ 0x5c#8)).length = 64 := by
    simp [keyBlock_length hlen]
  have hiv_len : (shaStateBytes sha256IV).length = 32 :=
    shaStateBytes_length sha256IV
  refine (nfs_opad_chunk0_ext h1).trans fun s2 h2 => ?_
  have hrw1 : (xorChunk s1.mem (nfsSp s₀ + 288#64)).RW (nfsSp s₀) 544 :=
    rw_xorChunk _ h1.memInv.rw_stack
  refine (nfs_opad_chunk1_ext hrw1 h2).trans fun s3 h3 => ?_
  have hrw2 : (xorChunk s2.mem (nfsSp s₀ + 304#64)).RW (nfsSp s₀) 544 :=
    rw_xorChunk _ (h2.mem_eq ▸ hrw1)
  refine (nfs_opad_chunk2_ext hrw2 h3).trans fun s4 h4 => ?_
  have hrw3 : (xorChunk s3.mem (nfsSp s₀ + 320#64)).RW (nfsSp s₀) 544 :=
    rw_xorChunk _ (h3.mem_eq ▸ hrw2)
  refine (nfs_opad_chunk3_ext hrw3 h4).mono fun s5 h5 => ?_
  have hm4 : xorChunk s4.mem (nfsSp s₀ + 336#64) =
      s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8)) := by
    rw [h4.mem_eq, h3.mem_eq, h2.mem_eq]
    have ha1 : nfsSp s₀ + 304#64 = (nfsSp s₀ + 288#64) + 16#64 := by clear * -; bv_omega
    have ha2 : nfsSp s₀ + 320#64 = (nfsSp s₀ + 288#64) + 32#64 := by clear * -; bv_omega
    have ha3 : nfsSp s₀ + 336#64 = (nfsSp s₀ + 288#64) + 48#64 := by clear * -; bv_omega
    rw [ha1, ha2, ha3, xorChunk4_eq_writeBytes, h1.blk_eq, map_xor_0x36_0x6a]
  have hmem5 : s5.mem =
      (((s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))).writeBytes
        (nfsSp s₀ + 176#64) (shaStateBytes sha256IV)).write64 (nfsSp s₀ + 208#64) 1#64) := by
    rw [h5.mem_eq, hm4, write128_pair_ivsw _ s1.mem (nfsSp s₀) h1.ivsw_eq]
  have hM5 : NfsMemInv b s₀ s5.mem := by
    rw [hmem5]
    exact ((h1.memInv.writeBytes_low 288#64 _ (by rw [hopad_len]; decide)).writeBytes_low
      176#64 _ (by rw [hiv_len]; decide)).write64_low 208#64 1#64 (by decide)
  have hA_opad := CryptoHmacSha256.AgreesOutside.writeBytes_self s1.mem (nfsSp s₀ + 288#64)
    ((keyBlock key).map (· ^^^ 0x5c#8))
  have hA_iv := CryptoHmacSha256.AgreesOutside.writeBytes_self
    (s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8)))
    (nfsSp s₀ + 176#64) (shaStateBytes sha256IV)
  have hA_208 := AgreesOutside.write64_self
    ((s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))).writeBytes
      (nfsSp s₀ + 176#64) (shaStateBytes sha256IV))
    (nfsSp s₀ + 208#64) 1#64
  refine {
    pc_eq := h5.pc_eq
    status := h5.status
    regInv := h5.regInv
    memInv := hM5
    x0_eq := h5.x0_eq
    x1_eq := h5.x1_eq
    x2_eq := h5.x2_eq
    ist_eq := by
      rw [hmem5,
          (agreesOutside_toFrame hA_208).readBytes_eq
            (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
          (agreesOutside_toFrame hA_iv).readBytes_eq
            (by rw [hiv_len]; clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
          (agreesOutside_toFrame hA_opad).readBytes_eq
            (by rw [hopad_len]; clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
          h1.ist_eq]
    blk_eq := by
      rw [hmem5,
          (agreesOutside_toFrame hA_208).readBytes_eq
            (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
          (agreesOutside_toFrame hA_iv).readBytes_eq
            (by rw [hiv_len]; clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide)]
      exact CryptoHmacSha256.Layout.readBytes_writeBytes_eq s1.mem (nfsSp s₀ + 288#64) _ 64 hopad_len (by decide)
    ost_eq := by
      rw [hmem5,
          (agreesOutside_toFrame hA_208).readBytes_eq
            (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide)]
      exact CryptoHmacSha256.Layout.readBytes_writeBytes_eq _ (nfsSp s₀ + 176#64) _ 32 hiv_len (by decide)
    obl_eq := by
      rw [hmem5, Memory.read64_write64_same]
  }

set_option maxHeartbeats 1600000 in
theorem nfs_epilogue_ext {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hs : NfsPostCompress2 b F s₀ key s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  generalize hPost : (fun s' : State => _) = Post
  have hpc := hs.pc_eq
  have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hM := hs.memInv
  have hm_ost := hs.ost_eq
  have hm_ist := hs.ist_eq
  have hm_208 := hs.obl_eq
  have hm_432 := hM.saved.m432
  have hm_464 := hM.saved.m464
  have hm_472 := hM.saved.m472
  have hm_480 := hM.saved.m480
  have hm_496 := hM.saved.m496
  have hm_504 := hM.saved.m504
  have hm_512 := hM.saved.m512
  have hm_520 := hM.saved.m520
  have hm_528 := hM.saved.m528
  have hm_536 := hM.saved.m536
  have hrw_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hrw_out : s.mem.RW (s₀.readReg64 .x0) 0x98 := hM.rw_out
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hcross1 := read64_sp_write8_out hM.disj_out_stack
  have hcross2 := read64_sp_write64_out hM.disj_out_stack
  have hcross3 := read64_sp_write64_out_zero hM.disj_out_stack
  have hcross4 := read64_out_write64_sp hM.disj_out_stack
  have hcross5 := read64_out_zero_write64_sp hM.disj_out_stack
  have hcross6 := read8_out_write64_sp hM.disj_out_stack
  iterate 25 sess_step
  subst hPost
  refine RunsTo.refl ?_
  have hsp_restore : nfsSp s₀ + 544#64 = s₀.sp := (nfs_sp_eq_add s₀).symm
  have hpos_addr : (s₀.readReg64 .x0 + 8#64) + 0x3f#64 = s₀.readReg64 .x0 + 71#64 := by clear * -; bv_omega
  have hist_addr : (s₀.readReg64 .x0 + 8#64) + 0x40#64 = s₀.readReg64 .x0 + 72#64 := by clear * -; bv_omega
  have hibl_addr : (s₀.readReg64 .x0 + 8#64) + 0x60#64 = s₀.readReg64 .x0 + 104#64 := by clear * -; bv_omega
  have host_addr : (s₀.readReg64 .x0 + 8#64) + 0x68#64 = s₀.readReg64 .x0 + 112#64 := by clear * -; bv_omega
  have hobl_addr : (s₀.readReg64 .x0 + 8#64) + 0x88#64 = s₀.readReg64 .x0 + 144#64 := by clear * -; bv_omega
  refine ⟨by simp only [arm64_norm], by simp only [arm64_norm, hstat], ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp only [arm64_norm, hsp_restore], ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := { decide := true }) only [arm64_norm, hx25, hx26, hx27]
  · simp (config := { decide := true }) only [arm64_norm, *]
  · refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpos_addr]
      simp (config := { decide := true }) only [arm64_norm, *]
    · rw [hist_addr, ← hm_ist]
      refine readBytes_32_eq_of_read64_eq _ s.mem (s₀.readReg64 .x0 + 72#64) (nfsSp s₀ + 400#64)
        ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, *]
    · rw [hibl_addr]
      simp (config := { decide := true }) only [arm64_norm, *]
    · rw [host_addr, ← hm_ost]
      refine readBytes_32_eq_of_read64_eq _ s.mem (s₀.readReg64 .x0 + 112#64) (nfsSp s₀ + 176#64)
        ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, *]
    · rw [hobl_addr]
      simp (config := { decide := true }) only [arm64_norm, *]
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC, State.setPC]
    refine Frame.write64_out ?_ 80#64 _
    refine Frame.write64_out ?_ 72#64 _
    refine Frame.write64_out ?_ 144#64 _
    refine Frame.write64_out ?_ 136#64 _
    refine Frame.write64_stack ?_ 56#64 _
    refine Frame.write64_stack ?_ 48#64 _
    refine Frame.write64_stack ?_ 40#64 _
    refine Frame.write64_stack ?_ 32#64 _
    refine Frame.write64_out ?_ 96#64 _
    refine Frame.write64_out ?_ 88#64 _
    refine Frame.write64_out ?_ 128#64 _
    refine Frame.write64_out ?_ 120#64 _
    refine Frame.write64_out ?_ 112#64 _
    refine Frame.write64_out ?_ 104#64 _
    refine Frame.write64_out_zero ?_ 0#64
    refine Frame.write64_stack ?_ 104#64 _
    refine Frame.write64_stack ?_ 96#64 _
    refine Frame.write64_stack ?_ 88#64 _
    refine Frame.write64_stack ?_ 80#64 _
    refine Frame.write64_stack ?_ 72#64 _
    refine Frame.write64_stack ?_ 64#64 _
    refine Frame.write8_out ?_ 71#64 _
    exact hM.frame

end CryptoVerification.LibsignalTripleRatchet.HkdfExt.NfsSteps
