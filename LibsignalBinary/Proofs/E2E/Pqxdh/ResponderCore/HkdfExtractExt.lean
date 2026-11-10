/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfStubsExt
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfFinGenExt
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.NewFromSliceExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.NewFromSliceStepsExt

/-!
# `.inImage`-Free `Hmac::new_from_slice` and `pqxdhHkdfExtractSome_ok`

Proves `.inImage`-free `Hmac<Sha256>::new_from_slice` (`16928` B stack) and
`pqxdhHkdfExtractSome_ok_of_stubsExt` (`salt = some`, `32`-B salt and IKM) on
`tripleRatchetProgAtExt img.base ext` under `img.RoDataLoaded`, without `img.FrozenLoaded` or
`s.symtab = img.symtab`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExtractX
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState)
open CryptoVerification.E2E.Pqxdh.Initiator

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

theorem HkdfStubsExt.memsetStep {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)} (hS : HkdfStubsExt b F ext) :
    MemsetStepExt b ext :=
  fun hpc hstat hx0 hx1 hx2 hrw_dst hrw_stk hd_dst_stk hsp_al =>
    memset_stub_runsTo hS.memset hpc hstat hx0 hx1 hx2 hrw_dst hrw_stk hd_dst_stk hsp_al

theorem HkdfStubsExt.compressOneStep {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)} (hS : HkdfStubsExt b F ext) :
    CompressOneStepExt b F ext :=
  fun hpc hstat hx0 hx1 hx2 hst hblk hrw_st hrw_blk hrw_stk hd_sb hd_ss hd_bs hsp_al =>
    compress256_one_stub_runsTo hS.compress256 (by decide)
      hpc hstat hx0 hx1 hx2 hst hblk hrw_st hrw_blk hrw_stk hd_sb hd_ss hd_bs hsp_al

/-! ## `.inImage`-Free `new_from_slice` under `img.RoDataLoaded` -/

section NewFromSliceRO

open CryptoVerification.LibsignalTripleRatchet.HkdfExt.NfsSteps
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.NfsExt

private theorem nfs_compress1_ro_ext {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hComp : subroutine_ok (tripleRatchetProgAtExt b ext)
      (b + bv% (ls_off% "sha2::sha256::compress256"))
      (HkdfExt.compress256ExternShaSpec F extHookStack))
    {s₀ s : State} {m₀ : Memory} {key : List (BitVec 8)}
    (hd_stk_ext : DisjointRegions (CryptoHmacSha256.nfsSp s₀) 544 (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384)
    (hd_iv_ext : DisjointRegions (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384)
    (hrw_extstk : RW s.mem (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384)
    (hpc : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1260))
    (hstat : s.status = .Running)
    (hR : CryptoHmacSha256.NfsRegInv b (s₀.setMem m₀) s)
    (hM : CryptoHmacSha256.NfsMemInv b (s₀.setMem m₀) s.mem)
    (hx0 : s.readReg64 .x0 = CryptoHmacSha256.nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = CryptoHmacSha256.nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (CryptoHmacSha256.nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (CryptoHmacSha256.nfsSp s₀ + 288#64) 64 = (CryptoHmacSha256.keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (CryptoHmacSha256.nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s (fun s' =>
      CryptoHmacSha256.NfsOpadPostHook b F (s₀.setMem s'.mem) key s' ∧
      RW s'.mem (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384 ∧
      Extract.S2Frame s.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)]) := by
  have hbl : Extract.RunsToE (tripleRatchetProgAtExt b ext) s (fun s1 =>
      s1 = (s.writeReg64 .lr (b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1264))).setPC (b + bv% (ls_off% "sha2::sha256::compress256"))) :=
    Extract.RunsTo.toE (nfs_bl_compress1_ext hpc hstat)
  refine hbl.trans_full fun s1 hs1 _ _ => ?_
  have hmem1 : s1.mem = s.mem := by rw [hs1]; rfl
  have hsp1 : s1.sp = CryptoHmacSha256.nfsSp s₀ := by rw [hs1]; exact hR.sp_eq
  have hpc1 : s1.pc = b + bv% (ls_off% "sha2::sha256::compress256") := by rw [hs1]; rfl
  have hstat1 : s1.status = .Running := by rw [hs1]; exact hstat
  have hx0_1 : s1.readReg64 .x0 = CryptoHmacSha256.nfsSp s₀ + 400#64 := by rw [hs1]; exact hx0
  have hx1_1 : s1.readReg64 .x1 = CryptoHmacSha256.nfsSp s₀ + 288#64 := by rw [hs1]; exact hx1
  have hx2_1 : s1.readReg64 .x2 = 1#64 := by rw [hs1]; exact hx2
  have hist1 : s1.mem.readBytes (CryptoHmacSha256.nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV := by
    rw [hmem1]; exact hist
  have hblk1 : s1.mem.readBytes (CryptoHmacSha256.nfsSp s₀ + 288#64) 64 = (CryptoHmacSha256.keyBlock key).map (· ^^^ 0x36#8) := by
    rw [hmem1]; exact hblk
  have hal1 : (s1.sp &&& 15#64) = 0#64 := by rw [hsp1]; exact hR.sp_align
  have hrw_stk : RW s.mem (CryptoHmacSha256.nfsSp s₀) 544 := hM.rw_stack
  have hrw_st : RW s1.mem (CryptoHmacSha256.nfsSp s₀ + 400#64) 32 := by
    rw [hmem1]; exact hrw_stk.sub (by clear * -; bv_omega)
  have hrw_blk : RW s1.mem (CryptoHmacSha256.nfsSp s₀ + 288#64) 64 := by
    rw [hmem1]; exact hrw_stk.sub (by clear * -; bv_omega)
  have hd_st_blk : DisjointRegions (CryptoHmacSha256.nfsSp s₀ + 400#64) 32 (CryptoHmacSha256.nfsSp s₀ + 288#64) 64 := by
    clear * -; simp only [DisjointRegions]; bv_omega
  have hd_st_stk : DisjointRegions (CryptoHmacSha256.nfsSp s₀ + 400#64) 32
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]; exact hd_stk_ext.sub_left (CryptoHmacSha256.nfsSp s₀ + 400#64) ⟨by decide, by clear * -; bv_omega⟩
  have hd_blk_stk : DisjointRegions (CryptoHmacSha256.nfsSp s₀ + 288#64) 64
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]; exact hd_stk_ext.sub_left (CryptoHmacSha256.nfsSp s₀ + 288#64) ⟨by decide, by clear * -; bv_omega⟩
  have hcomp := compress256_one_stub_runsTo hComp (by decide)
    hpc1 hstat1 hx0_1 hx1_1 hx2_1 hist1 hblk1
    hrw_st hrw_blk (by rw [hmem1, hsp1]; exact hrw_extstk)
    hd_st_blk hd_st_stk hd_blk_stk hal1
  refine hcomp.mono fun s' ⟨hpc', hstat', hcc, hist', hblk', hfr⟩ => ?_
  have hfr' : Extract.S2Frame s.mem s'.mem [(CryptoHmacSha256.nfsSp s₀ + 400#64, 32),
      (CryptoHmacSha256.nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hmem1, hsp1] at hfr
  subst hs1
  refine ⟨{
    pc_eq := hpc'
    status := hstat'
    regInv := NfsRegInv_setMem_iff.mpr (HkdfExt.NfsSteps.nfsRegInv_of_cc (NfsRegInv_setMem_iff.mp hR) hcc)
    memInv := NfsMemInv.of_s2Frame_low hM hd_stk_ext hd_iv_ext hfr' ⟨by decide, by decide⟩
    ist_eq := hist'
    blk_eq := hblk'
    ivsw_eq := by
      have h0 : s'.mem.readBytes (CryptoHmacSha256.nfsSp s₀ + 0#64) 32 = s.mem.readBytes (CryptoHmacSha256.nfsSp s₀ + 0#64) 32 :=
        s2Frame_hook_readBytes_stack_eq hfr' hrw_stk hd_stk_ext ⟨by decide, by decide⟩ (by decide)
      rw [BitVec.add_zero] at h0
      exact h0.trans hivsw
  }, hfr'.rw_of_rw _ _ hrw_extstk, s2Frame_of_hook_frame_16928 hfr' rfl (by decide)⟩

private theorem nfs_compress2_ro_ext {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hComp : subroutine_ok (tripleRatchetProgAtExt b ext)
      (b + bv% (ls_off% "sha2::sha256::compress256"))
      (HkdfExt.compress256ExternShaSpec F extHookStack))
    {s₀ s : State} {m₀ : Memory} {key : List (BitVec 8)}
    (hd_stk_ext : DisjointRegions (CryptoHmacSha256.nfsSp s₀) 544 (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384)
    (hd_iv_ext : DisjointRegions (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384)
    (hrw_extstk : RW s.mem (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384)
    (hs : CryptoHmacSha256.NfsPreCompress2 b F (s₀.setMem m₀) key s) :
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s (fun s' =>
      CryptoHmacSha256.NfsPostCompress2 b F (s₀.setMem s'.mem) key s' ∧
      Extract.S2Frame s.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)]) := by
  have hR := hs.regInv
  have hM := hs.memInv
  have hrw_stk : RW s.mem (CryptoHmacSha256.nfsSp s₀) 544 := hM.rw_stack
  have hbl : Extract.RunsToE (tripleRatchetProgAtExt b ext) s (fun s1 =>
      s1 = (s.writeReg64 .lr (b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 2064))).setPC (b + bv% (ls_off% "sha2::sha256::compress256"))) :=
    Extract.RunsTo.toE (nfs_bl_compress2_ext hs.pc_eq hs.status)
  refine hbl.trans_full fun s1 hs1 _ _ => ?_
  have hmem1 : s1.mem = s.mem := by rw [hs1]; rfl
  have hsp1 : s1.sp = CryptoHmacSha256.nfsSp s₀ := by rw [hs1]; exact hR.sp_eq
  have hpc1 : s1.pc = b + bv% (ls_off% "sha2::sha256::compress256") := by rw [hs1]; rfl
  have hstat1 : s1.status = .Running := by rw [hs1]; exact hs.status
  have hx0_1 : s1.readReg64 .x0 = CryptoHmacSha256.nfsSp s₀ + 176#64 := by rw [hs1]; exact hs.x0_eq
  have hx1_1 : s1.readReg64 .x1 = CryptoHmacSha256.nfsSp s₀ + 288#64 := by rw [hs1]; exact hs.x1_eq
  have hx2_1 : s1.readReg64 .x2 = 1#64 := by rw [hs1]; exact hs.x2_eq
  have host1 : s1.mem.readBytes (CryptoHmacSha256.nfsSp s₀ + 176#64) 32 = shaStateBytes sha256IV := by
    rw [hmem1]; exact hs.ost_eq
  have hblk1 : s1.mem.readBytes (CryptoHmacSha256.nfsSp s₀ + 288#64) 64 = (CryptoHmacSha256.keyBlock key).map (· ^^^ 0x5c#8) := by
    rw [hmem1]; exact hs.blk_eq
  have hal1 : (s1.sp &&& 15#64) = 0#64 := by rw [hsp1]; exact hR.sp_align
  have hrw_st : RW s1.mem (CryptoHmacSha256.nfsSp s₀ + 176#64) 32 := by
    rw [hmem1]; exact hrw_stk.sub (by clear * -; bv_omega)
  have hrw_blk : RW s1.mem (CryptoHmacSha256.nfsSp s₀ + 288#64) 64 := by
    rw [hmem1]; exact hrw_stk.sub (by clear * -; bv_omega)
  have hd_st_blk : DisjointRegions (CryptoHmacSha256.nfsSp s₀ + 176#64) 32 (CryptoHmacSha256.nfsSp s₀ + 288#64) 64 := by
    clear * -; simp only [DisjointRegions]; bv_omega
  have hd_st_stk : DisjointRegions (CryptoHmacSha256.nfsSp s₀ + 176#64) 32
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]; exact hd_stk_ext.sub_left (CryptoHmacSha256.nfsSp s₀ + 176#64) ⟨by decide, by clear * -; bv_omega⟩
  have hd_blk_stk : DisjointRegions (CryptoHmacSha256.nfsSp s₀ + 288#64) 64
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]; exact hd_stk_ext.sub_left (CryptoHmacSha256.nfsSp s₀ + 288#64) ⟨by decide, by clear * -; bv_omega⟩
  have hcomp := compress256_one_stub_runsTo hComp (by decide)
    hpc1 hstat1 hx0_1 hx1_1 hx2_1 host1 hblk1
    hrw_st hrw_blk (by rw [hmem1, hsp1]; exact hrw_extstk)
    hd_st_blk hd_st_stk hd_blk_stk hal1
  refine hcomp.mono fun s' ⟨hpc', hstat', hcc, host', hblk', hfr⟩ => ?_
  have hfr' : Extract.S2Frame s.mem s'.mem [(CryptoHmacSha256.nfsSp s₀ + 176#64, 32),
      (CryptoHmacSha256.nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hmem1, hsp1] at hfr
  subst hs1
  refine ⟨{
    pc_eq := hpc'
    status := hstat'
    regInv := NfsRegInv_setMem_iff.mpr (HkdfExt.NfsSteps.nfsRegInv_of_cc (NfsRegInv_setMem_iff.mp hR) hcc)
    memInv := NfsMemInv.of_s2Frame_low hM hd_stk_ext hd_iv_ext hfr' ⟨by decide, by decide⟩
    ist_eq := (s2Frame_hook_readBytes_stack_eq hfr' hrw_stk hd_stk_ext
      ⟨by decide, by decide⟩ (by decide)).trans hs.ist_eq
    ost_eq := host'
    obl_eq := (s2Frame_hook_read64_stack_eq hfr' hrw_stk hd_stk_ext
      (by decide) (by decide)).trans hs.obl_eq
  }, s2Frame_of_hook_frame_16928 hfr' rfl (by decide)⟩

/-- `Hmac<Sha256>::new_from_slice` on `tripleRatchetProgAtExt img.base ext` under
`img.RoDataLoaded s₀.mem` (without `img.FrozenLoaded` or `s₀.symtab = img.symtab`). -/
theorem new_from_slice_ro_runsToE_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : HkdfStubsExt img.base F ext)
    {s₀ : State}
    (hro : img.RoDataLoaded s₀.mem)
    (hpc : s₀.pc = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]"))
    (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_key : RW s₀.mem (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hrw_stk : RW s₀.mem (s₀.sp - 544#64) 544)
    (hrw_extstk : RW s₀.mem (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384)
    (hdisj_out_stk : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_stk_extstk : DisjointRegions (s₀.sp - 544#64) 544 (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384)
    (hdisj_key_stk : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hdisj_key_extstk : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Extract.S2Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)]) := by
  intro key
  have hkey_len_eq : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_len : key.length ≤ 64 := hkey_len_eq ▸ hlen
  have hb : (img.base &&& 0xfff#64) = 0#64 := ProofLib.base_aligned_of_loads himg
  obtain ⟨hro_iv, hiv_eq⟩ := CryptoHmacSha256.rodata_sha256IV himg hro
  have hdisj_iv_stk : DisjointRegions (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (CryptoHmacSha256.nfsSp s₀) 544 :=
    CryptoHmacSha256.disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
  have hdisj_iv_extstk : DisjointRegions (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384 :=
    CryptoHmacSha256.disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_extstk
  refine NfsExt.RunsToE.mono_traceEq (P := fun sf =>
      sf.pc = s₀.readReg64 .lr ∧
      sf.status = .Running ∧
      CryptoHmacSha256.CalleeSaved s₀ sf ∧
      sf.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt sf.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Extract.S2Frame s₀.mem sf.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)]) ?_
    fun sf htr ⟨hpc_sf, hstat_sf, hcs_sf, hret_sf, hhm_sf, hfr0f⟩ =>
      ⟨hpc_sf, hstat_sf, CryptoHmacSha256.CallingConventionPreserved_of_calleeSaved hcs_sf htr.2,
        hret_sf, hhm_sf, hfr0f⟩
  have hseg0a : Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s₀ _ :=
    NfsExt.RunsToE.of_runsTo (nfs_seg0a_ext hpc hstat hlen hb hrw_stk hal)
  refine hseg0a.trans_full fun s1 h1 hkf1 _ => ?_
  rcases h1 with ⟨hpc1, hstat1, hsp1, hal1, hx29_1, hx19_1, hx22_1, hx25_1, hx26_1, hx27_1,
    hx0_1, hx1_1, hx2_1, hlr_1, hzero1, hsaved1, hfr1_r7b⟩
  have hro1 : img.RoDataLoaded s1.mem := roDataLoaded_of_keepsFrozen hro hkf1
  have hfr01 : Extract.S2Frame s₀.mem s1.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    s2Frame_of_r7b_stack_frame_16928 hfr1_r7b
  have hrw_stk1 : RW s1.mem (CryptoHmacSha256.nfsSp s₀) 544 := (CryptoHmacSha256.Frame.rw_iff hfr1_r7b _ _).mpr hrw_stk
  have hrw_out1 : RW s1.mem (s₀.readReg64 .x0) 0x98 := (CryptoHmacSha256.Frame.rw_iff hfr1_r7b _ _).mpr hrw_out
  have hrw_extstk1 : RW s1.mem (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384 :=
    (CryptoHmacSha256.Frame.rw_iff hfr1_r7b _ _).mpr hrw_extstk
  have hrw_key1 : RW s1.mem (s₀.readReg64 .x1) key.length :=
    (CryptoHmacSha256.Frame.rw_iff hfr1_r7b _ _).mpr (hkey_len_eq ▸ hrw_key)
  have hkey_s1 : s1.mem.readBytes (s₀.readReg64 .x1) key.length = key := by
    rw [hkey_len_eq]
    rcases hdisj_key_stk with h0 | hd
    · dsimp only [key]; rw [h0]; rfl
    · have hd' : DisjointRegions (CryptoHmacSha256.nfsSp s₀) 544 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := hd.symm
      exact hfr1_r7b.readBytes_eq (by simp [hd']) (by omega)
  have hd_dst_src1 : key.length = 0 ∨ DisjointRegions (CryptoHmacSha256.nfsSp s₀ + 112#64) key.length (s₀.readReg64 .x1) key.length := by
    rw [hkey_len_eq]
    rcases hdisj_key_stk with h0 | hd
    · exact Or.inl h0
    · by_cases hkn0 : (s₀.readReg64 .x2).toNat = 0
      · exact Or.inl hkn0
      · have hd' : DisjointRegions (CryptoHmacSha256.nfsSp s₀) 544 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := hd.symm
        exact Or.inr (hd'.sub_left (CryptoHmacSha256.nfsSp s₀ + 112#64) ⟨by omega, by clear * - hlen; bv_omega⟩)
  have hd_dst_stk1 : key.length = 0 ∨ DisjointRegions (CryptoHmacSha256.nfsSp s₀ + 112#64) key.length
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]
    by_cases hkn0 : key.length = 0
    · exact Or.inl hkn0
    · have hd' : DisjointRegions (CryptoHmacSha256.nfsSp s₀) 544 (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384 := hdisj_stk_extstk
      exact Or.inr (hd'.sub_left (CryptoHmacSha256.nfsSp s₀ + 112#64) ⟨by omega, by clear * - hkey_len; bv_omega⟩)
  have hd_src_stk1 : key.length = 0 ∨ DisjointRegions (s₀.readReg64 .x1) key.length
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1, hkey_len_eq]; exact hdisj_key_extstk
  have hmemcpy1 := memcpy_opt_stub_runsTo hS.memcpy hpc1 hstat1
    hx0_1 hx1_1 (by rw [hx2_1, hkey_len_eq]) hkey_s1
    (hrw_stk1.sub (by clear * - hkey_len; bv_omega)) hrw_key1
    (by rw [hsp1]; exact hrw_extstk1)
    hd_dst_src1 hd_dst_stk1 hd_src_stk1 (by rw [hsp1]; exact hal1)
  refine hmemcpy1.trans_full fun s2 ⟨hpc2, hstat2, hcc12, hx0_2, hdst2, _, hfr12⟩ hkf2 _ => ?_
  rw [hlr_1] at hpc2
  have hro2 : img.RoDataLoaded s2.mem := roDataLoaded_of_keepsFrozen hro1 hkf2
  have hfr12_stk : Extract.S2Frame s1.mem s2.mem
      [(CryptoHmacSha256.nfsSp s₀ + 112#64, key.length), (CryptoHmacSha256.nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hsp1] at hfr12
  have hfr02 : Extract.S2Frame s₀.mem s2.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    hfr01.trans (s2Frame_of_hook_frame_16928 hfr12_stk rfl (by clear * - hkey_len; bv_omega))
  have hkb2 : s2.mem.readBytes (CryptoHmacSha256.nfsSp s₀ + 112#64) 64 = CryptoHmacSha256.keyBlock key :=
    readBytes_64_eq_keyBlock_of_s2Frame hkey_len hrw_stk1 hdisj_stk_extstk hzero1 hdst2 hfr12_stk
  have hsaved2_432 : CryptoHmacSha256.NfsSavedStack s₀ (s2.mem.write64 (CryptoHmacSha256.nfsSp s₀ + 432#64) 1#64) :=
    nfsSavedStack_write64_432_of_s2Frame hsaved1 hrw_stk1 hdisj_stk_extstk hfr12_stk hkey_len
  obtain ⟨hro_iv2, hiv_eq2⟩ := CryptoHmacSha256.rodata_sha256IV himg hro2
  have hread_iv2 : s2.mem.Readable (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 :=
    fun a ha => ⟨by rw [(hro_iv2 a ha).1]; rfl, (hro_iv2 a ha).2⟩
  have hA2_432 : AgreesOutside s2.mem (s2.mem.write64 (CryptoHmacSha256.nfsSp s₀ + 432#64) 1#64) (CryptoHmacSha256.nfsSp s₀ + 432#64) 8 :=
    CryptoHmacSha256.AgreesOutside.write64_self s2.mem (CryptoHmacSha256.nfsSp s₀ + 432#64) 1#64
  have hf2_432 : CryptoHmacSha256.Frame s2.mem (s2.mem.write64 (CryptoHmacSha256.nfsSp s₀ + 432#64) 1#64) [(CryptoHmacSha256.nfsSp s₀ + 432#64, 8)] :=
    CryptoHmacSha256.agreesOutside_toFrame hA2_432
  have hM2_432 : CryptoHmacSha256.NfsMemInv img.base (s₀.setMem s2.mem) (s2.mem.write64 (CryptoHmacSha256.nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (CryptoHmacSha256.Frame.rw_iff hf2_432 _ _).mpr (hfr12_stk.rw_of_rw _ _ hrw_stk1)
    rw_out := (CryptoHmacSha256.Frame.rw_iff hf2_432 _ _).mpr (hfr12_stk.rw_of_rw _ _ hrw_out1)
    readable_iv := (CryptoHmacSha256.Frame.readable_iff hf2_432 _ _).mpr hread_iv2
    iv_bytes := by
      have hd432 : DisjointRegions (CryptoHmacSha256.nfsSp s₀ + 432#64) 8
          (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 := by
        clear * - hdisj_iv_stk; simp only [DisjointRegions, CryptoHmacSha256.nfsSp] at hdisj_iv_stk ⊢; bv_omega
      exact (hf2_432.readBytes_eq (by simp [hd432]) (by decide)).trans hiv_eq2
    disj_iv_stack := hdisj_iv_stk
    disj_out_stack := hdisj_out_stk
    saved := NfsSavedStack_setMem_iff.mpr hsaved2_432
    frame := CryptoHmacSha256.Frame.of_agreesOutside_stack (CryptoHmacSha256.Frame.refl s2.mem _) hA2_432 (by decide)
  }
  have hrw_extstk2 : RW s2.mem (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384 := hfr12_stk.rw_of_rw _ _ hrw_extstk1
  have hto_c1 : Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s2 _ :=
    NfsExt.RunsToE.of_runsTo (nfs_after_memcpy_to_compress1_ext hkey_len hal hb hpc2 hstat2
      (hcc12.1.trans hsp1) hal1
      (hcc12.2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1)
      (hcc12.2.1.trans hx19_1)
      (hcc12.2.2.2.2.1.trans hx22_1)
      (hcc12.2.2.2.2.2.2.2.1.trans hx25_1)
      (hcc12.2.2.2.2.2.2.2.2.1.trans hx26_1)
      (hcc12.2.2.2.2.2.2.2.2.2.1.trans hx27_1)
      hM2_432 hkb2)
  refine hto_c1.trans_full fun s3 ⟨hpc3, hstat3, hR3, hM3, hx0_3, hx1_3, hx2_3, hist3, hblk3, hivsw3⟩ _ _ => ?_
  have hfr03 : Extract.S2Frame s₀.mem s3.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    hfr02.trans (s2Frame_of_r7b_frame_16928 hM3.frame)
  have hrw_extstk3 : RW s3.mem (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384 :=
    (CryptoHmacSha256.Frame.rw_iff hM3.frame _ _).mpr hrw_extstk2
  have hc1 := nfs_compress1_ro_ext hS.compress256 hdisj_stk_extstk hdisj_iv_extstk hrw_extstk3
    hpc3 hstat3 hR3 hM3 hx0_3 hx1_3 hx2_3 hist3 hblk3 hivsw3
  refine hc1.trans_full fun s4 ⟨hpost4, hrw_extstk4, hfr34⟩ _ _ => ?_
  have hfr04 : Extract.S2Frame s₀.mem s4.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    hfr03.trans hfr34
  have hopad : Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s4 _ :=
    NfsExt.RunsToE.of_runsTo (nfs_opad_after_compress1_ext hkey_len hpost4)
  refine hopad.trans_full fun s5 hpre5 _ _ => ?_
  have hfr05 : Extract.S2Frame s₀.mem s5.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    hfr04.trans (s2Frame_of_r7b_frame_16928 hpre5.memInv.frame)
  have hrw_extstk5 : RW s5.mem (CryptoHmacSha256.nfsSp s₀ - 16384#64) 16384 :=
    (CryptoHmacSha256.Frame.rw_iff hpre5.memInv.frame _ _).mpr hrw_extstk4
  have hc2 := nfs_compress2_ro_ext hS.compress256 hdisj_stk_extstk hdisj_iv_extstk hrw_extstk5 hpre5
  refine hc2.trans_full fun s6 ⟨hpost6, hfr56⟩ _ _ => ?_
  have hfr06 : Extract.S2Frame s₀.mem s6.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    hfr05.trans hfr56
  have hep : Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s6 _ :=
    NfsExt.RunsToE.of_runsTo (nfs_epilogue_ext (s₀ := s₀.setMem s6.mem) hal hpost6)
  refine hep.mono fun sf ⟨hpc_sf, hstat_sf, hcs_sf, hret_sf, hhm_sf, hfr6f⟩ => ?_
  exact ⟨hpc_sf, hstat_sf, ⟨hcs_sf.1, hcs_sf.2⟩, hret_sf, hhm_sf,
    hfr06.trans (s2Frame_of_r7b_frame_16928 hfr6f)⟩

theorem nfs_ro_runsTo_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : HkdfStubsExt img.base F ext)
    {s : State} {ret keyA : BitVec 64} {key : List (BitVec 8)}
    (hro : img.RoDataLoaded s.mem)
    (hpc : s.pc = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret)
    (hx1 : s.readReg64 .x1 = keyA)
    (hx2 : (s.readReg64 .x2).toNat = key.length)
    (hkey_le : key.length ≤ 64)
    (hkey_mem : s.mem.readBytes keyA key.length = key)
    (hrw_ret : RW s.mem ret 0x98)
    (hrw_key : RW s.mem keyA key.length)
    (hrw_stk : RW s.mem (s.sp - 16928#64) 16928)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 16928#64) 16928)
    (hd_key_stk : key.length = 0 ∨ DisjointRegions keyA key.length (s.sp - 16928#64) 16928)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧
      HmacSt s'.mem (ret + 8#64) F key [] ∧
      Extract.S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 16928#64, 16928)]) := by
  have hd_key_544 : (s.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s.readReg64 .x1) (s.readReg64 .x2).toNat (s.sp - 544#64) 544 := by
    rw [hx1, hx2]
    rcases hd_key_stk with h0 | hd
    · exact Or.inl h0
    · exact Or.inr (hd.sub_right _ ⟨by decide, by bv_omega⟩)
  have hd_key_ext : (s.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s.readReg64 .x1) (s.readReg64 .x2).toNat (CryptoHmacSha256.nfsSp s - 16384#64) 16384 := by
    rw [hx1, hx2]
    rcases hd_key_stk with h0 | hd
    · exact Or.inl h0
    · exact Or.inr (hd.sub_right _ ⟨by decide, by simp only [CryptoHmacSha256.nfsSp]; bv_omega⟩)
  have hrun := new_from_slice_ro_runsToE_ext himg hS hro hpc hstat (hx2 ▸ hkey_le)
    (hx0 ▸ hrw_ret) (by rw [hx1, hx2]; exact hrw_key)
    (hrw_stk.sub (by bv_omega))
    (hrw_stk.sub (by simp only [CryptoHmacSha256.nfsSp]; bv_omega))
    (by rw [hx0]; exact hd_ret_stk.sub_right _ ⟨by decide, by bv_omega⟩)
    (by simp only [DisjointRegions, CryptoHmacSha256.nfsSp]; bv_omega)
    hd_key_544 hd_key_ext hsp_al
  refine hrun.mono fun s' hs' => ?_
  rw [hx0, hx1, hx2, hkey_mem] at hs'
  exact hs'

theorem nfs32_ro_runsTo_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : HkdfStubsExt img.base F ext)
    {s : State} {ret keyA : BitVec 64} {key : List (BitVec 8)}
    (hro : img.RoDataLoaded s.mem)
    (hpc : s.pc = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret)
    (hx1 : s.readReg64 .x1 = keyA)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hkey_len : key.length = 32)
    (hkey_mem : s.mem.readBytes keyA 32 = key)
    (hrw_ret : RW s.mem ret 0x98)
    (hrw_key : RW s.mem keyA 32)
    (hrw_stk : RW s.mem (s.sp - 16928#64) 16928)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 16928#64) 16928)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 16928#64) 16928)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧
      HmacSt s'.mem (ret + 8#64) F key [] ∧
      Extract.S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 16928#64, 16928)]) :=
  nfs_ro_runsTo_ext himg hS hro hpc hstat hx0 hx1 (by rw [hx2, hkey_len]; rfl)
    (by omega) (by rwa [hkey_len]) hrw_ret (by rwa [hkey_len]) hrw_stk
    hd_ret_stk (Or.inr (by rwa [hkey_len])) hsp_al

end NewFromSliceRO

/-! ## `pqxdhHkdfExtractSome_ok_of_stubsExt` (`32`-B Salt, `32`-B IKM) -/

section ExtractSomeRO

private theorem nfs1_ro_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : HkdfStubsExt img.base C.F ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hro0 : img.RoDataLoaded s0.mem)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hRW_salt : RW s0.mem (saltPtrOf sp0 x) 32)
    (hd_salt_16928 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 16928#64) 16928)
    (hsalt_none0 : x.salt = none → x.saltA = 0#64)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs1X img.base x s0 sp0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s (ERet1X img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hsalt_some_ne, hsalt_mem⟩
  have hreg_eq : saltRegOf sp0 x = saltPtrOf sp0 x := by
    cases hxs : x.salt with
    | none => simp [saltRegOf, saltPtrOf, hxs, hsalt_none0 hxs]
    | some sv => simp [saltRegOf, saltPtrOf, hxs, hsalt_some_ne sv hxs]
  have hlen32 : (saltSliceOf x).length = 32 := by
    cases hxs : x.salt with
    | none => simp [saltSliceOf, hxs, hsalt_none0 hxs]
    | some sv => simp [saltSliceOf, hxs]
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 16928#64)).toNat + 0x98 ≤ 17360 := by
    have heq : (sp0 + 176#64) - (sp0 - 16928#64) = 17104#64 := by bv_lin
    rw [heq]; decide
  have hsub_16928 : 0 < 16928 ∧ ((sp0 - 16928#64) - (sp0 - 16928#64)).toNat + 16928 ≤ 17360 := by
    have heq : (sp0 - 16928#64) - (sp0 - 16928#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 16928#64)).toNat + 96 ≤ 17360 := by
    have heq : (sp0 + 336#64) - (sp0 - 16928#64) = 17264#64 := by bv_lin
    rw [heq]; decide
  have hrun := nfs32_ro_runsTo_ext himg hS (roDataLoaded_of_keepsFrozen hro0 hkf)
    hpc hstat hx0 (hx1.trans hreg_eq) (by rw [hx2, hlen32])
    hlen32 (by rwa [hlen32] at hsalt_mem)
    (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_x0.2))
    (hframe.rw_of_rw _ _ hRW_salt)
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_16928.2))
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 16928#64 16928 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact hd_salt_16928)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8, hmacSt_saltSliceOf] at hhm
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 16928#64 16928 336#64 96 (by decide)
  have hframe' : ExtFrameX s0 sp0 s'.mem :=
    ExtFrameX.trans_pair hframe hfr' hsub_x0.2 hsub_16928.2
  exact ⟨⟨hstat', (Extract.CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (CallingConventionPreserved.x20 hcs).trans hx20,
    (CallingConventionPreserved.x21 hcs).trans hx21, hok, hhm⟩

private theorem seg1b_ro_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hS : HkdfStubsExt img.base C.F ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hRW_ikm : RW s0.mem x.ikmA 32)
    (hikm_len : x.ikm.length = 32)
    (hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 16928#64) 17360)
    (hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EMemcpyX img.base C.F x s0 sp0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s (EC88X img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx21, hx22, hx25, hhm⟩
  have hikm_s : s.mem.readBytes x.ikmA 32 = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ (by decide)]
    · exact hikm_mem0
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hd_ikm_out.symm
      · exact hd_ikm_stk.symm
  have hsub_432 : (sp0 - (sp0 - 16928#64)).toNat + 432 ≤ 17360 := by
    have heq : sp0 - (sp0 - 16928#64) = 16928#64 := by bv_lin
    rw [heq]; decide
  have hsub_32 : 0 < 32 ∧ (sp0 - (sp0 - 16928#64)).toNat + 32 ≤ 17360 := by
    have heq : sp0 - (sp0 - 16928#64) = 16928#64 := by bv_lin
    rw [heq]; decide
  have hsub_ext : 0 < 16384 ∧ ((sp0 - 16384#64) - (sp0 - 16928#64)).toNat + 16384 ≤ 17360 := by
    have heq : (sp0 - 16384#64) - (sp0 - 16928#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 16928#64)).toNat + 96 ≤ 17360 := by
    have heq : (sp0 + 336#64) - (sp0 - 16928#64) = 17264#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stkX_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_32 : s.mem.RW sp0 32 :=
    rw_sp0_sub hrw_sp0_s sp0 32 (by rw [BitVec.sub_self]; decide)
  have hrw_ikm_s : s.mem.RW x.ikmA 32 :=
    hframe.rw_of_rw x.ikmA 32 hRW_ikm
  have hrw_ext_s : s.mem.RW (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp]
    exact hframe.rw_of_rw (sp0 - 16384#64) 16384 (rw_stkX_sub hRW_stk (sp0 - 16384#64) 16384 hsub_ext.2)
  have hd_dst_src : DisjointRegions sp0 32 x.ikmA 32 :=
    (disj_stkX_sub_right hd_ikm_stk sp0 32 hsub_32).symm
  have hd_dst_ext : DisjointRegions sp0 32 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp]
    simpa [BitVec.add_zero, extHookStack] using
      (disj_sp0_sub_off sp0 16384#64 16384 0#64 32 (by decide)).symm
  have hd_src_ext : DisjointRegions x.ikmA 32 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp]
    exact disj_stkX_sub_right hd_ikm_stk (sp0 - 16384#64) 16384 hsub_ext
  have hmc := memcpy_stub_runsTo hS.memcpy (bs := x.ikm)
    hpc hstat hx0 hx1
    (by rw [hx2, hikm_len]; rfl)
    (by rw [hikm_len]; exact hikm_s)
    (by rw [hikm_len]; exact hrw_sp0_32)
    (by rw [hikm_len]; exact hrw_ikm_s)
    hrw_ext_s
    (by rw [hikm_len]; exact hd_dst_src)
    (by rw [hikm_len]; exact hd_dst_ext)
    (by rw [hikm_len]; exact hd_src_ext)
    (by rw [hsp]; exact hsp_al)
  refine hmc.trans fun s1 hs1 => ?_
  rcases hs1 with ⟨hpc1, hstat1, hcc1, _, hdst1, _, hfr_mc⟩
  rw [hsp, hikm_len] at hfr_mc
  rw [hikm_len] at hdst1
  have hpc1' : s1.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 192) :=
    hpc1.trans hlr
  have hsp1 : s1.sp = sp0 := (Extract.CallingConventionPreserved.sp_eq hcc1).trans hsp
  have hx19_1 : s1.readReg64 .x19 = s0.readReg64 .x0 := (CallingConventionPreserved.x19 hcc1).trans hx19
  have hx21_1 : s1.readReg64 .x21 = 32#64 := (CallingConventionPreserved.x21 hcc1).trans hx21
  have hx22_1 : s1.readReg64 .x22 = sp0 + 176#64 := (CallingConventionPreserved.x22 hcc1).trans hx22
  have hx25_1 : s1.readReg64 .x25 = 0#64 := hcc1.2.2.2.2.2.2.2.1.trans hx25
  have hx27_1 : s1.readReg64 .x27 = s0.readReg64 .x27 := (CallingConventionPreserved.x27 hcc1).trans hx27
  have hx29_1 : s1.readReg64 .x29 = sp0 + 336#64 := (CallingConventionPreserved.x29 hcc1).trans hx29
  have hsaved1 : ExtSaved s0 sp0 s1.mem := by
    refine hsaved.of_s2frame hfr_mc (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_zero_off sp0 32 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 16384#64 16384 336#64 96 (by decide)
  have hframe1 : ExtFrameX s0 sp0 s1.mem :=
    ExtFrameX.trans_pair hframe hfr_mc hsub_32.2 hsub_ext.2
  have hrw_sp0 : s1.mem.RW sp0 432 :=
    hframe1.rw_of_rw sp0 432 (rw_stkX_sub hRW_stk sp0 432 hsub_432)
  have htail : RunsTo (tripleRatchetProgAtExt img.base ext) s1 (EC88X img.base C.F x s0 sp0) := by
    iterate 3 s2_step
    refine RunsTo.refl ?_
    have hag : AgreesOutside s1.mem (s1.mem.write8 (sp0 + 63#64) 32#8) sp0 328 :=
      agreesOutside_sp0_write8 (AgreesOutside.rfl' s1.mem sp0 328) (by decide)
    unfold EC88X ExtCommonX
    simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
      State.readReg64_advancePC, State.readReg64_writeReg64,
      Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_false]
    dsimp only [State.setMem, State.setPC, State.advancePC, State.writeReg64]
    exact ⟨⟨hstat1, hsp1, hx19_1, hx27_1, hx29_1,
      hsaved1.of_agreesOutside_328 hag,
      ExtFrameX.of_agreesOutside_sp0 hframe1 (by decide) hag⟩,
      rfl, hx22_1, hmacSt_of_memcpy_32_write8_pos hhm hrw_sp0_s hikm_len hdst1 hfr_mc⟩
  exact Extract.RunsTo.toE htail

private theorem fin_ro_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hS : HkdfStubsExt img.base C.F ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hikm_len : x.ikm.length = 32)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFinX img.base C.F x s0 sp0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s (ERetFinX img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx22, hhm⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 16928#64)).toNat + 32 ≤ 17360 := by
    have heq : (sp0 + 144#64) - (sp0 - 16928#64) = 17072#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x90 ∧ ((sp0 + 176#64) - (sp0 - 16928#64)).toNat + 0x90 ≤ 17360 := by
    have heq : (sp0 + 176#64) - (sp0 - 16928#64) = 17104#64 := by bv_lin
    rw [heq]; decide
  have hsub_m16528 : 0 < 16528 ∧ ((sp0 - 16528#64) - (sp0 - 16928#64)).toNat + 16528 ≤ 17360 := by
    have heq : (sp0 - 16528#64) - (sp0 - 16928#64) = 400#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 16928#64)).toNat + 96 ≤ 17360 := by
    have heq : (sp0 + 336#64) - (sp0 - 16928#64) = 17264#64 := by bv_lin
    rw [heq]; decide
  have hfin := finalize_fixed_single_runsToE_base hS.memsetStep hS.compressOneStep
    hpc hstat hx0 hx1
    (by rw [effectiveSalt_length]; decide)
    (by omega)
    hhm
    (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_144.2))
    (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_176.2))
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_m16528.2))
    (disj_sp0_off sp0 144#64 32 176#64 0x90 (by decide))
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 16528#64 16528 144#64 32 (by decide)).symm)
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 16528#64 16528 176#64 0x90 (by decide)).symm)
    (by rw [hsp]; exact hsp_al)
  refine hfin.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcc, hout, hfr'⟩
  rw [hsp] at hfr'
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact disj_sp0_off sp0 144#64 32 336#64 96 (by decide)
    · exact disj_sp0_off sp0 176#64 0x90 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 16528#64 16528 336#64 96 (by decide)
  have hframe' : ExtFrameX s0 sp0 s'.mem :=
    ExtFrameX.trans_triple hframe hfr' hsub_144.2 hsub_176.2 hsub_m16528.2
  exact ⟨⟨hstat', (Extract.CallingConventionPreserved.sp_eq hcc).trans hsp,
    (CallingConventionPreserved.x19 hcc).trans hx19,
    (CallingConventionPreserved.x27 hcc).trans hx27,
    (CallingConventionPreserved.x29 hcc).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (CallingConventionPreserved.x22 hcc).trans hx22, hout⟩

theorem nfs2_ro_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : HkdfStubsExt img.base C.F ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hro0 : img.RoDataLoaded s0.mem)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs2X img.base C.F x s0 sp0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s (ERet2X img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx22, hprk⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 16928#64)).toNat + 32 ≤ 17360 := by
    have heq : (sp0 + 144#64) - (sp0 - 16928#64) = 17072#64 := by bv_lin
    rw [heq]; decide
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 16928#64)).toNat + 0x98 ≤ 17360 := by
    have heq : (sp0 + 176#64) - (sp0 - 16928#64) = 17104#64 := by bv_lin
    rw [heq]; decide
  have hsub_16928 : 0 < 16928 ∧ ((sp0 - 16928#64) - (sp0 - 16928#64)).toNat + 16928 ≤ 17360 := by
    have heq : (sp0 - 16928#64) - (sp0 - 16928#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 16928#64)).toNat + 96 ≤ 17360 := by
    have heq : (sp0 + 336#64) - (sp0 - 16928#64) = 17264#64 := by bv_lin
    rw [heq]; decide
  have hprk_len : (x.prk C.F).length = 32 := by
    dsimp [ExtractGhost.prk, hkdfExtract]
    exact length_hmacWith C.F _ _
  have hrw_144_s : s.mem.RW (sp0 + 144#64) 32 :=
    hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_144.2)
  have hrun := nfs32_ro_runsTo_ext himg hS (roDataLoaded_of_keepsFrozen hro0 hkf)
    hpc hstat hx0 hx1 hx2 hprk_len hprk
    (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_x0.2))
    hrw_144_s
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_16928.2))
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 16928#64 16928 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 16928#64 16928 144#64 32 (by decide)).symm)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8] at hhm
  have hprk' : s'.mem.readBytes (sp0 + 144#64) 32 = x.prk C.F := by
    rw [hfr'.readBytes_eq hrw_144_s ?_ (by decide)]
    · exact hprk
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)).symm
      · exact disj_sp0_sub_off sp0 16928#64 16928 144#64 32 (by decide)
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 16928#64 16928 336#64 96 (by decide)
  have hframe' : ExtFrameX s0 sp0 s'.mem :=
    ExtFrameX.trans_pair hframe hfr' hsub_x0.2 hsub_16928.2
  exact ⟨⟨hstat', (Extract.CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (CallingConventionPreserved.x22 hcs).trans hx22, hok, hprk', hhm⟩

/-- Pure `RunsToE` contract for `extract` (`32`-B IKM) at `17360` B stack under
`img.RoDataLoaded s0.mem`. -/
theorem extract_32_ro_runsToE_ext {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : HkdfStubsExt img.base C.F ext)
    {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract"))
    (hrun : s0.status = .Running)
    (hro0 : img.RoDataLoaded s0.mem)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx2 : x.salt.isSome → s0.readReg64 .x2 = 32#64)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = 32#64)
    (hikm_len : x.ikm.length = 32)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hRW_ikm : RW s0.mem x.ikmA 32)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 16928#64) 17360)
    (hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm)
    (hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0)
    (hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 16928#64) 17360)
    (hsalt_none : x.salt = none → x.saltA = 0#64)
    (hsalt_some : ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ RW s0.mem x.saltA 32 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      DisjointRegions x.saltA 32 (sp0 - 16928#64) 17360) :
    Extract.RunsToE (tripleRatchetProgAtExt img.base ext) s0 (EPostX C.F x s0 sp0) := by
  have hsub_432 : (sp0 - (sp0 - 16928#64)).toNat + 432 ≤ 17360 := by
    have heq : sp0 - (sp0 - 16928#64) = 16928#64 := by bv_lin
    rw [heq]; decide
  have hsub_16928 : 0 < 16928 ∧ ((sp0 - 16928#64) - (sp0 - 16928#64)).toNat + 16928 ≤ 17360 := by
    have heq : (sp0 - 16928#64) - (sp0 - 16928#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := rw_stkX_sub hRW_stk sp0 432 hsub_432
  have hRW_salt : RW s0.mem (saltPtrOf sp0 x) 32 := by
    cases hxs : x.salt with
    | none =>
      rw [saltPtrOf, hxs]
      exact rw_stkX_sub hRW_stk (sp0 + 144#64) 32 (by
        have heq : (sp0 + 144#64) - (sp0 - 16928#64) = 17072#64 := by bv_lin
        rw [heq]; decide)
    | some sv =>
      rw [saltPtrOf, hxs]
      exact (hsalt_some sv hxs).2.1
  have hd_salt_16928 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 16928#64) 16928 := by
    cases hxs : x.salt with
    | none =>
      rw [saltPtrOf, hxs]
      exact (disj_sp0_sub_off sp0 16928#64 16928 144#64 32 (by decide)).symm
    | some sv =>
      rw [saltPtrOf, hxs]
      exact disj_stkX_sub_right (hsalt_some sv hxs).2.2.2 (sp0 - 16928#64) 16928 hsub_16928
  have h0 := Extract.RunsTo.toE (seg0_x_runsTo (img := img) (ext := ext)
    hpc hrun hsp0 hx1 hx2 hx3 hx4 hsp_al hrw_sp0
    (fun h => Or.inl (hsalt_none h))
    (fun sv hsv => ⟨(hsalt_some sv hsv).1, (hsalt_some sv hsv).2.2.1, (hsalt_some sv hsv).2.2.2⟩))
  have h1 := Extract.RunsToE.trans_full h0 fun s hs hkf _ =>
    nfs1_ro_x_runsTo himg hS hro0 hkf hRW_stk hRW_salt hd_salt_16928 hsalt_none hsp_al hs
  have h2 := h1.trans fun s hs =>
    Extract.RunsTo.toE (seg1a_x_runsTo (img := img) (C := C) (ext := ext) hRW_stk hsp_al hs)
  have h3 := h2.trans fun s hs =>
    seg1b_ro_x_runsTo hS hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs
  have h4 := h3.trans fun s hs =>
    Extract.RunsTo.toE (seg1c_x_runsTo (img := img) (C := C) (ext := ext) hRW_stk hsp_al hs)
  have h5 := h4.trans fun s hs =>
    fin_ro_x_runsTo hS hRW_stk hikm_len hsp_al hs
  have h6 := h5.trans fun s hs =>
    Extract.RunsTo.toE (seg2_x_runsTo (img := img) (C := C) (ext := ext) hsp_al hs)
  have h7 := Extract.RunsToE.trans_full h6 fun s hs hkf _ =>
    nfs2_ro_x_runsTo himg hS hro0 hkf hRW_stk hsp_al hs
  exact h7.trans fun s hs =>
    Extract.RunsTo.toE (seg3_x_runsTo (img := img) (C := C) (ext := ext)
      hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs)

private theorem sep_some_ext_1 (A B C G I R : SepProp) :
    (A ∗ B ∗ C ∗ G ∗ I) ∗ R = A ∗ (G ∗ (B ∗ C ∗ I ∗ R)) := by ac_rfl

private theorem sep_some_ext_2 (A B C G I R : SepProp) :
    (A ∗ B ∗ C ∗ G ∗ I) ∗ R = G ∗ (A ∗ (B ∗ C ∗ I ∗ R)) := by ac_rfl

private theorem sep_some_ext_3 (A B C G I R : SepProp) :
    (A ∗ B ∗ C ∗ G ∗ I) ∗ R = C ∗ (A ∗ (B ∗ G ∗ I ∗ R)) := by ac_rfl

private theorem sep_some_ext_4 (A B C G I R : SepProp) :
    (A ∗ B ∗ C ∗ G ∗ I) ∗ R = C ∗ (G ∗ (A ∗ B ∗ I ∗ R)) := by ac_rfl

private theorem sep_some_ext_5 (A B C G I R : SepProp) :
    (A ∗ B ∗ C ∗ G ∗ I) ∗ R = B ∗ (G ∗ (A ∗ C ∗ I ∗ R)) := by ac_rfl

private theorem sep_some_ext_post (P1 P2 B C G I R : SepProp) :
    (P1 ∗ P2) ∗ (G ∗ (B ∗ C ∗ I ∗ R)) = (P1 ∗ P2 ∗ B ∗ C ∗ G ∗ I) ∗ R := by ac_rfl

theorem pqxdhHkdfExtractSome_ok_at_ext {P : Primitives} {C : Crypto}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : HkdfStubsExt img.base C.F ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExtractSym)
      (pqxdhHkdfExtractSomeSpecAt extractStackExt P img) := by
  have hfn : (tripleRatchetProgAtExt img.base ext).fnAddr hkdfExtractSym =
      img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract") := by
    unfold tripleRatchetProgAtExt hkdfExtractSym
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract")]
  rw [hfn]
  refine subroutine_ok_intro fun ⟨ret, saltA, salt, ikmA, ikm, sp⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [pqxdhHkdfExtractSomeSpecAt, stackAt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF0, hx0, hx1, hx2, hx3, hx4, hsp_eq, hsalt_ne, hsalt_len, hikm_len⟩, hsep⟩
  subst hsp_eq
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hstk_eq : memRegion (s0.sp - BitVec.ofNat 64 extractStackExt) extractStackExt =
      memRegion (sp0 - 16928#64) 17360 :=
    congrArg₂ memRegion
      (by dsimp [sp0, extractStackExt, extractStack, newFromSliceStack, extHookStack]; bv_lin) rfl
  have hsp_al_0 : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  have hsp_al : (sp0 &&& 15#64) = 0#64 := sp0_aligned hsp0 hsp_al_0
  let x : ExtractGhost := ⟨ret, saltA, some (u8Vec 32 salt), ikmA, bytesToBv8 ikm⟩
  have hsalt_list : (u8Vec 32 salt).toList = bytesToBv8 salt := u8Vec_toList_of_length hsalt_len
  have hikm_bv_len : x.ikm.length = 32 := by dsimp [x]; rw [bytesToBv8_length, hikm_len]
  rw [hstk_eq] at hsep
  have hb_ret := IsBlock.memRegion ret 0xb0
  have hb_salt := IsBlock.pointsToBytes_len (a := saltA)
    (by rw [bytesToBv8_length, hsalt_len] : (bytesToBv8 salt).length = 32)
  have hb_ikm := IsBlock.pointsToBytes_len (a := ikmA) hikm_bv_len
  have hb_stk := IsBlock.memRegion (sp0 - 16928#64) 17360
  have hsep_ret_stk := sep_some_ext_1 _ _ _ _ _ R ▸ hsep
  have hsep_stk := sep_some_ext_2 _ _ _ _ _ R ▸ hsep
  have hsep_ikm_ret := sep_some_ext_3 _ _ _ _ _ R ▸ hsep
  have hsep_ikm_stk := sep_some_ext_4 _ _ _ _ _ R ▸ hsep
  have hsep_salt_stk := sep_some_ext_5 _ _ _ _ _ R ▸ hsep
  have hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact fun a ha => hb_ret.permNoLazy_rw hsep_ret_stk ha
  have hRW_stk : RW s0.mem (sp0 - 16928#64) 17360 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hRW_ikm : RW s0.mem x.ikmA 32 :=
    fun a ha => hb_ikm.permNoLazy_rw hsep_ikm_ret ha
  have hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 16928#64) 17360 := by
    rw [hx0]; exact hb_ret.disjoint hb_stk (by decide) (by decide) hsep_ret_stk
  have hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm := by
    have h := (hb_ikm.read hsep_ikm_ret).2
    rwa [hikm_bv_len] at h
  have hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret (by decide) (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 16928#64) 17360 :=
    hb_ikm.disjoint hb_stk (by decide) (by decide) hsep_ikm_stk
  have hsalt_some : ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ RW s0.mem x.saltA 32 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      DisjointRegions x.saltA 32 (sp0 - 16928#64) 17360 := by
    intro sv hsv
    injection hsv with hsv_eq
    subst hsv_eq
    refine ⟨hsalt_ne, fun a ha => hb_salt.permNoLazy_rw hsep_salt_stk ha, ?_,
      hb_salt.disjoint hb_stk (by decide) (by decide) hsep_salt_stk⟩
    have h := (hb_salt.read hsep_salt_stk).2
    rw [bytesToBv8_length, hsalt_len] at h
    exact h.trans hsalt_list.symm
  have hruns := extract_32_ro_runsToE_ext himg hS (x := x)
    hpc hrun hF0.roData hsp0 hx1 (fun _ => hx2) hx3 hx4 hikm_bv_len hsp_al
    hRW_out hRW_stk hRW_ikm hd_out_stk hikm_mem0 hd_ikm_out hd_ikm_stk
    (fun h => by nomatch h) hsalt_some
  refine hruns.to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_,
    LibsignalTripleRatchet.CallingConventionPreserved_of_calleeSaved hcallee htr⟩
  dsimp only [pqxdhHkdfExtractSomeSpecAt, stackAt]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExtFrameX at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_eq : x.prk C.F = bytesToBv8 (hkdfExtractRef P (some salt) ikm) := by
    dsimp [x, ExtractGhost.prk]
    exact (bytesToBv8_hkdfExtractRef_some hP hsalt_len ikm).symm
  have hprk_ref_len : (hkdfExtractRef P (some salt) ikm).length = 32 := by
    have h := congrArg List.length hprk_eq.symm
    rw [bytesToBv8_length] at h
    exact h.trans (length_hmacWith C.F _ _)
  have hprk_len : (x.prk C.F).length = 32 := by
    rw [hprk_eq, bytesToBv8_length, hprk_ref_len]
  have hb_prk := IsBlock.pointsToBytes_len (a := ret) hprk_len
  have hb_hm := isBlock_hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) [] (by decide)
  have hb_ret' : IsBlock ((ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) [])
      ret 0xb0
      (fun m => ((x.prk C.F).length ≤ 2 ^ 64 ∧ m.readBytes ret (x.prk C.F).length = x.prk C.F) ∧
        HmacSt m (ret + 0x20#64) C.F (x.prk C.F) []) :=
    hb_prk.sepConj hb_hm rfl (by decide)
  have hpost_sep := S2Frame.update_two_blocks hb_ret hb_ret' hb_stk hb_stk hsep_ret_stk hframe_sf
    ⟨⟨by rw [hprk_len]; decide, by rwa [hprk_len]⟩, hhm_sf⟩ trivial
  rw [hprk_eq, ← pqxdhHmacStateAt_eq hP (ret + 0x20#64) (by omega)] at hpost_sep
  rw [hstk_eq, ← sep_some_ext_post]
  exact hpost_sep

/-- `subroutine_ok` for `pqxdhHkdfExtractSomeSpecExt P img` (`24576` B stack). -/
theorem pqxdhHkdfExtractSome_ok_of_stubsExt {P : Primitives} {C : Crypto}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : HkdfStubsExt img.base C.F ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExtractSym)
      (pqxdhHkdfExtractSomeSpecExt P img) :=
  pqxdhHkdfExtractSome_mono_stack (by decide) (by decide)
    (pqxdhHkdfExtractSome_ok_at_ext hP himg hS)

end ExtractSomeRO

end CryptoVerification.E2E.Pqxdh.ResponderCore

