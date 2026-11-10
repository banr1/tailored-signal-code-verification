/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGt64SegsExt
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceLe64HalfExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGen
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceLe64Ext
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice -- shake: keep

/-!
# Contract-Backed Generalized `Hmac<Sha256>::new_from_slice [local#3]`

Contract-backed (`RunsToE` / `S2FrameRO`) finalization of `SHA-256(key)` on the `key.length > 64`
path (`0x6707c → 0x6717c`) and assembly of `new_from_slice3_gen_runsToE_ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.Nfs3Ext

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet (
  tripleRatchetProgAtExt extHookStack
  zeroExtend64_truncate32_ofNat64 zeroExtend64_ofNat8 xor_63_of_lt_64
  ult_7_of_lt_56 toLEBytes_8_read64 readBytes_56_eq_append_8 readBytes_56_of_buf_eq
  read32_words_at_104_of_shaStateBytes readBytes_write32_8_digestBytes toLEBytes_4_rev32)
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof hiding
  NfsMemInv3 NfsRegInv3
  read64_write8_stack_iv write64_quad_400_iv write64_quad_0_ivsw
  Nfs3OpadPostHook Nfs3OpadMidState Nfs3OpadEndState
  Nfs3PreCompress2 Nfs3PostCompress2 rodata_sha256IV_0x837d8
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3GenProof hiding
  write64_quad_240_iv NfsGt64Common StateG0 StateG1 StateG2a StateG2 StateG3 StateG2b StateG2c StateG4
open ProofLib.ProgramReflection
open CryptoVerification.CodeLayout

attribute [-arm64_norm, -simp] CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof.read64_write8_stack_iv

@[local simp, local arm64_norm] private theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl
@[local simp, local arm64_norm] private theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl
@[local simp, local arm64_norm] private theorem zero8_append_8 :
    (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
@[local simp, local arm64_norm] private theorem zero64_append_2 : (0#64 ++ 0#64 : BitVec 128) = 0#128 := rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint Memory.read8_write8_base_zero_off Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint Memory.read8_write64_base_zero_off Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds
  Memory.read32_write8_base_off_disjoint Memory.read32_write8_base_zero_off Memory.read32_write8_base_off_zero
  Memory.read32_write64_base_off_disjoint Memory.read32_write64_base_zero_off Memory.read32_write64_base_off_zero
  Memory.read64_write8_base_off_disjoint Memory.read64_write8_base_zero_off Memory.read64_write8_base_off_zero
  Memory.read64_write32_base_off_disjoint Memory.read64_write32_base_zero_off Memory.read64_write32_base_off_zero
  Memory.read64_write64_base_off_disjoint Memory.read64_write64_base_zero_off Memory.read64_write64_base_off_zero

@[local simp, local arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [(ls_off% newFromSlice3Name + 220) → (ls_off% newFromSlice3Name + 480)]

local macro "nfs3gt2_step" : tactic =>
  `(tactic| (
    refine RunsTo.step (inst := ?inst) ?hrun ?hfetch ?_
    case hfetch => (
      (try simp (config := { decide := true }) only [arm64_norm, *])
      refine libsignalSessionCode_fetch_rebase_text ?_ (by decide) (by decide)
      (try simp only [arm64_norm]) <;> rfl)
    case hrun => (simp only [arm64_norm, *])
    try dsimp only [execInst, execAddSubImm, execAddSubExt, execAddSubShift, execAddSubCarry, execLogicalImm,
      execLogicalShift, execMoveWide, execBitfield, execCondSelect, execCondCompare,
      execDataProc1, execDataProc2, execDataProc3, execLdr, execLdrLit, execStr, execLdp, execStp,
      evalLogical, evalBitfield, evalAddrMode, AddrMode.baseReg, checkRegSPAligned,
      checkAddrSPAligned, MemWidth.isAligned, State.spAligned, extendVal, Reg.fromZRBits,
      Reg.fromSPBits]
    try simp (config := { decide := true }) only [arm64_norm, *]
    try arm64_discharge_perms_internal))

/-! ## Sub-segment 0c (`hex:6707c → hex:670e4`): One-Block vs Two-Block Finalization of `SHA-256(key)` -/

structure StateG3Ext (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq : s.pc = b + bv% (ls_off% newFromSlice3Name + 324)
  common : NfsGt64CommonExt b s₀ s
  st_fin : ∃ st_f : ShaState,
    s.mem.readBytes (nfsSp s₀ + 352#64) 32 = shaStateBytes st_f ∧
    digestBytes st_f = sha256With F key

set_option maxHeartbeats 1600000 in
theorem nfs3_seg0c_gt64_one_step {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2Ext b F key s₀ s)
    (hkey_gt : 64 < key.length)
    (hkey_lt : key.length < 2 ^ 63)
    (hlt56 : (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s1 =>
      s1.pc = b + bv% (ls_off% "sha2::sha256::compress256") ∧
      NfsGt64CommonExt b s₀ s1 ∧
      s1.readReg64 .x0 = nfsSp s₀ + 352#64 ∧
      s1.readReg64 .x1 = nfsSp s₀ + 400#64 ∧
      s1.readReg64 .x2 = 1#64 ∧
      s1.readReg64 .lr = b + bv% (ls_off% newFromSlice3Name + 324) ∧
      s1.mem.readBytes (nfsSp s₀ + 352#64) 32 =
        shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV) ∧
      s1.mem.readBytes (nfsSp s₀ + 400#64) 64 =
        sha256PadBlock1 (key.length / 64) (key.drop (64 * (key.length / 64)))) := by
  generalize hPost : (fun s1 : State => _) = Post
  rcases hs with ⟨hpc, hcom, hx20, hx21, hx23, hx24, hbuf, hst0_bytes⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hf_zero⟩
  set pfx := key.take (64 * (key.length / 64))
  set tail := key.drop (64 * (key.length / 64))
  set st0 := (chunks64 pfx).foldl F sha256IV
  have htail_len : key.length - 64 * (key.length / 64) = tail.length := by simp [tail]
  rw [htail_len] at hx23 hx24
  clear htail_len
  have htail_lt : tail.length < 64 := by simp [tail]; omega
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_innerN_eq_lt64 (b := key.length / 64) htail_lt
  have hult_7 : (7#64).ult (BitVec.ofNat 64 (63 - tail.length)) = true := ult_7_of_lt_56 hlt56
  iterate 14 nfs3gt2_step
  subst hPost
  refine RunsTo.refl ?_
  set w56 := rev64 (BitVec.ofNat 64 (8 * (64 * (key.length / 64) + tail.length)))
  set m_pre_c :=
    ((((((((s.mem.write64 (nfsSp s₀ + 400#64) (s.mem.read64 (nfsSp s₀ + 288#64))).write64
      (nfsSp s₀ + 408#64) (s.mem.read64 (nfsSp s₀ + 296#64))).write64
      (nfsSp s₀ + 416#64) (s.mem.read64 (nfsSp s₀ + 304#64))).write64
      (nfsSp s₀ + 424#64) (s.mem.read64 (nfsSp s₀ + 312#64))).write64
      (nfsSp s₀ + 344#64) w56).write64
      (nfsSp s₀ + 432#64) (s.mem.read64 (nfsSp s₀ + 320#64))).write64
      (nfsSp s₀ + 440#64) (s.mem.read64 (nfsSp s₀ + 328#64))).write64
      (nfsSp s₀ + 448#64) (s.mem.read64 (nfsSp s₀ + 336#64))).write64
      (nfsSp s₀ + 456#64) w56
  have hag_pre_c : AgreesOutside s.mem m_pre_c (nfsSp s₀ + 344#64) 120 := by
    dsimp only [m_pre_c]; agrees_outside_writes
  have hf_zero_pre_c : S2Frame (nfsZeroMem s₀) m_pre_c
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    s2Frame_zero_of_agreesOutside hf_zero hag_pre_c (by bv_omega)
  have hst0_pre_c : m_pre_c.readBytes (nfsSp s₀ + 352#64) 32 = shaStateBytes st0 := by
    set m_lo := ((((s.mem.write64 (nfsSp s₀ + 400#64) (s.mem.read64 (nfsSp s₀ + 288#64))).write64
      (nfsSp s₀ + 408#64) (s.mem.read64 (nfsSp s₀ + 296#64))).write64
      (nfsSp s₀ + 416#64) (s.mem.read64 (nfsSp s₀ + 304#64))).write64
      (nfsSp s₀ + 424#64) (s.mem.read64 (nfsSp s₀ + 312#64))).write64
      (nfsSp s₀ + 344#64) w56
    have hag_hi : AgreesOutside m_lo m_pre_c (nfsSp s₀ + 432#64) 32 := by
      dsimp only [m_pre_c]; agrees_outside_writes
    have hag_344 : AgreesOutside
        ((((s.mem.write64 (nfsSp s₀ + 400#64) (s.mem.read64 (nfsSp s₀ + 288#64))).write64
          (nfsSp s₀ + 408#64) (s.mem.read64 (nfsSp s₀ + 296#64))).write64
          (nfsSp s₀ + 416#64) (s.mem.read64 (nfsSp s₀ + 304#64))).write64
          (nfsSp s₀ + 424#64) (s.mem.read64 (nfsSp s₀ + 312#64)))
        m_lo (nfsSp s₀ + 344#64) 8 := by
      dsimp only [m_lo]; agrees_outside_writes
    have hag_400 : AgreesOutside s.mem
        ((((s.mem.write64 (nfsSp s₀ + 400#64) (s.mem.read64 (nfsSp s₀ + 288#64))).write64
          (nfsSp s₀ + 408#64) (s.mem.read64 (nfsSp s₀ + 296#64))).write64
          (nfsSp s₀ + 416#64) (s.mem.read64 (nfsSp s₀ + 304#64))).write64
          (nfsSp s₀ + 424#64) (s.mem.read64 (nfsSp s₀ + 312#64)))
        (nfsSp s₀ + 400#64) 32 := by
      agrees_outside_writes
    have hd1 : DisjointRegions (nfsSp s₀ + 432#64) 32 (nfsSp s₀ + 352#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    have hd2 : DisjointRegions (nfsSp s₀ + 344#64) 8 (nfsSp s₀ + 352#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    have hd3 : DisjointRegions (nfsSp s₀ + 400#64) 32 (nfsSp s₀ + 352#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    rw [(agreesOutside_toFrame hag_hi).readBytes_eq (by simp [hd1]) (by decide),
        (agreesOutside_toFrame hag_344).readBytes_eq (by simp [hd2]) (by decide),
        (agreesOutside_toFrame hag_400).readBytes_eq (by simp [hd3]) (by decide),
        hst0_bytes]
  have hblk_pre_c : m_pre_c.readBytes (nfsSp s₀ + 400#64) 64 =
      sha256PadBlock1 (key.length / 64) tail := by
    dsimp only [m_pre_c]
    rw [readBytes_400_seg2, toLEBytes_read64_288_56 s.mem (nfsSp s₀),
        readBytes_56_of_buf_eq s.mem (nfsSp s₀ + 288#64) tail hbuf hlt56,
        toLEBytes_8_rev64]
    rfl
  refine ⟨by simp only [arm64_norm],
    { status := by simp only [arm64_norm, hstat]
      sp_eq := by simp only [arm64_norm, hsp]
      sp_align := hal_nfs
      x29_eq := by simp only [arm64_norm, hx29]
      x19_eq := by simp only [arm64_norm, hx19]
      x22_eq := by simp only [arm64_norm, hx22]
      x25_eq := by simp only [arm64_norm, hx25]
      x26_eq := by simp only [arm64_norm, hx26]
      x27_eq := by simp only [arm64_norm, hx27]
      frame_zero := by
        dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
        exact hf_zero_pre_c },
    by simp only [arm64_norm, hx20],
    by simp only [arm64_norm],
    by simp only [arm64_norm],
    by simp only [arm64_norm],
    by
      dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
      exact hst0_pre_c,
    by
      dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
      exact hblk_pre_c⟩

theorem nfs3_seg0c_gt64_one_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hHooks : SpqrKdfHooksExt img F ext)
    {key : List (BitVec 8)} {s₀ s : State}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hs : StateG2Ext img.base F key s₀ s)
    (hkey_gt : 64 < key.length)
    (hkey_lt : key.length < 2 ^ 63)
    (hlt56 : (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hdisj_iv_stack : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (s₀.sp - 16928#64) 16928) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateG3Ext img.base F key s₀) := by
  set pfx := key.take (64 * (key.length / 64))
  set tail := key.drop (64 * (key.length / 64))
  have hpfx_len : pfx.length = 64 * (key.length / 64) := by simp [pfx]; omega
  have hpfx_mod : pfx.length % 64 = 0 := by rw [hpfx_len]; omega
  have hpfx_div : pfx.length / 64 = key.length / 64 := by rw [hpfx_len]; omega
  have hkey_split : pfx ++ tail = key := List.take_append_drop (64 * (key.length / 64)) key
  have hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384 :=
    disj_stk_extstk_of_disj_16928 hdisj_iv_stack
  have hstep : RunsToE (tripleRatchetProgAtExt img.base ext) s _ :=
    RunsToE.of_hmacRunsTo (nfs3_seg0c_gt64_one_step (ext := ext) hs hkey_gt hkey_lt hlt56 hrw_stack)
  refine hstep.trans_full fun s1 h1 hkf1 hsym1 => ?_
  rcases h1 with ⟨hpc1, hcom1, hx0_1, hx1_1, hx2_1, hlr_1, hst0_1, hblk_1⟩
  have hfrz1 : img.FrozenLoaded s1 := hfrz.of_keepsFrozen hkf1
  have hsym1' : s1.symtab = img.symtab := hsym1.trans hsym
  have hrw_stk1 : s1.mem.RW (nfsSp s₀) 544 := hcom1.rw_stack hrw_stack
  have hrw_extstk1 : s1.mem.RW (nfsSp s₀ - 16384#64) 16384 := hcom1.rw_extstk hrw_stack
  have hd_st_blk : DisjointRegions (nfsSp s₀ + 352#64) 32 (nfsSp s₀ + 400#64) 64 := by
    clear * -; simp only [DisjointRegions]; bv_omega
  have hd_st_ext : DisjointRegions (nfsSp s₀ + 352#64) 32
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hcom1.sp_eq]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 352#64) ⟨by decide, by clear * -; bv_omega⟩
  have hd_blk_ext : DisjointRegions (nfsSp s₀ + 400#64) 64
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hcom1.sp_eq]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 400#64) ⟨by decide, by clear * -; bv_omega⟩
  have hc := compress256_one_subroutine_runsTo hHooks.compress256 (by decide)
    hfrz1 hsym1' hpc1 hcom1.status hx0_1 hx1_1 hx2_1 hst0_1 hblk_1
    (hrw_stk1.sub (by clear * -; bv_omega))
    (hrw_stk1.sub (by clear * -; bv_omega))
    (by rw [hcom1.sp_eq]; exact hrw_extstk1)
    hd_st_blk hd_st_ext hd_blk_ext
    (by rw [hcom1.sp_eq]; exact hcom1.sp_align)
  refine hc.mono fun s' ⟨hpc', hstat', hcc, hst', _, hfr⟩ => ?_
  rw [hlr_1] at hpc'
  have hfr_stk : S2Frame s1.mem s'.mem
      [(nfsSp s₀ + 352#64, 32), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hcom1.sp_eq] at hfr
  refine
    { pc_eq := hpc'
      common := NfsGt64CommonExt.of_cc_hook hstat' hcom1.sp_eq hcom1.sp_align
        hcom1.x29_eq hcom1.x19_eq hcom1.x22_eq hcom1.x25_eq hcom1.x26_eq hcom1.x27_eq
        hcc hcom1.frame_zero hfr_stk (by decide)
      st_fin := ⟨F ((chunks64 pfx).foldl F sha256IV) (sha256PadBlock1 (key.length / 64) tail),
        hst',
        by
          have hsha := sha256With_pfx_one_block F pfx tail hpfx_mod hlt56
          rw [hkey_split, hpfx_div] at hsha
          exact hsha.symm⟩ }

structure StateG2bExt (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq : s.pc = b + bv% (ls_off% newFromSlice3Name + 260)
  common : NfsGt64CommonExt b s₀ s
  x20_eq : s.readReg64 .x20 = nfsSp s₀ + 352#64
  x21_eq : s.readReg64 .x21 = BitVec.ofNat 64 (key.length / 64)
  x23_eq : s.readReg64 .x23 = BitVec.ofNat 64 (key.length - 64 * (key.length / 64))
  st1_bytes : s.mem.readBytes (nfsSp s₀ + 352#64) 32 =
    shaStateBytes (F ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV)
      (innerPadBlock1 (key.drop (64 * (key.length / 64)))))

structure StateG2cExt (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq : s.pc = b + bv% (ls_off% "sha2::sha256::compress256")
  common : NfsGt64CommonExt b s₀ s
  x0_eq : s.readReg64 .x0 = nfsSp s₀ + 352#64
  x1_eq : s.readReg64 .x1 = nfsSp s₀ + 400#64
  x2_eq : s.readReg64 .x2 = 1#64
  lr_eq : s.readReg64 .lr = b + bv% (ls_off% newFromSlice3Name + 324)
  st1_bytes : s.mem.readBytes (nfsSp s₀ + 352#64) 32 =
    shaStateBytes (F ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV)
      (innerPadBlock1 (key.drop (64 * (key.length / 64)))))
  blk2_bytes : s.mem.readBytes (nfsSp s₀ + 400#64) 64 =
    innerPadBlock2 (key.length / 64) (key.drop (64 * (key.length / 64)))

set_option maxHeartbeats 1600000 in
theorem nfs3_seg0c_gt64_two_a_step {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2Ext b F key s₀ s)
    (hnlt56 : ¬ (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s1 =>
      s1.pc = b + bv% (ls_off% "sha2::sha256::compress256") ∧
      NfsGt64CommonExt b s₀ s1 ∧
      s1.readReg64 .x0 = nfsSp s₀ + 352#64 ∧
      s1.readReg64 .x1 = nfsSp s₀ + 400#64 ∧
      s1.readReg64 .x2 = 1#64 ∧
      s1.readReg64 .lr = b + bv% (ls_off% newFromSlice3Name + 260) ∧
      s1.readReg64 .x20 = nfsSp s₀ + 352#64 ∧
      s1.readReg64 .x21 = BitVec.ofNat 64 (key.length / 64) ∧
      s1.readReg64 .x23 = BitVec.ofNat 64 (key.length - 64 * (key.length / 64)) ∧
      s1.mem.readBytes (nfsSp s₀ + 352#64) 32 =
        shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV) ∧
      s1.mem.readBytes (nfsSp s₀ + 400#64) 64 =
        innerPadBlock1 (key.drop (64 * (key.length / 64)))) := by
  generalize hPost : (fun s1 : State => _) = Post
  rcases hs with ⟨hpc, hcom, hx20, hx21, hx23, hx24, hbuf, hst0_bytes⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hf_zero⟩
  set pfx := key.take (64 * (key.length / 64))
  set tail := key.drop (64 * (key.length / 64))
  set st0 := (chunks64 pfx).foldl F sha256IV
  have htail_len : key.length - 64 * (key.length / 64) = tail.length := by simp [tail]
  rw [htail_len] at hx23 hx24
  clear htail_len
  have htail_lt : tail.length < 64 := by simp [tail]; omega
  have hge56 : 56 ≤ tail.length := by omega
  have hult_7 : (7#64).ult (BitVec.ofNat 64 (63 - tail.length)) = false :=
    ult_7_of_ge_56 hge56 htail_lt
  iterate 10 nfs3gt2_step
  subst hPost
  refine RunsTo.refl ?_
  set m_pre_c1 :=
    (((((((s.mem.write64 (nfsSp s₀ + 400#64) (s.mem.read64 (nfsSp s₀ + 288#64))).write64
      (nfsSp s₀ + 408#64) (s.mem.read64 (nfsSp s₀ + 296#64))).write64
      (nfsSp s₀ + 416#64) (s.mem.read64 (nfsSp s₀ + 304#64))).write64
      (nfsSp s₀ + 424#64) (s.mem.read64 (nfsSp s₀ + 312#64))).write64
      (nfsSp s₀ + 432#64) (s.mem.read64 (nfsSp s₀ + 320#64))).write64
      (nfsSp s₀ + 440#64) (s.mem.read64 (nfsSp s₀ + 328#64))).write64
      (nfsSp s₀ + 448#64) (s.mem.read64 (nfsSp s₀ + 336#64))).write64
      (nfsSp s₀ + 456#64) (s.mem.read64 (nfsSp s₀ + 344#64))
  have hag_pre_c1 : AgreesOutside s.mem m_pre_c1 (nfsSp s₀ + 400#64) 64 := by
    dsimp only [m_pre_c1]; agrees_outside_writes
  have hf_zero_pre_c1 : S2Frame (nfsZeroMem s₀) m_pre_c1
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    s2Frame_zero_of_agreesOutside hf_zero hag_pre_c1 (by bv_omega)
  have hst0_pre_c1 : m_pre_c1.readBytes (nfsSp s₀ + 352#64) 32 = shaStateBytes st0 := by
    have hd1 : DisjointRegions (nfsSp s₀ + 400#64) 64 (nfsSp s₀ + 352#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    rw [(agreesOutside_toFrame hag_pre_c1).readBytes_eq (by simp [hd1]) (by decide), hst0_bytes]
  have hblk_pre_c1 : m_pre_c1.readBytes (nfsSp s₀ + 400#64) 64 = innerPadBlock1 tail := by
    dsimp only [m_pre_c1]
    rw [readBytes_400_copy, toLEBytes_read64_288_64 s.mem (nfsSp s₀), hbuf]
  have htail_len' : tail.length = key.length - 64 * (key.length / 64) := by simp [tail]
  refine ⟨by simp only [arm64_norm],
    { status := by simp only [arm64_norm, hstat]
      sp_eq := by simp only [arm64_norm, hsp]
      sp_align := hal_nfs
      x29_eq := by simp only [arm64_norm, hx29]
      x19_eq := by simp only [arm64_norm, hx19]
      x22_eq := by simp only [arm64_norm, hx22]
      x25_eq := by simp only [arm64_norm, hx25]
      x26_eq := by simp only [arm64_norm, hx26]
      x27_eq := by simp only [arm64_norm, hx27]
      frame_zero := by
        dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
        exact hf_zero_pre_c1 },
    by simp only [arm64_norm, hx20],
    by simp only [arm64_norm],
    by simp only [arm64_norm],
    by simp only [arm64_norm],
    by simp only [arm64_norm, hx20],
    by simp only [arm64_norm, hx21],
    by simp only [arm64_norm, hx23, htail_len'],
    by
      dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
      exact hst0_pre_c1,
    by
      dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
      exact hblk_pre_c1⟩

theorem nfs3_seg0c_gt64_two_a_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hHooks : SpqrKdfHooksExt img F ext)
    {key : List (BitVec 8)} {s₀ s : State}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hs : StateG2Ext img.base F key s₀ s)
    (hnlt56 : ¬ (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hdisj_iv_stack : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (s₀.sp - 16928#64) 16928) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateG2bExt img.base F key s₀) := by
  have hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384 :=
    disj_stk_extstk_of_disj_16928 hdisj_iv_stack
  have hstep : RunsToE (tripleRatchetProgAtExt img.base ext) s _ :=
    RunsToE.of_hmacRunsTo (nfs3_seg0c_gt64_two_a_step (ext := ext) hs hnlt56 hrw_stack)
  refine hstep.trans_full fun s1 h1 hkf1 hsym1 => ?_
  rcases h1 with ⟨hpc1, hcom1, hx0_1, hx1_1, hx2_1, hlr_1, hx20_1, hx21_1, hx23_1, hst0_1, hblk_1⟩
  have hfrz1 : img.FrozenLoaded s1 := hfrz.of_keepsFrozen hkf1
  have hsym1' : s1.symtab = img.symtab := hsym1.trans hsym
  have hrw_stk1 : s1.mem.RW (nfsSp s₀) 544 := hcom1.rw_stack hrw_stack
  have hrw_extstk1 : s1.mem.RW (nfsSp s₀ - 16384#64) 16384 := hcom1.rw_extstk hrw_stack
  have hd_st_blk : DisjointRegions (nfsSp s₀ + 352#64) 32 (nfsSp s₀ + 400#64) 64 := by
    clear * -; simp only [DisjointRegions]; bv_omega
  have hd_st_ext : DisjointRegions (nfsSp s₀ + 352#64) 32
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hcom1.sp_eq]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 352#64) ⟨by decide, by clear * -; bv_omega⟩
  have hd_blk_ext : DisjointRegions (nfsSp s₀ + 400#64) 64
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hcom1.sp_eq]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 400#64) ⟨by decide, by clear * -; bv_omega⟩
  have hc := compress256_one_subroutine_runsTo hHooks.compress256 (by decide)
    hfrz1 hsym1' hpc1 hcom1.status hx0_1 hx1_1 hx2_1 hst0_1 hblk_1
    (hrw_stk1.sub (by clear * -; bv_omega))
    (hrw_stk1.sub (by clear * -; bv_omega))
    (by rw [hcom1.sp_eq]; exact hrw_extstk1)
    hd_st_blk hd_st_ext hd_blk_ext
    (by rw [hcom1.sp_eq]; exact hcom1.sp_align)
  refine hc.mono fun s' ⟨hpc', hstat', hcc, hst1', _, hfr⟩ => ?_
  rw [hlr_1] at hpc'
  have hfr_stk : S2Frame s1.mem s'.mem
      [(nfsSp s₀ + 352#64, 32), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hcom1.sp_eq] at hfr
  exact
    { pc_eq := hpc'
      common := NfsGt64CommonExt.of_cc_hook hstat' hcom1.sp_eq hcom1.sp_align
        hcom1.x29_eq hcom1.x19_eq hcom1.x22_eq hcom1.x25_eq hcom1.x26_eq hcom1.x27_eq
        hcc hcom1.frame_zero hfr_stk (by decide)
      x20_eq := hcc.2.2.1.trans hx20_1
      x21_eq := hcc.2.2.2.1.trans hx21_1
      x23_eq := hcc.2.2.2.2.2.1.trans hx23_1
      st1_bytes := hst1' }

set_option maxHeartbeats 1600000 in
theorem nfs3_seg0c_gt64_two_b_ext {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2bExt b F key s₀ s)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateG2cExt b F key s₀) := by
  rcases hs with ⟨hpc, hcom, hx20, hx21, hx23, hst1_bytes⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hf_zero⟩
  set pfx := key.take (64 * (key.length / 64))
  set tail := key.drop (64 * (key.length / 64))
  set st0 := (chunks64 pfx).foldl F sha256IV
  set st1 := F st0 (innerPadBlock1 tail)
  have htail_len : key.length - 64 * (key.length / 64) = tail.length := by simp [tail]
  rw [htail_len] at hx23
  clear htail_len
  have htail_lt : tail.length < 64 := by simp [tail]; omega
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_innerN_eq_lt64 (b := key.length / 64) htail_lt
  iterate 16 nfs3gt2_step
  refine RunsTo.refl ?_
  set w56 := rev64 (BitVec.ofNat 64 (8 * (64 * (key.length / 64) + tail.length)))
  set m_z :=
    ((((((s.mem.write64 (nfsSp s₀ + 336#64) 0#64).write64
      (nfsSp s₀ + 288#64) 0#64).write64
      (nfsSp s₀ + 296#64) 0#64).write64
      (nfsSp s₀ + 304#64) 0#64).write64
      (nfsSp s₀ + 312#64) 0#64).write64
      (nfsSp s₀ + 320#64) 0#64).write64
      (nfsSp s₀ + 328#64) 0#64
  set m_pre_c2 :=
    ((((((((m_z.write64 (nfsSp s₀ + 400#64) 0#64).write64
      (nfsSp s₀ + 408#64) 0#64).write64
      (nfsSp s₀ + 416#64) 0#64).write64
      (nfsSp s₀ + 424#64) 0#64).write64
      (nfsSp s₀ + 344#64) w56).write64
      (nfsSp s₀ + 432#64) 0#64).write64
      (nfsSp s₀ + 440#64) 0#64).write64
      (nfsSp s₀ + 448#64) 0#64).write64
      (nfsSp s₀ + 456#64) w56
  have hag_z : AgreesOutside s.mem m_z (nfsSp s₀ + 288#64) 56 := by
    dsimp only [m_z]; agrees_outside_writes
  have hag_c2_400 : AgreesOutside m_z m_pre_c2 (nfsSp s₀ + 344#64) 120 := by
    dsimp only [m_pre_c2]; agrees_outside_writes
  have hf_zero_z : S2Frame (nfsZeroMem s₀) m_z
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    s2Frame_zero_of_agreesOutside hf_zero hag_z (by bv_omega)
  have hf_zero_pre_c2 : S2Frame (nfsZeroMem s₀) m_pre_c2
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    s2Frame_zero_of_agreesOutside hf_zero_z hag_c2_400 (by bv_omega)
  have hst1_pre_c2 : m_pre_c2.readBytes (nfsSp s₀ + 352#64) 32 = shaStateBytes st1 := by
    set m_lo2 := ((((m_z.write64 (nfsSp s₀ + 400#64) 0#64).write64
      (nfsSp s₀ + 408#64) 0#64).write64
      (nfsSp s₀ + 416#64) 0#64).write64
      (nfsSp s₀ + 424#64) 0#64).write64
      (nfsSp s₀ + 344#64) w56
    have hag_hi2 : AgreesOutside m_lo2 m_pre_c2 (nfsSp s₀ + 432#64) 32 := by
      dsimp only [m_pre_c2]; agrees_outside_writes
    have hag_344_2 : AgreesOutside
        ((((m_z.write64 (nfsSp s₀ + 400#64) 0#64).write64
          (nfsSp s₀ + 408#64) 0#64).write64
          (nfsSp s₀ + 416#64) 0#64).write64
          (nfsSp s₀ + 424#64) 0#64)
        m_lo2 (nfsSp s₀ + 344#64) 8 := by
      dsimp only [m_lo2]; agrees_outside_writes
    have hag_400_2 : AgreesOutside m_z
        ((((m_z.write64 (nfsSp s₀ + 400#64) 0#64).write64
          (nfsSp s₀ + 408#64) 0#64).write64
          (nfsSp s₀ + 416#64) 0#64).write64
          (nfsSp s₀ + 424#64) 0#64)
        (nfsSp s₀ + 400#64) 32 := by
      agrees_outside_writes
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
        (agreesOutside_toFrame hag_z).readBytes_eq (by simp [hd4]) (by decide),
        hst1_bytes]
  have hblk_pre_c2 : m_pre_c2.readBytes (nfsSp s₀ + 400#64) 64 =
      innerPadBlock2 (key.length / 64) tail := by
    dsimp only [m_pre_c2]
    rw [readBytes_400_seg2, toLEBytes_8_zero_7, toLEBytes_8_rev64]
    rfl
  refine
    { pc_eq := rfl
      common :=
        { status := by simp only [arm64_norm, hstat]
          sp_eq := by simp only [arm64_norm, hsp]
          sp_align := hal_nfs
          x29_eq := by simp only [arm64_norm, hx29]
          x19_eq := by simp only [arm64_norm, hx19]
          x22_eq := by simp only [arm64_norm, hx22]
          x25_eq := by simp only [arm64_norm, hx25]
          x26_eq := by simp only [arm64_norm, hx26]
          x27_eq := by simp only [arm64_norm, hx27]
          frame_zero := by
            dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
            exact hf_zero_pre_c2 }
      x0_eq := by simp only [arm64_norm, hx20]
      x1_eq := by simp only [arm64_norm]
      x2_eq := by simp only [arm64_norm]
      lr_eq := by simp only [arm64_norm]
      st1_bytes := by
        dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
        exact hst1_pre_c2
      blk2_bytes := by
        dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
        exact hblk_pre_c2 }

theorem nfs3_seg0c_gt64_two_c_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hHooks : SpqrKdfHooksExt img F ext)
    {key : List (BitVec 8)} {s₀ s : State}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hs : StateG2cExt img.base F key s₀ s)
    (hnlt56 : ¬ (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hdisj_iv_stack : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (s₀.sp - 16928#64) 16928) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateG3Ext img.base F key s₀) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hlr, hst1_bytes, hblk2_bytes⟩
  have hrw_stk : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  have hrw_extstk : s.mem.RW (nfsSp s₀ - 16384#64) 16384 := hcom.rw_extstk hrw_stack
  have hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384 :=
    disj_stk_extstk_of_disj_16928 hdisj_iv_stack
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
  have hd_st_blk : DisjointRegions (nfsSp s₀ + 352#64) 32 (nfsSp s₀ + 400#64) 64 := by
    clear * -; simp only [DisjointRegions]; bv_omega
  have hd_st_ext : DisjointRegions (nfsSp s₀ + 352#64) 32
      (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hcom.sp_eq]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 352#64) ⟨by decide, by clear * -; bv_omega⟩
  have hd_blk_ext : DisjointRegions (nfsSp s₀ + 400#64) 64
      (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hcom.sp_eq]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 400#64) ⟨by decide, by clear * -; bv_omega⟩
  have hc := compress256_one_subroutine_runsTo hHooks.compress256 (by decide)
    hfrz hsym hpc hcom.status hx0 hx1 hx2 hst1_bytes hblk2_bytes
    (hrw_stk.sub (by clear * -; bv_omega))
    (hrw_stk.sub (by clear * -; bv_omega))
    (by rw [hcom.sp_eq]; exact hrw_extstk)
    hd_st_blk hd_st_ext hd_blk_ext
    (by rw [hcom.sp_eq]; exact hcom.sp_align)
  refine hc.mono fun s' ⟨hpc', hstat', hcc, hst_f, _, hfr⟩ => ?_
  rw [hlr] at hpc'
  have hfr_stk : S2Frame s.mem s'.mem
      [(nfsSp s₀ + 352#64, 32), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hcom.sp_eq] at hfr
  exact
    { pc_eq := hpc'
      common := NfsGt64CommonExt.of_cc_hook hstat' hcom.sp_eq hcom.sp_align
        hcom.x29_eq hcom.x19_eq hcom.x22_eq hcom.x25_eq hcom.x26_eq hcom.x27_eq
        hcc hcom.frame_zero hfr_stk (by decide)
      st_fin := ⟨F st1 (innerPadBlock2 (key.length / 64) tail),
        hst_f,
        by
          have hsha := sha256With_pfx_two_blocks F pfx tail hpfx_mod hge56 htail_lt
          rw [hkey_split, hpfx_div] at hsha
          exact hsha.symm⟩ }

theorem nfs3_seg0c_gt64_two_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hHooks : SpqrKdfHooksExt img F ext)
    {key : List (BitVec 8)} {s₀ s : State}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hs : StateG2Ext img.base F key s₀ s)
    (hnlt56 : ¬ (key.drop (64 * (key.length / 64))).length < 56)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hdisj_iv_stack : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (s₀.sp - 16928#64) 16928) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateG3Ext img.base F key s₀) := by
  refine (nfs3_seg0c_gt64_two_a_ext hHooks hfrz hsym hs hnlt56 hrw_stack hdisj_iv_stack).trans_full
    fun s2b h2b hkf2b hsym2b => ?_
  have hfrz2b : img.FrozenLoaded s2b := hfrz.of_keepsFrozen hkf2b
  have hsym2b' : s2b.symtab = img.symtab := hsym2b.trans hsym
  have hstep_b : RunsToE (tripleRatchetProgAtExt img.base ext) s2b _ :=
    RunsToE.of_hmacRunsTo (nfs3_seg0c_gt64_two_b_ext (ext := ext) h2b hrw_stack)
  refine hstep_b.trans_full fun s2c h2c hkf2c hsym2c => ?_
  exact nfs3_seg0c_gt64_two_c_ext hHooks (hfrz2b.of_keepsFrozen hkf2c) (hsym2c.trans hsym2b')
    h2c hnlt56 hrw_stack hdisj_iv_stack

theorem nfs3_seg0c_gt64_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hHooks : SpqrKdfHooksExt img F ext)
    {key : List (BitVec 8)} {s₀ s : State}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hs : StateG2Ext img.base F key s₀ s)
    (hkey_gt : 64 < key.length)
    (hkey_lt : key.length < 2 ^ 63)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hdisj_iv_stack : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (s₀.sp - 16928#64) 16928) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateG3Ext img.base F key s₀) := by
  by_cases hlt56 : (key.drop (64 * (key.length / 64))).length < 56
  · exact nfs3_seg0c_gt64_one_ext hHooks hfrz hsym hs hkey_gt hkey_lt hlt56 hrw_stack hdisj_iv_stack
  · exact nfs3_seg0c_gt64_two_ext hHooks hfrz hsym hs hlt56 hrw_stack hdisj_iv_stack

/-! ## Sub-segment 0d (`hex:670e4 → hex:6717c`): Writing Digest to `sp + 112..144` and Joining `hex:67158` -/

theorem s2Frame_pro_112_of_agreesOutside {s₀ : State} {m₁ m₂ : Memory} {off : BitVec 64} {sz : ℕ}
    (h1 : S2Frame (nfsPrologueMem s₀) m₁
      [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (h2 : AgreesOutside m₁ m₂ (nfsSp s₀ + off) sz)
    (hoff : 112 ≤ off.toNat ∧ off.toNat + sz ≤ 464) :
    S2Frame (nfsPrologueMem s₀) m₂
      [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
  refine h1.trans ((S2Frame.of_frame (agreesOutside_toFrame h2)).mono fun a ha r hr => ?_)
  have ha1 := ha (nfsSp s₀ + 112#64, 352) (by simp)
  simp only [List.mem_singleton] at hr
  subst hr
  rcases hoff with ⟨hlo, hhi⟩
  clear * - ha1 hlo hhi
  simp only [OutsideRegion] at ha1 ⊢
  bv_omega

structure StateG4Ext (b : BitVec 64) (k : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq : s.pc = b + bv% (ls_off% newFromSlice3Name + 440)
  status : s.status = .Running
  sp_eq : s.sp = nfsSp s₀
  sp_align : (nfsSp s₀ &&& 0b1111#64) = 0#64
  x29_eq : s.readReg64 .x29 = nfsSp s₀ + 464#64
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x22_eq : s.readReg64 .x22 = b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))
  x25_eq : s.readReg64 .x25 = s₀.readReg64 .x25
  x26_eq : s.readReg64 .x26 = s₀.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27
  frame_pro_112 : S2Frame (nfsPrologueMem s₀) s.mem
    [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]
  k_take32 : s.mem.readBytes (nfsSp s₀ + 112#64) 32 = (keyBlock k).take 32
  k_drop32 : s.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock k).drop 32

set_option maxHeartbeats 1600000 in
theorem nfs3_seg0d1_gt64_ext {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG3Ext b F key s₀ s)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (s₀.sp - 16928#64) 16928) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateG4Ext b (sha256With F key) s₀) := by
  rcases hs with ⟨hpc, hcom, ⟨st_f, hst_f, hdig_f⟩⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  have hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384 :=
    disj_stk_extstk_of_disj_16928 hdisj_iv_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hf_zero⟩
  have hst_words := read32_words_at_104_of_shaStateBytes s.mem (nfsSp s₀ + 248#64) st_f
    (by
      have h352 : nfsSp s₀ + 248#64 + 0x68#64 = nfsSp s₀ + 352#64 := by bv_omega
      rw [h352]; exact hst_f)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hst_words
  rcases hst_words with ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩
  iterate 29 nfs3gt2_step
  refine RunsTo.refl ?_
  set m_mid :=
    (((((((((s.mem.write8 (nfsSp s₀ + 351#64) 0#8).write64
      (nfsSp s₀ + 400#64) 0#64).write64
      (nfsSp s₀ + 408#64) 0#64).write64
      (nfsSp s₀ + 416#64) 0#64).write64
      (nfsSp s₀ + 424#64) 0#64).write64
      (nfsSp s₀ + 432#64) 0#64).write64
      (nfsSp s₀ + 440#64) 0#64).write64
      (nfsSp s₀ + 448#64) 0#64).write64
      (nfsSp s₀ + 456#64) 0#64).write64
      (nfsSp s₀ + 336#64) 0#64
  set m_mid2 :=
    (((((((m_mid.write64 (nfsSp s₀ + 344#64) 0#64).write64
      (nfsSp s₀ + 320#64) 0#64).write64
      (nfsSp s₀ + 328#64) 0#64).write64
      (nfsSp s₀ + 304#64) 0#64).write64
      (nfsSp s₀ + 312#64) 0#64).write64
      (nfsSp s₀ + 288#64) 0#64).write64
      (nfsSp s₀ + 296#64) 0#64)
  have hag_mid1 : AgreesOutside s.mem m_mid (nfsSp s₀ + 320#64) 144 := by
    dsimp only [m_mid]; agrees_outside_writes
  have hag_mid2 : AgreesOutside m_mid m_mid2 (nfsSp s₀ + 288#64) 64 := by
    dsimp only [m_mid2]; agrees_outside_writes
  have hf_zero_mid2 : S2Frame (nfsZeroMem s₀) m_mid2
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    s2Frame_zero_of_agreesOutside
      (s2Frame_zero_of_agreesOutside hf_zero hag_mid1 (by bv_omega))
      hag_mid2 (by bv_omega)
  set m_end :=
    ((((((((m_mid2.write32 (nfsSp s₀ + 112#64) ((rev32_64 ((st_f.get 0).zeroExtend 64)).truncate 32)).write32
      (nfsSp s₀ + 116#64) ((rev32_64 ((st_f.get 1).zeroExtend 64)).truncate 32)).write32
      (nfsSp s₀ + 120#64) ((rev32_64 ((st_f.get 2).zeroExtend 64)).truncate 32)).write32
      (nfsSp s₀ + 124#64) ((rev32_64 ((st_f.get 3).zeroExtend 64)).truncate 32)).write32
      (nfsSp s₀ + 128#64) ((rev32_64 ((st_f.get 4).zeroExtend 64)).truncate 32)).write32
      (nfsSp s₀ + 132#64) ((rev32_64 ((st_f.get 5).zeroExtend 64)).truncate 32)).write32
      (nfsSp s₀ + 136#64) ((rev32_64 ((st_f.get 6).zeroExtend 64)).truncate 32)).write32
      (nfsSp s₀ + 140#64) ((rev32_64 ((st_f.get 7).zeroExtend 64)).truncate 32))
  have hag_dig : AgreesOutside m_mid2 m_end (nfsSp s₀ + 112#64) 32 := by
    dsimp only [m_end]; agrees_outside_writes
  have hf_pro_end : S2Frame (nfsPrologueMem s₀) m_end
      [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    s2Frame_pro_112_of_agreesOutside (s2Frame_pro_112_of_zero hf_zero_mid2) hag_dig (by decide)
  have hk_len : (sha256With F key).length = 32 := sha256With_length F key
  have hRW_zero : (nfsZeroMem s₀).RW (nfsSp s₀) 544 := by
    have hA_pro := agreesOutside_nfsPrologueMem s₀
    have hA_zero := agreesOutside_nfsZeroMem s₀
    exact (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr
      ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr
        (hrw_stack.sub (by clear * -; simp only [nfsSp]; bv_omega)))
  have h144_zero : (nfsZeroMem s₀).readBytes (nfsSp s₀ + 144#64) 32 = List.replicate 32 0#8 := by
    unfold nfsZeroMem
    have h64 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).readBytes
        (nfsSp s₀ + 112#64) 64 = List.replicate 64 0#8 :=
      CryptoVerification.LibsignalAesCbc.Run.Layout.readBytes_writeBytes_eq _ _ _ 64 List.length_replicate (by decide)
    have hslice := readBytes_slice_of_readBytes_eq
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8))
      (nfsSp s₀ + 112#64) (List.replicate 64 0#8)
      (by rw [List.length_replicate]; exact h64) 32 32 (by decide)
    have hadd : (nfsSp s₀ + 112#64) + BitVec.ofNat 64 32 = nfsSp s₀ + 144#64 := by bv_omega
    rw [hadd] at hslice
    simpa using hslice
  refine
    { pc_eq := by simp only [arm64_norm, hpc]
      status := by simp only [arm64_norm, hstat]
      sp_eq := by simp only [arm64_norm, hsp]
      sp_align := hal_nfs
      x29_eq := by simp only [arm64_norm, hx29]
      x19_eq := by simp only [arm64_norm, hx19]
      x22_eq := by simp only [arm64_norm, hx22]
      x25_eq := by simp only [arm64_norm, hx25]
      x26_eq := by simp only [arm64_norm, hx26]
      x27_eq := by simp only [arm64_norm, hx27]
      frame_pro_112 := by
        dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
        exact hf_pro_end
      k_take32 := by
        dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
        exact (readBytes_write32_8_112_eq_digest m_mid2 (nfsSp s₀) st_f).trans
          (hdig_f.trans (keyBlock_take32_of_len32 hk_len).symm)
      k_drop32 := by
        dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
        have hd1 : DisjointRegions (nfsSp s₀ + 112#64) 32 (nfsSp s₀ + 144#64) 32 := by
          clear * -; simp only [DisjointRegions]; bv_omega
        have hd2 : DisjointRegions (nfsSp s₀ + 176#64) 288 (nfsSp s₀ + 144#64) 32 := by
          clear * -; simp only [DisjointRegions]; bv_omega
        have hd3 : DisjointRegions (nfsSp s₀ - BitVec.ofNat 64 extHookStack) extHookStack
            (nfsSp s₀ + 144#64) 32 :=
          (hd_stk_ext.sub_left (nfsSp s₀ + 144#64) ⟨by decide, by clear * -; bv_omega⟩).symm
        rw [(agreesOutside_toFrame hag_dig).readBytes_eq (by simp [hd1]) (by decide),
            S2Frame.readBytes_eq_of_readable hf_zero_mid2
              (hRW_zero.sub (by clear * -; bv_omega)).readable
              (fun r hr => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                rcases hr with rfl | rfl
                · exact hd2
                · exact hd3)
              (by decide),
            h144_zero, keyBlock_drop32_of_len32 hk_len] }

theorem nfsSavedStack_prologue_352_s2 (s₀ : State) (m : Memory)
    (hf : S2Frame (nfsPrologueMem s₀) m
      [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hrw_stk : s₀.mem.RW (nfsSp s₀) 544)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384) :
    NfsSavedStack s₀ (m.write64 (nfsSp s₀ + 432#64) 1#64) := by
  have hrw_pro : (nfsPrologueMem s₀).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame (agreesOutside_nfsPrologueMem s₀)) _ _).mpr hrw_stk
  have hread (k : BitVec 64) (hk : 464 ≤ k.toNat ∧ k.toNat + 8 ≤ 544) :
      m.read64 (nfsSp s₀ + k) = (nfsPrologueMem s₀).read64 (nfsSp s₀ + k) := by
    rcases hk with ⟨hk1, hk2⟩
    refine hf.read64_eq
      (hrw_pro.sub (by clear * - hk1 hk2; bv_omega))
      (fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · clear * - hk1 hk2
      simp only [DisjointRegions]; bv_omega
    · exact (hd_stk_ext.sub_left (nfsSp s₀ + k)
        ⟨by decide, by clear * - hk1 hk2; bv_omega⟩).symm
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

set_option maxHeartbeats 1600000 in
theorem nfs3_seg0d2_gt64_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {k : List (BitVec 8)} {s₀ s : State}
    (hs : StateG4Ext b k s₀ s)
    (hk_len : k.length ≤ 64)
    (hiv : s₀.mem.readBytes (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (s₀.sp - 16928#64) 16928)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 16928#64) 16928) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = b + bv% (ls_off% newFromSlice3Name + 476) ∧
      s'.status = .Running ∧
      NfsRegInv3 b (s₀.setMem s.mem) s' ∧
      NfsMemInv3 b (s₀.setMem s.mem) s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s.mem.read64 (nfsSp s₀ + 152#64) ++ s.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s.mem.read64 (nfsSp s₀ + 168#64) ++ s.mem.read64 (nfsSp s₀ + 160#64) ∧
      s.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock k).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock k) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock k) 16) := by
  generalize hPost : (fun s' : State => _) = Post
  rcases hs with ⟨hpc, hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hf_pro_112, hk0_take32, hk0_drop32⟩
  have hkb_len : (keyBlock k).length = 64 := keyBlock_length hk_len
  have hf_16928 : S2Frame s₀.mem s.mem [(s₀.sp - 16928#64, 16928)] :=
    s2Frame_16928_of_pro_112 hf_pro_112
  have hrw_stk0 : s₀.mem.RW (nfsSp s₀) 544 :=
    hrw_stack.sub (by clear * -; simp only [nfsSp]; bv_omega)
  have hRW_k0 : s.mem.RW (nfsSp s₀) 544 := S2Frame.rw_of_rw hf_16928 _ _ hrw_stk0
  have hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384 :=
    disj_stk_extstk_of_disj_16928 hdisj_iv_stack
  have hdisj_iv_stk : DisjointRegions (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (nfsSp s₀) 544 :=
    hdisj_iv_stack.sub_right _ ⟨by decide, by clear * -; simp only [nfsSp]; bv_omega⟩
  have hdisj_out_stk : DisjointRegions (s₀.readReg64 .x0) 0x98 (nfsSp s₀) 544 :=
    hdisj_out_stack.sub_right _ ⟨by decide, by clear * -; simp only [nfsSp]; bv_omega⟩
  iterate 9 nfs3gt2_step
  subst hPost
  refine RunsTo.refl ?_
  set m_k0 := s.mem
  have hA_432 : AgreesOutside m_k0 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self m_k0 (nfsSp s₀ + 432#64) 1#64
  have hf_432 : Frame m_k0 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64)
      [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] :=
    Frame.of_agreesOutside_stack (Frame.refl m_k0 _) hA_432 (by decide)
  have hread_iv_k0 : m_k0.Readable (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 :=
    S2Frame.readable_of_readable hf_16928 hread_iv
  have hiv_k0 : m_k0.readBytes (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV :=
    (S2Frame.readBytes_eq_of_readable hf_16928 hread_iv
      (by simp [hdisj_iv_stack.symm]) (by decide)).trans hiv
  have hM_432 : NfsMemInv3 b (s₀.setMem m_k0) (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf_432 _ _).mpr hRW_k0
    rw_out := (Frame.rw_iff hf_432 _ _).mpr (S2Frame.rw_of_rw hf_16928 _ _ hrw_out)
    readable_iv := (Frame.readable_iff hf_432 _ _).mpr hread_iv_k0
    iv_bytes := by
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 := by
        clear * - hdisj_iv_stk; simp only [DisjointRegions, nfsSp] at hdisj_iv_stk ⊢; bv_omega
      rw [(agreesOutside_toFrame hA_432).readBytes_eq (by simp [hd432]) (by decide), hiv_k0]
    disj_iv_stack := hdisj_iv_stk
    disj_out_stack := hdisj_out_stk
    saved := nfsSavedStack_setMem_iff.mpr
      (nfsSavedStack_prologue_352_s2 s₀ m_k0 hf_pro_112 hrw_stk0 hd_stk_ext)
    frame := hf_432
  }
  have hM_final : NfsMemInv3 b (s₀.setMem m_k0)
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock k) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock k) 16)) :=
    (hM_432.writeBytes_low 288#64 _ (by simp [slice16_length])).writeBytes_low
      304#64 _ (by simp [slice16_length])
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp, nfsSp], hal_nfs, by simp only [arm64_norm, hx29, nfsSp],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, nfsSp],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    hk0_drop32, ?_, ?_⟩
  · dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock k) hkb_len hk0_take32]
    exact hM_final
  · dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock k) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock k) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

/-! ## Full `> 64` Execution (`nfs3_gt64_runsToE_ext`) and `new_from_slice3_gen_runsToE_ext` -/

theorem nfs3_chunks_1_to_4_of_G4Ext {b : BitVec 64} {ext : String → Option (State → State)}
    {k : List (BitVec 8)} {s₀ s : State}
    (hs : StateG4Ext b k s₀ s)
    (hk_le : k.length ≤ 64)
    (hiv : s₀.mem.readBytes (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hread_iv : s₀.mem.Readable (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (s₀.sp - 16928#64) 16928)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 16928#64) 16928)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = b + bv% (ls_off% newFromSlice3Name + 1260) ∧
      s'.status = .Running ∧
      NfsRegInv3 b (s₀.setMem s.mem) s' ∧
      NfsMemInv3 b (s₀.setMem s.mem) s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock k).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 =
        (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  refine (nfs3_seg0d2_gt64_ext hs hk_le hiv hread_iv hdisj_iv_stack hrw_out hrw_stack hdisj_out_stack).trans
    fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1, hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩
  exact nfs3_chunks_1_to_4_ext (s₀ := s₀.setMem s.mem) (m_k0 := s.mem)
    hk_le hal hb hpc1 hstat1 hR1 hM1 hx8_1 hx0_1 hx1_1 hx2_1 hq2_1 hq0_1 hk0_1 hs0_1 hs16_1

theorem nfs3_gt64_runsToE_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hHooks : SpqrKdfHooksExt img F ext)
    {s₀ : State}
    (hfrz : img.FrozenLoaded s₀)
    (hsym : s₀.symtab = img.symtab)
    (hpc : s₀.pc = img.base + bv% (ls_off% newFromSlice3Name))
    (hstat : s₀.status = .Running)
    (hgt : 64 < (s₀.readReg64 .x2).toNat)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hread_iv : s₀.mem.Readable (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32)
    (hdisj_iv_stack : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (s₀.sp - 16928#64) 16928)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_key : s₀.mem.RW (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 16928#64) 16928)
    (hdisj_key_stack : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 16928#64) 16928)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsToE (tripleRatchetProgAtExt img.base ext) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CryptoVerification.LibsignalTripleRatchet.CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F (sha256With F key) [] ∧
      S2Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)]) := by
  intro key
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_gt : 64 < key.length := by omega
  have hkey_lt : key.length < 2 ^ 63 := by omega
  have hk_le : (sha256With F key).length ≤ 64 := by
    have : (sha256With F key).length = 32 := sha256With_length F key
    omega
  have hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384 :=
    disj_stk_extstk_of_disj_16928 hdisj_iv_stack
  have hd_iv_ext : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (nfsSp s₀ - 16384#64) 16384 :=
    hdisj_iv_stack.sub_right _ ⟨by decide, by clear * -; simp only [nfsSp]; bv_omega⟩
  have hpro : RunsToE (tripleRatchetProgAtExt img.base ext) s₀ _ :=
    RunsToE.of_hmacRunsTo (nfs3_seg0_pro_gt64_ext (ext := ext) hpc hstat hgt hb hrw_stack hal)
  refine hpro.trans_full fun s_g0 hg0 hkf0 hsym0 => ?_
  have hfrz0 : img.FrozenLoaded s_g0 := hfrz.of_keepsFrozen hkf0
  have hsym0' : s_g0.symtab = img.symtab := hsym0.trans hsym
  refine (nfs3_seg0a_gt64_ext hHooks hfrz0 hsym0' hg0 hgt hlt hiv hread_iv
    hdisj_iv_stack hrw_key hrw_stack hdisj_key_stack).trans_full fun s_g1 hg1 hkf1 hsym1 => ?_
  have hfrz1 : img.FrozenLoaded s_g1 := hfrz0.of_keepsFrozen hkf1
  have hsym1' : s_g1.symtab = img.symtab := hsym1.trans hsym0'
  refine (nfs3_seg0b_gt64_ext hHooks hfrz1 hsym1' hg1 hkey_gt hkey_lt hrw_stack hdisj_iv_stack).trans_full
    fun s_g2 hg2 hkf2 hsym2 => ?_
  have hfrz2 : img.FrozenLoaded s_g2 := hfrz1.of_keepsFrozen hkf2
  have hsym2' : s_g2.symtab = img.symtab := hsym2.trans hsym1'
  refine (nfs3_seg0c_gt64_ext hHooks hfrz2 hsym2' hg2 hkey_gt hkey_lt hrw_stack hdisj_iv_stack).trans_full
    fun s_g3 hg3 hkf3 hsym3 => ?_
  have hfrz3 : img.FrozenLoaded s_g3 := hfrz2.of_keepsFrozen hkf3
  have hsym3' : s_g3.symtab = img.symtab := hsym3.trans hsym2'
  have hseg0d1 : RunsToE (tripleRatchetProgAtExt img.base ext) s_g3 _ :=
    RunsToE.of_hmacRunsTo (nfs3_seg0d1_gt64_ext (ext := ext) hg3 hrw_stack hdisj_iv_stack)
  refine hseg0d1.trans_full fun s_g4 hg4 hkf4 hsym4 => ?_
  have hfrz4 : img.FrozenLoaded s_g4 := hfrz3.of_keepsFrozen hkf4
  have hsym4' : s_g4.symtab = img.symtab := hsym4.trans hsym3'
  have hfr04 : S2Frame s₀.mem s_g4.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    s2Frame_out_16928_of_16928 (s2Frame_16928_of_pro_112 hg4.frame_pro_112)
  have hrw_extstk4 : RW s_g4.mem (nfsSp s₀ - 16384#64) 16384 :=
    S2Frame.rw_of_rw (s2Frame_16928_of_pro_112 hg4.frame_pro_112) _ _
      (hrw_stack.sub (by clear * -; simp only [nfsSp]; bv_omega))
  have hchunks : RunsToE (tripleRatchetProgAtExt img.base ext) s_g4 _ :=
    RunsToE.of_hmacRunsTo (nfs3_chunks_1_to_4_of_G4Ext (ext := ext) hg4 hk_le hiv hb hread_iv
      hdisj_iv_stack hrw_out hrw_stack hdisj_out_stack hal)
  refine hchunks.trans_full fun s_mid ⟨hpc_m, hstat_m, hR_m, hM_m, hx0_m, hx1_m, hx2_m, hist_m, hblk_m, hivsw_m⟩ hkfm hsymm => ?_
  have hfrzm : img.FrozenLoaded s_mid := hfrz4.of_keepsFrozen hkfm
  have hsymm' : s_mid.symtab = img.symtab := hsymm.trans hsym4'
  have hrw_extstkm : RW s_mid.mem (nfsSp s₀ - 16384#64) 16384 :=
    (Frame.rw_iff hM_m.frame _ _).mpr hrw_extstk4
  refine (nfs3_second_half_ext hHooks.compress256 hk_le hal hfrzm hsymm' hd_stk_ext hd_iv_ext
    hrw_extstkm hpc_m hstat_m hR_m hM_m hx0_m hx1_m hx2_m hist_m hblk_m hivsw_m).mono fun sf hsf => ?_
  rcases hsf with ⟨hpc_sf, hstat_sf, hcs_sf, hret_sf, hhm_sf, hfr4f⟩
  exact ⟨hpc_sf, hstat_sf, hcs_sf, hret_sf, hhm_sf, S2Frame.trans hfr04 hfr4f⟩

end CryptoVerification.SpqrV1.Kdf.Nfs3Ext

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt extHookStack RW)
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt

/-- Generalized `RunsToE` / `S2FrameRO` contract of `new_from_slice [local#3]` (`hex:66fa0`) on
`tripleRatchetProgAtExt img.base ext` at `16928` B stack (`Nfs3GenRunsToEExt img F ext`), handling
both `key.length ≤ 64` (arbitrary `keyRO`) and `key.length > 64` (`keyRO = false`, `RW` key). -/
theorem new_from_slice3_gen_runsToE_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hHooks : SpqrKdfHooksExt img F ext) :
    Nfs3GenRunsToEExt img F ext := by
  intro keyRO roRegs s₀ hpre
  by_cases hle : (s₀.readReg64 .x2).toNat ≤ 64
  · exact Nfs3Ext.nfs3_le64_runsToE_ext hHooks hpre hle
  · have hgt : 64 < (s₀.readReg64 .x2).toNat := by omega
    have hkr_false : keyRO = false := by
      cases hkr : keyRO
      · rfl
      · have hkp := hpre.key_perm
        rw [hkr] at hkp
        simp only [↓reduceIte] at hkp
        omega
    have hrw_key : RW s₀.mem (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      have hkp := hpre.key_perm
      rw [hkr_false] at hkp
      simpa using hkp
    have hdisj_key_stk : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
        (s₀.sp - 16928#64) 16928 :=
      disjointRegions_of_outside (by omega) (by decide) hpre.out_key_stk
    set key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
    have heff : effectiveHmacKey F key = sha256With F key := by
      unfold effectiveHmacKey
      have hgt' : 64 < key.length := by omega
      have hnle' : ¬ key.length ≤ 64 := by omega
      simp [hgt', hnle']
    rw [heff]
    refine (Nfs3Ext.nfs3_gt64_runsToE_ext hHooks hpre.frz hpre.sym hpre.pc_eq hpre.status
      hgt hpre.key_lt hpre.ro_iv_bytes hpre.base_al hpre.ro_iv_read hpre.disj_iv_stk
      hpre.rw_out hrw_key hpre.rw_stk hpre.disj_out_stk hdisj_key_stk hpre.sp_aligned).mono
      fun s' ⟨hpc', hstat', hcs', hret', hhm', hfr'⟩ => ?_
    exact ⟨hpc', hstat', hcs', hret', hhm', S2FrameRO.of_s2frame hfr'⟩

end CryptoVerification.SpqrV1.Kdf
