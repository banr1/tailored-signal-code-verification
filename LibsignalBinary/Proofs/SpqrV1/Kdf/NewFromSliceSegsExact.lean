/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGt64 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon

/-!
# `HookSatExactMemcpy` Siblings of `SpqrV1.Kdf.NewFromSlice*` (`NewFromSliceSegsExact`, Block `402`)

- **Role:** `Role::Proof` (untrusted proof module outside the TCB; #1255 mc2 Cone 3).
- **Overview:**
  Replaces `h_memcpy : H lsMemcpySym = some memcpyHook` on Block `402`'s two `memcpy` segments
  (`NewFromSlice3Proof.nfs_seg0_placed` for `key.length ≤ 64` and
  `NewFromSlice3GenProof.nfs_seg0a_gt64_placed` for `key.length > 64`) with
  `(h_mc : HookSatExactMemcpy H lsMemcpySym)` via `placed_memcpy_step_of_exact`, keeping all
  cut predicates (`NfsRegInv3`, `NfsMemInv3`, `StateG0`, `StateG1`, `Frame`) **100% unchanged**
  and reusing all remaining Block `402` segments (`nfs_chunk1..4_placed`, `nfs_second_half_placed`)
  verbatim.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceSegsExact

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState chunks64 sha256IV)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement LibsignalRoLoaded blkPl_402 lsProg_402 lsmpl lsρ
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (AgreesOutside.write64_self AgreesOutside.write8_self CalleeSaved
   CallingConventionPreserved_of_calleeSaved Frame RW RunsTo TraceEq
   TraceEq.advancePC_step TraceEq.refl TraceEq.setMem_step TraceEq.setPC_step
   TraceEq.setPState_step TraceEq.writeReg32_step TraceEq.writeReg64_step
   TraceEq.writeVReg128_step agreesOutside_nfsPrologueMem agreesOutside_toFrame
   disjointRegions_of_ro_rw keyBlock keyBlock_length lsCompress256Sym lsMemcpySym
   nfsPrologueMem nfsSavedStack_prologue_432 nfsSp nfs_sp_add_464_align
   nfs_sp_add_544_align nfs_sp_align nfs_sp_eq_add nfs_ule_65_false
   readBytes_writeBytes_16_other readBytes_writeBytes_16_self shaStateBytes_length
   slice16 slice16_length write64_oct_zero_eq_writeBytes_64
   write64_quad_288_eq_writeBytes_slice16 writeBytes_key_over_zero64)
open CryptoVerification.LibsignalTripleRatchet
  (HmacSt newFromSliceSpec newFromSliceStack)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (isBlock_nfsResult)
open CryptoVerification.SpqrV1.Kdf (ikm_split_lemmas)
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3GenProof
  (StateG0 StateG1 agreesOutside_nfsZeroMem agreesOutside_sub_176_288 nfs3CodeFakeB
   nfsZeroMem placed_compress256_multi_step readBytes_take_of_le write64_quad_240_iv_placed)
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof
  (NfsMemInv3 NfsRegInv3 nfs3PlacedFakeB nfs3PlacedFakeB_add_iv nfs_chunk1_placed
   nfs_chunk2_placed nfs_chunk3_placed nfs_chunk4_placed nfs_second_half_placed
   rodata_placed_spqrSha256IV spqrSha256IVAddr)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open scoped LibsignalBinary.Heap.MuslMemOpsRunsToPlaced
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookSatExactMemcpy placed_memcpy_step_of_exact)

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

local macro (priority := high) "sess_step" : tactic =>
  `(tactic| (
    refine RunsTo.step (inst := ?inst) ?hrun ?hfetch ?_
    case hfetch => (
      (try simp (config := { decide := true }) only [arm64_norm, *])
      try rfl)
    case hrun => (simp only [arm64_norm, *])
    try dsimp only [execInst, execAddSubImm, execAddSubExt, execAddSubShift, execAddSubCarry, execLogicalImm,
      execLogicalShift, execMoveWide, execBitfield, execCondSelect, execCondCompare,
      execDataProc1, execDataProc2, execDataProc3, execLdr, execLdrLit, execStr, execLdp, execStp,
      evalLogical, evalBitfield, evalAddrMode, AddrMode.baseReg, checkRegSPAligned,
      checkAddrSPAligned, MemWidth.isAligned, State.spAligned, extendVal, Reg.fromZRBits,
      Reg.fromSPBits]
    try simp (config := { decide := true }) only [arm64_norm, *]
    try arm64_discharge_perms_internal))

local macro "prove_trace_eq" : tactic =>
  `(tactic|
    repeat' (first
      | with_reducible exact TraceEq.refl _
      | with_reducible apply TraceEq.writeReg64_step
      | with_reducible apply TraceEq.advancePC_step
      | with_reducible apply TraceEq.setMem_step
      | with_reducible apply TraceEq.setPC_step
      | with_reducible apply TraceEq.setPState_step
      | with_reducible apply TraceEq.writeReg32_step
      | with_reducible apply TraceEq.writeVReg128_step (by decide)))

private theorem readable_of_rw {m : Memory} {a : BitVec 64} {n : Nat} (h : m.RW a n) :
    m.Readable a n := by
  intro x hx
  obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (h x hx)
  exact ⟨by rw [hp]; rfl, hlf⟩

/-! ## 1. `key.length ≤ 64` Exact `memcpy` Segment & Composition (Block `402`) -/

set_option maxHeartbeats 3200000 in
/-- `HookSatExactMemcpy` sibling of `NewFromSlice3Proof.nfs_seg0_placed`
(`NewFromSliceFirstHalf.lean:917`). -/
public theorem nfs_seg0_placed_exact [LibsignalPlacement] {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = (blkPl_402).base + 476#64 ∧ s'.status = .Running ∧
      NfsRegInv3 nfs3PlacedFakeB s₀ s' ∧ NfsMemInv3 nfs3PlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧ s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  intro key; generalize hPost : (fun s' : State => _) = Post
  have hkey_len : key.length ≤ 64 := by dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hkey_len
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = false := nfs_ule_65_false hlen
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  refine CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof.RunsTo.pairStep_402_0x28
    (by simp only [arm64_norm, hpc]) (by simp only [arm64_norm, hstat]) ?_
  sess_step; sess_step; sess_step; sess_step; sess_step
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 := agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)) (nfsSp s₀ + 112#64) 64 := by
    simpa using ProofLib.agreesOutside_writeBytes (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (List.replicate 64 0#8)
  have hread_key_mc : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).readBytes
      (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · simp only [key, h0, Memory.readBytes]
    have hdisj_key_pro : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    have hdisj_key_112 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    rw [(agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hdisj_key_112]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdisj_key_pro]) (by omega)]
  have hrw_memcpy : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW
      (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat := by
    have hrw0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW (nfsSp s₀) 544 :=
      (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
    exact hrw0.sub (by clear * - hlen; bv_omega)
  have hreadable_mc : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).Readable
      (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat :=
    (Frame.readable_iff (agreesOutside_toFrame hA_zero) _ _).mpr
      ((Frame.readable_iff (agreesOutside_toFrame hA_pro) _ _).mpr hread_key)
  have hdisj_mc : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat
        (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
    rcases hdisj_key_stack with h0 | hd
    · exact Or.inl h0
    · exact Or.inr (by clear * - hd hlen; simp only [DisjointRegions, nfsSp] at hd ⊢; bv_omega)
  refine placed_memcpy_step_of_exact h_mc
    (hrun := by simp only [arm64_norm, hstat])
    (hsp := by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hal_nfs])
    (hpc := by simp only [arm64_norm, lsMemcpySym])
    (hx0 := by simp only [arm64_norm])
    (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm])
    (hlr := by simp only [arm64_norm]; rfl)
    (hmem := write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀))
    (hread := hread_key_mc) (hrw := hrw_memcpy) (hreadable := hreadable_mc) (hdisj := hdisj_mc)
    fun c => ?_
  dsimp only [applyMemcpyClobber]
  rw [writeBytes_key_over_zero64]
  have hA_k0 : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)) (nfsSp s₀ + 112#64) 64 := by
    have h := ProofLib.agreesOutside_writeBytes (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key); rwa [hkb_len] at h
  have hRW_k0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_k0) _ _).mpr ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost; refine RunsTo.refl ?_ (htr := by prove_trace_eq)
  set m_k0 := (nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)
  have hk0_64 : m_k0.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key :=
    readBytes_writeBytes_eq (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key) 64 hkb_len (by decide)
  have hk0_take32 : m_k0.readBytes (nfsSp s₀ + 112#64) 32 = (keyBlock key).take 32 := by
    simpa using readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key) (by rw [hkb_len]; exact hk0_64) 0 32 (by omega)
  have hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key) (by rw [hkb_len]; exact hk0_64) 32 32 (by omega)
    have hadd : (nfsSp s₀ + 112#64) + BitVec.ofNat 64 32 = nfsSp s₀ + 144#64 := by clear * -; bv_omega
    rw [hadd, List.take_of_length_le (by simp [hkb_len])] at h; exact h
  have hA_432 : AgreesOutside m_k0 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self m_k0 (nfsSp s₀ + 432#64) 1#64
  have hf_k0 : Frame s₀.mem (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := by
    have hf0 : Frame s₀.mem s₀.mem [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := Frame.refl _ _
    have hf1 := Frame.of_agreesOutside_stack hf0 hA_pro (by decide)
    have hf2 := Frame.of_agreesOutside_stack hf1 hA_k0 (by decide)
    exact Frame.of_agreesOutside_stack hf2 hA_432 (by decide)
  have hM_432 : NfsMemInv3 nfs3PlacedFakeB s₀ (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf_k0 _ _).mpr hrw_stack, rw_out := (Frame.rw_iff hf_k0 _ _).mpr hrw_out
    readable_iv := by rw [nfs3PlacedFakeB_add_iv]; exact (Frame.readable_iff hf_k0 _ _).mpr hread_iv
    iv_bytes := by
      rw [nfs3PlacedFakeB_add_iv]
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8 spqrSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdk0 : DisjointRegions (nfsSp s₀ + 112#64) 64 spqrSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdpro : DisjointRegions (nfsSp s₀ + 464#64) 80 spqrSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      rw [(agreesOutside_toFrame hA_432).readBytes_eq (by simp [hd432]) (by decide),
          (agreesOutside_toFrame hA_k0).readBytes_eq (by simp [hdk0]) (by decide),
          (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdpro]) (by decide), hiv]
    disj_iv_stack := by rw [nfs3PlacedFakeB_add_iv]; exact hdisj_iv_stack
    disj_out_stack := hdisj_out_stack, saved := nfsSavedStack_prologue_432 s₀ m_k0 hA_k0, frame := hf_k0 }
  have hM_final : NfsMemInv3 nfs3PlacedFakeB s₀
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)) :=
    (hM_432.writeBytes_low 288#64 _ (by simp [slice16_length])).writeBytes_low 304#64 _ (by simp [slice16_length])
  have h144_eq : (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes (nfsSp s₀ + 288#64)
        (slice16 (keyBlock key) 0)).writeBytes (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)).readBytes
        (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    rw [readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        (agreesOutside_toFrame hA_432).readBytes_eq
          (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide), hk0_drop32]
  refine ⟨by simp only [arm64_norm], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm], hal_nfs, by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩, ?_,
    by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm], ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact hM_final
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact h144_eq
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

set_option maxHeartbeats 1600000 in
/-- `HookSatExactMemcpy` sibling of `NewFromSlice3Proof.nfs_first_half_placed`
(`NewFromSliceFirstHalf.lean:1167`). -/
public theorem nfs_first_half_placed_exact [LibsignalPlacement] {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = (blkPl_402).base + 1260#64 ∧ s'.status = .Running ∧
      NfsRegInv3 nfs3PlacedFakeB s₀ s' ∧ NfsMemInv3 nfs3PlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧ s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 = (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  intro key
  have hkey_len : key.length ≤ 64 := by dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  refine (nfs_seg0_placed_exact h_mc hpc hstat hlen hiv hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hread_key hdisj_key_stack hal).trans fun s1 h1 => ?_
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

set_option maxHeartbeats 1600000 in
/-- `HookSatExactMemcpy` sibling of `NewFromSlice3Proof.new_from_slice3_placed_run`
(`NewFromSlice.lean:980`). -/
public theorem new_from_slice3_placed_run_exact [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  have hkey_len : (s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat).length ≤ 64 := by
    rw [Memory.readBytes_length]; exact hlen
  refine (nfs_first_half_placed_exact h_mc hpc hstat hlen hiv hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hread_key hdisj_key_stack hal).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx0_1, hx1_1, hx2_1, hist1, hblk1, hivsw1⟩
  exact nfs_second_half_placed h_compress hkey_len hal hpc1 hstat1 hR1 hM1 hx0_1 hx1_1 hx2_1 hist1 hblk1 hivsw1

/-- `HookSatExactMemcpy` sibling of `NewFromSlice3Proof.new_from_slice3_placed_ro_ok`
(`NewFromSlice.lean:1021`). -/
public theorem new_from_slice3_placed_ro_ok_exact [LibsignalPlacement] (F : ShaCompress)
    {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok (lsProg_402 H) (blkPl_402).base
      { newFromSliceSpec F with
        pre := fun x s0 => (newFromSliceSpec F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ } := by
  refine subroutine_ok_intro fun ⟨ret, keyA, key⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [newFromSliceSpec] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, ⟨hx0, hx1, hx2_nat, hkey_len⟩, hsep⟩
  have hb_out := IsBlock.memRegion ret 0x98
  have hb_key := IsBlock.pointsToBytes (a := keyA) key
  have hb_stk := IsBlock.memRegion (s0.sp - 544#64) 544
  have hsep_out : s0.mem ⊨ memRegion ret 0x98 ∗ (memRegion (s0.sp - 544#64) 544 ∗
      ((keyA ↦ₛ key) ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep; ac_nf at hsep ⊢
  have hsep_key : s0.mem ⊨ (keyA ↦ₛ key) ∗ (memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗ R) := by
    simp only [newFromSliceStack, stackAt] at hsep; ac_nf at hsep ⊢
  have hkey_eq : s0.mem.readBytes keyA key.length = key := (hb_key.read hsep_key).2
  have hrw_out : s0.mem.RW ret 0x98 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_key : s0.mem.RW keyA key.length := fun a ha => hb_key.permNoLazy_rw hsep_key ha
  have hrw_stk : s0.mem.RW (s0.sp - 544#64) 544 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_spqrSha256IV hro
  have hread_iv : s0.mem.Readable spqrSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hdisj_key : key.length = 0 ∨ DisjointRegions keyA key.length (s0.sp - 544#64) 544 := by
    rcases key with _ | ⟨k0, ks⟩
    · exact Or.inl rfl
    · exact Or.inr (hb_key.disjoint hb_stk (by simp) (by decide) hsep_key)
  have hx2_len : (s0.readReg64 .x2).toNat = key.length := hx2_nat
  have hrunsTo := new_from_slice3_placed_run_exact (F := F) h_mc h_compress
    hpc hrun (by rw [hx2_len]; exact hkey_len) hiv_eq hread_iv
    (disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk)
    (by rw [hx0]; exact hrw_out) hrw_stk
    (by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out)
    (by rw [hx1, hx2_len]; exact readable_of_rw hrw_key)
    (by rw [hx1, hx2_len]; exact hdisj_key)
    (by simpa [State.spAligned] using hsp)
  rw [hx1, hx2_len, hkey_eq] at hrunsTo
  refine hrunsTo.to_reaches_pc fun sf h5 _ _ htr hvregs => ?_
  rcases h5 with ⟨hpc_sf, hstat_sf, hcallee, hret_sf, hst_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_,
    CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩
  dsimp only [newFromSliceSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, ?_⟩
  rw [hx0] at hret_sf hst_sf hframe_sf
  have hpost := Frame.update_two_blocks hb_out
    (isBlock_nfsResult F ret key) hb_stk hb_stk hsep_out hframe_sf ⟨hret_sf, hst_sf⟩ trivial
  simp only [newFromSliceStack, stackAt]
  ac_nf at hpost ⊢

/-- `withLsCodeLoaded` corollary of `new_from_slice3_placed_ro_ok_exact`. -/
public theorem new_from_slice3_placed_ok_withLsCodeLoaded_ro_exact [LibsignalPlacement] (F : ShaCompress)
    {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok (lsProg_402 H) (blkPl_402).base
      (withLsCodeLoaded lsmpl
        { newFromSliceSpec F with
          pre := fun x s0 => (newFromSliceSpec F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ }) :=
  subroutine_ok_withLsCodeLoaded_of_plain (new_from_slice3_placed_ro_ok_exact F h_mc h_compress)

/-! ## 2. `key.length > 64` Exact `memcpy` Segment (`nfs_seg0a_gt64_placed_exact`, Block `402`) -/

set_option maxHeartbeats 1600000 in
/-- `HookSatExactMemcpy` sibling of `NewFromSlice3GenProof.nfs_seg0a_gt64_placed`
(`NewFromSliceGt64.lean:712`). -/
public theorem nfs_seg0a_gt64_placed_exact [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) {s₀ s : State}
    (hs : StateG0 nfs3CodeFakeB s₀ s nfs3PlacedFakeB)
    (hgt : 64 < (s₀.readReg64 .x2).toNat)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32)
    (hdisj_iv_stack : DisjointRegions (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s (StateG1 nfs3CodeFakeB F key s₀ · nfs3PlacedFakeB) := by
  intro key
  rcases hs with ⟨hpc, hcom, hx1, hx2⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hag_zero⟩
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 :=
    agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀) (nfsZeroMem s₀) (nfsSp s₀ + 112#64) 64 :=
    agreesOutside_nfsZeroMem s₀
  have hRW_pro : (nfsPrologueMem s₀).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack
  have hRW_zero : (nfsZeroMem s₀).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr hRW_pro
  have hread_iv_s : s.mem.Readable (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 :=
    (Frame.readable_iff (agreesOutside_toFrame hag_zero) _ _).mpr
      ((Frame.readable_iff (agreesOutside_toFrame hA_zero) _ _).mpr
        ((Frame.readable_iff (agreesOutside_toFrame hA_pro) _ _).mpr hread_iv))
  try simp only [arm64_norm] at hread_iv_s
  have hiv_s : s.mem.readBytes (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV := by
    have hd0 : DisjointRegions (nfsSp s₀ + 176#64) 288 (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
      clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
    have hd1 : DisjointRegions (nfsSp s₀ + 112#64) 64 (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
      clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
    have hd2 : DisjointRegions (nfsSp s₀ + 464#64) 80 (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
      clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
    rw [(agreesOutside_toFrame hag_zero).readBytes_eq (by simp only [List.mem_singleton, forall_eq]; exact hd0) (by decide),
        (agreesOutside_toFrame hA_zero).readBytes_eq (by simp only [List.mem_singleton, forall_eq]; exact hd1) (by decide),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp only [List.mem_singleton, forall_eq]; exact hd2) (by decide), hiv]
  iterate 12 sess_step
  set m_pre_c1 := ((s.mem.write8 (nfsSp s₀ + 239#64) 0#8).writeBytes
    (nfsSp s₀ + 240#64) (shaStateBytes sha256IV)).write64
    (nfsSp s₀ + 272#64) (s₀.readReg64 .x2 >>> 6)
  have hag_pre_c1 : AgreesOutside (nfsZeroMem s₀) m_pre_c1 (nfsSp s₀ + 176#64) 288 := by
    have h1 := agreesOutside_sub_176_288 hag_zero
      (AgreesOutside.write8_self s.mem (nfsSp s₀ + 239#64) 0#8) (by decide)
    have h2 : AgreesOutside (s.mem.write8 (nfsSp s₀ + 239#64) 0#8)
        ((s.mem.write8 (nfsSp s₀ + 239#64) 0#8).writeBytes (nfsSp s₀ + 240#64) (shaStateBytes sha256IV))
        (nfsSp s₀ + 240#64) 32 := by
      have hlen : (shaStateBytes sha256IV).length = 32 := shaStateBytes_length sha256IV
      rw [← hlen]; exact ProofLib.agreesOutside_writeBytes _ _ _
    have h3 := agreesOutside_sub_176_288 h1 h2 (by decide)
    exact agreesOutside_sub_176_288 h3
      (AgreesOutside.write64_self _ (nfsSp s₀ + 272#64) (s₀.readReg64 .x2 >>> 6)) (by decide)
  have hst_pre_c1 : m_pre_c1.readBytes (nfsSp s₀ + 240#64) 32 = shaStateBytes sha256IV := by
    dsimp only [m_pre_c1]
    have hd : DisjointRegions (nfsSp s₀ + 272#64) 8 (nfsSp s₀ + 240#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    rw [(agreesOutside_toFrame (AgreesOutside.write64_self _ (nfsSp s₀ + 272#64) _)).readBytes_eq
      (by simp [hd]) (by decide)]
    exact readBytes_writeBytes_eq _ _ _ 32 (shaStateBytes_length sha256IV) (by decide)
  have hkey_pre_c1 : m_pre_c1.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    have hd1 : DisjointRegions (nfsSp s₀ + 176#64) 288 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    have hd2 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    have hd3 : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    rw [(agreesOutside_toFrame hag_pre_c1).readBytes_eq (by simp [hd1]) (by omega),
        (agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hd2]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hd3]) (by omega)]
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_gt : 64 < key.length := by omega
  have hkey_lt : key.length < 2 ^ 63 := by omega
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := ikm_split_lemmas hkey_lt
  have hpfx_pre_c1 : m_pre_c1.readBytes (s₀.readReg64 .x1) (64 * (key.length / 64)) =
      key.take (64 * (key.length / 64)) := by
    rw [readBytes_take_of_le m_pre_c1 (s₀.readReg64 .x1) (by omega : 64 * (key.length / 64) ≤ (s₀.readReg64 .x2).toNat),
        hkey_pre_c1]
  have hrw_pre_c1 : m_pre_c1.RW (nfsSp s₀ + 240#64) 32 :=
    ((Frame.rw_iff (agreesOutside_toFrame hag_pre_c1) _ _).mpr hRW_zero).sub (by clear * -; bv_omega)
  refine placed_compress256_multi_step h_compress
    (by simp only [arm64_norm, hstat]) rfl (by simp only [arm64_norm])
    (by simp only [arm64_norm, hx1])
    (by
      simp only [arm64_norm]
      have hx2_eq : s₀.readReg64 .x2 = BitVec.ofNat 64 key.length := by
        rw [hkey_len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [hx2_eq, hs1])
    (by simp only [arm64_norm]; rfl)
    (by
      rw [State.mem_setMem]
      dsimp only [m_pre_c1]
      rw [write64_quad_240_iv_placed (s.mem.write8 (nfsSp s₀ + 239#64) 0#8) s.mem (nfsSp s₀) (by simpa only [arm64_norm] using hiv_s)])
    hst_pre_c1 hpfx_pre_c1 rfl hrw_pre_c1 ?_
  set st0 := (chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV
  set m_post_c1 := m_pre_c1.writeBytes (nfsSp s₀ + 240#64) (shaStateBytes st0)
  have hag_post_c1 : AgreesOutside (nfsZeroMem s₀) m_post_c1 (nfsSp s₀ + 176#64) 288 := by
    have h2 : AgreesOutside m_pre_c1 m_post_c1 (nfsSp s₀ + 240#64) 32 := by
      have hlen : (shaStateBytes st0).length = 32 := shaStateBytes_length st0
      rw [← hlen]; exact ProofLib.agreesOutside_writeBytes _ _ _
    exact agreesOutside_sub_176_288 hag_pre_c1 h2 (by decide)
  have hRW_post_c1 : m_post_c1.RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hag_post_c1) _ _).mpr hRW_zero
  iterate 5 sess_step
  have hx2_eq : s₀.readReg64 .x2 = BitVec.ofNat 64 key.length := by
    rw [hkey_len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  set m_pre_mc := m_post_c1.write8 (nfsSp s₀ + 239#64) (BitVec.truncate 8 (s₀.readReg64 .x2 &&& 63#64))
  have hag_pre_mc : AgreesOutside (nfsZeroMem s₀) m_pre_mc (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 hag_post_c1
      (AgreesOutside.write8_self m_post_c1 (nfsSp s₀ + 239#64) _) (by decide)
  have hkey_pre_mc : m_pre_mc.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    have hd1 : DisjointRegions (nfsSp s₀ + 176#64) 288 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    have hd2 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    have hd3 : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    rw [(agreesOutside_toFrame hag_pre_mc).readBytes_eq (by simp [hd1]) (by omega),
        (agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hd2]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hd3]) (by omega)]
  have htail_pre_mc : m_pre_mc.readBytes
      (s₀.readReg64 .x1 + (s₀.readReg64 .x2 &&& 9223372036854775744#64))
      (key.length - 64 * (key.length / 64)) =
      key.drop (64 * (key.length / 64)) := by
    rw [hx2_eq, hs3]
    have hsplit : (s₀.readReg64 .x2).toNat =
        64 * (key.length / 64) + (key.length - 64 * (key.length / 64)) := by omega
    have hadd := readBytes_add m_pre_mc (s₀.readReg64 .x1)
      (64 * (key.length / 64)) (key.length - 64 * (key.length / 64))
    rw [← hsplit, hkey_pre_mc] at hadd
    have hdrop := congrArg (List.drop (64 * (key.length / 64))) hadd.symm
    rwa [List.drop_left' (Memory.readBytes_length _ _ _)] at hdrop
  have hrw_pre_mc : m_pre_mc.RW (nfsSp s₀ + 176#64) (key.length - 64 * (key.length / 64)) := by
    have hlt64 : key.length - 64 * (key.length / 64) < 64 := by omega
    exact ((Frame.rw_iff (agreesOutside_toFrame hag_pre_mc) _ _).mpr hRW_zero).sub (by
      generalize key.length - 64 * (key.length / 64) = len at hlt64 ⊢
      clear * - hlt64; bv_omega)
  have hread_key_mc : m_pre_mc.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat :=
    (Frame.readable_iff (agreesOutside_toFrame hag_pre_mc) _ _).mpr
      ((Frame.readable_iff (agreesOutside_toFrame hA_zero) _ _).mpr
        ((Frame.readable_iff (agreesOutside_toFrame hA_pro) _ _).mpr hread_key))
  have hread_tail_mc : m_pre_mc.Readable
      (s₀.readReg64 .x1 + (s₀.readReg64 .x2 &&& 9223372036854775744#64))
      (key.length - 64 * (key.length / 64)) := by
    rw [hx2_eq, hs3]
    intro a ha
    refine hread_key_mc a ?_
    have htot : (BitVec.ofNat 64 (64 * (key.length / 64))).toNat +
        (key.length - 64 * (key.length / 64)) ≤ (s₀.readReg64 .x2).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    generalize BitVec.ofNat 64 (64 * (key.length / 64)) = d at ha htot
    generalize key.length - 64 * (key.length / 64) = len at ha htot
    clear * - ha htot hlt
    dsimp only [InRegion] at ha ⊢
    bv_omega
  have hdisj_tail_mc : (key.length - 64 * (key.length / 64)) = 0 ∨
      DisjointRegions (nfsSp s₀ + 176#64) (key.length - 64 * (key.length / 64))
        (s₀.readReg64 .x1 + (s₀.readReg64 .x2 &&& 9223372036854775744#64))
        (key.length - 64 * (key.length / 64)) := by
    by_cases h0 : key.length - 64 * (key.length / 64) = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      rw [hx2_eq, hs3]
      refine ((hdisj_key_stack.sub_left
        (s₀.readReg64 .x1 + BitVec.ofNat 64 (64 * (key.length / 64))) ?_).sub_right
        (nfsSp s₀ + 176#64) ?_).symm
      · refine ⟨by omega, ?_⟩
        have htot : (BitVec.ofNat 64 (64 * (key.length / 64))).toNat +
            (key.length - 64 * (key.length / 64)) ≤ (s₀.readReg64 .x2).toNat := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
        generalize BitVec.ofNat 64 (64 * (key.length / 64)) = d at htot ⊢
        generalize key.length - 64 * (key.length / 64) = tl at htot ⊢
        clear * - htot hlt
        bv_omega
      · refine ⟨by omega, ?_⟩
        have htl_lt : key.length - 64 * (key.length / 64) < 64 := by omega
        generalize key.length - 64 * (key.length / 64) = tl at htl_lt ⊢
        clear * - htl_lt
        simp only [nfsSp]
        bv_omega
  refine placed_memcpy_step_of_exact h_mc
    (by simp only [arm64_norm, hstat])
    (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp, hal_nfs])
    rfl (by simp only [arm64_norm])
    (by simp only [arm64_norm, hx1])
    (by simp only [arm64_norm, hx2_eq, hs4])
    (by simp only [arm64_norm]; rfl)
    (State.mem_setMem _ _) htail_pre_mc hrw_pre_mc hread_tail_mc hdisj_tail_mc
    fun c => ?_
  dsimp only [applyMemcpyClobber]
  refine RunsTo.refl ?_ (htr := by prove_trace_eq)
  set tail := key.drop (64 * (key.length / 64))
  have htail_len : tail.length = key.length - 64 * (key.length / 64) := by simp [tail]
  have htail_lt : tail.length < 64 := by omega
  set m_end := m_pre_mc.writeBytes (nfsSp s₀ + 176#64) tail
  have hag_mc : AgreesOutside m_pre_mc m_end (nfsSp s₀ + 176#64) tail.length :=
    ProofLib.agreesOutside_writeBytes m_pre_mc (nfsSp s₀ + 176#64) tail
  have hag_end : AgreesOutside (nfsZeroMem s₀) m_end (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 hag_pre_mc hag_mc
      (by generalize tail.length = tl at htail_lt ⊢; clear * - htail_lt; bv_omega)
  refine
    { pc_eq := by simp only [arm64_norm]
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
          agrees_zero := hag_end }
      tail_bytes := by
        rw [State.mem_setPC, State.mem_setMem]
        exact readBytes_writeBytes_eq m_pre_mc (nfsSp s₀ + 176#64) tail
          (key.length - 64 * (key.length / 64)) htail_len (by omega)
      pos_byte := by
        have hd : DisjointRegions (nfsSp s₀ + 176#64) tail.length (nfsSp s₀ + 239#64) 1 := by
          generalize tail.length = tl at htail_lt ⊢; clear * - htail_lt; simp only [DisjointRegions]; bv_omega
        have h1 : m_end.read8 (nfsSp s₀ + 239#64) = m_pre_mc.read8 (nfsSp s₀ + 239#64) :=
          hag_mc.1 (nfsSp s₀ + 239#64) (by generalize tail.length = tl at htail_lt ⊢; clear * - htail_lt; simp only [OutsideRegion]; bv_omega)
        rw [State.mem_setPC, State.mem_setMem, h1]
        dsimp only [m_pre_mc]
        rw [Memory.read8_write8_same, hx2_eq, hs5]
      st0_bytes := by
        have hd1 : DisjointRegions (nfsSp s₀ + 176#64) tail.length (nfsSp s₀ + 240#64) 32 := by
          generalize tail.length = tl at htail_lt ⊢; clear * - htail_lt; simp only [DisjointRegions]; bv_omega
        have hd2 : DisjointRegions (nfsSp s₀ + 239#64) 1 (nfsSp s₀ + 240#64) 32 := by
          clear * -; simp only [DisjointRegions]; bv_omega
        rw [State.mem_setPC, State.mem_setMem,
            (agreesOutside_toFrame hag_mc).readBytes_eq (by simp [hd1]) (by decide)]
        dsimp only [m_pre_mc]
        rw [(agreesOutside_toFrame (AgreesOutside.write8_self m_post_c1 (nfsSp s₀ + 239#64) _)).readBytes_eq
              (by simp [hd2]) (by decide)]
        exact readBytes_writeBytes_eq m_pre_c1 (nfsSp s₀ + 240#64) (shaStateBytes st0) 32
          (shaStateBytes_length st0) (by decide)
      nblk_word := by
        have hd1 : DisjointRegions (nfsSp s₀ + 176#64) tail.length (nfsSp s₀ + 272#64) 8 := by
          generalize tail.length = tl at htail_lt ⊢; clear * - htail_lt; simp only [DisjointRegions]; bv_omega
        have hd2 : DisjointRegions (nfsSp s₀ + 239#64) 1 (nfsSp s₀ + 272#64) 8 := by
          clear * -; simp only [DisjointRegions]; bv_omega
        have hd3 : DisjointRegions (nfsSp s₀ + 240#64) 32 (nfsSp s₀ + 272#64) 8 := by
          clear * -; simp only [DisjointRegions]; bv_omega
        rw [State.mem_setPC, State.mem_setMem,
            (agreesOutside_toFrame hag_mc).read64_eq (by simp [hd1])]
        dsimp only [m_pre_mc]
        rw [(agreesOutside_toFrame (AgreesOutside.write8_self m_post_c1 (nfsSp s₀ + 239#64) _)).read64_eq
              (by simp [hd2])]
        dsimp only [m_post_c1]
        rw [(agreesOutside_toFrame (ProofLib.agreesOutside_writeBytes m_pre_c1 (nfsSp s₀ + 240#64) (shaStateBytes st0))).read64_eq
              (by simp [shaStateBytes_length, hd3])]
        dsimp only [m_pre_c1]
        rw [Memory.read64_write64_same, hx2_eq]
        apply BitVec.eq_of_toNat_eq
        rw [hs1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] }

end LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceSegsExact
