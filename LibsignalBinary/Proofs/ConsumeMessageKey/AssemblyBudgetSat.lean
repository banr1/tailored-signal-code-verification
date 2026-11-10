/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudgetSat -- proof-setup: allow-public-import
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlockExact
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceExact
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `HookSat`-Backed Budget-Threaded Refinement for `RatchetState::consume_message_key`

Proves the budget-threaded placed `hmac_sha256` and `consume_message_key` contracts assuming
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec` rather than concrete `memset` hook equality.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetSat

open Arm64 Arm64.Obj ProofLib
open CryptoGames.HMAC (ShaState hmacWith sha256IV)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
  blkLib_eq_73 blkLib_eq_114
  blkPC_24 blkPC_73 blkPC_114 blkPl_24 blkPl_73 blkPl_114
  extract_withLsCodeLoaded libsignalRoLoaded_of_keepsFrozen
  libsignalSessionExterns libsignalSessionLib
  lsBlackBoxU8Sym lsNoAllocShimSym lsProg_73 lsProg_114 lsRustReallocSym
  ls_externAt?_blockProgram_eq_of_externs_eq ls_subroutine_ok_of_block
  lsmpl withLsCodeLoaded
)
open CryptoVerification.LibsignalAesCbc (memcpyHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  AgreesOutside.write64_self CalleeSaved CallingConventionPreserved_of_calleeSaved Frame
  Frame.trans_nfs HmacPlacedPre HmacSaved HmacSt Layout.readBytes_writeBytes_eq NfsMemInv
  NfsRegInv NfsSavedStack RW RunsTo RunsTo.lsProg_svc RunsTo.pairStep_114_0x28 StateH0Placed
  StateH1Placed StateH1mPlaced StateH1pPlaced StateH2Placed StateH5 TraceEq
  agreesOutside_nfsPrologueMem agreesOutside_toFrame disjointRegions_of_ro_rw hmacPlacedSpec
  hookMemcpy_eq_memcpyHook hsp hsp_align hsp_sub_544_eq innerState keyBlock keyBlock_length
  length_hmacWith lsCompress256Sym lsMemcpySym lsMemsetSym lsSha256IVAddr
  new_from_slice_placed_run nfsPlacedFakeB nfsPlacedFakeB_add_iv nfsPrologueMem
  nfsSavedStack_prologue_432 nfsSp nfs_chunk1_placed nfs_chunk2_placed nfs_chunk3_placed
  nfs_chunk4_placed nfs_second_half_placed nfs_sp_add_464_align nfs_sp_add_544_align nfs_sp_align
  nfs_sp_eq_add nfs_ule_65_false outerState read64_writeBytes_replicate_off_disjoint
  read64_writeBytes_replicate_zero_off readBytes_32_eq_of_read64_eq readBytes_writeBytes_16_other
  readBytes_writeBytes_16_self readBytes_writeBytes_replicate_off_disjoint rodata_placed_sha256IV
  seg0a_placed_runsTo seg1a_placed_runsTo seg1b1_placed_runsTo seg2_placed_runsTo
  seg3_placed_runsTo seg4_placed_runsTo slice16 slice16_length toLEBytes_8_read64_writeBytes_146_62
  write64_oct_zero_eq_writeBytes_64 write64_quad_288_eq_writeBytes_slice16 writeBytes_key_over_zero64
  writeBytes_singleton
)
open CryptoVerification.LibsignalTripleRatchet.Extract (
  CallingConventionPreserved.x19 CallingConventionPreserved.x20
  CallingConventionPreserved.x21 CallingConventionPreserved.x22
  CallingConventionPreserved.x27 CallingConventionPreserved.x29 S2Frame
)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (AgreesOn)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (GrowOnePlacedOk hmacSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks FindIndexPlacedOk HmacPlacedOk HmacPlacedRoOk
)
open LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudgetSat (
  CmkPlacedRunStmtSat consume_message_key_placed_ro_run_of_sat consume_message_key_placed_run_of_sat
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux (
  hmacPlacedPre_stripS stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw
  unstrip_frame
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat (
  hmacCompressOnlyExcHooks hmacCompressOnlyExcHooks_compress
  placed_memset_budget_steps_sat runsTo_block_lift_vm_compress_only
)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat (
  hmacSaved_of_agreesOn s2Frame_of_hmacFrame s2Frame_readBytes_eq_of_readable
  s2Frame_readable_of_readable
)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacSat (StateH2PlacedSat StateH5Sat)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (
  HookSatExactMemcpy placed_memcpy_step_of_exact
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (
  CallingConventionPreserved.x23 CallingConventionPreserved.x24
  CallingConventionPreserved.x25 CallingConventionPreserved.x26
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds

private theorem stripS_read8 (p : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS p s).mem.read8 a = s.mem.read8 a := by
  cases s; simp [ProofLib.stripS, ProofLib.strip_read8]

private theorem stripS_read64 (p : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS p s).mem.read64 a = s.mem.read64 a := by
  cases s; simp [ProofLib.stripS, Memory.read64, ProofLib.strip_read8]

private theorem stripExecOutside_hmacSt {F : ShaState → List (BitVec 8) → ShaState}
    {p : BitVec 64 → Bool} {m : Memory} {a : BitVec 64} {key msg : List (BitVec 8)} :
    CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt
      (ProofLib.stripExecOutside p m) a F key msg ↔
    CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt m a F key msg := by
  unfold CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt
  simp only [stripExecOutside_readBytes, Memory.read64, ProofLib.strip_read8]

private theorem runsTo_73_to_bp [LibsignalPlacement] {X : LibsignalHooks}
    {s : State} {P : State → Prop} (h : RunsTo (lsProg_73 X) s P) :
    RunsTo (libsignalSessionLib.blockProgram lsmpl 73 X) s P := by
  rwa [← IsLsBlockProg.eq_blockProgram (prog := lsProg_73 X)]

private theorem steps_bp_to_73 [LibsignalPlacement] {X : LibsignalHooks} {s s' : State}
    (h : Steps (libsignalSessionLib.blockProgram lsmpl 73 X) s s') :
    Steps (lsProg_73 X) s s' := by
  rwa [IsLsBlockProg.eq_blockProgram (prog := lsProg_73 X)]

private theorem stripS_hmacSaved (p : BitVec 64 → Bool) (s0 s : State) :
    HmacSaved (ProofLib.stripS p s0) (hsp (ProofLib.stripS p s0)) (ProofLib.stripS p s).mem ↔
    HmacSaved s0 (hsp s0) s.mem := by
  have hsp0 : hsp (ProofLib.stripS p s0) = hsp s0 := by cases s0; rfl
  have hr : ∀ r, (ProofLib.stripS p s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  unfold HmacSaved
  simp only [hsp0, stripS_read64, hr]

private theorem runsTo_114_to_bp [LibsignalPlacement] {X : LibsignalHooks}
    {s : State} {P : State → Prop} (h : RunsTo (lsProg_114 X) s P) :
    RunsTo (libsignalSessionLib.blockProgram lsmpl 114 X) s P := by
  rwa [← IsLsBlockProg.eq_blockProgram (prog := lsProg_114 X)]

private theorem steps_bp_to_114 [LibsignalPlacement] {X : LibsignalHooks} {s s' : State}
    (h : Steps (libsignalSessionLib.blockProgram lsmpl 114 X) s s') :
    Steps (lsProg_114 X) s s' := by
  rwa [IsLsBlockProg.eq_blockProgram (prog := lsProg_114 X)]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option linter.unnecessarySimpa false in
set_option maxHeartbeats 3200000 in
private theorem nfs_seg0_placed_vm_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
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
    (hread_key_s0 : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_114 H) s₀ (fun s' =>
      VmPreserved s₀ s' ∧
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
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    have hdisj_key_112 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    rw [(agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hdisj_key_112]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdisj_key_pro]) (by omega)]
  have hrw_memcpy : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW
      (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat := by
    have hrw0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW (nfsSp s₀) 544 :=
      (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr
        ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
    exact hrw0.sub (by clear * - hlen; bv_omega)
  have hreadable_memcpy :
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).Readable
        (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat :=
    (Frame.readable_iff (agreesOutside_toFrame hA_zero) _ _).mpr
      ((Frame.readable_iff (agreesOutside_toFrame hA_pro) _ _).mpr hread_key_s0)
  have hdisj_memcpy :
      (s₀.readReg64 .x2).toNat = 0 ∨
        DisjointRegions (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat
          (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · exact Or.inl h0
    · refine Or.inr ?_
      clear * - hdisj_key_stack hlen; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
  refine placed_memcpy_step_of_exact h_memcpy
    (hrun := by simp only [arm64_norm, hstat])
    (hsp := by simp only [State.spAligned, arm64_norm, hal_nfs])
    (hpc := by simp only [arm64_norm, lsMemcpySym])
    (hx0 := by simp only [arm64_norm])
    (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm])
    (hlr := by simp only [arm64_norm]; rfl)
    (hmem := write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀))
    (hread := hread_key)
    (hrw := hrw_memcpy)
    (hreadable := hreadable_memcpy)
    (hdisj := hdisj_memcpy)
    fun c => ?_
  dsimp only [applyMemcpyClobber]
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
    simpa using readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 0 32 (by omega)
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
    readable_iv := by rw [nfsPlacedFakeB_add_iv]; exact (Frame.readable_iff hf_k0 _ _).mpr hread_iv
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
  refine ⟨?_, by simp only [arm64_norm], by simp only [arm64_norm, hstat],
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
  · refine ⟨⟨by cases s₀; rfl, by cases s₀; rfl, by cases s₀; rfl⟩,
      by cases s₀; rfl, fun a => ?_, fun _ _ _ => by cases s₀; rfl⟩
    dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact congrFun hM_final.frame.2.1 a
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact hM_final
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact h144_eq
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

private theorem nfs_post_seg0_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {X : LibsignalHooks} (h_compress : X lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {s₀ s1 : State}
    (hkey_len : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc1 : s1.pc = (blkPl_114).base + 476#64)
    (hstat1 : s1.status = .Running)
    (hR1 : NfsRegInv nfsPlacedFakeB s₀ s1)
    (hM1 : NfsMemInv nfsPlacedFakeB s₀ s1.mem)
    (hx8_1 : s1.readReg64 .x8 = 0x36#64)
    (hx0_1 : s1.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1_1 : s1.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2_1 : s1.readReg64 .x2 = 1#64)
    (hq2_1 : s1.readVReg128 2#5 = s1.mem.read64 (nfsSp s₀ + 152#64) ++ s1.mem.read64 (nfsSp s₀ + 144#64))
    (hq0_1 : s1.readVReg128 0#5 = s1.mem.read64 (nfsSp s₀ + 168#64) ++ s1.mem.read64 (nfsSp s₀ + 160#64))
    (hk0_1 : s1.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32)
    (hs0_1 : s1.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0)
    (hs16_1 : s1.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (lsProg_114 X) s1 (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  refine (nfs_chunk1_placed hkey_len hpc1 hstat1 hR1 hM1 hx8_1 hx0_1 hx1_1 hx2_1 hs0_1 hs16_1).trans fun s2 h2 => ?_
  rcases h2 with ⟨hpc2, hstat2, hR2, hM2, hx8_2, hx0_2, hx1_2, hx2_2, hx10_2, hx11_2, hq2_2, hq0_2, hs0_2, hs16_2⟩
  refine (nfs_chunk2_placed hkey_len hal hpc2 hstat2 hR2 hM2 hx8_2 hx0_2 hx1_2 hx2_2 hx10_2 hx11_2
    (hq2_2.trans hq2_1) (hq0_2.trans hq0_1) hk0_1 hs0_2 hs16_2).trans fun s3 h3 => ?_
  rcases h3 with ⟨hpc3, hstat3, hR3, hM3, hx8_3, hx0_3, hx1_3, hx2_3, hx11_3, hx9_3, hs0_3, hs16_3, hs32_3, hs48_3⟩
  refine (nfs_chunk3_placed hkey_len hpc3 hstat3 hR3 hM3 hx8_3 hx0_3 hx1_3 hx2_3 hx11_3 hx9_3
    hs0_3 hs16_3 hs32_3 hs48_3).trans fun s4 h4 => ?_
  rcases h4 with ⟨hpc4, hstat4, hR4, hM4, hx8_4, hx0_4, hx1_4, hx2_4, hx9_4, hx10_4, hs0_4, hs16_4, hs32_4, hs48_4⟩
  refine (nfs_chunk4_placed hkey_len hal hpc4 hstat4 hR4 hM4 hx8_4 hx0_4 hx1_4 hx2_4 hx9_4 hx10_4
    hs0_4 hs16_4 hs32_4 hs48_4).trans fun s5 h5 => ?_
  rcases h5 with ⟨hpc5, hstat5, hR5, hM5, hx0_5, hx1_5, hx2_5, hist5, hblk5, hivsw5⟩
  exact nfs_second_half_placed h_compress hkey_len hal hpc5 hstat5 hR5 hM5 hx0_5 hx1_5 hx2_5 hist5 hblk5 hivsw5

private theorem new_from_slice_placed_runsTo_vm_sat [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) {s₀ : State}
    (hpc : s₀.pc = (blkPl_114).base) (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable lsSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key_s0 : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hL114 : (lsProg_114 H).CodeLoaded s₀.mem) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    ∃ sf : State,
      Steps (lsProg_114 H) s₀ sf ∧
      VmPreserved s₀ sf ∧
      sf.trace = s₀.trace ∧
      calleeSavedVRegs sf = calleeSavedVRegs s₀ ∧
      sf.pc = s₀.readReg64 .lr ∧ sf.status = .Running ∧ CalleeSaved s₀ sf ∧
      sf.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt sf.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem sf.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)] := by
  intro key
  have hkey_len : key.length ≤ 64 := by
    dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  obtain ⟨s1, hsteps1, htr1, hvregs1,
      ⟨hvm1, hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1, hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩,
      hL1⟩ :=
    nfs_seg0_placed_vm_sat h_memcpy hpc hstat hlen hiv hread_iv hdisj_iv_stack hrw_out hrw_stack
      hdisj_out_stack hread_key_s0 hdisj_key_stack hal hL114
  let Q114 := libsignalSessionLib.blockProgram lsmpl 114 (hmacCompressOnlyExcHooks F H)
  let kp114 := ProofLib.progKeep Q114
  have hc256Q := hmacCompressOnlyExcHooks_compress F H
  have hL1_bp : (libsignalSessionLib.blockProgram lsmpl 114 H).CodeLoaded s1.mem := by
    rwa [← IsLsBlockProg.eq_blockProgram (prog := lsProg_114 H)]
  have hnsp0 : nfsSp (ProofLib.stripS kp114 s₀) = nfsSp s₀ := by cases s₀; rfl
  have hm0_114 : (ProofLib.stripS kp114 s₀).mem = ProofLib.stripExecOutside kp114 s₀.mem := by cases s₀; rfl
  have hm1_114 : (ProofLib.stripS kp114 s1).mem = ProofLib.stripExecOutside kp114 s1.mem := by cases s1; rfl
  have hr0_x0 : (ProofLib.stripS kp114 s₀).readReg64 .x0 = s₀.readReg64 .x0 := by cases s₀; rfl
  have hR1_strip : NfsRegInv nfsPlacedFakeB (ProofLib.stripS kp114 s₀) (ProofLib.stripS kp114 s1) :=
    { sp_eq := by rw [hnsp0]; cases s1; exact hR1.sp_eq, sp_align := by rw [hnsp0]; exact hR1.sp_align
      x29_eq := by rw [hnsp0]; cases s1; exact hR1.x29_eq, x19_eq := by rw [hr0_x0]; cases s1; exact hR1.x19_eq
      x20_eq := by cases s1; exact hR1.x20_eq, x22_eq := by cases s1; exact hR1.x22_eq
      x25_eq := by cases s₀; cases s1; exact hR1.x25_eq, x26_eq := by cases s₀; cases s1; exact hR1.x26_eq
      x27_eq := by cases s₀; cases s1; exact hR1.x27_eq }
  have hsaved1_strip : NfsSavedStack (ProofLib.stripS kp114 s₀) (ProofLib.stripS kp114 s1).mem :=
    { m432 := by rw [hnsp0, stripS_read64]; exact hM1.saved.m432
      m464 := by rw [hnsp0, stripS_read64]; cases s₀; exact hM1.saved.m464
      m472 := by rw [hnsp0, stripS_read64]; cases s₀; exact hM1.saved.m472
      m480 := by rw [hnsp0, stripS_read64]; cases s₀; exact hM1.saved.m480
      m496 := by rw [hnsp0, stripS_read64]; cases s₀; exact hM1.saved.m496
      m504 := by rw [hnsp0, stripS_read64]; cases s₀; exact hM1.saved.m504
      m512 := by rw [hnsp0, stripS_read64]; cases s₀; exact hM1.saved.m512
      m520 := by rw [hnsp0, stripS_read64]; cases s₀; exact hM1.saved.m520
      m528 := by rw [hnsp0, stripS_read64]; cases s₀; exact hM1.saved.m528
      m536 := by rw [hnsp0, stripS_read64]; cases s₀; exact hM1.saved.m536 }
  have hframe1_strip : Frame (ProofLib.stripS kp114 s₀).mem (ProofLib.stripS kp114 s1).mem
      [((ProofLib.stripS kp114 s₀).readReg64 .x0, 0x98), (nfsSp (ProofLib.stripS kp114 s₀), 544)] := by
    rw [hm0_114, hm1_114, hr0_x0, hnsp0]
    exact ⟨fun a hout => by simpa only [ProofLib.strip_read8] using hM1.frame.1 a hout,
      funext fun a => by simp [ProofLib.strip_perm, hvm1.perm_eq a],
      fun a hout => by simpa only [ProofLib.strip_isLazyFree] using hM1.frame.2.2.1 a hout,
      fun a hlf => by simpa only [ProofLib.strip_isLazyFree] using
        hM1.frame.2.2.2.1 a (by simpa only [ProofLib.strip_isLazyFree] using hlf),
      fun a han => by simpa only [ProofLib.strip_isAnon] using
        hM1.frame.2.2.2.2 a (by simpa only [ProofLib.strip_isAnon] using han)⟩
  have hM1_strip : NfsMemInv nfsPlacedFakeB (ProofLib.stripS kp114 s₀) (ProofLib.stripS kp114 s1).mem :=
    { rw_stack := by rw [hm1_114, hnsp0]; exact stripExecOutside_rw kp114 s1.mem _ _ hM1.rw_stack
      rw_out := by rw [hm1_114, hr0_x0]; exact stripExecOutside_rw kp114 s1.mem _ _ hM1.rw_out
      readable_iv := by rw [hm1_114]; exact stripExecOutside_readable kp114 s1.mem _ _ hM1.readable_iv
      iv_bytes := by rw [hm1_114, stripExecOutside_readBytes]; exact hM1.iv_bytes
      disj_iv_stack := by rw [hnsp0]; exact hM1.disj_iv_stack
      disj_out_stack := by rw [hr0_x0, hnsp0]; exact hM1.disj_out_stack
      saved := hsaved1_strip, frame := hframe1_strip }
  have hrunsP := runsTo_114_to_bp (nfs_post_seg0_runsTo h_compress hkey_len hal hpc1 hstat1 hR1 hM1
    hx8_1 hx0_1 hx1_1 hx2_1 hq2_1 hq0_1 hk0_1 hs0_1 hs16_1)
  have hrunsQ := runsTo_114_to_bp (nfs_post_seg0_runsTo hc256Q hkey_len
    (by cases s₀; exact hal) (by cases s1; exact hpc1) (by cases s1; exact hstat1) hR1_strip hM1_strip
    (by cases s1; exact hx8_1) (by rw [hnsp0]; cases s1; exact hx0_1)
    (by rw [hnsp0]; cases s1; exact hx1_1) (by cases s1; exact hx2_1)
    (by rw [hnsp0, stripS_read64, stripS_read64]; cases s1; exact hq2_1)
    (by rw [hnsp0, stripS_read64, stripS_read64]; cases s1; exact hq0_1)
    (by rw [hnsp0, hm1_114, stripExecOutside_readBytes]; exact hk0_1)
    (by rw [hnsp0, hm1_114, stripExecOutside_readBytes]; exact hs0_1)
    (by rw [hnsp0, hm1_114, stripExecOutside_readBytes]; exact hs16_1))
  obtain ⟨sf, hsteps_tail_bp, hvm_tail, htr_tail, hvregs_tail, hsf_or⟩ :=
    runsTo_block_lift_vm_compress_only h_compress blkLib_eq_114 rfl rfl hL1_bp
      hrunsP hrunsQ (fun _ hs => hs.2.1) (fun _ hs => hs.2.1)
  have hsteps_tail : Steps (lsProg_114 H) s1 sf := steps_bp_to_114 hsteps_tail_bp
  have hvm_all : VmPreserved s₀ sf := hvm1.trans hvm_tail
  refine ⟨sf, hsteps1.trans hsteps_tail, hvm_all, htr_tail.trans htr1, hvregs_tail.trans hvregs1, ?_⟩
  rcases hsf_or with hsf_strip | hsf_real
  · rcases hsf_strip with ⟨hpc_f, hstat_f, hcs_f, htag_f, hhmac_f, hframe_f⟩
    have hmf_114 : (ProofLib.stripS kp114 sf).mem = ProofLib.stripExecOutside kp114 sf.mem := by cases sf; rfl
    have hr0_lr : (ProofLib.stripS kp114 s₀).readReg64 .lr = s₀.readReg64 .lr := by cases s₀; rfl
    have hsp_s0 : (ProofLib.stripS kp114 s₀).sp = s₀.sp := by cases s₀; rfl
    rw [hm0_114, hmf_114, hr0_x0, hsp_s0] at hframe_f
    rw [hmf_114, hr0_x0] at hhmac_f
    exact ⟨by rw [hr0_lr] at hpc_f; cases sf; exact hpc_f,
      by cases sf; exact hstat_f,
      ⟨by cases s₀; cases sf; exact hcs_f.1,
       fun r hr => by have := hcs_f.2 r hr; cases s₀; cases sf; exact this⟩,
      by rw [hr0_x0, stripS_read64] at htag_f; exact htag_f,
      stripExecOutside_hmacSt.mp hhmac_f,
      unstrip_frame hframe_f hvm_all.perm_eq⟩
  · exact hsf_real

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option linter.unnecessarySimpa false in
set_option maxHeartbeats 1600000 in
private theorem seg1b1_placed_runsTo_vm_sat [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH1mPlaced F key s₀ s) :
    RunsTo (lsProg_73 H) s (fun s' => VmPreserved s s' ∧ StateH1pPlaced F key byte s₀ s') := by
  generalize hPost : (fun s' : State => VmPreserved s s' ∧ StateH1pPlaced F key byte s₀ s') = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx21, hx22, hx23, hx25, hist, hibl, host, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by clear * -; unfold hsp; bv_omega)
  have hinp_s : s.mem.readBytes (s₀.readReg64 .x3) 1 = [byte] := by
    rw [hframe.readBytes_eq (by simp [hpre.disj_inp_stack.symm]) (by decide), hpre.inp_eq]
  have hread_inp_s : s.mem.Readable (s₀.readReg64 .x3) 1 :=
    (hframe.readable_iff _ _).mpr hpre.read_inp
  have hdisj_inp : 1 = 0 ∨ DisjointRegions (hsp s₀) 1 (s₀.readReg64 .x3) 1 :=
    Or.inr ((hpre.disj_inp_stack.sub_right _ ⟨by decide, by clear * -; unfold hsp; bv_omega⟩).symm)
  refine placed_memcpy_step_of_exact h_memcpy
    (hrun := hstat)
    (hsp := by simp only [State.spAligned, hsp_eq, hal_hsp]; rfl)
    (hpc := hpc) (hx0 := hx0) (hx1 := hx1) (hx2 := by rw [hx2]; rfl)
    (hlr := hlr) (hmem := rfl) (hread := hinp_s) (hrw := hrw_hsp.sub (by clear * -; bv_omega))
    (hreadable := hread_inp_s) (hdisj := hdisj_inp)
    fun c => ?_
  dsimp only [applyMemcpyClobber]
  rw [writeBytes_singleton]
  iterate 25 sess_step
  subst hPost; refine RunsTo.refl ⟨?_, ?_⟩
  · refine ⟨⟨by cases s; rfl, by cases s; rfl, by cases s; rfl⟩,
      by cases s; rfl, fun a => ?_, fun _ _ _ => by cases s; rfl⟩
    dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp only [Memory.perm_write8, Memory.perm_write64]
  refine ⟨by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, lsMemsetSym],
    ⟨by simp only [arm64_norm, hstat], by simp only [arm64_norm, hsp_eq],
     by simp only [arm64_norm, hx29], by simp only [arm64_norm, hx27], ?_, ?_⟩,
    by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm, hx19], by simp only [arm64_norm],
    by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm, hx22], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm, hibl],
    by simp (config := { decide := true }) only [arm64_norm], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
    dsimp only [HmacSaved, State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine Frame.write8_stack1024 ?_ _ _; iterate 18 refine Frame.write64_stack1024 ?_ _ _
    (iterate 2 refine Frame.write8_stack1024 ?_ _ _); exact hframe
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [← hist]; refine readBytes_32_eq_of_read64_eq _ s.mem (hsp s₀ + 208#64) (hsp s₀ + 64#64) ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hibl]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [← host]; refine readBytes_32_eq_of_read64_eq _ s.mem (hsp s₀ + 248#64) (hsp s₀ + 104#64) ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hobl]

/-- Thread `VmPreserved` across Block 73 (`hmac_sha256`, `compress256`) and Block 114 (`new_from_slice`) under `HookSatExactMemcpy H lsMemcpySym` and `HookSat` for `memset`. -/
theorem hmac_placed_runsTo_vm_sat [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {byte : BitVec 8} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : HmacPlacedPre F key [byte] s0)
    (hread_key : s0.mem.Readable (s0.readReg64 .x1) 32)
    (hL73 : (lsProg_73 H).CodeLoaded s0.mem) :
    ∃ sf : State,
      Steps (lsProg_73 H) s0 sf ∧
      VmPreserved s0 sf ∧
      sf.trace = s0.trace ∧
      calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
      StateH5Sat F key byte s0 sf := by
  have heq73 : ∀ X, lsProg_73 X = libsignalSessionLib.blockProgram lsmpl 73 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := lsProg_73 X)
  have heq114 : ∀ X, lsProg_114 X = libsignalSessionLib.blockProgram lsmpl 114 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := lsProg_114 X)
  let Q73 := libsignalSessionLib.blockProgram lsmpl 73 (hmacCompressOnlyExcHooks F H)
  let kp73 := ProofLib.progKeep Q73
  have hc256Q := hmacCompressOnlyExcHooks_compress F H
  -- Piece 1: `seg0a_placed_runsTo` on Block `73` (`s0 → sc`, 0 extern calls)
  have hL73_bp : (libsignalSessionLib.blockProgram lsmpl 73 H).CodeLoaded s0.mem := by
    rwa [← heq73 H]
  obtain ⟨sc, hsteps0a_bp, hvm0a, htr0a, hvregs0a, hsc_or⟩ :=
    runsTo_block_lift_vm_compress_only h_compress blkLib_eq_73 rfl rfl hL73_bp
      (runsTo_73_to_bp (seg0a_placed_runsTo (H := H) hpre))
      (runsTo_73_to_bp (seg0a_placed_runsTo (H := hmacCompressOnlyExcHooks F H)
        (hmacPlacedPre_stripS kp73 hpre)))
      (fun _ (hs : StateH0Placed s0 _) => hs.common.1)
      (fun _ (hs : StateH0Placed (ProofLib.stripS kp73 s0) _) => hs.common.1)
  have hsteps0a : Steps (lsProg_73 H) s0 sc := steps_bp_to_73 hsteps0a_bp
  have hsc : StateH0Placed s0 sc := by
    rcases hsc_or with hsc_strip | hsc_real
    · rcases hsc_strip with ⟨hpc_c, ⟨hstat_c, hsp_c, hx29_c, hx27_c, hsaved_c, hframe_c⟩,
        hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c, hx21_c⟩
      have hm0 : (ProofLib.stripS kp73 s0).mem = ProofLib.stripExecOutside kp73 s0.mem := by cases s0; rfl
      have hmc : (ProofLib.stripS kp73 sc).mem = ProofLib.stripExecOutside kp73 sc.mem := by cases sc; rfl
      rw [hm0, hmc] at hframe_c
      exact ⟨(by cases sc; exact hpc_c), ⟨(by cases sc; exact hstat_c), (by cases s0; cases sc; exact hsp_c),
        (by cases s0; cases sc; exact hx29_c), (by cases s0; cases sc; exact hx27_c),
        (stripS_hmacSaved kp73 s0 sc).mp hsaved_c, unstrip_frame hframe_c hvm0a.perm_eq⟩,
        (by cases s0; cases sc; exact hx0_c), (by cases s0; cases sc; exact hx1_c),
        (by cases sc; exact hx2_c), (by cases sc; exact hlr_c), (by cases s0; cases sc; exact hx19_c),
        (by cases s0; cases sc; exact hx20_c), (by cases sc; exact hx21_c)⟩
    · exact hsc_real
  have hcl_sc : LibsignalCodeLoaded lsmpl sc.mem := hcl.of_keepsFrozen hsteps0a.keepsFrozen
  have hL114_sc : (lsProg_114 H).CodeLoaded sc.mem := by
    rw [heq114 H]; exact hcl_sc 114 (by decide) (by decide) H (fun _ => none) Syscall.standard
  rcases hsc with ⟨hpc_c, ⟨hstat_c, hsp_c, hx29_c, hx27_c, hsaved_c, hframe_c⟩,
    hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c, hx21_c⟩
  have hal_hsp : (hsp s0 &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hkey_c : sc.mem.readBytes (sc.readReg64 .x1) (sc.readReg64 .x2).toNat = key := by
    rw [hx1_c, hx2_c, show (32#64 : BitVec 64).toNat = 32 from rfl,
      hframe_c.readBytes_eq (by simp [hpre.disj_key_stack.symm]) (by decide), hpre.key_eq]
  have hiv_c : sc.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV := by
    rw [hframe_c.readBytes_eq (by simp [hpre.disj_iv_stack.symm]) (by decide), hpre.iv_eq]
  have hread_iv_c : sc.mem.Readable lsSha256IVAddr 32 := (hframe_c.readable_iff _ _).mpr hpre.read_iv
  have hrw_stack_c : RW sc.mem (s0.sp - 1024#64) 1024 := (hframe_c.rw_iff _ _).mpr hpre.rw_stack
  have hdisj_iv_nfs : DisjointRegions lsSha256IVAddr 32 (sc.sp - 544#64) 544 := by
    rw [hsp_c, hsp_sub_544_eq]; exact hpre.disj_iv_stack.sub_right _ ⟨by decide, by clear * -; bv_omega⟩
  have hrw_out_nfs : RW sc.mem (sc.readReg64 .x0) 0x98 := by
    rw [hx0_c]; exact hrw_stack_c.sub (by clear * -; unfold hsp; bv_omega)
  have hrw_stack_nfs : RW sc.mem (sc.sp - 544#64) 544 := by
    rw [hsp_c, hsp_sub_544_eq]; exact hrw_stack_c.sub (by clear * -; bv_omega)
  have hdisj_out_nfs : DisjointRegions (sc.readReg64 .x0) 0x98 (sc.sp - 544#64) 544 := by
    rw [hx0_c, hsp_c]; clear * -; unfold hsp DisjointRegions; bv_omega
  have hread_key_nfs : sc.mem.Readable (sc.readReg64 .x1) (sc.readReg64 .x2).toNat := by
    rw [hx1_c, hx2_c, show (32#64 : BitVec 64).toNat = 32 from rfl]
    exact (hframe_c.readable_iff _ _).mpr hread_key
  have hdisj_key_nfs : DisjointRegions (sc.readReg64 .x1) (sc.readReg64 .x2).toNat (sc.sp - 544#64) 544 := by
    rw [hx1_c, hx2_c, hsp_c, hsp_sub_544_eq, show (32#64 : BitVec 64).toNat = 32 from rfl]
    exact hpre.disj_key_stack.sub_right _ ⟨by decide, by clear * -; bv_omega⟩
  obtain ⟨s1, hsteps114, hvm0b, htr0b, hvregs0b, hpc1, hstat1, hcs1, htag1, hhmac1, hframe1⟩ :=
    new_from_slice_placed_runsTo_vm_sat h_memcpy h_compress hpc_c hstat_c (by rw [hx2_c]; decide)
      hiv_c hread_iv_c hdisj_iv_nfs hrw_out_nfs hrw_stack_nfs hdisj_out_nfs hread_key_nfs
      (Or.inr hdisj_key_nfs) (by rw [hsp_c]; exact hal_hsp) hL114_sc
  have hext_114_73 : ∀ pc, (lsProg_114 H).externAt? pc = (lsProg_73 H).externAt? pc := fun pc => by
    have he114 : (libsignalSessionLib.blockLib 114).text.externs = libsignalSessionExterns :=
      IsLsBlockProg.externs_eq (prog := lsProg_114 H)
    have he73 : (libsignalSessionLib.blockLib 73).text.externs = libsignalSessionExterns :=
      IsLsBlockProg.externs_eq (prog := lsProg_73 H)
    rw [heq114 H, heq73 H, ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H
      Syscall.standard (he114.trans he73.symm)]
  have hsteps0b : Steps (lsProg_73 H) sc s1 :=
    Steps.of_sameHooks hext_114_73 (by rw [heq114 H, heq73 H]; rfl) hsteps114
  have hs1_real_st : StateH1Placed F key s0 s1 := by
    rw [hlr_c] at hpc1; rw [hx0_c] at htag1 hhmac1 hframe1; rw [hsp_c] at hframe1; rw [hkey_c] at hhmac1
    have hhmac_addr : hsp s0 + 144#64 + 8#64 = hsp s0 + 152#64 := by clear * -; bv_omega
    rw [hhmac_addr] at hhmac1
    exact ⟨hpc1, ⟨hstat1, hcs1.1.trans hsp_c, (hcs1.2 .x29 (by simp)).trans hx29_c,
      (hcs1.2 .x27 (by simp)).trans hx27_c,
      HmacSaved.of_frame hsaved_c hframe1 (by
        intro r hr; clear * - hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> (unfold hsp DisjointRegions; bv_omega)),
      Frame.trans_nfs hframe_c hframe1⟩,
      (hcs1.2 .x19 (by simp)).trans hx19_c, (hcs1.2 .x20 (by simp)).trans hx20_c,
      (hcs1.2 .x21 (by simp)).trans hx21_c, htag1, hhmac1⟩
  have hs1 : StateH1Placed F key (ProofLib.stripS kp73 s0) (ProofLib.stripS kp73 s1) := by
    rcases hs1_real_st with ⟨hpc1', ⟨hstat1', hsp1, hx29_1, hx27_1, hsaved1, hframe01⟩,
      hx19_1, hx20_1, hx21_1, htag1', hhmac1'⟩
    have hm0 : (ProofLib.stripS kp73 s0).mem = ProofLib.stripExecOutside kp73 s0.mem := by cases s0; rfl
    have hm1 : (ProofLib.stripS kp73 s1).mem = ProofLib.stripExecOutside kp73 s1.mem := by cases s1; rfl
    have hs0 : (ProofLib.stripS kp73 s0).sp = s0.sp := by cases s0; rfl
    have hsp0 : hsp (ProofLib.stripS kp73 s0) = hsp s0 := by cases s0; rfl
    have hframe01_73 : Frame (ProofLib.stripS kp73 s0).mem (ProofLib.stripS kp73 s1).mem
        [((ProofLib.stripS kp73 s0).sp - 1024#64, 1024)] := by
      rw [hm0, hm1, hs0]
      exact ⟨fun a hout => by simpa only [ProofLib.strip_read8] using hframe01.1 a hout,
        funext fun a => by simp [ProofLib.strip_perm, (hvm0a.trans hvm0b).perm_eq a],
        fun a hout => by simpa only [ProofLib.strip_isLazyFree] using hframe01.2.2.1 a hout,
        fun a hlf => by simpa only [ProofLib.strip_isLazyFree] using
          hframe01.2.2.2.1 a (by simpa only [ProofLib.strip_isLazyFree] using hlf),
        fun a han => by simpa only [ProofLib.strip_isAnon] using
          hframe01.2.2.2.2 a (by simpa only [ProofLib.strip_isAnon] using han)⟩
    exact ⟨(by cases s1; exact hpc1'), ⟨(by cases s1; exact hstat1'), (by cases s0; cases s1; exact hsp1),
       (by cases s0; cases s1; exact hx29_1), (by cases s0; cases s1; exact hx27_1),
       (stripS_hmacSaved kp73 s0 s1).mpr hsaved1, hframe01_73⟩,
      (by cases s0; cases s1; exact hx19_1), (by cases s0; cases s1; exact hx20_1),
      (by cases s1; exact hx21_1), by rw [hsp0, stripS_read64]; exact htag1',
      by rw [hm1, hsp0]; exact stripExecOutside_hmacSt.mpr hhmac1'⟩
  -- Piece 3a: `seg1a_placed_runsTo` on Block `73` (`s1 → s1m`, 0 extern calls)
  have hpre73 := hmacPlacedPre_stripS kp73 hpre
  have hL73_s1 : (libsignalSessionLib.blockProgram lsmpl 73 H).CodeLoaded s1.mem := by
    rw [← heq73 H]; exact (hsteps0a.trans hsteps0b).codeLoaded hL73
  obtain ⟨s1m, hsteps1a_bp, hvm1a, htr1a, hvregs1a, h1m_or⟩ :=
    runsTo_block_lift_vm_compress_only h_compress blkLib_eq_73 rfl rfl hL73_s1
      (runsTo_73_to_bp (seg1a_placed_runsTo (H := H) hpre hs1_real_st))
      (runsTo_73_to_bp (seg1a_placed_runsTo (H := hmacCompressOnlyExcHooks F H) hpre73 hs1))
      (fun _ hs => hs.common.status) (fun _ hs => hs.common.status)
  have hsteps1a : Steps (lsProg_73 H) s1 s1m := steps_bp_to_73 hsteps1a_bp
  have hvm0_1m : VmPreserved s0 s1m := (hvm0a.trans hvm0b).trans hvm1a
  have h1m : StateH1mPlaced F key s0 s1m := by
    rcases h1m_or with h1m_strip | h1m_real
    · rcases h1m_strip with ⟨hpc_m, ⟨hstat_m, hsp_m, hx29_m, hx27_m, hsaved_m, hframe_m⟩,
        hx0_m, hx1_m, hx2_m, hlr_m, hx19_m, hx21_m, hx22_m, hx23_m, hx25_m, hist_m, hibl_m, host_m, hobl_m⟩
      have hm0 : (ProofLib.stripS kp73 s0).mem = ProofLib.stripExecOutside kp73 s0.mem := by cases s0; rfl
      have hmm : (ProofLib.stripS kp73 s1m).mem = ProofLib.stripExecOutside kp73 s1m.mem := by cases s1m; rfl
      have hsp0 : hsp (ProofLib.stripS kp73 s0) = hsp s0 := by cases s0; rfl
      have hs0 : (ProofLib.stripS kp73 s0).sp = s0.sp := by cases s0; rfl
      rw [hm0, hmm, hs0] at hframe_m; rw [hsp0, hmm, stripExecOutside_readBytes] at hist_m host_m
      rw [hsp0, stripS_read64] at hibl_m hobl_m
      exact ⟨(by cases s1m; exact hpc_m), ⟨(by cases s1m; exact hstat_m), (by cases s0; cases s1m; exact hsp_m),
         (by cases s0; cases s1m; exact hx29_m), (by cases s0; cases s1m; exact hx27_m),
         (stripS_hmacSaved kp73 s0 s1m).mp hsaved_m, unstrip_frame hframe_m hvm0_1m.perm_eq⟩,
        (by cases s0; cases s1m; exact hx0_m), (by cases s0; cases s1m; exact hx1_m),
        (by cases s1m; exact hx2_m), (by cases s1m; exact hlr_m), (by cases s0; cases s1m; exact hx19_m),
        (by cases s1m; exact hx21_m), (by cases s0; cases s1m; exact hx22_m), (by cases s1m; exact hx23_m),
        (by cases s1m; exact hx25_m), hist_m, hibl_m, host_m, hobl_m⟩
    · exact h1m_real
  -- Piece 3b: `seg1b1_placed_runsTo_vm_sat` on Block `73` (`s1m → s1p`)
  have hL73_s1m : (lsProg_73 H).CodeLoaded s1m.mem :=
    ((hsteps0a.trans hsteps0b).trans hsteps1a).codeLoaded hL73
  obtain ⟨s1p, hsteps1b1_only, htr1b1_only, hvregs1b1_only, ⟨hvm1b1_only, h1p⟩, _⟩ :=
    seg1b1_placed_runsTo_vm_sat h_memcpy hpre h1m hL73_s1m
  have hsteps1b1 : Steps (lsProg_73 H) s1 s1p := hsteps1a.trans hsteps1b1_only
  have htr1b1 : s1p.trace = s1.trace := htr1b1_only.trans htr1a
  have hvregs1b1 : calleeSavedVRegs s1p = calleeSavedVRegs s1 := hvregs1b1_only.trans hvregs1a
  have hvm0_1p : VmPreserved s0 s1p := hvm0_1m.trans hvm1b1_only
  rcases h1p with ⟨hpc_p, ⟨hstat_p, hsp_p, hx29_p, hx27_p, hsaved_p, hframe_p⟩,
    hx0_p, hx1_p, hx2_p, hlr_p, hx19_p, hx20_p, hx21_p, hx22_p, hx23_p, hx24_p, hx25_p, hx26_p,
    hm144_0, hm144_1, hist_p, hibl_p, host_p, hobl_p⟩
  have hrw_hsp : s1p.mem.RW (hsp s0) 480 :=
    ((hframe_p.rw_iff _ _).mpr hpre.rw_stack).sub (by clear * -; unfold hsp; bv_omega)
  have hsp_al_1p : (s1p.sp &&& 15#64) = 0#64 := by rw [hsp_p]; exact hal_hsp
  obtain ⟨s2, hsteps1b2, hvm1b2, htr1b2, hvregs1b2, hpc2, hstat2, hcc2, _, _, _, hs2_step_fr, hag2⟩ :=
    placed_memset_budget_steps_sat (prog := lsProg_73 H) (i := 73) h_memset
      (dst := hsp s0 + 146#64) (lr := (blkPl_73).base + 388#64) (val := 0#8) (len := 62)
      hstat_p hpc_p hx0_p hx1_p (by rw [hx2_p]; rfl) hlr_p hsp_al_1p
      (hrw_hsp.sub (by clear * -; bv_omega))
  have hP_hsp : ∀ {off : BitVec 64} {n : Nat},
      (off - hsp s0).toNat + n ≤ 480 →
      ∀ a, InRegion off n a → (s1p.mem.perm a).r = true ∧ s1p.mem.isLazyFree a = false := by
    intro off n hsub a ha
    have hnl := hrw_hsp a (by unfold InRegion at ha ⊢; bv_omega)
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
    exact ⟨by rw [hp]; rfl, hlf⟩
  have hs2_frame : S2Frame s0.mem s2.mem [(s0.sp - 1024#64, 1024)] := by
    refine (s2Frame_of_hmacFrame hframe_p).trans (hs2_step_fr.mono fun a ha => ?_)
    intro r hr_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem; subst hr_mem
    have ha_stk := ha (s0.sp - 1024#64, 1024) (by simp)
    clear * - ha_stk; unfold hsp OutsideRegion at ha_stk ⊢; bv_omega
  have hsaved_wb : HmacSaved s0 (hsp s0)
      (s1p.mem.writeBytes (hsp s0 + 146#64) (List.replicate 62 0#8)) :=
    hsaved_p.of_agreesOutside (AgreesOutside.writeBytes_self _ _ _)
      (by clear * -; simp only [List.length_replicate, DisjointRegions]; bv_omega)
  have h2 : StateH2PlacedSat F key byte s0 s2 :=
    { pc_eq := hpc2
      common :=
        { status := hstat2, sp_eq := (CallingConventionPreserved.sp_eq hcc2).trans hsp_p
          x29_eq := (CallingConventionPreserved.x29 hcc2).trans hx29_p
          x27_eq := (CallingConventionPreserved.x27 hcc2).trans hx27_p
          saved := hmacSaved_of_agreesOn hag2 hsaved_wb (hP_hsp (by clear * -; bv_omega))
          frame := hs2_frame }
      x19_eq := (CallingConventionPreserved.x19 hcc2).trans hx19_p
      x20_eq := (CallingConventionPreserved.x20 hcc2).trans hx20_p
      x21_eq := (CallingConventionPreserved.x21 hcc2).trans hx21_p
      x22_eq := (CallingConventionPreserved.x22 hcc2).trans hx22_p
      x23_eq := (CallingConventionPreserved.x23 hcc2).trans hx23_p
      x24_eq := (CallingConventionPreserved.x24 hcc2).trans hx24_p
      x25_eq := (CallingConventionPreserved.x25 hcc2).trans hx25_p
      x26_eq := (CallingConventionPreserved.x26 hcc2).trans hx26_p
      m144 := by
        rw [AgreesOn.read64_eq hag2 (hsp s0 + 144#64) (hP_hsp (by clear * -; bv_omega)),
            toLEBytes_8_read64_writeBytes_146_62 s1p.mem (hsp s0), hm144_0, hm144_1]; rfl
      m152 := (AgreesOn.read64_eq hag2 (hsp s0 + 152#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s1p.mem (hsp s0) 146#64 152#64 62)
      m160 := (AgreesOn.read64_eq hag2 (hsp s0 + 160#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s1p.mem (hsp s0) 146#64 160#64 62)
      m168 := (AgreesOn.read64_eq hag2 (hsp s0 + 168#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s1p.mem (hsp s0) 146#64 168#64 62)
      m176 := (AgreesOn.read64_eq hag2 (hsp s0 + 176#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s1p.mem (hsp s0) 146#64 176#64 62)
      m184 := (AgreesOn.read64_eq hag2 (hsp s0 + 184#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s1p.mem (hsp s0) 146#64 184#64 62)
      m192 := (AgreesOn.read64_eq hag2 (hsp s0 + 192#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s1p.mem (hsp s0) 146#64 192#64 62)
      ist_eq := (AgreesOn.readBytes_eq hag2 (hsp s0 + 208#64) 32 (by decide)
          (hP_hsp (by clear * -; bv_omega))).trans
        ((readBytes_writeBytes_replicate_off_disjoint s1p.mem (hsp s0) 146#64 208#64 32 62 0#8).trans hist_p)
      ibl_eq := (AgreesOn.read64_eq hag2 (hsp s0 + 240#64) (hP_hsp (by clear * -; bv_omega))).trans
        ((read64_writeBytes_replicate_off_disjoint s1p.mem (hsp s0) 146#64 240#64 62 0#8).trans hibl_p)
      ost_eq := (AgreesOn.readBytes_eq hag2 (hsp s0 + 248#64) 32 (by decide)
          (hP_hsp (by clear * -; bv_omega))).trans
        ((readBytes_writeBytes_replicate_off_disjoint s1p.mem (hsp s0) 146#64 248#64 32 62 0#8).trans host_p)
      obl_eq := (AgreesOn.read64_eq hag2 (hsp s0 + 280#64) (hP_hsp (by clear * -; bv_omega))).trans
        ((read64_writeBytes_replicate_off_disjoint s1p.mem (hsp s0) 146#64 280#64 62 0#8).trans hobl_p) }
  let s0' : State := s0.setMem s2.mem
  have hpre' : HmacPlacedPre F key [byte] s0' :=
    { pc_eq := hpre.pc_eq, status := hpre.status, sp_aligned := hpre.sp_aligned
      x2_eq := hpre.x2_eq, x4_eq := hpre.x4_eq, key_len := hpre.key_len, inp_len := hpre.inp_len
      key_eq := (s2Frame_readBytes_eq_of_readable hs2_frame hread_key (by decide)
        (by simp [hpre.disj_key_stack.symm])).trans hpre.key_eq
      inp_eq := (s2Frame_readBytes_eq_of_readable hs2_frame hpre.read_inp (by decide)
        (by simp [hpre.disj_inp_stack.symm])).trans hpre.inp_eq
      iv_eq := (s2Frame_readBytes_eq_of_readable hs2_frame hpre.read_iv (by decide)
        (by simp [hpre.disj_iv_stack.symm])).trans hpre.iv_eq
      read_iv := s2Frame_readable_of_readable hs2_frame hpre.read_iv
      read_inp := s2Frame_readable_of_readable hs2_frame hpre.read_inp
      rw_out := hs2_frame.rw_of_rw _ _ hpre.rw_out, rw_stack := hs2_frame.rw_of_rw _ _ hpre.rw_stack
      disj_iv_stack := hpre.disj_iv_stack, disj_out_stack := hpre.disj_out_stack
      disj_key_stack := hpre.disj_key_stack, disj_inp_stack := hpre.disj_inp_stack }
  have hpre'73 := hmacPlacedPre_stripS kp73 hpre'
  have h2'_real : StateH2Placed F key byte s0' s2 :=
    { pc_eq := h2.pc_eq
      common := { status := h2.common.status, sp_eq := h2.common.sp_eq, x29_eq := h2.common.x29_eq
                  x27_eq := h2.common.x27_eq, saved := h2.common.saved, frame := Frame.refl s2.mem _ }
      x19_eq := h2.x19_eq, x20_eq := h2.x20_eq, x21_eq := h2.x21_eq, x22_eq := h2.x22_eq,
      x23_eq := h2.x23_eq, x24_eq := h2.x24_eq, x25_eq := h2.x25_eq, x26_eq := h2.x26_eq,
      m144 := h2.m144, m152 := h2.m152, m160 := h2.m160, m168 := h2.m168,
      m176 := h2.m176, m184 := h2.m184, m192 := h2.m192,
      ist_eq := h2.ist_eq, ibl_eq := h2.ibl_eq, ost_eq := h2.ost_eq, obl_eq := h2.obl_eq }
  have h2'_strip : StateH2Placed F key byte (ProofLib.stripS kp73 s0') (ProofLib.stripS kp73 s2) := by
    have hsp0' : hsp (ProofLib.stripS kp73 s0') = hsp s0 := by cases s0; rfl
    have hm2_73 : (ProofLib.stripS kp73 s2).mem = ProofLib.stripExecOutside kp73 s2.mem := by cases s2; rfl
    have hm0'_eq : (ProofLib.stripS kp73 s0').mem = (ProofLib.stripS kp73 s2).mem := by cases s0; cases s2; rfl
    exact
      { pc_eq := by cases s2; exact h2.pc_eq
        common :=
          { status := by cases s2; exact h2.common.status
            sp_eq := by cases s0; cases s2; exact h2.common.sp_eq
            x29_eq := by cases s0; cases s2; exact h2.common.x29_eq
            x27_eq := by cases s0; cases s2; exact h2.common.x27_eq
            saved := (stripS_hmacSaved kp73 s0' s2).mpr h2.common.saved
            frame := hm0'_eq ▸ Frame.refl _ _ }
        x19_eq := by cases s0; cases s2; exact h2.x19_eq
        x20_eq := by cases s0; cases s2; exact h2.x20_eq
        x21_eq := by cases s0; cases s2; exact h2.x21_eq
        x22_eq := by cases s0; cases s2; exact h2.x22_eq
        x23_eq := by cases s2; exact h2.x23_eq
        x24_eq := by cases s2; exact h2.x24_eq
        x25_eq := by cases s2; exact h2.x25_eq
        x26_eq := by cases s2; exact h2.x26_eq
        m144 := by rw [hsp0', stripS_read64]; exact h2.m144
        m152 := by rw [hsp0', stripS_read64]; exact h2.m152
        m160 := by rw [hsp0', stripS_read64]; exact h2.m160
        m168 := by rw [hsp0', stripS_read64]; exact h2.m168
        m176 := by rw [hsp0', stripS_read64]; exact h2.m176
        m184 := by rw [hsp0', stripS_read64]; exact h2.m184
        m192 := by rw [hsp0', stripS_read64]; exact h2.m192
        ist_eq := by rw [hsp0', hm2_73, stripExecOutside_readBytes]; exact h2.ist_eq
        ibl_eq := by rw [hsp0', stripS_read64]; exact h2.ibl_eq
        ost_eq := by rw [hsp0', hm2_73, stripExecOutside_readBytes]; exact h2.ost_eq
        obl_eq := by rw [hsp0', stripS_read64]; exact h2.obl_eq }
  have hsteps0_2 : Steps (lsProg_73 H) s0 s2 :=
    ((hsteps0a.trans hsteps0b).trans hsteps1b1).trans hsteps1b2
  have hL73_s2 : (libsignalSessionLib.blockProgram lsmpl 73 H).CodeLoaded s2.mem := by
    rw [← heq73 H]; exact hsteps0_2.codeLoaded hL73
  have hruns_tail_P : RunsTo (libsignalSessionLib.blockProgram lsmpl 73 H) s2
      (StateH5 F key byte s0') :=
    runsTo_73_to_bp (
      (seg2_placed_runsTo h_compress hpre' h2'_real).trans fun _ h3 =>
      (seg3_placed_runsTo h_compress hpre' h3).trans fun _ h4 =>
      seg4_placed_runsTo hpre' h4)
  have hruns_tail_Q : RunsTo Q73 (ProofLib.stripS kp73 s2)
      (StateH5 F key byte (ProofLib.stripS kp73 s0')) :=
    runsTo_73_to_bp (
      (seg2_placed_runsTo hc256Q hpre'73 h2'_strip).trans fun _ h3 =>
      (seg3_placed_runsTo hc256Q hpre'73 h3).trans fun _ h4 =>
      seg4_placed_runsTo hpre'73 h4)
  obtain ⟨sf, hsteps_tail_bp, hvm_tail, htr_tail, hvregs_tail, h5_or⟩ :=
    runsTo_block_lift_vm_compress_only h_compress blkLib_eq_73 rfl rfl hL73_s2
      hruns_tail_P hruns_tail_Q (fun _ hs => hs.status) (fun _ hs => hs.status)
  have hsteps_tail : Steps (lsProg_73 H) s2 sf := steps_bp_to_73 hsteps_tail_bp
  have hvm_all : VmPreserved s0 sf := (hvm0_1p.trans hvm1b2).trans hvm_tail
  have h5_s0' : StateH5 F key byte s0' sf := by
    rcases h5_or with h5_strip | h5_real
    · rcases h5_strip with ⟨hpc_sf, hstat_sf, hcs_sf, hout_sf, hframe_sf⟩
      have hm0'_73 : (ProofLib.stripS kp73 s0').mem = ProofLib.stripExecOutside kp73 s0'.mem := by cases s0; rfl
      have hmf_73 : (ProofLib.stripS kp73 sf).mem = ProofLib.stripExecOutside kp73 sf.mem := by cases sf; rfl
      have hr0_73 : (ProofLib.stripS kp73 s0').readReg64 .x0 = s0'.readReg64 .x0 := by cases s0; rfl
      have hs0_73 : (ProofLib.stripS kp73 s0').sp = s0'.sp := by cases s0; rfl
      rw [hm0'_73, hmf_73, hr0_73, hs0_73] at hframe_sf
      rw [hmf_73, hr0_73, stripExecOutside_readBytes] at hout_sf
      have hcs_u : CalleeSaved s0' sf := by
        refine ⟨by cases s0; cases sf; exact hcs_sf.1, fun r hr => ?_⟩
        have := hcs_sf.2 r hr; cases s0; cases sf; exact this
      have hperm_0'f : ∀ a, sf.mem.perm a = s0'.mem.perm a := fun a => by
        have h := hvm_tail.perm_eq a; cases s0; exact h
      exact ⟨by cases s0; cases sf; exact hpc_sf, by cases sf; exact hstat_sf,
        hcs_u, hout_sf, unstrip_frame hframe_sf hperm_0'f⟩
    · exact h5_real
  rcases h5_s0' with ⟨hpc_sf, hstat_sf, hcs_sf, hout_sf, hfr_sf⟩
  have hs2_widen : S2Frame s0.mem s2.mem [(s0.readReg64 .x0, 32), (s0.sp - 1024#64, 1024)] :=
    hs2_frame.mono fun a ha r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact ha _ (by simp)
  have hfr_s2_sf : Frame s2.mem sf.mem [(s0.readReg64 .x0, 32), (s0.sp - 1024#64, 1024)] := by
    cases s0; exact hfr_sf
  have hcs_0_sf : CalleeSaved s0 sf := by
    refine ⟨hcs_sf.1, fun r hr => ?_⟩
    have := hcs_sf.2 r hr; cases s0; exact this
  exact ⟨sf, hsteps0_2.trans hsteps_tail, hvm_all,
    htr_tail.trans (htr1b2.trans (htr1b1.trans (htr0b.trans htr0a))),
    hvregs_tail.trans (hvregs1b2.trans (hvregs1b1.trans (hvregs0b.trans hvregs0a))),
    { pc_eq := by cases s0; exact hpc_sf
      status := hstat_sf
      calleeSaved := hcs_0_sf
      out_eq := by cases s0; exact hout_sf
      frame := hs2_widen.trans (s2Frame_of_hmacFrame hfr_s2_sf) }⟩

/-- `VmPreserved`-strengthened `hmac_sha256` contract on Block 73 under `HookSatExactMemcpy H lsMemcpySym` and `HookSat` for `memset` (sibling of `AssemblyBudget.hmac_sha256_placed_ok`). -/
theorem hmac_sha256_placed_ok_sat [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl (withVmPreserved (hmacPlacedSpec F))) := by
  refine subroutine_ok_intro fun ⟨out, ka, key, ia, inp⟩ R s0 hpc hrun hpre hsp => ?_
  have ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  rw [withVmPreserved, hmacPlacedSpec] at hpre
  dsimp only [] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat, hx3, hx4_nat, hkey_len, hinp_len, hro⟩, hsep⟩
  rcases inp with _ | ⟨byte, _ | _⟩ <;> try { simp at hinp_len }
  have hx2 : s0.readReg64 .x2 = 32#64 := by
    apply BitVec.eq_of_toNat_eq; simp [hx2_nat, hkey_len]
  have hx4 : s0.readReg64 .x4 = 1#64 := by
    apply BitVec.eq_of_toNat_eq; simp at hx4_nat; simp [hx4_nat]
  have hsp_split : stackAt s0.sp 2048 =
      memRegion (s0.sp - 2048#64) 1024 ∗ memRegion (s0.sp - 1024#64) 1024 :=
    stackAt_split_bottom s0.sp 1024 1024 (by decide)
  rw [hsp_split] at hsep
  have hb_out := IsBlock.memRegion out 32
  have hb_key := IsBlock.pointsToBytes_len (a := ka) hkey_len
  have hb_inp := IsBlock.pointsToBytes_len (a := ia) (rfl : [byte].length = 1)
  have hb_stk := IsBlock.memRegion (s0.sp - 1024#64) 1024
  have hsep_key : s0.mem ⊨ (ka ↦ₛ key) ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      (memRegion out 32 ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_inp : s0.mem ⊨ (ia ↦ₛ [byte]) ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      (memRegion out 32 ∗ (ka ↦ₛ key) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_out : s0.mem ⊨ memRegion out 32 ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      ((ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 1024#64) 1024 ∗
      (memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hkey_eq : s0.mem.readBytes ka 32 = key := by
    have h := (hb_key.read hsep_key).2
    rwa [hkey_len] at h
  have hinp_eq : s0.mem.readBytes ia 1 = [byte] :=
    (hb_inp.read hsep_inp).2
  have hrw_out : RW s0.mem out 32 :=
    fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : RW s0.mem (s0.sp - 1024#64) 1024 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hread_key : s0.mem.Readable ka 32 :=
    Memory.RW.readable (fun a ha => hb_key.permNoLazy_rw hsep_key ha)
  have hread_inp : s0.mem.Readable ia 1 :=
    Memory.RW.readable (fun a ha => hb_inp.permNoLazy_rw hsep_inp ha)
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_sha256IV hro
  have hread_iv : s0.mem.Readable lsSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hpre_hmac : HmacPlacedPre F key [byte] s0 := {
    pc_eq := hpc, status := hrun, sp_aligned := by simpa [State.spAligned] using hsp
    x2_eq := hx2, x4_eq := hx4, key_len := hkey_len, inp_len := rfl
    key_eq := by rw [hx1]; exact hkey_eq, inp_eq := by rw [hx3]; exact hinp_eq
    iv_eq := hiv_eq, read_iv := hread_iv, read_inp := by rw [hx3]; exact hread_inp
    rw_out := by rw [hx0]; exact hrw_out, rw_stack := hrw_stk
    disj_iv_stack := disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
    disj_out_stack := by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out
    disj_key_stack := by rw [hx1]; exact hb_key.disjoint hb_stk (by decide) (by decide) hsep_key
    disj_inp_stack := by rw [hx3]; exact hb_inp.disjoint hb_stk (by simp) (by decide) hsep_inp }
  have hread_x1 : s0.mem.Readable (s0.readReg64 .x1) 32 := by rw [hx1]; exact hread_key
  intro hL73
  obtain ⟨sf, hsteps, hvm, htr, hvregs, hpc_sf, hstat_sf, hcallee, hout_sf, hframe_sf⟩ :=
    hmac_placed_runsTo_vm_sat h_mc h_ms h_c256 hcl hpre_hmac hread_x1 hL73
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hstat_sf, ?_,
    CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩⟩
  dsimp only [withLsCodeLoaded, withVmPreserved, hmacPlacedSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨htr, libsignalRoLoaded_of_keepsFrozen hro hsteps.keepsFrozen⟩, ?_⟩
  rw [hsp_split]
  have hb_out' := IsBlock.pointsToBytes_len (a := out) (length_hmacWith F key [byte])
  rw [hx0] at hout_sf hframe_sf
  have hpost_sep : sf.mem ⊨ (out ↦ₛ hmacWith F key [byte]) ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      ((ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) :=
    S2Frame.update_two_blocks hb_out hb_out' hb_stk hb_stk hsep_out hframe_sf
      ⟨by rw [length_hmacWith]; decide, by rwa [length_hmacWith]⟩ trivial
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost_sep

/-- `.rodata`-backed `VmPreserved` `hmac_sha256` contract on Block 73 under `HookSatExactMemcpy H lsMemcpySym` and `HookSat` for `memset` (sibling of `AssemblyBudget.hmac_sha256_placed_ro_ok`). -/
theorem hmac_sha256_placed_ro_ok_sat [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        { hmacSpec F with pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) := by
  refine subroutine_ok_mono (hmac_sha256_placed_ok_sat F h_mc h_ms h_c256)
    (fun ⟨out, ka, key, ia, inp⟩ R s0 hp => ?_)
    (fun ⟨out, ka, key, ia, inp⟩ R s0 sf hq => ?_)
  · have ⟨hcl, hp'⟩ := extract_withLsCodeLoaded hp
    dsimp only [withLsCodeLoaded, withVmPreserved, hmacPlacedSpec, hmacSpec,
      CryptoVerification.LibsignalSession.hmacSpec] at hp' ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp' ⊢
    rcases hp' with ⟨hro, hp''⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp''
    rcases hp'' with ⟨hpure, hsep⟩
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpure.1, hpure.2.1, hpure.2.2.1, hpure.2.2.2.1, hpure.2.2.2.2.1,
      hpure.2.2.2.2.2.1, hpure.2.2.2.2.2.2, hro⟩, hsep⟩
  · dsimp only [withLsCodeLoaded, withVmPreserved, hmacPlacedSpec, hmacSpec,
      CryptoVerification.LibsignalSession.hmacSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    have hq' := hq.2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq' ⊢
    exact ⟨hq'.1.1, hq'.2⟩

/-! ## Callee Lifts and Top-Level `consume_message_key` Assembly -/

theorem find_receiver_chain_index_placed_ok_at_cmk_sat [LibsignalPlacement] {M : AllocCostModel}
    {H : String → Option (State → State)} (A : RustCliAllocBudget M)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    FindIndexPlacedOk H A :=
  AssemblyBudget.find_receiver_chain_index_placed_ok_at_cmk A h_bb

theorem grow_one_placed_ok_at_cmk_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    GrowOnePlacedOk H A lim :=
  AssemblyBudget.grow_one_placed_ok_at_cmk hA h_realloc

theorem grow_one_placed_ok_of_noop_at_cmk_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hA : CmkAllocHooks A lim H) :
    GrowOnePlacedOk H A lim :=
  AssemblyBudget.grow_one_placed_ok_of_noop_at_cmk h_shim h_realloc hA

theorem hmac_sha256_placed_ro_ok_at_cmk_sat [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    HmacPlacedRoOk H F :=
  ls_subroutine_ok_of_block (i := 24) (j := 73) (hmac_sha256_placed_ro_ok_sat F h_mc h_ms h_c256)

theorem consume_message_key_placed_run_of_hooks_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hhmac : HmacPlacedOk H F) :
    CmkPlacedRunStmtSat F A lim H := by
  intro hA hmm
  exact consume_message_key_placed_run_of_sat F A lim H
    (find_receiver_chain_index_placed_ok_at_cmk_sat A h_bb)
    hhmac
    (grow_one_placed_ok_at_cmk_sat hA h_realloc) hA hmm

theorem consume_message_key_placed_run_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hhmac : HmacPlacedOk H F) :
    CmkPlacedRunStmtSat F A lim H := by
  intro hA hmm
  exact consume_message_key_placed_run_of_sat F A lim H
    (find_receiver_chain_index_placed_ok_at_cmk_sat A h_bb)
    hhmac
    (grow_one_placed_ok_of_noop_at_cmk_sat h_shim h_realloc hA) hA hmm

/-- `.rodata`-backed budget-threaded placed refinement for `consume_message_key` (`HookSat` `memset`, `sessionMemmoveBoundedBudgetSpec 4096` `memmove`, and shim; sibling of `consume_message_key_placed_ro_run_of_hooks` replacing `some hookMemmove`). -/
theorem consume_message_key_placed_ro_run_of_hooks_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    CmkPlacedRunStmtSat F A lim H := by
  intro hA hmm
  exact consume_message_key_placed_ro_run_of_sat F A lim H
    (find_receiver_chain_index_placed_ok_at_cmk_sat A h_bb)
    (hmac_sha256_placed_ro_ok_at_cmk_sat F h_mc h_ms h_c256)
    (grow_one_placed_ok_at_cmk_sat hA h_realloc) hA hmm

/-- `.rodata`-backed budget-threaded placed refinement for `consume_message_key` (`HookSat` `memset` and `sessionMemmoveBoundedBudgetSpec 4096` `memmove`, `hookNoop` shim; sibling of `consume_message_key_placed_ro_run`). -/
theorem consume_message_key_placed_ro_run_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    CmkPlacedRunStmtSat F A lim H := by
  intro hA hmm
  exact consume_message_key_placed_ro_run_of_sat F A lim H
    (find_receiver_chain_index_placed_ok_at_cmk_sat A h_bb)
    (hmac_sha256_placed_ro_ok_at_cmk_sat F h_mc h_ms h_c256)
    (grow_one_placed_ok_of_noop_at_cmk_sat h_shim h_realloc hA) hA hmm

end LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetSat
