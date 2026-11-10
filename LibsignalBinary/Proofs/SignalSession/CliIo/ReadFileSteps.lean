/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinSteps
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin
public import VerifiedLibraries.Musl.Proofs.SyscallProof
public meta import ProofLib.ProgramReflection

/-!
# Bounded `read_file` Epilogues and Step Lemmas

Proves the return epilogue (`+0x208`), unconditional `close` epilogue (`+0x1f4`), and `Ok` / `Err`
epilogues (`+0x1c8`, `+0x1d4` for `cap = 0` and `0 < cap`) for `signalSessionIoMultiLib` block `3`
(`signal_session_io::read_file`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open VerifiedLibraries.RustStd (
  RustStdAlloc NullAllowed
  PoolPreserved AllocCallPreserved IoFrame StdErrnoCell stdErrnoAddr
  vecHeader ioVecBuf ioResultVecOk
  rustStdDeallocSpec allocFinishGrowSpec
  allocVecGrowLb allocVecGrowLk
)
open VerifiedLibraries.RustStd.Io (
  allocCallPreserved_of_seg allocCallPreserved_trans
)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  sepWP_seg_cliIo_block_pure cliIoBlocks_len
  cliIoOpenSym cliIoCloseSym cliIoReadSym cliIoErrnoLocationSym
  cliIoMemcpySym cliIoFinishGrowSym cliIoRustDeallocSym
  cliIoPl03 cliIoPC03 cliIoBlockNoSvc0_03
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  poolPreserved_of_syscall poolPreserved_of_stdState
  ioFrame_trans ioFrame_of_allocCall
  cliIoCap cliIoCap_zero cliIoCap_succ cliIoCap_strictMono
  cliIoCap_pos cliIoCap_lt_pow63 cliIoCap_lt_pow64 not_nullAllowed_cliIoCap
  allocVecGrowLb_from_zero allocVecGrowLk_from_zero allocVecGrowLb_telescopes allocVecGrowLk_from_pos
  dealloc_cancel_lb dealloc_cancel_lk
  wantBytes bv64_ult_ofNat_true bv64_ult_ofNat_false bv64_beq_ofNat_false
  bv64_shiftLeft1_ofNat bv64_sub_ofNat wantBytes_csel_bv
  cliIoSavedRegs12 cliIoReadFile_stack_refold
  ioVecBuf_entails_dealloc_mem vecHeader_to_err_sret
  ioVecBuf_unpack_pos ioVecBuf_repack_chunk stackBuf4096_repack
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinSteps (
  CliIoMidPreserved
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (muslClose48LocalSpec)

section
arm64_proof_prelude

theorem cliIo3_lt : 3 < signalSessionIoMultiLib.blocks.length := by
  rw [cliIoBlocks_len]; decide

theorem cliIoReadFile_open_pc [CliIoPlacement] :
    cliIoPl03.base + 132#64 + (cliIoPl03.ρ cliIoOpenSym - cliIoPl03.base - 132#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoOpenSym := by
  change cliIoPl03.base + 132#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl03.base - 132#64) = _
  bv_lin

theorem cliIoReadFile_errno1_pc [CliIoPlacement] :
    cliIoPl03.base + 140#64 + (cliIoPl03.ρ cliIoErrnoLocationSym - cliIoPl03.base - 140#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoErrnoLocationSym := by
  change cliIoPl03.base + 140#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl03.base - 140#64) = _
  bv_lin

theorem cliIoReadFile_errno2_pc [CliIoPlacement] :
    cliIoPl03.base + 156#64 + (cliIoPl03.ρ cliIoErrnoLocationSym - cliIoPl03.base - 156#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoErrnoLocationSym := by
  change cliIoPl03.base + 156#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl03.base - 156#64) = _
  bv_lin

theorem cliIoReadFile_read_pc [CliIoPlacement] :
    cliIoPl03.base + 228#64 + (cliIoPl03.ρ cliIoReadSym - cliIoPl03.base - 228#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoReadSym := by
  change cliIoPl03.base + 228#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl03.base - 228#64) = _
  bv_lin

theorem cliIoReadFile_errno3_pc [CliIoPlacement] :
    cliIoPl03.base + 240#64 + (cliIoPl03.ρ cliIoErrnoLocationSym - cliIoPl03.base - 240#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoErrnoLocationSym := by
  change cliIoPl03.base + 240#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl03.base - 240#64) = _
  bv_lin

theorem cliIoReadFile_memcpy_pc [CliIoPlacement] :
    cliIoPl03.base + 360#64 + (cliIoPl03.ρ cliIoMemcpySym - cliIoPl03.base - 360#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoMemcpySym := by
  change cliIoPl03.base + 360#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl03.base - 360#64) = _
  bv_lin

theorem cliIoReadFile_grow_pc [CliIoPlacement] :
    cliIoPl03.base + 432#64 + (cliIoPl03.ρ cliIoFinishGrowSym - cliIoPl03.base - 432#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoFinishGrowSym := by
  change cliIoPl03.base + 432#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl03.base - 432#64) = _
  bv_lin

theorem cliIoReadFile_dealloc_pc [CliIoPlacement] :
    cliIoPl03.base + 496#64 + (cliIoPl03.ρ cliIoRustDeallocSym - cliIoPl03.base - 496#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustDeallocSym := by
  change cliIoPl03.base + 496#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl03.base - 496#64) = _
  bv_lin

theorem cliIoReadFile_close_pc [CliIoPlacement] :
    cliIoPl03.base + 504#64 + (cliIoPl03.ρ cliIoCloseSym - cliIoPl03.base - 504#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoCloseSym := by
  change cliIoPl03.base + 504#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl03.base - 504#64) = _
  bv_lin

theorem readReg32_of_readReg64_eq {s1 s2 : State} {r : Reg}
    (h : s1.readReg64 r = s2.readReg64 r) :
    s1.readReg32 r = s2.readReg32 r := by
  simp only [State.readReg32, h]

/-- Shared stack-restore + `ret` epilogue of `read_file` (`+0x208 = 520#64 .. +0x228 = 552#64`). -/
theorem cliIoReadFile_ret_epilogue [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    {s0 se : State} {st0 st1 st2 st3 : BitVec 64}
    {R_out : SepProp} {stackBytes lb_f lk_f : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 520#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      AllocCallPreserved se sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ R_out ∗ A.pool lb_f lk_f sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        R_out ∗
        A.pool lb_f lk_f se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 520#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 8320#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  wp_conv_pre => dsimp only [cliIoSavedRegs12]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
  have hcpu_f := hcpu_f0.1
  have ⟨hacp_ef, hpool_ef⟩ :=
    allocCallPreserved_of_seg hcpu_e0 hcpu_f0 hnsp_f hsym_f
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool lb_f lk_f se = A.pool lb_f lk_f sf :=
    (A.pool_transport _ _ se sf hpool_ef).symm
  have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
  have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun_e'
  have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
  have hcs_f : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · exact hcpu_f.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))
  refine SepWP.done hpc_f hrun_f (hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_ef ?_)
  have hstk_back := cliIoReadFile_stack_refold s0 hlo hhi st0 st1 st2 st3
  dsimp only [cliIoSavedRegs12] at hstk_back
  rw [hpool_eq]
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono_left (Q := R_out ∗ A.pool lb_f lk_f sf) hstk_back) (by sep_entail))
  sep_entail

/-- Unconditional `close(w19)` + stack-restore + `ret` epilogue (`+0x1f4 = 500#64 .. +0x228 = 552#64`). -/
theorem cliIoReadFile_close_epilogue [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 se : State} {fd : BitVec 64} {desc : FdEntry} {st0 st1 st2 st3 : BitVec 64}
    {R_out : SepProp} {stackBytes lb_f lk_f : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : se.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 500#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hw19 : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = se.fs.setFd fd none →
      sf.trace = se.trace → sf.sigActions = se.sigActions →
      sf.tpidrEl0 = se.tpidrEl0 → sf.brkStart = se.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ R_out ∗ A.pool lb_f lk_f sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        R_out ∗
        A.pool lb_f lk_f se)
      post oomProp := by
  have h48_le : 48 ≤ stackBytes - 8320 := by omega
  have hsb_hi : stackBytes - 8320 ≤ 2 ^ 64 := by omega
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 48 h48_le hsb_hi]
    simp only [sepConj_assoc]
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 500#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  wp_sym_steps
  refine SepWP.done cliIoReadFile_close_pc (by simpa [arm64_norm] using hrun_e')
    fun sm_cl hcpu_cl0 hcl_cl hnsp_cl hsym_cl => ?_
  have hcpu_cl := hcpu_cl0.1
  have ⟨hacp_ecl, hpool_ecl⟩ :=
    allocCallPreserved_of_seg hcpu_e0 hcpu_cl0 hnsp_cl hsym_cl
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ecl : A.pool lb_f lk_f se = A.pool lb_f lk_f sm_cl :=
    (A.pool_transport _ _ se sm_cl hpool_ecl).symm
  have hpc_cl : sm_cl.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym :=
    hcpu_cl.pc_eq.trans cliIoReadFile_close_pc
  have hrun_cl : sm_cl.status = .Running := hcpu_cl.status_eq.trans hrun_e'
  have hsp_cl_eq : sm_cl.sp = s0.sp - 8320#64 :=
    hcpu_cl.sp_eq.trans ((by simp [arm64_norm] : _ = se'.sp).trans (hcpu_e.sp_eq.trans hsp_eq))
  have hsp_cl : sm_cl.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_cl_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_cl : sm_cl.readReg64 .lr = cliIoPl03.base + 508#64 := by
    rw [hcpu_cl.readReg64 .lr]; simp [arm64_norm]
  have hx0_cl : (sm_cl.readReg32 .x0).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_cl.readReg64 .x0)]
    simp only [arm64_norm]
    rw [hcpu_e.readReg64 (.gpr 19#5)]
    exact hw19
  have hfds_cl : sm_cl.fs.fds fd = some desc := by rw [hacp_ecl.1]; exact hfds
  let T_cl : SepProp :=
    memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320)) (stackBytes - 8320 - 48) ∗
      memRegion (s0.sp - 8320#64) 4096 ∗
      memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗
      R_out ∗
      A.pool lb_f lk_f sm_cl
  apply seqCodeLoaded hcl_cl (mid := cliIoPl03.base + 508#64)
  apply (SepWP.call_subroutine_frame hclose (F := T_cl) (x := (fd, desc))
    hpc_cl hrun_cl hsp_cl hlr_cl
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslClose48LocalSpec, T_cl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_cl, hfd_lt, hfds_cl, hkind⟩, ?_⟩
    rw [hpool_eq_ecl] at hm'
    rw [hsp_cl_eq]
    exact Satisfies.mono (by sep_frame) hm'
  · intro sm_cl' hpc_cl' hrun_cl' hsp_cl' hcs_cl'
    refine SepWP.done hpc_cl' hrun_cl' fun hcl_cl' => ?_
    wp_conv_pre => dsimp only [muslClose48LocalSpec, T_cl]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_, hfs_cl', htr_cl', hsys_cl'⟩
    have hpool_eq_cl' : A.pool lb_f lk_f sm_cl = A.pool lb_f lk_f sm_cl' :=
      (A.pool_transport _ _ sm_cl sm_cl' (poolPreserved_of_syscall hsys_cl')).symm
    have hsp_cl'_eq : sm_cl'.sp = s0.sp - 8320#64 := hsp_cl'.trans hsp_cl_eq
    have hvregs_cl' : calleeSavedVRegs sm_cl' = calleeSavedVRegs s0 :=
      hcs_cl'.vregs.trans (hcpu_cl.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs)))
    apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_cl'
      (mid := cliIoPl03.base + 520#64)
    intro sb' hcpu_b0
    have hcpu_b := hcpu_b0.1
    change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
    have hpc_b' : sb'.pc = cliIoPl03.base + 508#64 := hcpu_b.pc_eq.trans hpc_cl'
    have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_cl'
    have hsp_b' : sb'.spAligned = true := by
      rw [hcpu_b.spAligned]; simp only [State.spAligned]; rw [hsp_cl'_eq]
      exact s0.spAligned_sub 8320#64 hsp0
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
      fun sr_ret hcpu_r0 hcl_r hnsp_r hsym_r => ?_
    have hcpu_r := hcpu_r0.1
    have ⟨hacp_br, hpool_br⟩ :=
      allocCallPreserved_of_seg hcpu_b0 hcpu_r0 hnsp_r hsym_r
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_br : A.pool lb_f lk_f sm_cl' = A.pool lb_f lk_f sr_ret :=
      (A.pool_transport _ _ sm_cl' sr_ret hpool_br).symm
    have hsp_r : sr_ret.sp = s0.sp - 8320#64 :=
      hcpu_r.sp_eq.trans ((by simp [arm64_norm] : _ = sb'.sp).trans (hcpu_b.sp_eq.trans hsp_cl'_eq))
    have hvregs_r : calleeSavedVRegs sr_ret = calleeSavedVRegs s0 :=
      hcpu_r.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
        (hcpu_b.calleeSavedVRegs.trans hvregs_cl'))
    refine SepWP.weaken_pre ?_
      (cliIoReadFile_ret_epilogue A hext3 (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
        (R_out := R_out) (lb_f := lb_f) (lk_f := lk_f)
        (by omega) hhi hcl_r (hcpu_r.pc_eq.trans (by simp [arm64_norm]))
        (hcpu_r.status_eq.trans hrun_b') hsp0 hsp_r hvregs_r
        fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_rf _ hent =>
          hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
            (hacp_rf.1.trans (hacp_br.1.trans (hfs_cl'.trans (congrArg (fun f => f.setFd fd none) hacp_ecl.1))))
            (hacp_rf.2.1.trans (hacp_br.2.1.trans (htr_cl'.trans hacp_ecl.2.1)))
            (hacp_rf.2.2.1.trans (hacp_br.2.2.1.trans (hsys_cl'.2.1.trans hacp_ecl.2.2.1)))
            (hacp_rf.2.2.2.1.trans (hacp_br.2.2.2.1.trans (hsys_cl'.1.trans hacp_ecl.2.2.2.1)))
            (hacp_rf.2.2.2.2.1.trans (hacp_br.2.2.2.2.1.trans (hsys_cl'.2.2.brkStart_eq.trans hacp_ecl.2.2.2.2.1)))
            hent)
    rw [hpool_eq_cl', hpool_eq_br, hsp_cl_eq,
      stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 48 h48_le hsb_hi]
    sep_entail

/-- `Ok(bs)` epilogue of `read_file` (`+0x1c8 = 456#64 → +0x1f4 = 500#64 → ret`). -/
theorem cliIoReadFile_ok_epilogue [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 se : State} {fd sret v0 v1 v2 cap ptr st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {bs : List (BitVec 8)} {stackBytes lb_cur lk_cur : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : se.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 456#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hw19 : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : se.readReg64 (.gpr 20#5) = ptr)
    (hx21 : se.readReg64 (.gpr 21#5) = cap)
    (hx24 : se.readReg64 (.gpr 24#5) = sret)
    (hx28 : se.readReg64 (.gpr 28#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = se.fs.setFd fd none →
      sf.trace = se.trace → sf.sigActions = se.sigActions →
      sf.tpidrEl0 = se.tpidrEl0 → sf.brkStart = se.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          (ioResultVecOk A sret cap ptr bs ∗ StdErrnoCell s0.tpidrEl0) ∗
          A.pool lb_cur lk_cur sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        ioVecBuf A cap ptr bs ∗
        StdErrnoCell s0.tpidrEl0 ∗
        A.pool lb_cur lk_cur se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 500#64)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 456#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx20_e' : se'.readReg64 (.gpr 20#5) = ptr := (hcpu_e.readReg64 _).trans hx20
  have hx21_e' : se'.readReg64 (.gpr 21#5) = cap := (hcpu_e.readReg64 _).trans hx21
  have hx24_e' : se'.readReg64 (.gpr 24#5) = sret := (hcpu_e.readReg64 _).trans hx24
  have hx28_e' : se'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 bs.length :=
    (hcpu_e.readReg64 _).trans hx28
  wp_conv_pre =>
    rw [show vecHeader sret v0 v1 v2 =
      (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sc_cl hcpu_c0 hcl_c hnsp_c hsym_c => ?_
  have hcpu_c := hcpu_c0.1
  have ⟨hacp_ec, hpool_ec⟩ :=
    allocCallPreserved_of_seg hcpu_e0 hcpu_c0 hnsp_c hsym_c
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ec : A.pool lb_cur lk_cur se = A.pool lb_cur lk_cur sc_cl :=
    (A.pool_transport _ _ se sc_cl hpool_ec).symm
  have hw19_c : (sc_cl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_c.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_e.readReg64 (.gpr 19#5)]
    exact hw19
  refine SepWP.weaken_pre ?_
    (cliIoReadFile_close_epilogue A hext3 hclose
      (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
      (R_out := ioResultVecOk A sret cap ptr bs ∗ StdErrnoCell s0.tpidrEl0)
      (lb_f := lb_cur) (lk_f := lk_cur)
      hlo hhi hfd_lt (by rw [hacp_ec.1]; exact hfds) hkind hcl_c
      (hcpu_c.pc_eq.trans (by simp [arm64_norm])) (hcpu_c.status_eq.trans hrun_e') hsp0
      (hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = se'.sp).trans (hcpu_e.sp_eq.trans hsp_eq)))
      hw19_c
      (hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
        (hcpu_e.calleeSavedVRegs.trans hvregs)))
      fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
        hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
          (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_ec.1))
          (htr_f.trans hacp_ec.2.1) (hsig_f.trans hacp_ec.2.2.1)
          (htp_f.trans hacp_ec.2.2.2.1) (hbs_f.trans hacp_ec.2.2.2.2.1) hent)
  rw [hpool_eq_ec]
  dsimp only [ioResultVecOk, vecHeader]
  sep_entail

/-- `Err(())` epilogue of `read_file` when `cap = 0` (`+0x1d4 = 468#64 → +0x1f4 = 500#64 → ret`),
    used on `.localDir` (`EISDIR`) where `cbz x22, 0x1f4` skips `__rust_dealloc`. -/
theorem cliIoReadFile_err_cap0_epilogue [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 se : State} {fd sret v0 v1 v2 st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {stackBytes lb lk : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : se.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 468#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hw19 : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx21 : se.readReg64 (.gpr 21#5) = 0#64)
    (hx24 : se.readReg64 (.gpr 24#5) = sret)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = se.fs.setFd fd none →
      sf.trace = se.trace → sf.sigActions = se.sigActions →
      sf.tpidrEl0 = se.tpidrEl0 → sf.brkStart = se.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          (((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
            StdErrnoCell s0.tpidrEl0) ∗
          A.pool lb lk sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        StdErrnoCell s0.tpidrEl0 ∗
        A.pool lb lk se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 500#64)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 468#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx21_e' : se'.readReg64 (.gpr 21#5) = 0#64 := (hcpu_e.readReg64 _).trans hx21
  have hx24_e' : se'.readReg64 (.gpr 24#5) = sret := (hcpu_e.readReg64 _).trans hx24
  wp_conv_pre =>
    rw [show vecHeader sret v0 v1 v2 =
      (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sc_cl hcpu_c0 hcl_c hnsp_c hsym_c => ?_
  have hcpu_c := hcpu_c0.1
  have ⟨hacp_ec, hpool_ec⟩ :=
    allocCallPreserved_of_seg hcpu_e0 hcpu_c0 hnsp_c hsym_c
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ec : A.pool lb lk se = A.pool lb lk sc_cl :=
    (A.pool_transport _ _ se sc_cl hpool_ec).symm
  have hw19_c : (sc_cl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_c.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_e.readReg64 (.gpr 19#5)]
    exact hw19
  have herr_sret := vecHeader_to_err_sret sret v1 v2
  dsimp only [vecHeader] at herr_sret
  refine SepWP.weaken_pre ?_
    (cliIoReadFile_close_epilogue A hext3 hclose
      (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
      (R_out := ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
        StdErrnoCell s0.tpidrEl0)
      (lb_f := lb) (lk_f := lk)
      hlo hhi hfd_lt (by rw [hacp_ec.1]; exact hfds) hkind hcl_c
      (hcpu_c.pc_eq.trans (by simp [arm64_norm])) (hcpu_c.status_eq.trans hrun_e') hsp0
      (hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = se'.sp).trans (hcpu_e.sp_eq.trans hsp_eq)))
      hw19_c
      (hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
        (hcpu_e.calleeSavedVRegs.trans hvregs)))
      fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
        hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
          (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_ec.1))
          (htr_f.trans hacp_ec.2.1) (hsig_f.trans hacp_ec.2.2.1)
          (htp_f.trans hacp_ec.2.2.2.1) (hbs_f.trans hacp_ec.2.2.2.2.1) hent)
  rw [hpool_eq_ec]
  let Rest : SepProp :=
    stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 8320#64) 4096 ∗
      memRegion (s0.sp - 4224#64) 4096 ∗ vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗
      StdErrnoCell s0.tpidrEl0 ∗ A.pool lb lk sc_cl
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono_left (Q := Rest) herr_sret) (by dsimp only [Rest]; sep_entail))
  dsimp only [Rest]; sep_entail

/-- Over-cap `Err(())` epilogue of `read_file` (`+0x1d4 = 468#64 → bl __rust_dealloc → close → ret`),
    cancelling `(lb + A.cost cap 1, lk + 1)` back to `(lb, lk)` before `close(w19)`. -/
theorem cliIoReadFile_err_dealloc_epilogue [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustStdDeallocSpec A))
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 se : State} {fd sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {bs : List (BitVec 8)} {cap stackBytes lb lk : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 + Rust.hookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcap_pos : 0 < cap) (hcap_lt63 : cap < 2 ^ 63)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : se.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl03.base + 468#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 8320#64)
    (hw19 : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : se.readReg64 (.gpr 20#5) = ptr)
    (hx21 : se.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx24 : se.readReg64 (.gpr 24#5) = sret)
    (htp : se.tpidrEl0 = s0.tpidrEl0)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = se.fs.setFd fd none →
      sf.trace = se.trace → sf.sigActions = se.sigActions →
      sf.tpidrEl0 = se.tpidrEl0 → sf.brkStart = se.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          (((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
            StdErrnoCell s0.tpidrEl0) ∗
          A.pool lb lk sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        ioVecBuf A (BitVec.ofNat 64 cap) ptr bs ∗
        StdErrnoCell s0.tpidrEl0 ∗
        A.pool (lb + A.cost cap 1) (lk + 1) se)
      post oomProp := by
  have hlo8368 : 8368 ≤ stackBytes := by dsimp [Rust.hookStack] at hlo; omega
  have hhk_le : Rust.hookStack ≤ stackBytes - 8320 := by omega
  have hsb_hi : stackBytes - 8320 ≤ 2 ^ 64 := by omega
  have hcap_lt64 : cap < 2 ^ 64 := Nat.lt_trans hcap_lt63 (by decide)
  have hcap_beq0 : (BitVec.ofNat 64 cap == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) hcap_lt64 (by decide)
  have hcap_toNat : (BitVec.ofNat 64 cap).toNat = cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64]
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) Rust.hookStack hhk_le hsb_hi]
    simp only [sepConj_assoc]
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl03.base + 468#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx20_e' : se'.readReg64 (.gpr 20#5) = ptr := (hcpu_e.readReg64 _).trans hx20
  have hx21_e' : se'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_e.readReg64 _).trans hx21
  have hx24_e' : se'.readReg64 (.gpr 24#5) = sret := (hcpu_e.readReg64 _).trans hx24
  wp_conv_pre =>
    rw [show vecHeader sret v0 v1 v2 =
      (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
  wp_sym_steps
  refine SepWP.done cliIoReadFile_dealloc_pc (by simpa [arm64_norm] using hrun_e')
    fun sm_dl hcpu_dl0 hcl_dl hnsp_dl hsym_dl => ?_
  have hcpu_dl := hcpu_dl0.1
  have ⟨hacp_edl, hpool_edl⟩ :=
    allocCallPreserved_of_seg hcpu_e0 hcpu_dl0 hnsp_dl hsym_dl
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_edl :
      A.pool (lb + A.cost cap 1) (lk + 1) se = A.pool (lb + A.cost cap 1) (lk + 1) sm_dl :=
    (A.pool_transport _ _ se sm_dl hpool_edl).symm
  have htp_dl : sm_dl.tpidrEl0 = s0.tpidrEl0 := hacp_edl.2.2.2.1.trans htp
  have hpc_dl : sm_dl.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym :=
    hcpu_dl.pc_eq.trans cliIoReadFile_dealloc_pc
  have hrun_dl : sm_dl.status = .Running := hcpu_dl.status_eq.trans hrun_e'
  have hsp_dl_eq : sm_dl.sp = s0.sp - 8320#64 :=
    hcpu_dl.sp_eq.trans ((by simp [arm64_norm] : _ = se'.sp).trans (hcpu_e.sp_eq.trans hsp_eq))
  have hsp_dl : sm_dl.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_dl_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_dl : sm_dl.readReg64 .lr = cliIoPl03.base + 500#64 := by
    rw [hcpu_dl.readReg64 .lr]; simp [arm64_norm]
  have hx0_dl : sm_dl.readReg64 .x0 = ptr :=
    (hcpu_dl.readReg64 .x0).trans (by simp [arm64_norm])
  have hx1_dl : (sm_dl.readReg64 .x1).toNat = cap := by
    rw [hcpu_dl.readReg64 .x1]; simpa [arm64_norm] using hcap_toNat
  have hx2_dl : (sm_dl.readReg64 .x2).toNat = 1 := by
    rw [hcpu_dl.readReg64 .x2]; simp [arm64_norm]
  have herr_sret := vecHeader_to_err_sret sret v1 v2
  dsimp only [vecHeader] at herr_sret
  have hde_mem := ioVecBuf_entails_dealloc_mem A (ptr := ptr) (bs := bs) hcap_pos hcap_lt63
  let T_dl : SepProp :=
    memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320))
        (stackBytes - 8320 - Rust.hookStack) ∗
      memRegion (s0.sp - 8320#64) 4096 ∗
      memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗
      ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16)
  apply seqCodeLoaded hcl_dl (mid := cliIoPl03.base + 500#64)
  apply (SepWP.call_subroutine_frame (F := T_dl) hdealloc
    (x := (ptr, cap, 1, lb + A.cost cap 1, lk + 1))
    hpc_dl hrun_dl hsp_dl hlr_dl
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [rustStdDeallocSpec, T_dl, Rust.hookFrame]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_dl, hx1_dl, hx2_dl⟩, ?_⟩
    refine Satisfies.mono ?_ hm'
    rw [hpool_eq_edl, htp_dl, hsp_dl_eq]
    let Rest : SepProp :=
      memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320))
          (stackBytes - 8320 - Rust.hookStack) ∗
        stackAt (s0.sp - 8320#64) Rust.hookStack ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        StdErrnoCell s0.tpidrEl0 ∗
        A.pool (lb + A.cost cap 1) (lk + 1) sm_dl ∗ R'
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := Rest) (sepConj_mono herr_sret hde_mem))
        (by dsimp only [Rest, ProofLib.stackAt]; sep_entail))
    dsimp only [Rest, ProofLib.stackAt]; sep_entail
  · intro sm_dl' hpc_dl' hrun_dl' hsp_dl' hcs_dl'
    refine SepWP.done hpc_dl' hrun_dl' fun hcl_dl' => ?_
    wp_conv_pre => dsimp only [rustStdDeallocSpec, T_dl, Rust.hookFrame]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; intro hacp_dl'
    have hsp_dl'_eq : sm_dl'.sp = s0.sp - 8320#64 := hsp_dl'.trans hsp_dl_eq
    have hw19_dl' : (sm_dl'.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
      rw [readReg32_of_readReg64_eq hcs_dl'.readReg64_x19,
        readReg32_of_readReg64_eq (hcpu_dl.readReg64 (.gpr 19#5))]
      simp only [arm64_norm]
      rw [hcpu_e.readReg64 (.gpr 19#5)]
      exact hw19
    have hvregs_dl' : calleeSavedVRegs sm_dl' = calleeSavedVRegs s0 :=
      hcs_dl'.vregs.trans (hcpu_dl.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs)))
    have hacp_edl' : AllocCallPreserved se sm_dl' := allocCallPreserved_trans hacp_edl hacp_dl'
    refine SepWP.weaken_pre ?_
      (cliIoReadFile_close_epilogue A hext3 hclose
        (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
        (R_out := ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
          StdErrnoCell s0.tpidrEl0)
        (lb_f := lb) (lk_f := lk)
        hlo8368 hhi hfd_lt (by rw [hacp_edl'.1]; exact hfds) hkind hcl_dl'
        hpc_dl' hrun_dl' hsp0 hsp_dl'_eq hw19_dl' hvregs_dl'
        fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
          hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
            (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_edl'.1))
            (htr_f.trans hacp_edl'.2.1) (hsig_f.trans hacp_edl'.2.2.1)
            (htp_f.trans hacp_edl'.2.2.2.1) (hbs_f.trans hacp_edl'.2.2.2.2.1) hent)
    rw [dealloc_cancel_lb A lb cap 1, dealloc_cancel_lk lk, htp_dl, hsp_dl_eq,
      stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) Rust.hookStack hhk_le hsb_hi]
    dsimp only [ProofLib.stackAt]
    sep_entail





end

end LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps
