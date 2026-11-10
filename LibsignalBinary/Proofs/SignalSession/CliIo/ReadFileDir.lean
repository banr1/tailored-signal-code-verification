/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps
public import VerifiedLibraries.Musl.Proofs.SyscallProof

/-!
# Directory-FD Read and `EISDIR` / `EFAULT` Exit Path for `read_file`

Proves `cliIoReadFile_dir_loop` for `signalSessionIoMultiLib` block `3` (`signal_session_io::read_file`)
on an open `.localDir` descriptor from loop header `+0xd8`: `read` returns `-1` with `errno ∈ {21, 14}`
(`≠ 4`), skips `__rust_dealloc` at `cap = 0`, closes `fd`, and returns `Err(())`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileDir

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open VerifiedLibraries.Musl (muslErrnoLocationSpec)
open VerifiedLibraries.RustStd (
  RustStdAlloc StdErrnoCell stdErrnoAddr vecHeader
)
open VerifiedLibraries.RustStd.Io (allocCallPreserved_of_seg)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  sepWP_seg_cliIo_block_pure
  cliIoCloseSym cliIoReadSym cliIoErrnoLocationSym
  cliIoPl03 cliIoPC03 cliIoBlockNoSvc0_03
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  poolPreserved_of_syscall poolPreserved_of_stdState cliIoSavedRegs12
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (
  muslClose48LocalSpec muslReadDir32Spec dirReadErrno32 dirReadErrno32_cases
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps (
  cliIo3_lt cliIoReadFile_read_pc cliIoReadFile_errno3_pc
  readReg32_of_readReg64_eq cliIoReadFile_err_cap0_epilogue
)

section
arm64_proof_prelude

theorem muslErrnoAddr_eq_stdErrnoAddr (s : State) :
    muslErrnoAddr s = stdErrnoAddr s.tpidrEl0 := rfl

/-- `.localDir` path at `+0xd8 = 216#64`: `read` returns `-1` with `errno ∈ {21, 14}` (`≠ 4`),
    `__errno_location` + `cmp w8, #4` takes `+0x100: b 0x1d4`, `cbz x22, 0x1f4` skips dealloc, and
    `close(fd)` restores `sf.fs = sl.fs.setFd fd none` and returns `Err(())`. -/
theorem cliIoReadFile_dir_loop [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadDir32Spec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 sl : State} {fd count sret v0 v1 v2 st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {stackBytes lb lk : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : sl.fs.fds fd = some desc)
    (hkind : desc.kind = .localDir) (hcanr : desc.accMode.canRead = true)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sl.mem)
    (hpc : sl.pc = cliIoPl03.base + 216#64) (hrun : sl.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sl.sp = s0.sp - 8320#64)
    (hw19 : (sl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx21 : sl.readReg64 (.gpr 21#5) = 0#64)
    (hx23 : sl.readReg64 (.gpr 23#5) = count)
    (hx24 : sl.readReg64 (.gpr 24#5) = sret)
    (htp : sl.tpidrEl0 = s0.tpidrEl0)
    (hvregs : calleeSavedVRegs sl = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = sl.fs.setFd fd none →
      sf.trace = sl.trace → sf.sigActions = sl.sigActions →
      sf.tpidrEl0 = sl.tpidrEl0 → sf.brkStart = sl.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          (((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
            StdErrnoCell s0.tpidrEl0) ∗
          A.pool lb lk sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sl
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        StdErrnoCell s0.tpidrEl0 ∗
        A.pool lb lk sl)
      post oomProp := by
  have h32_le : 32 ≤ stackBytes - 8320 := by omega
  have hsb_hi : stackBytes - 8320 ≤ 2 ^ 64 := by omega
  wp_conv_pre =>
    dsimp only [StdErrnoCell]
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 32 h32_le hsb_hi]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro e0
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
  intro sl' hcpu_l0
  have hcpu_l := hcpu_l0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_l' : sl'.pc = cliIoPl03.base + 216#64 := hcpu_l.pc_eq.trans hpc
  have hrun_l' : sl'.status = .Running := hcpu_l.status_eq.trans hrun
  have hsp_l_in : sl'.sp = s0.sp - 8320#64 := hcpu_l.sp_eq.trans hsp_eq
  have hsp_l' : sl'.spAligned = true := by
    rw [hcpu_l.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx23_l' : sl'.readReg64 (.gpr 23#5) = count := (hcpu_l.readReg64 _).trans hx23
  wp_sym_steps
  refine SepWP.done cliIoReadFile_read_pc (by simpa [arm64_norm] using hrun_l')
    fun sm_rd hcpu_rd0 hcl_rd hnsp_rd hsym_rd => ?_
  have hcpu_rd := hcpu_rd0.1
  have ⟨hacp_lrd, hpool_lrd⟩ :=
    allocCallPreserved_of_seg hcpu_l0 hcpu_rd0 hnsp_rd hsym_rd
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_lrd : A.pool lb lk sl = A.pool lb lk sm_rd :=
    (A.pool_transport _ _ sl sm_rd hpool_lrd).symm
  have hpc_rd : sm_rd.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym :=
    hcpu_rd.pc_eq.trans cliIoReadFile_read_pc
  have hrun_rd : sm_rd.status = .Running := hcpu_rd.status_eq.trans hrun_l'
  have hsp_rd_eq : sm_rd.sp = s0.sp - 8320#64 :=
    hcpu_rd.sp_eq.trans ((by simp [arm64_norm] : _ = sl'.sp).trans hsp_l_in)
  have hsp_rd : sm_rd.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_rd_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_rd : sm_rd.readReg64 .lr = cliIoPl03.base + 232#64 := by
    rw [hcpu_rd.readReg64 .lr]; simp [arm64_norm]
  have hx0_rd : (sm_rd.readReg32 .x0).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_rd.readReg64 .x0)]
    simp only [arm64_norm]
    rw [hcpu_l.readReg64 (.gpr 19#5)]
    exact hw19
  have hx1_rd : sm_rd.readReg64 .x1 = s0.sp - 4224#64 := by
    rw [hcpu_rd.readReg64 .x1]; simp only [arm64_norm]
  have hx2_rd : sm_rd.readReg64 .x2 = count := by
    rw [hcpu_rd.readReg64 .x2]; simp [arm64_norm]
  have hfds_rd : sm_rd.fs.fds fd = some desc := by rw [hacp_lrd.1]; exact hfds
  have htp_rd : sm_rd.tpidrEl0 = s0.tpidrEl0 := hacp_lrd.2.2.2.1.trans htp
  let T_rd : SepProp :=
    memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320)) (stackBytes - 8320 - 32) ∗
      memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ A.pool lb lk sm_rd
  apply seqCodeLoaded hcl_rd (mid := cliIoPl03.base + 232#64)
  apply (SepWP.call_subroutine_frame hread_dir (F := T_rd)
    (x := (fd, s0.sp - 4224#64, count, desc, e0))
    hpc_rd hrun_rd hsp_rd hlr_rd
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslReadDir32Spec, T_rd]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_rd, hfd_lt, hx1_rd, hx2_rd, hfds_rd, hkind, hcanr⟩, ?_⟩
    rw [hpool_eq_lrd] at hm'
    rw [hsp_rd_eq, muslErrnoAddr_eq_stdErrnoAddr, htp_rd]
    exact Satisfies.mono (by sep_frame) hm'

  · intro sr hpc_sr hrun_sr hsp_sr hcs_rdsr
    refine SepWP.done hpc_sr hrun_sr fun hcl_sr => ?_
    wp_conv_pre => dsimp only [muslReadDir32Spec, T_rd]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_sr, _, herr_ne4, hfs_sr, htr_sr, hsys_sr⟩
    have hpool_eq_sr : A.pool lb lk sm_rd = A.pool lb lk sr :=
      (A.pool_transport _ _ sm_rd sr (poolPreserved_of_syscall hsys_sr)).symm
    have hsp_sr_eq : sr.sp = s0.sp - 8320#64 := hsp_sr.trans hsp_rd_eq
    have htp_sr : sr.tpidrEl0 = s0.tpidrEl0 := hsys_sr.1.trans htp_rd
    apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_sr
      (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
    intro sr' hcpu_r0
    have hcpu_r := hcpu_r0.1
    change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
    have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc_sr
    have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun_sr
    have hsp_r' : sr'.spAligned = true := by
      rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_sr_eq]
      exact s0.spAligned_sub 8320#64 hsp0
    have hx0_r' : sr'.readReg64 .x0 = -1#64 := (hcpu_r.readReg64 _).trans hx0_sr
    wp_sym_steps
    refine SepWP.done cliIoReadFile_errno3_pc (by simpa [arm64_norm] using hrun_r')
      fun sm_el hcpu_el0 hcl_el hnsp_el hsym_el => ?_
    have hcpu_el := hcpu_el0.1
    have ⟨hacp_rel, hpool_rel⟩ :=
      allocCallPreserved_of_seg hcpu_r0 hcpu_el0 hnsp_el hsym_el
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_rel : A.pool lb lk sr = A.pool lb lk sm_el :=
      (A.pool_transport _ _ sr sm_el hpool_rel).symm
    have hpc_el : sm_el.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym :=
      hcpu_el.pc_eq.trans cliIoReadFile_errno3_pc
    have hrun_el : sm_el.status = .Running := hcpu_el.status_eq.trans hrun_r'
    have hsp_el_eq : sm_el.sp = s0.sp - 8320#64 :=
      hcpu_el.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_sr_eq))
    have hsp_el : sm_el.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_el_eq]; exact s0.spAligned_sub 8320#64 hsp0
    have hlr_el : sm_el.readReg64 .lr = cliIoPl03.base + 244#64 := by
      rw [hcpu_el.readReg64 .lr]; simp [arm64_norm]
    have htp_el : sm_el.tpidrEl0 = s0.tpidrEl0 := hacp_rel.2.2.2.1.trans htp_sr
    let ev := dirReadErrno32 (s0.sp - 4224#64) count
    have hev_beq4 : (ev == 4#32) = false := beq_false_of_ne herr_ne4
    let T_el : SepProp :=
      stackAt sm_rd.sp 32 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ∗
        memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320)) (stackBytes - 8320 - 32) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ A.pool lb lk sm_el
    apply seqCodeLoaded hcl_el (mid := cliIoPl03.base + 244#64)
    apply (SepWP.call_subroutine_frame herrno (F := T_el) (x := ())
      hpc_el hrun_el hsp_el hlr_el
      (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
      (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
    · intro R' hm'
      dsimp only [muslErrnoLocationSpec, T_el]
      rw [emp_sepConj]
      rw [hpool_eq_sr, hpool_eq_rel, muslErrnoAddr_eq_stdErrnoAddr, htp_sr] at hm'
      exact Satisfies.mono (by dsimp only [ev]; sep_frame) hm'
    · intro se0 hpc_se0 hrun_se0 hsp_se0 hcs_else0
      refine SepWP.done hpc_se0 hrun_se0 fun hcl_se0 => ?_
      wp_conv_pre => dsimp only [muslErrnoLocationSpec, T_el]; simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hx0_se0, _, hstd_el⟩
      have hpool_eq_el : A.pool lb lk sm_el = A.pool lb lk se0 :=
        (A.pool_transport _ _ sm_el se0 (poolPreserved_of_stdState hstd_el)).symm
      have hsp_se0_eq : se0.sp = s0.sp - 8320#64 := hsp_se0.trans hsp_el_eq
      have hx0_se0' : se0.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 := by
        rw [hx0_se0, muslErrnoAddr_eq_stdErrnoAddr, htp_el]
      apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_se0
        (mid := cliIoPl03.base + 468#64)
      intro sc' hcpu_c0
      have hcpu_c := hcpu_c0.1
      change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
      have hpc_c' : sc'.pc = cliIoPl03.base + 244#64 := hcpu_c.pc_eq.trans hpc_se0
      have hrun_c' : sc'.status = .Running := hcpu_c.status_eq.trans hrun_se0
      have hsp_c' : sc'.spAligned = true := by
        rw [hcpu_c.spAligned]; simp only [State.spAligned]; rw [hsp_se0_eq]
        exact s0.spAligned_sub 8320#64 hsp0
      have hx0_c' : sc'.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 := (hcpu_c.readReg64 _).trans hx0_se0'
      have hev_zext_beq4 : (BitVec.setWidth 64 ev - 4#64 == 0#64) = false := by
        rcases dirReadErrno32_cases (s0.sp - 4224#64) count with h21 | h14
        · dsimp only [ev]; rw [h21]; decide
        · dsimp only [ev]; rw [h14]; decide
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_c')
        fun se_ep hcpu_ep0 hcl_ep hnsp_ep hsym_ep => ?_
      have hcpu_ep := hcpu_ep0.1
      have ⟨hacp_cep, hpool_cep⟩ :=
        allocCallPreserved_of_seg hcpu_c0 hcpu_ep0 hnsp_ep hsym_ep
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_cep : A.pool lb lk se0 = A.pool lb lk se_ep :=
        (A.pool_transport _ _ se0 se_ep hpool_cep).symm
      have hfs_ep : se_ep.fs = sl.fs :=
        hacp_cep.1.trans (hstd_el.1.trans (hacp_rel.1.trans (hfs_sr.trans hacp_lrd.1)))
      have htr_ep : se_ep.trace = sl.trace :=
        hacp_cep.2.1.trans (hstd_el.2.1.trans (hacp_rel.2.1.trans (htr_sr.trans hacp_lrd.2.1)))
      have hsig_ep : se_ep.sigActions = sl.sigActions :=
        hacp_cep.2.2.1.trans (hstd_el.2.2.2.1.trans (hacp_rel.2.2.1.trans (hsys_sr.2.1.trans hacp_lrd.2.2.1)))
      have htp_ep : se_ep.tpidrEl0 = sl.tpidrEl0 :=
        hacp_cep.2.2.2.1.trans (hstd_el.2.2.1.trans (hacp_rel.2.2.2.1.trans (hsys_sr.1.trans hacp_lrd.2.2.2.1)))
      have hbs_ep : se_ep.brkStart = sl.brkStart :=
        hacp_cep.2.2.2.2.1.trans (hstd_el.2.2.2.2.2.1.trans
          (hacp_rel.2.2.2.2.1.trans (hsys_sr.2.2.brkStart_eq.trans hacp_lrd.2.2.2.2.1)))
      have hw19_ep : (se_ep.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
        rw [readReg32_of_readReg64_eq (hcpu_ep.readReg64 (.gpr 19#5))]
        simp only [arm64_norm]
        rw [hcpu_c.readReg64 (.gpr 19#5), hcs_else0.readReg64_x19,
          hcpu_el.readReg64 (.gpr 19#5)]
        simp only [arm64_norm]
        rw [hcpu_r.readReg64 (.gpr 19#5), hcs_rdsr.readReg64_x19,
          hcpu_rd.readReg64 (.gpr 19#5)]
        simp only [arm64_norm]
        rw [hcpu_l.readReg64 (.gpr 19#5)]
        exact hw19
      have hx21_ep : se_ep.readReg64 (.gpr 21#5) = 0#64 := by
        rw [hcpu_ep.readReg64]; simp only [arm64_norm]
        rw [hcpu_c.readReg64, hcs_else0.readReg64_x21, hcpu_el.readReg64]; simp only [arm64_norm]
        rw [hcpu_r.readReg64, hcs_rdsr.readReg64_x21, hcpu_rd.readReg64]; simp only [arm64_norm]
        exact (hcpu_l.readReg64 _).trans hx21
      have hx24_ep : se_ep.readReg64 (.gpr 24#5) = sret := by
        rw [hcpu_ep.readReg64]; simp only [arm64_norm]
        rw [hcpu_c.readReg64, hcs_else0.readReg64_x24, hcpu_el.readReg64]; simp only [arm64_norm]
        rw [hcpu_r.readReg64, hcs_rdsr.readReg64_x24, hcpu_rd.readReg64]; simp only [arm64_norm]
        exact (hcpu_l.readReg64 _).trans hx24
      have hvregs_ep : calleeSavedVRegs se_ep = calleeSavedVRegs s0 :=
        hcpu_ep.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sc').trans
          (hcpu_c.calleeSavedVRegs.trans (hcs_else0.vregs.trans
            (hcpu_el.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
              (hcpu_r.calleeSavedVRegs.trans (hcs_rdsr.vregs.trans
                (hcpu_rd.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sl').trans
                  (hcpu_l.calleeSavedVRegs.trans hvregs))))))))))
      refine SepWP.weaken_pre ?_
        (cliIoReadFile_err_cap0_epilogue A hext3 hclose
          (v0 := v0) (v1 := v1) (v2 := v2)
          (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
          (lb := lb) (lk := lk)
          hlo hhi hfd_lt (by rw [hfs_ep]; exact hfds) (Or.inr hkind) hcl_ep
          (hcpu_ep.pc_eq.trans (by simp [arm64_norm])) (hcpu_ep.status_eq.trans hrun_c') hsp0
          (hcpu_ep.sp_eq.trans ((by simp [arm64_norm] : _ = sc'.sp).trans (hcpu_c.sp_eq.trans hsp_se0_eq)))
          hw19_ep hx21_ep hx24_ep hvregs_ep
          fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
            hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
              (hfs_f.trans (congrArg (fun f => f.setFd fd none) hfs_ep))
              (htr_f.trans htr_ep) (hsig_f.trans hsig_ep) (htp_f.trans htp_ep) (hbs_f.trans hbs_ep) hent)
      rw [hpool_eq_el, hpool_eq_cep, hsp_rd_eq,
        stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 32 h32_le hsb_hi]
      have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ⊢ StdErrnoCell s0.tpidrEl0 :=
        Entails.sepExists_right ev (Entails.refl _)
      let Rest : SepProp :=
        stackAt (s0.sp - 8320#64) 32 ∗
          memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320)) (stackBytes - 8320 - 32) ∗
          memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ A.pool lb lk se_ep
      refine Entails.trans ?_
        (Entails.trans (sepConj_mono_right (P := Rest) hev_cell) (by dsimp only [Rest]; sep_entail))
      dsimp only [Rest]; sep_entail

end

end LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileDir
