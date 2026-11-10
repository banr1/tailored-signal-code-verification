/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileGrowSteps
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic
public import VerifiedLibraries.Musl.Proofs.SyscallProof

/-!
# Bounded `read_file` `.localFile` Chunk Loop

Proves `cliIoReadFile_file_loop` for `signalSessionIoMultiLib` block `3` (`signal_session_io::read_file`)
from loop header `+0xd8` (`FILE_CAP = 2^21 = 2,097,152`): bounded `4096`-byte `.localFile` read loop
and `close(fd)` restoring `sf.fs = s0.fs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileLoop

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open VerifiedLibraries.RustStd (
  RustStdAlloc PoolPreserved
  AllocCallPreserved IoFrame StdErrnoCell
  vecHeader ioVecBuf ioResultVecOk
  rustStdDeallocSpec allocFinishGrowSpec
  AllocSeqFits allocSeqPool
)
open VerifiedLibraries.RustStd.Io (allocCallPreserved_of_seg)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  sepWP_seg_cliIo_block_pure
  cliIoCloseSym cliIoReadSym
  cliIoMemcpySym cliIoFinishGrowSym cliIoRustDeallocSym
  cliIoPl03 cliIoPC03 cliIoBlockNoSvc0_03
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  poolPreserved_of_syscall
  cliIoFileCap cliIoCap cliIoCap_mono
  cliIoCap_pos cliIoCap_lt_pow63
  cliIoCapIdx cliIoCapIdx_le le_cliIoCap_cliIoCapIdx
  cliIoCapIdx_eq_of_bounds cliIoCapIdx_cap_self
  cliIoReadCaps cliIoFinalCap cliIoFinalCap_zero cliIoFinalCap_pos
  allocSeqPool_cliIoReadCaps_pos
  AllocSeqFits_canAlloc_zero AllocSeqFits_canAlloc_succ
  wantBytes wantBytes_pos wantBytes_le_4096
  overCap_forces_eq_max dvd_4096_preserved no_grow_capIdx_eq grow_step_bounds
  bit63_eq_zero_of_lt bv64_ult_ofNat_true bv64_ult_ofNat_false
  bv64_beq_ofNat_false bv64_sub_ofNat
  cliIoSavedRegs12 stackBuf4096_repack
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (muslClose48LocalSpec)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin (
  muslReadFileOrStdio32Spec sp_sub_4224_va_bound
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic (setFd_none_setFd_of_fds_none)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinSteps (CliIoMidPreserved)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps (
  cliIo3_lt cliIoReadFile_read_pc
  readReg32_of_readReg64_eq
  cliIoReadFile_ok_epilogue cliIoReadFile_err_dealloc_epilogue
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileGrowSteps (
  cliIoReadFile_grow_from_zero cliIoReadFile_grow_from_pos cliIoReadFile_memcpy_backedge
)

section
arm64_proof_prelude

/-- Spatial + `fs` postcondition of `read_file` on `.localFile` (`rem = (s0.fs.fdBytes d0).drop d0.offset`). -/
def cliIoFileLoopResult {oom : State → State → Prop} (A : RustStdAlloc oom)
    (sret : BitVec 64) (d0 : FdEntry) (lb lk : Nat) (s0 sf : State) : SepProp :=
  let rem := (s0.fs.fdBytes d0).drop d0.offset
  if rem.length ≤ cliIoFileCap then
    ⌜sf.fs = s0.fs⌝ ∗
      (∃∗ ptr : BitVec 64,
        ioResultVecOk A sret (BitVec.ofNat 64 (cliIoFinalCap 9 rem.length)) ptr rem) ∗
      A.pool (allocSeqPool A 1 lb lk (cliIoReadCaps 9 rem.length)).1
        (allocSeqPool A 1 lb lk (cliIoReadCaps 9 rem.length)).2 sf
  else
    ⌜sf.fs = s0.fs⌝ ∗
      ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
      A.pool lb lk sf

/-- OOM postcondition of `read_file` on `.localFile` (`fd` still open at `d0.offset + k`). -/
def cliIoFileOom (oom : State → State → Prop) (fd : BitVec 64) (d0 : FdEntry) (s0 sf : State) : SepProp :=
  ⌜∃ k sm, k ≤ min ((s0.fs.fdBytes d0).drop d0.offset).length cliIoFileCap ∧
    IoFrame s0 sm ∧
    sm.fs = s0.fs.setFd fd (some { d0 with offset := d0.offset + k }) ∧
    oom sm sf⌝

/-- Post-`read` EOF (`x0 = 0#64`) branch `+0xe8 → +0x1c8`: jumps to `Ok` + `close` epilogue. -/
private theorem cliIoReadFile_after_read_eof [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 sr : State} {fd sret v0 v1 v2 cap ptr st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {bs : List (BitVec 8)} {stackBytes lb_cur lk_cur : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : sr.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl03.base + 232#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 8320#64)
    (hx0 : sr.readReg64 .x0 = 0#64)
    (hw19 : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = cap)
    (hx24 : sr.readReg64 (.gpr 24#5) = sret)
    (hx28 : sr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = sr.fs.setFd fd none →
      sf.trace = sr.trace → sf.sigActions = sr.sigActions →
      sf.tpidrEl0 = sr.tpidrEl0 → sf.brkStart = sr.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          (ioResultVecOk A sret cap ptr bs ∗ StdErrnoCell s0.tpidrEl0) ∗
          A.pool lb_cur lk_cur sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sr
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        ioVecBuf A cap ptr bs ∗ StdErrnoCell s0.tpidrEl0 ∗ A.pool lb_cur lk_cur sr)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 456#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = 0#64 := (hcpu_r.readReg64 _).trans hx0
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
  have hcpu_e := hcpu_e0.1
  have ⟨hacp_re, hpool_re⟩ :=
    allocCallPreserved_of_seg hcpu_r0 hcpu_e0 hnsp_e hsym_e
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool lb_cur lk_cur sr = A.pool lb_cur lk_cur se :=
    (A.pool_transport _ _ sr se hpool_re).symm
  have hw19_e : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_e.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_r.readReg64 (.gpr 19#5)]
    exact hw19
  rw [hpool_eq]
  exact cliIoReadFile_ok_epilogue A hext3 hclose hlo hhi hfd_lt
    (by rw [hacp_re.1]; exact hfds) hkind hcl_e
    (hcpu_e.pc_eq.trans (by simp [arm64_norm])) (hcpu_e.status_eq.trans hrun_r') hsp0
    (hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    hw19_e
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx21)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx28)
    (hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
      hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
        (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_re.1))
        (htr_f.trans hacp_re.2.1) (hsig_f.trans hacp_re.2.2.1)
        (htp_f.trans hacp_re.2.2.2.1) (hbs_f.trans hacp_re.2.2.2.2.1) hent

/-- Post-`read` over-cap (`len = 2097152`, `n = 1`, `want = 1`) branch `+0xe8 .. +0x114 → +0x1d4`. -/
private theorem cliIoReadFile_after_read_overcap [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustStdDeallocSpec A))
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 sr : State} {fd sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {bs : List (BitVec 8)} {stackBytes lb lk : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 + Rust.hookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : sr.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl03.base + 232#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 8320#64)
    (hx0 : sr.readReg64 .x0 = 1#64)
    (hw19 : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap 9))
    (hx23 : sr.readReg64 (.gpr 23#5) = 1#64)
    (hx24 : sr.readReg64 (.gpr 24#5) = sret)
    (hx26 : sr.readReg64 (.gpr 26#5) = 2097152#64)
    (hx28 : sr.readReg64 (.gpr 28#5) = 2097152#64)
    (htp : sr.tpidrEl0 = s0.tpidrEl0)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = sr.fs.setFd fd none →
      sf.trace = sr.trace → sf.sigActions = sr.sigActions →
      sf.tpidrEl0 = sr.tpidrEl0 → sf.brkStart = sr.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          (((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
            StdErrnoCell s0.tpidrEl0) ∗
          A.pool lb lk sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sr
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        ioVecBuf A (BitVec.ofNat 64 (cliIoCap 9)) ptr bs ∗
        StdErrnoCell s0.tpidrEl0 ∗ A.pool (lb + A.cost (cliIoCap 9) 1) (lk + 1) sr)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 468#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = 1#64 := (hcpu_r.readReg64 _).trans hx0
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = 1#64 := (hcpu_r.readReg64 _).trans hx23
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_r.readReg64 _).trans hx26
  have hx28_r' : sr'.readReg64 (.gpr 28#5) = 2097152#64 := (hcpu_r.readReg64 _).trans hx28
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
  have hcpu_e := hcpu_e0.1
  have ⟨hacp_re, hpool_re⟩ :=
    allocCallPreserved_of_seg hcpu_r0 hcpu_e0 hnsp_e hsym_e
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool (lb + A.cost (cliIoCap 9) 1) (lk + 1) sr =
      A.pool (lb + A.cost (cliIoCap 9) 1) (lk + 1) se :=
    (A.pool_transport _ _ sr se hpool_re).symm
  have hw19_e : (se.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_e.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_r.readReg64 (.gpr 19#5)]
    exact hw19
  rw [hpool_eq]
  exact cliIoReadFile_err_dealloc_epilogue A hext3 hdealloc hclose hlo hhi
    (cliIoCap_pos 9) (cliIoCap_lt_pow63 (by decide)) hfd_lt
    (by rw [hacp_re.1]; exact hfds) hkind hcl_e
    (hcpu_e.pc_eq.trans (by simp [arm64_norm])) (hcpu_e.status_eq.trans hrun_r') hsp0
    (hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    hw19_e
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx21)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (hacp_re.2.2.2.1.trans htp)
    (hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
      hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
        (hfs_f.trans (congrArg (fun f => f.setFd fd none) hacp_re.1))
        (htr_f.trans hacp_re.2.1) (hsig_f.trans hacp_re.2.2.1)
        (htp_f.trans hacp_re.2.2.2.1) (hbs_f.trans hacp_re.2.2.2.2.1) hent

/-- Post-`read` in-cap no-grow (`0 < n ≤ want`, `len + n ≤ cap ≤ 2097152`) branch
    `+0xe8 .. +0x120 → +0x154 .. +0x158 → +0x15c = 348#64`. -/
private theorem cliIoReadFile_after_read_nogrow [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    {s0 sr : State} {fd sret ptr : BitVec 64} {Pre : SepProp}
    {cap len want n : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hn_pos : 0 < n) (hn_le_want : n ≤ want) (hwant_le : want ≤ 4096)
    (hlen_cap : len + n ≤ cap) (hcap_max : cap ≤ 2097152)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl03.base + 232#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 8320#64)
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 n)
    (hw19 : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx23 : sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sr.readReg64 (.gpr 24#5) = sret)
    (hx25 : sr.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sr.readReg64 (.gpr 26#5) = 2097152#64)
    (hx28 : sr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sr.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sc : State,
      sc.pc = cliIoPl03.base + 348#64 → sc.status = .Running → sc.sp = s0.sp - 8320#64 →
      (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sc.readReg64 (.gpr 20#5) = ptr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = sret →
      sc.readReg64 (.gpr 25#5) = 4096#64 → sc.readReg64 (.gpr 26#5) = 2097152#64 →
      sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem →
      AllocCallPreserved sr sc → PoolPreserved sr sc →
      SepWP P (s0.readReg64 .lr) sc Pre post oomProp) :
    SepWP P (s0.readReg64 .lr) sr Pre post oomProp := by
  have hn_beq0 : (BitVec.ofNat 64 n == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) (by omega) (by decide)
  have hbit63 : (BitVec.ofNat 64 n).getLsbD 63 = false := bit63_eq_zero_of_lt (by omega)
  have hule_w : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 want) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_w : (BitVec.ofNat 64 want).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le_want (by omega)
  have hsub26 : 2097152#64 - BitVec.ofNat 64 len = BitVec.ofNat 64 (2097152 - len) :=
    bv64_sub_ofNat (by omega)
  have hule_rem : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (2097152 - len)) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_rem : (BitVec.ofNat 64 (2097152 - len)).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false (by omega) (by omega)
  have hadd27 : BitVec.ofNat 64 n + BitVec.ofNat 64 len = BitVec.ofNat 64 (len + n) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hule_cap : (BitVec.ofNat 64 (len + n)).ule (BitVec.ofNat 64 cap) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_cap : (BitVec.ofNat 64 cap).ult (BitVec.ofNat 64 (len + n)) = false :=
    bv64_ult_ofNat_false hlen_cap (by omega)
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 348#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_r.readReg64 _).trans hx0
  have hx21_r' : sr'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_r.readReg64 _).trans hx21
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_r.readReg64 _).trans hx23
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_r.readReg64 _).trans hx26
  have hx28_r' : sr'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := (hcpu_r.readReg64 _).trans hx28
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun sc hcpu_c0 hcl_c hnsp_c hsym_c => ?_
  have hcpu_c := hcpu_c0.1
  have ⟨hacp_rc, hpp_rc⟩ :=
    allocCallPreserved_of_seg hcpu_r0 hcpu_c0 hnsp_c hsym_c
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hw19_c : (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_c.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_r.readReg64 (.gpr 19#5)]
    exact hw19
  exact hcont sc (hcpu_c.pc_eq.trans (by simp [arm64_norm])) (hcpu_c.status_eq.trans hrun_r')
    (hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    hw19_c
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx25)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm, hx26_r'])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm, hx28_r'])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx29)
    (hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    hcl_c hacp_rc hpp_rc

/-- Post-`read` in-cap grow (`0 < n ≤ want`, `cap < len + n ≤ 2097152`) branch
    `+0xe8 .. +0x120 → +0x124 = 292#64`. -/
private theorem cliIoReadFile_after_read_grow [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    {s0 sr : State} {fd sret ptr : BitVec 64} {Pre : SepProp}
    {cap len want n : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hn_pos : 0 < n) (hn_le_want : n ≤ want) (hwant_le : want ≤ 4096)
    (hgt_cap : cap < len + n) (hlen_max : len + n ≤ 2097152)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl03.base + 232#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 8320#64)
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 n)
    (hw19 : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx23 : sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sr.readReg64 (.gpr 24#5) = sret)
    (hx25 : sr.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sr.readReg64 (.gpr 26#5) = 2097152#64)
    (hx28 : sr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sr.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sg : State,
      sg.pc = cliIoPl03.base + 292#64 → sg.status = .Running → sg.sp = s0.sp - 8320#64 →
      sg.readReg64 .x0 = BitVec.ofNat 64 n →
      (sg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sg.readReg64 (.gpr 20#5) = ptr →
      sg.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sg.readReg64 (.gpr 24#5) = sret →
      sg.readReg64 (.gpr 25#5) = 4096#64 → sg.readReg64 (.gpr 26#5) = 2097152#64 →
      sg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) →
      sg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sg.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sg = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sg.mem →
      AllocCallPreserved sr sg → PoolPreserved sr sg →
      SepWP P (s0.readReg64 .lr) sg Pre post oomProp) :
    SepWP P (s0.readReg64 .lr) sr Pre post oomProp := by
  have hn_beq0 : (BitVec.ofNat 64 n == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) (by omega) (by decide)
  have hbit63 : (BitVec.ofNat 64 n).getLsbD 63 = false := bit63_eq_zero_of_lt (by omega)
  have hule_w : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 want) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_w : (BitVec.ofNat 64 want).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le_want (by omega)
  have hsub26 : 2097152#64 - BitVec.ofNat 64 len = BitVec.ofNat 64 (2097152 - len) :=
    bv64_sub_ofNat (by omega)
  have hule_rem : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (2097152 - len)) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_rem : (BitVec.ofNat 64 (2097152 - len)).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false (by omega) (by omega)
  have hadd27 : BitVec.ofNat 64 n + BitVec.ofNat 64 len = BitVec.ofNat 64 (len + n) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hule_cap : (BitVec.ofNat 64 (len + n)).ule (BitVec.ofNat 64 cap) = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hult_cap : (BitVec.ofNat 64 cap).ult (BitVec.ofNat 64 (len + n)) = true :=
    bv64_ult_ofNat_true hgt_cap (by omega)
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := cliIoPl03.base + 292#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_r.readReg64 _).trans hx0
  have hx21_r' : sr'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_r.readReg64 _).trans hx21
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_r.readReg64 _).trans hx23
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_r.readReg64 _).trans hx26
  have hx28_r' : sr'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := (hcpu_r.readReg64 _).trans hx28
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun sg hcpu_g0 hcl_g hnsp_g hsym_g => ?_
  have hcpu_g := hcpu_g0.1
  have ⟨hacp_rg, hpp_rg⟩ :=
    allocCallPreserved_of_seg hcpu_r0 hcpu_g0 hnsp_g hsym_g
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hw19_g : (sg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_g.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_r.readReg64 (.gpr 19#5)]
    exact hw19
  exact hcont sg (hcpu_g.pc_eq.trans (by simp [arm64_norm])) (hcpu_g.status_eq.trans hrun_r')
    (hcpu_g.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx0_r'])
    hw19_g
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx21_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx25)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx26_r'])
    (by rw [hcpu_g.readReg64]; simp [arm64_norm])
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx28_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx29)
    (hcpu_g.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    hcl_g hacp_rg hpp_rg

/-- Step `+0xd8 .. +0xe4` and call `muslReadFileOrStdio32Spec` at `sp + 4096 = s0.sp - 4224#64`,
    landing at `+0xe8 = 232#64`. -/
private theorem cliIoReadFile_do_read [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    {s0 sl : State} {d0 : FdEntry} {fd sret ptr cap_bv : BitVec 64} {R_frame : SepProp}
    {len want stackBytes lb_cur lk_cur : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8352 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hwant_le : want ≤ 4096)
    (hoff_le : d0.offset + len + want ≤ Arm64.MAX_LFS_FILESIZE)
    (hkind : d0.kind = .localFile) (hcanr : d0.accMode.canRead = true)
    (hfs : sl.fs = s0.fs.setFd fd (some { d0 with offset := d0.offset + len }))
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sl.mem)
    (hpc : sl.pc = cliIoPl03.base + 216#64) (hrun : sl.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sl.sp = s0.sp - 8320#64)
    (hw19 : (sl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sl.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sl.readReg64 (.gpr 21#5) = cap_bv)
    (hx23 : sl.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sl.readReg64 (.gpr 24#5) = sret)
    (hx25 : sl.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sl.readReg64 (.gpr 26#5) = 2097152#64)
    (hx28 : sl.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sl.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sl = calleeSavedVRegs s0)
    (hcont : ∀ (sr : State) (oldBuf : List (BitVec 8)),
      let rem := (s0.fs.fdBytes d0).drop d0.offset
      let chunk := (rem.drop len).take want
      oldBuf.length = want →
      sr.pc = cliIoPl03.base + 232#64 → sr.status = .Running → sr.sp = s0.sp - 8320#64 →
      sr.readReg64 .x0 = BitVec.ofNat 64 chunk.length →
      (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sr.readReg64 (.gpr 20#5) = ptr →
      sr.readReg64 (.gpr 21#5) = cap_bv →
      sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want →
      sr.readReg64 (.gpr 24#5) = sret →
      sr.readReg64 (.gpr 25#5) = 4096#64 →
      sr.readReg64 (.gpr 26#5) = 2097152#64 →
      sr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sr.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs sr = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem →
      sr.fs = s0.fs.setFd fd (some { d0 with offset := d0.offset + (len + chunk.length) }) →
      sr.trace = sl.trace → sr.sigActions = sl.sigActions →
      sr.tpidrEl0 = sl.tpidrEl0 → sr.brkStart = sl.brkStart →
      SepWP P (s0.readReg64 .lr) sr
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
            memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want)) ∗
          R_frame ∗ A.pool lb_cur lk_cur sr)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sl
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        R_frame ∗ A.pool lb_cur lk_cur sl)
      post oomProp := by
  have hwant_toNat : (BitVec.ofNat 64 want).toNat = want := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  wp_conv_pre =>
    rw [memRegion_split_le (s0.sp - 4224#64) want 4096 hwant_le (by decide),
      memRegion_eq_exists_bytes (s0.sp - 4224#64) want (by omega)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro oldBuf
  wp_conv_pre =>
    rw [← sepConj_assoc (stackAt _ _), sepConj_comm (stackAt _ _) ⌜oldBuf.length = want⌝]
    simp only [sepConj_assoc]
  apply SepWP.pure_elim; intro hold_len
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
  have hx23_l' : sl'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_l.readReg64 _).trans hx23
  wp_sym_steps
  refine SepWP.done cliIoReadFile_read_pc (by simpa [arm64_norm] using hrun_l')
    fun sm_rd hcpu_rd0 hcl_rd hnsp_rd hsym_rd => ?_
  have hcpu_rd := hcpu_rd0.1
  have ⟨hacp_lrd, hpool_lrd⟩ :=
    allocCallPreserved_of_seg hcpu_l0 hcpu_rd0 hnsp_rd hsym_rd
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_lrd : A.pool lb_cur lk_cur sl = A.pool lb_cur lk_cur sm_rd :=
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
  have hx2_rd : sm_rd.readReg64 .x2 = BitVec.ofNat 64 want := by
    rw [hcpu_rd.readReg64 .x2]; simp [arm64_norm]
  have hfs_rd : sm_rd.fs = s0.fs.setFd fd (some { d0 with offset := d0.offset + len }) :=
    hacp_lrd.1.trans hfs
  have hfds_rd : sm_rd.fs.fds fd = some { d0 with offset := d0.offset + len } := by
    rw [hfs_rd]; simp [FsState.setFd]
  rw [hpool_eq_lrd]
  let d_cur : FdEntry := { d0 with offset := d0.offset + len }
  have hkind_or : (d_cur.kind == .localFile || d_cur.kind == .stdio) = true := by
    dsimp only [d_cur]; rw [hkind]; rfl
  apply seqCodeLoaded hcl_rd (mid := cliIoPl03.base + 232#64)
  apply (SepWP.call_subroutine_frame hread
    (x := (fd, s0.sp - 4224#64, BitVec.ofNat 64 want, d_cur, oldBuf))
    hpc_rd hrun_rd hsp_rd hlr_rd
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslReadFileOrStdio32Spec]
    rw [hsp_rd_eq, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_rd, hfd_lt, hx1_rd, hx2_rd,
      by rw [hwant_toNat]; simp only [Arm64.MAX_RW_COUNT]; omega,
      by rw [hwant_toNat]; exact sp_sub_4224_va_bound (by omega) hsp_va hwant_le,
      fun _ => by dsimp only [d_cur]; rw [hwant_toNat]; exact hoff_le,
      by rw [hwant_toNat]; exact hold_len, hfds_rd, hkind_or, hcanr⟩, ?_⟩
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 32 (by omega) (by omega)] at hm'
    exact Satisfies.mono (by sep_frame) hm'
  · intro sr hpc_sr hrun_sr hsp_sr hcs_rdsr
    refine SepWP.done hpc_sr hrun_sr fun hcl_sr => ?_
    wp_conv_pre => dsimp only [muslReadFileOrStdio32Spec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_sr, hfs_sr, htr_sr, hsys_sr⟩
    have hpool_eq_sr : A.pool lb_cur lk_cur sm_rd = A.pool lb_cur lk_cur sr :=
      (A.pool_transport _ _ sm_rd sr (poolPreserved_of_syscall hsys_sr)).symm
    have hchunk_eq :
        ((sm_rd.fs.fdBytes d_cur).drop d_cur.offset).take (BitVec.ofNat 64 want).toNat =
          (((s0.fs.fdBytes d0).drop d0.offset).drop len).take want := by
      rw [hfs_rd, hwant_toNat]
      dsimp only [FsState.setFd, FsState.fdBytes, FsState.files, FsState.getEntry, d_cur]
      rw [← List.drop_drop]
    have hfs_sr' : sr.fs = s0.fs.setFd fd
        (some { d0 with offset := d0.offset + (len + ((((s0.fs.fdBytes d0).drop d0.offset).drop len).take want).length) }) := by
      rw [hfs_sr, hchunk_eq, hfs_rd, FsState.setFd_setFd_same]
      dsimp only [d_cur]
      rw [Nat.add_assoc]
    have hsp_sr_eq : sr.sp = s0.sp - 8320#64 := hsp_sr.trans hsp_rd_eq
    have hw19_sr : (sr.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
      rw [readReg32_of_readReg64_eq hcs_rdsr.readReg64_x19,
        readReg32_of_readReg64_eq (hcpu_rd.readReg64 (.gpr 19#5))]
      simp only [arm64_norm]
      rw [hcpu_l.readReg64 (.gpr 19#5)]
      exact hw19
    refine SepWP.weaken_pre ?_
      (hcont sr oldBuf hold_len hpc_sr hrun_sr hsp_sr_eq
        (by rwa [hchunk_eq] at hx0_sr)
        hw19_sr
        (by rw [hcs_rdsr.readReg64_x20, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx20)
        (by rw [hcs_rdsr.readReg64_x21, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx21)
        (by rw [hcs_rdsr.readReg64_x23, hcpu_rd.readReg64]; simp only [arm64_norm]; exact hx23_l')
        (by rw [hcs_rdsr.readReg64_x24, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx24)
        (by rw [hcs_rdsr.readReg64_x25, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx25)
        (by rw [hcs_rdsr.readReg64_x26, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx26)
        (by rw [hcs_rdsr.readReg64_x28, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx28)
        (by rw [hcs_rdsr.readReg64_x29, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx29)
        (hcs_rdsr.vregs.trans (hcpu_rd.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs sl').trans (hcpu_l.calleeSavedVRegs.trans hvregs))))
        hcl_sr hfs_sr' (htr_sr.trans hacp_lrd.2.1) (hsys_sr.2.1.trans hacp_lrd.2.2.1)
        (hsys_sr.1.trans hacp_lrd.2.2.2.1) (hsys_sr.2.2.brkStart_eq.trans hacp_lrd.2.2.2.2.1))
    rw [hpool_eq_sr, hchunk_eq, hsp_rd_eq,
      stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 32 (by omega) (by omega)]
    sep_entail

/-- Full bounded `4096`-byte `read_file` `.localFile` loop from header `+0xd8 = 216#64` by strong
    induction on `fuel = cliIoFileCap + 1 - len`, including `close(fd)` restoring `sf.fs = s0.fs`. -/
theorem cliIoReadFile_file_loop [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
      stdMemcpySpec)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (allocFinishGrowSpec A)))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustStdDeallocSpec A))
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 : State} {d0 : FdEntry} {fd sret v0 v1 v2 : BitVec 64}
    {stackBytes lb lk : Nat}
    {post : State → SepProp → Prop}
    (hlo : 8368 + Rust.hookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hsp0 : s0.spAligned = true)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds_none : s0.fs.fds fd = none)
    (hkind : d0.kind = .localFile) (hcanr : d0.accMode.canRead = true) (hoff0 : d0.offset = 0)
    (hfits : AllocSeqFits A 1 lb lk (cliIoReadCaps 9 ((s0.fs.fdBytes d0).drop d0.offset).length))
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      sf.trace = s0.trace → sf.sigActions = s0.sigActions →
      sf.tpidrEl0 = s0.tpidrEl0 → sf.brkStart = s0.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ cliIoFileLoopResult A sret d0 lb lk s0 sf ∗
          StdErrnoCell s0.tpidrEl0) →
        post sf Pre_f) :
    ∀ (fuel : Nat) (sl : State) (ptr st0 st1 st2 st3 : BitVec 64) (cap len lb_cur lk_cur : Nat),
      cliIoFileCap + 1 - len ≤ fuel →
      len ≤ min ((s0.fs.fdBytes d0).drop d0.offset).length cliIoFileCap →
      (len < ((s0.fs.fdBytes d0).drop d0.offset).length → 4096 ∣ len) →
      cap = cliIoFinalCap 9 len →
      lb_cur = (allocSeqPool A 1 lb lk (cliIoReadCaps 9 len)).1 →
      lk_cur = (allocSeqPool A 1 lb lk (cliIoReadCaps 9 len)).2 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sl.mem →
      sl.pc = cliIoPl03.base + 216#64 → sl.status = .Running → sl.sp = s0.sp - 8320#64 →
      (sl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd → sl.readReg64 (.gpr 20#5) = ptr →
      sl.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sl.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 2097152 len) →
      sl.readReg64 (.gpr 24#5) = sret →
      sl.readReg64 (.gpr 25#5) = 4096#64 → sl.readReg64 (.gpr 26#5) = 2097152#64 →
      sl.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sl.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sl = calleeSavedVRegs s0 →
      sl.fs = s0.fs.setFd fd (some { d0 with offset := d0.offset + len }) →
      sl.trace = s0.trace → sl.sigActions = s0.sigActions →
      sl.tpidrEl0 = s0.tpidrEl0 → sl.brkStart = s0.brkStart →
      SepWP P (s0.readReg64 .lr) sl
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          ioVecBuf A (BitVec.ofNat 64 cap) ptr (((s0.fs.fdBytes d0).drop d0.offset).take len) ∗
          A.pool lb_cur lk_cur sl ∗ StdErrnoCell s0.tpidrEl0)
        post (cliIoFileOom oom fd d0 s0) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro sl ptr st0 st1 st2 st3 cap len lb_cur lk_cur
      hfuel hlen_le hdvd hcap_eq hlb_eq hlk_eq hcl hpc hrun hsp_eq
      hw19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hx29 hvregs
      hfs_sl htr_sl hsig_sl htp_sl hbs_sl
    let rem := (s0.fs.fdBytes d0).drop d0.offset
    have hrem_def : rem = (s0.fs.fdBytes d0).drop d0.offset := rfl
    let want := wantBytes 2097152 len
    have hwant_def : want = wantBytes 2097152 len := rfl
    have hcap2097 : cliIoFileCap = 2097152 := rfl
    have hlen_max : len ≤ cliIoFileCap := Nat.le_trans hlen_le (Nat.min_le_right _ _)
    have hlen_rem : len ≤ rem.length := Nat.le_trans hlen_le (Nat.min_le_left _ _)
    have hwant_le : want ≤ 4096 := wantBytes_le_4096 2097152 len
    let R_fr : SepProp :=
      memRegion (s0.sp - 8320#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        ioVecBuf A (BitVec.ofNat 64 cap) ptr (rem.take len) ∗ StdErrnoCell s0.tpidrEl0
    refine SepWP.weaken_pre (by dsimp only [R_fr]; sep_entail)
      (cliIoReadFile_do_read A hext3 hread (R_frame := R_fr) (by omega) hhi hsp_lo hsp_va hfd_lt hwant_le
        (by simp only [Arm64.MAX_LFS_FILESIZE, hoff0]; omega)
        hkind hcanr hfs_sl hcl hpc hrun hsp0 hsp_eq
        hw19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hx29 hvregs
        fun sr oldBuf hold_len hpc_sr hrun_sr hsp_sr hx0_sr hw19_sr hx20_sr hx21_sr hx23_sr
            hx24_sr hx25_sr hx26_sr hx28_sr hx29_sr hvregs_sr hcl_sr hfs_sr htr_sr hsig_sr
            htp_sr hbs_sr => ?_)
    dsimp only [R_fr]
    let chunk := (rem.drop len).take want
    have hchunk_def : chunk = (rem.drop len).take want := rfl
    have hn_min : chunk.length = min (rem.length - len) want := by
      rw [hchunk_def, List.length_take, List.length_drop, Nat.min_comm]
    have hn_le_want : chunk.length ≤ want := by rw [hn_min]; exact Nat.min_le_right _ _
    have hn_le_rem : len + chunk.length ≤ rem.length := by rw [hn_min]; omega
    let d_sr : FdEntry := { d0 with offset := d0.offset + (len + chunk.length) }
    have hfds_sr : sr.fs.fds fd = some d_sr := by
      rw [hfs_sr]; simp only [FsState.setFd, beq_self_eq_true, ↓reduceIte]; rfl
    have hkind_sr : d_sr.kind = .localFile ∨ d_sr.kind = .localDir := Or.inl hkind
    rcases Nat.eq_zero_or_pos chunk.length with hn0 | hn_pos
    · have hwant_pos : 0 < want := wantBytes_pos (by omega : len ≤ 2097152)
      have hlen_eq_rem : len = rem.length := by omega
      have hrem_le_cap : rem.length ≤ cliIoFileCap := by omega
      have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
      have htake_rem : rem.take len = rem := by rw [hlen_eq_rem, List.take_length]
      refine SepWP.weaken_pre ?_
        (cliIoReadFile_after_read_eof A hext3 hclose
          (v0 := v0) (v1 := v1) (v2 := v2)
          (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
          (lb_cur := lb_cur) (lk_cur := lk_cur)
          (by omega) hhi hfd_lt hfds_sr hkind_sr hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
          (by rw [hx0_sr, ← hchunk_def, hn0]) hw19_sr hx20_sr hx21_sr hx24_sr
          (by rw [hx28_sr, hlen_eq_rem]) hvregs_sr
          fun sf hpc_f hrun_f hsp_f hcs_f _ hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
            hpost sf hpc_f hrun_f hsp_f hcs_f
              (htr_f.trans (htr_sr.trans htr_sl))
              (hsig_f.trans (hsig_sr.trans hsig_sl))
              (htp_f.trans (htp_sr.trans htp_sl))
              (hbs_f.trans (hbs_sr.trans hbs_sl))
              (Entails.trans hent ?_))
      · rw [htake_rem]
        let Rest : SepProp :=
          stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 8320#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
            ioVecBuf A (BitVec.ofNat 64 cap) ptr rem ∗ A.pool lb_cur lk_cur sr ∗ StdErrnoCell s0.tpidrEl0
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono_left (Q := Rest) hbuf_back) (by dsimp only [Rest]; sep_entail))
        rw [← hrem_def, ← hchunk_def,
          pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
        dsimp only [Rest]; sep_entail
      · unfold cliIoFileLoopResult
        rw [← hrem_def]
        simp only [hrem_le_cap, ↓reduceIte]
        have hfs_eq : sf.fs = s0.fs := by
          rw [hfs_f, hfs_sr]; exact setFd_none_setFd_of_fds_none hfds_none
        rw [hcap_eq, hlb_eq, hlk_eq, hlen_eq_rem, pure_sepConj_of_true hfs_eq]
        have hex_ok : ioResultVecOk A sret (BitVec.ofNat 64 (cliIoFinalCap 9 rem.length)) ptr rem ⊢
            (∃∗ ptr' : BitVec 64,
              ioResultVecOk A sret (BitVec.ofNat 64 (cliIoFinalCap 9 rem.length)) ptr' rem) :=
          Entails.sepExists_right ptr (Entails.refl _)
        let RestOk : SepProp :=
          stackAt s0.sp stackBytes ∗
            A.pool (allocSeqPool A 1 lb lk (cliIoReadCaps 9 rem.length)).1
              (allocSeqPool A 1 lb lk (cliIoReadCaps 9 rem.length)).2 sf ∗
            StdErrnoCell s0.tpidrEl0
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono_left (Q := RestOk) hex_ok) (by dsimp only [RestOk]; sep_entail))
        dsimp only [RestOk]; sep_entail
    · by_cases hover : cliIoFileCap < len + chunk.length
      · have ⟨hlen_eq, hn_eq1, hrem_gt⟩ :=
          overCap_forces_eq_max (K := 9) hlen_le hdvd hn_min hn_pos hover
        have hwant_eq1 : want = 1 := by rw [hwant_def, hlen_eq]; rfl
        have hidx9 : cliIoCapIdx 9 len = 9 := by rw [hlen_eq]; exact cliIoCapIdx_cap_self 9
        have hcap9 : cap = cliIoCap 9 := by rw [hcap_eq, cliIoFinalCap_pos (by omega), hidx9]
        have hpool9 : allocSeqPool A 1 lb lk (cliIoReadCaps 9 len) =
            (lb + A.cost (cliIoCap 9) 1, lk + 1) := by
          rw [allocSeqPool_cliIoReadCaps_pos A (by omega), hidx9]
        have hlb9 : lb_cur = lb + A.cost (cliIoCap 9) 1 := by rw [hlb_eq, hpool9]
        have hlk9 : lk_cur = lk + 1 := by rw [hlk_eq, hpool9]
        have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
        refine SepWP.weaken_pre ?_
          (cliIoReadFile_after_read_overcap A hext3 hdealloc hclose
            (v0 := v0) (v1 := v1) (v2 := v2)
            (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (bs := rem.take len) (lb := lb) (lk := lk)
            (by omega) hhi hfd_lt hfds_sr hkind_sr hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            (by rw [hx0_sr, ← hchunk_def, hn_eq1]) hw19_sr hx20_sr
            (by rw [hx21_sr, hcap9]) (by rw [hx23_sr, hwant_eq1]) hx24_sr hx26_sr
            (by rw [hx28_sr, hlen_eq]; rfl) (htp_sr.trans htp_sl) hvregs_sr
            fun sf hpc_f hrun_f hsp_f hcs_f _ hfs_f htr_f hsig_f htp_f hbs_f _ hent =>
              hpost sf hpc_f hrun_f hsp_f hcs_f
                (htr_f.trans (htr_sr.trans htr_sl))
                (hsig_f.trans (hsig_sr.trans hsig_sl))
                (htp_f.trans (htp_sr.trans htp_sl))
                (hbs_f.trans (hbs_sr.trans hbs_sl))
                (Entails.trans hent ?_))
        · rw [hcap9, hlb9, hlk9]
          let Rest : SepProp :=
            stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ memRegion (s0.sp - 8320#64) 4096 ∗
              vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
              cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
              ioVecBuf A (BitVec.ofNat 64 (cliIoCap 9)) ptr (rem.take len) ∗
              A.pool (lb + A.cost (cliIoCap 9) 1) (lk + 1) sr ∗ StdErrnoCell s0.tpidrEl0
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono_left (Q := Rest) hbuf_back) (by dsimp only [Rest]; sep_entail))
          rw [← hrem_def, ← hchunk_def,
            pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
          dsimp only [Rest]; sep_entail
        · unfold cliIoFileLoopResult
          have hnot_le : ¬ rem.length ≤ cliIoFileCap := by omega
          rw [← hrem_def]
          simp only [hnot_le, ↓reduceIte]
          have hfs_eq : sf.fs = s0.fs := by
            rw [hfs_f, hfs_sr]; exact setFd_none_setFd_of_fds_none hfds_none
          rw [pure_sepConj_of_true hfs_eq]
          sep_entail
      · have hlen'_max : len + chunk.length ≤ cliIoFileCap := by omega
        have hlen'_le : len + chunk.length ≤ min rem.length cliIoFileCap :=
          Nat.le_min.mpr ⟨hn_le_rem, hlen'_max⟩
        have hdvd' : len + chunk.length < rem.length → 4096 ∣ (len + chunk.length) :=
          dvd_4096_preserved (K := 9) hlen_le hdvd hn_min hn_pos hlen'_max
        have hm_lt : cliIoFileCap + 1 - (len + chunk.length) < fuel := by omega
        by_cases hnogrow : len + chunk.length ≤ cap
        · have hlen_pos : 0 < len := by
            rcases Nat.eq_zero_or_pos len with rfl | hp
            · rw [cliIoFinalCap_zero] at hcap_eq; omega
            · exact hp
          let j := cliIoCapIdx 9 len
          have hj : j ≤ 9 := cliIoCapIdx_le 9 len
          have hcap_j : cap = cliIoCap j := by rw [hcap_eq, cliIoFinalCap_pos hlen_pos]
          have hcap_le_max : cap ≤ 2097152 := by rw [hcap_j]; exact cliIoCap_mono hj
          have hidx_eq : cliIoCapIdx 9 (len + chunk.length) = j :=
            no_grow_capIdx_eq hlen_pos (by omega) (by rwa [← hcap_j])
          have hcap'_eq : cap = cliIoFinalCap 9 (len + chunk.length) := by
            rw [cliIoFinalCap_pos (by omega), hidx_eq, hcap_j]
          have hpool_eq_idx :
              allocSeqPool A 1 lb lk (cliIoReadCaps 9 (len + chunk.length)) =
                allocSeqPool A 1 lb lk (cliIoReadCaps 9 len) := by
            rw [allocSeqPool_cliIoReadCaps_pos A (by omega), allocSeqPool_cliIoReadCaps_pos A hlen_pos, hidx_eq]
          refine cliIoReadFile_after_read_nogrow hext3 hn_pos hn_le_want hwant_le
            hnogrow hcap_le_max hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            hx0_sr hw19_sr hx20_sr hx21_sr hx23_sr hx24_sr hx25_sr hx26_sr hx28_sr hx29_sr hvregs_sr
            fun sc hpc_sc hrun_sc hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc hx24_sc hx25_sc
                hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_srsc hpp_srsc => ?_
          have hpool_srsc : A.pool lb_cur lk_cur sr = A.pool lb_cur lk_cur sc :=
            (A.pool_transport _ _ sr sc hpp_srsc).symm
          refine SepWP.weaken_pre (by rw [hpool_srsc]; sep_entail)
            (cliIoReadFile_memcpy_backedge A hext3 hmemcpy (R_path := memRegion (s0.sp - 8320#64) 4096)
              (by rw [hcap_j]; exact cliIoCap_pos j) (by rw [hcap_j]; exact cliIoCap_lt_pow63 (by omega))
              hn_le_rem hnogrow hlen'_max hwant_le hold_len hn_le_want rfl
              hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc hx24_sc
              hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc
              fun sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                  hx26_sn hx28_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                ih (cliIoFileCap + 1 - (len + chunk.length)) hm_lt sn ptr st0 st1 st2 st3
                  cap (len + chunk.length) lb_cur lk_cur (Nat.le_refl _)
                  hlen'_le hdvd' hcap'_eq
                  (by rw [hpool_eq_idx]; exact hlb_eq) (by rw [hpool_eq_idx]; exact hlk_eq)
                  hcl_sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                  hx26_sn hx28_sn hx29_sn hvregs_sn
                  (hmid_scsn.1.trans (hacp_srsc.1.trans hfs_sr))
                  (hmid_scsn.2.1.trans (hacp_srsc.2.1.trans (htr_sr.trans htr_sl)))
                  (hmid_scsn.2.2.1.trans (hacp_srsc.2.2.1.trans (hsig_sr.trans hsig_sl)))
                  (hmid_scsn.2.2.2.1.trans (hacp_srsc.2.2.2.1.trans (htp_sr.trans htp_sl)))
                  (hmid_scsn.2.2.2.2.trans (hacp_srsc.2.2.2.2.1.trans (hbs_sr.trans hbs_sl))))
        · have hgt_cap : cap < len + chunk.length := by omega
          refine cliIoReadFile_after_read_grow hext3 hn_pos hn_le_want hwant_le
            hgt_cap hlen'_max hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            hx0_sr hw19_sr hx20_sr hx21_sr hx23_sr hx24_sr hx25_sr hx26_sr hx28_sr hx29_sr hvregs_sr
            fun sg hpc_sg hrun_sg hsp_sg hx0_sg hw19_sg hx20_sg hx21_sg hx24_sg hx25_sg
                hx26_sg hx27_sg hx28_sg hx29_sg hvregs_sg hcl_sg hacp_srsg hpp_srsg => ?_
          have hpool_srsg : A.pool lb_cur lk_cur sr = A.pool lb_cur lk_cur sg :=
            (A.pool_transport _ _ sr sg hpp_srsg).symm
          have hfs_sg : sg.fs = s0.fs.setFd fd
              (some { d0 with offset := d0.offset + (len + chunk.length) }) :=
            hacp_srsg.1.trans hfs_sr
          have htr_sg : sg.trace = s0.trace := hacp_srsg.2.1.trans (htr_sr.trans htr_sl)
          have hsig_sg : sg.sigActions = s0.sigActions := hacp_srsg.2.2.1.trans (hsig_sr.trans hsig_sl)
          have htp_sg : sg.tpidrEl0 = s0.tpidrEl0 := hacp_srsg.2.2.2.1.trans (htp_sr.trans htp_sl)
          have hbs_sg : sg.brkStart = s0.brkStart := hacp_srsg.2.2.2.2.1.trans (hbs_sr.trans hbs_sl)
          have hoom_sg : ∀ (sm sf_oom : State),
              IoFrame sg sm → sm.fs = sg.fs → oom sm sf_oom → emp ⊢ cliIoFileOom oom fd d0 s0 sf_oom := by
            intro sm sf_oom hif hfs_m hoom_m
            unfold cliIoFileOom
            exact Entails.pure_right_only ⟨len + chunk.length, sm, hlen'_le,
              ⟨hif.1.trans htr_sg, hif.2.trans hsig_sg⟩, hfs_m.trans hfs_sg, hoom_m⟩ (Entails.refl _)
          let R_buf : SepProp :=
            memRegion (s0.sp - 8320#64) 4096 ∗
              (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
                memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want))
          rcases Nat.eq_zero_or_pos len with rfl | hlen_pos
          · have hcap0 : cap = 0 := hcap_eq
            subst hcap0
            have hlb0 : lb_cur = lb := hlb_eq
            have hlk0 : lk_cur = lk := hlk_eq
            have hcan0 : A.CanAlloc lb lk 4096 1 :=
              AllocSeqFits_canAlloc_zero (K := 9) (by omega : 0 < rem.length) hfits
            have hidx0 : cliIoCapIdx 9 chunk.length = 0 :=
              cliIoCapIdx_eq_of_bounds (Nat.zero_le 9) (Or.inl rfl) (Nat.le_trans hn_le_want hwant_le)
            have hpool0 : allocSeqPool A 1 lb lk (cliIoReadCaps 9 chunk.length) =
                (lb + A.cost (cliIoCap 0) 1, lk + 1) := by
              rw [allocSeqPool_cliIoReadCaps_pos A hn_pos, hidx0]
            refine SepWP.weaken_pre (by rw [hpool_srsg, hlb0, hlk0]; dsimp only [R_buf]; sep_entail)
              (cliIoReadFile_grow_from_zero A hext3 hfg (R_buf := R_buf) (by omega) hhi hn_pos
                (Nat.le_trans hn_le_want hwant_le) hcan0 hcl_sg hpc_sg hrun_sg hsp0 hsp_sg
                hx0_sg hw19_sg hx20_sg hx21_sg hx24_sg hx25_sg hx26_sg
                (by rw [Nat.zero_add] at hx27_sg; exact hx27_sg) hx28_sg hx29_sg htp_sg hvregs_sg hoom_sg
                fun sc newPtr st1' st2' hpc_sc hrun_sc hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc
                    hx24_sc hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_sgsc =>
                  SepWP.weaken_pre (by dsimp only [R_buf]; sep_entail)
                    (cliIoReadFile_memcpy_backedge A hext3 hmemcpy (R_path := memRegion (s0.sp - 8320#64) 4096)
                      (cliIoCap_pos 0) (cliIoCap_lt_pow63 (by decide))
                      hn_le_rem (Nat.le_trans (by rw [Nat.zero_add]; exact hn_le_want) hwant_le)
                      hlen'_max hwant_le hold_len hn_le_want rfl
                      hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc hx24_sc
                      hx25_sc hx26_sc (by rw [Nat.zero_add]; exact hx27_sc) hx28_sc hx29_sc hvregs_sc
                      fun sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                          hx26_sn hx28_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                        ih (cliIoFileCap + 1 - (0 + chunk.length)) hm_lt sn newPtr 0#64 st1' st2' st3
                          (cliIoCap 0) (0 + chunk.length) (lb + A.cost (cliIoCap 0) 1) (lk + 1)
                          (Nat.le_refl _) hlen'_le hdvd'
                          (by simp [cliIoFinalCap_pos hn_pos, hidx0])
                          (by simp [hpool0]) (by simp [hpool0])
                          hcl_sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn
                          hx25_sn hx26_sn hx28_sn hx29_sn hvregs_sn
                          (hmid_scsn.1.trans (hacp_sgsc.1.trans hfs_sg))
                          (hmid_scsn.2.1.trans (hacp_sgsc.2.1.trans htr_sg))
                          (hmid_scsn.2.2.1.trans (hacp_sgsc.2.2.1.trans hsig_sg))
                          (hmid_scsn.2.2.2.1.trans (hacp_sgsc.2.2.2.1.trans htp_sg))
                          (hmid_scsn.2.2.2.2.trans (hacp_sgsc.2.2.2.2.1.trans hbs_sg))))
          · let j := cliIoCapIdx 9 len
            have hj : j ≤ 9 := cliIoCapIdx_le 9 len
            have hcap_j : cap = cliIoCap j := by rw [hcap_eq, cliIoFinalCap_pos hlen_pos]
            have hlen_le_j : len ≤ cliIoCap j := le_cliIoCap_cliIoCapIdx hlen_max
            have ⟨hj1, hj1_r, hidx_j1, hle_j1, _⟩ :=
              grow_step_bounds (K := 9) (by decide) hj hlen_le_j
                (Nat.le_trans hn_le_want hwant_le) hn_le_rem hlen'_max (by rwa [← hcap_j])
            have hcan_succ : A.CanAlloc (lb + A.cost (cliIoCap j) 1) (lk + 1) (cliIoCap (j + 1)) 1 :=
              AllocSeqFits_canAlloc_succ (K := 9) (by omega : 0 < rem.length) hj1_r hfits
            have hpool_j : allocSeqPool A 1 lb lk (cliIoReadCaps 9 len) =
                (lb + A.cost (cliIoCap j) 1, lk + 1) :=
              allocSeqPool_cliIoReadCaps_pos A hlen_pos lb lk
            have hlb_j : lb_cur = lb + A.cost (cliIoCap j) 1 := by rw [hlb_eq, hpool_j]
            have hlk_j : lk_cur = lk + 1 := by rw [hlk_eq, hpool_j]
            have hpool_j1 : allocSeqPool A 1 lb lk (cliIoReadCaps 9 (len + chunk.length)) =
                (lb + A.cost (cliIoCap (j + 1)) 1, lk + 1) := by
              rw [allocSeqPool_cliIoReadCaps_pos A (by omega), hidx_j1]
            refine SepWP.weaken_pre (by rw [hpool_srsg, hcap_j, hlb_j, hlk_j]; dsimp only [R_buf]; sep_entail)
              (cliIoReadFile_grow_from_pos A hext3 hfg (R_buf := R_buf) (by omega) hhi hj1 hlen_le_j
                (List.length_take_of_le hlen_rem) (by rwa [← hcap_j]) hle_j1 hcan_succ
                hcl_sg hpc_sg hrun_sg hsp0 hsp_sg
                hx0_sg hw19_sg hx20_sg (by rw [hx21_sg, hcap_j]) hx24_sg hx25_sg
                hx26_sg hx27_sg hx28_sg hx29_sg htp_sg hvregs_sg hoom_sg
                fun sc newPtr st1' st2' hpc_sc hrun_sc hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc
                    hx24_sc hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_sgsc =>
                  SepWP.weaken_pre (by dsimp only [R_buf]; sep_entail)
                    (cliIoReadFile_memcpy_backedge A hext3 hmemcpy (R_path := memRegion (s0.sp - 8320#64) 4096)
                      (cliIoCap_pos (j + 1)) (cliIoCap_lt_pow63 (by omega))
                      hn_le_rem hle_j1 hlen'_max hwant_le hold_len hn_le_want rfl
                      hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hw19_sc hx20_sc hx22_sc hx23_sc hx24_sc
                      hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc
                      fun sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                          hx26_sn hx28_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                        ih (cliIoFileCap + 1 - (len + chunk.length)) hm_lt sn newPtr 0#64 st1' st2' st3
                          (cliIoCap (j + 1)) (len + chunk.length)
                          (lb + A.cost (cliIoCap (j + 1)) 1) (lk + 1)
                          (Nat.le_refl _) hlen'_le hdvd'
                          (by rw [cliIoFinalCap_pos (by omega), hidx_j1])
                          (by rw [hpool_j1]) (by rw [hpool_j1])
                          hcl_sn hpc_sn hrun_sn hsp_sn hw19_sn hx20_sn hx21_sn hx23_sn hx24_sn
                          hx25_sn hx26_sn hx28_sn hx29_sn hvregs_sn
                          (hmid_scsn.1.trans (hacp_sgsc.1.trans hfs_sg))
                          (hmid_scsn.2.1.trans (hacp_sgsc.2.1.trans htr_sg))
                          (hmid_scsn.2.2.1.trans (hacp_sgsc.2.2.1.trans hsig_sg))
                          (hmid_scsn.2.2.2.1.trans (hacp_sgsc.2.2.2.1.trans htp_sg))
                          (hmid_scsn.2.2.2.2.trans (hacp_sgsc.2.2.2.2.1.trans hbs_sg))))

end

end LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileLoop
