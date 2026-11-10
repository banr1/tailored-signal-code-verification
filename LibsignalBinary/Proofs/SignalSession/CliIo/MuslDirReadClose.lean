/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Proofs.SyscallProof
public import ProofLib

/-!
# Placement-Generic `musl` Directory `open` / `read` / `close` Contracts

Extends `VerifiedLibraries.Musl.SyscallProof` over `muslSysPlacedLib` with:
1. `muslClose48Local_block_ok` / `muslClose48Local_ok`: `close(fd)` (`48`-B stack frame) on an open
   `.localFile` or `.localDir` descriptor (`fd < 2 ^ 31`).
2. `muslReadDir32_block_ok` / `muslReadDir32_ok` (`muslReadDirEisdir32_*`): `read(fd, buf, count)`
   (`32`-B stack frame) on an open readable `.localDir` descriptor, returning `-1` with `errno = 21`
   (`EISDIR`) or `14` (`EFAULT` if `buf + count > USER_VA_LIMIT`).
3. `muslOpenNoCreatCloexecLocalExec_block_ok` / `muslOpenNoCreatCloexecLocalExec_ok` and
   `muslOpenDir_block_ok` / `muslOpenDir_ok`: `open(path, O_CLOEXEC)` (`112`-B stack frame) opening
   `.localFile` or `.localDir` descriptors.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open VerifiedLibraries.Musl (
  MuslSysPlacement muslSysPlacedLib muslSysMpl
  muslSysLib02 muslSysPl02 muslSysPC02
  muslSysLib03 muslSysPl03 muslSysPC03
  muslSysLib04 muslSysPl04 muslSysPC04
  muslSysLib05 muslSysPl05 muslSysPC05
  muslSysLib06 muslSysPl06 muslSysPC06
  muslSysLib08 muslSysPl08 muslSysPC08
  ValidCPath ValidRelCPath
  placed_program_rebase_self
  sxtw64_truncate32 ofNat64_toNat_of_lt63 ofNat64_le_maxSyscallOk
  CodeLoadedAt seq_codeLoaded_lr
  step_str64_perm_c step_stp64_perm step_str32_perm step_stp32_64_perm
  muslErrnoLocation_block_ok muslSyscallRetOk_block_ok muslSyscallRetErr_block_ok
  muslSysPC02_svc muslSysPC08_svc
)

/-! ## 1. Shared Internal Trampoline (`__syscall_cp` -> `sccp`) & `__aio_close` Helpers -/

theorem muslSyscallCp_step [MuslSysPlacement] {s0 : State} {target_pc : BitVec 64}
    {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s0.pc = muslSysPl03.base) (hrun : s0.status = .Running)
    (hcl : muslSysPlacedLib.CodeLoaded MuslSysPlacement.mpl s0.mem)
    (hnext : SepWP (muslSysPC02.rebase muslSysPl02.base (fun _ => none)) target_pc
      ((((((((s0.writeReg64 .x8 (s0.readReg64 .x0)).writeReg64 .x0 (s0.readReg64 .x1)).writeReg64
        .x1 (s0.readReg64 .x2)).writeReg64 .x2 (s0.readReg64 .x3)).writeReg64
        .x3 (s0.readReg64 .x4)).writeReg64 .x4 (s0.readReg64 .x5)).writeReg64
        .x5 (s0.readReg64 .x6)).setPC (muslSysPl02.base + 28#64)) P post) :
    SepWP (muslSysPC03.rebase muslSysPl03.base (fun _ => none)) target_pc s0 P post := by
  wp_sym_steps
  have hsccp : muslSysPl03.base + (muslSysPl03.ρ "sccp" - muslSysPl03.base) = muslSysPl02.base := by
    have hadd : muslSysPl03.base + (muslSysPl03.ρ "sccp" - muslSysPl03.base) = muslSysPl03.ρ "sccp" := by bv_omega
    have hl : Obj.lookupBlockSym "sccp" muslSysPlacedLib.blocks = some (2, 0) := by decide
    rw [hadd]
    simp [muslSysPl03, muslSysPl02, Obj.MultiPlacedLib.blockPlacement, Obj.MultiPlacedLib.resolve, hl]
  rw [hsccp]
  refine SepWP.of_sameHooks (P := muslSysPC03.rebase muslSysPl03.base (fun _ => none))
    (Q := muslSysPC02.rebase muslSysPl02.base (fun _ => none))
    (by intro pc
        change ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 2).rebase muslSysPl02.base (fun _ => none)).externAt? pc =
          ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 3).rebase muslSysPl03.base (fun _ => none)).externAt? pc
        simp)
    rfl ((hcl 2 (by decide)).of_base_code rfl rfl) ?_
  wp_sym_steps
  simpa [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8] using hnext

theorem resolve_syscall_cp [MuslSysPlacement] :
    muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp" = muslSysPl03.base := by
  have hl : Obj.lookupBlockSym "__syscall_cp" muslSysPlacedLib.blocks = some (3, 0) := by decide
  simp [Obj.MultiPlacedLib.resolve, hl, muslSysPl03, Obj.MultiPlacedLib.blockPlacement]

private def muslAioCloseSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = s0.readReg64 .x0 ∧ sf.mem = s0.mem ∧ StdStatePreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem muslAioClose_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC04.rebase muslSysPl04.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__aio_close")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslAioCloseSpec) := by
  have hentry : muslSysPlacedLib.resolve MuslSysPlacement.mpl "__aio_close" = muslSysPl04.base := by
    have hl : Obj.lookupBlockSym "__aio_close" muslSysPlacedLib.blocks = some (4, 0) := by decide
    simp [Obj.MultiPlacedLib.resolve, hl, muslSysPl04, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry; wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], by simp (disch := decide) [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
    by simpa using hmem⟩

private theorem state_setPC_eq_self {s : State} {pc : BitVec 64} (hpc : s.pc = pc) :
    s.setPC pc = s := by
  cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm

private theorem state_advancePC_eq_setPC {s : State} {pc : BitVec 64} (hpc : s.pc = pc) :
    s.advancePC = s.setPC (pc + 4#64) := by
  subst hpc; rfl

private theorem readReg32_slt_zero_false {w : BitVec 32} {fd : BitVec 64}
    (hfd : w.zeroExtend 64 = fd) (hlt : fd.toNat < 2 ^ 31) :
    w.slt 0#32 = false := by
  subst hfd
  have hw : w.toNat < 2 ^ 31 := by
    simpa [BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans w.isLt (by omega : 2 ^ 32 < 2 ^ 64))] using hlt
  unfold BitVec.slt BitVec.toInt
  simp; omega

@[local simp] private theorem muslErrnoAddr_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    muslErrnoAddr (s.writeReg64 r v) = muslErrnoAddr s := rfl
@[local simp] private theorem muslErrnoAddr_setPC (s : State) (pc : BitVec 64) :
    muslErrnoAddr (s.setPC pc) = muslErrnoAddr s := rfl
@[local simp] private theorem muslErrnoAddr_setMem (s : State) (m : Memory) :
    muslErrnoAddr (s.setMem m) = muslErrnoAddr s := rfl
@[local simp] private theorem muslErrnoAddr_setPState (s : State) (ps : PState) :
    muslErrnoAddr (s.setPState ps) = muslErrnoAddr s := rfl

/-! ## 2. `close` on `.localFile ∨ .localDir` (`muslClose48Local_block_ok` / `muslClose48Local_ok`) -/

/-- `SVC #0` rule for `close` (`X8 = 57`) closing an open `.localFile` or `.localDir` descriptor `fd`. -/
theorem step_svc_close_fd_local {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd : BitVec 64} {desc : FdEntry} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 57#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir)
    (hnext :
      let s' := ((s.setFs (s.fs.setFd fd none)).writeReg64 .x0 0#64).setPC (pc + 4#64)
      SepWP prog target_pc s' P post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execClose s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  have hslt : (s.readReg32 .x0).slt 0#32 = false := readReg32_slt_zero_false hfd hfd_lt
  have hk_false : (desc.kind != .localFile && desc.kind != .localDir) = false := by
    rcases hkind with hk | hk <;> (rw [hk]; rfl)
  refine SepWP.step_svc_close hpc hrun hfetch hx8 ?_ hsvc
  dsimp only [execClose]
  rw [hslt, hfd, hopen]; dsimp only
  rw [hk_false]; simp only [Bool.false_eq_true, ↓reduceIte]
  change SepWP prog target_pc
    (((s.setFs (s.fs.setFd fd none)).writeReg64 .x0 0#64).setPC (s.pc + 4#64)) P post oom
  rw [hpc]
  exact hnext

private def muslSccpCloseLocalSpec : Spec (BitVec 64 × FdEntry) where
  pre := fun (fd, desc) s0 =>
    ⌜s0.readReg64 .x0 = 57#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.fs.fds fd = some desc ∧
      (desc.kind = .localFile ∨ desc.kind = .localDir)⌝
  post := fun (fd, _) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
      sf.fs = s0.fs.setFd fd none ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem muslSccpCloseLocal_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC03.rebase muslSysPl03.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSccpCloseLocalSpec) := by
  rw [resolve_syscall_cp]; wp_entry
  refine muslSyscallCp_step hpc hrun h ?_
  refine step_svc_close_fd_local (fd := a_1) (desc := a_rest) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4 h_5 h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  dsimp only; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

/-- Contract for `int close(int fd)` (`blk05`, `48`-byte stack frame) on an open `.localFile` or
    `.localDir` descriptor (`fd < 2 ^ 31`). -/
def muslClose48LocalSpec : Spec (BitVec 64 × FdEntry) where
  pre := fun (fd, desc) s0 =>
    ⌜(s0.readReg32 .x0).zeroExtend 64 = fd ∧ fd.toNat < 2 ^ 31 ∧
      s0.fs.fds fd = some desc ∧ (desc.kind = .localFile ∨ desc.kind = .localDir)⌝ ∗
    stackAt s0.sp 48
  post := fun (fd, _) s0 sf =>
    ⌜sf.readReg32 .x0 = 0#32 ∧ sf.fs = s0.fs.setFd fd none ∧ sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝ ∗
    stackAt s0.sp 48
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslClose48Local_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 5)
      (muslSysPlacedLib.fnAddr muslSysMpl "close")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslClose48LocalSpec) := by
  rw [show muslSysPlacedLib.blockProgram muslSysMpl 5 =
    muslSysPC05.rebase muslSysPl05.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib05 muslSysPl05).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "close" = muslSysPl05.base := by
    have hl : Obj.lookupBlockSym "close" muslSysPlacedLib.blocks = some (5, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl05, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 32 2 (by decide)]
  cells_unfold; simp only [sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep muslAioClose_blk_ok ()
  rcases ‹StdStatePreserved _ _› with ⟨hfs1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at hfs1 htr1 htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block_keep muslSccpCloseLocal_blk_ok (a_1, a_rest)
  rcases ‹SyscallPreserved _ _› with ⟨htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at htp2 hsig2 hb2 hbs2 hp2 hmp2
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block muslSyscallRetOk_block_ok 0#64
  rcases ‹StdStatePreserved _ _› with ⟨hfs3, htr3, htp3, hsig3, hb3, hbs3, hp3, hmp3⟩
  simp only [wp_norm, arm64_norm, htp2, hsig2, hb2, hbs2, hp2, hmp2] at hfs3 htr3 htp3 hsig3 hb3 hbs3 hp3 hmp3
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
      by simp [wp_norm, arm64_norm, *], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
        stackAt_split_cells s0.sp 32 2 (by decide)]
      cells_unfold; simp only [wp_norm, arm64_norm, *]; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

theorem muslClose48Local_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "close")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslClose48LocalSpec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 5) (by decide) muslClose48Local_block_ok hext hsvc

/-! ## 3. `read` on `.localDir` (`muslReadDir32_block_ok` / `muslReadDir32_ok`) -/

/-- Exact `errno` (`Nat`) written by `musl` `read(fd, buf, count)` on a readable `.localDir`:
    `14` (`EFAULT`) if `buf + count > USER_VA_LIMIT`, else `21` (`EISDIR`). -/
def dirReadErrnoNat (buf count : BitVec 64) : Nat :=
  if buf.toNat + count.toNat > USER_VA_LIMIT then 14 else 21

/-- Exact 32-bit `errno` written by `musl` `read(fd, buf, count)` on a readable `.localDir`. -/
def dirReadErrno32 (buf count : BitVec 64) : BitVec 32 :=
  BitVec.ofNat 32 (dirReadErrnoNat buf count)

theorem dirReadErrnoNat_bounds (buf count : BitVec 64) :
    1 ≤ dirReadErrnoNat buf count ∧ dirReadErrnoNat buf count ≤ 4095 := by
  unfold dirReadErrnoNat
  by_cases h : buf.toNat + count.toNat > USER_VA_LIMIT <;> simp [h]

theorem dirReadErrno32_cases (buf count : BitVec 64) :
    dirReadErrno32 buf count = 21#32 ∨ dirReadErrno32 buf count = 14#32 := by
  unfold dirReadErrno32 dirReadErrnoNat
  by_cases h : buf.toNat + count.toNat > USER_VA_LIMIT <;> simp [h]

theorem dirReadErrno32_ne_eintr (buf count : BitVec 64) :
    dirReadErrno32 buf count ≠ 4#32 := by
  rcases dirReadErrno32_cases buf count with h | h <;> (rw [h]; decide)

theorem dirReadErrno32_eq_eisdir_of_le {buf count : BitVec 64}
    (hle : buf.toNat + count.toNat ≤ USER_VA_LIMIT) :
    dirReadErrno32 buf count = 21#32 := by
  have hnot : ¬(buf.toNat + count.toNat > USER_VA_LIMIT) := Nat.not_lt.mpr hle
  simp [dirReadErrno32, dirReadErrnoNat, hnot]

/-- `SVC #0` rule for `read` (`X8 = 63`) on an open readable `.localDir` descriptor `fd`. -/
theorem step_svc_read_dir {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd buf count : BitVec 64} {desc : FdEntry} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (_hx8 : s.readReg64 .x8 = 63#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hbuf : s.readReg64 .x1 = buf)
    (hcnt : s.readReg64 .x2 = count)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localDir)
    (hrd : desc.accMode.canRead = true)
    (hnext :
      let s' := (s.writeReg64 .x0 (-BitVec.ofNat 64 (dirReadErrnoNat buf count))).setPC (pc + 4#64)
      SepWP prog target_pc s' P post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execRead s := by
      simp [wp_norm, arm64_norm, Reg.x8, execRead, *]) :
    SepWP prog target_pc s P post oom := by
  have hpc_eq : s.setPC pc = s := state_setPC_eq_self hpc
  have hslt : (s.readReg32 .x0).slt 0#32 = false := readReg32_slt_zero_false hfd hfd_lt
  have hexec : execRead s =
      (s.writeReg64 .x0 (-BitVec.ofNat 64 (dirReadErrnoNat buf count))).setPC (pc + 4#64) := by
    have hk_dir : (FdKind.localDir == FdKind.localDir) = true := rfl
    refine Eq.trans ?_ (state_advancePC_eq_setPC hpc)
    dsimp only [execRead, execReadCommon, dirReadErrnoNat]
    rw [hslt, hfd, hbuf, hcnt, hopen]; dsimp only
    rw [hkind, hrd, hk_dir]
    by_cases hva : buf.toNat + count.toNat > USER_VA_LIMIT
    · simp [hva, EFAULT_RET]
    · simp [hva, EISDIR]
  exact SepWP.step_pure hpc hrun hfetch
    (by rw [hpc_eq, hsvc, hexec])
    (by cases s; rfl)
    hnext

private def muslSccpReadDirSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry) where
  pre := fun (fd, buf, count, desc) s0 =>
    ⌜s0.readReg64 .x0 = 63#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = count ∧
      s0.fs.fds fd = some desc ∧
      desc.kind = .localDir ∧
      desc.accMode.canRead = true⌝
  post := fun (_, buf, count, _) s0 sf =>
    ⌜sf.readReg64 .x0 = -BitVec.ofNat 64 (dirReadErrnoNat buf count) ∧
      sf.fs = s0.fs ∧
      sf.mem = s0.mem ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem muslSccpReadDir_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC03.rebase muslSysPl03.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSccpReadDirSpec) := by
  rw [resolve_syscall_cp]; wp_entry
  refine muslSyscallCp_step hpc hrun h ?_
  refine step_svc_read_dir (fd := a_1) (buf := a) (count := a_2) (desc := a_rest) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4
    (by simp [wp_norm, arm64_norm, h_5]) (by simp [wp_norm, arm64_norm, h_6])
    h_7 h_8 h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, execRead, h_2])
  dsimp only; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      rfl, by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
      by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

/-- Contract for `ssize_t read(int fd, void *buf, size_t count)` (`blk06`, `32`-byte stack frame +
    `muslErrnoAddr`) on an open readable `.localDir` descriptor (`fd < 2 ^ 31`), without any
    `buf` memory or `USER_VA_LIMIT` hypothesis. Returns `-1` and writes `dirReadErrno32 buf count`
    (`21#32` = `EISDIR`, or `14#32` = `EFAULT` if `buf + count > USER_VA_LIMIT`; never `4#32`). -/
def muslReadDir32Spec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × BitVec 32) where
  pre := fun (fd, buf, count, desc, e0) s0 =>
    ⌜(s0.readReg32 .x0).zeroExtend 64 = fd ∧ fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x1 = buf ∧ s0.readReg64 .x2 = count ∧
      s0.fs.fds fd = some desc ∧ desc.kind = .localDir ∧ desc.accMode.canRead = true⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun (_, buf, count, _, _) s0 sf =>
    ⌜sf.readReg64 .x0 = -1#64 ∧
      (dirReadErrno32 buf count = 21#32 ∨ dirReadErrno32 buf count = 14#32) ∧
      dirReadErrno32 buf count ≠ 4#32 ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ SyscallPreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr sf ↦₃₂ dirReadErrno32 buf count))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslReadDir32_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 6)
      (muslSysPlacedLib.fnAddr muslSysMpl "read")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslReadDir32Spec) := by
  rw [show muslSysPlacedLib.blockProgram muslSysMpl 6 =
    muslSysPC06.rebase muslSysPl06.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib06 muslSysPl06).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "read" = muslSysPl06.base := by
    have hl : Obj.lookupBlockSym "read" muslSysPlacedLib.blocks = some (6, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl06, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep muslSccpReadDir_blk_ok (a_1, a, a_2, a_3)
  rcases ‹SyscallPreserved _ sf› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  have htp_e : muslErrnoAddr s0 = muslErrnoAddr sf := by unfold muslErrnoAddr; rw [htp1]
  wp_conv_pre => rw [htp_e]
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗ (muslErrnoAddr sf ↦₃₂ a_rest_1))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have ⟨h1_err, h2_err⟩ := dirReadErrnoNat_bounds a a_2
  wp_call_block muslSyscallRetErr_block_ok (dirReadErrnoNat a a_2, a_rest_1)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · first | rw [satisfies_pure_sepConj] | rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], dirReadErrno32_cases a a_2,
      dirReadErrno32_ne_eintr a a_2, by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · simp only [dirReadErrno32, muslErrnoAddr, wp_norm, arm64_norm, *] at *; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

theorem muslReadDir32_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "read")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslReadDir32Spec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 6) (by decide) muslReadDir32_block_ok hext hsvc

/-- Specialized `read` contract on `.localDir` when `buf + count ≤ USER_VA_LIMIT` (`errno = 21#32` = `EISDIR`). -/
def muslReadDirEisdir32Spec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × BitVec 32) where
  pre := fun (fd, buf, count, desc, e0) s0 =>
    ⌜(s0.readReg32 .x0).zeroExtend 64 = fd ∧ fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x1 = buf ∧ s0.readReg64 .x2 = count ∧
      buf.toNat + count.toNat ≤ USER_VA_LIMIT ∧
      s0.fs.fds fd = some desc ∧ desc.kind = .localDir ∧ desc.accMode.canRead = true⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = -1#64 ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ SyscallPreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr sf ↦₃₂ 21#32))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslReadDirEisdir32_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 6)
      (muslSysPlacedLib.fnAddr muslSysMpl "read")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslReadDirEisdir32Spec) := by
  refine subroutine_ok_refine_entails muslReadDir32_block_ok ?_
  rintro ⟨fd, buf, count, desc, e0⟩ R s0 hpre
  simp only [MultiPlacedLib.withCodeLoaded, muslReadDirEisdir32Spec, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfd, hlt, hbuf, hcnt, hva, hopen, hk, hrd⟩, hm⟩
  refine ⟨(fd, buf, count, desc, e0), ?_, fun sf => ?_⟩
  · simp only [MultiPlacedLib.withCodeLoaded, muslReadDir32Spec, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨⟨hfd, hlt, hbuf, hcnt, hopen, hk, hrd⟩, hm⟩
  · simp only [MultiPlacedLib.withCodeLoaded, muslReadDir32Spec, muslReadDirEisdir32Spec,
      dirReadErrno32_eq_eisdir_of_le hva]
    exact sepConj_mono_left (Entails.pure_mono fun ⟨hx0, _, _, hfs, htr, hsp⟩ =>
      ⟨hx0, hfs, htr, hsp⟩)

theorem muslReadDirEisdir32_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "read")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslReadDirEisdir32Spec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 6) (by decide) muslReadDirEisdir32_block_ok hext hsvc

/-! ## 4. Local-FD (`.localFile ∨ .localDir`) & Directory `open` Contracts (`blk08`) -/

/-- Outcome characterization of `execOpenat` allowing both `.localFile` and `.localDir` opens. -/
inductive OpenatLocalOutcome where
  | ok (fd : BitVec 64) (desc : FdEntry) (fs' : FsState) (traceExtra : List TraceEvent)
  | err (errPred : Nat → Prop)

/-- Hypothesis asserting that `execOpenat` on `(AT_FDCWD, path, flags ||| O_LARGEFILE_W32)` from
    any state with filesystem `fs0` and trace `tr0` behaves according to `out` (with
    `desc.kind = .localFile ∨ desc.kind = .localDir` in `.ok`). -/
def OpenatLocalExecSpec (fs0 : FsState) (tr0 : List TraceEvent) (path : String)
    (flags : BitVec 32) (out : OpenatLocalOutcome) : Prop :=
  ∀ {s : State},
    readCString s.mem (s.readReg64 .x1) = .ok path →
    s.fs = fs0 →
    s.trace = tr0 →
    s.readReg32 .x0 = AT_FDCWD_W32 →
    s.readReg32 .x2 = flags ||| O_LARGEFILE_W32 →
    match out with
    | .ok fd desc fs' traceExtra =>
      fd.toNat < 2 ^ 31 ∧
      fs'.fds fd = some desc ∧
      (desc.kind = .localFile ∨ desc.kind = .localDir) ∧
      desc.cloexec = true ∧
      execOpenat s =
        (((s.setFs fs').appendTrace traceExtra).writeReg64 .x0 fd).advancePC
    | .err errPred =>
      ∃ errno : Nat,
        1 ≤ errno ∧ errno ≤ 4095 ∧ errPred errno ∧
        execOpenat s = (s.writeReg64 .x0 (-BitVec.ofNat 64 errno)).advancePC

private def muslSccpOpenatLocalExecSpec :
    Spec (BitVec 64 × String × BitVec 32 × FsState × List TraceEvent × OpenatLocalOutcome) where
  pre := fun (cstr, path, flags, fs0, tr0, out) s0 =>
    ⌜s0.readReg64 .x0 = 56#64 ∧
      s0.readReg32 .x1 = AT_FDCWD_W32 ∧
      s0.readReg64 .x2 = cstr ∧
      s0.readReg32 .x3 = flags ||| O_LARGEFILE_W32 ∧
      s0.fs = fs0 ∧
      s0.trace = tr0 ∧
      ValidCPath path ∧
      OpenatLocalExecSpec fs0 tr0 path flags out⌝ ∗
    (cstr ↦ₛ cstrBytes path)
  post := fun (cstr, path, _, fs0, tr0, out) s0 sf =>
    match out with
    | .ok fd desc fs' traceExtra =>
      ⌜sf.readReg64 .x0 = fd ∧
        fd.toNat < 2 ^ 31 ∧
        fs'.fds fd = some desc ∧
        (desc.kind = .localFile ∨ desc.kind = .localDir) ∧
        desc.cloexec = true ∧
        sf.fs = fs' ∧
        sf.mem = s0.mem ∧
        sf.trace = tr0 ++ traceExtra ∧
        SyscallPreserved s0 sf⌝ ∗
      (cstr ↦ₛ cstrBytes path)
    | .err errPred =>
      ∃∗ errno : Nat,
        ⌜sf.readReg64 .x0 = -BitVec.ofNat 64 errno ∧
          1 ≤ errno ∧ errno ≤ 4095 ∧ errPred errno ∧
          sf.fs = fs0 ∧
          sf.mem = s0.mem ∧
          sf.trace = tr0 ∧
          SyscallPreserved s0 sf⌝ ∗
        (cstr ↦ₛ cstrBytes path)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem muslSccpOpenatLocalExec_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC03.rebase muslSysPl03.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSccpOpenatLocalExecSpec) := by
  rw [resolve_syscall_cp]; wp_entry
  obtain ⟨hlen_p, hval_p⟩ := h_8
  refine muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine step_svc_openat_rw (path := a) (fname := a_1) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simp [wp_norm, arm64_norm, h_4])
    hlen_p hval_p (fun hcs => ?_)
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  rw [sepConj_emp]
  have hexec := h_1 hcs (by simp [wp_norm, arm64_norm, h_6]) (by simp [wp_norm, arm64_norm, h_7])
    (by simpa [wp_norm, arm64_norm] using h_3) (by simpa [wp_norm, arm64_norm] using h_5)
  cases a_rest with
  | ok fd desc fs' traceExtra =>
    dsimp only [OpenatLocalExecSpec] at hexec
    rcases hexec with ⟨hfd_lt, hfds, hkind, hclo, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [muslSccpOpenatLocalExecSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], hfd_lt, hfds, hkind, hclo,
        by simp [wp_norm, arm64_norm, State.appendTrace], rfl,
        by simp [wp_norm, arm64_norm, State.appendTrace, h_7], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [wp_norm, arm64_norm, State.appendTrace, calleeSavedVRegs]
  | err errPred =>
    dsimp only [OpenatLocalExecSpec] at hexec
    rcases hexec with ⟨errno, h1, h2, hpred, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [muslSccpOpenatLocalExecSpec]
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨errno, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], h1, h2, hpred,
        by simp [wp_norm, arm64_norm, h_6], rfl,
        by simp [wp_norm, arm64_norm, h_7], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem truncate32_and64 (x y : BitVec 64) :
    (x &&& y).truncate 32 = x.truncate 32 &&& y.truncate 32 := by ext i hi; simp

private theorem getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    fd.getLsbD 31 = false := by
  rw [BitVec.getLsbD]
  exact Nat.testBit_lt_two_pow hfd

private theorem truncate32_getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd.truncate 32).getLsbD 31 = false := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, getLsbD_31_false_of_lt hfd]; decide

private theorem mask32_or_zero_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 ||| 0#64) = fd := by
  simp only [BitVec.ushiftRight_zero, BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem setWidth64_setWidth32_and_mask_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.setWidth 32 fd) &&& 4294967295#64 = fd := by
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
  rw [h1]
  simpa [BitVec.ushiftRight_zero, BitVec.or_zero] using mask32_or_zero_of_lt31 hfd

private theorem sxtw64_eq_self_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 |||
      (if fd.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = fd := by
  rw [getLsbD_31_false_of_lt hfd]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_and, BitVec.or_zero, BitVec.ushiftRight_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem neg_ofNat_toNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).toNat = 2 ^ 64 - err := by
  rw [BitVec.toNat_neg, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).getLsbD 31 = true := by
  rw [BitVec.getLsbD, neg_ofNat_toNat h1 h2, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hdiv : (2 ^ 64 - err) / 2 ^ 31 = 2 ^ 33 - 1 := by omega
  rw [hdiv]; decide

private theorem truncate32_getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err).truncate 32).getLsbD 31 = true := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, getLsbD_31_neg_ofNat h1 h2]; decide

private theorem sxtw_neg_of_hi_ones {v : BitVec 64} (h : v >>> 32 = 0xffffffff#64) :
    (v >>> 0 &&& 4294967295#64 ||| 0xffffffffffffffff#64 &&& 0xffffffff00000000#64) = v := by
  bv_robdd

private theorem sxtw64_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err) >>> 0 &&& 4294967295#64 |||
      (if (-BitVec.ofNat 64 err).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = -BitVec.ofNat 64 err := by
  rw [getLsbD_31_neg_ofNat h1 h2]
  simp only [↓reduceIte]
  refine sxtw_neg_of_hi_ones (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_ushiftRight, neg_ofNat_toNat h1 h2, Nat.shiftRight_eq_div_pow]
  have hmax : (4294967295#64 : BitVec 64).toNat = 2 ^ 32 - 1 := by decide
  rw [hmax]; omega

private theorem zeroExtend64_getLsbD_6 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 6 = flags.getLsbD 6 := by simp

private theorem zeroExtend64_getLsbD_19 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 19 = flags.getLsbD 19 := by simp

private theorem tmpfile_mask_eq_zero {flags : BitVec 32} (h : flags &&& 0x00404000#32 = 0#32) :
    (flags &&& 0x007fc000#32) &&& 0xffc07fff#32 = 0#32 := by
  have heq : (flags &&& 0x007fc000#32) &&& 0xffc07fff#32 = flags &&& 0x00404000#32 := by bv_bits
  rw [heq, h]

private theorem or_largefile_sxtw_truncate32 (flags : BitVec 32) :
    (((flags.zeroExtend 64 ||| 131072#64) >>> 0 &&& 4294967295#64 |||
      (if (flags.zeroExtend 64 ||| 131072#64).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64).truncate 32) = flags ||| O_LARGEFILE_W32 := by
  rw [sxtw64_truncate32]
  change (flags.zeroExtend 64 ||| 131072#64).truncate 32 = flags ||| 0x00020000#32
  bv_bits

/-- Generic `execOpenat`-parameterized contract for `open(path, flags, mode)` (`blk08`, `112`-byte
    stack frame) on the non-`O_CREAT` path (`O_CREAT = 0`, not `O_TMPFILE`, `O_CLOEXEC = 1`),
    allowing both `.localFile` and `.localDir` descriptors. -/
def muslOpenNoCreatCloexecLocalExecSpec :
    Spec (BitVec 64 × String × BitVec 32 × BitVec 32 × OpenatLocalOutcome) where
  pre := fun (cstr, path, flags, e0, out) s0 =>
    ⌜s0.readReg64 .x0 = cstr ∧
      s0.readReg32 .x1 = flags ∧
      flags.getLsbD 6 = false ∧
      flags &&& 0x00404000#32 = 0#32 ∧
      flags.getLsbD 19 = true ∧
      ValidCPath path ∧
      OpenatLocalExecSpec s0.fs s0.trace path flags out⌝ ∗
    (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun (cstr, path, _, e0, out) s0 sf =>
    match out with
    | .ok fd _ fs' traceExtra =>
      ⌜sf.readReg32 .x0 = fd.truncate 32 ∧
        sf.fs = fs' ∧
        sf.trace = s0.trace ++ traceExtra ∧
        SyscallPreserved s0 sf⌝ ∗
      (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr sf ↦₃₂ e0))
    | .err errPred =>
      ∃∗ errno : Nat,
        ⌜1 ≤ errno ∧ errno ≤ 4095 ∧ errPred errno ∧
          sf.readReg32 .x0 = 0xffffffff#32 ∧
          sf.fs = s0.fs ∧
          sf.trace = s0.trace ∧
          SyscallPreserved s0 sf⌝ ∗
        (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr sf ↦₃₂ BitVec.ofNat 32 errno))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

set_option maxHeartbeats 400000 in
theorem muslOpenNoCreatCloexecLocalExec_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 8)
      (muslSysPlacedLib.fnAddr muslSysMpl "open")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslOpenNoCreatCloexecLocalExecSpec) := by
  rw [show muslSysPlacedLib.blockProgram muslSysMpl 8 =
    muslSysPC08.rebase muslSysPl08.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib08 muslSysPl08).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "open" = muslSysPl08.base := by
    have hl : Obj.lookupBlockSym "open" muslSysPlacedLib.blocks = some (8, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl08, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 112 = stackAt (s0.sp - 80#64) 32 ∗ cells (s0.sp - 80#64) 10 from
      stackAt_split_cells s0.sp 32 10 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  wp_stp64_perm hm1; wp_sym_steps 1; wp_str64_perm hm2; wp_sym_steps 1; wp_str64_perm hm3
  (conv => arg 3; simp only [wp_norm, arm64_norm, h_3, zeroExtend64_getLsbD_6, h_4])
  wp_sym_steps 3
  have htmp := tmpfile_mask_eq_zero h_5
  (conv => arg 3; simp only [wp_norm, arm64_norm, truncate32_and64, h_3, htmp])
  wp_sym_steps
  have hcwd : (-100#32 : BitVec 32) = AT_FDCWD_W32 := by decide
  have hflg := or_largefile_sxtw_truncate32 a_2
  have ⟨_, _⟩ := ‹ValidCPath a›
  wp_call_block_keep muslSccpOpenatLocalExec_blk_ok (a_1, a, a_2, s0.fs, s0.trace, a_rest_1)
  cases a_rest_1 with
  | ok fd desc fs' traceExtra =>
    wp_conv_pre => try dsimp only [muslSccpOpenatLocalExecSpec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨hx0, hfd_lt, hfds, hkind, hclo, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
    try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
    have hsvc08 : muslSysPC08.svc = Syscall.standard := rfl
    have hsxtw : (fd >>> 0 &&& 4294967295#64 |||
        (if fd.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
          0xffffffff00000000#64) = fd := sxtw64_eq_self_of_lt31 hfd_lt
    have hmask0 : (fd >>> 0 &&& 4294967295#64 ||| 0#64) = fd := mask32_or_zero_of_lt31 hfd_lt
    have hfd_ze_mask : BitVec.setWidth 64 (BitVec.setWidth 32 fd) &&& 4294967295#64 = fd :=
      setWidth64_setWidth32_and_mask_of_lt31 hfd_lt
    have hfd_ze : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
    have htbnz : fd.getLsbD 31 = false := getLsbD_31_false_of_lt hfd_lt
    have htbnz32 : (fd.truncate 32).getLsbD 31 = false := truncate32_getLsbD_31_false_of_lt hfd_lt
    wp_sym_steps 1
    (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, hmask0, htbnz, htbnz32])
    wp_sym_steps 2
    simp only [wp_norm, arm64_norm, zeroExtend64_getLsbD_19, h_6]
    have hdesc_eq : ({ desc with cloexec := true } : FdEntry) = desc := by
      cases desc; simp at hclo; subst hclo; rfl
    have hsetfd_eq : fs'.setFd fd (some { desc with cloexec := true }) = fs' := by
      rw [hdesc_eq]; exact FsState.setFd_eq_self hfds
    have h1_clo : (1#64 &&& 1#64 != 0#64) = true := by decide
    wp_sym_steps
    refine step_svc_fcntl_setfd_local (fd := fd) (arg := 1#64) rfl
      (by simp [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hfd_ze]) hfd_lt
      (by simp [wp_norm, arm64_norm, F_SETFD_W32]) (by simp [wp_norm, arm64_norm])
      (by simpa [wp_norm, arm64_norm, hfs1] using hfds) hkind ?_
      (by simp [wp_norm, arm64_norm, *])
    dsimp only
    (conv => arg 3; simp only [wp_norm, arm64_norm, hfs1, h1_clo, hsetfd_eq])
    wp_sym_steps
    have hfd_ok : fd.toNat ≤ 2 ^ 64 - 4096 := by omega
    wp_cut_codeLoaded
    wp_call_block muslSyscallRetOk_block_ok fd
    rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
    try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1]
      at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
    · try dsimp only [muslOpenNoCreatCloexecLocalExecSpec]
      try rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp_all [wp_norm, arm64_norm],
        by simp_all [wp_norm, arm64_norm], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
      · rw [show stackAt (State.sp s0) 112 =
            stackAt (State.sp s0 - 80#64) 32 ∗ cells (State.sp s0 - 80#64) 10 from
          stackAt_split_cells (State.sp s0) 32 10 (by decide)]
        cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]
  | err errPred =>
    wp_conv_pre => try dsimp only [muslSccpOpenatLocalExecSpec]; simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_left; intro errno
    apply SepWP.pure_elim
    rintro ⟨hx0, h1, h2, hpred, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
    try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
    have hsxtw : ((-BitVec.ofNat 64 errno) >>> 0 &&& 4294967295#64 |||
        (if (-BitVec.ofNat 64 errno).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
          0xffffffff00000000#64) = -BitVec.ofNat 64 errno := sxtw64_neg_ofNat h1 h2
    have htbnz : (-BitVec.ofNat 64 errno).getLsbD 31 = true := getLsbD_31_neg_ofNat h1 h2
    have htbnz32 : ((-BitVec.ofNat 64 errno).truncate 32).getLsbD 31 = true :=
      truncate32_getLsbD_31_neg_ofNat h1 h2
    have htp_e : muslErrnoAddr s0 = muslErrnoAddr sf := by unfold muslErrnoAddr; rw [htp1]
    wp_conv_pre => rw [htp_e]
    wp_cut_codeLoaded; wp_sym_steps 1
    (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, htbnz, htbnz32])
    wp_sym_steps
    wp_call_block muslSyscallRetErr_block_ok (errno, a_3)
    rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
    try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1]
      at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
    · try dsimp only [muslOpenNoCreatCloexecLocalExecSpec]
      try rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨errno, ?_⟩
      try rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨h1, h2, hpred, by simp [wp_norm, arm64_norm, *],
        by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *], ?_⟩,
        ProofLib.Satisfies.of_entails hmem ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
      · rw [show stackAt (State.sp s0) 112 =
            stackAt (State.sp s0 - 80#64) 32 ∗ cells (State.sp s0 - 80#64) 10 from
          stackAt_split_cells (State.sp s0) 32 10 (by decide)]
        cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

theorem muslOpenNoCreatCloexecLocalExec_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "open")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslOpenNoCreatCloexecLocalExecSpec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 8) (by decide)
    muslOpenNoCreatCloexecLocalExec_block_ok hext hsvc

/-- Pure `execOpenat` characterization when `path` resolves to an existing `.dir` (`ancestorWalkErrno? = none`). -/
theorem execOpenat_rdonly_cloexec_dir {s : State} {path : String} {fd : BitVec 64}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hdir : s.fs.files path = some .dir)
    (halloc : s.fs.allocFd = some fd) :
    execOpenat s =
      ((s.setFs (s.fs.setFd fd (some
          { path := path, accMode := .rdonly, append := false, cloexec := true,
            offset := 0, kind := .localDir }))).writeReg64 .x0 fd).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_m0 : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32 == 0#32) = true := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hf_ex : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_EXCL_W32 != 0#32) = false := by decide
  have hf_tr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_TRUNC_W32 != 0#32) = false := by decide
  have hf_ap : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_APPEND_W32 != 0#32) = false := by decide
  have hf_dr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_DIRECTORY_W32 != 0#32) = false := by decide
  have hf_cl : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CLOEXEC_W32 != 0#32) = true := by decide
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  have hge : s.fs.getEntry (normalizePath path) = some .dir := hdir
  have hsanc : strictAncestorWalkErrno? s.fs path = none ∧
      ((splitSlash path).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) = false := by
    unfold ancestorWalkErrno? at hanc
    unfold strictAncestorWalkErrno?
    dsimp only at hanc
    cases hw : ancestorWalkErrno?.walk s.fs [] ((splitSlash path).filter (!·.isEmpty)).dropLast with
    | some _ => rw [hw] at hanc; cases hanc
    | none =>
      rw [hw] at hanc
      cases hl : ((splitSlash path).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) with
      | true => rw [hl] at hanc; cases hanc
      | false => exact ⟨rfl, rfl⟩
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_m0, hf_cr, hf_ex, hf_tr, hf_ap, hf_dr, hf_cl, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  have hrd_ne : (FdAccessMode.rdonly != FdAccessMode.rdonly) = false := rfl
  rw [hres, hsanc.1]
  dsimp only
  rw [hsanc.2]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge, hrd_ne, halloc]
  simp

private theorem setFs_appendTrace_nil (s : State) (fs' : FsState) :
    (s.setFs fs').appendTrace [] = s.setFs fs' := by
  cases s; simp [State.setFs, State.appendTrace]

/-- Concrete contract for `int open(const char *path, O_CLOEXEC, mode)` (`blk08`, `112`-byte stack
    frame) opening an existing directory (`s0.fs.files path = some .dir`, `ancestorWalkErrno? = none`)
    as a `.localDir` descriptor (`fd < 2 ^ 31`). -/
def muslOpenDirSpec (fd : BitVec 64 := 3#64) : Spec (BitVec 64 × String × BitVec 32) where
  pre := fun (cstr, path, e0) s0 =>
    ⌜s0.readReg64 .x0 = cstr ∧
      s0.readReg32 .x1 = O_CLOEXEC_W32 ∧
      ValidRelCPath path ∧
      path.isEmpty = false ∧
      ancestorWalkErrno? s0.fs path = none ∧
      s0.fs.files path = some .dir ∧
      s0.fs.allocFd = some fd ∧
      fd.toNat < 2 ^ 31⌝ ∗
    (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun (cstr, path, e0) s0 sf =>
    ⌜sf.readReg32 .x0 = fd.truncate 32 ∧
      sf.fs = s0.fs.setFd fd
        (some { path := path, accMode := .rdonly, append := false, cloexec := true,
                offset := 0, kind := .localDir }) ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝ ∗
    (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr sf ↦₃₂ e0))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslOpenDir_block_ok [MuslSysPlacement] (fd : BitVec 64 := 3#64) :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 8)
      (muslSysPlacedLib.fnAddr muslSysMpl "open")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl (muslOpenDirSpec fd)) := by
  refine subroutine_ok_refine_entails muslOpenNoCreatCloexecLocalExec_block_ok ?_
  rintro ⟨cstr, path, e0⟩ R s0 hpre
  simp only [MultiPlacedLib.withCodeLoaded, muslOpenDirSpec, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, ⟨hcp, hlead, hdot⟩, hne, hanc, hdir, halloc, hfd_lt⟩, hm⟩
  have hb6 : O_CLOEXEC_W32.getLsbD 6 = false := by decide
  have htmp : O_CLOEXEC_W32 &&& 0x00404000#32 = 0#32 := by decide
  have hb19 : O_CLOEXEC_W32.getLsbD 19 = true := by decide
  have hfl_eq : O_CLOEXEC_W32 ||| O_LARGEFILE_W32 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32 := by decide
  let desc : FdEntry :=
    { path := path, accMode := .rdonly, append := false, cloexec := true,
      offset := 0, kind := .localDir }
  let fs' : FsState := s0.fs.setFd fd (some desc)
  refine ⟨(cstr, path, O_CLOEXEC_W32, e0, .ok fd desc fs' []), ?_, fun sf => ?_⟩
  · simp only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecLocalExecSpec, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hb6, htmp, hb19, hcp, ?_⟩, hm⟩
    intro s hcs hs_fs _ hs_x0 hs_x2
    have hexec := execOpenat_rdonly_cloexec_dir hs_x0 (hfl_eq ▸ hs_x2) hcs hne hlead hdot
      (hs_fs.symm ▸ hanc) (hs_fs.symm ▸ hdir) (hs_fs.symm ▸ halloc)
    rw [hs_fs] at hexec
    refine ⟨hfd_lt, by simp [fs', FsState.setFd], Or.inr rfl, rfl, ?_⟩
    rw [setFs_appendTrace_nil]
    exact hexec
  · simp only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecLocalExecSpec,
      muslOpenDirSpec, List.append_nil]
    exact Entails.refl _

theorem muslOpenDir_ok [MuslSysPlacement] {P : Program} (fd : BitVec 64 := 3#64)
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "open")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl (muslOpenDirSpec fd)) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 8) (by decide) (muslOpenDir_block_ok fd) hext hsvc

end LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose
