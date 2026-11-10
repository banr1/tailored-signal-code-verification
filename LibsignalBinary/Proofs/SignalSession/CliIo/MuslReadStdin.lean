/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Proofs.SyscallProof
public import ProofLib
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose

/-!
# Placement-Generic `musl` `read` Contract for `stdin` and `.localFile ∨ .stdio`

Extends `VerifiedLibraries.Musl.SyscallProof` over `muslSysPlacedLib` with:
1. `muslReadFileOrStdio32_block_ok` / `muslReadFileOrStdio32_ok`: `read(fd, buf, count)` (`blk06`,
   `32`-B stack frame) on any open readable `.localFile` or `.stdio` descriptor (`fd < 2 ^ 31`).
2. `muslReadStdin32_block_ok` / `muslReadStdin32_ok`: specialization for `fd = 0#64` (`stdin`),
   reading `(s0.fs.stdin.drop desc.offset).take count.toNat` into `buf` and advancing `desc.offset`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open VerifiedLibraries.Musl (
  MuslSysPlacement muslSysPlacedLib muslSysMpl
  muslSysPl02 muslSysPC02
  muslSysPl03 muslSysPC03
  muslSysLib06 muslSysPl06 muslSysPC06
  placed_program_rebase_self
  ofNat64_le_maxSyscallOk
  CodeLoadedAt seq_codeLoaded_lr
  step_stp64_perm
  muslSyscallRetOk_block_ok
  muslSysPC02_svc
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (
  muslSyscallCp_step resolve_syscall_cp
)

/-! ## 1. Internal `sccp` Trampoline for `.localFile ∨ .stdio` `read` (`X8 = 63`) -/

private def muslSccpReadFileOrStdioSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, count, desc, oldBuf) s0 =>
    ⌜s0.readReg64 .x0 = 63#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = count ∧
      count.toNat ≤ Arm64.MAX_RW_COUNT ∧
      buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      (desc.kind = .localFile → desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE) ∧
      oldBuf.length = count.toNat ∧
      s0.fs.fds fd = some desc ∧
      (desc.kind == .localFile || desc.kind == .stdio) = true ∧
      desc.accMode.canRead = true⌝ ∗
    (buf ↦ₛ oldBuf)
  post := fun (fd, buf, count, desc, oldBuf) s0 sf =>
    let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take count.toNat
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧
      sf.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝ ∗
    (buf ↦ₛ (chunk ++ oldBuf.drop chunk.length))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem muslSccpReadFileOrStdio_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC03.rebase muslSysPl03.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSccpReadFileOrStdioSpec) := by
  rw [resolve_syscall_cp]; wp_entry
  refine muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine SepWP.step_svc_read (fd := a_1) (buf := a) (count := a_2) (desc := a_3) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x0 = 63#64›])
    (by simpa [wp_norm, arm64_norm] using ‹(s0.readReg32 .x1).zeroExtend 64 = a_1›)
    ‹a_1.toNat < 2 ^ 31›
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x2 = a›])
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x3 = a_2›])
    ‹a_rest_1.length = a_2.toNat›
    ‹s0.fs.fds a_1 = some a_3›
    ‹(a_3.kind == .localFile || a_3.kind == .stdio) = true›
    ‹a_3.accMode.canRead = true› ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, execRead, ‹s0.readReg64 .x0 = 63#64›])
    ‹a_2.toNat ≤ Arm64.MAX_RW_COUNT›
    ‹a.toNat + a_2.toNat ≤ Arm64.USER_VA_LIMIT›
    ‹a_3.kind = .localFile → a_3.offset + a_2.toNat ≤ Arm64.MAX_LFS_FILESIZE›
  dsimp only; rw [sepConj_emp]
  (conv => arg 3; simp only [wp_norm, arm64_norm])
  (conv => arg 4; simp only [wp_norm, arm64_norm, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8])
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by cases a_3; simp_all [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp [wp_norm, arm64_norm]⟩, by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

/-! ## 2. Unified `muslReadFileOrStdio32` Contract (`blk06`, `32`-byte stack frame) -/

/-- Contract for `ssize_t read(int fd, void *buf, size_t count)` (`blk06`, `32`-byte stack frame)
    on an open readable `.localFile` or `.stdio` descriptor (`fd < 2 ^ 31`, `count < 2 ^ 63`). -/
def muslReadFileOrStdio32Spec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, count, desc, oldBuf) s0 =>
    ⌜(s0.readReg32 .x0).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x1 = buf ∧
      s0.readReg64 .x2 = count ∧
      count.toNat ≤ Arm64.MAX_RW_COUNT ∧
      buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      (desc.kind = .localFile → desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE) ∧
      oldBuf.length = count.toNat ∧
      s0.fs.fds fd = some desc ∧
      (desc.kind == .localFile || desc.kind == .stdio) = true ∧
      desc.accMode.canRead = true⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ₛ oldBuf))
  post := fun (fd, buf, count, desc, oldBuf) s0 sf =>
    let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take count.toNat
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧
      sf.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ₛ (chunk ++ oldBuf.drop chunk.length)))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslReadFileOrStdio32_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 6)
      (muslSysPlacedLib.fnAddr muslSysMpl "read")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslReadFileOrStdio32Spec) := by
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
  wp_call_block_keep muslSccpReadFileOrStdio_blk_ok (a_1, a, a_2, a_3, a_rest_1)
  rcases ‹SyscallPreserved _ _› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗
    (a ↦ₛ (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat ++
      a_rest_1.drop (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length)))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have hchunk_lt : (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length < 2 ^ 63 := by
    simp only [List.length_take]
    have := ‹a_2.toNat ≤ Arm64.MAX_RW_COUNT›
    simp only [Arm64.MAX_RW_COUNT] at this
    omega
  have hchunk_ok := ofNat64_le_maxSyscallOk hchunk_lt
  wp_call_block muslSyscallRetOk_block_ok
    (BitVec.ofNat 64 (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1]
    at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · first | rw [satisfies_pure_sepConj] | rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], ?_, by simp [wp_norm, arm64_norm, *], ?_⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    · simp_all [wp_norm, arm64_norm]
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm] at *; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

theorem muslReadFileOrStdio32_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "read")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslReadFileOrStdio32Spec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 6) (by decide) muslReadFileOrStdio32_block_ok
    hext hsvc

/-! ## 3. Concrete `stdin` (`fd = 0`) Specialization (`muslReadStdin32_block_ok` / `muslReadStdin32_ok`) -/

/-- Contract for `ssize_t read(0, void *buf, size_t count)` (`blk06`, `32`-byte stack frame)
    on an open readable `.stdio` `stdin` descriptor (`fd = 0`, `count < 2 ^ 63`). -/
def muslReadStdin32Spec : Spec (BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (buf, count, desc, oldBuf) s0 =>
    ⌜s0.readReg32 .x0 = 0#32 ∧
      s0.readReg64 .x1 = buf ∧
      s0.readReg64 .x2 = count ∧
      count.toNat ≤ Arm64.MAX_RW_COUNT ∧
      buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      oldBuf.length = count.toNat ∧
      s0.fs.fds 0#64 = some desc ∧
      desc.kind = .stdio ∧
      desc.accMode.canRead = true⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ₛ oldBuf))
  post := fun (buf, count, desc, oldBuf) s0 sf =>
    let chunk := (s0.fs.stdin.drop desc.offset).take count.toNat
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧
      sf.fs = s0.fs.setFd 0#64 (some { desc with offset := desc.offset + chunk.length }) ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (buf ↦ₛ (chunk ++ oldBuf.drop chunk.length)))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem muslReadStdin32_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 6)
      (muslSysPlacedLib.fnAddr muslSysMpl "read")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslReadStdin32Spec) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨buf, count, desc, oldBuf⟩ R s0 hpc hrun hpre hsp _hL
  simp only [MultiPlacedLib.withCodeLoaded, muslReadStdin32Spec, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hcnt_le, hva_le, hlen, hfds0, hkind, hrd⟩, hm⟩
  have hx0_ze : (s0.readReg32 .x0).zeroExtend 64 = 0#64 := by rw [hx0]; rfl
  have h0_lt : (0#64 : BitVec 64).toNat < 2 ^ 31 := by decide
  have hk_or : (desc.kind == .localFile || desc.kind == .stdio) = true := by rw [hkind]; rfl
  have hlfs : desc.kind = .localFile → desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE := by
    rw [hkind]; intro h; cases h
  have hfdbytes : s0.fs.fdBytes desc = s0.fs.stdin := by simp [FsState.fdBytes, hkind]
  refine muslReadFileOrStdio32_block_ok.mono_outcome (0#64, buf, count, desc, oldBuf) R s0 hpc hrun
    ?_ hsp (fun sf hout => ?_)
  · simp only [MultiPlacedLib.withCodeLoaded, muslReadFileOrStdio32Spec, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨⟨hx0_ze, h0_lt, hx1, hx2, hcnt_le, hva_le, hlfs, hlen, hfds0, hk_or, hrd⟩, hm⟩
  · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [MultiPlacedLib.withCodeLoaded, muslReadFileOrStdio32Spec, muslReadStdin32Spec,
        hfdbytes] using hq
    · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))

theorem muslReadStdin32_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "read")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslReadStdin32Spec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 6) (by decide) muslReadStdin32_block_ok hext hsvc

theorem sp_sub_4224_va_bound {sp : BitVec 64} {want : Nat}
    (hlo : 4224 ≤ sp.toNat) (hhi : sp.toNat ≤ Arm64.USER_VA_LIMIT) (hw : want ≤ 4096) :
    (sp - 4224#64).toNat + want ≤ Arm64.USER_VA_LIMIT := by
  have h64 := sp.isLt
  have hLim : Arm64.USER_VA_LIMIT = 2 ^ 48 := rfl
  rw [BitVec.toNat_sub]
  change (2 ^ 64 - 4224 + sp.toNat) % 2 ^ 64 + want ≤ Arm64.USER_VA_LIMIT
  have h1 : 2 ^ 64 - 4224 + sp.toNat = 2 ^ 64 + (sp.toNat - 4224) := by omega
  rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  omega

end LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin
