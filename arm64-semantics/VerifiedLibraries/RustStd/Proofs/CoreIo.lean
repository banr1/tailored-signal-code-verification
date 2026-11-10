/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.Sym
public import VerifiedLibraries.Musl.Proofs.SyscallProof
public import VerifiedLibraries.Musl.Proofs.MemOps
public import ProofLib
public meta import ProofLib.ProgramReflection

/-!
# Placement-Generic Rust `std` Core and I/O Helper Proofs

Proves placement-generic subroutine contracts over `[RustStdPlacement]` for
`std::sys::io::error::unix::is_interrupted` (`rustStdPC00`) and
`<std::io::stdio::Stderr as std::io::Write>::write_all` (`rustStdPC04`), together with
the 16-byte SWAR interior-NUL scan lemmas (`rustRunWithCstr_nul_scan`) for
`run_with_cstr_allocating::<File>` (`rustStdPC02`).
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib VerifiedLibraries.Musl ProofLib.ProgramReflection ProofLib.StdStartup

section
arm64_proof_prelude

/-! ## Low-Level `musl` and Outline-Atomics Call Bundle -/

/-- Bundle of low-level `musl` syscall, memory, and outline-atomics contracts called by
    `rustStdPlacedLib` routines on program `P`. -/
structure RustLowLevelIoContracts (P : Program) [RustStdPlacement] (fd : BitVec 64 := 3#64) : Prop where
  cas4Acq_ok :
    subroutine_ok P (rustStdPlacedLib.resolve rustStdMpl "__aarch64_cas4_acq")
      (rustStdPlacedLib.withCodeLoaded rustStdMpl
        (stdCas4Spec (rustStdPlacedLib.resolve rustStdMpl "__aarch64_have_lse_atomics")))
  swp4Rel_ok :
    subroutine_ok P (rustStdPlacedLib.resolve rustStdMpl "__aarch64_swp4_rel")
      (rustStdPlacedLib.withCodeLoaded rustStdMpl
        (stdSwp4Spec (rustStdPlacedLib.resolve rustStdMpl "__aarch64_have_lse_atomics")))
  writeStderr_ok :
    subroutine_ok P (rustStdPlacedLib.resolve rustStdMpl "write")
      (rustStdPlacedLib.withCodeLoaded rustStdMpl muslWriteStderr32Spec)
  errnoLocation_ok :
    subroutine_ok P (rustStdPlacedLib.resolve rustStdMpl "___errno_location")
      (rustStdPlacedLib.withCodeLoaded rustStdMpl muslErrnoLocationSpec)
  openRdonly_ok :
    subroutine_ok P (rustStdPlacedLib.resolve rustStdMpl "open")
      (rustStdPlacedLib.withCodeLoaded rustStdMpl (muslOpenRdonlySpec fd))
  openCreateTrunc_ok :
    subroutine_ok P (rustStdPlacedLib.resolve rustStdMpl "open")
      (rustStdPlacedLib.withCodeLoaded rustStdMpl (muslOpenCreateTruncSpec fd))
  read_ok :
    subroutine_ok P (rustStdPlacedLib.resolve rustStdMpl "read")
      (rustStdPlacedLib.withCodeLoaded rustStdMpl muslRead32Spec)
  memcpy_ok :
    subroutine_ok P (rustStdPlacedLib.resolve rustStdMpl "memcpy")
      (rustStdPlacedLib.withCodeLoaded rustStdMpl stdMemcpySpec)

theorem rustFnAddr_eq_base [RustStdPlacement] (j : Nat) (sym : String)
    (hj : j < rustStdPlacedLib.blocks.length)
    (hl : lookup sym rustStdPlacedLib.blocks[j].symbols = some 0) :
    rustStdPlacedLib.fnAddr rustStdMpl sym = rustStdMpl.base j :=
  fnAddr_eq_base RustStdPlacement.placeable j sym hj hl

/-! ## `std::sys::io::error::unix::is_interrupted` -/

/-- Contract for `is_interrupted(errno: i32) -> bool` (`rustStdPC00`, `isInterruptedSym`):
    returns `1` when `w0 == 4` (`EINTR`) and `0` otherwise, leaving memory and OS state unchanged. -/
def rustIsInterruptedSpec : Spec (BitVec 32) where
  pre := fun err s0 =>
    ⌜s0.readReg32 .x0 = err⌝
  post := fun err s0 sf =>
    ⌜sf.readReg64 .x0 = (if err == 4#32 then 1#64 else 0#64) ∧
      sf.readReg32 .x0 = (if err == 4#32 then 1#32 else 0#32) ∧
      sf.mem = s0.mem ∧
      StdStatePreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Block-program contract for `is_interrupted` (`rustStdPlacedLib.blockProgram rustStdMpl 0`),
    directly compatible with `wp_call_block`. -/
theorem rustIsInterrupted_block_ok [RustStdPlacement] :
    subroutine_ok (rustStdPlacedLib.blockProgram RustStdPlacement.mpl 0)
      (rustStdPlacedLib.fnAddr RustStdPlacement.mpl isInterruptedSym)
      (rustStdPlacedLib.withCodeLoaded RustStdPlacement.mpl rustIsInterruptedSpec) := by
  rw [rustFnAddr_eq_base 0 isInterruptedSym (by decide) (by decide)]
  apply subroutine_ok_of_sepWP_init; intro err R s0 hpc hrun hpre _hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, rustIsInterruptedSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hx0, hpre⟩
  rw [satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hcl, hR⟩
  refine ⟨emp, by simpa [emp_sepConj] using hR, ?_⟩
  apply sepWP_block_to_rebase 0 (by decide) hcl
  change SepWP (rustStdPC00.rebase rustStdPl00.base (fun _ => none)) _ _ _ _
  have hpc' : s0.pc = rustStdPl00.base := hpc; clear hpc; rename_i hpc; wp_steps
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨?_, by simp [wp_norm, arm64_norm], by simp [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm]⟩
  intro _; rw [satisfies_pure_sepConj]; refine ⟨⟨?_, ?_, rfl, ?_⟩, hR⟩
  · subst hx0; simp only [State.readReg32] at *
    by_cases h4 : (BitVec.truncate 32 (s0.readReg64 (.gpr 0#5)) == 4#32) = true
    · have hne : (BitVec.truncate 32 (s0.readReg64 (.gpr 0#5)) != 4#32) = false := by simp [bne, h4]
      simp [wp_norm, arm64_norm, h4, hne]
    · simp only [Bool.not_eq_true] at h4
      have hne : (BitVec.truncate 32 (s0.readReg64 (.gpr 0#5)) != 4#32) = true := by simp [bne, h4]
      simp [wp_norm, arm64_norm, h4, hne]
  · subst hx0; simp only [State.readReg32] at *
    by_cases h4 : (BitVec.truncate 32 (s0.readReg64 (.gpr 0#5)) == 4#32) = true
    · have hne : (BitVec.truncate 32 (s0.readReg64 (.gpr 0#5)) != 4#32) = false := by simp [bne, h4]
      simp [wp_norm, arm64_norm, h4, hne]
    · simp only [Bool.not_eq_true] at h4
      have hne : (BitVec.truncate 32 (s0.readReg64 (.gpr 0#5)) != 4#32) = true := by simp [bne, h4]
      simp [wp_norm, arm64_norm, h4, hne]
  · cases s0; exact ProcessFieldsPreserved.refl _

/-- Program-generic contract for `is_interrupted` over any hook-free `P : Program` (`P.svc = Syscall.standard`). -/
theorem rustIsInterrupted_ok [RustStdPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none := by intro; simp)
    (hsvc : P.svc = Syscall.standard := by rfl) :
    subroutine_ok P (rustStdPlacedLib.fnAddr rustStdMpl isInterruptedSym)
      (rustStdPlacedLib.withCodeLoaded rustStdMpl rustIsInterruptedSpec) :=
  rustStdPlacedLib.subroutine_ok_of_block (j := 0) (by decide) rustIsInterrupted_block_ok hext hsvc

/-! ## `<std::io::Stderr as std::io::Write>::write_all` -/

/-- Unlocked 24-byte `ReentrantLock<RefCell<LineWriter<StderrRaw>>>` static instance at
    `rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance"` (`+0`: owner, `+8`: futex, `+12`: count, `+16`: borrow). -/
def RustStderrUnlocked [RustStdPlacement] : SepProp :=
  let inst := rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance"
  ⌜(inst &&& 7#64) = 0#64 ∧ inst.toNat + 24 < 2 ^ 64⌝ ∗
  ((inst ↦₆₄ 0#64) ∗ ((inst + 8#64) ↦₃₂ 0#32) ∗ ((inst + 12#64) ↦₃₂ 0#32) ∗ ((inst + 16#64) ↦₆₄ 0#64))

/-- Contract for `<Stderr as Write>::write_all(&mut Stderr, buf, len)` (`rustStdPC04`, `stderrWriteAllSym`):
    acquires the uncontended `rustStderrInstance` reentrant lock under nonzero TLS thread ID `tid`,
    writes the read-only message `bs` (`0 < bs.length ≤ MAX_RW_COUNT`) to `stderr` (`fd = 2`), releases
    the borrow and lock, and returns `x0 = 0` (`Ok(())`). -/
def rustStderrWriteAllSpec [RustStdPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 8) where
  pre := fun (buf, bs, tid, haveLse) s0 =>
    ⌜s0.readReg64 .x0 = rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance" ∧ s0.readReg64 .x1 = buf ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ 0 < bs.length ∧
      bs.length ≤ Arm64.MAX_RW_COUNT ∧ buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT ∧ tid ≠ 0#64⌝ ∗
    (stackAt s0.sp 112 ∗ RustStderrUnlocked ∗ ((s0.tpidrEl0 + 16#64) ↦₆₄ tid) ∗
      (rustStdPlacedLib.resolve rustStdMpl "__aarch64_have_lse_atomics" ↦₈ᵣ haveLse) ∗ (buf ↦ᵣ bs))
  post := fun (buf, bs, tid, haveLse) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ++ TraceEvent.ofBytes .stderr bs ∧ SyscallPreserved s0 sf⌝ ∗
    (stackAt s0.sp 112 ∗ RustStderrUnlocked ∗ ((sf.tpidrEl0 + 16#64) ↦₆₄ tid) ∗
      (rustStdPlacedLib.resolve rustStdMpl "__aarch64_have_lse_atomics" ↦₈ᵣ haveLse) ∗ (buf ↦ᵣ bs))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

set_option maxHeartbeats 800000 in
/-- Program-generic contract for `Stderr::write_all` (`rustStdPC04`, `stderrWriteAllSym`). -/
theorem rustStderrWriteAll_ok [RustStdPlacement] {P : Program} {fd : BitVec 64}
    (hext : ∀ pc, P.externAt? pc = none) (llc : RustLowLevelIoContracts P fd) :
    subroutine_ok P (rustStdPlacedLib.fnAddr rustStdMpl stderrWriteAllSym)
      (rustStdPlacedLib.withCodeLoaded rustStdMpl rustStderrWriteAllSpec) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨buf, bs, tid, haveLse⟩ R s0 hpc hrun hpre hsp
  rw [rustFnAddr_eq_base 4 stderrWriteAllSym (by decide) (by decide)] at hpc
  dsimp only [MultiPlacedLib.withCodeLoaded, rustStderrWriteAllSpec, RustStderrUnlocked] at hpre ⊢
  rw [sepConj_comm _ ⌜rustStdPlacedLib.CodeLoaded rustStdMpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen_pos, hlen_max, hva, htid_ne⟩, hpre⟩
  have hlen_lt : bs.length < 2 ^ 63 := Nat.lt_of_le_of_lt hlen_max (by decide)
  rw [sepConj_assoc, sepConj_assoc, sepConj_left_comm (stackAt s0.sp 112), sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hinst_al, hinst_nw⟩, hpre⟩
  have hmem_sp' : s0.mem ⊨ (stackAt s0.sp 112 ∗ (rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance" ↦₆₄ 0#64) ∗
      ((rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance" + 8#64) ↦₃₂ 0#32) ∗
      ((rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance" + 12#64) ↦₃₂ 0#32) ∗
      ((rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance" + 16#64) ↦₆₄ 0#64) ∗
      ((s0.tpidrEl0 + 16#64) ↦₆₄ tid) ∗ (rustStdPlacedLib.resolve rustStdMpl "__aarch64_have_lse_atomics" ↦₈ᵣ haveLse) ∗
      (buf ↦ᵣ bs)) ∗ R := by revert hpre; intro hpre; sep_frame
  refine ⟨_, hmem_sp', ?_⟩
  wp_conv_pre =>
    rw [stackAt_frame s0.sp 112 10 (by decide)]; dsimp only [cells]
    simp only [Nat.reduceMul, Nat.reduceSub, BitVec.add_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 => SepWP.exists_elim fun st2 =>
    SepWP.exists_elim fun st3 => SepWP.exists_elim fun st4 => SepWP.exists_elim fun st5 =>
    SepWP.exists_elim fun st6 => SepWP.exists_elim fun st7 => SepWP.exists_elim fun st8 => SepWP.exists_elim fun st9 => ?_
  apply sepWP_seg_rebase_pure hext 4 (by decide) rustBlockNoSvc0_04 hcl (mid := rustStdPlacedLib.resolve rustStdMpl "__aarch64_cas4_acq")
  intro s0' hcpu0; change SepWP (rustStdPC04.rebase rustStdPl04.base (fun _ => none)) _ _ _ _
  have hpc0' : s0'.pc = rustStdPl04.base := hcpu0.pc_eq.trans hpc; have hrun' : s0'.status = .Running := hcpu0.status_eq.trans hrun
  have hsp' : s0'.spAligned = true := hcpu0.spAligned.trans hsp
  have hx0' : s0'.readReg64 .x0 = rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance" := (hcpu0.readReg64 .x0).trans hx0
  have hx1' : s0'.readReg64 .x1 = buf := (hcpu0.readReg64 .x1).trans hx1
  have hx2' : s0'.readReg64 .x2 = BitVec.ofNat 64 bs.length := (hcpu0.readReg64 .x2).trans hx2
  wp_conv_pre => rw [← hcpu0.sp_eq, ← hcpu0.tpidrEl0_eq]
  clear hpc; wp_sym_steps
  apply SepWP.done (by
    dsimp only [State.setMem, State.setPC]
    change rustStdPl04.base + 168#64 + (rustStdPlacedLib.resolve rustStdMpl "__aarch64_cas4_acq" - rustStdPl04.base - 168#64) =
      rustStdPlacedLib.resolve rustStdMpl "__aarch64_cas4_acq"; bv_omega) (by simpa [arm64_norm] using hrun')
  intro sm1 hcpu1 hcl1 hnsp1
  have hpres_m1 : SyscallPreserved s0 sm1 := syscallPreserved_of_seg hcpu0 hcpu1 hnsp1 (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpc1 : sm1.pc = rustStdPlacedLib.resolve rustStdMpl "__aarch64_cas4_acq" := by
    rw [hcpu1.pc_eq]; dsimp only [State.setMem, State.setPC]
    change rustStdPl04.base + 168#64 + (rustStdPlacedLib.resolve rustStdMpl "__aarch64_cas4_acq" - rustStdPl04.base - 168#64) =
      rustStdPlacedLib.resolve rustStdMpl "__aarch64_cas4_acq"; bv_omega
  have hrun1 : sm1.status = .Running := hcpu1.status_eq.trans hrun'
  have hsp1_eq : sm1.sp = s0.sp - 80#64 := by rw [hcpu1.sp_eq]; simp [arm64_norm, hcpu0.sp_eq]
  have hsp1 : sm1.spAligned = true := by simp only [State.spAligned]; rw [hsp1_eq]; exact s0.spAligned_sub 80#64 hsp
  have hlr1 : sm1.readReg64 .lr = rustStdPl04.base + (reloc_call_off% rustBlk04_stderr_write_all.relocs "__aarch64_cas4_acq" + 4#64) := by
    rw [hcpu1.readReg64 .lr]; simp [arm64_norm]
  have hx0_1 : sm1.readReg32 .x0 = 0#32 := by rw [hcpu1.readReg32 .x0]; simp [arm64_norm]
  have hx1_1 : sm1.readReg32 .x1 = 1#32 := by rw [hcpu1.readReg32 .x1]; simp [arm64_norm]
  have hx2_1 : sm1.readReg64 .x2 = rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance" + 8#64 := by
    rw [hcpu1.readReg64 .x2]; simp [arm64_norm]
  have hal_fut : MemWidth.isAligned .W32 (rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance" + 8#64) = true := by
    simp only [MemWidth.isAligned, beq_iff_eq]; apply BitVec.eq_of_toNat_eq
    have h7 : (rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance").toNat % 8 = 0 := by
      have := congrArg BitVec.toNat hinst_al
      simpa [BitVec.toNat_and, show (7#64).toNat = 7 from rfl, Nat.and_two_pow_sub_one_eq_mod _ 3] using this
    simp only [BitVec.toNat_and, BitVec.toNat_add, show (3#64).toNat = 3 from rfl,
      show (8#64).toNat = 8 from rfl, show (0#64).toNat = 0 from rfl, Nat.and_two_pow_sub_one_eq_mod _ 2]; omega
  apply MultiPlacedLib.seq_codeLoaded hcl1
    (mid := rustStdPl04.base + (reloc_call_off% rustBlk04_stderr_write_all.relocs "__aarch64_cas4_acq" + 4#64))
  wp_call llc.cas4Acq_ok; apply SepWP.done ‹_› ‹_›; intro hcl_sf1
  have hx0_1g : BitVec.truncate 32 (sm1.readReg64 (.gpr 0#5)) = 0#32 := hx0_1
  have hx1_1g : BitVec.truncate 32 (sm1.readReg64 (.gpr 1#5)) = 1#32 := hx1_1
  wp_conv_pre => simp only [hx0_1g, hx1_1g, beq_self_eq_true, ↓reduceIte, hcpu0.sp_eq, hcpu0.tpidrEl0_eq, hcpu0.readReg64]
  apply sepWP_seg_rebase_pure hext 4 (by decide) rustBlockNoSvc0_04 hcl_sf1 (mid := rustStdPlacedLib.resolve rustStdMpl "write")
  intro s2' hcpu2; change SepWP (rustStdPC04.rebase rustStdPl04.base (fun _ => none)) _ _ _ _
  have hpc2' : s2'.pc = rustStdPl04.base + 172#64 := hcpu2.pc_eq.trans ‹_ = rustStdPl04.base + 172#64›
  have hrun2' : s2'.status = .Running := hcpu2.status_eq.trans ‹_›
  have hsp2_in : s2'.sp = s0.sp - 80#64 := (hcpu2.sp_eq.trans ‹_ = sm1.sp›).trans hsp1_eq
  have hsp2' : s2'.spAligned = true := by simp only [State.spAligned]; rw [hsp2_in]; exact s0.spAligned_sub 80#64 hsp
  have hx0_2' : s2'.readReg64 .x0 = 0#64 := (hcpu2.readReg64 .x0).trans ‹_ = 0#64›
  have hx19_2' : s2'.readReg64 .x19 = rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance" := by
    rw [(hcpu2.readReg64 .x19).trans ‹_ = sm1.readReg64 (.gpr 19#5)›, hcpu1.readReg64 .x19]; simp [arm64_norm]
  have hx20_2' : s2'.readReg64 .x20 = BitVec.ofNat 64 bs.length := by
    rw [(hcpu2.readReg64 .x20).trans ‹_ = sm1.readReg64 (.gpr 20#5)›, hcpu1.readReg64 .x20]; simp [arm64_norm]
  have hx21_2' : s2'.readReg64 .x21 = buf := by
    rw [(hcpu2.readReg64 .x21).trans ‹_ = sm1.readReg64 (.gpr 21#5)›, hcpu1.readReg64 .x21]; simp [arm64_norm]
  have hx22_2' : s2'.readReg64 .x22 = 1#64 := by
    rw [(hcpu2.readReg64 .x22).trans ‹_ = sm1.readReg64 (.gpr 22#5)›, hcpu1.readReg64 .x22]; simp [arm64_norm]
  have hx24_2' : s2'.readReg64 .x24 = tid := by
    rw [(hcpu2.readReg64 .x24).trans ‹_ = sm1.readReg64 (.gpr 24#5)›, hcpu1.readReg64 .x24]; simp [arm64_norm]
  wp_sym_steps
  apply SepWP.done (by
    dsimp only [State.setMem, State.setPC]
    change rustStdPl04.base + 240#64 + (rustStdPlacedLib.resolve rustStdMpl "write" - rustStdPl04.base - 240#64) =
      rustStdPlacedLib.resolve rustStdMpl "write"; bv_omega) (by simpa [arm64_norm] using hrun2')
  intro sm2 hcpu_m2 hcl2 hnsp2
  have hstd1 : StdStatePreserved sm1 _ := ‹StdStatePreserved sm1 _›
  have hpres_m2 : SyscallPreserved s0 sm2 :=
    hpres_m1.trans ((SyscallPreserved.of_std hstd1).trans
      (syscallPreserved_of_seg hcpu2 hcpu_m2 hnsp2 (by simp [arm64_norm]) (by simp [arm64_norm])))
  have hfs_m2 : sm2.fs = s0.fs := hnsp2.2.2.2.2.2.2.trans (hstd1.1.trans hnsp1.2.2.2.2.2.2)
  have htr_m2 : sm2.trace = s0.trace := hnsp2.1.trans (hstd1.2.1.trans hnsp1.1)
  have hpc2 : sm2.pc = rustStdPlacedLib.resolve rustStdMpl "write" := by
    rw [hcpu_m2.pc_eq]; dsimp only [State.setMem, State.setPC]
    change rustStdPl04.base + 240#64 + (rustStdPlacedLib.resolve rustStdMpl "write" - rustStdPl04.base - 240#64) =
      rustStdPlacedLib.resolve rustStdMpl "write"; bv_omega
  have hrun2 : sm2.status = .Running := hcpu_m2.status_eq.trans hrun2'
  have hsp2_eq : sm2.sp = s0.sp - 80#64 := by rw [hcpu_m2.sp_eq]; simp [arm64_norm, hsp2_in]
  have hsp2 : sm2.spAligned = true := by simp only [State.spAligned]; rw [hsp2_eq]; exact s0.spAligned_sub 80#64 hsp
  have hlr2 : sm2.readReg64 .lr = rustStdPl04.base + (reloc_call_off% rustBlk04_stderr_write_all.relocs "write" + 4#64) := by
    rw [hcpu_m2.readReg64 .lr]; simp [arm64_norm]
  have hx0_m2 : sm2.readReg32 .x0 = 2#32 := by rw [hcpu_m2.readReg32 .x0]; simp [arm64_norm]
  have hx1_m2 : sm2.readReg64 .x1 = buf := by rw [hcpu_m2.readReg64 .x1]; simp [arm64_norm]
  have hx2_m2 : sm2.readReg64 .x2 = BitVec.ofNat 64 bs.length := by rw [hcpu_m2.readReg64 .x2]; simp [arm64_norm]
  wp_conv_pre => rw [← hsp2_eq]
  apply MultiPlacedLib.seq_codeLoaded hcl2 (mid := rustStdPl04.base + (reloc_call_off% rustBlk04_stderr_write_all.relocs "write" + 4#64))
  wp_call llc.writeStderr_ok; apply SepWP.done ‹_› ‹_›; intro hcl_sf2
  wp_conv_pre => rw [hsp2_eq]
  have hlen_ne_zero : BitVec.ofNat 64 bs.length ≠ 0#64 := by bv_omega
  have hlen_add1_ne_zero : BitVec.ofNat 64 bs.length + 1#64 ≠ 0#64 := by bv_omega
  apply sepWP_seg_rebase_pure hext 4 (by decide) rustBlockNoSvc0_04 hcl_sf2 (mid := rustStdPlacedLib.resolve rustStdMpl "__aarch64_swp4_rel")
  intro s3' hcpu3; change SepWP (rustStdPC04.rebase rustStdPl04.base (fun _ => none)) _ _ _ _
  have hpc3' : s3'.pc = rustStdPl04.base + 244#64 := hcpu3.pc_eq.trans ‹_ = rustStdPl04.base + 244#64›
  have hrun3' : s3'.status = .Running := hcpu3.status_eq.trans ‹_›
  have hsp3_in : s3'.sp = s0.sp - 80#64 := (hcpu3.sp_eq.trans ‹_ = sm2.sp›).trans hsp2_eq
  have hsp3' : s3'.spAligned = true := by simp only [State.spAligned]; rw [hsp3_in]; exact s0.spAligned_sub 80#64 hsp
  have hx0_3' : s3'.readReg64 .x0 = BitVec.ofNat 64 bs.length := (hcpu3.readReg64 .x0).trans ‹_ = BitVec.ofNat 64 bs.length›
  have hx19_3' : s3'.readReg64 .x19 = rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance" := by
    rw [(hcpu3.readReg64 .x19).trans ‹_ = sm2.readReg64 (.gpr 19#5)›, hcpu_m2.readReg64 .x19]; simp [arm64_norm, hx19_2']
  have hx20_3' : s3'.readReg64 .x20 = BitVec.ofNat 64 bs.length := by
    rw [(hcpu3.readReg64 .x20).trans ‹_ = sm2.readReg64 (.gpr 20#5)›, hcpu_m2.readReg64 .x20]; simp [arm64_norm, hx20_2']
  have hx21_3' : s3'.readReg64 .x21 = buf := by
    rw [(hcpu3.readReg64 .x21).trans ‹_ = sm2.readReg64 (.gpr 21#5)›, hcpu_m2.readReg64 .x21]; simp [arm64_norm, hx21_2']
  wp_sym_steps
  apply SepWP.done (by
    dsimp only [State.setMem, State.setPC]
    change rustStdPl04.base + 408#64 + (rustStdPlacedLib.resolve rustStdMpl "__aarch64_swp4_rel" - rustStdPl04.base - 408#64) =
      rustStdPlacedLib.resolve rustStdMpl "__aarch64_swp4_rel"; bv_lin) (by simpa [arm64_norm] using hrun3')
  intro sm3 hcpu_m3 hcl3 hnsp3
  have hpres_sf2 : SyscallPreserved sm2 (sameCpuRhs hcpu3) := by assumption
  have hpres_m3 : SyscallPreserved s0 sm3 :=
    hpres_m2.trans (hpres_sf2.trans (syscallPreserved_of_seg hcpu3 hcpu_m3 hnsp3 (by simp [arm64_norm]) (by simp [arm64_norm])))
  have hfs_m3 : sm3.fs = s0.fs := by
    have h22 : (sameCpuRhs hcpu3).fs = sm2.fs := by assumption
    exact hnsp3.2.2.2.2.2.2.trans (h22.trans hfs_m2)
  have htr_m3 : sm3.trace = s0.trace ++ TraceEvent.ofBytes .stderr bs := by
    have h23 : (sameCpuRhs hcpu3).trace = sm2.trace ++ List.map (TraceEvent.writeByte OutputStream.stderr) bs := by assumption
    rw [hnsp3.1, h23, htr_m2]; rfl
  have hpc3 : sm3.pc = rustStdPlacedLib.resolve rustStdMpl "__aarch64_swp4_rel" := by
    rw [hcpu_m3.pc_eq]; dsimp only [State.setMem, State.setPC]
    change rustStdPl04.base + 408#64 + (rustStdPlacedLib.resolve rustStdMpl "__aarch64_swp4_rel" - rustStdPl04.base - 408#64) =
      rustStdPlacedLib.resolve rustStdMpl "__aarch64_swp4_rel"; bv_lin
  have hrun3 : sm3.status = .Running := hcpu_m3.status_eq.trans hrun3'
  have hsp3_eq : sm3.sp = s0.sp - 80#64 := by rw [hcpu_m3.sp_eq]; simp [arm64_norm, hsp3_in]
  have hsp3 : sm3.spAligned = true := by simp only [State.spAligned]; rw [hsp3_eq]; exact s0.spAligned_sub 80#64 hsp
  have hlr3 : sm3.readReg64 .lr = rustStdPl04.base + (reloc_call_off% rustBlk04_stderr_write_all.relocs "__aarch64_swp4_rel" + 4#64) := by
    rw [hcpu_m3.readReg64 .lr]; simp [arm64_norm]
  have hx0_m3 : sm3.readReg32 .x0 = 0#32 := by rw [hcpu_m3.readReg32 .x0]; simp [arm64_norm]
  have hx1_m3 : sm3.readReg64 .x1 = rustStdPlacedLib.resolve rustStdMpl "rustStderrInstance" + 8#64 := by
    rw [hcpu_m3.readReg64 .x1]; simp [arm64_norm]
  apply MultiPlacedLib.seq_codeLoaded hcl3
    (mid := rustStdPl04.base + (reloc_call_off% rustBlk04_stderr_write_all.relocs "__aarch64_swp4_rel" + 4#64))
  wp_call llc.swp4Rel_ok; apply SepWP.done ‹_› ‹_›; intro hcl_sf3
  have hx0_m3g : BitVec.truncate 32 (sm3.readReg64 (.gpr 0#5)) = 0#32 := hx0_m3
  wp_conv_pre => simp only [hx0_m3g]
  apply sepWP_seg_rebase_pure hext 4 (by decide) rustBlockNoSvc0_04 hcl_sf3 (mid := s0.readReg64 .lr)
  intro s4' hcpu4; change SepWP (rustStdPC04.rebase rustStdPl04.base (fun _ => none)) _ _ _ _
  have hpc4' : s4'.pc = rustStdPl04.base + 412#64 := hcpu4.pc_eq.trans ‹_ = rustStdPl04.base + 412#64›
  have hrun4' : s4'.status = .Running := hcpu4.status_eq.trans ‹_›
  have hsp4_eq' : s4'.sp = s0.sp - 80#64 := (hcpu4.sp_eq.trans ‹_ = sm3.sp›).trans hsp3_eq
  have hsp4' : s4'.spAligned = true := by simp only [State.spAligned]; rw [hsp4_eq']; exact s0.spAligned_sub 80#64 hsp
  have hx0_4' : s4'.readReg64 .x0 = 1#64 := by
    have hswp : (sameCpuRhs hcpu4).readReg64 .x0 = (1#32).zeroExtend 64 := by assumption
    exact (hcpu4.readReg64 .x0).trans hswp
  have hx20_4' : s4'.readReg64 .x20 = 0#64 := by
    rw [(hcpu4.readReg64 .x20).trans ‹_ = sm3.readReg64 (.gpr 20#5)›, hcpu_m3.readReg64 .x20]; simp [arm64_norm]
  wp_conv_pre => simp only [← hsp4_eq',
    show s0.sp - 72#64 = s4'.sp + 8#64 by rw [hsp4_eq']; bv_lin, show s0.sp - 64#64 = s4'.sp + 16#64 by rw [hsp4_eq']; bv_lin,
    show s0.sp - 56#64 = s4'.sp + 24#64 by rw [hsp4_eq']; bv_lin, show s0.sp - 48#64 = s4'.sp + 32#64 by rw [hsp4_eq']; bv_lin,
    show s0.sp - 40#64 = s4'.sp + 40#64 by rw [hsp4_eq']; bv_lin, show s0.sp - 32#64 = s4'.sp + 48#64 by rw [hsp4_eq']; bv_lin,
    show s0.sp - 24#64 = s4'.sp + 56#64 by rw [hsp4_eq']; bv_lin, show s0.sp - 16#64 = s4'.sp + 64#64 by rw [hsp4_eq']; bv_lin,
    show s0.sp - 8#64 = s4'.sp + 72#64 by rw [hsp4_eq']; bv_lin]
  wp_sym_steps; apply SepWP.done (by rfl) (by simpa [arm64_norm] using hrun4')
  intro sf4 hcpu_f4 hcl4 hnsp4
  have hstd3 : StdStatePreserved sm3 (sameCpuRhs hcpu4) := by assumption
  have hpres_f4 : SyscallPreserved s0 sf4 :=
    hpres_m3.trans ((SyscallPreserved.of_std hstd3).trans
      (syscallPreserved_of_seg hcpu4 hcpu_f4 hnsp4 (by simp [arm64_norm]) (by simp [arm64_norm])))
  have hfs_f4 : sf4.fs = s0.fs := hnsp4.2.2.2.2.2.2.trans (hstd3.1.trans hfs_m3)
  have htr_f4 : sf4.trace = s0.trace ++ TraceEvent.ofBytes .stderr bs := hnsp4.1.trans (hstd3.2.1.trans htr_m3)
  have hx0_f4 : sf4.readReg64 .x0 = 0#64 := by rw [hcpu_f4.readReg64 .x0]; simp [arm64_norm]
  have hsp_f4 : sf4.sp = s0.sp := by rw [hcpu_f4.sp_eq]; simp [arm64_norm]
  have hcs_f4 : CalleeSavedPreserved s0 sf4 := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨by rw [hcpu_f4.readReg64 (.gpr 19#5)]; simp [arm64_norm],
      by rw [hcpu_f4.readReg64 (.gpr 20#5)]; simp [arm64_norm], by rw [hcpu_f4.readReg64 (.gpr 21#5)]; simp [arm64_norm],
      by rw [hcpu_f4.readReg64 (.gpr 22#5)]; simp [arm64_norm], by rw [hcpu_f4.readReg64 (.gpr 23#5)]; simp [arm64_norm],
      by rw [hcpu_f4.readReg64 (.gpr 24#5)]; simp [arm64_norm], by rw [hcpu_f4.readReg64 (.gpr 25#5)]; simp [arm64_norm], ?_, ?_, ?_,
      by rw [hcpu_f4.readReg64 Reg.fp]; simp [arm64_norm], ?_⟩
    · rw [hcpu_f4.readReg64 (.gpr 26#5)]; simp only [arm64_norm]
      rw [(hcpu4.readReg64 (.gpr 26#5)).trans ‹_ = sm3.readReg64 (.gpr 26#5)›, hcpu_m3.readReg64 (.gpr 26#5)]; simp only [arm64_norm]
      rw [(hcpu3.readReg64 (.gpr 26#5)).trans ‹_ = sm2.readReg64 (.gpr 26#5)›, hcpu_m2.readReg64 (.gpr 26#5)]; simp only [arm64_norm]
      rw [(hcpu2.readReg64 (.gpr 26#5)).trans ‹_ = sm1.readReg64 (.gpr 26#5)›, hcpu1.readReg64 (.gpr 26#5)]; simp [arm64_norm, hcpu0.readReg64]
    · rw [hcpu_f4.readReg64 (.gpr 27#5)]; simp only [arm64_norm]
      rw [(hcpu4.readReg64 (.gpr 27#5)).trans ‹_ = sm3.readReg64 (.gpr 27#5)›, hcpu_m3.readReg64 (.gpr 27#5)]; simp only [arm64_norm]
      rw [(hcpu3.readReg64 (.gpr 27#5)).trans ‹_ = sm2.readReg64 (.gpr 27#5)›, hcpu_m2.readReg64 (.gpr 27#5)]; simp only [arm64_norm]
      rw [(hcpu2.readReg64 (.gpr 27#5)).trans ‹_ = sm1.readReg64 (.gpr 27#5)›, hcpu1.readReg64 (.gpr 27#5)]; simp [arm64_norm, hcpu0.readReg64]
    · rw [hcpu_f4.readReg64 (.gpr 28#5)]; simp only [arm64_norm]
      rw [(hcpu4.readReg64 (.gpr 28#5)).trans ‹_ = sm3.readReg64 (.gpr 28#5)›, hcpu_m3.readReg64 (.gpr 28#5)]; simp only [arm64_norm]
      rw [(hcpu3.readReg64 (.gpr 28#5)).trans ‹_ = sm2.readReg64 (.gpr 28#5)›, hcpu_m2.readReg64 (.gpr 28#5)]; simp only [arm64_norm]
      rw [(hcpu2.readReg64 (.gpr 28#5)).trans ‹_ = sm1.readReg64 (.gpr 28#5)›, hcpu1.readReg64 (.gpr 28#5)]; simp [arm64_norm, hcpu0.readReg64]
    · rw [hcpu_f4.calleeSavedVRegs]; dsimp only [calleeSavedVRegs, State.setMem, State.setPC, State.writeReg64]
      change calleeSavedVRegs s4' = calleeSavedVRegs s0
      rw [hcpu4.calleeSavedVRegs.trans ‹_ = calleeSavedVRegs sm3›, hcpu_m3.calleeSavedVRegs]
      change calleeSavedVRegs s3' = calleeSavedVRegs s0
      rw [hcpu3.calleeSavedVRegs.trans ‹_ = calleeSavedVRegs sm2›, hcpu_m2.calleeSavedVRegs]
      change calleeSavedVRegs s2' = calleeSavedVRegs s0
      rw [hcpu2.calleeSavedVRegs.trans ‹_ = calleeSavedVRegs sm1›, hcpu1.calleeSavedVRegs]
      exact hcpu0.calleeSavedVRegs
  refine SepWP.done (by rw [hcpu_f4.pc_eq]; rfl) (hcpu_f4.status_eq.trans hrun4') ⟨fun hmem_f => Satisfies.mono ?_ hmem_f, hsp_f4, hcs_f4⟩
  rw [hpres_f4.1, pure_sepConj_of_true ⟨hx0_f4, hfs_f4, htr_f4, hpres_f4⟩,
      pure_sepConj_of_true ⟨hinst_al, hinst_nw⟩, stackAt_frame s0.sp 112 10 (by decide)]
  dsimp only [cells]; simp only [Nat.reduceMul, Nat.reduceSub, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, hsp4_eq', bv_lin_norm]
  refine Entails.sepExists_right (s0.readReg64 (.gpr 29#5)) <| Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 25#5)) <| Entails.sepExists_right st3 <|
    Entails.sepExists_right (s0.readReg64 (.gpr 24#5)) <| Entails.sepExists_right (s0.readReg64 (.gpr 23#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 22#5)) <| Entails.sepExists_right (s0.readReg64 (.gpr 21#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 20#5)) <| Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) ?_
  sep_entail

/-! ## SWAR NUL-Scan Lemmas for `run_with_cstr_allocating` -/

theorem rustSetWidth32_signExtend64 (x : BitVec 32) : BitVec.setWidth 32 (x.signExtend 64) = x := by bv_slice

theorem rustPointsTo64_sp96_zero (sp : BitVec 64) :
    (((sp - 96#64) ↦₆₄ 0#64) ∗ ((sp - 88#64) ↦₆₄ 0#64) ∗ ((sp - 80#64) ↦₆₄ 0#64) ∗ ((sp - 72#64) ↦₆₄ 0#64)) =
      ((sp - 96#64) ↦ₛ List.replicate 32 0#8) := by
  have h32 : List.replicate 32 0#8 = (unpack64 0#64 ++ unpack64 0#64) ++ (unpack64 0#64 ++ unpack64 0#64) := by decide
  rw [h32, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [List.length_append, unpack64_length, Nat.reduceAdd, ← pointsTo64_eq_pointsToBytes, bv_lin_norm, sepConj_assoc]

theorem rustExists_sp96_quad (sp : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64, ((sp - 96#64) ↦ₛ bs) =
      (((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗ ((sp - 80#64) ↦₆₄ w2) ∗ ((sp - 72#64) ↦₆₄ w3)) := by
  obtain ⟨w0, w1, w2, w3, _, hq⟩ := exists_unpack64_of_length_32 h
  exact ⟨w0, w1, w2, w3, by simpa only [bv_lin_norm, sepConj_assoc] using hq (sp - 96#64)⟩

theorem rustBv64_ofNat_sub_len {len rlen : Nat} (_h : len + rlen < 2 ^ 64) :
    BitVec.ofNat 64 (len + rlen) - BitVec.ofNat 64 len = BitVec.ofNat 64 rlen := by
  have := _h; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

private theorem rustSwar_word_high_bits {w : BitVec 64}
    (h0 : w.extractLsb' 0 8 ≠ 0#8) (h1 : w.extractLsb' 8 8 ≠ 0#8) (h2 : w.extractLsb' 16 8 ≠ 0#8) (h3 : w.extractLsb' 24 8 ≠ 0#8)
    (h4 : w.extractLsb' 32 8 ≠ 0#8) (h5 : w.extractLsb' 40 8 ≠ 0#8) (h6 : w.extractLsb' 48 8 ≠ 0#8) (h7 : w.extractLsb' 56 8 ≠ 0#8) :
    ((72340172838076672#64 - w) ||| w) &&& 9259542123273814144#64 = 9259542123273814144#64 := by bv_robdd

theorem rustSwar_bics_eq_zero {w0 w1 : BitVec 64}
    (hw0 : ∀ b ∈ unpack64 w0, b ≠ 0#8) (hw1 : ∀ b ∈ unpack64 w1, b ≠ 0#8) :
    9259542123273814144#64 &&& ~~~(((72340172838076672#64 - w0) ||| w0) &&& ((72340172838076672#64 - w1) ||| w1)) = 0#64 := by
  have h0 : ((72340172838076672#64 - w0) ||| w0) &&& 9259542123273814144#64 = 9259542123273814144#64 := by
    simp only [unpack64, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hw0
    exact rustSwar_word_high_bits hw0.1 hw0.2.1 hw0.2.2.1 hw0.2.2.2.1 hw0.2.2.2.2.1 hw0.2.2.2.2.2.1 hw0.2.2.2.2.2.2.1 hw0.2.2.2.2.2.2.2
  have h1 : ((72340172838076672#64 - w1) ||| w1) &&& 9259542123273814144#64 = 9259542123273814144#64 := by
    simp only [unpack64, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hw1
    exact rustSwar_word_high_bits hw1.1 hw1.2.1 hw1.2.2.1 hw1.2.2.2.1 hw1.2.2.2.2.1 hw1.2.2.2.2.2.1 hw1.2.2.2.2.2.2.1 hw1.2.2.2.2.2.2.2
  generalize (72340172838076672#64 - w0) ||| w0 = u0 at h0 ⊢
  generalize (72340172838076672#64 - w1) ||| w1 = u1 at h1 ⊢; bv_robdd

abbrev rustAlign8 (p : BitVec 64) : BitVec 64 := (p + 7#64) &&& 0xffff_ffff_ffff_fff8#64
abbrev rustHeadBV (p : BitVec 64) : BitVec 64 := rustAlign8 p - p

theorem rustHeadBV_lt8 (p : BitVec 64) : (rustHeadBV p).toNat < 8 := by
  have h : (rustHeadBV p).ult 8#64 = true := by dsimp [rustHeadBV, rustAlign8]; bv_robdd
  simpa [BitVec.ult] using h

theorem rustSepWP_cut {prog : Program} {mid tgt : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog mid s Pre fun sm Pm => SepWP prog tgt sm Pm post) : SepWP prog tgt s Pre post := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sm, hs1, ⟨_, _, _, hmm, hc⟩ | ⟨hr, ho⟩⟩ := SepWP.to_reaches_pc h hm hL
  · obtain ⟨sf, hs2, hout⟩ := SepWP.to_reaches_pc hc hmm (hs1.codeLoaded hL); exact ⟨sf, hs1.trans hs2, hout⟩
  · exact ⟨sm, hs1, Or.inr ⟨hr, ho⟩⟩

def RustScanRegs (s0 s1 : State) : Prop :=
  s1.readReg64 .x19 = s0.readReg64 .x19 ∧ s1.readReg64 .x20 = s0.readReg64 .x20 ∧
  s1.readReg64 .x21 = s0.readReg64 .x21 ∧ s1.readReg64 .x22 = s0.readReg64 .x22 ∧
  s1.readReg64 .x23 = s0.readReg64 .x23 ∧ s1.readReg64 .x24 = s0.readReg64 .x24 ∧
  s1.readReg64 .x25 = s0.readReg64 .x25 ∧ s1.readReg64 .x26 = s0.readReg64 .x26 ∧
  s1.readReg64 .x27 = s0.readReg64 .x27 ∧ s1.readReg64 .x28 = s0.readReg64 .x28 ∧ s1.readReg64 .fp = s0.readReg64 .fp

theorem RustScanRegs.trans {s0 s1 s2 : State} (a : RustScanRegs s0 s1) (b : RustScanRegs s1 s2) : RustScanRegs s0 s2 :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.1.trans a.2.2.2.1, b.2.2.2.2.1.trans a.2.2.2.2.1,
   b.2.2.2.2.2.1.trans a.2.2.2.2.2.1, b.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.1, b.2.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.2.1,
   b.2.2.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.2.2.1, b.2.2.2.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.2.2.2.1,
   b.2.2.2.2.2.2.2.2.2.2.trans a.2.2.2.2.2.2.2.2.2.2⟩

def RustScanPreserved (s0 s1 : State) : Prop :=
  s1.status = .Running ∧ s1.sp = s0.sp ∧ s1.spAligned = true ∧
  s1.tpidrEl0 = s0.tpidrEl0 ∧ s1.sigActions = s0.sigActions ∧ RustScanRegs s0 s1 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0

theorem RustScanPreserved.trans {s0 s1 s2 : State} (h01 : RustScanPreserved s0 s1) (h12 : RustScanPreserved s1 s2) : RustScanPreserved s0 s2 :=
  ⟨h12.1, h12.2.1.trans h01.2.1, h12.2.2.1, h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h01.2.2.2.2.2.1.trans h12.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

theorem rustNz_byte_ze_beq_false {b : BitVec 8} (hb : b ≠ 0#8) :
    (BitVec.setWidth 32 (b.zeroExtend 64) == 0#32) = false ∧ (b.zeroExtend 32 == 0#32) = false ∧ (b.zeroExtend 64 == 0#64) = false := by
  have h32 : b.zeroExtend 32 ≠ 0#32 := by intro h; apply hb; bv_omega
  have h64 : b.zeroExtend 64 ≠ 0#64 := by intro h; apply hb; bv_omega
  have hsw : BitVec.setWidth 32 (b.zeroExtend 64) = b.zeroExtend 32 := by bv_slice
  exact ⟨hsw ▸ beq_false_of_ne h32, beq_false_of_ne h32, beq_false_of_ne h64⟩

private theorem rustRunWithCstr_head_loop [RustStdPlacement] {tgt : BitVec 64} {post : State → SepProp → Prop} :
    ∀ (k : Nat) {p : BitVec 64} {rem : List (BitVec 8)} {F : SepProp} {s : State},
      1 ≤ k → k ≤ 7 → rem.length = k → (∀ b ∈ rem, b ≠ 0#8) →
      s.pc = rustStdPl02.base + 96#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 (.gpr 9#5) = 0#64 - BitVec.ofNat 64 k → s.readReg64 (.gpr 10#5) = p →
      (∀ sf : State, sf.pc = rustStdPl02.base + 112#64 → RustScanPreserved s sf →
        sf.readReg64 (.gpr 8#5) = s.readReg64 (.gpr 8#5) →
        SepWP (rustStdPC02.rebase rustStdPl02.base (fun _ => none)) tgt sf ((p ↦ₛ rem) ∗ F) post) →
      SepWP (rustStdPC02.rebase rustStdPl02.base (fun _ => none)) tgt s ((p ↦ₛ rem) ∗ F) post
  | 0, _, _, _, _, hk1, _, _, _, _, _, _, _, _, _ => by omega
  | 1, p, rem, F, s, _, _, hlen, hnz, hpc, hrun, hsp, hx9, hx10, hcont => by
    rcases rem with _ | ⟨b, _ | _⟩ <;> try (simp at hlen)
    obtain ⟨hb1, hb2, hb3⟩ := rustNz_byte_ze_beq_false (hnz b (List.mem_cons_self ..))
    have hx9' : s.readReg64 (.gpr 9#5) = 0xffff_ffff_ffff_ffff#64 := hx9
    apply rustSepWP_cut (mid := rustStdPl02.base + 112#64)
    wp_conv_pre => simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    wp_sym_steps; refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => simp only [← pointsToBytes_singleton]
    exact hcont _ rfl ⟨by simpa [arm64_norm] using hrun, rfl, by simpa [arm64_norm] using hsp, rfl, rfl,
      by simp [RustScanRegs, arm64_norm], rfl⟩ (by simp [arm64_norm])
  | k + 2, p, rem, F, s, _, hk7, hlen, hnz, hpc, hrun, hsp, hx9, hx10, hcont => by
    rcases rem with _ | ⟨b, rest⟩; · simp at hlen
    obtain ⟨hb1, hb2, hb3⟩ := rustNz_byte_ze_beq_false (hnz b (List.mem_cons_self ..))
    wp_conv_pre => rw [pointsToBytes_cons, sepConj_assoc]
    have hstep : ∀ s1 : State, s1.pc = rustStdPl02.base + 96#64 → RustScanPreserved s s1 →
        s1.readReg64 (.gpr 8#5) = s.readReg64 (.gpr 8#5) → s1.readReg64 (.gpr 9#5) = 0#64 - BitVec.ofNat 64 (k + 1) →
        s1.readReg64 (.gpr 10#5) = p + 1#64 →
        SepWP (rustStdPC02.rebase rustStdPl02.base (fun _ => none)) tgt s1 ((p ↦₈ b) ∗ ((p + 1#64) ↦ₛ rest) ∗ F) post := by
      intro s1 hpc1 hsc1 hx8_1 hx9_1 hx10_1
      refine SepWP.weaken_pre (P' := ((p + 1#64) ↦ₛ rest) ∗ ((p ↦₈ b) ∗ F)) (by sep_entail) ?_
      refine rustRunWithCstr_head_loop (k + 1) (by omega) (by omega) (by simp at hlen; omega)
        (fun x hx => hnz x (List.mem_cons_of_mem _ hx)) hpc1 hsc1.1 hsc1.2.2.1 hx9_1 hx10_1 fun sf hpcf hscf hx8f => ?_
      refine SepWP.weaken_pre ?_ (hcont sf hpcf (hsc1.trans hscf) (hx8f.trans hx8_1)); rw [pointsToBytes_cons]; sep_entail
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [Nat.reduceAdd] at hx9; apply rustSepWP_cut (mid := rustStdPl02.base + 96#64); wp_sym_steps
      exact SepWP.done rfl (by simpa [arm64_norm] using hrun) (hstep _ rfl
        ⟨by simpa [arm64_norm] using hrun, rfl, by simpa [arm64_norm] using hsp, rfl, rfl, by simp [RustScanRegs, arm64_norm], rfl⟩
        (by simp [arm64_norm]) (by simp only [arm64_norm]; decide) (by simp [arm64_norm]))

private theorem rustRunWithCstr_tail_loop [RustStdPlacement] {tgt : BitVec 64} {post : State → SepProp → Prop} :
    ∀ (rem : List (BitVec 8)) {p : BitVec 64} {F : SepProp} {s : State},
      1 ≤ rem.length → rem.length < 16 → (∀ b ∈ rem, b ≠ 0#8) →
      s.pc = rustStdPl02.base + 188#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 (.gpr 8#5) = p → s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 rem.length →
      (∀ sf : State, sf.pc = rustStdPl02.base + 204#64 → RustScanPreserved s sf →
        SepWP (rustStdPC02.rebase rustStdPl02.base (fun _ => none)) tgt sf ((p ↦ₛ rem) ∗ F) post) →
      SepWP (rustStdPC02.rebase rustStdPl02.base (fun _ => none)) tgt s ((p ↦ₛ rem) ∗ F) post
  | [], _, _, _, h1, _, _, _, _, _, _, _, _ => by simp at h1
  | [b], p, F, s, _, _, hnz, hpc, hrun, hsp, hx8, hx9, hcont => by
    obtain ⟨hb1, hb2, hb3⟩ := rustNz_byte_ze_beq_false (hnz b (List.mem_cons_self ..)); have hx9' : s.readReg64 (.gpr 9#5) = 1#64 := hx9
    apply rustSepWP_cut (mid := rustStdPl02.base + 204#64)
    wp_conv_pre => simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    wp_sym_steps; refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => simp only [← pointsToBytes_singleton]
    exact hcont _ rfl ⟨by simpa [arm64_norm] using hrun, rfl, by simpa [arm64_norm] using hsp, rfl, rfl, by simp [RustScanRegs, arm64_norm], rfl⟩
  | b :: b2 :: rest, p, F, s, _, hlt, hnz, hpc, hrun, hsp, hx8, hx9, hcont => by
    obtain ⟨hb1, hb2, hb3⟩ := rustNz_byte_ze_beq_false (hnz b (List.mem_cons_self ..))
    have hne1 : BitVec.ofNat 64 (b :: b2 :: rest).length ≠ 1#64 := (by simp only [List.length_cons] at hlt ⊢; bv_omega)
    have hbeq1 : (BitVec.ofNat 64 (b :: b2 :: rest).length == 1#64) = false := beq_false_of_ne hne1
    have hbne1 : (BitVec.ofNat 64 (b :: b2 :: rest).length != 1#64) = true := bne_iff_ne.mpr hne1
    have hne0 : (BitVec.ofNat 64 (b2 :: rest).length != 0#64) = true := bne_iff_ne.mpr (by simp only [List.length_cons] at hlt ⊢; bv_omega)
    have hbeq0 : (BitVec.ofNat 64 (b2 :: rest).length == 0#64) = false := beq_false_of_ne (by simp only [List.length_cons] at hlt ⊢; bv_omega)
    apply rustSepWP_cut (mid := rustStdPl02.base + 188#64); wp_conv_pre => rw [pointsToBytes_cons, sepConj_assoc]
    wp_sym_steps; refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    refine SepWP.weaken_pre (P' := ((p + 1#64) ↦ₛ (b2 :: rest)) ∗ ((p ↦₈ b) ∗ F)) (by sep_entail) ?_
    refine rustRunWithCstr_tail_loop (b2 :: rest) (by simp) (by simp at hlt ⊢; omega)
      (fun x hx => hnz x (List.mem_cons_of_mem _ hx)) rfl (by simpa [arm64_norm] using hrun)
      (by simpa [arm64_norm] using hsp) (by simp [arm64_norm])
      (by simp only [List.length_cons] at hlt ⊢; simp [arm64_norm]; bv_omega) fun sf hpcf hscf => ?_
    have hsc0 : RustScanPreserved s _ := ⟨by simpa [arm64_norm] using hrun, rfl, by simpa [arm64_norm] using hsp, rfl, rfl, by simp [RustScanRegs, arm64_norm], rfl⟩
    refine SepWP.weaken_pre ?_ (hcont sf hpcf (hsc0.trans hscf)); conv => rhs; rw [pointsToBytes_cons]
    sep_entail

private theorem rustRunWithCstr_tail_entry [RustStdPlacement] {tgt : BitVec 64}
    {off n : Nat} {slicePtr : BitVec 64} {rem : List (BitVec 8)} {F : SepProp} {s : State} {post : State → SepProp → Prop}
    (hoff : off ≤ n) (hn : n < 4096) (hlt16 : n - off < 16) (hlen : rem.length = n - off) (hnz : ∀ b ∈ rem, b ≠ 0#8)
    (hpc : s.pc = rustStdPl02.base + 176#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 off)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n) (hx23 : s.readReg64 (.gpr 23#5) = slicePtr)
    (hcont : ∀ sf : State, sf.pc = rustStdPl02.base + 204#64 → RustScanPreserved s sf →
      SepWP (rustStdPC02.rebase rustStdPl02.base (fun _ => none)) tgt sf (((slicePtr + BitVec.ofNat 64 off) ↦ₛ rem) ∗ F) post) :
    SepWP (rustStdPC02.rebase rustStdPl02.base (fun _ => none)) tgt s (((slicePtr + BitVec.ofNat 64 off) ↦ₛ rem) ∗ F) post := by
  by_cases heq : off = n
  · subst heq; apply rustSepWP_cut (mid := rustStdPl02.base + 204#64); wp_sym_steps
    exact SepWP.done rfl (by simpa [arm64_norm] using hrun)
      (hcont _ rfl ⟨by simpa [arm64_norm] using hrun, rfl, by simpa [arm64_norm] using hsp, rfl, rfl, by simp [RustScanRegs, arm64_norm], rfl⟩)
  · have hne_bv : BitVec.ofNat 64 n ≠ BitVec.ofNat 64 off := by bv_omega
    have hbeq_bv : (BitVec.ofNat 64 n == BitVec.ofNat 64 off) = false := beq_false_of_ne hne_bv
    have hbne_bv : (BitVec.ofNat 64 n != BitVec.ofNat 64 off) = true := bne_iff_ne.mpr hne_bv
    have hsub_ne0 : BitVec.ofNat 64 (n - off) ≠ 0#64 := by bv_omega
    have hsub_beq0 : (BitVec.ofNat 64 (n - off) == 0#64) = false := beq_false_of_ne hsub_ne0
    have hsub_raw_beq0 : (BitVec.ofNat 64 n - BitVec.ofNat 64 off == 0#64) = false := beq_false_of_ne (by bv_omega)
    apply rustSepWP_cut (mid := rustStdPl02.base + 188#64); wp_sym_steps; refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    refine rustRunWithCstr_tail_loop rem (by omega) (by omega) hnz rfl (by simpa [arm64_norm] using hrun) (by simpa [arm64_norm] using hsp)
      (by simp [arm64_norm]) (by simp [arm64_norm, hlen]; bv_omega) fun sf hpcf hscf => ?_
    have hsc0 : RustScanPreserved s _ := ⟨by simpa [arm64_norm] using hrun, rfl, by simpa [arm64_norm] using hsp, rfl, rfl, by simp [RustScanRegs, arm64_norm], rfl⟩
    exact hcont sf hpcf (hsc0.trans hscf)

private theorem rustRunWithCstr_swar_loop [RustStdPlacement] {tgt : BitVec 64} {post : State → SepProp → Prop} :
    ∀ (fuel : Nat) {off n : Nat} {slicePtr : BitVec 64} {rem : List (BitVec 8)} {F : SepProp} {s : State},
      16 ≤ n → off ≤ n - 16 → n < 4096 → n - 16 - off < 16 * (fuel + 1) → rem.length = n - off → (∀ b ∈ rem, b ≠ 0#8) →
      s.pc = rustStdPl02.base + 128#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 off → s.readReg64 (.gpr 9#5) = 72340172838076672#64 →
      s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (n - 16) → s.readReg64 (.gpr 11#5) = 9259542123273814144#64 →
      s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n → s.readReg64 (.gpr 23#5) = slicePtr →
      (∀ sf : State, sf.pc = rustStdPl02.base + 204#64 → RustScanPreserved s sf →
        SepWP (rustStdPC02.rebase rustStdPl02.base (fun _ => none)) tgt sf (((slicePtr + BitVec.ofNat 64 off) ↦ₛ rem) ∗ F) post) →
      SepWP (rustStdPC02.rebase rustStdPl02.base (fun _ => none)) tgt s (((slicePtr + BitVec.ofNat 64 off) ↦ₛ rem) ∗ F) post
  | fuel, off, n, slicePtr, rem, F, s, hn16, hoff, hn, hfuel, hlen, hnz, hpc, hrun, hsp, hx8, hx9, hx10, hx11, hx21, hx23, hcont => by
    have hrem_eq : rem = rem.take 16 ++ rem.drop 16 := (List.take_append_drop 16 rem).symm
    have htlen : (rem.take 16).length = 16 := (by simp [hlen]; omega)
    obtain ⟨w0, w1, hw_eq, hw_pts⟩ := exists_unpack64_of_length_16 htlen
    have hnz16 : ∀ b ∈ unpack64 w0 ++ unpack64 w1, b ≠ 0#8 := (by rw [← hw_eq]; exact fun b hb => hnz b (List.mem_of_mem_take hb))
    have hbics : 9259542123273814144#64 &&& ~~~(((72340172838076672#64 - w0) ||| w0) &&& ((72340172838076672#64 - w1) ||| w1)) = 0#64 :=
      rustSwar_bics_eq_zero (fun b hb => hnz16 b (List.mem_append_left _ hb)) (fun b hb => hnz16 b (List.mem_append_right _ hb))
    have hadd16 : BitVec.ofNat 64 off + 16#64 = BitVec.ofNat 64 (off + 16) := by bv_omega
    have hptr16 : slicePtr + BitVec.ofNat 64 off + BitVec.ofNat 64 16 = slicePtr + BitVec.ofNat 64 (off + 16) := (by rw [BitVec.add_assoc]; congr 1)
    have hsplit : ((slicePtr + BitVec.ofNat 64 off) ↦ₛ rem) =
        (((slicePtr + BitVec.ofNat 64 off) ↦₆₄ w0) ∗ ((slicePtr + BitVec.ofNat 64 off + 8#64) ↦₆₄ w1) ∗
         ((slicePtr + BitVec.ofNat 64 (off + 16)) ↦ₛ rem.drop 16)) := by
      conv => lhs; rw [hrem_eq]
      rw [pointsToBytes_append, htlen, hw_pts, hptr16, sepConj_assoc]
    wp_conv_pre => rw [hsplit]
    by_cases hle : off + 16 ≤ n - 16
    · rcases fuel with _ | fuel'; · omega
      have hule : (BitVec.ofNat 64 (off + 16)).ule (BitVec.ofNat 64 (n - 16)) = true := by
        simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off + 16 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : n - 16 < 2 ^ 64)]; omega
      have hult : (BitVec.ofNat 64 (n - 16)).ult (BitVec.ofNat 64 (off + 16)) = false := by
        simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off + 16 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : n - 16 < 2 ^ 64)]; omega
      apply rustSepWP_cut (mid := rustStdPl02.base + 128#64); wp_sym_steps; refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      refine SepWP.weaken_pre (P' := ((slicePtr + BitVec.ofNat 64 (off + 16)) ↦ₛ rem.drop 16) ∗
        (((slicePtr + BitVec.ofNat 64 off) ↦₆₄ w0) ∗ ((slicePtr + BitVec.ofNat 64 off + 8#64) ↦₆₄ w1) ∗ F)) (by sep_entail) ?_
      refine rustRunWithCstr_swar_loop fuel' hn16 hle hn (by omega) (by simp [hlen]; omega)
        (fun b hb => hnz b (List.mem_of_mem_drop hb)) rfl (by simpa [arm64_norm] using hrun) (by simpa [arm64_norm] using hsp)
        (by simp [arm64_norm]) (by simp [arm64_norm, hx9]) (by simp [arm64_norm, hx10]) (by simp [arm64_norm, hx11])
        (by simp [arm64_norm, hx21]) (by simp [arm64_norm, hx23]) fun sf hpcf hscf => ?_
      have hsc0 : RustScanPreserved s _ := ⟨by simpa [arm64_norm] using hrun, rfl, by simpa [arm64_norm] using hsp, rfl, rfl, by simp [RustScanRegs, arm64_norm], rfl⟩
      refine SepWP.weaken_pre ?_ (hcont sf hpcf (hsc0.trans hscf)); rw [hsplit]; sep_entail
    · have hule : (BitVec.ofNat 64 (off + 16)).ule (BitVec.ofNat 64 (n - 16)) = false := by
        simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off + 16 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : n - 16 < 2 ^ 64)]; omega
      have hult : (BitVec.ofNat 64 (n - 16)).ult (BitVec.ofNat 64 (off + 16)) = true := by
        simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off + 16 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : n - 16 < 2 ^ 64)]; omega
      apply rustSepWP_cut (mid := rustStdPl02.base + 176#64); wp_sym_steps; refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      refine SepWP.weaken_pre (P' := ((slicePtr + BitVec.ofNat 64 (off + 16)) ↦ₛ rem.drop 16) ∗
        (((slicePtr + BitVec.ofNat 64 off) ↦₆₄ w0) ∗ ((slicePtr + BitVec.ofNat 64 off + 8#64) ↦₆₄ w1) ∗ F)) (by sep_entail) ?_
      refine rustRunWithCstr_tail_entry (by omega) hn (by omega) (by simp [hlen]; omega)
        (fun b hb => hnz b (List.mem_of_mem_drop hb)) rfl (by simpa [arm64_norm] using hrun) (by simpa [arm64_norm] using hsp)
        (by simp [arm64_norm]) (by simp [arm64_norm, hx21]) (by simp [arm64_norm, hx23]) fun sf hpcf hscf => ?_
      have hsc0 : RustScanPreserved s _ := ⟨by simpa [arm64_norm] using hrun, rfl, by simpa [arm64_norm] using hsp, rfl, rfl, by simp [RustScanRegs, arm64_norm], rfl⟩
      refine SepWP.weaken_pre ?_ (hcont sf hpcf (hsc0.trans hscf)); rw [hsplit]; sep_entail

private theorem rustRunWithCstr_open_pc [RustStdPlacement] :
    rustStdPl02.base + 220#64 + (rustStdPl02.ρ fileOpenCSym - rustStdPl02.base - 220#64) =
      rustStdPlacedLib.fnAddr rustStdMpl fileOpenCSym := by
  have hr : rustStdPl02.ρ fileOpenCSym = rustStdPlacedLib.fnAddr rustStdMpl fileOpenCSym := by
    rw [rustFnAddr_eq_base 1 fileOpenCSym (by decide) (by decide)]
    change rustStdPlacedLib.resolve rustStdMpl fileOpenCSym = rustStdMpl.base 1
    have hblk := lookupBlockSym_of_lookup (blocks := rustStdPlacedLib.blocks) (i := 1) (name := fileOpenCSym)
      (off := 0) (hi := by decide) (hnd := RustStdPlacement.placeable.symbols_nodup) (hl := by decide)
    simp [MultiPlacedLib.resolve, hblk]
  rw [hr]; bv_lin

theorem rustRunWithCstr_nul_scan [RustStdPlacement]
    {path : String} {retPtr slicePtr cstr envPtr optsPtr : BitVec 64} {b_nul : BitVec 8}
    {F : SepProp} {s : State} {post : State → SepProp → Prop}
    (hge24 : 24 ≤ (bytesOfString path).length) (hvalid : ValidCPath path)
    (hpc : s.pc = rustStdPl02.base + 72#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx19 : s.readReg64 (.gpr 19#5) = retPtr) (hx20 : s.readReg64 (.gpr 20#5) = cstr)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (bytesOfString path).length)
    (hx22 : s.readReg64 (.gpr 22#5) = envPtr) (hx23 : s.readReg64 (.gpr 23#5) = slicePtr)
    (hcont : ∀ sf : State, sf.pc = rustStdPlacedLib.fnAddr rustStdMpl fileOpenCSym → RustScanPreserved s sf →
      sf.readReg64 .x0 = retPtr → sf.readReg64 .x1 = cstr → sf.readReg64 .x2 = optsPtr →
      sf.readReg64 .lr = rustStdPl02.base + 224#64 →
      post sf ((slicePtr ↦ₛ bytesOfString path) ∗ (cstr ↦ₛ cstrBytes path) ∗ (envPtr ↦₆₄ optsPtr) ∗ F)) :
    SepWP (rustStdPC02.rebase rustStdPl02.base (fun _ => none)) (rustStdPlacedLib.fnAddr rustStdMpl fileOpenCSym) s
      ((slicePtr ↦ₛ bytesOfString path) ∗ (cstr ↦ₛ bytesOfString path) ∗
       ((cstr + BitVec.ofNat 64 (bytesOfString path).length) ↦₈ b_nul) ∗ (envPtr ↦₆₄ optsPtr) ∗ F) post := by
  let bs := bytesOfString path; obtain ⟨hlen_lt, hnz⟩ := hvalid.bytesOfString_spec
  change bs.length < 4096 at hlen_lt; change ∀ b ∈ bs, b ≠ 0#8 at hnz; change 24 ≤ bs.length at hge24
  let head := (rustHeadBV slicePtr).toNat; have hhead_lt : head < 8 := rustHeadBV_lt8 slicePtr
  have hhead_bv : rustHeadBV slicePtr = BitVec.ofNat 64 head := BitVec.eq_of_toNat_eq (by simp [head])
  have hbs_split : (slicePtr ↦ₛ bs) = ((slicePtr ↦ₛ bs.take head) ∗ ((slicePtr + BitVec.ofNat 64 head) ↦ₛ bs.drop head)) := by
    conv => lhs; rw [(List.take_append_drop head bs).symm]
    rw [pointsToBytes_append, List.length_take_of_le (by omega)]
  have h112 : ∀ s1 : State, s1.pc = rustStdPl02.base + 112#64 → RustScanPreserved s s1 → s1.readReg64 (.gpr 8#5) = BitVec.ofNat 64 head →
      SepWP (rustStdPC02.rebase rustStdPl02.base (fun _ => none)) (rustStdPlacedLib.fnAddr rustStdMpl fileOpenCSym) s1
        ((slicePtr ↦ₛ bs) ∗ (cstr ↦ₛ bs) ∗ ((cstr + BitVec.ofNat 64 bs.length) ↦₈ b_nul) ∗ (envPtr ↦₆₄ optsPtr) ∗ F) post := by
    intro s1 hpc1 hsc1 hx8_1; have hrun1 := hsc1.1; have hsp1 := hsc1.2.2.1
    have hx21_1 : s1.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length := hsc1.2.2.2.2.2.1.2.2.1.trans hx21
    have hx23_1 : s1.readReg64 (.gpr 23#5) = slicePtr := hsc1.2.2.2.2.2.1.2.2.2.2.1.trans hx23
    apply rustSepWP_cut (mid := rustStdPl02.base + 128#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun1) ?_
    wp_conv_pre => rw [hbs_split]
    refine SepWP.weaken_pre (P' := ((slicePtr + BitVec.ofNat 64 head) ↦ₛ bs.drop head) ∗
      ((slicePtr ↦ₛ bs.take head) ∗ (cstr ↦ₛ bs) ∗ ((cstr + BitVec.ofNat 64 bs.length) ↦₈ b_nul) ∗ (envPtr ↦₆₄ optsPtr) ∗ F)) (by sep_entail) ?_
    have hsub16 : BitVec.ofNat 64 bs.length - 16#64 = BitVec.ofNat 64 (bs.length - 16) := by bv_omega
    refine rustRunWithCstr_swar_loop bs.length (by omega) (by omega) hlen_lt (by omega)
      (by simp) (fun b hb => hnz b (List.mem_of_mem_drop hb)) rfl
      (by simpa [arm64_norm] using hrun1) (by simpa [arm64_norm] using hsp1)
      (by simp [arm64_norm, hx8_1]) (by simp [arm64_norm]) (by simp only [arm64_norm]; exact hsub16)
      (by simp [arm64_norm]) (by simp [arm64_norm, hx21_1]) (by simp [arm64_norm, hx23_1]) fun s2 hpc2 hsc2 => ?_
    have hsc12 : RustScanPreserved s s2 := hsc1.trans (RustScanPreserved.trans
      ⟨by simpa [arm64_norm] using hrun1, rfl, by simpa [arm64_norm] using hsp1, rfl, rfl, by simp [RustScanRegs, arm64_norm], rfl⟩ hsc2)
    have hx19_2 : s2.readReg64 (.gpr 19#5) = retPtr := hsc12.2.2.2.2.2.1.1.trans hx19
    have hx20_2 : s2.readReg64 (.gpr 20#5) = cstr := hsc12.2.2.2.2.2.1.2.1.trans hx20
    have hx21_2 : s2.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length := hsc12.2.2.2.2.2.1.2.2.1.trans hx21
    have hx22_2 : s2.readReg64 (.gpr 22#5) = envPtr := hsc12.2.2.2.2.2.1.2.2.2.1.trans hx22
    have hrun2 := hsc12.1; have hsp2 := hsc12.2.2.1; wp_sym_steps
    refine SepWP.weaken_pre ?_ (SepWP.done rustRunWithCstr_open_pc (by simpa [arm64_norm] using hrun2) <|
      hcont _ rustRunWithCstr_open_pc
        (hsc12.trans ⟨by simpa [arm64_norm] using hrun2, rfl, by simpa [arm64_norm] using hsp2, rfl, rfl, by simp [RustScanRegs, arm64_norm], rfl⟩)
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
    rw [show (cstr ↦ₛ cstrBytes path) = ((cstr ↦ₛ bs) ∗ ((cstr + BitVec.ofNat 64 bs.length) ↦₈ 0#8)) by
      rw [cstrBytes_eq_bytesOfString, pointsToBytes_append, pointsToBytes_singleton], hbs_split]; sep_entail
  by_cases h0 : head = 0
  · have hzbv : rustHeadBV slicePtr = 0#64 := (by rw [hhead_bv, h0])
    have hal_eq : rustAlign8 slicePtr = slicePtr := (by dsimp [rustHeadBV] at hzbv; bv_omega)
    apply rustSepWP_cut (mid := rustStdPl02.base + 112#64); wp_sym_steps
    exact SepWP.done rfl (by simpa [arm64_norm] using hrun) (h112 _ rfl
      ⟨by simpa [arm64_norm] using hrun, rfl, by simpa [arm64_norm] using hsp, rfl, rfl, by simp [RustScanRegs, arm64_norm], rfl⟩
      (by simp [rustHeadBV] at hzbv; simp [arm64_norm, h0]))
  · have hnzbv : rustHeadBV slicePtr ≠ 0#64 := (by rw [hhead_bv]; bv_omega)
    have hal_ne : rustAlign8 slicePtr ≠ slicePtr := (by intro he; apply hnzbv; dsimp [rustHeadBV]; rw [he]; simp)
    have hal_beq : (rustAlign8 slicePtr == slicePtr) = false := beq_false_of_ne hal_ne
    have hzbv_beq : (rustHeadBV slicePtr == 0#64) = false := beq_false_of_ne hnzbv
    have hneg : slicePtr - rustAlign8 slicePtr = 0#64 - BitVec.ofNat 64 head := (by rw [← hhead_bv]; dsimp [rustHeadBV]; bv_lin)
    apply rustSepWP_cut (mid := rustStdPl02.base + 96#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_; wp_conv_pre => rw [hbs_split]
    refine SepWP.weaken_pre (P' := (slicePtr ↦ₛ bs.take head) ∗
      (((slicePtr + BitVec.ofNat 64 head) ↦ₛ bs.drop head) ∗ (cstr ↦ₛ bs) ∗
       ((cstr + BitVec.ofNat 64 bs.length) ↦₈ b_nul) ∗ (envPtr ↦₆₄ optsPtr) ∗ F)) (by sep_entail) ?_
    refine rustRunWithCstr_head_loop head (by omega) (by omega) (by simp; omega)
      (fun b hb => hnz b (List.mem_of_mem_take hb)) rfl (by simpa [arm64_norm] using hrun) (by simpa [arm64_norm] using hsp)
      (by simp only [arm64_norm]; exact hneg) (by simp [arm64_norm]) fun s1 hpc1 hsc1 hx8_1 => ?_
    have hsc0 : RustScanPreserved s _ :=
      ⟨by simpa [arm64_norm] using hrun, rfl, by simpa [arm64_norm] using hsp, rfl, rfl, by simp [RustScanRegs, arm64_norm], rfl⟩
    refine SepWP.weaken_pre ?_ (h112 s1 hpc1 (hsc0.trans hsc1) (hx8_1.trans (by simp only [arm64_norm])))
    rw [hbs_split]; sep_entail

end

end VerifiedLibraries.RustStd
