/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinLoop
public import LibsignalBinary.Proofs.SignalSession.CliIo.FinishGrow

/-!
# Placement-Generic Proof of `signal_session_io::read_stdin`

Proves `cliIoReadStdin_ok` against `cliIoReadStdinSpec` for `signalSessionIoMultiLib` block `0`
(`436` B, `4224`-B stack frame): reads `stdin` up to `1,048,576` bytes (`2^20`) into `Ok(rem)` under
the doubling schedule `cliIoReadCaps 8 rem.length`, deallocates and returns `Err(())` when input
exceeds `1 MiB`, and propagates allocator OOM via `cliIoStdinOom`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinProof

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open VerifiedLibraries.RustStd (
  RustStdAlloc StdErrnoCell stdErrnoAddr
  vecHeader ioVecBuf
  allocAllocShimSpec rustStdAllocSpec rustStdReallocSpec rustStdDeallocSpec
  AllocSeqFits allocSeqPool
)
open VerifiedLibraries.RustStd.Io (allocCallPreserved_of_seg)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  cliIoResolve_eq_base cliIoReadStdin_lookup
  sepWP_seg_cliIo_block_pure
  cliIoReadStdinSym cliIoReadSym cliIoMemcpySym
  cliIoRustAllocSym cliIoRustReallocSym cliIoRustDeallocSym cliIoRustNoAllocShimSym
  cliIoPl00 cliIoPC00 cliIoBlockNoSvc0_00
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  ExternPreservesOracleSymtab cliIo_sepWP_carry_oracle_symtab
  cliIoStdinCap cliIoReadCaps cliIoFinalCap
  allocSeqPool_cliIoReadCaps_zero
  wantBytes
  cliIoSavedRegs12 memRegion4096_split_probe32 memRegion4096_refold_probe32
  cliIoReadStdin_stack_split ioVecBuf_zero_intro
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin (muslReadStdin32Spec)
open LibsignalBinary.Proofs.SignalSession.CliIo.FinishGrow (cliIoFinishGrow_ok_withCodeLoaded)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinSteps (cliIo0_lt)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinLoop (
  cliIoStdinLoopResult cliIoStdinOom cliIoReadStdin_loop
)

/-- State-field preservation across `signal_session_io::read_stdin` / `read_file`
    (all non-`fs` architectural/OS fields preserved). -/
def CliIoCallPreserved (s0 sf : State) : Prop :=
  sf.trace = s0.trace ∧
    sf.sigActions = s0.sigActions ∧
    sf.tpidrEl0 = s0.tpidrEl0 ∧
    sf.brkStart = s0.brkStart ∧
    sf.oracle = s0.oracle ∧
    sf.symtab = s0.symtab

/-- Hoare contract for `signal_session_io::read_stdin() -> Result<Vec<u8>, IoError>` (`x8 = sret`).
    Ghost argument: `(sret, d0, lb, lk)`. -/
def cliIoReadStdinSpec {oom : State → State → Prop} (A : RustStdAlloc oom)
    (stackBytes : Nat) : Spec (BitVec 64 × FdEntry × Nat × Nat) where
  pre := fun (sret, d0, lb, lk) s0 =>
    ⌜4256 + Rust.hookStack ≤ stackBytes ∧
      stackBytes ≤ 2 ^ 64 ∧
      stackBytes ≤ s0.sp.toNat ∧
      s0.sp.toNat ≤ Arm64.USER_VA_LIMIT ∧
      s0.readReg64 .x8 = sret ∧
      s0.fs.fds 0#64 = some d0 ∧
      d0.kind = .stdio ∧
      d0.accMode.canRead = true ∧
      AllocSeqFits A 1 lb lk (cliIoReadCaps 8 (s0.fs.stdin.drop d0.offset).length)⌝ ∗
    (stackAt s0.sp stackBytes ∗
      memRegion sret 24 ∗
      StdErrnoCell s0.tpidrEl0 ∗
      A.pool lb lk s0)
  post := fun (sret, d0, lb, lk) s0 sf =>
    ⌜CliIoCallPreserved s0 sf⌝ ∗
      (stackAt s0.sp stackBytes ∗
        cliIoStdinLoopResult A sret d0 lb lk s0 sf ∗
        StdErrnoCell s0.tpidrEl0)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun (_, d0, _, _) s0 sf => cliIoStdinOom oom d0 s0 sf

section
arm64_proof_prelude

/-- Split a `24`-byte `sret` region into `∃∗ v0 v1 v2, vecHeader sret v0 v1 v2`. -/
theorem memRegion24_eq_exists_vecHeader (sret : BitVec 64) :
    memRegion sret 24 = ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      vecHeader sret v0 v1 v2 := by
  rw [show (24 : Nat) = 8 * 3 by decide, memRegion_cells sret 3 (by decide)]
  dsimp only [cells, vecHeader]
  simp only [sepConj_emp, sepExists_sepConj_right, bv_lin_norm]

private theorem setFd_offset_add_zero {fs : FsState} {fd : BitVec 64} {d0 : FdEntry}
    (h : fs.fds fd = some d0) :
    fs = fs.setFd fd (some { d0 with offset := d0.offset + 0 }) := by
  have hd : ({ d0 with offset := d0.offset + 0 } : FdEntry) = d0 := by
    cases d0; simp
  rw [hd]
  cases fs
  dsimp only [FsState.setFd] at h ⊢
  congr
  funext k
  by_cases hkf : k = fd
  · subst hkf; simp [h]
  · simp [beq_false_of_ne hkf]

/-- Placement-generic proof of `signal_session_io::read_stdin` (`block[0]`). -/
theorem cliIoReadStdin_ok {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stackBytes : Nat}
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext0 : CliIoBlockNoExtern mpl P 0)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadStdin32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      allocAllocShimSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustStdAllocSpec A))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustStdReallocSpec A))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustStdDeallocSpec A)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl (cliIoReadStdinSpec A stackBytes)) := by
  have hfg := cliIoFinishGrow_ok_withCodeLoaded A hpl hext4 hshim halloc hrealloc
  letI : CliIoPlacement := ⟨mpl, hpl⟩
  rw [cliIoResolve_eq_base hpl 0 cliIoReadStdinSym cliIo0_lt cliIoReadStdin_lookup]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨sret, d0, lb, lk⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadStdinSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hlo, hhi, hsp_lo, hsp_va, hx8, hfds0, hkind, hcanr, hfits⟩, hmem⟩
  refine ⟨_, hmem, ?_⟩
  apply cliIo_sepWP_carry_oracle_symtab hsvc hext_os
  wp_conv_pre =>
    dsimp only [StdErrnoCell]
    rw [cliIoReadStdin_stack_split s0.sp (by omega) hhi,
      memRegion24_eq_exists_vecHeader sret,
      memRegion4096_split_probe32 (s0.sp - 4224#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, bv_lin_norm]
  refine SepWP.exists_elim fun ev0 =>
    SepWP.exists_elim fun v0 => SepWP.exists_elim fun v1 =>
    SepWP.exists_elim fun v2 =>
    SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 =>
    SepWP.exists_elim fun r0 => SepWP.exists_elim fun r1 =>
    SepWP.exists_elim fun r2 => SepWP.exists_elim fun r3 =>
    SepWP.exists_elim fun r4 => SepWP.exists_elim fun r5 =>
    SepWP.exists_elim fun r6 => SepWP.exists_elim fun r7 =>
    SepWP.exists_elim fun r8 => SepWP.exists_elim fun r9 =>
    SepWP.exists_elim fun r10 => SepWP.exists_elim fun r11 =>
    SepWP.exists_elim fun w_probe => ?_
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl0
    (mid := cliIoPl00.base + 72#64)
  intro s1' hcpu1_0
  have hcpu1 := hcpu1_0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc1' : s1'.pc = cliIoPl00.base := hcpu1.pc_eq.trans hpc
  have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
  have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
  have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
  have hx8_1' : s1'.readReg64 .x8 = sret := (hcpu1.readReg64 .x8).trans hx8
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1')
    fun sl hcpu_l0 hcl_l hnsp_l hsym_l => ?_
  have hcpu_l := hcpu_l0.1
  have ⟨hacp_0l, hpool_0l⟩ :=
    allocCallPreserved_of_seg hcpu1_0 hcpu_l0 hnsp_l hsym_l
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_0l : A.pool lb lk s0 = A.pool lb lk sl :=
    (A.pool_transport _ _ s0 sl hpool_0l).symm
  have hpc_l : sl.pc = cliIoPl00.base + 72#64 := hcpu_l.pc_eq.trans (by simp [arm64_norm])
  have hrun_l : sl.status = .Running := hcpu_l.status_eq.trans hrun1'
  have hsp_l : sl.sp = s0.sp - 4224#64 :=
    hcpu_l.sp_eq.trans (by simp [arm64_norm])
  have hfs_l : sl.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + 0 }) :=
    hacp_0l.1.trans (setFd_offset_add_zero hfds0)
  have hpool0 : allocSeqPool A 1 lb lk (cliIoReadCaps 8 0) = (lb, lk) :=
    allocSeqPool_cliIoReadCaps_zero A 8 lb lk
  refine SepWP.weaken_pre ?_
    (cliIoReadStdin_loop A hext0 hread hmemcpy hfg hdealloc
      (sret := sret) (v0 := v0) (v1 := v1) (v2 := v2)
      hlo hhi hsp_lo hsp_va hsp0 hkind hcanr hfits
      (fun sf _hpc_f _hrun_f hsp_f hcs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent horc_f hsym_f =>
        have hpres : CliIoCallPreserved s0 sf := ⟨htr_f, hsig_f, htp_f, hbs_f, horc_f, hsym_f⟩
        ⟨fun hm_out => by
          rw [pure_sepConj_of_true hpres]
          exact Satisfies.mono (sepConj_mono_left hent) hm_out,
        hsp_f, hcs_f⟩)
      (cliIoStdinCap + 1) sl 1#64 st0 st1 st2 st3 0 0 lb lk
      (Nat.le_refl _) (Nat.zero_le _) (fun _ => Nat.dvd_zero 4096) rfl
      (by rw [hpool0]) (by rw [hpool0])
      hcl_l hpc_l hrun_l hsp_l
      (by rw [hcpu_l.readReg64]; simp only [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp [arm64_norm])
      (by rw [hcpu_l.readReg64]; simp only [arm64_norm])
      (hcpu_l.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs))
      hfs_l hacp_0l.2.1 hacp_0l.2.2.1 hacp_0l.2.2.2.1 hacp_0l.2.2.2.2.1)
  have hrefold_probe :
      memRegion (s0.sp - 4224#64) 32 ∗ ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 4184#64) 4056 ⊢ memRegion (s0.sp - 4224#64) 4096 := by
    simpa only [bv_lin_norm] using memRegion4096_refold_probe32 (s0.sp - 4224#64) 0#64
  have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ⊢ StdErrnoCell s0.tpidrEl0 :=
    Entails.sepExists_right ev0 (Entails.refl _)
  have hvec0 : emp ⊢ ioVecBuf A (BitVec.ofNat 64 0) 1#64 ((s0.fs.stdin.drop d0.offset).take 0) :=
    ioVecBuf_zero_intro A (ptr := 1#64) (by decide)
  rw [hpool_eq_0l,
    hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
    hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 27#5),
    hcpu1.readReg64 (.gpr 26#5), hcpu1.readReg64 (.gpr 25#5),
    hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
    hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
    hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5)]
  dsimp only [cliIoSavedRegs12]
  simp only [bv_lin_norm]
  let SavedAndRest : SepProp :=
    stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
      (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
      vecHeader sret v0 v1 v2 ∗ A.pool lb lk sl
  have hwith_vec :
      SavedAndRest ⊢ SavedAndRest ∗
        ioVecBuf A (BitVec.ofNat 64 0) 1#64 ((s0.fs.stdin.drop d0.offset).take 0) := by
    simpa only [sepConj_emp] using sepConj_mono_right (P := SavedAndRest) hvec0
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono hrefold_probe (sepConj_mono hwith_vec hev_cell))
      (by dsimp only [SavedAndRest]; sep_entail))
  dsimp only [SavedAndRest]; sep_entail

end

end LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinProof
