/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.StdStartup.TopInit
import ProofLib.StdStartup.StartupCompose

/-!
# Whole-ELF Startup and Exit Composition

Composes `_start`, `userMain`, and post-`main` cleanup through `exit_group` under `Program.pureMem`
for static AArch64 `musl` + Rust `std` `ET_EXEC` binaries matching `StdBinaryLayout`, covering both
`() -> ()` (`stdElfImage_runsTo_unit`, `stdElf_runsTo_unit`) and `() -> ExitCode`
(`stdElfImage_runsTo_exitCode`, `stdElf_runsTo_exitCode`) entry points.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib.StdStartup

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection StdBinaryLayout

private theorem swap_stk384 (S A B Rest : SepProp) :
    S ∗ (A ∗ B ∗ Rest) ⊢ A ∗ B ∗ S ∗ Rest := by
  sep_entail

private theorem reorder_musl_exit (C E B80 S80 M : SepProp) :
    C ∗ E ∗ (B80 ∗ S80) ∗ M ⊢ M ∗ S80 ∗ (C ∗ E ∗ B80) := by
  sep_entail

private theorem signExtend32_zeroExtend8 (b : BitVec 8) :
    (((b.zeroExtend 64).truncate 32).signExtend 64) = b.zeroExtend 64 := by
  bv_bits

private def stdPostMainCleanupFrozen (L : StdBinaryLayout) (haveLse : BitVec 8)
    (sp_cmain saved_fp : BitVec 64) : SepProp :=
  let ret_cmain := if L.hasArgcGlobal then L.cMainAddr + 0x208#64 else L.cMainAddr + 0x1f4#64
  ((sp_cmain - 0x10#64) ↦₆₄ (sp_cmain + 0x20#64)) ∗
  ((sp_cmain - 0x08#64) ↦₆₄ ret_cmain) ∗
  stackAt (sp_cmain + 0x20#64) 32 ∗
  ((sp_cmain + 0x20#64) ↦₆₄ saved_fp) ∗
  ((sp_cmain + 0x28#64) ↦₆₄ (L.libcStartMainStage2Addr + 0x38#64)) ∗
  stackAt (sp_cmain + 0x60#64) 48 ∗
  StdCleanupOnceGlobals L haveLse 3#32 (List.replicate 56 0#8) ∗
  (L.exitingThreadIdAddr ↦₆₄ 0#64) ∗
  StdMuslExitGlobals L 0#8

private theorem cleanup_and_exit_runsTo {P : Program} {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {post : ProcessOutcome → Prop} {oom : State → Prop}
    {s0 s_ret : State} {haveLse : BitVec 8} {sp_cmain saved_fp exitCode : BitVec 64} {R_end : SepProp}
    (c : StdStartupCode P L) (lf : LayoutImageFacts L)
    (hload : img.loadState inputs = .ok s0) (hL0 : P.CodeLoaded s0.mem)
    (hst_to_ret : Steps P s0 s_ret)
    (hpc_ret : s_ret.pc = L.beginShortBacktraceAddr + 0x0c#64)
    (hrun_ret : s_ret.status = .Running)
    (hsp_ret : s_ret.sp = sp_cmain - 0x10#64) (hsp_al_ret : s_ret.spAligned = true)
    (hsp_lo_cm : 400 ≤ sp_cmain.toNat)
    (h_argc_ret : L.hasArgcGlobal = L.userMainReturnsExitCode)
    (hexit_eq : if L.userMainReturnsExitCode
      then exitCode = ((s_ret.readReg32 .x0).truncate 8).zeroExtend 64
      else exitCode = 0#64)
    (hpost : post (ProcessOutcome.ofState exitCode s_ret))
    (hm_ret : s_ret.mem ⊨ ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
      (stackAt (sp_cmain - 0x10#64) 384 ∗
       StdPostMainCleanup L haveLse sp_cmain saved_fp ∗ R_end)) :
    ElfImageRunsTo img inputs post oom := by
  have hm_frz := Satisfies.of_bupd_frame_left (pointsTo8_freeze_ro (L.libcAddr + 3#64) 0#8) hm_ret
  have hm_full : s_ret.mem ⊨ (stackAt (sp_cmain - 0x10#64) 384 ∗
      stdPostMainCleanupFrozen L haveLse sp_cmain saved_fp) ∗ R_end := by
    refine Satisfies.mono ?_ hm_frz
    dsimp only [StdPostMainCleanup, stdPostMainCleanupFrozen,
      StdMuslExitGlobalsNoNeedLocks, StdMuslExitGlobals]
    sep_frame
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc_cas8r, hc_cas4a, hc_cas8a, hc_swp4r⟩ :=
    unpack_extra_chunks c.extra
  have hAtomics := stdOutlineAtomics_of_hasInstrs P L hc_cas8r hc_cas4a hc_cas8a hc_swp4r
  have hwp_exit : SepWP P (L.sysExitAddr + 0x0c#64) s_ret
      (stackAt (sp_cmain - 0x10#64) 384 ∗ stdPostMainCleanupFrozen L haveLse sp_cmain saved_fp)
      (fun s_svc _ => s_svc.readReg64 .x8 = 94#64 ∧ s_svc.readReg64 .x0 = exitCode ∧
        s_svc.fs = s_ret.fs ∧ s_svc.trace = s_ret.trace) := by
    dsimp only [stdPostMainCleanupFrozen]
    rw [h_argc_ret]
    have hcm_code := c.cleanup.cMain
    cases h_ret : L.userMainReturnsExitCode
    · simp only [h_ret, Bool.false_eq_true, ↓reduceIte] at hcm_code hexit_eq ⊢
      apply SepWP.weaken_pre (swap_stk384 _ _ _ _)
      refine cMain_post_unit_wp hcm_code c.cleanup.onceCall c.cleanup.cleanup c.cleanup.stdout
        c.cleanup.errnoLoc hAtomics.cas4Acq_ok hAtomics.swp4Rel_ok hAtomics.cas8Acq_ok
        hpc_ret hrun_ret hsp_ret hsp_al_ret hsp_lo_cm lf.al_clean lf.al_outOnce lf.al_exiting
        fun sf hpc_f hrun_f hsp_f hsp_al_f hx0_f hstd_f => ?_
      rw [stackAt_split_bottom (sp_cmain + 0x60#64) 80 416 (by decide)]
      apply SepWP.weaken_pre (reorder_musl_exit _ _ _ _ _)
      refine muslExit_to_svc_wp c.cleanup.muslExit hpc_f hrun_f hsp_f hsp_al_f lf.finiArray_bnd
        lf.al_got lf.al_fini lf.al_ofl lf.al_stdin lf.al_stdout lf.al_stderrUsed lf.al_stderrFile
        lf.stderrFile_nz fun s_svc hpc_s hrun_s _ _ hx8_s hx0_s hstd_s => ?_
      apply SepWP.done hpc_s hrun_s
      have hstd_all := hstd_f.trans hstd_s
      refine ⟨hx8_s, ?_, hstd_all.1, hstd_all.2.1⟩
      rw [hx0_s, State.readReg32, hx0_f, hexit_eq]; rfl
    · simp only [h_ret, ↓reduceIte] at hcm_code hexit_eq ⊢
      apply SepWP.weaken_pre (swap_stk384 _ _ _ _)
      refine cMain_post_exitCode_wp hcm_code c.cleanup.onceCall c.cleanup.cleanup c.cleanup.stdout
        c.cleanup.errnoLoc hAtomics.cas4Acq_ok hAtomics.swp4Rel_ok hAtomics.cas8Acq_ok
        hpc_ret hrun_ret hsp_ret hsp_al_ret hsp_lo_cm lf.al_clean lf.al_outOnce lf.al_exiting
        fun sf hpc_f hrun_f hsp_f hsp_al_f hx0_f hstd_f => ?_
      rw [stackAt_split_bottom (sp_cmain + 0x60#64) 80 416 (by decide)]
      apply SepWP.weaken_pre (reorder_musl_exit _ _ _ _ _)
      refine muslExit_to_svc_wp c.cleanup.muslExit hpc_f hrun_f hsp_f hsp_al_f lf.finiArray_bnd
        lf.al_got lf.al_fini lf.al_ofl lf.al_stdin lf.al_stdout lf.al_stderrUsed lf.al_stderrFile
        lf.stderrFile_nz fun s_svc hpc_s hrun_s _ _ hx8_s hx0_s hstd_s => ?_
      apply SepWP.done hpc_s hrun_s
      have hstd_all := hstd_f.trans hstd_s
      refine ⟨hx8_s, ?_, hstd_all.1, hstd_all.2.1⟩
      rw [hx0_s, State.readReg32, hx0_f, hexit_eq, signExtend32_zeroExtend8]
  obtain ⟨s_svc, hst_exit, hres | ⟨_, hfalse⟩⟩ :=
    SepWP.to_reaches_pc hwp_exit hm_full (hst_to_ret.codeLoaded hL0)
  · obtain ⟨hpc_s, hrun_s, _, _, hx8_s, hx0_s, hfs_s, htr_s⟩ := hres
    have hst_all : Steps P s0 s_svc := hst_to_ret.trans hst_exit
    have hst_pure : Steps Program.pureMem s0 s_svc := hst_all.to_pureMem c.no_hooks c.svc_eq
    have hfetch_s : Program.pureMem.fetchMem s_svc.mem (L.sysExitAddr + 0x0c#64) =
        some (.system false 0#16) := by
      rw [← c.no_hooks.fetchMem_eq_pureMem]
      exact Program.fetchMem_of_fetch (hst_all.codeLoaded hL0)
        (MuslExitCode.fetch_sysExit_svc c.cleanup.muslExit)
    obtain ⟨sf_final, hst_one, hterm⟩ := step_exit_group_exitsWith hpc_s hrun_s hx8_s hfetch_s
    exact ElfImageRunsTo.of_exitsWith hload ⟨sf_final, hst_pure.trans hst_one, hterm⟩
      (by simpa only [ProcessOutcome.ofState, hx0_s, hfs_s, htr_s] using hpost)
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-! ## Whole-ELF Composition Theorems -/

/-- Whole-`ElfImage` correctness under `Program.pureMem` for a `() -> ()` Rust `std` binary
    (`L.userMainReturnsExitCode = false`, exiting with code `0#64`). -/
theorem stdElfImage_runsTo_unit {P : Program} {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {post : ProcessOutcome → Prop}
    {oom : State → Prop}
    (c : StdStartupCode P L)
    (hmatch : L.MatchesImage img = true)
    (hvalid : inputs.Valid)
    (h_ret : L.userMainReturnsExitCode = false := by rfl)
    (h_argc : L.hasArgcGlobal = false := by rfl)
    (hrx : L.rxProgram img = P := by rfl)
    (hMain : ∀ (s0 s_main : State) (R_cleanup : SepProp),
      img.loadState inputs = .ok s0 →
      StdUserMainState P L img inputs s0 s_main →
      (s_main.mem ⊨ StdUserMainPre L img inputs s_main ∗ R_cleanup) →
      ∃ (P_call : SepProp) (oomSep : State → SepProp),
        (s_main.mem ⊨ P_call ∗ R_cleanup) ∧
        (∀ sf, sf.status = .OutOfMemory → (sf.mem ⊨ oomSep sf ∗ R_cleanup) → oom sf) ∧
        SepWP P (L.beginShortBacktraceAddr + 0x0c#64) s_main P_call
          (fun s_ret Pf =>
            s_ret.sp = s_main.sp ∧
            post (ProcessOutcome.ofState 0#64 s_ret) ∧
            ∃ R_ret : SepProp, Pf ⊢ stackAt s_main.sp 384 ∗ ((L.libcAddr + 3#64) ↦₈ 0#8) ∗ R_ret)
          oomSep) :
    ElfImageRunsTo img inputs post oom := by
  obtain ⟨s0, s_main, saved_fp, R_unused, hload, hL0, lf, hst1, hs_main, hm_main⟩ :=
    startup_to_userMain c hmatch hvalid hrx
  let haveLse : BitVec 8 := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8
  let sp_cmain := (StackLayout.of img inputs).sp0 - 0x90#64
  obtain ⟨P_call, oomSep, hm_call, hoom_imp, hwp_main⟩ :=
    hMain s0 s_main (StdPostMainCleanup L haveLse sp_cmain saved_fp ∗ R_unused)
      hload hs_main hm_main
  obtain ⟨s_ret, hst2, hres | ⟨hoom_st, hoom_sat⟩⟩ :=
    SepWP.to_reaches_pc hwp_main hm_call hs_main.codeLoaded
  · obtain ⟨hpc_r, hrun_r, Pf, hm_ret, hsp_r, hpost_r, R_ret, hent_ret⟩ := hres
    have hsp_r_cm : s_ret.sp = sp_cmain - 0x10#64 := by
      rw [hsp_r, hs_main.sp_eq]; dsimp only [sp_cmain]; bv_lin
    have hsp_al_r : s_ret.spAligned = true := by
      simp only [State.spAligned, hsp_r]; exact hs_main.spAligned_eq
    have hsp_lo_cm : 400 ≤ sp_cmain.toNat := by
      have hge := hs_main.initInfo.sp0_headroom.2
      change 400 ≤ ((StackLayout.of img inputs).sp0 - 0x90#64).toNat
      rw [BitVec.toNat_sub_of_le (by change 144 ≤ (StackLayout.of img inputs).sp0.toNat; omega)]
      change 400 ≤ (StackLayout.of img inputs).sp0.toNat - 144; omega
    have hm_ret' : s_ret.mem ⊨ ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
        (stackAt (sp_cmain - 0x10#64) 384 ∗
         StdPostMainCleanup L haveLse sp_cmain saved_fp ∗ (R_ret ∗ R_unused)) := by
      have hm1 := Satisfies.mono (sepConj_mono_left hent_ret) hm_ret
      rw [← hsp_r, hsp_r_cm] at hm1; revert hm1; sep_frame
    exact cleanup_and_exit_runsTo c lf hload hL0 (hst1.trans hst2) hpc_r hrun_r hsp_r_cm
      hsp_al_r hsp_lo_cm (h_argc.trans h_ret.symm) (by simp [h_ret]) hpost_r hm_ret'
  · exact ElfImageRunsTo.of_oom hload ((hst1.trans hst2).to_pureMem c.no_hooks c.svc_eq)
      hoom_st (hoom_imp s_ret hoom_st hoom_sat)

/-- Whole-ELF correctness (`ElfRunsTo elfBytes pre post oom`) for a `() -> ()` Rust `std` binary. -/
theorem stdElf_runsTo_unit {P : Program} {L : StdBinaryLayout}
    {elfBytes : List (BitVec 8)} {img : ElfImage}
    {pre : ProcessInputs → Prop} {post : ProcessInputs → ProcessOutcome → Prop}
    {oom : ProcessInputs → State → Prop}
    (c : StdStartupCode P L)
    (hparse : ElfImage.parse elfBytes = .ok img)
    (hmatch : L.MatchesImage img = true)
    (hvalid : ∀ inputs, pre inputs → inputs.Valid)
    (h_ret : L.userMainReturnsExitCode = false := by rfl)
    (h_argc : L.hasArgcGlobal = false := by rfl)
    (hrx : L.rxProgram img = P := by rfl)
    (hMain : ∀ inputs, pre inputs → ∀ (s0 s_main : State) (R_cleanup : SepProp),
      img.loadState inputs = .ok s0 →
      StdUserMainState P L img inputs s0 s_main →
      (s_main.mem ⊨ StdUserMainPre L img inputs s_main ∗ R_cleanup) →
      ∃ (P_call : SepProp) (oomSep : State → SepProp),
        (s_main.mem ⊨ P_call ∗ R_cleanup) ∧
        (∀ sf, sf.status = .OutOfMemory → (sf.mem ⊨ oomSep sf ∗ R_cleanup) → oom inputs sf) ∧
        SepWP P (L.beginShortBacktraceAddr + 0x0c#64) s_main P_call
          (fun s_ret Pf =>
            s_ret.sp = s_main.sp ∧
            post inputs (ProcessOutcome.ofState 0#64 s_ret) ∧
            ∃ R_ret : SepProp, Pf ⊢ stackAt s_main.sp 384 ∗ ((L.libcAddr + 3#64) ↦₈ 0#8) ∗ R_ret)
          oomSep) :
    ElfRunsTo elfBytes pre post oom :=
  ElfRunsTo.intro hparse fun inputs hi =>
    stdElfImage_runsTo_unit c hmatch (hvalid inputs hi) h_ret h_argc hrx (hMain inputs hi)

/-- Whole-`ElfImage` correctness under `Program.pureMem` for a `() -> ExitCode` Rust `std` binary
    (`L.userMainReturnsExitCode = true`, exiting with `((s_ret.readReg32 .x0).truncate 8).zeroExtend 64`). -/
theorem stdElfImage_runsTo_exitCode {P : Program} {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {post : ProcessOutcome → Prop}
    {oom : State → Prop}
    (c : StdStartupCode P L)
    (hmatch : L.MatchesImage img = true)
    (hvalid : inputs.Valid)
    (h_ret : L.userMainReturnsExitCode = true := by rfl)
    (h_argc : L.hasArgcGlobal = true := by rfl)
    (hrx : L.rxProgram img = P := by rfl)
    (hMain : ∀ (s0 s_main : State) (R_cleanup : SepProp),
      img.loadState inputs = .ok s0 →
      StdUserMainState P L img inputs s0 s_main →
      (s_main.mem ⊨ StdUserMainPre L img inputs s_main ∗ R_cleanup) →
      ∃ (P_call : SepProp) (oomSep : State → SepProp),
        (s_main.mem ⊨ P_call ∗ R_cleanup) ∧
        (∀ sf, sf.status = .OutOfMemory → (sf.mem ⊨ oomSep sf ∗ R_cleanup) → oom sf) ∧
        SepWP P (L.beginShortBacktraceAddr + 0x0c#64) s_main P_call
          (fun s_ret Pf =>
            s_ret.sp = s_main.sp ∧
            post (ProcessOutcome.ofState (((s_ret.readReg32 .x0).truncate 8).zeroExtend 64) s_ret) ∧
            ∃ R_ret : SepProp, Pf ⊢ stackAt s_main.sp 384 ∗ ((L.libcAddr + 3#64) ↦₈ 0#8) ∗ R_ret)
          oomSep) :
    ElfImageRunsTo img inputs post oom := by
  obtain ⟨s0, s_main, saved_fp, R_unused, hload, hL0, lf, hst1, hs_main, hm_main⟩ :=
    startup_to_userMain c hmatch hvalid hrx
  let haveLse : BitVec 8 := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8
  let sp_cmain := (StackLayout.of img inputs).sp0 - 0x90#64
  obtain ⟨P_call, oomSep, hm_call, hoom_imp, hwp_main⟩ :=
    hMain s0 s_main (StdPostMainCleanup L haveLse sp_cmain saved_fp ∗ R_unused)
      hload hs_main hm_main
  obtain ⟨s_ret, hst2, hres | ⟨hoom_st, hoom_sat⟩⟩ :=
    SepWP.to_reaches_pc hwp_main hm_call hs_main.codeLoaded
  · obtain ⟨hpc_r, hrun_r, Pf, hm_ret, hsp_r, hpost_r, R_ret, hent_ret⟩ := hres
    have hsp_r_cm : s_ret.sp = sp_cmain - 0x10#64 := by
      rw [hsp_r, hs_main.sp_eq]; dsimp only [sp_cmain]; bv_lin
    have hsp_al_r : s_ret.spAligned = true := by
      simp only [State.spAligned, hsp_r]; exact hs_main.spAligned_eq
    have hsp_lo_cm : 400 ≤ sp_cmain.toNat := by
      have hge := hs_main.initInfo.sp0_headroom.2
      change 400 ≤ ((StackLayout.of img inputs).sp0 - 0x90#64).toNat
      rw [BitVec.toNat_sub_of_le (by change 144 ≤ (StackLayout.of img inputs).sp0.toNat; omega)]
      change 400 ≤ (StackLayout.of img inputs).sp0.toNat - 144; omega
    have hm_ret' : s_ret.mem ⊨ ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
        (stackAt (sp_cmain - 0x10#64) 384 ∗
         StdPostMainCleanup L haveLse sp_cmain saved_fp ∗ (R_ret ∗ R_unused)) := by
      have hm1 := Satisfies.mono (sepConj_mono_left hent_ret) hm_ret
      rw [← hsp_r, hsp_r_cm] at hm1; revert hm1; sep_frame
    exact cleanup_and_exit_runsTo c lf hload hL0 (hst1.trans hst2) hpc_r hrun_r hsp_r_cm
      hsp_al_r hsp_lo_cm (h_argc.trans h_ret.symm) (by simp [h_ret]) hpost_r hm_ret'
  · exact ElfImageRunsTo.of_oom hload ((hst1.trans hst2).to_pureMem c.no_hooks c.svc_eq)
      hoom_st (hoom_imp s_ret hoom_st hoom_sat)

/-- Whole-ELF correctness (`ElfRunsTo elfBytes pre post oom`) for a `() -> ExitCode` Rust `std`
    binary. -/
theorem stdElf_runsTo_exitCode {P : Program} {L : StdBinaryLayout}
    {elfBytes : List (BitVec 8)} {img : ElfImage}
    {pre : ProcessInputs → Prop} {post : ProcessInputs → ProcessOutcome → Prop}
    {oom : ProcessInputs → State → Prop}
    (c : StdStartupCode P L)
    (hparse : ElfImage.parse elfBytes = .ok img)
    (hmatch : L.MatchesImage img = true)
    (hvalid : ∀ inputs, pre inputs → inputs.Valid)
    (h_ret : L.userMainReturnsExitCode = true := by rfl)
    (h_argc : L.hasArgcGlobal = true := by rfl)
    (hrx : L.rxProgram img = P := by rfl)
    (hMain : ∀ inputs, pre inputs → ∀ (s0 s_main : State) (R_cleanup : SepProp),
      img.loadState inputs = .ok s0 →
      StdUserMainState P L img inputs s0 s_main →
      (s_main.mem ⊨ StdUserMainPre L img inputs s_main ∗ R_cleanup) →
      ∃ (P_call : SepProp) (oomSep : State → SepProp),
        (s_main.mem ⊨ P_call ∗ R_cleanup) ∧
        (∀ sf, sf.status = .OutOfMemory → (sf.mem ⊨ oomSep sf ∗ R_cleanup) → oom inputs sf) ∧
        SepWP P (L.beginShortBacktraceAddr + 0x0c#64) s_main P_call
          (fun s_ret Pf =>
            s_ret.sp = s_main.sp ∧
            post inputs (ProcessOutcome.ofState (((s_ret.readReg32 .x0).truncate 8).zeroExtend 64) s_ret) ∧
            ∃ R_ret : SepProp, Pf ⊢ stackAt s_main.sp 384 ∗ ((L.libcAddr + 3#64) ↦₈ 0#8) ∗ R_ret)
          oomSep) :
    ElfRunsTo elfBytes pre post oom :=
  ElfRunsTo.intro hparse fun inputs hi =>
    stdElfImage_runsTo_exitCode c hmatch (hvalid inputs hi) h_ret h_argc hrx (hMain inputs hi)

end ProofLib.StdStartup
