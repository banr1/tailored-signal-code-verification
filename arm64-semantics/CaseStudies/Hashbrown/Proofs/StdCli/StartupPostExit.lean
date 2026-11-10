/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.StartupPost
public import CaseStudies.Hashbrown.Proofs.StdCli.StartupPostCleanup
public meta import ProofLib.LiteralFetchLint
public meta import ProofLib.SepLogic.Stack
import CaseStudies.Hashbrown.Proofs.StdCli.StdoutInit
import ProofLib.BV

/-!
# Post-Main Epilogue and Process Exit

Post-`userMain` execution through `std::rt::lang_start_internal`, `Once::call` around
`cleanupClosure`, `musl` `exit`, and `SYS_exit_group` (`hbPostMain_to_exit`).
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown

attribute [local simp]
  hbExitF_w64 hbExitF_w32 hbExitF_wReg hbExitF_wV128
  hbExitF_pstate hbExitF_advPC hbExitF_setPC hbExitF_setMem

private theorem hbLibcExitFini_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc ret_pc sp0 : BitVec 64} {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hc : CodeChunks P (hbMuslExitChunks C S)) (hs : S.Valid C)
    (hpc : s.pc = C.std.libcExitFiniAddr) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 →
      CalleeSavedPreserved s sf → HbPostExitFields s sf →
      SepWP P target_pc sf ((C.std.finiArrayAddr ↦₆₄ C.std.doFiniAddr) ∗
        ((C.std.gotAddr + 0x20#64) ↦₆₄ 0#64) ∗ ((C.std.gotAddr + 0x28#64) ↦₆₄ 0#64) ∗
        (S.gotFiniArrayEndAddr ↦₆₄ (C.std.finiArrayAddr + 0x08#64)) ∗
        (S.gotFiniArrayStartAddr ↦₆₄ C.std.finiArrayAddr) ∗
        (C.std.finalizedAddr ↦₈ 1#8) ∗ stackAt sp0 32 ∗ F) post) :
    SepWP P target_pc s ((C.std.finiArrayAddr ↦₆₄ C.std.doFiniAddr) ∗
      ((C.std.gotAddr + 0x20#64) ↦₆₄ 0#64) ∗ ((C.std.gotAddr + 0x28#64) ↦₆₄ 0#64) ∗
      (S.gotFiniArrayEndAddr ↦₆₄ (C.std.finiArrayAddr + 0x08#64)) ∗
      (S.gotFiniArrayStartAddr ↦₆₄ C.std.finiArrayAddr) ∗
      (C.std.finalizedAddr ↦₈ 0#8) ∗ stackAt sp0 32 ∗ F) post := by
  subst hsp; hb_unpack_code hbMuslExitChunks hc
  have hfini_bnd : C.std.finiArrayAddr.toNat + 8 ≤ 2 ^ 48 := hs.finiArray_noWrap
  have hgot_al : MemWidth.isAligned .X64 C.std.gotAddr = true := hbAlign64_of_mod hs.got_align
  have hfini_al : MemWidth.isAligned .X64 C.std.finiArrayAddr = true := hbAlign64_of_mod hs.finiArray_align
  have hal_end : MemWidth.isAligned .X64 S.gotFiniArrayEndAddr = true := hbAlign64_of_mod hs.gotFiniArrayEnd_align
  have hal_start : MemWidth.isAligned .X64 S.gotFiniArrayStartAddr = true := hbAlign64_of_mod hs.gotFiniArrayStart_align
  have hls1 : BitVec.ule (C.std.finiArrayAddr + 0x08#64) C.std.finiArrayAddr = false := by
    simp only [BitVec.ule, decide_eq_false_iff_not, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ⟨hal20, hal28⟩ : MemWidth.isAligned .X64 (C.std.gotAddr + 0x20#64) = true ∧
      MemWidth.isAligned .X64 (C.std.gotAddr + 0x28#64) = true := by
    simp only [MemWidth.isAligned, beq_iff_eq] at hgot_al ⊢; refine ⟨?_, ?_⟩ <;> bv_bits
  rw [stackAt_eq_cells s.sp 4]; hb_unpack_cells 4
  wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; hb_norm_jmp; wp_steps
  refine SepWP.weaken_pre_frame (fun _ _ => by rw [stackAt_eq_cells s.sp 4]; hb_repack_cells)
    (hnext _ hb_wp_a (by simp [wp_norm, arm64_norm, hrun]) hb_wp_a (by hb_close_cs) hb_exit_rfl)

private theorem hbCloseFile_stderr_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc ret_pc sp0 : BitVec 64} {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hc : CodeChunks P (hbMuslExitChunks C S)) (hs : S.Valid C)
    (hpc : s.pc = C.std.closeFileAddr) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = C.std.stderrFileAddr)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 →
      CalleeSavedPreserved s sf → HbPostExitFields s sf →
      SepWP P target_pc sf (StdStderrFile C.std ∗ stackAt sp0 32 ∗ F) post) :
    SepWP P target_pc s (StdStderrFile C.std ∗ stackAt sp0 32 ∗ F) post := by
  subst hsp; hb_unpack_code hbMuslExitChunks hc
  by_cases hstderr_z : C.std.stderrFileAddr = 0#64
  · have hzb : (C.std.stderrFileAddr == 0#64) = true := beq_iff_eq.mpr hstderr_z
    wp_steps; wp_steps
    exact hnext _ hb_wp_a (by simp [wp_norm, arm64_norm, hrun]) hb_wp_a (by hb_close_cs) hb_exit_rfl
  · have hstderr_al : MemWidth.isAligned .X64 C.std.stderrFileAddr = true := hbAlign64_of_mod hs.stderrFile_align
    have hnzb : (C.std.stderrFileAddr == 0#64) = false := beq_false_of_ne hstderr_z
    have ⟨hal08, hal10, hal28, hal38, hal8c⟩ :
        MemWidth.isAligned .X64 (C.std.stderrFileAddr + 0x08#64) = true ∧
        MemWidth.isAligned .X64 (C.std.stderrFileAddr + 0x10#64) = true ∧
        MemWidth.isAligned .X64 (C.std.stderrFileAddr + 0x28#64) = true ∧
        MemWidth.isAligned .X64 (C.std.stderrFileAddr + 0x38#64) = true ∧
        MemWidth.isAligned .W32 (C.std.stderrFileAddr + 0x8c#64) = true := by
      simp only [MemWidth.isAligned, beq_iff_eq] at hstderr_al ⊢; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits
    dsimp only [StdStderrFile, StdBinaryLayout.stderrFileAtoms, rwAtomListSep, RwAtom.toSepProp]
    rw [stackAt_eq_cells s.sp 4]; hb_unpack_cells 4; wp_steps; wp_steps; wp_steps
    refine SepWP.weaken_pre_frame (fun _ _ => by
        dsimp only [StdStderrFile, StdBinaryLayout.stderrFileAtoms, rwAtomListSep, RwAtom.toSepProp]
        rw [stackAt_eq_cells s.sp 4]; hb_repack_cells)
      (hnext _ hb_wp_a (by simp [wp_norm, arm64_norm, hrun]) hb_wp_a (by hb_close_cs) hb_exit_rfl)

private theorem hbStdioExitNeeded_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc ret_pc sp0 : BitVec 64} {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hc : CodeChunks P (hbMuslExitChunks C S)) (hs : S.Valid C)
    (hpc : s.pc = C.std.stdioExitNeededAddr) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 →
      CalleeSavedPreserved s sf → HbPostExitFields s sf →
      SepWP P target_pc sf (((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ (C.std.oflHeadAddr ↦₆₄ 0#64) ∗
        (C.std.stdinUsedAddr ↦₆₄ 0#64) ∗ (C.std.stdoutUsedAddr ↦₆₄ 0#64) ∗
        (C.std.stderrUsedAddr ↦₆₄ C.std.stderrFileAddr) ∗ StdStderrFile C.std ∗ stackAt sp0 48 ∗ F) post) :
    SepWP P target_pc s (((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ (C.std.oflHeadAddr ↦₆₄ 0#64) ∗
      (C.std.stdinUsedAddr ↦₆₄ 0#64) ∗ (C.std.stdoutUsedAddr ↦₆₄ 0#64) ∗
      (C.std.stderrUsedAddr ↦₆₄ C.std.stderrFileAddr) ∗ StdStderrFile C.std ∗ stackAt sp0 48 ∗ F) post := by
  subst hsp; hb_unpack_code hbMuslExitChunks hc
  have hal_ofl : MemWidth.isAligned .X64 C.std.oflHeadAddr = true := hbAlign64_of_mod hs.oflHead_align
  have hal_stdin : MemWidth.isAligned .X64 C.std.stdinUsedAddr = true := hbAlign64_of_mod hs.stdinUsed_align
  have hal_stdout : MemWidth.isAligned .X64 C.std.stdoutUsedAddr = true := hbAlign64_of_mod hs.stdoutUsed_align
  have hal_stderr_u : MemWidth.isAligned .X64 C.std.stderrUsedAddr = true := hbAlign64_of_mod hs.stderrUsed_align
  have hstk : stackAt s.sp 48 = stackAt s.sp 32 ∗ stackAt (s.sp - 32#64) 16 := by
    rw [hbStackAt_split s.sp 32 16, sepConj_comm]
  rw [stackAt_eq_cells s.sp 6]; hb_unpack_cells 6
  wp_steps; hb_norm_jmp; wp_steps; wp_steps; wp_steps; hb_norm_jmp; wp_steps; wp_steps; wp_steps; wp_steps
  try (conv => repeat rw [hbBv64_add_sub_cancel])
  wp_steps; wp_steps; hb_norm_jmp; wp_steps; wp_steps; hb_norm_jmp; wp_steps; wp_steps; wp_steps; hb_norm_jmp
  refine SepWP.weaken_pre_frame
    (P' := StdStderrFile C.std ∗ stackAt s.sp 32 ∗ (stackAt (s.sp - 32#64) 16 ∗ ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗
      (C.std.oflHeadAddr ↦₆₄ 0#64) ∗ (C.std.stdinUsedAddr ↦₆₄ 0#64) ∗ (C.std.stdoutUsedAddr ↦₆₄ 0#64) ∗
      (C.std.stderrUsedAddr ↦₆₄ C.std.stderrFileAddr) ∗ F))
    (fun _ _ => by rw [← sepConj_assoc (stackAt s.sp 32), ← hstk, stackAt_eq_cells s.sp 6]; hb_repack_cells) ?_
  refine hbCloseFile_stderr_wp (ret_pc := ret_pc) (sp0 := s.sp) hc hs hb_wp_a
    (by simp [wp_norm, arm64_norm, hrun]) hb_wp_a
    (by simp [State.spAligned, wp_norm, arm64_norm, bv_lin_norm]; simpa [State.spAligned] using hsp_align)
    hb_wp_a hb_wp_a fun sf hpc_f hrun_f hsp_f hcs_f hex_f =>
      SepWP.weaken_pre (by rw [← sepConj_assoc (stackAt s.sp 32), ← hstk]; sep_frame)
        (hnext sf hpc_f hrun_f hsp_f (by hb_unpack_cs hcs_f; hb_close_cs) (HbPostExitFields.trans hb_exit_rfl hex_f))

theorem hbMuslExit_to_svc_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc sp0 : BitVec 64} {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hc : CodeChunks P (hbMuslExitChunks C S)) (hs : S.Valid C)
    (hpc : s.pc = C.std.libcStartMainStage2Addr + 0x38#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hnext : ∀ sf : State, sf.pc = C.std.sysExitAddr + 0x0c#64 → sf.status = .Running →
      sf.sp = sp0 - 0x20#64 → sf.spAligned = true →
      sf.readReg64 .x8 = 94#64 → sf.readReg64 .x0 = (s.readReg32 .x0).signExtend 64 →
      HbPostExitFields s sf →
      SepWP P target_pc sf (HbMuslExitGlobalsNoNeedLocks C S 1#8 ∗ ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sp0 80 ∗ F) post) :
    SepWP P target_pc s (HbMuslExitGlobalsNoNeedLocks C S 0#8 ∗ ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sp0 80 ∗ F) post := by
  subst hsp; hb_unpack_code hbMuslExitChunks hc
  dsimp only [HbMuslExitGlobalsNoNeedLocks]
  rw [stackAt_split_cells s.sp 48 4 (by decide)]; hb_unpack_cells 4
  wp_steps; hb_norm_jmp; wp_steps; hb_norm_jmp; wp_steps; wp_steps; hb_norm_jmp
  rw [hbStackAt_split (s.sp - 32#64) 32 16]
  refine SepWP.weaken_pre (P' := (C.std.finiArrayAddr ↦₆₄ C.std.doFiniAddr) ∗
      ((C.std.gotAddr + 0x20#64) ↦₆₄ 0#64) ∗ ((C.std.gotAddr + 0x28#64) ↦₆₄ 0#64) ∗
      (S.gotFiniArrayEndAddr ↦₆₄ (C.std.finiArrayAddr + 0x08#64)) ∗
      (S.gotFiniArrayStartAddr ↦₆₄ C.std.finiArrayAddr) ∗
      (C.std.finalizedAddr ↦₈ 0#8) ∗ stackAt (s.sp - 32#64) 32 ∗ ?F1) (by sep_frame) ?_
  refine hbLibcExitFini_wp (ret_pc := C.std.exitAddr + 0x18#64) (sp0 := s.sp - 32#64) hc hs
    hb_wp_a (by simp [wp_norm, arm64_norm, hrun]) hb_wp_a
    (by simp [State.spAligned, wp_norm, arm64_norm]; simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align)
    hb_wp_a fun s1 hpc1 hrun1 hsp1 hcs1 hex1 => ?_
  have hx19_1 : s1.readReg64 .x19 = (s.readReg32 .x0).zeroExtend 64 := by
    rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]
  have hex_s1 : HbPostExitFields s s1 := HbPostExitFields.trans hb_exit_rfl hex1
  wp_steps; hb_norm_jmp
  refine SepWP.weaken_pre (P' := ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ (C.std.oflHeadAddr ↦₆₄ 0#64) ∗
      (C.std.stdinUsedAddr ↦₆₄ 0#64) ∗ (C.std.stdoutUsedAddr ↦₆₄ 0#64) ∗
      (C.std.stderrUsedAddr ↦₆₄ C.std.stderrFileAddr) ∗ StdStderrFile C.std ∗ stackAt (s.sp - 32#64) 48 ∗ ?F2)
    (by rw [hbStackAt_split (s.sp - 32#64) 32 16 (n := 48)]; sep_frame) ?_
  refine hbStdioExitNeeded_wp (ret_pc := C.std.exitAddr + 0x1c#64) (sp0 := s.sp - 32#64) hc hs
    hb_wp_a (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp1]; simpa [State.spAligned, beq_iff_eq] using hsp_align)
    hb_wp_a fun s2 hpc2 hrun2 hsp2 hcs2 hex2 => ?_
  have hx19_2 : s2.readReg64 (.gpr 19#5) = (s.readReg32 .x0).zeroExtend 64 := by
    have := hcs2.readReg64_x19; simp [wp_norm, arm64_norm, hx19_1] at this; exact this
  wp_steps; hb_norm_jmp; wp_steps 3
  refine SepWP.weaken_pre_frame (fun _ _ => by dsimp only [HbMuslExitGlobalsNoNeedLocks]; rw [stackAt_split_cells s.sp 48 4 (by decide)]; hb_repack_cells)
    (hnext _ hb_wp_a (by simp [wp_norm, arm64_norm, hrun2]) (by simp [wp_norm, arm64_norm, hsp2]; try bv_lin)
      (by simp [State.spAligned, wp_norm, arm64_norm, hsp2]; simpa [State.spAligned, beq_iff_eq] using hsp_align)
      hb_wp_a
      (by simp [wp_norm, arm64_norm]; simpa [Arm64.evalBitfield] using BitVec.sbfm_sxtw_eq_signExtend 0#64 (BitVec.setWidth 64 (BitVec.setWidth 32 (s.readReg64 (.gpr 0#5)))))
      (HbPostExitFields.trans hex_s1 (HbPostExitFields.trans hb_exit_rfl (HbPostExitFields.trans hex2 hb_exit_rfl))))

set_option linter.literalFetch false in
theorem hbMuslExit_fetch_svc {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    (hc : CodeChunks P (hbMuslExitChunks C S)) :
    P.fetch (C.std.sysExitAddr + 0x0c#64) = some (.system false 0#16) := by
  hb_unpack_code hbMuslExitChunks hc
  exact Program.fetch_of_hasCode_decodeAt 3 (hex := sysExitWords) (by with_reducible assumption) (by simp only [wp_norm]) (by decide)

theorem hbOnceCallCleanup_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc ret_pc sp0 dataPtr : BitVec 64} {haveLse : BitVec 8}
    {s : State} {Pre Post F : SepProp} {post : State → SepProp → Prop}
    (hc : HbPostMainCode P C S) (hv : C.Valid)
    (hd_once : RoDisj C C.std.cleanupOnceAddr 4)
    (hpc : s.pc = C.std.onceCallAddr) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = C.std.cleanupOnceAddr)
    (hx1 : s.readReg64 .x1 = 0#64)
    (hx2 : s.readReg64 .x2 = dataPtr)
    (hx3 : s.readReg64 .x3 = C.std.cleanupVtableAddr)
    (hclosure : ∀ sc : State, ∀ G : SepProp,
      sc.pc = C.std.cleanupClosureAddr → sc.status = .Running →
      sc.sp = sp0 - 0x60#64 → sc.spAligned = true →
      sc.readReg64 Reg.lr = C.std.onceCallAddr + 0x11c#64 →
      sc.readReg64 .x0 = dataPtr → ProcessFieldsPreserved s sc →
      (∀ sr : State, sr.pc = C.std.onceCallAddr + 0x11c#64 → sr.status = .Running →
        sr.sp = sc.sp → CalleeSavedPreserved sc sr → HbPostExitFields sc sr →
        RoPostFacts C haveLse sr.mem →
        SepWP P target_pc sr (Post ∗ G) post) →
      SepWP P target_pc sc
        ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          StdVtableRo C.std.cleanupVtableAddr C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr ∗
          Pre ∗ G) post)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → CalleeSavedPreserved s sf → HbPostExitFields s sf →
      RoPostFacts C haveLse sf.mem →
      SepWP P target_pc sf ((C.std.cleanupOnceAddr ↦₃₂ 0#32) ∗ stackAt sp0 96 ∗ Post ∗ F) post) :
    SepWP P target_pc s
      ((C.std.cleanupOnceAddr ↦₃₂ 3#32) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.std.cleanupVtableAddr C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr ∗
        stackAt sp0 96 ∗ Pre ∗ F) post := by
  subst hsp
  have halign : MemWidth.isAligned .W32 C.std.cleanupOnceAddr = true := hbAlign32_of_mod hv.cleanupOnce_align
  unfold StdVtableRo
  rw [stackAt_eq_cells s.sp 12]; hb_unpack_cells 12
  rw [pointsTo64_split32_sub s.sp 88#64 84#64, hbPointsTo32_split8_sub s.sp 84#64 83#64 82#64 81#64]
  refine hb_wp_step_proc C.std.cas4AcqAddr hc.no_hooks hc.svc_eq (by
    hb_unpack_code_nosvc hbOnceCallPostChunks hc.onceCallPost
    wp_steps
    refine step_ldar32_words C.std.onceCallAddr _ 7 (C.std.onceCallAddr + 32#64) halign (rt' := .gpr 22#5) (hnext := ?_)
    wp_steps; wp_steps; wp_steps; wp_steps; hb_norm_jmp
    exact hb_done_proc) fun m0 hp0 => ?_
  refine call_stdCas4 hc.atomics.cas4Acq_ok (haveLse := haveLse) (ptr := C.std.cleanupOnceAddr) (v0 := 3#32) (exp := 3#32) (new := 1#32)
    (hrun := by simp [wp_norm, arm64_norm, hrun])
    (ret_pc := C.std.onceCallAddr + 0x1f8#64) (F := ?_) (by sep_frame) (fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hstd1 => ?_) (halign := halign)
  simp only [beq_self_eq_true, ↓reduceIte]
  have ⟨hx19_1, hx20_1, hx21_1, hx22_1⟩ :
      s1.readReg64 .x19 = C.std.cleanupOnceAddr ∧ s1.readReg64 .x20 = dataPtr ∧
      s1.readReg64 .x21 = C.std.cleanupVtableAddr ∧ BitVec.truncate 32 (s1.readReg64 (.gpr 22#5)) = 3#32 :=
    ⟨by rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm],
     by rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm],
     by rw [hcs1.readReg64_x21]; simp [wp_norm, arm64_norm],
     by have := hcs1.readReg32_x22; simp [wp_norm, arm64_norm] at this; exact this⟩
  have hsp1_eq : s1.sp = s.sp - 0x60#64 := by rw [hsp1]; exact hb_wp_a
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1_eq]; exact s.spAligned_sub 0x60#64 hsp_align
  have hp_s1 : ProcessFieldsPreserved s s1 := hp0.trans (hbStdState_toProcess hstd1)
  refine hb_wp_step_proc C.std.cleanupClosureAddr hc.no_hooks hc.svc_eq (by
    hb_unpack_code_nosvc hbOnceCallPostChunks hc.onceCallPost
    wp_steps; wp_steps; wp_steps
    exact hb_done_proc) fun m2 hp2 => ?_
  have hp_sc : ProcessFieldsPreserved s _ := hp_s1.trans hp2
  have hex_sc : HbPostExitFields s _ := ⟨hp_sc.1, hp_sc.2.1, hp_sc.2.2.1, hp_sc.2.2.2.1⟩
  wp_conv_pre => simp only [wp_norm, arm64_norm, hsp1_eq,
    show (s.sp - 96#64) + 8#64 = s.sp - 88#64 by bv_lin,
    show (s.sp - 96#64) + 12#64 = s.sp - 84#64 by bv_lin]
  refine SepWP.weaken_pre
    (P' := (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      StdVtableRo C.std.cleanupVtableAddr C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr ∗ Pre ∗ ?G)
    (by unfold StdVtableRo; sep_frame) ?_
  apply hclosure
  · exact hb_wp_a
  · simp [wp_norm, arm64_norm, hrun1]
  · simp [wp_norm, arm64_norm, hsp1_eq]
  · simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_al
  · exact hb_wp_a
  · exact hb_wp_a
  · exact hp_sc
  · intro s2 hpc2 hrun2 hsp2 hcs2 hex2 hro2
    hb_unpack_code hbOnceCallPostChunks hc.onceCallPost
    have hx19_2 : s2.readReg64 (.gpr 19#5) = C.std.cleanupOnceAddr := by
      have := hcs2.readReg64_x19; simpa [wp_norm, arm64_norm, hx19_1] using this
    have hsp2_eq : s2.sp = s.sp - 0x60#64 := by rw [hsp2]; simp [wp_norm, arm64_norm, hsp1_eq]
    have hsp2_al : s2.spAligned = true := by simp only [State.spAligned, hsp2_eq]; exact s.spAligned_sub 0x60#64 hsp_align
    have h88_2 : s.sp - 88#64 = s2.sp + 8#64 := by rw [hsp2_eq]; bv_lin
    clear hsp2 hsp2_eq
    wp_conv_pre => rw [h88_2]
    wp_steps; hb_norm_jmp
    refine call_swp4Rel_ro hc.swp4Rel (by simpa [wp_norm, arm64_norm] using hro2) hd_once halign
      (ret_pc := C.std.onceCallAddr + 0x128#64) (v0 := 1#32) (new := 0#32)
      (hnext := fun s3 hpc3 hrun3 hsp3 hcs3 hstd3 hx0_3 hro3 => ?_)
    have hx0_3' : s3.readReg64 (.gpr 0#5) = 1#64 := hx0_3
    have hsp3_eq : s3.sp = s.sp - 0x60#64 := by
      have hsp3' : s3.sp = s2.sp := by simpa [wp_norm, arm64_norm] using hsp3
      rw [hsp3']; have := h88_2; bv_omega
    have hsp3_al : s3.spAligned = true := by simp only [State.spAligned, hsp3_eq]; exact s.spAligned_sub 0x60#64 hsp_align
    have h64 : s.sp - 64#64 = s3.sp + 32#64 := by rw [hsp3_eq]; bv_lin
    have h56 : s.sp - 56#64 = s3.sp + 40#64 := by rw [hsp3_eq]; bv_lin
    have h48 : s.sp - 48#64 = s3.sp + 48#64 := by rw [hsp3_eq]; bv_lin
    have h40 : s.sp - 40#64 = s3.sp + 56#64 := by rw [hsp3_eq]; bv_lin
    have h32 : s.sp - 32#64 = s3.sp + 64#64 := by rw [hsp3_eq]; bv_lin
    have h24 : s.sp - 24#64 = s3.sp + 72#64 := by rw [hsp3_eq]; bv_lin
    have h16 : s.sp - 16#64 = s3.sp + 80#64 := by rw [hsp3_eq]; bv_lin
    have h08 : s.sp - 8#64 = s3.sp + 88#64 := by rw [hsp3_eq]; bv_lin
    have hsp_end : s3.sp + 0x60#64 = s.sp := by rw [hsp3_eq]; bv_lin
    clear hsp3 hsp3_eq
    wp_conv_pre => rw [← h88_2, h64, h56, h48, h40, h32, h24, h16, h08]
    wp_steps; wp_steps
    refine SepWP.weaken_pre_frame
      (fun _ hm => by
        rw [← h08, ← h16, ← h24, ← h32, ← h40, ← h48, ← h56, ← h64] at hm
        rw [stackAt_eq_cells s.sp 12]; hb_repack_cells_split hm, s.sp, 88#64, 84#64, 83#64, 82#64, 81#64)
      (hnext _ hb_wp_a (by simp [wp_norm, arm64_norm, hrun3]) hb_wp_a
        (by hb_unpack_cs hcs1; hb_unpack_cs hcs2; hb_unpack_cs hcs3; hb_close_cs)
        (HbPostExitFields.trans hex_sc
          (HbPostExitFields.trans hex2 (HbPostExitFields.trans hb_exit_rfl
            (HbPostExitFields.trans (HbPostExitFields.ofState hstd3) hb_exit_rfl))))
        (by simpa [wp_norm, arm64_norm] using hro3))

private theorem hbAnd32_ff_eq {w : BitVec 32} {code8 : BitVec 8}
    (h : w.truncate 8 = code8) :
    (w &&& 0xff#32).zeroExtend 64 = code8.zeroExtend 64 := by
  subst h; bv_bits

private theorem merge_stk_32 (sp0 v0 v1 v2 v3 : BitVec 64) :
    ((sp0 - 0x170#64) ↦₆₄ v0) ∗ ((sp0 - 0x168#64) ↦₆₄ v1) ∗
    ((sp0 - 0x160#64) ↦₆₄ v2) ∗ ((sp0 - 0x158#64) ↦₆₄ v3) ∗
    stackAt (sp0 - 0x170#64) 64 ⊢ stackAt (sp0 - 0x150#64) 96 := by
  rw [stackAt_split_cells (sp0 - 0x150#64) 64 4 (by decide)]
  simp only [Nat.reduceMul]; cells_unfold
  rw [show (sp0 - 0x150#64) - 32#64 = sp0 - 0x170#64 by bv_lin,
      show (sp0 - 0x150#64) - 24#64 = sp0 - 0x168#64 by bv_lin,
      show (sp0 - 0x150#64) - 16#64 = sp0 - 0x160#64 by bv_lin,
      show (sp0 - 0x150#64) - 8#64 = sp0 - 0x158#64 by bv_lin]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (by sep_entail))))

def HbDead : SepProp := ∃∗ P : SepProp, P

theorem entails_with_dead {A B : SepProp} : A ∗ B ⊢ A ∗ HbDead :=
  sepConj_mono_right (Entails.sepExists_right B (Entails.refl B))

theorem hbLangStartPost_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc sp0 : BitVec 64} {haveLse : BitVec 8}
    {s : State} {Pre Post F : SepProp} {post : State → SepProp → Prop}
    (hc : HbPostMainCode P C S) (hv : C.Valid) (hs : S.Valid C)
    (hd_once : RoDisj C C.std.cleanupOnceAddr 4)
    (hd_exit : RoDisj C C.std.exitingThreadIdAddr 8)
    (hpc : s.pc = C.std.beginShortBacktraceAddr + 0x0c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0x170#64) (hsp_align : s.spAligned = true)
    (hclosure : ∀ sc : State, ∀ G : SepProp,
      sc.pc = C.std.cleanupClosureAddr → sc.status = .Running →
      sc.sp = sp0 - 0x1b0#64 → sc.spAligned = true →
      sc.readReg64 Reg.lr = C.std.onceCallAddr + 0x11c#64 →
      sc.readReg64 .x0 = sp0 - 0x150#64 → ProcessFieldsPreserved s sc →
      (∀ sr : State, sr.pc = C.std.onceCallAddr + 0x11c#64 → sr.status = .Running →
        sr.sp = sc.sp → CalleeSavedPreserved sc sr → HbPostExitFields sc sr →
        RoPostFacts C haveLse sr.mem →
        SepWP P target_pc sr
          ((((sp0 - 0x150#64) ↦₆₄ (sp0 - 0xb4#64)) ∗ ((sp0 - 0xb4#64) ↦₈ 0#8) ∗ Post) ∗ G) post) →
      SepWP P target_pc sc
        ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          StdVtableRo C.std.cleanupVtableAddr C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr ∗
          (((sp0 - 0x150#64) ↦₆₄ (sp0 - 0xb4#64)) ∗ ((sp0 - 0xb4#64) ↦₈ 1#8) ∗ Pre) ∗ G) post)
    (hnext : ∀ sf : State, sf.pc = C.std.libcStartMainStage2Addr + 0x38#64 → sf.status = .Running →
      sf.sp = sp0 - 0x30#64 → sf.spAligned = true →
      sf.readReg64 .x0 = ((s.readReg32 .x0).truncate 8).zeroExtend 64 →
      HbPostExitFields s sf →
      SepWP P target_pc sf
        ((C.std.cleanupOnceAddr ↦₃₂ 0#32) ∗
          (C.std.exitingThreadIdAddr ↦₆₄ (s.tpidrEl0 - 0xa4#64)) ∗
          stackAt (sp0 - 0x30#64) 80 ∗ Post ∗ HbDead ∗ F) post) :
    SepWP P target_pc s
      (HbCallerFrames C sp0 ∗ stackAt (sp0 - 0x170#64) 64 ∗
        (C.std.cleanupOnceAddr ↦₃₂ 3#32) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.std.cleanupVtableAddr C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr ∗
        (C.std.exitingThreadIdAddr ↦₆₄ 0#64) ∗ Pre ∗ F) post := by
  rcases hc.lsAdrX4 with ⟨imm_x4, hfetch_x4⟩
  have hal_once : MemWidth.isAligned .W32 C.std.cleanupOnceAddr = true := hbAlign32_of_mod hv.cleanupOnce_align
  have hal_exit : MemWidth.isAligned .X64 C.std.exitingThreadIdAddr = true := hbAlign64_of_mod hs.exitingTid_align
  have hal_150 : ((sp0 - 0x150#64) &&& 15#64 == 0#64) = true := by
    have := hsp_align; simp only [State.spAligned, hsp, beq_iff_eq] at this ⊢; bv_bits
  unfold HbCallerFrames
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro fp_cm
  rw [hbStackAt_split (sp0 - 0xb0#64) 8 152,
      show (sp0 - 0xb0#64) - 8#64 = sp0 - 0xb8#64 by bv_lin,
      hbStackAt_split (sp0 - 0xb8#64) 144 8,
      show (sp0 - 0xb8#64) - 144#64 = sp0 - 0x148#64 by bv_lin,
      stackAt_eq_cells (sp0 - 0xb0#64) 1,
      stackAt_eq_cells (sp0 - 0x148#64) 1]
  hb_unpack_cells 2
  simp only [sepConj_assoc,
    show (sp0 - 0xb0#64) - 8#64 = sp0 - 0xb8#64 by bv_lin,
    show (sp0 - 0x148#64) - 8#64 = sp0 - 0x150#64 by bv_lin]
  rw [pointsTo64_split32_sub sp0 0xb8#64 0xb4#64,
      hbPointsTo32_split8_sub sp0 0xb4#64 0xb3#64 0xb2#64 0xb1#64]
  have h170 : sp0 - 0x170#64 = s.sp := hsp.symm
  have h168 : sp0 - 0x168#64 = s.sp + 8#64 := by rw [hsp]; bv_lin
  have h160 : sp0 - 0x160#64 = s.sp + 16#64 := by rw [hsp]; bv_lin
  have h158 : sp0 - 0x158#64 = (s.sp + 16#64) + 8#64 := by rw [hsp]; bv_lin
  have h150 : sp0 - 0x150#64 = (s.sp + 16#64) + 16#64 := by rw [hsp]; bv_lin
  have hal_s16 : ((s.sp + 16#64) &&& 15#64 == 0#64) = true := by
    have := hsp_align; simp only [State.spAligned, beq_iff_eq] at this ⊢; bv_bits
  have hal_s32 : (((s.sp + 16#64) + 16#64) &&& 15#64 == 0#64) = true := by
    have := hsp_align; simp only [State.spAligned, beq_iff_eq] at this ⊢; bv_bits
  clear hsp
  wp_conv_pre => rw [h170, h168, h160, h158, h150]
  refine hb_wp_step_proc C.std.onceCallAddr hc.no_hooks hc.svc_eq (by
    have hfetch_x4_ns : (P.withSvc noSyscalls).fetch (C.langStartInternalAddr + 0x554#64) =
        some (.adr false .x4 imm_x4) := by simpa [fetch_withSvc] using hfetch_x4
    hb_unpack_code_nosvc hbLangStartPostChunks hc.langStartPost
    dsimp only [beginShortBacktraceWords] at *
    wp_steps; wp_steps; wp_steps; wp_steps
    refine step_ldar32_words (C.langStartInternalAddr + 0x3a0#64) _ 0 (C.langStartInternalAddr + 0x3a4#64) hal_once
      (rt' := .gpr 8#5)
      (hpc := by simp [wp_norm, arm64_norm]; try bv_lin)
      (haddr := by simp [wp_norm, arm64_norm]; try bv_lin)
      (hnext := ?_)
    wp_steps; hb_norm_jmp; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; hb_norm_jmp
    exact hb_done_proc) fun m0 hp0 => ?_
  wp_conv_pre =>
    rw [← h150, ← h158, ← h160, ← h168, ← h170]
    simp only [wp_norm, arm64_norm,
      show (sp0 - 176#64) - 4#64 = sp0 - 180#64 by bv_lin,
      show (sp0 - 176#64) + (0#64 - 4#64) = sp0 - 180#64 by bv_lin]
  refine SepWP.weaken_pre (P' := stackAt (sp0 - 0x150#64) 96 ∗ ?_)
    (Entails.trans (by sep_frame)
      (sepConj_mono_left (merge_stk_32 sp0 (sp0 - 0x160#64) (C.langStartClosureAddr + 0x10#64)
        (sp0 - 0xb0#64) (C.langStartInternalAddr + 0x394#64)))) ?_
  refine SepWP.weaken_pre
    (P' := (C.std.cleanupOnceAddr ↦₃₂ 3#32) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      StdVtableRo C.std.cleanupVtableAddr C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr ∗
      stackAt (sp0 - 0x150#64) 96 ∗
      (((sp0 - 0x150#64) ↦₆₄ (sp0 - 0xb4#64)) ∗ ((sp0 - 0xb4#64) ↦₈ 1#8) ∗ Pre) ∗ ?F1)
    (by sep_frame) ?_
  apply hbOnceCallCleanup_wp hc hv hd_once
    (sp0 := sp0 - 0x150#64) (ret_pc := C.langStartInternalAddr + 0x564#64) (dataPtr := sp0 - 0x150#64)
    (Pre := ((sp0 - 0x150#64) ↦₆₄ (sp0 - 0xb4#64)) ∗ ((sp0 - 0xb4#64) ↦₈ 1#8) ∗ Pre)
    (Post := ((sp0 - 0x150#64) ↦₆₄ (sp0 - 0xb4#64)) ∗ ((sp0 - 0xb4#64) ↦₈ 0#8) ∗ Post)
  · exact hb_wp_a
  · simp [wp_norm, arm64_norm, hrun]
  · simp only [wp_norm, arm64_norm]; rw [← h170]; bv_lin
  · simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align
  · exact hb_wp_a
  · exact hb_wp_a
  · exact hb_wp_a
  · simp only [wp_norm, arm64_norm]; rw [← h170]; bv_lin
  · exact hb_wp_a
  · intro sc G hpc_c hrun_c hsp_c hal_c hlr_c hx0_c hp_c hcont_c
    exact hclosure sc G hpc_c hrun_c (by rw [hsp_c]; bv_lin) hal_c hlr_c hx0_c
      (hp0.trans hp_c) hcont_c
  · intro s1 hpc1 hrun1 hsp1 hcs1 hex1 hro1
    hb_unpack_code hbLangStartPostChunks hc.langStartPost
    have herr : P.hasCode C.std.errnoLocationAddr errnoLocationWords := hc.teardownSys.1
    dsimp only [beginShortBacktraceWords, errnoLocationWords] at *
    have hx19_1 : s1.readReg64 (.gpr 19#5) = ((s.readReg32 .x0).truncate 8).zeroExtend 64 := by
      have h19 := hcs1.readReg64_x19
      simp only [wp_norm, arm64_norm] at h19
      rw [h19]; dsimp [State.readReg32, Reg.x0, Arm64.evalBitfield]; bv_bits
    have hex_s1 : HbPostExitFields s s1 :=
      HbPostExitFields.trans ⟨hp0.1, hp0.2.1, hp0.2.2.1, hp0.2.2.2.1⟩ hex1
    wp_steps; hb_norm_jmp; wp_steps; hb_norm_jmp; wp_steps
    wp_steps; wp_steps; wp_steps; wp_steps; hb_norm_jmp
    refine call_cas8Acq_ro hc.cas8Acq (by simpa [wp_norm, arm64_norm] using hro1) hd_exit hal_exit
      (ret_pc := C.langStartInternalAddr + 0x3c4#64) (ptr := C.std.exitingThreadIdAddr)
      (v0 := 0#64) (new := s.tpidrEl0 - 0xa4#64)
      (hx1 := by simp [wp_norm, arm64_norm, hex_s1.2.2.1])
      (hnext := fun s2 hpc2 hrun2 hsp2 hcs2 hstd2 hx0_2 _hro2 => ?_)
    have hx0_2' : s2.readReg64 (.gpr 0#5) = 0#64 := hx0_2
    have hx19_2 : s2.readReg64 (.gpr 19#5) = ((s.readReg32 .x0).truncate 8).zeroExtend 64 := by
      have := hcs2.readReg64_x19; simpa [wp_norm, arm64_norm, hx19_1] using this
    have hsp2_eq : s2.sp = sp0 - 0x150#64 := by simpa [wp_norm, arm64_norm, hsp1] using hsp2
    have hsp2_al : s2.spAligned = true := by simp only [State.spAligned, hsp2_eq]; exact hal_150
    rw [stackAt_eq_cells (sp0 - 0x40#64) 12]; hb_unpack_cells 12
    have hb0 : sp0 - 0xb0#64 = s2.sp + 160#64 := by rw [hsp2_eq]; bv_lin
    have ha8 : sp0 - 0xa8#64 = s2.sp + 168#64 := by rw [hsp2_eq]; bv_lin
    have ha0 : (sp0 - 0x40#64) - 96#64 = s2.sp + 176#64 := by rw [hsp2_eq]; bv_lin
    have h98 : (sp0 - 0x40#64) - 88#64 = s2.sp + 184#64 := by rw [hsp2_eq]; bv_lin
    have h90 : (sp0 - 0x40#64) - 80#64 = s2.sp + 192#64 := by rw [hsp2_eq]; bv_lin
    have h88 : (sp0 - 0x40#64) - 72#64 = s2.sp + 200#64 := by rw [hsp2_eq]; bv_lin
    have h80 : (sp0 - 0x40#64) - 64#64 = s2.sp + 208#64 := by rw [hsp2_eq]; bv_lin
    have h78 : (sp0 - 0x40#64) - 56#64 = s2.sp + 216#64 := by rw [hsp2_eq]; bv_lin
    have h70 : (sp0 - 0x40#64) - 48#64 = s2.sp + 224#64 := by rw [hsp2_eq]; bv_lin
    have h68 : (sp0 - 0x40#64) - 40#64 = s2.sp + 232#64 := by rw [hsp2_eq]; bv_lin
    have h60 : (sp0 - 0x40#64) - 32#64 = s2.sp + 240#64 := by rw [hsp2_eq]; bv_lin
    have h58 : (sp0 - 0x40#64) - 24#64 = s2.sp + 248#64 := by rw [hsp2_eq]; bv_lin
    have h40 : sp0 - 0x40#64 = (s2.sp + 256#64) + 16#64 := by rw [hsp2_eq]; bv_lin
    have h38 : sp0 - 0x38#64 = (s2.sp + 256#64) + 24#64 := by rw [hsp2_eq]; bv_lin
    have hsp_end : (s2.sp + 256#64) + 32#64 = sp0 - 0x30#64 := by rw [hsp2_eq]; bv_lin
    have hal_256 : ((s2.sp + 256#64) &&& 15#64 == 0#64) = true := by
      rw [hsp2_eq]; simp only [beq_iff_eq] at hal_150 ⊢; bv_bits
    clear hsp2 hsp2_eq
    wp_conv_pre => rw [hb0, ha8, ha0, h98, h90, h88, h80, h78, h70, h68, h60, h58, h40, h38]
    wp_steps; wp_steps; wp_steps
    refine SepWP.weaken_pre
      (P' := ((C.std.cleanupOnceAddr ↦₃₂ 0#32) ∗
        (C.std.exitingThreadIdAddr ↦₆₄ (s.tpidrEl0 - 0xa4#64)) ∗
        stackAt (sp0 - 0x30#64) 80 ∗ Post ∗ F) ∗ ?Dead)
      (by
        rw [← h38, ← h40, ← h58, ← h60, ← h68, ← h70, ← h78, ← h80,
            stackAt_eq_cells (sp0 - 0x30#64) 10]
        simp only [Nat.reduceMul]; cells_unfold
        rw [show (sp0 - 0x30#64) - 80#64 = (sp0 - 0x40#64) - 64#64 by bv_lin,
            show (sp0 - 0x30#64) - 72#64 = (sp0 - 0x40#64) - 56#64 by bv_lin,
            show (sp0 - 0x30#64) - 64#64 = (sp0 - 0x40#64) - 48#64 by bv_lin,
            show (sp0 - 0x30#64) - 56#64 = (sp0 - 0x40#64) - 40#64 by bv_lin,
            show (sp0 - 0x30#64) - 48#64 = (sp0 - 0x40#64) - 32#64 by bv_lin,
            show (sp0 - 0x30#64) - 40#64 = (sp0 - 0x40#64) - 24#64 by bv_lin,
            show (sp0 - 0x30#64) - 32#64 = (sp0 - 0x40#64) - 16#64 by bv_lin,
            show (sp0 - 0x30#64) - 24#64 = (sp0 - 0x40#64) - 8#64 by bv_lin,
            show (sp0 - 0x30#64) - 16#64 = sp0 - 0x40#64 by bv_lin,
            show (sp0 - 0x30#64) - 8#64 = sp0 - 0x38#64 by bv_lin]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        sep_frame) ?_
    refine SepWP.weaken_pre (by refine Entails.trans entails_with_dead (by sep_entail))
      (hnext _ hb_wp_a (by simp [wp_norm, arm64_norm, hrun2])
        (by simp only [wp_norm, arm64_norm]; rw [← hsp_end]; bv_lin)
        (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp2_al)
        (by simp [wp_norm, arm64_norm])
        (HbPostExitFields.trans hex_s1
          (HbPostExitFields.trans hb_exit_rfl
            (HbPostExitFields.trans (HbPostExitFields.ofState hstd2) hb_exit_rfl))))

theorem rwSurvivesUnmap_stdStderrFile (C : HbCliLayout) (uBase : BitVec 64) (uRwSz : Nat) :
    RwSurvivesUnmap uBase uRwSz (StdStderrFile C.std) := by
  dsimp only [StdStderrFile]
  repeat first
    | apply rwSurvivesUnmap_sepConj
    | exact rwSurvivesUnmap_pointsTo32 _ _ _ _
    | exact rwSurvivesUnmap_pointsTo64 _ _ _ _
    | exact rwSurvivesUnmap_memRegion _ _ _ _

theorem rwSurvivesUnmap_hbMuslExitGlobalsNoNeedLocks (C : HbCliLayout) (S : HbStartupLayout)
    (finalized : BitVec 8) (uBase : BitVec 64) (uRwSz : Nat) :
    RwSurvivesUnmap uBase uRwSz (HbMuslExitGlobalsNoNeedLocks C S finalized) := by
  dsimp only [HbMuslExitGlobalsNoNeedLocks]
  repeat first
    | apply rwSurvivesUnmap_sepConj
    | exact rwSurvivesUnmap_pointsTo64 _ _ _ _
    | exact rwSurvivesUnmap_pointsTo32 _ _ _ _
    | exact rwSurvivesUnmap_pointsTo8 _ _ _ _
    | exact rwSurvivesUnmap_stdStderrFile C uBase uRwSz

theorem hbPostMain_to_svc_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc sp0 : BitVec 64} {haveLse : BitVec 8} {s : State} {Pre Post F : SepProp}
    {post : State → SepProp → Prop}
    (hc : HbPostMainCode P C S) (hv : C.Valid) (hs : S.Valid C)
    (hd_once : RoDisj C C.std.cleanupOnceAddr 4)
    (hd_exit : RoDisj C C.std.exitingThreadIdAddr 8)
    (hpc : s.pc = C.std.beginShortBacktraceAddr + 0x0c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0x170#64) (hsp_align : s.spAligned = true)
    (hclosure : ∀ (sc : State) (G : SepProp),
      sc.pc = C.std.cleanupClosureAddr → sc.status = .Running →
      sc.sp = sp0 - 0x1b0#64 → sc.spAligned = true →
      sc.readReg64 Reg.lr = C.std.onceCallAddr + 0x11c#64 →
      sc.readReg64 .x0 = sp0 - 0x150#64 →
      ProcessFieldsPreserved s sc →
      (∀ sr : State, sr.pc = C.std.onceCallAddr + 0x11c#64 → sr.status = .Running →
        sr.sp = sc.sp → CalleeSavedPreserved sc sr → HbPostExitFields sc sr →
        RoPostFacts C haveLse sr.mem →
        SepWP P target_pc sr
          ((((sp0 - 0x150#64) ↦₆₄ (sp0 - 0xb4#64)) ∗ ((sp0 - 0xb4#64) ↦₈ 0#8) ∗
            (((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ Post)) ∗ G) post) →
      SepWP P target_pc sc
        ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          StdVtableRo C.std.cleanupVtableAddr C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr ∗
          (((sp0 - 0x150#64) ↦₆₄ (sp0 - 0xb4#64)) ∗ ((sp0 - 0xb4#64) ↦₈ 1#8) ∗ Pre) ∗ G) post)
    (hnext : ∀ sf : State, sf.pc = C.std.sysExitAddr + 0x0c#64 → sf.status = .Running →
      sf.sp = sp0 - 0x50#64 → sf.spAligned = true →
      sf.readReg64 .x8 = 94#64 →
      sf.readReg64 .x0 = ((s.readReg32 .x0).truncate 8).zeroExtend 64 →
      HbPostExitFields s sf →
      SepWP P target_pc sf
        (HbMuslExitGlobalsNoNeedLocks C S 1#8 ∗ ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗
          stackAt (sp0 - 0x30#64) 80 ∗
          ((C.std.cleanupOnceAddr ↦₃₂ 0#32) ∗
            (C.std.exitingThreadIdAddr ↦₆₄ (s.tpidrEl0 - 0xa4#64)) ∗
            Post ∗ HbDead ∗ F)) post) :
    SepWP P target_pc s
      (HbCallerFrames C sp0 ∗ stackAt (sp0 - 0x170#64) 64 ∗
        (C.std.cleanupOnceAddr ↦₃₂ 3#32) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.std.cleanupVtableAddr C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr ∗
        (C.std.exitingThreadIdAddr ↦₆₄ 0#64) ∗
        Pre ∗ (HbMuslExitGlobalsNoNeedLocks C S 0#8 ∗ F)) post := by
  refine hbLangStartPost_wp hc hv hs hd_once hd_exit
    (F := HbMuslExitGlobalsNoNeedLocks C S 0#8 ∗ F)
    (Post := ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ Post)
    hpc hrun hsp hsp_align hclosure fun s_st2 hpc_st2 hrun_st2 hsp_st2 hal_st2 hx0_st2 hex_st2 => ?_
  refine SepWP.weaken_pre
    (P' := HbMuslExitGlobalsNoNeedLocks C S 0#8 ∗ ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗
      stackAt (sp0 - 0x30#64) 80 ∗
      ((C.std.cleanupOnceAddr ↦₃₂ 0#32) ∗
        (C.std.exitingThreadIdAddr ↦₆₄ (s.tpidrEl0 - 0xa4#64)) ∗
        Post ∗ HbDead ∗ F))
    (by sep_frame) ?_
  refine hbMuslExit_to_svc_wp hc.muslExit hs hpc_st2 hrun_st2 hsp_st2 hal_st2
    fun sf hpc_f hrun_f hsp_f hal_f hx8_f hx0_f hex_f => ?_
  refine hnext sf hpc_f hrun_f (by rw [hsp_f]; bv_lin) hal_f hx8_f ?_
    (HbPostExitFields.trans hex_st2 hex_f)
  rw [hx0_f, State.readReg32, hx0_st2]; bv_bits

theorem hbPostMain_to_exit {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {lim : MallocngLimits} {M : MallocngCoreIface P C.mallocng lim} {γ : GhostName}
    {init : Bool} {lc_leak blk_leak : Nat} {e0 : BitVec 32}
    {img : ElfImage} {inputs : ProcessInputs} {post : ProcessOutcome → Prop} {oom : State → Prop}
    {s0 s_ret : State} {sp0 auxvAddr : BitVec 64} {haveLse : BitVec 8}
    {entries : List (BitVec 64 × BitVec 64)} {altOpt : Option (BitVec 64 × Nat)}
    {Tear R_ret : SepProp}
    (hc : HbPostMainCode P C S) (hv : C.Valid) (hs : S.Valid C)
    (htear : ∀ s_t, M.Heap γ lc_leak blk_leak s_t ∗ Tear ⊢
      (C.mallocng.libcNeedLocksAddr ↦₈ 0#8) ∗ (C.mallocng.libcAuxvAddr ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
      ∃∗ R_dead : SepProp, R_dead)
    (hraw : ∀ altBase altRawSz, altOpt = some (altBase, altRawSz) →
      altRawSz = Arm64.pageAlignUp (hbAltstackReqSz entries))
    (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (hbnd_req : hbAltstackReqSz entries ≤ 524288)
    (hload : img.loadState inputs = .ok s0) (hcode_s0 : P.CodeLoaded s0.mem)
    (hst : Steps P s0 s_ret)
    (hpc : s_ret.pc = C.std.beginShortBacktraceAddr + 0x0c#64) (hrun : s_ret.status = .Running)
    (hsp : s_ret.sp = sp0 - 0x170#64) (hsp_align : s_ret.spAligned = true)
    (hsp_lo : 4304 ≤ s_ret.sp.toNat)
    (hpost : post (ProcessOutcome.ofState (((s_ret.readReg32 .x0).truncate 8).zeroExtend 64) s_ret))
    (hm_ret : s_ret.mem ⊨
      ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
        HbCallerFrames C sp0 ∗
        HbPostMainGlobals C S ∗
        HbAltstackInv4k C S altOpt ∗ HbAltstackMapped altOpt ∗
        HbStdoutInv C M γ init ∗
        HbThreadIdInv C s_ret.tpidrEl0 ∗
        M.Heap γ (lc_leak + hbStdoutCost init) (blk_leak + hbStdoutBlocks init) s_ret ∗
        Tear ∗
        (muslErrnoAddr s_ret ↦₃₂ e0) ∗
        stackAt s_ret.sp 4304) ∗ R_ret) :
    ElfImageRunsTo img inputs post oom := by
  have hsp_cl_lo : 4240 ≤ (sp0 - 0x1b0#64).toNat := by
    have heq : sp0 - 0x1b0#64 = s_ret.sp - 64#64 := by rw [hsp]; bv_lin
    rw [heq]; bv_omega
  dsimp only [HbPostMainGlobals] at hm_ret
  rw [hsp, hbStackAt_split (sp0 - 0x170#64) 64 4240,
      show (sp0 - 0x170#64) - 64#64 = sp0 - 0x1b0#64 by bv_lin] at hm_ret
  have hm_safe : s_ret.mem ⊨ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
      ((C.std.cleanupOnceAddr ↦₃₂ 3#32) ∗ (C.std.exitingThreadIdAddr ↦₆₄ 0#64)) ∗
      (HbCallerFrames C sp0 ∗ stackAt (sp0 - 0x170#64) 64 ∗
        StdVtableRo C.std.cleanupVtableAddr C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr ∗
        StdVtableRo C.std.stdoutVtableAddr C.std.stdoutVtableShimAddr C.std.stdoutCleanupClosureAddr ∗
        (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
        HbAltstackInv4k C S altOpt ∗ HbAltstackMapped altOpt ∗
        HbStdoutInv C M γ init ∗
        HbThreadIdInv C s_ret.tpidrEl0 ∗
        M.Heap γ (lc_leak + hbStdoutCost init) (blk_leak + hbStdoutBlocks init) s_ret ∗
        Tear ∗
        (muslErrnoAddr s_ret ↦₃₂ e0) ∗
        stackAt (sp0 - 0x1b0#64) 4240 ∗
        HbMuslExitGlobalsNoNeedLocks C S 0#8 ∗ R_ret) :=
    Satisfies.mono (by sep_frame) hm_ret
  have hSafe := roSafe_of_pre hm_safe
  have hd_once : RoDisj C C.std.cleanupOnceAddr 4 := roSafe_disj32 _ hSafe
  have hd_exit : RoDisj C C.std.exitingThreadIdAddr 8 := roSafe_disj64 _ hSafe
  let Pre_cl : SepProp :=
    (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
    HbStdoutInv C M γ init ∗
    HbThreadIdInv C s_ret.tpidrEl0 ∗
    M.Heap γ (lc_leak + hbStdoutCost init) (blk_leak + hbStdoutBlocks init) s_ret ∗
    Tear ∗
    (muslErrnoAddr s_ret ↦₃₂ e0) ∗
    StdVtableRo C.std.stdoutVtableAddr C.std.stdoutVtableShimAddr C.std.stdoutCleanupClosureAddr ∗
    (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
    HbAltstackInv4k C S altOpt ∗ HbAltstackMapped altOpt ∗
    stackAt (sp0 - 0x1b0#64) 4240
  have hm_pre : s_ret.mem ⊨
      (HbCallerFrames C sp0 ∗ stackAt (sp0 - 0x170#64) 64 ∗
        (C.std.cleanupOnceAddr ↦₃₂ 3#32) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.std.cleanupVtableAddr C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr ∗
        (C.std.exitingThreadIdAddr ↦₆₄ 0#64) ∗
        Pre_cl ∗ (HbMuslExitGlobalsNoNeedLocks C S 0#8 ∗ emp)) ∗ R_ret := by
    dsimp only [Pre_cl]
    exact Satisfies.mono (by sep_frame) hm_ret
  have hwp : SepWP P (C.std.sysExitAddr + 0x0c#64) s_ret
      (HbCallerFrames C sp0 ∗ stackAt (sp0 - 0x170#64) 64 ∗
        (C.std.cleanupOnceAddr ↦₃₂ 3#32) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.std.cleanupVtableAddr C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr ∗
        (C.std.exitingThreadIdAddr ↦₆₄ 0#64) ∗
        Pre_cl ∗ (HbMuslExitGlobalsNoNeedLocks C S 0#8 ∗ emp))
      (fun s_svc _ => s_svc.readReg64 .x8 = 94#64 ∧
        s_svc.readReg64 .x0 = ((s_ret.readReg32 .x0).truncate 8).zeroExtend 64 ∧
        HbPostExitFields s_ret s_svc) := by
    refine hbPostMain_to_svc_wp hc hv hs hd_once hd_exit
      (Post := ∃∗ R_dead : SepProp, R_dead)
      hpc hrun hsp hsp_align
      (fun sc G hpc_c hrun_c hsp_c hal_c hlr_c hx0_c hp_c hcont_c => by
        dsimp only [Pre_cl]
        refine SepWP.weaken_pre (by sep_frame)
          (hbCleanupClosure_wp
            (Extra := StdVtableRo C.std.cleanupVtableAddr C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr)
            hc hv hs htear hraw hnonull hbnd_req
            hpc_c hrun_c hsp_c hal_c hsp_cl_lo hlr_c hx0_c hp_c hcont_c))
      fun sf hpc_f hrun_f _ _ hx8_f hx0_f hex_f =>
        SepWP.done hpc_f hrun_f ⟨hx8_f, hx0_f, hex_f⟩
  obtain ⟨s_svc, hst_svc, ⟨hpc_s, hrun_s, _, _, hx8_s, hx0_s, hex_s⟩ | ⟨_, hfalse⟩⟩ :=
    SepWP.to_reaches_pc hwp hm_pre (hst.codeLoaded hcode_s0)
  · have hst_all := hst.trans hst_svc
    have hfetch_s : Program.pureMem.fetchMem s_svc.mem (C.std.sysExitAddr + 0x0c#64) =
        some (.system false 0#16) := by
      rw [← hc.no_hooks.fetchMem_eq_pureMem]
      exact Program.fetchMem_of_fetch (hst_all.codeLoaded hcode_s0)
        (hbMuslExit_fetch_svc hc.muslExit)
    obtain ⟨sf_final, hst_one, hterm⟩ := step_exit_group_exitsWith hpc_s hrun_s hx8_s hfetch_s
    exact ElfImageRunsTo.of_exitsWith hload
      ⟨sf_final, (hst_all.to_pureMem hc.no_hooks hc.svc_eq).trans hst_one, hterm⟩
      (by simpa only [ProcessOutcome.ofState, hx0_s, hex_s.1, hex_s.2.1] using hpost)
  · exact False.elim (not_satisfies_false_sepConj hfalse)

end CaseStudies.Hashbrown.Proofs.StdCli
