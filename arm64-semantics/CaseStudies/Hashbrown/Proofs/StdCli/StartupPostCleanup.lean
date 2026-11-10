/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.StartupPost
import CaseStudies.Hashbrown.Proofs.StdCli.StdoutInit
import ProofLib.BV

/-!
# Post-Main Altstack Teardown and Cleanup Closure Proofs

Proves placement-generic `SepWP` specifications for `sigaltstack(SS_DISABLE)`, `munmap`,
`std::sys::pal::unix::stack_overflow::imp::drop_handler`, and `std::rt::cleanup`'s `Once` closure,
parameterized over `C : HbCliLayout` and `S : HbStartupLayout`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iLdr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W64 .X64 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iBl " pc:term:arg t:term:arg : term => `(Instr.bl (($t) - ($pc)))

attribute [local simp]
  hbExitF_w64 hbExitF_w32 hbExitF_wReg hbExitF_wV128
  hbExitF_pstate hbExitF_advPC hbExitF_setPC hbExitF_setMem
  hbExitF_setSigAltStack hbExitF_setPhysMemAvail
  calleeSavedVRegs_setSigAltStack_ro calleeSavedVRegs_setPhysMemAvail_ro

attribute [local simp, local wp_norm, local arm64_norm]
  sigAltStack_w64 sigAltStack_w32 sigAltStack_setPC sigAltStack_setMem
  sigAltStack_wReg sigAltStack_pstate
  bv64_add_sub_cancel_local bv64_add_add_sub_cancel_local

private theorem step_sigaltstack_disable {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc ret_pc uss ssSize : BitVec 64} {pad errno0 : BitVec 32}
    (hsvc : P.svc = Syscall.standard)
    (herr : P.hasCode C.std.errnoLocationAddr errnoLocationWords)
    (hret : P.hasCode C.std.syscallRetAddr syscallRetNonnegWords)
    (hret_bl : P.fetch (C.std.syscallRetAddr + 0x24#64) = some (.bl (C.std.errnoLocationAddr - (C.std.syscallRetAddr + 0x24#64))))
    (hret_err : P.hasCode (C.std.syscallRetAddr + 0x28#64)
      [0xaa0003e1#32, 0x4b1303f3#32, 0x92800000#32, 0xb9000033#32, 0x17fffff8#32])
    (hsas_w0 : P.hasCode S.sigaltstackAddr [0xa9bf7bfd#32, 0x910003fd#32, 0xb4000100#32, 0xb9400802#32, 0x370800a2#32,
      0xf9400804#32, 0xd282ffe3#32, 0xeb03009f#32, 0x540000e9#32, 0x37000182#32, 0xd2801088#32, 0xd4000001#32])
    (hsas_bl : P.fetch (S.sigaltstackAddr + 0x30#64) = some (.bl (C.std.syscallRetAddr - (S.sigaltstackAddr + 0x30#64))))
    (hsas_w1 : P.hasCode (S.sigaltstackAddr + 0x34#64) [0xa8c17bfd#32, 0xd65f03c0#32])
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R →
      s.mem ⊨ (((uss ↦₆₄ 0#64) ∗ ((uss + 8#64) ↦₃₂ 2#32) ∗ ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗
        (muslErrnoAddr s ↦₃₂ errno0) ∗ stackAt s.sp 0x30) ∗ (F ∗ R))
    (hpc : s.pc = S.sigaltstackAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = uss) (hx1 : s.readReg64 .x1 = 0#64)
    (huss_ne : uss ≠ 0#64) (huss_fit : uss.toNat + 24 ≤ 2 ^ 64)
    (hnext : ∀ (sf : State) (errno1 : BitVec 32), sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → HbPostExitFields s sf →
      SepWP P target_pc sf ((((uss ↦₆₄ 0#64) ∗ ((uss + 8#64) ↦₃₂ 2#32) ∗ ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗
        (muslErrnoAddr sf ↦₃₂ errno1) ∗ stackAt s.sp 0x30) ∗ F) post) :
    SepWP P target_pc s Pre post := by
  have hret' := hret
  have herr' := herr
  have hret_err' := hret_err
  refine SepWP.weaken_pre_frame (P' := (((uss ↦₆₄ 0#64) ∗ ((uss + 8#64) ↦₃₂ 2#32) ∗ ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗
      (muslErrnoAddr s ↦₃₂ errno0) ∗ stackAt s.sp 0x30) ∗ F)
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have hsp_sub_al : ((s.sp + 0xfffffffffffffff0#64) &&& 0xf#64 == 0#64) = true := by
    simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x10#64 hsp_align
  have hu_f : (uss == 0#64) = false := beq_false_of_ne huss_ne
  have hf_svc : P.fetch (S.sigaltstackAddr + 44#64) = some (.system false 0#16) :=
    Program.fetch_of_hasCode_decodeAt 11 hsas_w0 (by bv_lin) (by decide)
  wp_conv_pre => rw [stackAt_split_cells s.sp 0x20 2 (by decide)]
  simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero,
    sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun w0 => SepWP.exists_elim fun w1 => ?_
  clear hret herr hret_err; wp_steps 7
  by_cases hon : s.sigAltStack.onSigStack (s.sp - 16#64) = false
  · refine SepWP.weaken_pre_frame (P' := stackTAt uss 0#64 2#32 pad ssSize ∗ (optOldStackTAt 0#64 [] ∗ ?_))
      (fun R hm => by dsimp only [stackTAt, optOldStackTAt]; rw [hu_f]; simp only [beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, emp_sepConj]; revert hm; sep_frame) ?_
    refine SepWP.step_svc_sigaltstack (pc := S.sigaltstackAddr + 44#64) (uss := uss) (ssSp := 0#64)
      (ssSize := ssSize) (uoss := 0#64) (ssFlags := 2#32) (pad := pad) (oldBs₀ := [])
      (by wp_ro_simp) (by wp_ro_simp) hf_svc (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
      (Or.inr ⟨huss_fit, by simpa [wp_norm, arm64_norm, bv_lin_norm] using hon, Or.inl rfl⟩)
      (Or.inl rfl) (fun m' => ?_)
      (by rw [_root_.Arm64.Program.evalInst_svc0, hsvc, evalSvc_standard]
          simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable,
            Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable,
            wp_norm, arm64_norm])
    dsimp only []
    wp_conv_pre => dsimp only [stackTAt, optOldStackTAt]; rw [hu_f]; simp only [beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, emp_sepConj]
    conv => arg 3; rw [hu_f]; simp only [Bool.false_eq_true, ↓reduceIte,
      show ((2#32 &&& ~~~SS_AUTODISARM) == SS_DISABLE) = true by decide,
      show ((2#32 &&& SS_AUTODISARM) != 0#32) = false by decide]
    refine step_bl_to (pc := S.sigaltstackAddr + 0x30#64) (dst := C.std.syscallRetAddr) (by wp_ro_simp) (by wp_ro_simp) hsas_bl ?_
    rw [show S.sigaltstackAddr + 0x30#64 + 4#64 = S.sigaltstackAddr + 0x34#64 by bv_lin]
    refine step_syscallRet0 hret' (ret_pc := S.sigaltstackAddr + 0x34#64) (F := ?_)
      (fun R hm => by simp only [wp_norm, arm64_norm, bv_lin_norm] at hm ⊢; revert hm; sep_frame)
      rfl (by wp_ro_simp)
      (by simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x10#64 hsp_align)
      (by wp_ro_simp) (by wp_ro_simp)
      fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 _ hex2 => ?_
    have hsp2_eq : s2.sp = s.sp - 16#64 := by simpa [wp_norm, arm64_norm, bv_lin_norm] using hsp2
    have h16 : s.sp - 16 = s2.sp := by simpa [BitVec.ofNat_eq_ofNat] using hsp2_eq.symm
    have h08 : s.sp - 8 = s2.sp + 8 := by rw [hsp2_eq]; bv_lin
    have hsp_end : s2.sp + 16#64 = s.sp := by rw [hsp2_eq]; bv_lin
    have hsp_al2_raw : (s2.sp &&& 15#64 == 0#64) = true := hsp_al2
    have htp2 : muslErrnoAddr s = muslErrnoAddr s2 := by
      dsimp [muslErrnoAddr]; rw [hex2.2.2.1]; simp [wp_norm, arm64_norm]
    clear hret' herr' hret_err' hsp2 hsp2_eq
    wp_conv_pre => simp only [wp_norm, arm64_norm, bv_lin_norm, BitVec.ofNat_eq_ofNat]; rw [h16, h08]
    wp_steps 2
    refine SepWP.weaken_pre_frame (P' := (((uss ↦₆₄ 0#64) ∗ ((uss + 8#64) ↦₃₂ 2#32) ∗ ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗
        (muslErrnoAddr s2 ↦₃₂ errno0) ∗ stackAt s.sp 0x30) ∗ F)
      (fun R hm => by
        simp only [State.mem_setPC, State.mem_writeReg64] at hm ⊢
        simp only [wp_norm, arm64_norm, bv_lin_norm, BitVec.ofNat_eq_ofNat] at hm
        rw [← h08, ← h16, htp2] at hm; rw [stackAt_split_cells s.sp 0x20 2 (by decide)]; fold_stack_cells) ?_
    refine hnext _ errno0 (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
      (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align)
      ?_ (HbPostExitFields.trans hb_exit_rfl (HbPostExitFields.trans hex2 hb_exit_rfl))
    rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
    simp only [wp_norm, arm64_norm] at g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
    rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]
  · have hon_t : s.sigAltStack.onSigStack (s.sp - 16#64) = true := by
      cases h : s.sigAltStack.onSigStack (s.sp - 16#64) <;> simp_all
    refine SepWP.weaken_pre_frame
      (P' := ((uss ↦₆₄ 0#64) ∗ ((uss + 8#64) ↦₃₂ 2#32) ∗ ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗ ?_)
      (fun R hm => by revert hm; sep_frame) ?_
    refine step_svc_sigaltstack_eperm (pc := S.sigaltstackAddr + 44#64) hsvc
      (by wp_ro_simp) (by wp_ro_simp) hf_svc (by wp_ro_simp) (by wp_ro_simp) huss_ne huss_fit
      (by simpa [wp_norm, arm64_norm, bv_lin_norm] using hon_t) ?_
    rw [show S.sigaltstackAddr + 44#64 + 4#64 = S.sigaltstackAddr + 0x30#64 by bv_lin]
    refine step_bl_to (pc := S.sigaltstackAddr + 0x30#64) (dst := C.std.syscallRetAddr) (by wp_ro_simp) (by wp_ro_simp) hsas_bl ?_
    rw [show S.sigaltstackAddr + 0x30#64 + 4#64 = S.sigaltstackAddr + 0x34#64 by bv_lin]
    refine step_syscallRet_neg1 herr' hret' hret_bl hret_err' (ret_pc := S.sigaltstackAddr + 0x34#64)
      (errno0 := errno0) (F := ?_)
      (fun R hm => by simp only [muslErrnoAddr, wp_norm, arm64_norm, bv_lin_norm] at hm ⊢; revert hm; sep_frame)
      rfl (by wp_ro_simp)
      (by simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x10#64 hsp_align)
      (by wp_ro_simp) (by wp_ro_simp)
      fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hex2 => ?_
    have hsp2_eq : s2.sp = s.sp - 16#64 := by simpa [wp_norm, arm64_norm, bv_lin_norm] using hsp2
    have h16 : s.sp - 16 = s2.sp := by simpa [BitVec.ofNat_eq_ofNat] using hsp2_eq.symm
    have h08 : s.sp - 8 = s2.sp + 8 := by rw [hsp2_eq]; bv_lin
    have hsp_end : s2.sp + 16#64 = s.sp := by rw [hsp2_eq]; bv_lin
    have hsp_al2_raw : (s2.sp &&& 15#64 == 0#64) = true := hsp_al2
    clear hret' herr' hret_err' hsp2 hsp2_eq
    wp_conv_pre => simp only [wp_norm, arm64_norm, bv_lin_norm, BitVec.ofNat_eq_ofNat]; rw [h16, h08]
    wp_steps 2
    refine SepWP.weaken_pre_frame (P' := (((uss ↦₆₄ 0#64) ∗ ((uss + 8#64) ↦₃₂ 2#32) ∗ ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗
        (muslErrnoAddr s2 ↦₃₂ 1#32) ∗ stackAt s.sp 0x30) ∗ F)
      (fun R hm => by
        simp only [State.mem_setPC, State.mem_writeReg64] at hm ⊢
        simp only [wp_norm, arm64_norm, bv_lin_norm, BitVec.ofNat_eq_ofNat] at hm
        rw [← h08, ← h16] at hm; rw [stackAt_split_cells s.sp 0x20 2 (by decide)]; fold_stack_cells) ?_
    refine hnext _ 1#32 (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
      (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align)
      ?_ (HbPostExitFields.trans hb_exit_rfl (HbPostExitFields.trans hex2 hb_exit_rfl))
    rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
    simp only [wp_norm, arm64_norm] at g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
    rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]

theorem step_stlr64_ro {prog : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc pc ea val : BitVec 64} {s : State} {P P' : SepProp} {post : State → SepProp → Prop}
    {rn rt : Reg}
    (hro : RoPostFacts C haveLse s.mem) (hd : RoDisj C ea 8)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .X64 false rn rt))
    (hsp : checkRegSPAligned s rn = true) (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .X64 ea = true) (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P')
    (hnext : ∀ m' : Memory, RoPostFacts C haveLse m' →
      SepWP prog target_pc ((s.setPC (pc + 4#64)).setMem m') P' post) :
    SepWP prog target_pc s P post :=
  SepWP.step_stlr64 hpc hrun hfetch hsp haddr halign hval hstore
    (show (s.setMem (s.mem.write64 ea val)).setPC (pc + 4#64) =
      (s.setPC (pc + 4#64)).setMem (s.mem.write64 ea val) by cases s; rfl)
    (hnext (s.mem.write64 ea val) (roPostFacts_write64 hd hro))

private theorem step_vmWait0_wp {P : Program} {S : HbStartupLayout}
    {target_pc ret_pc : BitVec 64}
    (hvw : P.hasCode S.vmWaitAddr [0xd65f03c0#32])
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = S.vmWaitAddr) (hrun : s.status = .Running)
    (hlr : s.readReg64 .lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → HbPostExitFields s sf →
      SepWP P target_pc sf F post) :
    SepWP P target_pc s F post := by
  wp_steps
  exact hnext _ (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
    (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hb_exit_rfl

private theorem step_munmapPre_to_svc_wp {P : Program} {S : HbStartupLayout}
    {target_pc ret_pc uBase : BitVec 64} {reqSz : Nat}
    (hmw_w0 : P.hasCode S.munmapWrapperAddr [0xa9be7bfd#32, 0x910003fd#32, 0xa90153f3#32, 0xaa0003f4#32, 0xaa0103f3#32])
    (hmw_bl0 : P.fetch (S.munmapWrapperAddr + 0x14#64) = some (.bl (S.vmWaitAddr - (S.munmapWrapperAddr + 0x14#64))))
    (hmw_w1 : P.hasCode (S.munmapWrapperAddr + 0x18#64) [0xaa1403e0#32, 0xaa1303e1#32, 0xd2801ae8#32, 0xd4000001#32])
    (hvw : P.hasCode S.vmWaitAddr [0xd65f03c0#32])
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = S.munmapWrapperAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = uBase)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (reqSz + 4096))
    (hnext : ∀ sf : State, sf.pc = S.munmapWrapperAddr + 0x24#64 → sf.status = .Running →
      sf.sp = s.sp - 0x20#64 → sf.spAligned = true →
      sf.readReg64 .x0 = uBase → sf.readReg64 .x1 = BitVec.ofNat 64 (reqSz + 4096) →
      sf.readReg64 .x8 = 215#64 →
      sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) →
      sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      Arm64.calleeSavedVRegs sf = Arm64.calleeSavedVRegs s →
      HbPostExitFields s sf →
      SepWP P target_pc sf
        (((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 24#64) ↦₆₄ ret_pc) ∗
         ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗
         stackAt (s.sp - 0x20#64) 0x20 ∗ F) post) :
    SepWP P target_pc s (stackAt s.sp 0x40 ∗ F) post := by
  have hsp20_al : ((s.sp + 0xffffffffffffffe0#64) &&& 0xf#64 == 0#64) = true := by
    simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align
  rw [stackAt_split_cells s.sp 0x20 4 (by decide)]; unfold_stack_cells 4
  wp_steps 5
  refine step_bl_to (pc := S.munmapWrapperAddr + 0x14#64) (dst := S.vmWaitAddr) (by wp_ro_simp) (by wp_ro_simp) hmw_bl0 ?_
  rw [show S.munmapWrapperAddr + 0x14#64 + 4#64 = S.munmapWrapperAddr + 0x18#64 by bv_lin]
  refine step_vmWait0_wp hvw
    (ret_pc := S.munmapWrapperAddr + 0x18#64) rfl (by wp_ro_simp) (by wp_ro_simp)
    fun s2 hpc2 hrun2 hsp2 hcs2 hex2 => ?_
  have hx20_2 : s2.readReg64 (.gpr 20#5) = uBase := by
    have := hcs2.readReg64_x20; simpa [wp_norm, arm64_norm, hx0] using this
  have hx19_2 : s2.readReg64 (.gpr 19#5) = BitVec.ofNat 64 (reqSz + 4096) := by
    have := hcs2.readReg64_x19; simpa [wp_norm, arm64_norm, hx1] using this
  have hsp2_eq : s2.sp = s.sp - 32#64 := by simpa [wp_norm, arm64_norm, bv_lin_norm] using hsp2
  have hsp_al2 : s2.spAligned = true := by
    simp only [State.spAligned, hsp2_eq]; simpa [BitVec.sub_eq_add_neg] using hsp20_al
  clear hsp2
  wp_steps 3
  refine SepWP.weaken_pre_frame
    (P' := ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 24#64) ↦₆₄ ret_pc) ∗
      ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗
      stackAt (s.sp - 0x20#64) 0x20 ∗ F)
    (fun R hm => by simp only [wp_norm, arm64_norm, bv_lin_norm] at hm ⊢; revert hm; sep_frame) ?_
  exact hnext _ (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al2)
    (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
    (by have := hcs2.readReg64_x27; simpa [wp_norm, arm64_norm] using this)
    (by have := hcs2.readReg64_x28; simpa [wp_norm, arm64_norm] using this)
    (by have := hcs2.2.2.2.2.2.2.2.2.2.2.2; simpa [wp_norm, arm64_norm] using this)
    (HbPostExitFields.trans hb_exit_rfl (HbPostExitFields.trans hex2 hb_exit_rfl))

private theorem step_munmapPost_from_after_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {haveLse : BitVec 8} {target_pc ret_pc sp0 sv29 sv19 sv20 : BitVec 64}
    (hmw_bl1 : P.fetch (S.munmapWrapperAddr + 0x28#64) = some (.bl (C.std.syscallRetAddr - (S.munmapWrapperAddr + 0x28#64))))
    (hmw_w2 : P.hasCode (S.munmapWrapperAddr + 0x2c#64) [0xa94153f3#32, 0xa8c27bfd#32, 0xd65f03c0#32])
    (hret : P.hasCode C.std.syscallRetAddr syscallRetNonnegWords)
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hro : RoPostFacts C haveLse s.mem) (hd : RoDisj C (sp0 - 0x40#64) 32)
    (hpc : s.pc = S.munmapWrapperAddr + 0x28#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0x20#64) (hsp_align : (sp0 &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → sf.spAligned = true →
      sf.readReg64 (.gpr 19#5) = sv19 → sf.readReg64 (.gpr 20#5) = sv20 → sf.readReg64 (.gpr 29#5) = sv29 →
      CalleeSavedPreserved (((s.writeReg64 (.gpr 19#5) sv19).writeReg64 (.gpr 20#5) sv20).writeReg64 (.gpr 29#5) sv29) sf →
      HbPostExitFields s sf → RoPostFacts C haveLse sf.mem →
      SepWP P target_pc sf (stackAt sp0 0x40 ∗ F) post) :
    SepWP P target_pc s
      (((sp0 - 32#64) ↦₆₄ sv29) ∗ ((sp0 - 24#64) ↦₆₄ ret_pc) ∗
       ((sp0 - 16#64) ↦₆₄ sv19) ∗ ((sp0 - 8#64) ↦₆₄ sv20) ∗
       stackAt (sp0 - 0x20#64) 0x20 ∗ F) post := by
  have hret' := hret
  have hsp_sub_al : s.spAligned = true := by
    simp only [State.spAligned, hsp]; simp only [beq_iff_eq] at hsp_align ⊢; bv_bits
  refine step_bl_to (pc := S.munmapWrapperAddr + 0x28#64) (dst := C.std.syscallRetAddr) hpc hrun hmw_bl1 ?_
  rw [show S.munmapWrapperAddr + 0x28#64 + 4#64 = S.munmapWrapperAddr + 0x2c#64 by bv_lin]
  let s1 := (s.writeReg64 .lr (S.munmapWrapperAddr + 0x2c#64)).setPC C.std.syscallRetAddr
  have hd' : RoDisj C (s1.sp - 32#64) 32 := by
    simpa [s1, wp_norm, arm64_norm, hsp, show sp0 - 0x20#64 - 32#64 = sp0 - 0x40#64 by bv_lin] using hd
  refine SepWP.weaken_pre_frame
    (P' := stackAt s1.sp 0x20 ∗
      (((sp0 - 32#64) ↦₆₄ sv29) ∗ ((sp0 - 24#64) ↦₆₄ ret_pc) ∗ ((sp0 - 16#64) ↦₆₄ sv19) ∗ ((sp0 - 8#64) ↦₆₄ sv20) ∗ F))
    (fun R hm => by simp only [s1, wp_norm, arm64_norm, hsp]; revert hm; sep_frame) ?_
  refine step_syscallRet0_ro (ret_pc := S.munmapWrapperAddr + 0x2c#64) hret' hro hd' rfl (by simp [wp_norm, arm64_norm, hrun])
    (by simpa [ s1, State.spAligned, wp_norm, arm64_norm] using hsp_sub_al) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx0])
    fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hx0_2 hex2 hro2 => ?_
  have hsp2_eq : s2.sp = sp0 - 32#64 := by simpa [s1, wp_norm, arm64_norm, hsp] using hsp2
  have h32 : sp0 - 32#64 = s2.sp := hsp2_eq.symm
  have h24 : sp0 - 24#64 = s2.sp + 8#64 := by rw [hsp2_eq]; bv_lin
  have h16 : sp0 - 16#64 = s2.sp + 16#64 := by rw [hsp2_eq]; bv_lin
  have h08 : sp0 - 8#64 = s2.sp + 24#64 := by rw [hsp2_eq]; bv_lin
  have hsp_end : s2.sp + 32#64 = sp0 := by rw [hsp2_eq]; bv_lin
  have hsp_al2_raw : (s2.sp &&& 15#64 == 0#64) = true := hsp_al2
  clear hret' hsp2 hsp2_eq
  wp_conv_pre =>
    simp only [s1, wp_norm, arm64_norm, hsp]
    rw [h32, h24, h16, h08]
  wp_steps 3
  refine SepWP.weaken_pre_frame (P' := stackAt sp0 0x40 ∗ F)
    (fun R hm => by
      simp only [State.mem_setPC, State.mem_writeReg64] at hm ⊢
      rw [← h08, ← h16, ← h24, ← h32] at hm
      rw [stackAt_split_cells sp0 0x20 4 (by decide)]; fold_stack_cells) ?_
  refine hnext _ (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align)
    (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) ?_
    (HbPostExitFields.trans hb_exit_rfl (HbPostExitFields.trans hex2 hb_exit_rfl)) hro2
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨_, _, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
  simp only [wp_norm, arm64_norm] at g21 g22 g23 g24 g25 g26 g27 g28 gv
  rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g21, g22, g23, g24, g25, g26, g27, g28, gv]

@[local simp, local wp_norm, local arm64_norm] private theorem applyWriteback_none (s : State) :
    applyWriteback s none = s := rfl

private theorem HbPostExitFields.of_std_chain {s0 s1 s2 sf : State}
    (h12 : StdStatePreserved s1 s2)
    (h01 : HbPostExitFields s0 s1 := by simp [HbPostExitFields.rfl])
    (h2f : HbPostExitFields s2 sf := by simp [HbPostExitFields.rfl]) :
    HbPostExitFields s0 sf :=
  HbPostExitFields.trans h01 (HbPostExitFields.trans (.ofState h12) h2f)

theorem sepWP_with_roPostFacts {P : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc : BitVec 64} {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hf : Pre ⊢ ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64)) ∗ F := by sep_frame)
    (h : RoPostFacts C haveLse s.mem → SepWP P target_pc s Pre post) :
    SepWP P target_pc s Pre post := by
  apply SepWP.of_reaches_pc; intro R hm
  have hm' : s.mem ⊨ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hf) hm
  exact SepWP.to_reaches_pc (h (roPostFacts_of_pre hm')) hm

private theorem step_dropHandler_from_cc_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {haveLse : BitVec 8} {target_pc ret_pc sp0 sv29 sv26 sv25 sv24 sv23 sv22 sv21 sv20 sv19 : BitVec 64}
    (hc : CodeChunks P (hbDropHandlerChunks C S))
    (hswp4 : hasInstrs P C.std.swp4RelAddr (swp4RelInstrs C.std))
    (hal_lock : MemWidth.isAligned .W32 S.threadInfoLockAddr = true)
    (hal_lock8 : MemWidth.isAligned .X64 (S.threadInfoLockAddr + 8#64) = true)
    (_hal_root : MemWidth.isAligned .X64 S.threadInfoRootAddr = true)
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hro : RoPostFacts C haveLse s.mem)
    (hd_lock4 : RoDisj C S.threadInfoLockAddr 4)
    (hd_lock8 : RoDisj C (S.threadInfoLockAddr + 8#64) 8)
    (hpc : s.pc = C.dropStackHandlerAddr + 0xcc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0xf0#64) (hsp_align : (sp0 &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 (.gpr 0#5) = 0#64)
    (hx21 : s.readReg64 (.gpr 21#5) = C.globalPanicCountAddr)
    (hx22 : s.readReg64 (.gpr 22#5) = 0#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → sf.spAligned = true →
      CalleeSavedPreserved
        ((((((((((s.writeReg64 (.gpr 19#5) sv19).writeReg64 (.gpr 20#5) sv20).writeReg64 (.gpr 21#5) sv21).writeReg64 (.gpr 22#5) sv22).writeReg64 (.gpr 23#5) sv23).writeReg64 (.gpr 24#5) sv24).writeReg64 (.gpr 25#5) sv25).writeReg64 (.gpr 26#5) sv26).writeReg64 (.gpr 29#5) sv29)) sf →
      HbPostExitFields s sf → RoPostFacts C haveLse sf.mem →
      SepWP P target_pc sf
        (stackAt sp0 0xf0 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
         (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
         ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗ F) post) :
    SepWP P target_pc s
      (((S.threadInfoLockAddr + 8#64) ↦₆₄ (s.tpidrEl0 - 164#64)) ∗
       ((sp0 - 80#64) ↦₆₄ sv29) ∗ ((sp0 - 72#64) ↦₆₄ ret_pc) ∗
       ((sp0 - 64#64) ↦₆₄ sv26) ∗ ((sp0 - 56#64) ↦₆₄ sv25) ∗
       ((sp0 - 48#64) ↦₆₄ sv24) ∗ ((sp0 - 40#64) ↦₆₄ sv23) ∗
       ((sp0 - 32#64) ↦₆₄ sv22) ∗ ((sp0 - 24#64) ↦₆₄ sv21) ∗
       ((sp0 - 16#64) ↦₆₄ sv20) ∗ ((sp0 - 8#64) ↦₆₄ sv19) ∗
       stackAt (sp0 - 0x50#64) 0xa0 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
       (S.threadInfoLockAddr ↦₃₂ 1#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗ F) post := by
  have hsp_sub_al : ((sp0 - 0xf0#64) &&& 15#64 == 0#64) = true := by
    simp only [beq_iff_eq] at hsp_align ⊢; bv_bits
  hb_unpack_code hbDropHandlerChunks hc
  wp_steps; wp_steps; wp_steps
  have hdec_stlr : P.fetch (C.dropStackHandlerAddr + 0x2b4#64) =
      some (.ldarStlr .X64 false (.gpr 23#5) .xzr) :=
    Program.fetch_of_hasWords_getElem_decode 0 _
      (by with_reducible assumption : P.hasCode (C.dropStackHandlerAddr + 692#64) _)
      (by bv_lin) rfl (by decide)
  refine step_stlr64_ro (val := 0#64) hro hd_lock8 (by wp_ro_simp) (by wp_ro_simp) hdec_stlr rfl
    (by wp_ro_simp) hal_lock8 (by wp_ro_simp) (by wp_sep_access) fun m5 hro5 => ?_
  rw [show C.dropStackHandlerAddr + 0x2b4#64 + 4#64 = C.dropStackHandlerAddr + 0x2b8#64 by bv_lin]
  wp_steps 1
  refine step_ldr64_panic_ro (addr := C.dropStackHandlerAddr + 0x2b4#64) 2 (C.dropStackHandlerAddr + 0x2c0#64) hro5 (hnext := ?_)
  wp_steps; wp_steps; wp_steps; wp_steps
  refine call_swp4Rel_ro hswp4 hro5 hd_lock4 hal_lock (ret_pc := C.dropStackHandlerAddr + 0x2d8#64)
    (ptr := S.threadInfoLockAddr) (v0 := 1#32) (new := 0#32)
    (hnext := fun s6 hpc6 hrun6 hsp6 hcs6 hstd6 hx0_6 hro6 => ?_)
  have hsp6_eq : s6.sp = sp0 - 0xf0#64 := by simpa [wp_norm, arm64_norm, hsp] using hsp6
  have hsp6_al : (s6.sp &&& 15#64 == 0#64) = true := by simpa [hsp6_eq] using hsp_sub_al
  clear hsp6
  wp_steps; wp_steps
  refine SepWP.weaken_pre_frame
    (P' := stackAt sp0 0xf0 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
      (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
      ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗ F)
    (fun R hm => by
      rw [stackAt_split_cells sp0 0xa0 10 (by decide)]; hb_repack_cells) ?_
  refine hnext _ (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, bv_lin_norm] using hsp_align) ?_
    (HbPostExitFields.of_std_chain hstd6) (by simpa only [wp_norm, arm64_norm] using hro6)
  hb_unpack_cs hcs6; hb_close_cs

private theorem step_dropHandler_from_68_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {haveLse : BitVec 8} {target_pc ret_pc sp0 sv29 sv26 sv25 sv24 sv23 sv22 sv21 sv20 sv19 : BitVec 64}
    (hc : CodeChunks P (hbDropHandlerChunks C S))
    (herr : P.hasCode C.std.errnoLocationAddr errnoLocationWords)
    (hcas4 : hasInstrs P C.std.cas4AcqAddr (cas4AcqInstrs C.std))
    (hcas8 : hasInstrs P C.std.cas8AcqAddr (cas8AcqInstrs C.std))
    (hswp4 : hasInstrs P C.std.swp4RelAddr (swp4RelInstrs C.std))
    (hal_lock : MemWidth.isAligned .W32 S.threadInfoLockAddr = true)
    (hal_lock8 : MemWidth.isAligned .X64 (S.threadInfoLockAddr + 8#64) = true)
    (hal_root : MemWidth.isAligned .X64 S.threadInfoRootAddr = true)
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hro : RoPostFacts C haveLse s.mem)
    (hd_lock4 : RoDisj C S.threadInfoLockAddr 4)
    (hd_lock8 : RoDisj C (S.threadInfoLockAddr + 8#64) 8)
    (hd_stk : RoDisj C (sp0 - 0xf0#64) 0xf0)
    (hpc : s.pc = C.dropStackHandlerAddr + 0x68#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0xf0#64) (hsp_align : (sp0 &&& 15#64 == 0#64) = true)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → sf.spAligned = true →
      CalleeSavedPreserved
        ((((((((((s.writeReg64 (.gpr 19#5) sv19).writeReg64 (.gpr 20#5) sv20).writeReg64 (.gpr 21#5) sv21).writeReg64 (.gpr 22#5) sv22).writeReg64 (.gpr 23#5) sv23).writeReg64 (.gpr 24#5) sv24).writeReg64 (.gpr 25#5) sv25).writeReg64 (.gpr 26#5) sv26).writeReg64 (.gpr 29#5) sv29)) sf →
      HbPostExitFields s sf → RoPostFacts C haveLse sf.mem →
      SepWP P target_pc sf
        (stackAt sp0 0xf0 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
         (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
         ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗ F) post) :
    SepWP P target_pc s
      (stackAt (sp0 - 0x50#64) 0xa0 ∗
       ((sp0 - 80#64) ↦₆₄ sv29) ∗ ((sp0 - 72#64) ↦₆₄ ret_pc) ∗
       ((sp0 - 64#64) ↦₆₄ sv26) ∗ ((sp0 - 56#64) ↦₆₄ sv25) ∗
       ((sp0 - 48#64) ↦₆₄ sv24) ∗ ((sp0 - 40#64) ↦₆₄ sv23) ∗
       ((sp0 - 32#64) ↦₆₄ sv22) ∗ ((sp0 - 24#64) ↦₆₄ sv21) ∗
       ((sp0 - 16#64) ↦₆₄ sv20) ∗ ((sp0 - 8#64) ↦₆₄ sv19) ∗
       (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
       (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
       ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗ F) post := by
  have hd_stk_d8 : RoDisj C (sp0 - 216#64) 1 := roDisj_sub hd_stk 24 1
  have hd_stk_e8 : RoDisj C (sp0 - 232#64) 8 := roDisj_sub hd_stk 8 8
  have hd_stk_e0 : RoDisj C (sp0 - 224#64) 8 := roDisj_sub hd_stk 16 8
  have hsp_sub_al : ((sp0 - 0xf0#64) &&& 15#64 == 0#64) = true := by
    simp only [beq_iff_eq] at hsp_align ⊢; bv_bits
  have hsp_al_s : s.spAligned = true := by simpa [State.spAligned, hsp] using hsp_sub_al
  hb_unpack_code hbDropHandlerChunks hc
  rw [hbStackAt_split (sp0 - 0x50#64) 0x80 0x20, show sp0 - 0x50#64 - 128#64 = sp0 - 0xd0#64 by bv_lin,
      stackAt_eq_cells (sp0 - 0xd0#64) 4]
  hb_unpack_cells 4; simp only [sepConj_assoc]
  rw [pointsTo64_split32_sub (sp0 - 0xd0#64) 8#64 4#64, hbPointsTo32_split8_sub (sp0 - 0xd0#64) 8#64 7#64 6#64 5#64]
  wp_steps; wp_steps; wp_steps; wp_steps; wp_steps
  refine call_cas4Acq_ro hcas4 hro hd_lock4 hal_lock (ret_pc := C.dropStackHandlerAddr + 0x88#64)
    (ptr := S.threadInfoLockAddr) (v0 := 0#32) (new := 1#32)
    (hnext := fun s1 hpc1 hrun1 hsp1 hcs1 hstd1 hx0_1 hro1 => ?_)
  have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
  have hx19_1 : s1.readReg64 (.gpr 19#5) = s.tpidrEl0 - 164#64 := by
    have := hcs1.readReg64_x19; simpa [wp_norm, arm64_norm] using this
  have hx20_1 : s1.readReg64 (.gpr 20#5) = S.threadInfoLockAddr := by
    have := hcs1.readReg64_x20; simpa [wp_norm, arm64_norm] using this
  have hsp1_eq : s1.sp = sp0 - 0xf0#64 := by simpa [wp_norm, arm64_norm, hsp] using hsp1
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1_eq] using hsp_sub_al
  wp_steps; wp_steps
  refine step_ldr64_panic_ro (addr := C.dropStackHandlerAddr + 0x98#64) 0 (C.dropStackHandlerAddr + 0x9c#64) hro1 (hnext := ?_)
  wp_steps 7
  have hdec_strb : P.fetch (C.dropStackHandlerAddr + 0xb8#64) =
      some (.str .B8 (.gpr 22#5) (.Offset .sp 24#64)) :=
    Program.fetch_of_hasWords_getElem_decode 8 _
      (by with_reducible assumption : P.hasCode (C.dropStackHandlerAddr + 152#64) _)
      (by bv_lin) rfl (by decide)
  refine step_str8_ro (wb := none) (val := 0#8) hro1 hd_stk_d8 (by wp_ro_simp) (by wp_ro_simp) hdec_strb
    (by simpa [checkAddrSPAligned, State.spAligned, wp_norm, arm64_norm, hsp1_eq] using hsp_sub_al)
    (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm, hsp1_eq]; try bv_lin) (by wp_ro_simp)
    (by wp_sep_access) rfl fun m2 hro2 => ?_
  rw [applyWriteback_none, show C.dropStackHandlerAddr + 0xb8#64 + 4#64 = C.dropStackHandlerAddr + 0xbc#64 by bv_lin]
  wp_steps 2
  have hdec_stp : P.fetch (C.dropStackHandlerAddr + 0xc4#64) =
      some (.stp .W64 (.gpr 8#5) (.gpr 20#5) (.Offset .sp 8#64)) :=
    Program.fetch_of_hasWords_getElem_decode 11 _
      (by with_reducible assumption : P.hasCode (C.dropStackHandlerAddr + 152#64) _)
      (by bv_lin) rfl (by decide)
  refine step_stp64_ro (wb := none) (v1 := 0#64) (v2 := S.threadInfoLockAddr)
    hro2 hd_stk_e8 hd_stk_e0 (by wp_ro_simp) (by wp_ro_simp) hdec_stp
    (by simpa [checkAddrSPAligned, State.spAligned, wp_norm, arm64_norm, hsp1_eq] using hsp_sub_al)
    (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm, hsp1_eq]; try bv_lin) (by bv_lin)
    (by wp_ro_simp) (by wp_ro_simp) (by wp_sep_access) (by wp_sep_access) rfl fun m3 hro3 => ?_
  rw [applyWriteback_none, show C.dropStackHandlerAddr + 0xc4#64 + 4#64 = C.dropStackHandlerAddr + 0xc8#64 by bv_lin]
  refine SepWP.weaken_pre_frame
    (P' := ((sp0 - 80#64) ↦₆₄ sv29) ∗ ((sp0 - 72#64) ↦₆₄ ret_pc) ∗
       ((sp0 - 64#64) ↦₆₄ sv26) ∗ ((sp0 - 56#64) ↦₆₄ sv25) ∗
       ((sp0 - 48#64) ↦₆₄ sv24) ∗ ((sp0 - 40#64) ↦₆₄ sv23) ∗
       ((sp0 - 32#64) ↦₆₄ sv22) ∗ ((sp0 - 24#64) ↦₆₄ sv21) ∗
       ((sp0 - 16#64) ↦₆₄ sv20) ∗ ((sp0 - 8#64) ↦₆₄ sv19) ∗
       stackAt (sp0 - 0x50#64) 0xa0 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
       (S.threadInfoLockAddr ↦₃₂ 1#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
       ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗ F)
    (fun R hm => by
      simp only [sepConj_assoc] at hm
      rw [hbPointsTo8_combine32_sub sp0 216#64 215#64 214#64 213#64,
          pointsTo32_combine64_sub sp0 216#64 212#64] at hm
      rw [hbStackAt_split (sp0 - 0x50#64) 0x80 0x20,
          show sp0 - 0x50#64 - 128#64 = sp0 - 0xd0#64 by bv_lin,
          stackAt_eq_cells (sp0 - 0xd0#64) 4]
      hb_repack_cells) ?_
  wp_steps
  refine call_cas8Acq_ro hcas8 hro3 hd_lock8 hal_lock8 (ret_pc := C.dropStackHandlerAddr + 0xcc#64)
    (ptr := S.threadInfoLockAddr + 8#64) (v0 := 0#64) (new := s.tpidrEl0 - 164#64)
    (hnext := fun s4 hpc4 hrun4 hsp4 hcs4 hstd4 hx0_4 hro4 => ?_)
  have hx21_4 : s4.readReg64 (.gpr 21#5) = C.globalPanicCountAddr := by
    have := hcs4.readReg64_x21; simpa [wp_norm, arm64_norm, hbBv64_add_sub_cancel] using this
  have hx22_4 : s4.readReg64 (.gpr 22#5) = 0#64 := by
    have := hcs4.readReg64_x22; simpa [wp_norm, arm64_norm] using this
  have hsp4_eq : s4.sp = sp0 - 0xf0#64 := by simpa [wp_norm, arm64_norm, hsp1_eq] using hsp4
  have htpidr4 : s4.tpidrEl0 = s.tpidrEl0 := by
    have h4 := hstd4.2.2.1
    have h1 := hstd1.2.2.1
    simpa [wp_norm, arm64_norm, h1] using h4
  rw [← htpidr4]
  refine step_dropHandler_from_cc_wp hc hswp4 hal_lock hal_lock8 hal_root hro4 hd_lock4 hd_lock8
    hpc4 hrun4 hsp4_eq hsp_align hx0_4 hx21_4 hx22_4
    fun sf hpc_f hrun_f hsp_f hsp_al_f hcs_f hex_f hro_f => ?_
  refine hnext sf hpc_f hrun_f hsp_f hsp_al_f ?_
    (HbPostExitFields.trans (HbPostExitFields.of_std_chain hstd1)
      (HbPostExitFields.trans (.ofState hstd4) hex_f)) hro_f
  hb_unpack_cs hcs1; hb_unpack_cs hcs4; hb_unpack_cs hcs_f; hb_close_cs

theorem hbDropHandler_none_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {haveLse : BitVec 8} {target_pc ret_pc : BitVec 64}
    (hc : CodeChunks P (hbDropHandlerChunks C S))
    (herr : P.hasCode C.std.errnoLocationAddr errnoLocationWords)
    (hcas4 : hasInstrs P C.std.cas4AcqAddr (cas4AcqInstrs C.std))
    (hcas8 : hasInstrs P C.std.cas8AcqAddr (cas8AcqInstrs C.std))
    (hswp4 : hasInstrs P C.std.swp4RelAddr (swp4RelInstrs C.std))
    (hal_lock : MemWidth.isAligned .W32 S.threadInfoLockAddr = true)
    (hal_lock8 : MemWidth.isAligned .X64 (S.threadInfoLockAddr + 8#64) = true)
    (hal_root : MemWidth.isAligned .X64 S.threadInfoRootAddr = true)
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hd_lock4 : RoDisj C S.threadInfoLockAddr 4)
    (hd_lock8 : RoDisj C (S.threadInfoLockAddr + 8#64) 8)
    (hd_stk : RoDisj C (s.sp - 0xf0#64) 0xf0)
    (hpc : s.pc = C.dropStackHandlerAddr) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → HbPostExitFields s sf → RoPostFacts C haveLse sf.mem →
      SepWP P target_pc sf
        (stackAt s.sp 0xf0 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
         (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
         ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
         ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ F)) post) :
    SepWP P target_pc s
      (stackAt s.sp 0xf0 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
       (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
       ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
       ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ F)) post := by
  have hx0' : s.readReg64 (.gpr 0#5) = 0#64 := hx0
  have hlr' : s.readReg64 (.gpr 30#5) = ret_pc := hlr
  have hsp_align_raw : (s.sp &&& 15#64 == 0#64) = true := hsp_align
  have hsp_sub_al : ((s.sp - 0xf0#64) &&& 15#64 == 0#64) = true := by
    simp only [beq_iff_eq] at hsp_align_raw ⊢; bv_bits
  have hdh_w0 : P.hasCode C.dropStackHandlerAddr
      [0xd103c3ff#32, 0xa90a7bfd#32, 0xa90b67fa#32, 0xa90c5ff8#32, 0xa90d57f6#32,
       0xa90e4ff4#32, 0x910283fd#32, 0xb4000260#32, 0xaa0003f3#32, 0x52800660#32] := hc.1
  rw [stackAt_split_cells s.sp 0xa0 10 (by decide)]; hb_unpack_cells 10; simp only [sepConj_assoc]
  wp_steps 8
  refine sepWP_with_roPostFacts (C := C) (haveLse := haveLse) (h := fun hro_curr => ?_)
  refine step_dropHandler_from_68_wp (sp0 := s.sp) hc herr hcas4 hcas8 hswp4 hal_lock hal_lock8 hal_root
    hro_curr hd_lock4 hd_lock8 hd_stk (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) hsp_align_raw
    fun sf hpc_f hrun_f hsp_f hsp_al_f hcs_f hex_f hro_f => ?_
  refine hnext sf hpc_f hrun_f hsp_f hsp_al_f ?_ (HbPostExitFields.trans hb_exit_rfl hex_f) hro_f
  hb_unpack_cs hcs_f; hb_close_cs

private theorem csel_altstack_add_4096 (entries : List (BitVec 64 × BitVec 64))
    (hbnd : hbAltstackReqSz entries ≤ 524288) :
    (if BitVec.ult 0x3000#64 (hbAuxvLookup entries 51#64)
     then hbAuxvLookup entries 51#64
     else 0x3000#64) + 4096#64 =
    BitVec.ofNat 64 (hbAltstackReqSz entries + 4096) := by
  apply BitVec.eq_of_toNat_eq
  have h1 := hbAltstackRawSz_eq_csel entries
  rw [hbAltstackRawSz_eq_reqSz] at h1
  have h4096 : (4096#64 : BitVec 64).toNat = 4096 := rfl
  rw [BitVec.toNat_add, h1, h4096, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem stackAt_20_20_to_10_30 (sp : BitVec 64) (R : SepProp) :
    stackAt (sp - 240#64) 0x20 ∗ stackAt (sp - 272#64) 0x20 ∗ R =
    stackAt (sp - 288#64) 0x10 ∗ stackAt (sp - 240#64) 0x30 ∗ R := by
  have h1 : stackAt (sp - 240#64) 0x40 = stackAt (sp - 272#64) 0x20 ∗ stackAt (sp - 240#64) 0x20 := by
    rw [hbStackAt_split (sp - 240#64) 0x20 0x20, show sp - 240#64 - 32#64 = sp - 272#64 by bv_lin]
  have h2 : stackAt (sp - 240#64) 0x40 = stackAt (sp - 288#64) 0x10 ∗ stackAt (sp - 240#64) 0x30 := by
    rw [hbStackAt_split (sp - 240#64) 0x30 0x10, show sp - 240#64 - 48#64 = sp - 288#64 by bv_lin]
  rw [← sepConj_assoc, sepConj_comm (stackAt (sp - 240#64) 0x20), ← h1, h2, sepConj_assoc]

private theorem repack_uss_cells {m : Memory} (sp : BitVec 64) (v0 v1 v2 : BitVec 64) (R : SepProp)
    (hm : m ⊨ (((sp - 152#64) ↦₆₄ v0) ∗ ((sp - 144#64) ↦₆₄ v1) ∗ ((sp - 136#64) ↦₆₄ v2) ∗
      stackAt (sp - 152#64) 88 ∗ stackAt (sp - 80#64) 48) ∗ R) :
    m ⊨ stackAt (sp - 80#64) 160 ∗ R := by
  rw [hbStackAt_split (sp - 80#64) 48 112 (n := 160),
      show sp - 80#64 - 48#64 = sp - 128#64 by bv_lin,
      stackAt_split_cells (sp - 128#64) 88 3 (by decide)]
  hb_repack_cells

private theorem hbDropHandler_some_to_svc_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc ret_pc altBase auxvAddr : BitVec 64} {entries : List (BitVec 64 × BitVec 64)}
    {errno0 : BitVec 32}
    (hsvc : P.svc = Syscall.standard)
    (hc : CodeChunks P (hbDropHandlerChunks C S))
    (hsys : CodeChunks P (hbTeardownSysChunks C S))
    (hgetaux : hasInstrs P C.std.getauxvalAddr (getauxvalInstrs C.std))
    (_hal_page : MemWidth.isAligned .X64 C.std.pageSizeGlobalAddr = true)
    (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (hbnd_req : hbAltstackReqSz entries ≤ 524288)
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (halt_ne : altBase + 4096#64 ≠ 0#64)
    (huss_ne : s.sp - 152#64 ≠ 0#64)
    (huss_fit : (s.sp - 152#64).toNat + 24 ≤ 2 ^ 64)
    (hpc : s.pc = C.dropStackHandlerAddr) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = altBase + 4096#64)
    (hnext : ∀ (sf : State) (errno1 : BitVec 32) (sv29_mw sv19_mw sv20_mw : BitVec 64),
      sf.pc = S.munmapWrapperAddr + 0x24#64 → sf.status = .Running →
      sf.sp = (s.sp - 0xf0#64) - 0x20#64 → sf.spAligned = true →
      sf.readReg64 .x0 = altBase →
      sf.readReg64 .x1 = BitVec.ofNat 64 (hbAltstackReqSz entries + 4096) →
      sf.readReg64 .x8 = 215#64 →
      sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) →
      sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      Arm64.calleeSavedVRegs sf = Arm64.calleeSavedVRegs s →
      HbPostExitFields s sf →
      SepWP P target_pc sf
        ((((s.sp - 0xf0#64) - 32#64) ↦₆₄ sv29_mw) ∗ (((s.sp - 0xf0#64) - 24#64) ↦₆₄ (C.dropStackHandlerAddr + 0x68#64)) ∗
         (((s.sp - 0xf0#64) - 16#64) ↦₆₄ sv19_mw) ∗ (((s.sp - 0xf0#64) - 8#64) ↦₆₄ sv20_mw) ∗
         stackAt ((s.sp - 0xf0#64) - 0x20#64) 0x20 ∗
         stackAt (s.sp - 0x50#64) 0xa0 ∗
         ((s.sp - 80#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 72#64) ↦₆₄ ret_pc) ∗
         ((s.sp - 64#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((s.sp - 56#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
         ((s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((s.sp - 40#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
         ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((s.sp - 24#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
         ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
         ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
         (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
         (muslErrnoAddr sf ↦₃₂ errno1) ∗
         (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ F) post) :
    SepWP P target_pc s
      (stackAt s.sp 0x130 ∗
       ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
       (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
       (muslErrnoAddr s ↦₃₂ errno0) ∗
       (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ F) post := by
  have hx0' : s.readReg64 (.gpr 0#5) = altBase + 4096#64 := hx0
  have hlr' : s.readReg64 (.gpr 30#5) = ret_pc := hlr
  have halt_beq : (altBase + 4096#64 == 0#64) = false := beq_false_of_ne halt_ne
  have hsp_align_raw : (s.sp &&& 15#64 == 0#64) = true := hsp_align
  have hsp_sub_al : ((s.sp - 0xf0#64) &&& 15#64 == 0#64) = true := by
    simp only [beq_iff_eq] at hsp_align_raw ⊢; bv_bits
  hb_unpack_code hbDropHandlerChunks hc
  hb_unpack_code hbTeardownSysChunks hsys
  rw [hbStackAt_split s.sp 0xf0 0x40, stackAt_split_cells s.sp 0xa0 10 (by decide)]
  hb_unpack_cells 10; simp only [sepConj_assoc]
  rw [hbStackAt_split (s.sp - 80#64) 48 112,
      show s.sp - 80#64 - 48#64 = s.sp - 128#64 by bv_lin,
      stackAt_split_cells (s.sp - 128#64) 88 3 (by decide)]
  hb_unpack_cells 3; simp only [sepConj_assoc]
  rw [pointsTo64_split32_sub (s.sp - 128#64) 16#64 12#64]
  wp_steps; wp_steps; wp_steps
  rw [hbStackAt_split (s.sp - 240#64) 0x20 0x20]
  refine step_getauxval51 hgetaux (by with_reducible assumption)
    (ret_pc := C.dropStackHandlerAddr + 0x2c#64) (auxvAddr := auxvAddr) (entries := entries) (errno0 := errno0)
    (F := ?_) (fun R hm => by simp only [muslErrnoAddr, wp_norm, arm64_norm, bv_lin_norm] at hm ⊢; revert hm; sep_frame)
    (by wp_ro_simp) (by wp_ro_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_sub_al)
    (by wp_ro_simp) (by wp_ro_simp) hnonull
    fun s2 errno1 hpc2 hrun2 hsp2 hsp_al2 hx0_2 hcs2 hex2 hsas2 => ?_
  have hsp2_eq : s2.sp = s.sp - 240#64 := by simpa [wp_norm, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 (.gpr 19#5) = altBase + 4096#64 := by
    have := hcs2.readReg64_x19; simpa [wp_norm, arm64_norm, hx0] using this
  have hx29_2 : s2.readReg64 (.gpr 29#5) = s.sp - 80#64 := by
    have := hcs2.readReg64_fp; simpa [wp_norm, arm64_norm] using this
  have hx0_2' : s2.readReg64 (.gpr 0#5) = hbAuxvLookup entries 51#64 := hx0_2
  wp_conv_pre =>
    simp only [wp_norm, arm64_norm, BitVec.ofNat_eq_ofNat, sepConj_assoc]
    rw [stackAt_20_20_to_10_30 s.sp]
  wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps
  let x21_val := if BitVec.ult 0x3000#64 (hbAuxvLookup entries 51#64) then hbAuxvLookup entries 51#64 else 0x3000#64
  have htp2 : s2.tpidrEl0 = s.tpidrEl0 := by simpa [wp_norm, arm64_norm] using hex2.2.2.1
  refine step_sigaltstack_disable hsvc
    (by with_reducible assumption) (by with_reducible assumption)
    (by with_reducible assumption) (by with_reducible assumption)
    (by with_reducible assumption) (by with_reducible assumption)
    (by with_reducible assumption)
    (ret_pc := C.dropStackHandlerAddr + 0x5c#64) (uss := s.sp - 152#64)
    (ssSize := x21_val) (pad := _) (errno0 := errno1) (F := ?_)
    (fun R hm => by simp only [muslErrnoAddr, wp_norm, arm64_norm, bv_lin_norm, hsp2_eq, htp2] at hm ⊢; revert hm; sep_frame)
    (by wp_ro_simp) (by wp_ro_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp2_eq] using hsp_sub_al)
    (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) huss_ne huss_fit
    fun s4 errno2 hpc4 hrun4 hsp4 hsp_al4 hcs4 hex4 => ?_
  have hsp4_eq : s4.sp = s.sp - 240#64 := by simpa [wp_norm, arm64_norm, hsp2_eq] using hsp4
  have hx19_4 : s4.readReg64 (.gpr 19#5) = altBase + 4096#64 := by
    have := hcs4.readReg64_x19; simpa [wp_norm, arm64_norm, hx19_2] using this
  have hx20_4 : s4.readReg64 (.gpr 20#5) = 4096#64 := by
    have := hcs4.readReg64_x20; simpa [wp_norm, arm64_norm] using this
  have hx21_4 : s4.readReg64 (.gpr 21#5) = x21_val := by
    have := hcs4.readReg64_x21; simpa [wp_norm, arm64_norm, x21_val] using this
  refine SepWP.weaken_pre_frame
    (P' := stackAt s4.sp 0x40 ∗
      (stackAt (s.sp - 0x50#64) 0xa0 ∗
       ((s.sp - 80#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 72#64) ↦₆₄ ret_pc) ∗
       ((s.sp - 64#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((s.sp - 56#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
       ((s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((s.sp - 40#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
       ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((s.sp - 24#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
       ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
       ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
       (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
       (muslErrnoAddr s4 ↦₃₂ errno2) ∗
       (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ F))
    (fun R hm => by
      rw [hsp4_eq]
      simp only [wp_norm, arm64_norm, bv_lin_norm, hsp2_eq] at hm ⊢
      simp only [BitVec.ofNat_eq_ofNat] at hm ⊢
      rw [pointsTo32_combine64_sub s.sp 144#64 140#64] at hm
      rw [hbStackAt_split (s.sp - 240#64) 0x30 0x10,
          show s.sp - 240#64 - 48#64 = s.sp - 288#64 by bv_lin]
      replace hm := repack_uss_cells s.sp _ _ _ _ (Satisfies.mono (by sep_frame) hm)
      revert hm; sep_frame) ?_
  wp_steps; wp_steps
  refine step_munmapPre_to_svc_wp (uBase := altBase) (reqSz := hbAltstackReqSz entries)
    (ret_pc := C.dropStackHandlerAddr + 0x68#64)
    (by with_reducible assumption) (by with_reducible assumption)
    (by with_reducible assumption) (by with_reducible assumption)
    (by wp_ro_simp) (by wp_ro_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp4_eq] using hsp_sub_al)
    (by wp_ro_simp)
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, x21_val, csel_altstack_add_4096 entries hbnd_req])
    fun sf hpc_f hrun_f hsp_f hsp_al_f hx0_f hx1_f hx8_f hx27_f hx28_f hv_f hex_f => ?_
  have htp_f : muslErrnoAddr s4 = muslErrnoAddr sf := by
    dsimp [muslErrnoAddr]; rw [hex_f.2.2.1]; simp [wp_norm, arm64_norm]
  refine SepWP.weaken_pre_frame
    (P' := (((s.sp - 0xf0#64) - 32#64) ↦₆₄ _) ∗ (((s.sp - 0xf0#64) - 24#64) ↦₆₄ (C.dropStackHandlerAddr + 0x68#64)) ∗
      (((s.sp - 0xf0#64) - 16#64) ↦₆₄ _) ∗ (((s.sp - 0xf0#64) - 8#64) ↦₆₄ _) ∗
      stackAt ((s.sp - 0xf0#64) - 0x20#64) 0x20 ∗
      stackAt (s.sp - 0x50#64) 0xa0 ∗
      ((s.sp - 80#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 72#64) ↦₆₄ ret_pc) ∗
      ((s.sp - 64#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((s.sp - 56#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
      ((s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((s.sp - 40#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
      ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((s.sp - 24#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
      ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
      ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
      (muslErrnoAddr sf ↦₃₂ errno2) ∗
      (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ F)
    (fun R hm => by
      simp only [wp_norm, arm64_norm, hsp4_eq, htp_f] at hm ⊢
      revert hm; sep_frame) ?_
  have hx27_all : sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
    have h4 := hcs4.readReg64_x27; have h2 := hcs2.readReg64_x27
    simp only [wp_norm, arm64_norm] at hx27_f h4 h2; exact hx27_f.trans (h4.trans h2)
  have hx28_all : sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by
    have h4 := hcs4.readReg64_x28; have h2 := hcs2.readReg64_x28
    simp only [wp_norm, arm64_norm] at hx28_f h4 h2; exact hx28_f.trans (h4.trans h2)
  have hv_all : Arm64.calleeSavedVRegs sf = Arm64.calleeSavedVRegs s := by
    have h4 := hcs4.2.2.2.2.2.2.2.2.2.2.2; have h2 := hcs2.2.2.2.2.2.2.2.2.2.2.2
    simp only [wp_norm, arm64_norm] at hv_f h4 h2; exact hv_f.trans (h4.trans h2)
  exact hnext sf errno2 _ _ _ hpc_f hrun_f (by simpa [wp_norm, arm64_norm, hsp4_eq] using hsp_f)
    hsp_al_f hx0_f hx1_f hx8_f hx27_all hx28_all hv_all
    (HbPostExitFields.trans hb_exit_rfl
      (HbPostExitFields.trans hex2
        (HbPostExitFields.trans hb_exit_rfl
          (HbPostExitFields.trans hex4
            (HbPostExitFields.trans hb_exit_rfl hex_f)))))

private theorem hbDropHandler_some_from_after_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {haveLse : BitVec 8} {target_pc ret_pc sp0 sv29_mw sv19_mw sv20_mw sv29 sv26 sv25 sv24 sv23 sv22 sv21 sv20 sv19 : BitVec 64}
    (hc : CodeChunks P (hbDropHandlerChunks C S))
    (hsys : CodeChunks P (hbTeardownSysChunks C S))
    (hcas4 : hasInstrs P C.std.cas4AcqAddr (cas4AcqInstrs C.std))
    (hcas8 : hasInstrs P C.std.cas8AcqAddr (cas8AcqInstrs C.std))
    (hswp4 : hasInstrs P C.std.swp4RelAddr (swp4RelInstrs C.std))
    (hal_lock : MemWidth.isAligned .W32 S.threadInfoLockAddr = true)
    (hal_lock8 : MemWidth.isAligned .X64 (S.threadInfoLockAddr + 8#64) = true)
    (hal_root : MemWidth.isAligned .X64 S.threadInfoRootAddr = true)
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hro : RoPostFacts C haveLse s.mem)
    (hd_lock4 : RoDisj C S.threadInfoLockAddr 4)
    (hd_lock8 : RoDisj C (S.threadInfoLockAddr + 8#64) 8)
    (hd_stk : RoDisj C (sp0 - 0xf0#64) 0xf0)
    (hd_mw : RoDisj C (sp0 - 0xf0#64 - 0x40#64) 32)
    (hpc : s.pc = S.munmapWrapperAddr + 0x28#64) (hrun : s.status = .Running)
    (hsp : s.sp = (sp0 - 0xf0#64) - 0x20#64) (hsp_align : (sp0 &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → sf.spAligned = true →
      CalleeSavedPreserved
        ((((((((((s.writeReg64 (.gpr 19#5) sv19).writeReg64 (.gpr 20#5) sv20).writeReg64 (.gpr 21#5) sv21).writeReg64 (.gpr 22#5) sv22).writeReg64 (.gpr 23#5) sv23).writeReg64 (.gpr 24#5) sv24).writeReg64 (.gpr 25#5) sv25).writeReg64 (.gpr 26#5) sv26).writeReg64 (.gpr 29#5) sv29)) sf →
      HbPostExitFields s sf → RoPostFacts C haveLse sf.mem →
      SepWP P target_pc sf
        (stackAt sp0 0x130 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
         (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
         ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗ F) post) :
    SepWP P target_pc s
      ((((sp0 - 0xf0#64) - 32#64) ↦₆₄ sv29_mw) ∗ (((sp0 - 0xf0#64) - 24#64) ↦₆₄ (C.dropStackHandlerAddr + 0x68#64)) ∗
       (((sp0 - 0xf0#64) - 16#64) ↦₆₄ sv19_mw) ∗ (((sp0 - 0xf0#64) - 8#64) ↦₆₄ sv20_mw) ∗
       stackAt ((sp0 - 0xf0#64) - 0x20#64) 0x20 ∗
       (stackAt (sp0 - 0x50#64) 0xa0 ∗
        ((sp0 - 80#64) ↦₆₄ sv29) ∗ ((sp0 - 72#64) ↦₆₄ ret_pc) ∗
        ((sp0 - 64#64) ↦₆₄ sv26) ∗ ((sp0 - 56#64) ↦₆₄ sv25) ∗
        ((sp0 - 48#64) ↦₆₄ sv24) ∗ ((sp0 - 40#64) ↦₆₄ sv23) ∗
        ((sp0 - 32#64) ↦₆₄ sv22) ∗ ((sp0 - 24#64) ↦₆₄ sv21) ∗
        ((sp0 - 16#64) ↦₆₄ sv20) ∗ ((sp0 - 8#64) ↦₆₄ sv19) ∗
        (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
        (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
        ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗ F)) post := by
  have hsp_sub_al : ((sp0 - 0xf0#64) &&& 15#64 == 0#64) = true := by
    simp only [beq_iff_eq] at hsp_align ⊢; bv_bits
  hb_unpack_code hbTeardownSysChunks hsys
  refine step_munmapPost_from_after_wp (sp0 := sp0 - 0xf0#64) (ret_pc := C.dropStackHandlerAddr + 0x68#64)
    (by with_reducible assumption) (by with_reducible assumption) (by with_reducible assumption)
    hro hd_mw hpc hrun hsp hsp_sub_al hx0
    fun s1 hpc1 hrun1 hsp1 _ _ _ _ hcs1 hex1 hro1 => ?_
  refine SepWP.weaken_pre_frame
    (P' := stackAt (sp0 - 0x50#64) 0xa0 ∗
      ((sp0 - 80#64) ↦₆₄ sv29) ∗ ((sp0 - 72#64) ↦₆₄ ret_pc) ∗
      ((sp0 - 64#64) ↦₆₄ sv26) ∗ ((sp0 - 56#64) ↦₆₄ sv25) ∗
      ((sp0 - 48#64) ↦₆₄ sv24) ∗ ((sp0 - 40#64) ↦₆₄ sv23) ∗
      ((sp0 - 32#64) ↦₆₄ sv22) ∗ ((sp0 - 24#64) ↦₆₄ sv21) ∗
      ((sp0 - 16#64) ↦₆₄ sv20) ∗ ((sp0 - 8#64) ↦₆₄ sv19) ∗
      (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
      (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
      ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗ (stackAt (sp0 - 0xf0#64) 0x40 ∗ F))
    (fun R hm => by revert hm; sep_frame) ?_
  refine step_dropHandler_from_68_wp (sp0 := sp0) hc (by with_reducible assumption) hcas4 hcas8 hswp4
    hal_lock hal_lock8 hal_root hro1 hd_lock4 hd_lock8 hd_stk hpc1 hrun1 hsp1 hsp_align
    fun sf hpc_f hrun_f hsp_f hsp_al_f hcs_f hex_f hro_f => ?_
  refine SepWP.weaken_pre_frame
    (P' := stackAt sp0 0x130 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
      (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
      ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗ F)
    (fun R hm => by rw [hbStackAt_split sp0 0xf0 0x40]; revert hm; sep_frame) ?_
  refine hnext sf hpc_f hrun_f hsp_f hsp_al_f ?_ (HbPostExitFields.trans hex1 hex_f) hro_f
  hb_unpack_cs hcs1; hb_unpack_cs hcs_f; hb_close_cs

private theorem inRegion_add_iff {base a : BitVec 64} {n1 n2 : Nat}
    (hbnd : base.toNat + n1 + n2 ≤ 2 ^ 64) :
    ((a - base).toNat < n1 + n2) ↔
      ((a - base).toNat < n1 ∨ (a - (base + BitVec.ofNat 64 n1)).toNat < n2) := by
  have hsub1 := BitVec.toNat_sub a base
  have hadd : (base + BitVec.ofNat 64 n1).toNat = (base.toNat + n1) % 2 ^ 64 := by
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hsub2 := BitVec.toNat_sub a (base + BitVec.ofNat 64 n1)
  have := a.isLt; have := base.isLt
  omega

private theorem unmapNonFrozen_add (m : Memory) (base : BitVec 64) (n1 n2 : Nat)
    (hbnd : base.toNat + n1 + n2 ≤ 2 ^ 64) :
    m.unmapNonFrozen base (n1 + n2) =
      (m.unmapNonFrozen base n1).unmapNonFrozen (base + BitVec.ofNat 64 n1) n2 := by
  have hmk : ∀ m' : Memory, m' = ⟨m'.cells⟩ := fun ⟨_⟩ => rfl
  rw [hmk (m.unmapNonFrozen base (n1 + n2)),
      hmk ((m.unmapNonFrozen base n1).unmapNonFrozen (base + BitVec.ofNat 64 n1) n2)]
  congr 1; funext a
  have hiff := inRegion_add_iff (a := a) hbnd
  have hperm := Memory.perm_unmapNonFrozen m base n1 a
  dsimp only [Memory.unmapNonFrozen] at hperm ⊢
  rw [hperm]
  by_cases h1 : (a - base).toNat < n1
  · have h12 : (a - base).toNat < n1 + n2 := hiff.mpr (Or.inl h1)
    cases hf : (m.perm a).frozen <;>
      simp only [decide_eq_true h1, decide_eq_true h12, hf, Bool.not_true, Bool.not_false,
        Bool.true_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Option.frozen, ite_self]
  · by_cases h2 : (a - (base + BitVec.ofNat 64 n1)).toNat < n2
    · have h12 : (a - base).toNat < n1 + n2 := hiff.mpr (Or.inr h2)
      cases hf : (m.perm a).frozen <;>
        simp only [decide_eq_false h1, decide_eq_true h2, decide_eq_true h12, hf,
          Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and, Bool.and_false,
          Bool.false_eq_true, ↓reduceIte]
    · have h12 : ¬ (a - base).toNat < n1 + n2 := fun h => (hiff.mp h).elim h1 h2
      simp only [decide_eq_false h1, decide_eq_false h2, decide_eq_false h12,
        Bool.false_and, Bool.false_eq_true, ↓reduceIte]

private theorem satisfies_unmapNonFrozen_altstack {P : SepProp} {m : Memory}
    {altBase : BitVec 64} {altRawSz : Nat}
    (hbnd : altBase.toNat + 4096 + altRawSz ≤ 2 ^ 64)
    (h : m ⊨ memRegionProtNone altBase 4096 ∗ memRegion (altBase + 4096#64) altRawSz ∗
      memMapped altBase (4096 + altRawSz) ∗ P) :
    m.unmapNonFrozen altBase (4096 + altRawSz) ⊨ P := by
  rw [unmapNonFrozen_add m altBase 4096 altRawSz hbnd]
  have hsplit_eq : memMapped altBase (4096 + altRawSz) =
      memMapped altBase 4096 ∗ memMapped (altBase + 4096#64) altRawSz :=
    memMapped_split altBase 4096 altRawSz (by omega)
  rw [hsplit_eq] at h
  have hsplit : m ⊨ memRegionProtNone altBase 4096 ∗ memMapped altBase 4096 ∗
      (memRegion (altBase + 4096#64) altRawSz ∗ memMapped (altBase + 4096#64) altRawSz ∗ P) := by
    revert h; sep_frame
  exact Satisfies.unmapNonFrozen (Satisfies.unmapNonFrozen_protNone hsplit)

/-- Ownership of the optional signal altstack allocation (guard page + RW stack pages). -/
def HbAltstackOwn (entries : List (BitVec 64 × BitVec 64)) (altOpt : Option (BitVec 64 × Nat)) : SepProp :=
  match altOpt with
  | none => emp
  | some (altBase, altRawSz) =>
      ⌜4096 ≤ altBase.toNat ∧ altBase.toNat % 4096 = 0 ∧
        altRawSz = Arm64.pageAlignUp (hbAltstackReqSz entries) ∧
        altBase.toNat + 4096 + altRawSz ≤ 2 ^ 48⌝ ∗
      memRegionProtNone altBase 4096 ∗ memRegion (altBase + 4096#64) altRawSz

/-- Mapping reservation token for the optional signal altstack allocation. -/
def HbAltstackMapped (altOpt : Option (BitVec 64 × Nat)) : SepProp :=
  match altOpt with
  | none => emp
  | some (altBase, altRawSz) => memMapped altBase (4096 + altRawSz)

/-- Pointer stored at `S.threadInfoRootAddr + 0x10` for the optional signal altstack. -/
def hbAltstackPtr (altOpt : Option (BitVec 64 × Nat)) : BitVec 64 :=
  match altOpt with
  | none => 0#64
  | some (altBase, _) => altBase + 4096#64

private theorem pageAlignUp_add_4096 (n : Nat) :
    Arm64.pageAlignUp (n + 4096) = 4096 + Arm64.pageAlignUp n := by
  unfold Arm64.pageAlignUp Arm64.PAGE_SIZE
  omega

private theorem step_svc_munmap_altstack_wp {P : Program} {S : HbStartupLayout}
    {target_pc altBase : BitVec 64} {reqSz altRawSz : Nat}
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard)
    (hmw_w1 : P.hasCode (S.munmapWrapperAddr + 0x18#64) [0xaa1403e0#32, 0xaa1303e1#32, 0xd2801ae8#32, 0xd4000001#32])
    (hpc : s.pc = S.munmapWrapperAddr + 0x24#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = altBase)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (reqSz + 4096))
    (hx8 : s.readReg64 .x8 = 215#64)
    (hal : altBase.toNat % 4096 = 0)
    (hreq : reqSz ≤ 524288)
    (hraw : altRawSz = Arm64.pageAlignUp reqSz)
    (hfit : altBase.toNat + 4096 + altRawSz ≤ 2 ^ 48)
    (hnext : ∀ sf : State, sf.pc = S.munmapWrapperAddr + 0x28#64 → sf.status = .Running →
      sf.sp = s.sp → sf.readReg64 .x0 = 0#64 → CalleeSavedPreserved s sf →
      HbPostExitFields s sf →
      SepWP P target_pc sf F post) :
    SepWP P target_pc s
      (memRegionProtNone altBase 4096 ∗ memRegion (altBase + 4096#64) altRawSz ∗
       memMapped altBase (4096 + altRawSz) ∗ F) post := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hf_svc : P.fetch (S.munmapWrapperAddr + 0x24#64) = some (.system false 0#16) :=
    Program.fetch_of_hasCode_decodeAt 3 hmw_w1 (by bv_lin) (by decide)
  apply reaches_pc_step hrun (hpc ▸ hf_svc)
  have heval : P.evalInst (.system false 0#16) s = execMunmap s := by
    rw [_root_.Arm64.Program.evalInst_svc0, hsvc, evalSvc_standard]
    simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable,
      Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable,
      wp_norm, arm64_norm, hx8]
  rw [heval]
  have hal0 : (s.readReg64 .x0).toNat % PAGE_SIZE = 0 := by
    rw [hx0]; unfold PAGE_SIZE; exact hal
  have hx1_nat : (s.readReg64 .x1).toNat = reqSz + 4096 := by
    rw [hx1, BitVec.toNat_ofNat]; omega
  have hlen : s.readReg64 .x1 ≠ 0#64 := by
    intro h0; rw [h0] at hx1_nat; simp at hx1_nat
  have hpage : Arm64.pageAlignUp (s.readReg64 .x1).toNat = 4096 + altRawSz := by
    rw [hx1_nat, pageAlignUp_add_4096, ← hraw]
  have hfit0 : (s.readReg64 .x0).toNat + Arm64.pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 48 := by
    rw [hx0, hpage]; omega
  have hm_alt : s.mem ⊨ memRegionProtNone altBase 4096 ∗ memRegion (altBase + 4096#64) altRawSz ∗
      memMapped altBase (4096 + altRawSz) ∗ (F ∗ R) := by
    revert hm; sep_frame
  have hfrz : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 .x0)
      (Arm64.pageAlignUp (s.readReg64 .x1).toNat) = true := by
    rw [hx0, hpage]; exact allPerm_not_frozen_of_altstack (by omega) hm_alt
  rw [execMunmap_ok s hal0 hlen hfit0 hfrz, hx0, hpage]
  have hpc_next : S.munmapWrapperAddr + 0x24#64 + 4#64 = S.munmapWrapperAddr + 0x28#64 := by bv_lin
  refine SepWP.to_reaches_pc (hnext _ ?_ hrun rfl ?_ ?_ ⟨rfl, rfl, rfl, rfl⟩)
    (satisfies_unmapNonFrozen_altstack (by omega) hm_alt)
  · simp [State.advancePC, hpc, hpc_next]
  · simp [wp_norm, arm64_norm]
  · simp [Arm64.CalleeSavedPreserved, Arm64.calleeSavedVRegs, State.advancePC,
      State.writeReg64, State.setPhysMemAvail, State.setMem, wp_norm, arm64_norm]

theorem sepWP_with_roSafe {P : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc : BitVec 64} {s : State} {Pre Keep : SepProp} {post : State → SepProp → Prop}
    (hf : Pre ⊢ ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64)) ∗ Keep := by sep_frame)
    (h : RoSafe C Keep → SepWP P target_pc s Pre post) :
    SepWP P target_pc s Pre post := by
  apply SepWP.of_reaches_pc; intro R hm
  have hm' : s.mem ⊨ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ Keep ∗ R := by
    rw [← sepConj_assoc, ← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hf) hm
  exact SepWP.to_reaches_pc (h (roSafe_of_pre hm')) hm

private theorem muslErrnoAddr_of_exitFields {s sf : State} (h : HbPostExitFields s sf) :
    muslErrnoAddr sf = muslErrnoAddr s := by
  simp [muslErrnoAddr, h.2.2.1]

private theorem altBase_add_4096_ne_zero {altBase : BitVec 64} {altRawSz : Nat}
    (hfit : altBase.toNat + 4096 + altRawSz ≤ 2 ^ 48) :
    altBase + 4096#64 ≠ 0#64 := by
  intro h
  have h0 : (altBase + 4096#64).toNat = 0 := by rw [h]; rfl
  have h4096 : (4096#64 : BitVec 64).toNat = 4096 := rfl
  rw [BitVec.toNat_add, h4096, Nat.mod_eq_of_lt (by omega)] at h0
  omega

/-- `SepWP` for `std::sys::pal::unix::stack_overflow::imp::drop_handler` (`C.dropStackHandlerAddr`)
    over both `altOpt = none` and `altOpt = some (altBase, altRawSz)`. -/
theorem hbDropHandler_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {haveLse : BitVec 8} {target_pc ret_pc auxvAddr : BitVec 64}
    {entries : List (BitVec 64 × BitVec 64)} {altOpt : Option (BitVec 64 × Nat)}
    {errno0 : BitVec 32}
    (hsvc : P.svc = Syscall.standard)
    (hc : CodeChunks P (hbDropHandlerChunks C S))
    (hsys : CodeChunks P (hbTeardownSysChunks C S))
    (hgetaux : hasInstrs P C.std.getauxvalAddr (getauxvalInstrs C.std))
    (hcas4 : hasInstrs P C.std.cas4AcqAddr (cas4AcqInstrs C.std))
    (hcas8 : hasInstrs P C.std.cas8AcqAddr (cas8AcqInstrs C.std))
    (hswp4 : hasInstrs P C.std.swp4RelAddr (swp4RelInstrs C.std))
    (hal_page : MemWidth.isAligned .X64 C.std.pageSizeGlobalAddr = true)
    (hal_lock : MemWidth.isAligned .W32 S.threadInfoLockAddr = true)
    (hal_lock8 : MemWidth.isAligned .X64 (S.threadInfoLockAddr + 8#64) = true)
    (hal_root : MemWidth.isAligned .X64 S.threadInfoRootAddr = true)
    (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (hbnd_req : hbAltstackReqSz entries ≤ 524288)
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (huss_ne : s.sp - 152#64 ≠ 0#64)
    (huss_fit : (s.sp - 152#64).toNat + 24 ≤ 2 ^ 64)
    (hpc : s.pc = C.dropStackHandlerAddr) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = hbAltstackPtr altOpt)
    (hnext : ∀ (sf : State) (errno1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf →
      HbPostExitFields s sf → RoPostFacts C haveLse sf.mem →
      SepWP P target_pc sf
        (stackAt s.sp 0x130 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
         (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
         ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
         ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
         (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
         (muslErrnoAddr sf ↦₃₂ errno1) ∗
         (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
         ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ F)) post) :
    SepWP P target_pc s
      (stackAt s.sp 0x130 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
       (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
       ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
       ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
       (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
       (muslErrnoAddr s ↦₃₂ errno0) ∗
       (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
       HbAltstackOwn entries altOpt ∗ HbAltstackMapped altOpt ∗
       ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ F)) post := by
  refine sepWP_with_roSafe (C := C) (haveLse := haveLse) (h := fun hSafe => ?_)
  have hd_lock4 : RoDisj C S.threadInfoLockAddr 4 := roSafe_disj32 S.threadInfoLockAddr hSafe
  have hd_lock8 : RoDisj C (S.threadInfoLockAddr + 8#64) 8 := roSafe_disj64 (S.threadInfoLockAddr + 8#64) hSafe
  have hd_stk130 : RoDisj C (s.sp - 0x130#64) 0x130 := roSafe_disj_stack s.sp 0x130 hSafe
  have hd_stk : RoDisj C (s.sp - 0xf0#64) 0xf0 := roDisj_sub hd_stk130 0x40 0xf0
  have hd_mw : RoDisj C (s.sp - 0xf0#64 - 0x40#64) 32 := roDisj_sub hd_stk130 0 32
  rcases altOpt with _ | ⟨altBase, altRawSz⟩
  · dsimp only [HbAltstackOwn, HbAltstackMapped, hbAltstackPtr] at hx0 ⊢
    refine SepWP.weaken_pre_frame
      (P' := stackAt s.sp 0xf0 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
        (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
        ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
        ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
         (stackAt (s.sp - 0xf0#64) 0x40 ∗
          ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
          (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
          (muslErrnoAddr s ↦₃₂ errno0) ∗
          (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ F)))
      (fun R hm => by rw [hbStackAt_split s.sp 0xf0 0x40] at hm; revert hm; sep_frame) ?_
    refine hbDropHandler_none_wp hc hsys.1 hcas4 hcas8 hswp4 hal_lock hal_lock8 hal_root
      hd_lock4 hd_lock8 hd_stk hpc hrun hsp_align hlr hx0
      fun sf hpc_f hrun_f hsp_f hsp_al_f hcs_f hex_f hro_f => ?_
    have herr_eq := muslErrnoAddr_of_exitFields hex_f
    refine SepWP.weaken_pre_frame
      (P' := stackAt s.sp 0x130 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
        (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
        ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
        ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
        (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
        (muslErrnoAddr sf ↦₃₂ errno0) ∗
        (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
        ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ F))
      (fun R hm => by rw [herr_eq, hbStackAt_split s.sp 0xf0 0x40]; revert hm; sep_frame) ?_
    exact hnext sf errno0 hpc_f hrun_f hsp_f hsp_al_f hcs_f hex_f hro_f
  · dsimp only [HbAltstackOwn, HbAltstackMapped, hbAltstackPtr] at hx0 ⊢
    refine SepWP.weaken_pre_frame
      (P' := ⌜4096 ≤ altBase.toNat ∧ altBase.toNat % 4096 = 0 ∧
          altRawSz = Arm64.pageAlignUp (hbAltstackReqSz entries) ∧
          altBase.toNat + 4096 + altRawSz ≤ 2 ^ 48⌝ ∗
        (stackAt s.sp 0x130 ∗
         ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
         (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
         (muslErrnoAddr s ↦₃₂ errno0) ∗
         (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
         (memRegionProtNone altBase 4096 ∗ memRegion (altBase + 4096#64) altRawSz ∗
          memMapped altBase (4096 + altRawSz) ∗
          (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
          (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
          ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
          ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ F))))
      (fun R hm => by ac_nf at hm ⊢) ?_
    refine SepWP.pure_elim fun ⟨_, hal_base, hraw_eq, hfit_base⟩ => ?_
    have halt_ne : altBase + 4096#64 ≠ 0#64 := altBase_add_4096_ne_zero hfit_base
    refine hbDropHandler_some_to_svc_wp hsvc hc hsys hgetaux hal_page hnonull hbnd_req
      halt_ne huss_ne huss_fit hpc hrun hsp_align hlr hx0
      fun s1 errno1 sv29_mw sv19_mw sv20_mw hpc1 hrun1 hsp1 _ hx0_1 hx1_1 hx8_1 hx27_1 hx28_1 hv_1 hex1 => ?_
    have hmw_w1 : P.hasCode (S.munmapWrapperAddr + 0x18#64)
        [0xaa1403e0#32, 0xaa1303e1#32, 0xd2801ae8#32, 0xd4000001#32] := by
      hb_unpack_code hbTeardownSysChunks hsys; with_reducible assumption
    refine SepWP.weaken_pre_frame
      (P' := memRegionProtNone altBase 4096 ∗ memRegion (altBase + 4096#64) altRawSz ∗
        memMapped altBase (4096 + altRawSz) ∗
        ((((s.sp - 0xf0#64) - 32#64) ↦₆₄ sv29_mw) ∗ (((s.sp - 0xf0#64) - 24#64) ↦₆₄ (C.dropStackHandlerAddr + 0x68#64)) ∗
         (((s.sp - 0xf0#64) - 16#64) ↦₆₄ sv19_mw) ∗ (((s.sp - 0xf0#64) - 8#64) ↦₆₄ sv20_mw) ∗
         stackAt ((s.sp - 0xf0#64) - 0x20#64) 0x20 ∗
         (stackAt (s.sp - 0x50#64) 0xa0 ∗
          ((s.sp - 80#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 72#64) ↦₆₄ ret_pc) ∗
          ((s.sp - 64#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((s.sp - 56#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
          ((s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((s.sp - 40#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
          ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((s.sp - 24#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
          ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
          (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
          (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
          ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
          (((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
           (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
           (muslErrnoAddr s1 ↦₃₂ errno1) ∗
           (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
           ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ F)))))
      (fun R hm => by revert hm; sep_frame) ?_
    refine step_svc_munmap_altstack_wp hsvc hmw_w1 hpc1 hrun1 hx0_1 hx1_1 hx8_1
      hal_base hbnd_req hraw_eq hfit_base
      fun s2 hpc2 hrun2 hsp2 hx0_2 hcs2 hex2 => ?_
    refine sepWP_with_roPostFacts (C := C) (haveLse := haveLse) (h := fun hro2 => ?_)
    have hsp2_eq : s2.sp = (s.sp - 0xf0#64) - 0x20#64 := hsp2.trans hsp1
    refine hbDropHandler_some_from_after_wp hc hsys hcas4 hcas8 hswp4 hal_lock hal_lock8 hal_root
      hro2 hd_lock4 hd_lock8 hd_stk hd_mw hpc2 hrun2 hsp2_eq hsp_align hx0_2
      fun sf hpc_f hrun_f hsp_f hsp_al_f hcs_f hex_f hro_f => ?_
    have herr_eq : muslErrnoAddr s1 = muslErrnoAddr sf := by
      rw [muslErrnoAddr_of_exitFields hex_f, muslErrnoAddr_of_exitFields hex2]
    refine SepWP.weaken_pre_frame
      (P' := stackAt s.sp 0x130 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
        (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
        ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
        ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
        (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
        (muslErrnoAddr sf ↦₃₂ errno1) ∗
        (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
        ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ F))
      (fun R hm => by rw [herr_eq] at hm; revert hm; sep_frame) ?_
    have hcs_all : CalleeSavedPreserved s sf := by
      rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs_f with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, gv⟩
      simp only [wp_norm, arm64_norm] at g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 gv
      rw [hcs2.readReg64_x27, hx27_1] at g27
      rw [hcs2.readReg64_x28, hx28_1] at g28
      rw [hcs2.2.2.2.2.2.2.2.2.2.2.2, hv_1] at gv
      rw [CalleeSavedPreserved.iff_regs]
      exact ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, gv⟩
    exact hnext sf errno1 hpc_f hrun_f hsp_f hsp_al_f hcs_all
      (HbPostExitFields.trans hex1 (HbPostExitFields.trans hex2 hex_f)) hro_f

theorem hbAltstackInv_entails_own {C : HbCliLayout} {S : HbStartupLayout}
    {entries : List (BitVec 64 × BitVec 64)} {altOpt : Option (BitVec 64 × Nat)}
    (hraw : ∀ altBase altRawSz, altOpt = some (altBase, altRawSz) →
      altRawSz = Arm64.pageAlignUp (hbAltstackReqSz entries)) :
    HbAltstackInv4k C S altOpt ⊢
      (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
      ((S.threadInfoRootAddr + 8#64) ↦₆₄ 0#64) ∗
      ((S.threadInfoRootAddr + 16#64) ↦₆₄ 0#64) ∗
      (S.threadInfoLockAddr ↦₃₂ 0#32) ∗
      ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
      ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
      (C.mainAltstackAddr ↦₆₄ hbAltstackPtr altOpt) ∗
      HbAltstackOwn entries altOpt := by
  unfold HbAltstackInv4k HbAltstackOwn hbAltstackPtr
  cases altOpt with
  | none =>
    dsimp only
    sep_entail
  | some p =>
    rcases p with ⟨altBase, altRawSz⟩
    have hr := hraw altBase altRawSz rfl
    dsimp only
    apply sepConj_mono_right; apply sepConj_mono_right; apply sepConj_mono_right
    apply sepConj_mono_right; apply sepConj_mono_right; apply sepConj_mono_right
    rw [← emp_sepConj (⌜_⌝ ∗ _), sepConj_comm ⌜_⌝ _]
    refine entails_pure_in_frame fun h => ?_
    have hpure : 4096 ≤ altBase.toNat ∧ altBase.toNat % 4096 = 0 ∧
        altRawSz = Arm64.pageAlignUp (hbAltstackReqSz entries) ∧
        altBase.toNat + 4096 + altRawSz ≤ 2 ^ 48 :=
      ⟨h.1, h.2.1, hr, by omega⟩
    rw [emp_sepConj]
    refine Entails.trans (by sep_entail)
      (sepConj_mono_right (Entails.pure_right hpure (Entails.refl _)))

private theorem hbFold_dead_closure_post (C : HbCliLayout) (dataPtr flagPtr : BitVec 64) (G : SepProp)
    {P_pre R_rest : SepProp}
    (hf : P_pre ⊢ ((dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗
      ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ G) ∗ R_rest := by sep_frame) :
    P_pre ⊢ (((dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗
      (((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ ∃∗ R_dead : SepProp, R_dead)) ∗ G) := by
  refine Entails.trans hf ?_
  have hex : R_rest ⊢ ∃∗ R_dead : SepProp, R_dead :=
    Entails.sepExists_right (Q := id) R_rest (Entails.refl R_rest)
  exact Entails.trans (sepConj_mono_right hex) (by sep_entail)

private theorem hbCleanupClosure_epilogue_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {haveLse : BitVec 8} {target_pc ret_pc dataPtr flagPtr auxvAddr : BitVec 64}
    {entries : List (BitVec 64 × BitVec 64)} {altOpt : Option (BitVec 64 × Nat)}
    {errno0 : BitVec 32} {sc s : State} {Dead G : SepProp} {post : State → SepProp → Prop}
    (hc : HbPostMainCode P C S) (hs : S.Valid C)
    (hraw : ∀ altBase altRawSz, altOpt = some (altBase, altRawSz) →
      altRawSz = Arm64.pageAlignUp (hbAltstackReqSz entries))
    (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (hbnd_req : hbAltstackReqSz entries ≤ 524288)
    (hsp_lo : 4240 ≤ sc.sp.toNat) (hsp_align : sc.spAligned = true)
    (hpc : s.pc = C.std.cleanupClosureAddr + 0x184#64) (hrun : s.status = .Running)
    (hsp : s.sp = sc.sp - 0x60#64)
    (hcs_hi : s.readReg64 (.gpr 24#5) = sc.readReg64 (.gpr 24#5) ∧
      s.readReg64 (.gpr 25#5) = sc.readReg64 (.gpr 25#5) ∧
      s.readReg64 (.gpr 26#5) = sc.readReg64 (.gpr 26#5) ∧
      s.readReg64 (.gpr 27#5) = sc.readReg64 (.gpr 27#5) ∧
      s.readReg64 (.gpr 28#5) = sc.readReg64 (.gpr 28#5) ∧
      Arm64.calleeSavedVRegs s = Arm64.calleeSavedVRegs sc)
    (hex_sc : HbPostExitFields sc s)
    (hnext : ∀ sr : State, sr.pc = ret_pc → sr.status = .Running →
      sr.sp = sc.sp → CalleeSavedPreserved sc sr → HbPostExitFields sc sr →
      RoPostFacts C haveLse sr.mem →
      SepWP P target_pc sr
        ((((dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗
          (((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ ∃∗ R_dead : SepProp, R_dead)) ∗ G)) post) :
    SepWP P target_pc s
      (((sc.sp - 64#64) ↦₆₄ sc.readReg64 (.gpr 29#5)) ∗
       ((sc.sp - 56#64) ↦₆₄ ret_pc) ∗
       ((sc.sp - 48#64) ↦₆₄ sc.readReg64 (.gpr 23#5)) ∗
       ((sc.sp - 32#64) ↦₆₄ sc.readReg64 (.gpr 22#5)) ∗
       ((sc.sp - 24#64) ↦₆₄ sc.readReg64 (.gpr 21#5)) ∗
       ((sc.sp - 16#64) ↦₆₄ sc.readReg64 (.gpr 20#5)) ∗
       ((sc.sp - 8#64) ↦₆₄ sc.readReg64 (.gpr 19#5)) ∗
       stackAt (sc.sp - 0x60#64) 0x130 ∗
       (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
       (dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗
       ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
       (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
       (muslErrnoAddr s ↦₃₂ errno0) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
       HbAltstackInv4k C S altOpt ∗ HbAltstackMapped altOpt ∗ Dead ∗ G) post := by
  have hal_mainAlt : MemWidth.isAligned .X64 C.mainAltstackAddr = true :=
    hbAlign64_of_mod hs.mainAltstack_align
  have hal_page : MemWidth.isAligned .X64 C.std.pageSizeGlobalAddr = true :=
    hbAlign64_of_mod hs.pageSizeGlobal_align
  have hal_lock : MemWidth.isAligned .W32 S.threadInfoLockAddr = true :=
    hbAlign32_of_mod (by have := hs.threadInfoLock_align; omega)
  have hal_lock8 : MemWidth.isAligned .X64 (S.threadInfoLockAddr + 8#64) = true :=
    hbAlign64_of_mod (by have := hs.threadInfoLock_align; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have hal_root : MemWidth.isAligned .X64 S.threadInfoRootAddr = true :=
    hbAlign64_of_mod hs.threadInfoRoot_align
  have hsp_sub_al : (sc.sp - 0x60#64 &&& 15#64 == 0#64) = true :=
    sc.spAligned_sub 0x60#64 hsp_align
  have huss_ne : (sc.sp - 0x60#64) - 152#64 ≠ 0#64 := by bv_omega
  have huss_fit : ((sc.sp - 0x60#64) - 152#64).toNat + 24 ≤ 2 ^ 64 := by bv_omega
  refine SepWP.weaken_pre
    (P' := (C.mainAltstackAddr ↦₆₄ hbAltstackPtr altOpt) ∗
      ((S.threadInfoRootAddr ↦₆₄ 0#64) ∗
       (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
       ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
       HbAltstackOwn entries altOpt ∗ HbAltstackMapped altOpt ∗
       stackAt (sc.sp - 0x60#64) 0x130 ∗
       ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
       (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
       (muslErrnoAddr s ↦₃₂ errno0) ∗
       (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
       (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
       (((sc.sp - 64#64) ↦₆₄ sc.readReg64 (.gpr 29#5)) ∗
        ((sc.sp - 56#64) ↦₆₄ ret_pc) ∗
        ((sc.sp - 48#64) ↦₆₄ sc.readReg64 (.gpr 23#5)) ∗
        ((sc.sp - 32#64) ↦₆₄ sc.readReg64 (.gpr 22#5)) ∗
        ((sc.sp - 24#64) ↦₆₄ sc.readReg64 (.gpr 21#5)) ∗
        ((sc.sp - 16#64) ↦₆₄ sc.readReg64 (.gpr 20#5)) ∗
        ((sc.sp - 8#64) ↦₆₄ sc.readReg64 (.gpr 19#5)) ∗
        ((S.threadInfoRootAddr + 8#64) ↦₆₄ 0#64) ∗
        ((S.threadInfoRootAddr + 16#64) ↦₆₄ 0#64) ∗
        (dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗
        ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ Dead ∗ G)))
    (by
      refine Entails.trans (Q := HbAltstackInv4k C S altOpt ∗ _) (by sep_frame) ?_
      exact Entails.trans (sepConj_mono_left (hbAltstackInv_entails_own hraw)) (by sep_frame)) ?_
  have ⟨hf_184, hf_188, hf_18c, hw_190⟩ :
      P.fetch (C.std.cleanupClosureAddr + 0x184#64) =
        some (iAdrp .x8 (C.std.cleanupClosureAddr + 0x184#64) C.mainAltstackAddr) ∧
      P.fetch (C.std.cleanupClosureAddr + 0x188#64) =
        some (iLdr64Lo12 .x0 .x8 C.mainAltstackAddr) ∧
      P.fetch (C.std.cleanupClosureAddr + 0x18c#64) =
        some (iBl (C.std.cleanupClosureAddr + 0x18c#64) C.dropStackHandlerAddr) ∧
      P.hasCode (C.std.cleanupClosureAddr + 0x190#64)
        [0xa9454ff4#32, 0xf9401bf7#32, 0xa94457f6#32, 0xa9427bfd#32, 0x910183ff#32, 0xd65f03c0#32] := by
    hb_unpack_code hbCleanupClosurePostChunks hc.cleanupPost
    exact ⟨by with_reducible assumption, by with_reducible assumption,
      by with_reducible assumption, by with_reducible assumption⟩
  wp_steps 2
  refine step_bl_to (pc := C.std.cleanupClosureAddr + 0x18c#64) (dst := C.dropStackHandlerAddr)
    (by wp_ro_simp) (by wp_ro_simp) hf_18c ?_
  rw [show C.std.cleanupClosureAddr + 0x18c#64 + 4#64 = C.std.cleanupClosureAddr + 0x190#64 by bv_lin]
  refine SepWP.weaken_pre_frame
    (P' := stackAt s.sp 0x130 ∗ (S.threadInfoRootAddr ↦₆₄ 0#64) ∗
      (S.threadInfoLockAddr ↦₃₂ 0#32) ∗ ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗
      ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
      ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
      (muslErrnoAddr s ↦₃₂ errno0) ∗
      (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
      HbAltstackOwn entries altOpt ∗ HbAltstackMapped altOpt ∗
      ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
       (((sc.sp - 64#64) ↦₆₄ sc.readReg64 (.gpr 29#5)) ∗
        ((sc.sp - 56#64) ↦₆₄ ret_pc) ∗
        ((sc.sp - 48#64) ↦₆₄ sc.readReg64 (.gpr 23#5)) ∗
        ((sc.sp - 32#64) ↦₆₄ sc.readReg64 (.gpr 22#5)) ∗
        ((sc.sp - 24#64) ↦₆₄ sc.readReg64 (.gpr 21#5)) ∗
        ((sc.sp - 16#64) ↦₆₄ sc.readReg64 (.gpr 20#5)) ∗
        ((sc.sp - 8#64) ↦₆₄ sc.readReg64 (.gpr 19#5)) ∗
        (C.mainAltstackAddr ↦₆₄ hbAltstackPtr altOpt) ∗
        ((S.threadInfoRootAddr + 8#64) ↦₆₄ 0#64) ∗
        ((S.threadInfoRootAddr + 16#64) ↦₆₄ 0#64) ∗
        (dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗
        ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ Dead ∗ G)))
    (fun R hm => by rw [hsp]; simp only [wp_norm, arm64_norm] at hm ⊢; revert hm; sep_frame) ?_
  apply hbDropHandler_wp (ret_pc := C.std.cleanupClosureAddr + 0x190#64)
    hc.svc_eq hc.dropHandler hc.teardownSys hc.getauxval
    hc.cas4Acq hc.cas8Acq hc.swp4Rel hal_page hal_lock hal_lock8 hal_root hnonull hbnd_req
  · simpa [wp_norm, arm64_norm, hsp] using huss_ne
  · simpa [wp_norm, arm64_norm, hsp] using huss_fit
  · rfl
  · wp_ro_simp
  · simpa [State.spAligned, wp_norm, arm64_norm, hsp] using hsp_sub_al
  · simp only [wp_norm, arm64_norm]
  · wp_ro_simp
  · intro sf errno1 hpc_f hrun_f hsp_f hsp_al_f hcs_f hex_f hro_f
    have hsp_sf : sf.sp = sc.sp - 0x60#64 := by simpa [wp_norm, arm64_norm, hsp] using hsp_f
    have hsp_al_raw : (sf.sp &&& 15#64 == 0#64) = true := hsp_al_f
    have hc64 : sc.sp - 64#64 = sf.sp + 32#64 := by rw [hsp_sf]; bv_lin
    have hc56 : sc.sp - 56#64 = sf.sp + 40#64 := by rw [hsp_sf]; bv_lin
    have hc48 : sc.sp - 48#64 = sf.sp + 48#64 := by rw [hsp_sf]; bv_lin
    have hc32 : sc.sp - 32#64 = sf.sp + 64#64 := by rw [hsp_sf]; bv_lin
    have hc24 : sc.sp - 24#64 = sf.sp + 72#64 := by rw [hsp_sf]; bv_lin
    have hc16 : sc.sp - 16#64 = sf.sp + 80#64 := by rw [hsp_sf]; bv_lin
    have hc08 : sc.sp - 8#64 = sf.sp + 88#64 := by rw [hsp_sf]; bv_lin
    have hsp_end : sf.sp + 96#64 = sc.sp := by rw [hsp_sf]; bv_lin
    clear hf_184 hf_188 hf_18c hsp_f hsp_sf
    wp_conv_pre => rw [hc64, hc56, hc48, hc32, hc24, hc16, hc08]
    wp_steps 6
    refine SepWP.weaken_pre (hbFold_dead_closure_post C dataPtr flagPtr G) ?_
    refine hnext _ (by wp_ro_simp) (by wp_ro_simp)
      (by simp only [wp_norm, arm64_norm])
      ?_
      (HbPostExitFields.trans hex_sc (HbPostExitFields.trans hb_exit_rfl
        (HbPostExitFields.trans hex_f hb_exit_rfl)))
      hro_f
    rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs_f with ⟨_, _, _, _, _, g24, g25, g26, g27, g28, _, gv⟩
    simp only [wp_norm, arm64_norm] at g24 g25 g26 g27 g28 gv
    rw [CalleeSavedPreserved.iff_regs]
    simp [wp_norm, arm64_norm, hcs_hi.1, hcs_hi.2.1, hcs_hi.2.2.1, hcs_hi.2.2.2.1,
      hcs_hi.2.2.2.2.1, hcs_hi.2.2.2.2.2, g24, g25, g26, g27, g28, gv]

private theorem hbStdout_merge_g30 (g : BitVec 64) :
    ((g + 0x30#64) ↦₈ 0#8) ∗ memRegion (g + 0x31#64) 7 ⊢
      ∃∗ w_g30 : BitVec 64, (g + 0x30#64) ↦₆₄ w_g30 := by
  have h1 := pointsToBytes_memRegion_entails (g + 0x30#64) [0#8] 8 (by decide) (by decide)
  rw [pointsToBytes_singleton, show (g + 0x30#64) + BitVec.ofNat 64 [0#8].length = g + 0x31#64 by
    simp only [List.length_singleton]; bv_lin] at h1
  refine Entails.trans h1 ?_
  rw [show (8 : Nat) = 8 * 1 from rfl, memRegion_cells (g + 0x30#64) 1 (by decide),
    cells_succ, cells_zero]
  simp only [sepConj_emp]
  exact Entails.refl _

private theorem hbCombine_cell_lo_byte4 (sp : BitVec 64)
    {b0 b1 b2 b3 : BitVec 8} {hi : BitVec 32} {R : SepProp} :
    ((sp - 72#64) ↦₈ b0) ∗ ((sp - 71#64) ↦₈ b1) ∗ ((sp - 70#64) ↦₈ b2) ∗
      ((sp - 69#64) ↦₈ b3) ∗ ((sp - 68#64) ↦₃₂ hi) ∗ R =
      ((sp - 72#64) ↦₆₄ (hi ++ (b3 ++ b2 ++ b1 ++ b0))) ∗ R := by
  rw [hbPointsTo8_combine32_sub sp 72#64 71#64 70#64 69#64 b0 b1 b2 b3 (((sp - 68#64) ↦₃₂ hi) ∗ R),
    pointsTo32_combine64_sub sp 72#64 68#64 _ hi R]

private theorem hbFocusFrame {P : Program} {target_pc : BitVec 64} {s : State}
    (Sub : SepProp) {Frame All : SepProp} {post : State → SepProp → Prop}
    (hent : All ⊢ Sub ∗ Frame)
    (hwp : ∀ F : SepProp, F = Frame → SepWP P target_pc s (Sub ∗ F) post) :
    SepWP P target_pc s All post :=
  SepWP.weaken_pre hent (hwp Frame rfl)

private theorem hbCleanupClosure_from_dc_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {lim : MallocngLimits} (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {haveLse : BitVec 8} {target_pc ret_pc dataPtr flagPtr auxvAddr bufPtr : BitVec 64}
    {w96 w88 w80 w72 : BitVec 64}
    {lc_leak blk_leak : Nat} {e0 : BitVec 32}
    {entries : List (BitVec 64 × BitVec 64)} {altOpt : Option (BitVec 64 × Nat)}
    {s_base sc s : State} {Tear Dead G : SepProp} {post : State → SepProp → Prop}
    (hc : HbPostMainCode P C S) (hv : C.Valid) (hs : S.Valid C)
    (htear : ∀ s_t, M.Heap γ lc_leak blk_leak s_t ∗ Tear ⊢
      (C.mallocng.libcNeedLocksAddr ↦₈ 0#8) ∗ (C.mallocng.libcAuxvAddr ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
      ∃∗ R_dead : SepProp, R_dead)
    (hraw : ∀ altBase altRawSz, altOpt = some (altBase, altRawSz) →
      altRawSz = Arm64.pageAlignUp (hbAltstackReqSz entries))
    (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (hbnd_req : hbAltstackReqSz entries ≤ 524288)
    (hsp_lo : 4240 ≤ sc.sp.toNat) (hsp_align : sc.spAligned = true)
    (hbuf_nz : bufPtr ≠ 0#64)
    (hpc : s.pc = C.std.cleanupClosureAddr + 0xdc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sc.sp - 0x60#64)
    (hx19 : s.readReg64 (.gpr 19#5) = C.std.stdoutGlobalAddr &&& 0xfffffffffffff000#64)
    (hx22 : s.readReg64 (.gpr 22#5) = 1#64)
    (hcs_hi : s.readReg64 (.gpr 24#5) = sc.readReg64 (.gpr 24#5) ∧
      s.readReg64 (.gpr 25#5) = sc.readReg64 (.gpr 25#5) ∧
      s.readReg64 (.gpr 26#5) = sc.readReg64 (.gpr 26#5) ∧
      s.readReg64 (.gpr 27#5) = sc.readReg64 (.gpr 27#5) ∧
      s.readReg64 (.gpr 28#5) = sc.readReg64 (.gpr 28#5) ∧
      Arm64.calleeSavedVRegs s = Arm64.calleeSavedVRegs sc)
    (hp_base : ProcessFieldsPreserved s_base s) (hex_sc : HbPostExitFields sc s)
    (hnext : ∀ sr : State, sr.pc = ret_pc → sr.status = .Running →
      sr.sp = sc.sp → CalleeSavedPreserved sc sr → HbPostExitFields sc sr →
      RoPostFacts C haveLse sr.mem →
      SepWP P target_pc sr
        ((((dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗
          (((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ ∃∗ R_dead : SepProp, R_dead)) ∗ G)) post) :
    SepWP P target_pc s
      (((sc.sp - 96#64) ↦₆₄ w96) ∗ ((sc.sp - 88#64) ↦₆₄ w88) ∗
       ((sc.sp - 80#64) ↦₆₄ w80) ∗ ((sc.sp - 72#64) ↦₆₄ w72) ∗
       ((sc.sp - 64#64) ↦₆₄ sc.readReg64 (.gpr 29#5)) ∗
       ((sc.sp - 56#64) ↦₆₄ ret_pc) ∗
       ((sc.sp - 48#64) ↦₆₄ sc.readReg64 (.gpr 23#5)) ∗
       ((sc.sp - 32#64) ↦₆₄ sc.readReg64 (.gpr 22#5)) ∗
       ((sc.sp - 24#64) ↦₆₄ sc.readReg64 (.gpr 21#5)) ∗
       ((sc.sp - 16#64) ↦₆₄ sc.readReg64 (.gpr 20#5)) ∗
       ((sc.sp - 8#64) ↦₆₄ sc.readReg64 (.gpr 19#5)) ∗
       stackAt (sc.sp - 0x60#64) 4144 ∗
       (C.std.stdoutGlobalAddr ↦₆₄ 0#64) ∗
       ((C.std.stdoutGlobalAddr + 0x08#64) ↦₃₂ 0#32) ∗
       ((C.std.stdoutGlobalAddr + 0x0c#64) ↦₃₂ 0#32) ∗
       ((C.std.stdoutGlobalAddr + 0x10#64) ↦₆₄ 0#64) ∗
       ((C.std.stdoutGlobalAddr + 0x18#64) ↦₆₄ 1024#64) ∗
       ((C.std.stdoutGlobalAddr + 0x20#64) ↦₆₄ bufPtr) ∗
       ((C.std.stdoutGlobalAddr + 0x28#64) ↦₆₄ 0#64) ∗
       ((C.std.stdoutGlobalAddr + 0x30#64) ↦₈ 0#8) ∗
       memRegion (C.std.stdoutGlobalAddr + 0x31#64) 7 ∗
       M.Heap γ (lc_leak + mallocngBlockCost 1024) (blk_leak + 1) s_base ∗
       M.Block γ bufPtr 1024 ∗ memRegion bufPtr 1024 ∗ Tear ∗
       (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
       (dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗
       (muslErrnoAddr s_base ↦₃₂ e0) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
       HbAltstackInv4k C S altOpt ∗ HbAltstackMapped altOpt ∗ Dead ∗ G) post := by
  obtain ⟨_, hal_g08, _, _⟩ := hbValid_stdout_align hv
  have hsp_sub_al : (sc.sp - 0x60#64 &&& 15#64 == 0#64) = true :=
    sc.spAligned_sub 0x60#64 hsp_align
  have hsp_s_al : s.spAligned = true := by simpa [State.spAligned, hsp] using hsp_sub_al
  refine hb_wp_step_proc C.std.cas4AcqAddr hc.no_hooks hc.svc_eq (by
    hb_unpack_code_nosvc hbCleanupClosurePostChunks hc.cleanupPost
    iterate 3 (wp_steps; hb_norm_jmp)
    exact hb_done_proc) fun m0 hp0 => ?_
  refine call_stdCas4 hc.atomics.cas4Acq_ok (haveLse := haveLse)
    (ptr := C.std.stdoutGlobalAddr + 0x08#64) (v0 := 0#32) (exp := 0#32) (new := 1#32)
    (ret_pc := C.std.cleanupClosureAddr + 0xf0#64) (F := ?_) (by sep_frame)
    (fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hstd1 => ?_)
    (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm, hsp] using hsp_sub_al)
    (halign := hal_g08)
  simp only [beq_self_eq_true, ↓reduceIte]
  have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := by simpa [Reg.x0] using hx0_1
  have hx19_1 : s1.readReg64 (.gpr 19#5) = C.std.stdoutGlobalAddr &&& 0xfffffffffffff000#64 := by
    have := hcs1.readReg64_x19; simpa [wp_norm, arm64_norm, hx19] using this
  have hx22_1 : s1.readReg64 (.gpr 22#5) = 1#64 := by
    have := hcs1.readReg64_x22; simpa [wp_norm, arm64_norm, hx22] using this
  have hsp1_eq : s1.sp = sc.sp - 0x60#64 := by simpa [wp_norm, arm64_norm, hsp] using hsp1
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1_eq] using hsp_sub_al
  refine SepWP.weaken_pre (P' := ((sc.sp - 72#64) ↦₆₄ w72) ∗ _) (by sep_frame) ?_
  rw [pointsTo64_split32_sub sc.sp 72#64 68#64,
      hbPointsTo32_split8_sub sc.sp 72#64 71#64 70#64 69#64]
  refine hbFocusFrame
    (((sc.sp - 96#64) ↦₆₄ w96) ∗ ((sc.sp - 88#64) ↦₆₄ w88) ∗ ((sc.sp - 80#64) ↦₆₄ w80) ∗
     ((sc.sp - 72#64) ↦₈ _) ∗ (C.std.stdoutGlobalAddr ↦₆₄ 0#64) ∗
     ((C.std.stdoutGlobalAddr + 0x0c#64) ↦₃₂ 0#32) ∗
     ((C.std.stdoutGlobalAddr + 0x10#64) ↦₆₄ 0#64))
    (by sep_frame) fun F1 hF1 => ?_
  refine hb_wp_step_proc C.lineWriterDropAddr hc.no_hooks hc.svc_eq (by
    hb_unpack_code_nosvc hbCleanupClosurePostChunks hc.cleanupPost
    iterate 8 (wp_steps; hb_norm_jmp)
    exact hb_done_proc) fun m1 hp1 => ?_
  subst hF1
  have hp_lw : ProcessFieldsPreserved s_base _ :=
    hp_base.trans (hp0.trans ((hbStdState_toProcess hstd1).trans hp1))
  have hht_lw := hbHeap_of_proc M hp_lw (γ := γ) (lc := lc_leak + mallocngBlockCost 1024) (blk := blk_leak + 1)
  have herr_lw := (muslErrnoAddr_of_exitFields ⟨hp_lw.1, hp_lw.2.1, hp_lw.2.2.1, hp_lw.2.2.2.1⟩).symm
  wp_conv_pre => rw [herr_lw]
  refine SepWP.weaken_pre
    (P' := M.Heap γ (lc_leak + mallocngBlockCost 1024) (blk_leak + 1) s_base ∗ _)
    (by sep_frame) ?_
  refine SepWP.weaken_pre (sepConj_mono_left hht_lw) ?_
  refine SepWP.weaken_pre (by sep_frame)
    (hbLineWriterDrop_wp M γ (lc := lc_leak) (blk := blk_leak) (e0 := e0)
      (ret_pc := C.std.cleanupClosureAddr + 0x13c#64)
      (sp0 := sc.sp - 0x60#64) (bufPtr := bufPtr) hc
      ?_ ?_ ?_ ?_ ?_ ?_ hbuf_nz
      fun s2 e1 hpc2 hrun2 hsp2 hcs2 hex2 => ?_)
  · exact hb_wp_a
  · simp [wp_norm, arm64_norm, hrun1]
  · simpa [wp_norm, arm64_norm] using hsp1_eq
  · simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_al
  · exact hb_wp_a
  · exact hb_wp_a
  have hx19_2 : s2.readReg64 (.gpr 19#5) = C.std.stdoutGlobalAddr + 0x0c#64 := by
    simpa [wp_norm, arm64_norm] using hcs2.readReg64_x19
  have hsp2_eq : s2.sp = sc.sp - 0x60#64 := hsp2
  have hsp2_al : s2.spAligned = true := by simpa [State.spAligned, hsp2_eq] using hsp_sub_al
  refine SepWP.weaken_pre
    (P' := ((sc.sp - 72#64) ↦₈ 0#8) ∗ ((sc.sp - 71#64) ↦₈ _) ∗
      ((sc.sp - 70#64) ↦₈ _) ∗ ((sc.sp - 69#64) ↦₈ _) ∗ ((sc.sp - 68#64) ↦₃₂ _) ∗
      (((C.std.stdoutGlobalAddr + 0x30#64) ↦₈ 0#8) ∗ memRegion (C.std.stdoutGlobalAddr + 0x31#64) 7) ∗ _)
    (by sep_frame) ?_
  rw [hbCombine_cell_lo_byte4 sc.sp]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (hbStdout_merge_g30 C.std.stdoutGlobalAddr))) ?_
  wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w_g30
  refine hbFocusFrame
    (((sc.sp - 96#64) ↦₆₄ _) ∗ ((sc.sp - 88#64) ↦₆₄ _) ∗ ((sc.sp - 80#64) ↦₆₄ _) ∗
     ((sc.sp - 72#64) ↦₆₄ _) ∗ (C.std.stdoutGlobalAddr ↦₆₄ 1#64) ∗
     ((C.std.stdoutGlobalAddr + 0x0c#64) ↦₃₂ 1#32) ∗
     ((C.std.stdoutGlobalAddr + 0x10#64) ↦₆₄ _) ∗
     ((C.std.stdoutGlobalAddr + 0x18#64) ↦₆₄ _) ∗
     ((C.std.stdoutGlobalAddr + 0x20#64) ↦₆₄ _) ∗
     ((C.std.stdoutGlobalAddr + 0x28#64) ↦₆₄ _) ∗
     ((C.std.stdoutGlobalAddr + 0x30#64) ↦₆₄ w_g30))
    (by sep_frame) fun F2 hF2 => ?_
  refine hb_wp_step_proc C.std.swp4RelAddr hc.no_hooks hc.svc_eq (by
    hb_unpack_code_nosvc hbCleanupClosurePostChunks hc.cleanupPost
    iterate 4 (wp_steps; hb_norm_jmp)
    exact hb_done_proc) fun m3 hp3 => ?_
  subst hF2
  refine call_stdSwp4 hc.atomics.swp4Rel_ok (haveLse := haveLse)
    (ptr := C.std.stdoutGlobalAddr + 0x08#64) (v0 := 1#32) (new := 0#32)
    (ret_pc := C.std.cleanupClosureAddr + 0x17c#64) (F := ?_) (by sep_frame)
    (fun s4 hpc4 hrun4 hsp4 hcs4 hx0_4 hstd4 => ?_)
    (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm] using hsp2_al)
    (halign := hal_g08)
  have hx0_4' : s4.readReg64 (.gpr 0#5) = 1#64 := by simpa [Reg.x0] using hx0_4
  have hsp4_eq : s4.sp = sc.sp - 0x60#64 := by simpa [wp_norm, arm64_norm, hsp2_eq] using hsp4
  have hsp4_al : s4.spAligned = true := by simpa [State.spAligned, hsp4_eq] using hsp_sub_al
  refine hb_wp_step_proc (C.std.cleanupClosureAddr + 0x184#64) hc.no_hooks hc.svc_eq (by
    hb_unpack_code_nosvc hbCleanupClosurePostChunks hc.cleanupPost
    wp_steps 2; hb_norm_jmp; exact hb_done_proc) fun m5 hp5 => ?_
  have hp_25 : ProcessFieldsPreserved s2 _ :=
    hp3.trans ((hbStdState_toProcess hstd4).trans hp5)
  have hht_end := hbHeap_of_proc M hp_25 (γ := γ) (lc := lc_leak) (blk := blk_leak)
  have herr_end := (muslErrnoAddr_of_exitFields ⟨hp_25.1, hp_25.2.1, hp_25.2.2.1, hp_25.2.2.2.1⟩).symm
  refine SepWP.weaken_pre (P' := (M.Heap γ lc_leak blk_leak _ ∗ Tear) ∗ _)
    (by
      rw [herr_end]
      refine Entails.trans (Q := M.Heap γ lc_leak blk_leak s2 ∗ _) (by sep_frame) ?_
      exact Entails.trans (sepConj_mono_left hht_end) (by sep_frame)) ?_
  refine SepWP.weaken_pre (sepConj_mono_left (htear _)) ?_
  wp_conv_pre => simp only [hv.needLocks_eq, hv.auxv_eq, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro R_heap_dead
  rw [hbStackAt_split (sc.sp - 0x60#64) 0x130 3840]
  refine SepWP.weaken_pre
    (P' := ((sc.sp - 64#64) ↦₆₄ sc.readReg64 (.gpr 29#5)) ∗
       ((sc.sp - 56#64) ↦₆₄ ret_pc) ∗
       ((sc.sp - 48#64) ↦₆₄ sc.readReg64 (.gpr 23#5)) ∗
       ((sc.sp - 32#64) ↦₆₄ sc.readReg64 (.gpr 22#5)) ∗
       ((sc.sp - 24#64) ↦₆₄ sc.readReg64 (.gpr 21#5)) ∗
       ((sc.sp - 16#64) ↦₆₄ sc.readReg64 (.gpr 20#5)) ∗
       ((sc.sp - 8#64) ↦₆₄ sc.readReg64 (.gpr 19#5)) ∗
       stackAt (sc.sp - 0x60#64) 0x130 ∗
       (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
       (dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗
       ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
       (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
       (muslErrnoAddr _ ↦₃₂ e1) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
       HbAltstackInv4k C S altOpt ∗ HbAltstackMapped altOpt ∗ _ ∗ G)
    (by sep_frame) ?_
  refine hbCleanupClosure_epilogue_wp hc hs hraw hnonull hbnd_req hsp_lo hsp_align
    hb_wp_a (by simp [wp_norm, arm64_norm, hrun4])
    (by simp [wp_norm, arm64_norm, hsp4_eq])
    ?_
    (HbPostExitFields.trans hex_sc
      (HbPostExitFields.trans ⟨hp0.1, hp0.2.1, hp0.2.2.1, hp0.2.2.2.1⟩
        (HbPostExitFields.trans (HbPostExitFields.ofState hstd1)
          (HbPostExitFields.trans ⟨hp1.1, hp1.2.1, hp1.2.2.1, hp1.2.2.2.1⟩
            (HbPostExitFields.trans hex2 ⟨hp_25.1, hp_25.2.1, hp_25.2.2.1, hp_25.2.2.2.1⟩)))))
    hnext
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with ⟨_, _, _, _, _, a24, a25, a26, a27, a28, _, av⟩
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨_, _, _, _, _, b24, b25, b26, b27, b28, _, bv⟩
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs4 with ⟨_, _, _, _, _, c24, c25, c26, c27, c28, _, cv⟩
  simp only [wp_norm, arm64_norm] at a24 a25 a26 a27 a28 av b24 b25 b26 b27 b28 bv c24 c25 c26 c27 c28 cv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Arm64.calleeSavedVRegs, wp_norm, arm64_norm,
      hcs_hi.1, hcs_hi.2.1, hcs_hi.2.2.1, hcs_hi.2.2.2.1, hcs_hi.2.2.2.2.1, hcs_hi.2.2.2.2.2,
      a24, a25, a26, a27, a28, av, b24, b25, b26, b27, b28, bv, c24, c25, c26, c27, c28, cv]

private theorem hbCleanupClosure_initTrue_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {lim : MallocngLimits} (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {haveLse : BitVec 8} {target_pc ret_pc dataPtr flagPtr auxvAddr bufPtr tid : BitVec 64}
    {w96 w88 w80 w72 : BitVec 64}
    {lc_leak blk_leak : Nat} {e0 : BitVec 32}
    {entries : List (BitVec 64 × BitVec 64)} {altOpt : Option (BitVec 64 × Nat)}
    {s_base sc s : State} {Tear Dead G : SepProp} {post : State → SepProp → Prop}
    (hc : HbPostMainCode P C S) (hv : C.Valid) (hs : S.Valid C)
    (htear : ∀ s_t, M.Heap γ lc_leak blk_leak s_t ∗ Tear ⊢
      (C.mallocng.libcNeedLocksAddr ↦₈ 0#8) ∗ (C.mallocng.libcAuxvAddr ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
      ∃∗ R_dead : SepProp, R_dead)
    (hraw : ∀ altBase altRawSz, altOpt = some (altBase, altRawSz) →
      altRawSz = Arm64.pageAlignUp (hbAltstackReqSz entries))
    (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (hbnd_req : hbAltstackReqSz entries ≤ 524288)
    (hsp_lo : 4240 ≤ sc.sp.toNat) (hsp_align : sc.spAligned = true)
    (hbuf_nz : bufPtr ≠ 0#64) (htid : tid = 0#64 ∨ tid = 1#64)
    (hpc : s.pc = C.std.cleanupClosureAddr + 0x3c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sc.sp - 0x60#64)
    (hx8 : s.readReg64 (.gpr 8#5) = 0#64)
    (hx29 : s.readReg64 (.gpr 29#5) = sc.sp - 64#64)
    (hcs_hi : s.readReg64 (.gpr 24#5) = sc.readReg64 (.gpr 24#5) ∧
      s.readReg64 (.gpr 25#5) = sc.readReg64 (.gpr 25#5) ∧
      s.readReg64 (.gpr 26#5) = sc.readReg64 (.gpr 26#5) ∧
      s.readReg64 (.gpr 27#5) = sc.readReg64 (.gpr 27#5) ∧
      s.readReg64 (.gpr 28#5) = sc.readReg64 (.gpr 28#5) ∧
      Arm64.calleeSavedVRegs s = Arm64.calleeSavedVRegs sc)
    (hp_base : ProcessFieldsPreserved s_base s) (hex_sc : HbPostExitFields sc s)
    (hnext : ∀ sr : State, sr.pc = ret_pc → sr.status = .Running →
      sr.sp = sc.sp → CalleeSavedPreserved sc sr → HbPostExitFields sc sr →
      RoPostFacts C haveLse sr.mem →
      SepWP P target_pc sr
        ((((dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗
          (((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ ∃∗ R_dead : SepProp, R_dead)) ∗ G)) post) :
    SepWP P target_pc s
      (((sc.sp - 96#64) ↦₆₄ w96) ∗ ((sc.sp - 88#64) ↦₆₄ w88) ∗
       ((sc.sp - 80#64) ↦₆₄ w80) ∗ ((sc.sp - 72#64) ↦₆₄ w72) ∗
       ((sc.sp - 64#64) ↦₆₄ sc.readReg64 (.gpr 29#5)) ∗
       ((sc.sp - 56#64) ↦₆₄ ret_pc) ∗
       ((sc.sp - 48#64) ↦₆₄ sc.readReg64 (.gpr 23#5)) ∗
       ((sc.sp - 36#64) ↦₈ 0#8) ∗
       ((sc.sp - 32#64) ↦₆₄ sc.readReg64 (.gpr 22#5)) ∗
       ((sc.sp - 24#64) ↦₆₄ sc.readReg64 (.gpr 21#5)) ∗
       ((sc.sp - 16#64) ↦₆₄ sc.readReg64 (.gpr 20#5)) ∗
       ((sc.sp - 8#64) ↦₆₄ sc.readReg64 (.gpr 19#5)) ∗
       stackAt (sc.sp - 0x60#64) 4144 ∗
       ((s_base.tpidrEl0 + 0x58#64) ↦₆₄ tid) ∗
       (C.std.threadIdCounterAddr ↦₆₄ tid) ∗
       (C.std.stdoutGlobalAddr ↦₆₄ 0#64) ∗
       ((C.std.stdoutGlobalAddr + 0x08#64) ↦₃₂ 0#32) ∗
       ((C.std.stdoutGlobalAddr + 0x0c#64) ↦₃₂ 0#32) ∗
       ((C.std.stdoutGlobalAddr + 0x10#64) ↦₆₄ 0#64) ∗
       ((C.std.stdoutGlobalAddr + 0x18#64) ↦₆₄ 1024#64) ∗
       ((C.std.stdoutGlobalAddr + 0x20#64) ↦₆₄ bufPtr) ∗
       ((C.std.stdoutGlobalAddr + 0x28#64) ↦₆₄ 0#64) ∗
       ((C.std.stdoutGlobalAddr + 0x30#64) ↦₈ 0#8) ∗
       memRegion (C.std.stdoutGlobalAddr + 0x31#64) 7 ∗
       M.Heap γ (lc_leak + mallocngBlockCost 1024) (blk_leak + 1) s_base ∗
       M.Block γ bufPtr 1024 ∗ memRegion bufPtr 1024 ∗ Tear ∗
       (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
       (dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗
       (muslErrnoAddr s_base ↦₃₂ e0) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
       HbAltstackInv4k C S altOpt ∗ HbAltstackMapped altOpt ∗ Dead ∗ G) post := by
  obtain ⟨_, _, _, hal_ctr⟩ := hbValid_stdout_align hv
  have hsp_sub_al : (sc.sp - 0x60#64 &&& 15#64 == 0#64) = true :=
    sc.spAligned_sub 0x60#64 hsp_align
  have htp_eq : s_base.tpidrEl0 = s.tpidrEl0 := hp_base.2.2.1.symm
  wp_conv_pre => rw [htp_eq]
  rcases htid with rfl | rfl
  · refine hb_wp_step_proc C.std.cas8RelaxAddr hc.no_hooks hc.svc_eq (by
      hb_unpack_code_nosvc hbCleanupClosurePostChunks hc.cleanupPost
      iterate 6 (wp_steps; hb_norm_jmp)
      exact hb_done_proc) fun ma hpa => ?_
    refine call_stdCas8 hc.atomics.cas8Relax_ok (haveLse := haveLse)
      (ptr := C.std.threadIdCounterAddr) (v0 := 0#64) (exp := 0#64) (new := 1#64)
      (ret_pc := C.std.cleanupClosureAddr + 0xbc#64) (F := ?_) (by sep_frame)
      (fun sc8 hpc_c8 hrun_c8 hsp_c8 hcs_c8 hx0_c8 hstd_c8 => ?_)
      (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm, hsp] using hsp_sub_al)
      (halign := hal_ctr)
    simp only [beq_self_eq_true, ↓reduceIte]
    have hx0_c8' : sc8.readReg64 (.gpr 0#5) = 0#64 := by simpa [Reg.x0] using hx0_c8
    have hx19_c8 : sc8.readReg64 (.gpr 19#5) = 0x58#64 := by
      have := hcs_c8.readReg64_x19; simpa [wp_norm, arm64_norm] using this
    have hx21_c8 : sc8.readReg64 (.gpr 21#5) = 0#64 := by
      have := hcs_c8.readReg64_x21; simpa [wp_norm, arm64_norm] using this
    have hx22_c8 : sc8.readReg64 (.gpr 22#5) = 1#64 := by
      have := hcs_c8.readReg64_x22; simpa [wp_norm, arm64_norm] using this
    have hx23_c8 : sc8.readReg64 (.gpr 23#5) = s.tpidrEl0 := by
      have := hcs_c8.readReg64_x23; simpa [wp_norm, arm64_norm] using this
    have hsp_c8_eq : sc8.sp = sc.sp - 0x60#64 := by simpa [wp_norm, arm64_norm, hsp] using hsp_c8
    refine hb_wp_step_proc (C.std.cleanupClosureAddr + 0xdc#64) hc.no_hooks hc.svc_eq (by
      hb_unpack_code_nosvc hbCleanupClosurePostChunks hc.cleanupPost
      iterate 2 (wp_steps; hb_norm_jmp)
      exact hb_done_proc) fun mb hpb => ?_
    refine SepWP.weaken_pre (by sep_frame)
      (hbCleanupClosure_from_dc_wp (w96 := w96) (w88 := w88) (w80 := w80) (w72 := w72) (e0 := e0)
        (Dead := ((sc.sp - 36#64) ↦₈ 0#8) ∗ ((s.tpidrEl0 + 0x58#64) ↦₆₄ 1#64) ∗
          (C.std.threadIdCounterAddr ↦₆₄ 1#64) ∗ Dead)
        M γ hc hv hs htear hraw hnonull hbnd_req
        hsp_lo hsp_align hbuf_nz
        hb_wp_a (by simp [wp_norm, arm64_norm, hrun_c8])
        (by simp [wp_norm, arm64_norm, hsp_c8_eq])
        hb_wp_a (by simp [wp_norm, arm64_norm, hx22_c8])
        ?_
        (hp_base.trans (hpa.trans ((hbStdState_toProcess hstd_c8).trans hpb)))
        (HbPostExitFields.trans hex_sc
          (HbPostExitFields.trans ⟨hpa.1, hpa.2.1, hpa.2.2.1, hpa.2.2.2.1⟩
            (HbPostExitFields.trans (HbPostExitFields.ofState hstd_c8)
              ⟨hpb.1, hpb.2.1, hpb.2.2.1, hpb.2.2.2.1⟩)))
        hnext)
    rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs_c8 with ⟨_, _, _, _, _, d24, d25, d26, d27, d28, _, dv⟩
    simp only [wp_norm, arm64_norm] at d24 d25 d26 d27 d28 dv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Arm64.calleeSavedVRegs, wp_norm, arm64_norm,
        hcs_hi.1, hcs_hi.2.1, hcs_hi.2.2.1, hcs_hi.2.2.2.1, hcs_hi.2.2.2.2.1, hcs_hi.2.2.2.2.2,
        d24, d25, d26, d27, d28, dv]
  · refine hb_wp_step_proc (C.std.cleanupClosureAddr + 0xdc#64) hc.no_hooks hc.svc_eq (by
      hb_unpack_code_nosvc hbCleanupClosurePostChunks hc.cleanupPost
      wp_steps 14; wp_steps 2; hb_norm_jmp
      exact hb_done_proc) fun ma hpa => ?_
    refine SepWP.weaken_pre (by sep_frame)
      (hbCleanupClosure_from_dc_wp (w96 := w96) (w88 := w88) (w80 := w80) (w72 := w72) (e0 := e0)
        (Dead := ((sc.sp - 36#64) ↦₈ 0#8) ∗ ((s.tpidrEl0 + 0x58#64) ↦₆₄ 1#64) ∗
          (C.std.threadIdCounterAddr ↦₆₄ 1#64) ∗ Dead)
        M γ hc hv hs htear hraw hnonull hbnd_req
        hsp_lo hsp_align hbuf_nz
        hb_wp_a (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        hb_wp_a hb_wp_a
        ?_
        (hp_base.trans hpa)
        (HbPostExitFields.trans hex_sc ⟨hpa.1, hpa.2.1, hpa.2.2.1, hpa.2.2.2.1⟩)
        hnext)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Arm64.calleeSavedVRegs, wp_norm, arm64_norm,
        hcs_hi.1, hcs_hi.2.1, hcs_hi.2.2.1, hcs_hi.2.2.2.1, hcs_hi.2.2.2.2.1, hcs_hi.2.2.2.2.2]

/-- `SepWP` for `std::rt::cleanup`'s `Once` closure (`C.std.cleanupClosureAddr`), flushing and
    dropping `STDOUT` when `init = true`, tearing down `M.Heap`, and running `drop_handler`. -/
theorem hbCleanupClosure_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {lim : MallocngLimits} {M : MallocngCoreIface P C.mallocng lim} {γ : GhostName}
    {init : Bool} {lc_leak blk_leak : Nat} {e0 : BitVec 32}
    {haveLse : BitVec 8} {target_pc ret_pc sp_cl dataPtr flagPtr auxvAddr : BitVec 64}
    {entries : List (BitVec 64 × BitVec 64)} {altOpt : Option (BitVec 64 × Nat)}
    {s_base sc : State} {Tear Extra G : SepProp} {post : State → SepProp → Prop}
    (hc : HbPostMainCode P C S) (hv : C.Valid) (hs : S.Valid C)
    (htear : ∀ s_t, M.Heap γ lc_leak blk_leak s_t ∗ Tear ⊢
      (C.mallocng.libcNeedLocksAddr ↦₈ 0#8) ∗ (C.mallocng.libcAuxvAddr ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
      ∃∗ R_dead : SepProp, R_dead)
    (hraw : ∀ altBase altRawSz, altOpt = some (altBase, altRawSz) →
      altRawSz = Arm64.pageAlignUp (hbAltstackReqSz entries))
    (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (hbnd_req : hbAltstackReqSz entries ≤ 524288)
    (hpc : sc.pc = C.std.cleanupClosureAddr) (hrun : sc.status = .Running)
    (hsp : sc.sp = sp_cl) (hsp_align : sc.spAligned = true) (hsp_lo : 4240 ≤ sp_cl.toNat)
    (hlr : sc.readReg64 Reg.lr = ret_pc) (hx0 : sc.readReg64 .x0 = dataPtr)
    (hproc : ProcessFieldsPreserved s_base sc)
    (hnext : ∀ sr : State, sr.pc = ret_pc → sr.status = .Running →
      sr.sp = sc.sp → CalleeSavedPreserved sc sr → HbPostExitFields sc sr →
      RoPostFacts C haveLse sr.mem →
      SepWP P target_pc sr
        ((((dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗
          (((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ ∃∗ R_dead : SepProp, R_dead)) ∗ G)) post) :
    SepWP P target_pc sc
      ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
       (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
       (dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 1#8) ∗
       HbStdoutInv C M γ init ∗
       HbThreadIdInv C s_base.tpidrEl0 ∗
       M.Heap γ (lc_leak + hbStdoutCost init) (blk_leak + hbStdoutBlocks init) s_base ∗
       Tear ∗
       (muslErrnoAddr s_base ↦₃₂ e0) ∗
       StdVtableRo C.std.stdoutVtableAddr C.std.stdoutVtableShimAddr C.std.stdoutCleanupClosureAddr ∗
       (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
       HbAltstackInv4k C S altOpt ∗ HbAltstackMapped altOpt ∗
       stackAt sp_cl 4240 ∗ Extra ∗ G) post := by
  subst hsp
  obtain ⟨_, _, hal_g38, _⟩ := hbValid_stdout_align hv
  have hsp_sub_al : (sc.sp - 0x60#64 &&& 15#64 == 0#64) = true :=
    sc.spAligned_sub 0x60#64 hsp_align
  have hx0' : sc.readReg64 (.gpr 0#5) = dataPtr := hx0
  have hlr' : sc.readReg64 (.gpr 30#5) = ret_pc := hlr
  refine SepWP.weaken_pre (P' := stackAt sc.sp 4240 ∗ _) (by sep_frame) ?_
  rw [stackAt_split_cells sc.sp 4144 12 (by decide)]
  wp_conv_pre => simp (disch := decide) only [Nat.reduceMul, ProofLib.cells_sub_succ,
    Nat.reduceSub, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro w96
  apply SepWP.exists_left; intro w88
  apply SepWP.exists_left; intro w80
  apply SepWP.exists_left; intro w72
  iterate 3 (apply SepWP.exists_left; intro _)
  apply SepWP.exists_left; intro w40
  iterate 4 (apply SepWP.exists_left; intro _)
  refine SepWP.weaken_pre (P' := ((sc.sp - 40#64) ↦₆₄ w40) ∗ _) (by sep_frame) ?_
  rw [pointsTo64_split32_sub sc.sp 40#64 36#64,
      hbPointsTo32_split8_sub sc.sp 36#64 35#64 34#64 33#64]
  cases init
  · simp only [hbStdoutCost, hbStdoutBlocks, HbStdoutInv, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    refine hb_wp_step_proc C.std.stdoutOnceLockInitAddr hc.no_hooks hc.svc_eq (by
      hb_unpack_code_nosvc hbCleanupClosurePostChunks hc.cleanupPost
      wp_steps; wp_steps
      refine step_ldar32_words (C.std.cleanupClosureAddr + 0x38#64) _ 0
        (C.std.cleanupClosureAddr + 0x3c#64) hal_g38 (hnext := ?_)
      iterate 3 (wp_steps; hb_norm_jmp)
      exact hb_done_proc) fun m0 hp0 => ?_
    rw [hbStackAt_split (sc.sp - 0x60#64) 160 3984]
    refine SepWP.weaken_pre
      (P' := ((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 3#32) ∗
        (C.std.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8) ∗
        ((sc.sp - 36#64) ↦₈ 0#8) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.std.stdoutVtableAddr C.std.stdoutVtableShimAddr C.std.stdoutCleanupClosureAddr ∗
        stackAt (sc.sp - 0x60#64) 160 ∗ _)
      (by sep_frame) ?_
    refine hbStdoutOnceLockInitPost_wp (ret_pc := C.std.cleanupClosureAddr + 0x1c0#64)
      (sp0 := sc.sp - 0x60#64) (notInitPtr := sc.sp - 36#64) hc hv hs
      hb_wp_a (by simp [wp_norm, arm64_norm, hrun])
      hb_wp_a (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_sub_al)
      hb_wp_a hb_wp_a (by bv_omega)
      fun s1 hpc1 hrun1 hsp1 hcs1 hp1 => ?_
    have hx29_1 : s1.readReg64 (.gpr 29#5) = sc.sp - 64#64 := by
      have := hcs1.readReg64_x29
      simp only [wp_norm, arm64_norm, bv_lin_norm] at this
      rw [this]; bv_lin
    have hsp1_al : s1.spAligned = true := by
      simpa [State.spAligned, hsp1] using hsp_sub_al
    refine hbFocusFrame (((sc.sp - 36#64) ↦₈ 1#8)) (by sep_frame) fun F0 hF0 => ?_
    refine hb_wp_step_proc (C.std.cleanupClosureAddr + 0x184#64) hc.no_hooks hc.svc_eq (by
      hb_unpack_code_nosvc hbCleanupClosurePostChunks hc.cleanupPost
      wp_steps; hb_norm_jmp
      exact hb_done_proc) fun m2 hp2 => ?_
    subst hF0
    have hp_all : ProcessFieldsPreserved s_base _ :=
      hproc.trans (hp0.trans (hp1.trans hp2))
    have herr_all := (muslErrnoAddr_of_exitFields ⟨hp_all.1, hp_all.2.1, hp_all.2.2.1, hp_all.2.2.2.1⟩).symm
    refine SepWP.weaken_pre
      (P' := (M.Heap γ lc_leak blk_leak s_base ∗ Tear) ∗
        stackAt (sc.sp - 0x60#64) 4144 ∗ _)
      (by
        rw [herr_all, hbStackAt_split (sc.sp - 0x60#64) 160 3984 (n := 4144)]
        sep_frame) ?_
    refine SepWP.weaken_pre (sepConj_mono_left (htear s_base)) ?_
    wp_conv_pre => simp only [hv.needLocks_eq, hv.auxv_eq, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro R_heap_dead
    rw [hbStackAt_split (sc.sp - 0x60#64) 0x130 3840]
    refine SepWP.weaken_pre
      (P' := ((sc.sp - 64#64) ↦₆₄ sc.readReg64 (.gpr 29#5)) ∗
         ((sc.sp - 56#64) ↦₆₄ ret_pc) ∗
         ((sc.sp - 48#64) ↦₆₄ sc.readReg64 (.gpr 23#5)) ∗
         ((sc.sp - 32#64) ↦₆₄ sc.readReg64 (.gpr 22#5)) ∗
         ((sc.sp - 24#64) ↦₆₄ sc.readReg64 (.gpr 21#5)) ∗
         ((sc.sp - 16#64) ↦₆₄ sc.readReg64 (.gpr 20#5)) ∗
         ((sc.sp - 8#64) ↦₆₄ sc.readReg64 (.gpr 19#5)) ∗
         stackAt (sc.sp - 0x60#64) 0x130 ∗
         (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
         (dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗
         ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
         (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
         (muslErrnoAddr _ ↦₃₂ e0) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
         HbAltstackInv4k C S altOpt ∗ HbAltstackMapped altOpt ∗ _ ∗ G)
      (by sep_frame) ?_
    refine hbCleanupClosure_epilogue_wp hc hs hraw hnonull hbnd_req hsp_lo hsp_align
      hb_wp_a (by simp [wp_norm, arm64_norm, hrun1])
      (by simp [wp_norm, arm64_norm, hsp1])
      ?_
      (HbPostExitFields.trans ⟨hp0.1, hp0.2.1, hp0.2.2.1, hp0.2.2.2.1⟩
        (HbPostExitFields.trans ⟨hp1.1, hp1.2.1, hp1.2.2.1, hp1.2.2.2.1⟩
          ⟨hp2.1, hp2.2.1, hp2.2.2.1, hp2.2.2.2.1⟩))
      hnext
    rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with ⟨_, _, _, _, _, e24, e25, e26, e27, e28, _, ev⟩
    simp only [wp_norm, arm64_norm] at e24 e25 e26 e27 e28 ev
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Arm64.calleeSavedVRegs, wp_norm, arm64_norm, e24, e25, e26, e27, e28, ev]
  · simp only [hbStdoutCost, hbStdoutBlocks, ↓reduceIte]
    refine SepWP.weaken_pre (P' := HbStdoutInv C M γ true ∗ _) (by sep_frame) ?_
    wp_conv_pre => lhs; simp only [HbStdoutInv, ↓reduceIte]
    wp_conv_pre => simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_elim; intro bufPtr
    apply SepWP.pure_elim; rintro ⟨hbuf_nz, _, _⟩
    refine SepWP.weaken_pre (P' := HbThreadIdInv C s_base.tpidrEl0 ∗ _) (by sep_frame) ?_
    dsimp only [HbThreadIdInv]
    wp_conv_pre => simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_elim; intro tid
    apply SepWP.pure_elim; intro htid
    refine hb_wp_step_proc (C.std.cleanupClosureAddr + 0x3c#64) hc.no_hooks hc.svc_eq (by
      hb_unpack_code_nosvc hbCleanupClosurePostChunks hc.cleanupPost
      wp_steps; wp_steps
      refine step_ldar32_words (C.std.cleanupClosureAddr + 0x38#64) _ 0
        (C.std.cleanupClosureAddr + 0x3c#64) hal_g38 (hnext := ?_)
      exact hb_done_proc) fun m0 hp0 => ?_
    refine SepWP.weaken_pre (by sep_frame)
      (hbCleanupClosure_initTrue_wp (w96 := w96) (w88 := w88) (w80 := w80) (w72 := w72) (e0 := e0)
        (Dead := ((sc.sp - 40#64) ↦₃₂ BitVec.truncate 32 w40) ∗
          ((sc.sp - 35#64) ↦₈ BitVec.extractLsb' 8 8 (BitVec.extractLsb' 32 32 w40)) ∗
          ((sc.sp - 34#64) ↦₈ BitVec.extractLsb' 16 8 (BitVec.extractLsb' 32 32 w40)) ∗
          ((sc.sp - 33#64) ↦₈ BitVec.extractLsb' 24 8 (BitVec.extractLsb' 32 32 w40)) ∗
          ((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 0#32) ∗
          StdVtableRo C.std.stdoutVtableAddr C.std.stdoutVtableShimAddr C.std.stdoutCleanupClosureAddr ∗
          Extra)
        M γ hc hv hs htear hraw hnonull hbnd_req
        hsp_lo hsp_align hbuf_nz htid
        hb_wp_a (by simp [wp_norm, arm64_norm, hrun])
        hb_wp_a hb_wp_a hb_wp_a
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Arm64.calleeSavedVRegs, wp_norm, arm64_norm])
        (hproc.trans hp0)
        ⟨hp0.1, hp0.2.1, hp0.2.2.1, hp0.2.2.2.1⟩
        hnext)

end CaseStudies.Hashbrown.Proofs.StdCli

