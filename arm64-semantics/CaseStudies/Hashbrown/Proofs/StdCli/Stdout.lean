/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.StdoutInit
public meta import CaseStudies.Hashbrown.Proofs.StdCli.StdoutInit
public meta import ProofLib.SepLogic.Stack

/-!
# Unified `std::io::stdio::__print` Proofs

Symbolic `SepWP` and `subroutine_ok` specifications for `std::io::stdio::__print` and
`hashbrown_cli::print_bool` over `C : HbCliLayout`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAdr " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr false $rd ($t - $pc))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iLdr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W64 .X64 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iLdrbLo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W32 .B8 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.str .X64 $rt (.Offset $rn (pageLo12 $t)))
local macro "iBl " pc:term:arg t:term:arg : term => `(Instr.bl ($t - $pc))
local macro "iB " pc:term:arg t:term:arg : term => `(Instr.b ($t - $pc))


local macro "unpack_stdout_code " chunks:ident h:term : tactic => `(tactic| (
  have _hc := stdoutToStepFacts $h
  simp only [$chunks:ident, stdoutStepFacts, stdoutStepAcc, fetchAtAcc',
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

local macro "norm_jmp" : tactic =>
  `(tactic| conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel'])

local macro "unpack_cells " k:num : tactic => `(tactic| (
  try simp only [Nat.reduceMul]
  cells_unfold
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate $k (apply SepWP.exists_left; intro _)))

local macro "repack_cells" : tactic => `(tactic| (
  try simp only [Nat.reduceMul]
  cells_unfold
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  sep_entail))

attribute [local simp] cpuAux_writeReg64 cpuAux_writeReg32 cpuAux_writeReg
  cpuAux_setPState cpuAux_advancePC cpuAux_setPC cpuAux_setMem

local macro "unpack_cs " h:ident : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := $h)
local macro "close_cs" : tactic =>
  `(tactic| simp [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm, *])
local macro "wp_a" : term =>
  `(by simp [wp_norm, arm64_norm, bv_lin_norm, bv64_add_sub_cancel', *]; try bv_lin)


/-! ## Unified `std::io::stdio::__print` (`C.stdioPrintAddr`) -/

private theorem hbStdoutWriteFmt_tid_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) (k : HbPrintKind)
    {target_pc ret_wf sp_pr lockPtrPtrSlot ptrSlot arg0 arg1 valPtr tid : BitVec 64} {haveLse : BitVec 8}
    {s_wf : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C)
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (htid_nz : tid ≠ 0#64) (hsp_lo : k.isU64 = true → 0x280 ≤ sp_pr.toNat)
    (hpc : s_wf.pc = C.stdoutWriteFmtAddr) (hrun : s_wf.status = .Running)
    (hsp : s_wf.sp = sp_pr) (hsp_al : s_wf.spAligned = true) (hlr : s_wf.readReg64 Reg.lr = ret_wf)
    (hx0 : s_wf.readReg64 .x0 = lockPtrPtrSlot) (hx1 : s_wf.readReg64 .x1 = arg0) (hx2 : s_wf.readReg64 .x2 = arg1)
    (hnext : ∀ sf : State,
      sf.pc = ret_wf → sf.status = .Running → sf.sp = sp_pr →
      CalleeSavedPreserved s_wf sf → HbPrintIoPreserved s_wf sf → sf.readReg64 .x0 = 0#64 →
      sf.trace = s_wf.trace ++ TraceEvent.ofBytes .stdout k.outBytes →
      SepWP P target_pc sf
        ((HbStdoutInv C M γ true ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ k.inputRes C arg0 arg1 valPtr ∗
          (lockPtrPtrSlot ↦₆₄ ptrSlot) ∗ (ptrSlot ↦₆₄ C.std.stdoutGlobalAddr) ∗
          ((s_wf.tpidrEl0 + 0x58#64) ↦₆₄ tid) ∗ stackAt sp_pr 4288) ∗ F) post oom) :
    SepWP P target_pc s_wf
      (((HbStdoutInv C M γ true ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr)) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ k.inputRes C arg0 arg1 valPtr ∗
        (lockPtrPtrSlot ↦₆₄ ptrSlot) ∗ (ptrSlot ↦₆₄ C.std.stdoutGlobalAddr) ∗
        ((s_wf.tpidrEl0 + 0x58#64) ↦₆₄ tid) ∗ stackAt sp_pr 4288) ∗ F) post oom := by
  subst hsp
  have htid_beq : (tid == 0#64) = false := beq_false_of_ne htid_nz
  have hx0' : s_wf.readReg64 (.gpr 0#5) = lockPtrPtrSlot := hx0
  have hx1' : s_wf.readReg64 (.gpr 1#5) = arg0 := hx1
  have hx2' : s_wf.readReg64 (.gpr 2#5) = arg1 := hx2
  have hlr' : s_wf.readReg64 (.gpr 30#5) = ret_wf := hlr
  have hsp1_al : (s_wf.sp - 128#64) &&& 15#64 == 0#64 := s_wf.spAligned_sub 128#64 hsp_al
  rw [show (4288 : Nat) = 4160 + 8 * 16 from rfl, stackAt_split_cells s_wf.sp 4160 16 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro w0; apply SepWP.exists_left; intro w1
  apply SepWP.exists_left; intro w2; apply SepWP.exists_left; intro w3
  apply SepWP.exists_left; intro w4; apply SepWP.exists_left; intro w5
  iterate 10 (apply SepWP.exists_left; intro _)
  refine SepWP.weaken_pre
    (sepConj_mono_left (sepConj_mono_left (hbStdoutInv_true_unpack C M γ))) ?_
  simp only [sepExists_sepConj_left]; apply SepWP.exists_elim; intro bufPtr
  simp only [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hbuf_ne, hbuf_al, hbuf_fit⟩
  refine sepWP_cpu_seg (mid_pc := C.stdoutWriteFmtAddr + 0xb8#64) hext ?_
  have hchunk := (hc.withSvc noSyscalls).stdoutWriteFmt
  unpack_stdout_code hbStdoutWriteFmtChunks hchunk
  wp_steps 21
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    ⟨by simp [CpuAuxPreserved.refl s_wf], fun hpure1 => ?_⟩
  have hhi1 := HbStdoutWfHiSaved.of_pure hpure1 (HbStdoutWfHiSaved.refl s_wf)
  refine SepWP.weaken_pre (by dsimp only [hbStdoutWriteFmtSavedRegs]; sep_frame)
    (hbStdoutWriteFmt_from0xb8_wp M γ k (ret_wf := ret_wf) (sp_pr := s_wf.sp)
      (arg0 := arg0) (arg1 := arg1) (valPtr := valPtr) (tid := tid) (bufPtr := bufPtr)
      (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
      hc hcSys hfmt hcas4 hswp4 hMem hMemmove hv hsvc hext hbuf_ne hbuf_al hbuf_fit hsp_lo
      wp_a (by simp [wp_norm, arm64_norm, hrun])
      wp_a (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp1_al)
      wp_a wp_a wp_a wp_a hhi1
      fun sf hpcf hrunf hspf hcsf hiof hx0f htrf => ?_)
  have hio_all : HbPrintIoPreserved s_wf sf := (HbPrintIoPreserved.of_std hpure1.1).trans hiof
  have htr_all : sf.trace = s_wf.trace ++ TraceEvent.ofBytes .stdout k.outBytes := by
    rw [htrf, hpure1.1.2.1]
  refine SepWP.weaken_pre_frame (fun R hm => by sep_entail)
    (hnext sf hpcf hrunf hspf hcsf hio_all hx0f htr_all)

private theorem hbStdoutWriteFmt_anyTid_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) (k : HbPrintKind)
    {target_pc ret_wf sp_pr lockPtrPtrSlot ptrSlot arg0 arg1 valPtr tid0 ctr : BitVec 64} {haveLse : BitVec 8}
    {s_wf : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C)
    (hcas8 : subroutine_ok P C.std.cas8RelaxAddr (stdCas8Spec C.std.haveLseAtomicsAddr))
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hctr : tid0 = 0#64 → ctr.toNat + 1 < 2 ^ 64) (hsp_lo : k.isU64 = true → 0x280 ≤ sp_pr.toNat)
    (hpc : s_wf.pc = C.stdoutWriteFmtAddr) (hrun : s_wf.status = .Running)
    (hsp : s_wf.sp = sp_pr) (hsp_al : s_wf.spAligned = true) (hlr : s_wf.readReg64 Reg.lr = ret_wf)
    (hx0 : s_wf.readReg64 .x0 = lockPtrPtrSlot) (hx1 : s_wf.readReg64 .x1 = arg0) (hx2 : s_wf.readReg64 .x2 = arg1)
    (hnext : ∀ sf : State,
      sf.pc = ret_wf → sf.status = .Running → sf.sp = sp_pr →
      CalleeSavedPreserved s_wf sf → HbPrintIoPreserved s_wf sf → sf.readReg64 .x0 = 0#64 →
      sf.trace = s_wf.trace ++ TraceEvent.ofBytes .stdout k.outBytes →
      SepWP P target_pc sf
        ((HbStdoutInv C M γ true ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ k.inputRes C arg0 arg1 valPtr ∗
          (lockPtrPtrSlot ↦₆₄ ptrSlot) ∗ (ptrSlot ↦₆₄ C.std.stdoutGlobalAddr) ∗
          ((s_wf.tpidrEl0 + 0x58#64) ↦₆₄ (if tid0 = 0#64 then ctr + 1#64 else tid0)) ∗
          (C.std.threadIdCounterAddr ↦₆₄ (if tid0 = 0#64 then ctr + 1#64 else ctr)) ∗
          stackAt sp_pr 4288) ∗ F) post oom) :
    SepWP P target_pc s_wf
      (((HbStdoutInv C M γ true ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr)) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ k.inputRes C arg0 arg1 valPtr ∗
        (lockPtrPtrSlot ↦₆₄ ptrSlot) ∗ (ptrSlot ↦₆₄ C.std.stdoutGlobalAddr) ∗
        ((s_wf.tpidrEl0 + 0x58#64) ↦₆₄ tid0) ∗ (C.std.threadIdCounterAddr ↦₆₄ ctr) ∗
        stackAt sp_pr 4288) ∗ F) post oom := by
  by_cases htid : tid0 = 0#64
  · subst htid; subst hsp
    simp only [↓reduceIte] at hnext
    have hctr_lt : ctr.toNat + 1 < 2 ^ 64 := hctr rfl
    have hctr1_nz : ctr + 1#64 ≠ 0#64 := by
      intro heq; have hnat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
          show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt hctr_lt] at hnat
      exact absurd hnat (by omega)
    have hctr1_beq : (ctr + 1#64 == 0#64) = false := beq_false_of_ne hctr1_nz
    obtain ⟨_, _, _, hal_ctr⟩ := hbValid_stdout_align hv
    have hx0' : s_wf.readReg64 (.gpr 0#5) = lockPtrPtrSlot := hx0
    have hx1' : s_wf.readReg64 (.gpr 1#5) = arg0 := hx1
    have hx2' : s_wf.readReg64 (.gpr 2#5) = arg1 := hx2
    have hlr' : s_wf.readReg64 (.gpr 30#5) = ret_wf := hlr
    have hsp1_al : (s_wf.sp - 128#64) &&& 15#64 == 0#64 := s_wf.spAligned_sub 128#64 hsp_al
    rw [show (4288 : Nat) = 4160 + 8 * 16 from rfl, stackAt_split_cells s_wf.sp 4160 16 (by decide)]
    cells_unfold; simp only [sepExists_sepConj_left]
    apply SepWP.exists_left; intro w0; apply SepWP.exists_left; intro w1
    apply SepWP.exists_left; intro w2; apply SepWP.exists_left; intro w3
    apply SepWP.exists_left; intro w4; apply SepWP.exists_left; intro w5
    iterate 10 (apply SepWP.exists_left; intro _)
    refine SepWP.weaken_pre
      (sepConj_mono_left (sepConj_mono_left (hbStdoutInv_true_unpack C M γ))) ?_
    simp only [sepExists_sepConj_left]; apply SepWP.exists_elim; intro bufPtr
    simp only [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hbuf_ne, hbuf_al, hbuf_fit⟩
    refine sepWP_cpu_seg (mid_pc := C.std.cas8RelaxAddr) hext ?_
    have hchunk := (hc.withSvc noSyscalls).stdoutWriteFmt
    unpack_stdout_code hbStdoutWriteFmtChunks hchunk
    wp_steps 18; wp_steps 1; wp_steps 1; wp_steps 3; wp_steps 6; wp_steps 1; norm_jmp
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
      ⟨by simp [CpuAuxPreserved.refl s_wf], fun hpure1 => ?_⟩
    have hhi1 := HbStdoutWfHiSaved.of_pure hpure1 (HbStdoutWfHiSaved.refl s_wf)
    refine call_stdCas8 hcas8 (haveLse := haveLse) (ptr := C.std.threadIdCounterAddr)
      (v0 := ctr) (exp := ctr) (new := ctr + 1#64)
      (ret_pc := C.stdoutWriteFmtAddr + 0x9c#64) (F := ?_) (by sep_frame)
      (fun s2 hpc2 hrun2 hsp2 hcs2 hx0_2 hstd2 => ?_)
      (hsp_align := by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp1_al) (halign := hal_ctr)
    simp only [beq_self_eq_true, ↓reduceIte]
    have hx0_2' : s2.readReg64 (.gpr 0#5) = ctr := hx0_2
    have hx19_2 : s2.readReg64 (.gpr 19#5) = arg1 := by rw [← Reg.x19, hcs2.readReg64_x19]; simp [wp_norm, arm64_norm]
    have hx20_2 : s2.readReg64 (.gpr 20#5) = arg0 := by rw [← Reg.x20, hcs2.readReg64_x20]; simp [wp_norm, arm64_norm]
    have hx21_2 : s2.readReg64 (.gpr 21#5) = 0x58#64 := by rw [← Reg.x21, hcs2.readReg64_x21]; simp [wp_norm, arm64_norm]
    have hx23_2 : s2.readReg64 (.gpr 23#5) = ctr := by rw [← Reg.x23, hcs2.readReg64_x23]; simp [wp_norm, arm64_norm]
    have hx24_2 : s2.readReg64 (.gpr 24#5) = C.std.stdoutGlobalAddr := by rw [← Reg.x24, hcs2.readReg64_x24]; simp [wp_norm, arm64_norm]
    have hx25_2 : s2.readReg64 (.gpr 25#5) = ctr + 1#64 := by rw [← Reg.x25, hcs2.readReg64_x25]; simp [wp_norm, arm64_norm]
    have hx26_2 : s2.readReg64 (.gpr 26#5) = s_wf.tpidrEl0 := by rw [← Reg.x26, hcs2.readReg64_x26]; simp [wp_norm, arm64_norm]
    have hsp2_eq : s2.sp = s_wf.sp - 128#64 := by rw [hsp2]; simp [wp_norm, arm64_norm]
    have hhi2 : HbStdoutWfHiSaved s_wf s2 := hhi1.trans_cs hcs2
    refine sepWP_cpu_seg (mid_pc := C.stdoutWriteFmtAddr + 0xb8#64) hext ?_
    have hchunk2 := (hc.withSvc noSyscalls).stdoutWriteFmt
    unpack_stdout_code hbStdoutWriteFmtChunks hchunk2
    wp_steps 7
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2])
      ⟨by simp [CpuAuxPreserved.refl s2], fun hpure3 => ?_⟩
    have hhi3 := HbStdoutWfHiSaved.of_pure hpure3 hhi2
    refine SepWP.weaken_pre (by dsimp only [hbStdoutWriteFmtSavedRegs]; sep_frame)
      (hbStdoutWriteFmt_from0xb8_wp M γ k (ret_wf := ret_wf) (sp_pr := s_wf.sp)
        (arg0 := arg0) (arg1 := arg1) (valPtr := valPtr) (tid := ctr + 1#64) (bufPtr := bufPtr)
        (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
        hc hcSys hfmt hcas4 hswp4 hMem hMemmove hv hsvc hext hbuf_ne hbuf_al hbuf_fit hsp_lo
        wp_a (by simp [wp_norm, arm64_norm, hrun2])
        (by simp [wp_norm, arm64_norm, hsp2_eq])
        (by simpa only [State.spAligned, wp_norm, arm64_norm, hsp2_eq] using hsp1_al)
        wp_a wp_a wp_a wp_a hhi3
        fun sf hpcf hrunf hspf hcsf hiof hx0f htrf => ?_)
    have hstd03 : StdStatePreserved s_wf _ :=
      StdStatePreserved.trans hpure1.1 (StdStatePreserved.trans hstd2 hpure3.1)
    have hio_all : HbPrintIoPreserved s_wf sf := (HbPrintIoPreserved.of_std hstd03).trans hiof
    have htr_all : sf.trace = s_wf.trace ++ TraceEvent.ofBytes .stdout k.outBytes := by
      rw [htrf, hstd03.2.1]
    refine SepWP.weaken_pre_frame (fun R hm => by sep_entail)
      (hnext sf hpcf hrunf hspf hcsf hio_all hx0f htr_all)
  · simp only [htid, ↓reduceIte] at hnext
    refine SepWP.weaken_pre (by sep_frame)
      (hbStdoutWriteFmt_tid_wp M γ k (ret_wf := ret_wf) (sp_pr := sp_pr)
        (lockPtrPtrSlot := lockPtrPtrSlot) (ptrSlot := ptrSlot)
        (arg0 := arg0) (arg1 := arg1) (valPtr := valPtr) (tid := tid0)
        hc hcSys hfmt hcas4 hswp4 hMem hMemmove hv hsvc hext htid hsp_lo
        hpc hrun hsp hsp_al hlr hx0 hx1 hx2
        fun sf hpcf hrunf hspf hcsf hiof hx0f htrf => ?_)
    exact SepWP.weaken_pre_frame (fun R hm => by sep_entail)
      (hnext sf hpcf hrunf hspf hcsf hiof hx0f htrf)

private def HbPrintHiSaved (s0 s : State) : Prop :=
  s.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧ s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧ s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧ s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧ s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem HbPrintHiSaved.refl (s0 : State) : HbPrintHiSaved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem HbPrintHiSaved.trans_cs {s0 s1 s2 : State}
    (h1 : HbPrintHiSaved s0 s1) (hcs : CalleeSavedPreserved s1 s2) :
    HbPrintHiSaved s0 s2 := by
  rcases h1 with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hv⟩; unpack_cs hcs
  exact ⟨by simp_all, by simp_all, by simp_all, by simp_all, by simp_all,
    by simp_all, by simp_all, by simp_all, by simp_all⟩

private theorem HbPrintHiSaved.of_pure {s0 s sm : State} (_ : FmtPureStatePreserved s sm)
    (hhi : HbPrintHiSaved s0 s)
    (h21 : sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) := by simp [wp_norm, arm64_norm])
    (h22 : sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) := by simp [wp_norm, arm64_norm])
    (h23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by simp [wp_norm, arm64_norm])
    (h24 : sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := by simp [wp_norm, arm64_norm])
    (h25 : sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) := by simp [wp_norm, arm64_norm])
    (h26 : sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) := by simp [wp_norm, arm64_norm])
    (h27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp [wp_norm, arm64_norm])
    (h28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp [wp_norm, arm64_norm])
    (hv : calleeSavedVRegs sm = calleeSavedVRegs s := by simp [wp_norm, arm64_norm]) :
    HbPrintHiSaved s0 sm :=
  ⟨h21.trans hhi.1, h22.trans hhi.2.1, h23.trans hhi.2.2.1, h24.trans hhi.2.2.2.1,
   h25.trans hhi.2.2.2.2.1, h26.trans hhi.2.2.2.2.2.1, h27.trans hhi.2.2.2.2.2.2.1,
   h28.trans hhi.2.2.2.2.2.2.2.1, hv.trans hhi.2.2.2.2.2.2.2.2⟩

private def hbStdioPrintSavedRegs (s0 : State) (sp0 ret_pc : BitVec 64) : SepProp :=
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((sp0 - 24#64) ↦₆₄ ret_pc) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

private theorem hbStdioPrint_to0x44_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) (init : Bool)
    {target_pc ret_pc sp0 arg0 arg1 : BitVec 64} {lc blk : Nat} {e0 : BitVec 32} {haveLse : BitVec 8}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (honce : HbOnceCallCode P C)
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64) (hext : ∀ pc, P.externAt? pc = none)
    (hbudget : init = false → 1024 ≤ lim.maxReq ∧
      lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)
    (hpc : s0.pc = C.stdioPrintAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_al : s0.spAligned = true) (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = arg0) (hx1 : s0.readReg64 .x1 = arg1)
    (hnext : ∀ (s1 : State) (e1 : BitVec 32) (c0 c1 c2 c3 c4 c5 c6 c7 : BitVec 64),
      s1.pc = C.stdioPrintAddr + 0x44#64 → s1.status = .Running →
      s1.sp = sp0 - 96#64 → s1.spAligned = true →
      s1.readReg64 (.gpr 19#5) = arg1 → s1.readReg64 (.gpr 20#5) = arg0 → HbPrintHiSaved s0 s1 →
      s1.fs = s0.fs → s1.trace = s0.trace → s1.sigActions = s0.sigActions → s1.tpidrEl0 = s0.tpidrEl0 →
      SepWP P target_pc s1
        ((HbStdoutInv C M γ true ∗ (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
          (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
          M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) s1 ∗
          (muslErrnoAddr s1 ↦₃₂ e1) ∗
          ((sp0 - 96#64) ↦₆₄ c0) ∗ ((sp0 - 88#64) ↦₆₄ c1) ∗ ((sp0 - 80#64) ↦₆₄ c2) ∗ ((sp0 - 72#64) ↦₆₄ c3) ∗
          ((sp0 - 64#64) ↦₆₄ c4) ∗ ((sp0 - 56#64) ↦₆₄ c5) ∗ ((sp0 - 48#64) ↦₆₄ c6) ∗ ((sp0 - 40#64) ↦₆₄ c7) ∗
          hbStdioPrintSavedRegs s0 sp0 ret_pc ∗ stackAt (sp0 - 96#64) 4288) ∗ F) post oom) :
    SepWP P target_pc s0
      ((HbStdoutInv C M γ init ∗ (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ M.Heap γ lc blk s0 ∗
        (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp0 4384) ∗ F) post oom := by
  subst hsp
  let g := C.std.stdoutGlobalAddr
  obtain ⟨_, _, hal_g38, _⟩ := hbValid_stdout_align hv
  have hx0' : s0.readReg64 (.gpr 0#5) = arg0 := hx0
  have hx1' : s0.readReg64 (.gpr 1#5) = arg1 := hx1
  have hlr' : s0.readReg64 (.gpr 30#5) = ret_pc := hlr
  have hsp1_al : (s0.sp - 96#64) &&& 15#64 == 0#64 := s0.spAligned_sub 96#64 hsp_al
  rw [show (4384 : Nat) = 4288 + 8 * 12 from rfl, stackAt_split_cells s0.sp 4288 12 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro c0; apply SepWP.exists_left; intro c1
  apply SepWP.exists_left; intro c2; apply SepWP.exists_left; intro c3
  apply SepWP.exists_left; intro c4; apply SepWP.exists_left; intro c5
  apply SepWP.exists_left; intro c6; apply SepWP.exists_left; intro c7
  iterate 4 (apply SepWP.exists_left; intro _)
  refine sepWP_cpu_seg (mid_pc := C.printToBufferCaptureAddr) hext ?_
  have hchunk0 := (hc.withSvc noSyscalls).stdioPrint
  unpack_stdout_code hbStdioPrintChunks hchunk0
  wp_steps 6; wp_steps 1; wp_steps 3; wp_steps 1; norm_jmp
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    ⟨by simp [CpuAuxPreserved.refl s0], fun hpure0 => ?_⟩
  have hhi0 := HbPrintHiSaved.of_pure hpure0 (HbPrintHiSaved.refl s0)
  rw [show (4288 : Nat) = 96 + 4192 from rfl, stackAt_split 96 4192]
  refine SepWP.weaken_pre (by sep_frame)
    (hbPrintToBufferCapture_wp (ret_pc := C.stdioPrintAddr + 0x2c#64) (sp0 := s0.sp - 96#64)
      hc hext wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
      (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp1_al) wp_a
      fun s1 hpc1 hrun1 hsp1 hcs1 hpure1 hx0_1 => ?_)
  have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
  have hx19_1 : s1.readReg64 (.gpr 19#5) = arg1 := by
    rw [← Reg.x19, hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]
  have hx20_1 : s1.readReg64 (.gpr 20#5) = arg0 := by
    rw [← Reg.x20, hcs1.readReg64_x20]; simp [wp_norm, arm64_norm]
  have hsp1_eq : s1.sp = s0.sp - 96#64 := hsp1
  have hsp1_s1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_eq] using hsp1_al
  have hhi1 : HbPrintHiSaved s0 s1 := hhi0.trans_cs hcs1
  have hstd01 : StdStatePreserved s0 s1 := StdStatePreserved.trans hpure0.1 hpure1.1
  cases init with
  | true =>
    simp only [HbStdoutInv, ↓reduceIte, sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro bufPtr
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (stackAt (s0.sp - 96#64) 96), sepConj_left_comm (C.captureUsedAddr ↦₈ᵣ 0#8)]
    apply SepWP.pure_elim; rintro ⟨hbuf_ne, hbuf_al, hbuf_fit⟩
    refine sepWP_cpu_seg (mid_pc := C.stdioPrintAddr + 0x44#64) hext ?_
    have hchunk := (hc.withSvc noSyscalls).stdioPrint
    unpack_stdout_code hbStdioPrintChunks hchunk
    wp_steps 1; wp_steps 2
    refine step_ldar32_words (C.stdioPrintAddr + 0x38#64) _ 0 (C.stdioPrintAddr + 0x3c#64) hal_g38 (hnext := ?_)
    wp_steps 2
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1])
      ⟨by simp [CpuAuxPreserved.refl s1], fun hpure2 => ?_⟩
    have hhi2 := HbPrintHiSaved.of_pure hpure2 hhi1
    have hstd02 : StdStatePreserved s0 _ := StdStatePreserved.trans hstd01 hpure2.1
    have hcont := hnext _ e0 C.stdoutLabelStrAddr 6#64 c2 c3 c4 c5 c6 c7
      wp_a (by simp [wp_norm, arm64_norm, hrun1])
      (by simp [wp_norm, arm64_norm, hsp1_eq])
      (by simpa only [State.spAligned, wp_norm, arm64_norm, hsp1_eq] using hsp1_al)
      wp_a wp_a hhi2 hstd02.1 hstd02.2.1 hstd02.2.2.2.1 hstd02.2.2.1
    refine SepWP.weaken_pre_frame (fun R hm => ?_) hcont
    rw [heap_eq_of_std M hstd02] at hm
    dsimp only [HbStdoutInv, hbStdioPrintSavedRegs, muslErrnoAddr] at hm ⊢
    rw [← hstd02.2.2.1] at hm
    rw [show (4288 : Nat) = 96 + 4192 from rfl, stackAt_split 96 4192]
    simp only [↓reduceIte, sepExists_sepConj_left]
    refine Satisfies.mono (Entails.sepExists_right bufPtr ?_) hm
    rw [sepConj_assoc, pure_sepConj_of_true ⟨hbuf_ne, hbuf_al, hbuf_fit⟩]
    sep_entail
  | false =>
    have hinv_false : HbStdoutInv C M γ false =
        (((g + 0x38#64) ↦₃₂ 3#32) ∗ (g ↦ₛ List.replicate 56 0#8)) := by
      simp [HbStdoutInv, g]
    rw [hinv_false]
    refine sepWP_cpu_seg (mid_pc := C.stdoutInitAddr) hext ?_
    have hchunk := (hc.withSvc noSyscalls).stdioPrint
    unpack_stdout_code hbStdioPrintChunks hchunk
    wp_steps 1; wp_steps 2
    refine step_ldar32_words (C.stdioPrintAddr + 0x38#64) _ 0 (C.stdioPrintAddr + 0x3c#64) hal_g38 (hnext := ?_)
    wp_steps 1; wp_steps 1; norm_jmp
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1])
      ⟨by simp [CpuAuxPreserved.refl s1], fun hpure2 => ?_⟩
    have hhi2 := HbPrintHiSaved.of_pure hpure2 hhi1
    have hstd02 : StdStatePreserved s0 _ := StdStatePreserved.trans hstd01 hpure2.1
    refine SepWP.weaken_pre
      (P' := (HbStdoutInv C M γ false ∗
              (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
              StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
              M.Heap γ lc blk _ ∗ (muslErrnoAddr _ ↦₃₂ e0) ∗
              stackAt (s0.sp - 96#64) 4288) ∗ ?F_init)
      (by
        dsimp only [muslErrnoAddr]
        rw [hinv_false, heap_eq_of_std M hstd02, ← hstd02.2.2.1,
            show (4288 : Nat) = 96 + 4192 from rfl, stackAt_split 96 4192]
        sep_frame)
      (hbStdoutInit_wp M γ false (ret_pc := C.stdioPrintAddr + 0x7c#64) hc honce hcas4 hswp4
        hv hg_nz hext hbudget
        wp_a (by simp [wp_norm, arm64_norm, hrun1])
        (by simp [wp_norm, arm64_norm, hsp1_eq])
        (by simpa only [State.spAligned, wp_norm, arm64_norm, hsp1_eq] using hsp1_al)
        wp_a fun s3 e1 hpc3 hrun3 hsp3 hcs3 hfs3 htr3 hsig3 htp3 => ?_)
    have hx19_3 : s3.readReg64 (.gpr 19#5) = arg1 := by
      rw [← Reg.x19, hcs3.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_1]
    have hx20_3 : s3.readReg64 (.gpr 20#5) = arg0 := by
      rw [← Reg.x20, hcs3.readReg64_x20]; simp [wp_norm, arm64_norm, hx20_1]
    have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp1_al
    have hhi3 : HbPrintHiSaved s0 s3 := hhi2.trans_cs hcs3
    refine sepWP_cpu_seg (mid_pc := C.stdioPrintAddr + 0x44#64) hext ?_
    have hchunk2 := (hc.withSvc noSyscalls).stdioPrint
    unpack_stdout_code hbStdioPrintChunks hchunk2
    wp_steps 1; wp_steps 1
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun3])
      ⟨by simp [CpuAuxPreserved.refl s3], fun hpure4 => ?_⟩
    have hhi4 := HbPrintHiSaved.of_pure hpure4 hhi3
    have hcont := hnext _ e1 C.stdoutLabelStrAddr 6#64 c2 c3 c4 c5 c6 c7
      wp_a (by simp [wp_norm, arm64_norm, hrun3])
      (by simp [wp_norm, arm64_norm, hsp3])
      (by simp only [State.spAligned, beq_iff_eq, wp_norm, arm64_norm] at hsp3_al ⊢; exact hsp3_al)
      wp_a wp_a hhi4
      (hpure4.1.1.trans (hfs3.trans hstd02.1))
      (hpure4.1.2.1.trans (htr3.trans hstd02.2.1))
      (hpure4.1.2.2.2.1.trans (hsig3.trans hstd02.2.2.2.1))
      (hpure4.1.2.2.1.trans (htp3.trans hstd02.2.2.1))
    refine SepWP.weaken_pre_frame (fun R hm => ?_) hcont
    rw [heap_eq_of_std M hpure4.1] at hm
    dsimp only [hbStdioPrintSavedRegs, muslErrnoAddr] at hm ⊢
    rw [← hpure4.1.2.2.1] at hm
    simp only [Bool.false_eq_true, ↓reduceIte] at hm ⊢
    sep_entail

private theorem hbStdioPrint_kind_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) (k : HbPrintKind) (init : Bool)
    {target_pc ret_pc sp0 arg0 arg1 valPtr tid : BitVec 64} {lc blk : Nat} {e0 : BitVec 32} {haveLse : BitVec 8}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C) (honce : HbOnceCallCode P C)
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64) (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (htid_nz : tid ≠ 0#64) (hsp_lo : k.isU64 = true → 0x2e0 ≤ sp0.toNat)
    (hbudget : init = false → 1024 ≤ lim.maxReq ∧ lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)
    (hpc : s0.pc = C.stdioPrintAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_al : s0.spAligned = true) (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = arg0) (hx1 : s0.readReg64 .x1 = arg1)
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs → sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout k.outBytes →
      sf.sigActions = s0.sigActions → sf.tpidrEl0 = s0.tpidrEl0 →
      SepWP P target_pc sf
        ((HbStdoutInv C M γ true ∗ k.inputRes C arg0 arg1 valPtr ∗ (C.captureUsedAddr ↦₈ᵣ 0#8) ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
          (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ ((s0.tpidrEl0 + 0x58#64) ↦₆₄ tid) ∗
          M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp0 4384) ∗ F) post oom) :
    SepWP P target_pc s0
      ((HbStdoutInv C M γ init ∗ k.inputRes C arg0 arg1 valPtr ∗ (C.captureUsedAddr ↦₈ᵣ 0#8) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ ((s0.tpidrEl0 + 0x58#64) ↦₆₄ tid) ∗
        M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp0 4384) ∗ F) post oom := by
  subst hsp
  have hsp_pr_lo : k.isU64 = true → 0x280 ≤ (s0.sp - 96#64).toNat := by
    intro hk; have := s0.sp.isLt; have := hsp_lo hk
    rw [BitVec.toNat_sub_of_le (show (96#64 : BitVec 64) ≤ s0.sp by rw [BitVec.le_def]; change 96 ≤ s0.sp.toNat; omega)]
    change 640 ≤ s0.sp.toNat - 96; omega
  refine SepWP.weaken_pre (by sep_frame)
    (hbStdioPrint_to0x44_wp M γ init hc honce hcas4 hswp4 hv hg_nz hext hbudget hpc hrun rfl hsp_al hlr hx0 hx1
      fun s1 e1 c0 c1 c2 c3 c4 c5 c6 c7 hpc1 hrun1 hsp1 hsp1_al hx19_1 hx20_1 hhi1 hfs1 htr1 hsig1 htp1 => ?_)
  refine sepWP_cpu_seg (mid_pc := C.stdoutWriteFmtAddr) hext ?_
  have hchunk := (hc.withSvc noSyscalls).stdioPrint; unpack_stdout_code hbStdioPrintChunks hchunk
  wp_steps 1; wp_steps 6; wp_steps 1; norm_jmp
  conv => repeat rw [bv64_add_sub_cancel']
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1]) ⟨by simp [CpuAuxPreserved.refl s1], fun hpure2 => ?_⟩
  have hhi2 := HbPrintHiSaved.of_pure hpure2 hhi1; have htp2 := hpure2.1.2.2.1.trans htp1
  refine SepWP.weaken_pre (by rw [← htp2]; sep_frame)
    (hbStdoutWriteFmt_tid_wp M γ k (ret_wf := C.stdioPrintAddr + 0x64#64) (sp_pr := s0.sp - 96#64)
      (lockPtrPtrSlot := s0.sp - 64#64) (ptrSlot := s0.sp - 80#64) (arg0 := arg0) (arg1 := arg1) (valPtr := valPtr) (tid := tid)
      hc hcSys hfmt hcas4 hswp4 hMem hMemmove hv hsvc hext htid_nz hsp_pr_lo
      wp_a (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1])
      (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp1_al) wp_a wp_a wp_a wp_a
      fun s3 hpc3 hrun3 hsp3 hcs3 hio3 hx0_3 htr3 => ?_)
  have hx0_3' : s3.readReg64 (.gpr 0#5) = 0#64 := hx0_3; have hhi3 : HbPrintHiSaved s0 s3 := hhi2.trans_cs hcs3
  dsimp only [hbStdioPrintSavedRegs]; refine sepWP_cpu_seg (mid_pc := ret_pc) hext ?_
  have hchunk2 := (hc.withSvc noSyscalls).stdioPrint; unpack_stdout_code hbStdioPrintChunks hchunk2
  wp_steps 5
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun3]) ⟨by simp [CpuAuxPreserved.refl s3], fun hpure4 => ?_⟩
  have hio1f : HbPrintIoPreserved s1 _ :=
    (HbPrintIoPreserved.of_std hpure2.1).trans (hio3.trans (HbPrintIoPreserved.of_std hpure4.1))
  have hcont := hnext _ e1 wp_a (by simp [wp_norm, arm64_norm, hrun3]) (by simp [wp_norm, arm64_norm])
    (by rcases hhi3 with ⟨_, _, _, _, _, _, _, _, _⟩; close_cs)
    (hio1f.1.trans hfs1) (by rw [hpure4.1.2.1, htr3, hpure2.1.2.1, htr1]) (hio1f.2.1.trans hsig1) (hio1f.2.2.1.trans htp1)
  refine SepWP.weaken_pre_frame (fun R hm => ?_) hcont
  rw [heap_eq_of_printIo M hio1f, htp2] at hm; dsimp only [muslErrnoAddr] at hm ⊢; rw [← hio1f.2.2.1] at hm
  rw [show (4384 : Nat) = 4288 + 8 * 12 from rfl, stackAt_split_cells s0.sp 4288 12 (by decide)]; repack_cells

theorem hbStdioPrint_getResult_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) (optVal : Option (BitVec 64)) (init : Bool)
    {target_pc ret_pc sp0 arg0 arg1 valPtr tid : BitVec 64} {lc blk : Nat} {e0 : BitVec 32} {haveLse : BitVec 8}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C) (honce : HbOnceCallCode P C)
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64) (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (htid_nz : tid ≠ 0#64) (hsp_lo : optVal.isSome = true → 0x2e0 ≤ sp0.toNat)
    (hbudget : init = false → 1024 ≤ lim.maxReq ∧ lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)
    (hpc : s0.pc = C.stdioPrintAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_al : s0.spAligned = true) (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = arg0) (hx1 : s0.readReg64 .x1 = arg1)
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs → sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatGetResult optVal) →
      sf.sigActions = s0.sigActions → sf.tpidrEl0 = s0.tpidrEl0 →
      SepWP P target_pc sf
        ((HbStdoutInv C M γ true ∗ hbStdioPrintInputRes C optVal arg0 arg1 valPtr ∗
          (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
          (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ ((s0.tpidrEl0 + 0x58#64) ↦₆₄ tid) ∗
          M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp0 4384) ∗ F) post oom) :
    SepWP P target_pc s0
      ((HbStdoutInv C M γ init ∗ hbStdioPrintInputRes C optVal arg0 arg1 valPtr ∗
        (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ ((s0.tpidrEl0 + 0x58#64) ↦₆₄ tid) ∗
        M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp0 4384) ∗ F) post oom := by
  let k : HbPrintKind := match optVal with | none => .constNl noneNlBytes | some v => .u64Nl v
  have hk_out : k.outBytes = formatGetResult optVal := by cases optVal <;> rfl
  have hk_u64 : k.isU64 = optVal.isSome := by cases optVal <;> rfl
  cases optVal with
  | none =>
    dsimp only [hbStdioPrintInputRes]; simp only [sepConj_assoc]
    rw [sepConj_left_comm (HbStdoutInv C M γ init)]; apply SepWP.pure_elim; rintro ⟨rfl, rfl⟩
    refine SepWP.weaken_pre
      (P' := (HbStdoutInv C M γ init ∗ k.inputRes C C.noneNlAddr 0x0b#64 valPtr ∗
        (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ ((s0.tpidrEl0 + 0x58#64) ↦₆₄ tid) ∗
        M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp0 4384) ∗ F)
      (by dsimp only [k, HbPrintKind.inputRes]
          rw [pure_sepConj_of_true ⟨by decide, by decide, by decide, hv.noneNl_noWrap, by decide, by decide⟩]; sep_entail)
      (hbStdioPrint_kind_wp M γ k init hc hcSys hfmt honce hcas4 hswp4 hMem hMemmove hv hg_nz hsvc hext htid_nz
        (fun h => hsp_lo (hk_u64 ▸ h)) hbudget hpc hrun hsp hsp_al hlr hx0 hx1
        fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf => ?_)
    refine SepWP.weaken_pre_frame (fun R hm => ?_) (hnext sf e1 hpcf hrunf hspf hcsf hfsf (hk_out ▸ htrf) hsigf htpf)
    dsimp only [k, HbPrintKind.inputRes, hbStdioPrintInputRes] at hm ⊢
    rw [pure_sepConj_of_true ⟨by decide, by decide, by decide, hv.noneNl_noWrap, by decide, by decide⟩] at hm
    rw [pure_sepConj_of_true ⟨rfl, rfl⟩]; sep_entail
  | some v =>
    exact hbStdioPrint_kind_wp M γ k init hc hcSys hfmt honce hcas4 hswp4 hMem hMemmove hv hg_nz hsvc hext htid_nz
      (fun h => hsp_lo (hk_u64 ▸ h)) hbudget hpc hrun hsp hsp_al hlr hx0 hx1
      fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf =>
        hnext sf e1 hpcf hrunf hspf hcsf hfsf (hk_out ▸ htrf) hsigf htpf

def hbStdioPrintGetResultSpec {P : Program} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) :
    Spec (Option (BitVec 64) × Bool × Nat × Nat × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 32 × BitVec 8) where
  pre := fun (optVal, init, lc, blk, arg0, arg1, valPtr, tid, e0, haveLse) s0 =>
    ⌜s0.readReg64 .x0 = arg0 ∧ s0.readReg64 .x1 = arg1 ∧ tid ≠ 0#64 ∧ (optVal.isSome = true → 0x2e0 ≤ s0.sp.toNat) ∧
      (init = false → 1024 ≤ lim.maxReq ∧ lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)⌝ ∗
    HbStdoutInv C M γ init ∗ hbStdioPrintInputRes C optVal arg0 arg1 valPtr ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ ((s0.tpidrEl0 + 0x58#64) ↦₆₄ tid) ∗
    M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp 4384
  post := fun (optVal, init, lc, blk, arg0, arg1, valPtr, tid, _, haveLse) s0 sf =>
    ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatGetResult optVal) ∧
      sf.sigActions = s0.sigActions ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
    HbStdoutInv C M γ true ∗ hbStdioPrintInputRes C optVal arg0 arg1 valPtr ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ ((s0.tpidrEl0 + 0x58#64) ↦₆₄ tid) ∗
    M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
    (∃∗ e1 : BitVec 32, muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt s0.sp 4384

theorem hbStdioPrint_getResult_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C) (honce : HbOnceCallCode P C)
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64) (hsvc : P.svc = Syscall.standard)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.stdioPrintAddr (hbStdioPrintGetResultSpec C M γ) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨optVal, init, lc, blk, arg0, arg1, valPtr, tid, e0, haveLse⟩ R s0 hpc hrun hpre hsp
  dsimp only [hbStdioPrintGetResultSpec] at hpre ⊢; simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, htid_nz, hsp_lo, hbudget⟩, hmem⟩
  refine ⟨(HbStdoutInv C M γ init ∗ hbStdioPrintInputRes C optVal arg0 arg1 valPtr ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ ((s0.tpidrEl0 + 0x58#64) ↦₆₄ tid) ∗
    M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp 4384) ∗ emp,
    by simpa [sepConj_emp, sepConj_assoc] using hmem, ?_⟩
  refine hbStdioPrint_getResult_wp M γ optVal init hc hcSys hfmt honce hcas4 hswp4
    hMem hMemmove hv hg_nz hsvc hext htid_nz hsp_lo hbudget hpc hrun rfl hsp rfl hx0 hx1
    fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf => ?_
  refine SepWP.done hpcf hrunf ⟨fun hm => ?_, hspf, hcsf⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hfsf, htrf, hsigf, htpf⟩, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_emp, sepConj_assoc] at hm ⊢
  exact Satisfies.mono (Entails.sepExists_right e1 (by sep_entail)) hm

theorem hbStdioPrint_kind_anyTid_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) (k : HbPrintKind) (init : Bool)
    {target_pc ret_pc sp0 arg0 arg1 valPtr tid0 ctr : BitVec 64} {lc blk : Nat} {e0 : BitVec 32} {haveLse : BitVec 8}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C) (honce : HbOnceCallCode P C)
    (hcas8 : subroutine_ok P C.std.cas8RelaxAddr (stdCas8Spec C.std.haveLseAtomicsAddr))
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64) (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hctr : tid0 = 0#64 → ctr.toNat + 1 < 2 ^ 64) (hsp_lo : k.isU64 = true → 0x2e0 ≤ sp0.toNat)
    (hbudget : init = false → 1024 ≤ lim.maxReq ∧ lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)
    (hpc : s0.pc = C.stdioPrintAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_al : s0.spAligned = true) (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = arg0) (hx1 : s0.readReg64 .x1 = arg1)
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs → sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout k.outBytes →
      sf.sigActions = s0.sigActions → sf.tpidrEl0 = s0.tpidrEl0 →
      SepWP P target_pc sf
        ((HbStdoutInv C M γ true ∗ k.inputRes C arg0 arg1 valPtr ∗ (C.captureUsedAddr ↦₈ᵣ 0#8) ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
          (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
          ((s0.tpidrEl0 + 0x58#64) ↦₆₄ (if tid0 = 0#64 then ctr + 1#64 else tid0)) ∗
          (C.std.threadIdCounterAddr ↦₆₄ (if tid0 = 0#64 then ctr + 1#64 else ctr)) ∗
          M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp0 4384) ∗ F) post oom) :
    SepWP P target_pc s0
      ((HbStdoutInv C M γ init ∗ k.inputRes C arg0 arg1 valPtr ∗ (C.captureUsedAddr ↦₈ᵣ 0#8) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ ((s0.tpidrEl0 + 0x58#64) ↦₆₄ tid0) ∗ (C.std.threadIdCounterAddr ↦₆₄ ctr) ∗
        M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp0 4384) ∗ F) post oom := by
  subst hsp
  have hsp_pr_lo : k.isU64 = true → 0x280 ≤ (s0.sp - 96#64).toNat := by
    intro hk; have := s0.sp.isLt; have := hsp_lo hk
    rw [BitVec.toNat_sub_of_le (show (96#64 : BitVec 64) ≤ s0.sp by rw [BitVec.le_def]; change 96 ≤ s0.sp.toNat; omega)]
    change 640 ≤ s0.sp.toNat - 96; omega
  refine SepWP.weaken_pre (by sep_frame)
    (hbStdioPrint_to0x44_wp M γ init hc honce hcas4 hswp4 hv hg_nz hext hbudget hpc hrun rfl hsp_al hlr hx0 hx1
      fun s1 e1 c0 c1 c2 c3 c4 c5 c6 c7 hpc1 hrun1 hsp1 hsp1_al hx19_1 hx20_1 hhi1 hfs1 htr1 hsig1 htp1 => ?_)
  refine sepWP_cpu_seg (mid_pc := C.stdoutWriteFmtAddr) hext ?_
  have hchunk := (hc.withSvc noSyscalls).stdioPrint; unpack_stdout_code hbStdioPrintChunks hchunk
  wp_steps 1; wp_steps 6; wp_steps 1; norm_jmp
  conv => repeat rw [bv64_add_sub_cancel']
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1]) ⟨by simp [CpuAuxPreserved.refl s1], fun hpure2 => ?_⟩
  have hhi2 := HbPrintHiSaved.of_pure hpure2 hhi1; have htp2 := hpure2.1.2.2.1.trans htp1
  refine SepWP.weaken_pre (by rw [← htp2]; sep_frame)
    (hbStdoutWriteFmt_anyTid_wp M γ k (ret_wf := C.stdioPrintAddr + 0x64#64) (sp_pr := s0.sp - 96#64)
      (lockPtrPtrSlot := s0.sp - 64#64) (ptrSlot := s0.sp - 80#64) (arg0 := arg0) (arg1 := arg1) (valPtr := valPtr) (tid0 := tid0) (ctr := ctr)
      hc hcSys hfmt hcas8 hcas4 hswp4 hMem hMemmove hv hsvc hext hctr hsp_pr_lo
      wp_a (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1])
      (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp1_al) wp_a wp_a wp_a wp_a
      fun s3 hpc3 hrun3 hsp3 hcs3 hio3 hx0_3 htr3 => ?_)
  have hx0_3' : s3.readReg64 (.gpr 0#5) = 0#64 := hx0_3; have hhi3 : HbPrintHiSaved s0 s3 := hhi2.trans_cs hcs3
  dsimp only [hbStdioPrintSavedRegs]; refine sepWP_cpu_seg (mid_pc := ret_pc) hext ?_
  have hchunk2 := (hc.withSvc noSyscalls).stdioPrint; unpack_stdout_code hbStdioPrintChunks hchunk2
  wp_steps 5
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun3]) ⟨by simp [CpuAuxPreserved.refl s3], fun hpure4 => ?_⟩
  have hio1f : HbPrintIoPreserved s1 _ :=
    (HbPrintIoPreserved.of_std hpure2.1).trans (hio3.trans (HbPrintIoPreserved.of_std hpure4.1))
  have hcont := hnext _ e1 wp_a (by simp [wp_norm, arm64_norm, hrun3]) (by simp [wp_norm, arm64_norm])
    (by rcases hhi3 with ⟨_, _, _, _, _, _, _, _, _⟩; close_cs)
    (hio1f.1.trans hfs1) (by rw [hpure4.1.2.1, htr3, hpure2.1.2.1, htr1]) (hio1f.2.1.trans hsig1) (hio1f.2.2.1.trans htp1)
  refine SepWP.weaken_pre_frame (fun R hm => ?_) hcont
  rw [heap_eq_of_printIo M hio1f, htp2] at hm; dsimp only [muslErrnoAddr] at hm ⊢; rw [← hio1f.2.2.1] at hm
  rw [show (4384 : Nat) = 4288 + 8 * 12 from rfl, stackAt_split_cells s0.sp 4288 12 (by decide)]; repack_cells

theorem hbStdioPrint_getResult_anyTid_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) (optVal : Option (BitVec 64)) (init : Bool)
    {target_pc ret_pc sp0 arg0 arg1 valPtr tid0 ctr : BitVec 64} {lc blk : Nat} {e0 : BitVec 32} {haveLse : BitVec 8}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C) (honce : HbOnceCallCode P C)
    (hcas8 : subroutine_ok P C.std.cas8RelaxAddr (stdCas8Spec C.std.haveLseAtomicsAddr))
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64) (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hctr : tid0 = 0#64 → ctr.toNat + 1 < 2 ^ 64) (hsp_lo : optVal.isSome = true → 0x2e0 ≤ sp0.toNat)
    (hbudget : init = false → 1024 ≤ lim.maxReq ∧ lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)
    (hpc : s0.pc = C.stdioPrintAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_al : s0.spAligned = true) (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = arg0) (hx1 : s0.readReg64 .x1 = arg1)
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs → sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatGetResult optVal) →
      sf.sigActions = s0.sigActions → sf.tpidrEl0 = s0.tpidrEl0 →
      SepWP P target_pc sf
        ((HbStdoutInv C M γ true ∗ hbStdioPrintInputRes C optVal arg0 arg1 valPtr ∗
          (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
          (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
          ((s0.tpidrEl0 + 0x58#64) ↦₆₄ (if tid0 = 0#64 then ctr + 1#64 else tid0)) ∗
          (C.std.threadIdCounterAddr ↦₆₄ (if tid0 = 0#64 then ctr + 1#64 else ctr)) ∗
          M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp0 4384) ∗ F) post oom) :
    SepWP P target_pc s0
      ((HbStdoutInv C M γ init ∗ hbStdioPrintInputRes C optVal arg0 arg1 valPtr ∗
        (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ ((s0.tpidrEl0 + 0x58#64) ↦₆₄ tid0) ∗ (C.std.threadIdCounterAddr ↦₆₄ ctr) ∗
        M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp0 4384) ∗ F) post oom := by
  let k : HbPrintKind := match optVal with | none => .constNl noneNlBytes | some v => .u64Nl v
  have hk_out : k.outBytes = formatGetResult optVal := by cases optVal <;> rfl
  have hk_u64 : k.isU64 = optVal.isSome := by cases optVal <;> rfl
  cases optVal with
  | none =>
    dsimp only [hbStdioPrintInputRes]; simp only [sepConj_assoc]
    rw [sepConj_left_comm (HbStdoutInv C M γ init)]; apply SepWP.pure_elim; rintro ⟨rfl, rfl⟩
    refine SepWP.weaken_pre
      (P' := (HbStdoutInv C M γ init ∗ k.inputRes C C.noneNlAddr 0x0b#64 valPtr ∗
        (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ ((s0.tpidrEl0 + 0x58#64) ↦₆₄ tid0) ∗ (C.std.threadIdCounterAddr ↦₆₄ ctr) ∗
        M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp0 4384) ∗ F)
      (by dsimp only [k, HbPrintKind.inputRes]
          rw [pure_sepConj_of_true ⟨by decide, by decide, by decide, hv.noneNl_noWrap, by decide, by decide⟩]; sep_entail)
      (hbStdioPrint_kind_anyTid_wp M γ k init hc hcSys hfmt honce hcas8 hcas4 hswp4 hMem hMemmove hv hg_nz hsvc hext hctr
        (fun h => hsp_lo (hk_u64 ▸ h)) hbudget hpc hrun hsp hsp_al hlr hx0 hx1
        fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf => ?_)
    refine SepWP.weaken_pre_frame (fun R hm => ?_) (hnext sf e1 hpcf hrunf hspf hcsf hfsf (hk_out ▸ htrf) hsigf htpf)
    dsimp only [k, HbPrintKind.inputRes, hbStdioPrintInputRes] at hm ⊢
    rw [pure_sepConj_of_true ⟨by decide, by decide, by decide, hv.noneNl_noWrap, by decide, by decide⟩] at hm
    rw [pure_sepConj_of_true ⟨rfl, rfl⟩]; sep_entail
  | some v =>
    exact hbStdioPrint_kind_anyTid_wp M γ k init hc hcSys hfmt honce hcas8 hcas4 hswp4 hMem hMemmove hv hg_nz hsvc hext hctr
      (fun h => hsp_lo (hk_u64 ▸ h)) hbudget hpc hrun hsp hsp_al hlr hx0 hx1
      fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf =>
        hnext sf e1 hpcf hrunf hspf hcsf hfsf (hk_out ▸ htrf) hsigf htpf

def hbStdioPrintGetResultAnyTidSpec {P : Program} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) :
    Spec (Option (BitVec 64) × Bool × Nat × Nat × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 32 × BitVec 8) where
  pre := fun (optVal, init, lc, blk, arg0, arg1, valPtr, tid0, ctr, e0, haveLse) s0 =>
    ⌜s0.readReg64 .x0 = arg0 ∧ s0.readReg64 .x1 = arg1 ∧ (tid0 = 0#64 → ctr.toNat + 1 < 2 ^ 64) ∧
      (optVal.isSome = true → 0x2e0 ≤ s0.sp.toNat) ∧
      (init = false → 1024 ≤ lim.maxReq ∧ lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)⌝ ∗
    HbStdoutInv C M γ init ∗ hbStdioPrintInputRes C optVal arg0 arg1 valPtr ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ ((s0.tpidrEl0 + 0x58#64) ↦₆₄ tid0) ∗ (C.std.threadIdCounterAddr ↦₆₄ ctr) ∗
    M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp 4384
  post := fun (optVal, init, lc, blk, arg0, arg1, valPtr, tid0, ctr, _, haveLse) s0 sf =>
    ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatGetResult optVal) ∧
      sf.sigActions = s0.sigActions ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
    HbStdoutInv C M γ true ∗ hbStdioPrintInputRes C optVal arg0 arg1 valPtr ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
    ((s0.tpidrEl0 + 0x58#64) ↦₆₄ (if tid0 = 0#64 then ctr + 1#64 else tid0)) ∗
    (C.std.threadIdCounterAddr ↦₆₄ (if tid0 = 0#64 then ctr + 1#64 else ctr)) ∗
    M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
    (∃∗ e1 : BitVec 32, muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt s0.sp 4384

theorem hbStdioPrint_getResult_anyTid_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C) (honce : HbOnceCallCode P C)
    (hcas8 : subroutine_ok P C.std.cas8RelaxAddr (stdCas8Spec C.std.haveLseAtomicsAddr))
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64) (hsvc : P.svc = Syscall.standard)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.stdioPrintAddr (hbStdioPrintGetResultAnyTidSpec C M γ) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨optVal, init, lc, blk, arg0, arg1, valPtr, tid0, ctr, e0, haveLse⟩ R s0 hpc hrun hpre hsp
  dsimp only [hbStdioPrintGetResultAnyTidSpec] at hpre ⊢; simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hctr, hsp_lo, hbudget⟩, hmem⟩
  refine ⟨(HbStdoutInv C M γ init ∗ hbStdioPrintInputRes C optVal arg0 arg1 valPtr ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ ((s0.tpidrEl0 + 0x58#64) ↦₆₄ tid0) ∗
    (C.std.threadIdCounterAddr ↦₆₄ ctr) ∗ M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp 4384) ∗ emp,
    by simpa [sepConj_emp, sepConj_assoc] using hmem, ?_⟩
  refine hbStdioPrint_getResult_anyTid_wp M γ optVal init hc hcSys hfmt honce
    hcas8 hcas4 hswp4 hMem hMemmove hv hg_nz hsvc hext hctr hsp_lo hbudget hpc hrun rfl hsp rfl hx0 hx1
    fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf => ?_
  refine SepWP.done hpcf hrunf ⟨fun hm => ?_, hspf, hcsf⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hfsf, htrf, hsigf, htpf⟩, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_emp, sepConj_assoc] at hm ⊢
  exact Satisfies.mono (Entails.sepExists_right e1 (by sep_entail)) hm

theorem hbStdioPrint_kind_tidInv_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) (k : HbPrintKind) (init : Bool)
    {target_pc ret_pc sp0 arg0 arg1 valPtr : BitVec 64} {lc blk : Nat} {e0 : BitVec 32} {haveLse : BitVec 8}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C) (honce : HbOnceCallCode P C)
    (hcas8 : subroutine_ok P C.std.cas8RelaxAddr (stdCas8Spec C.std.haveLseAtomicsAddr))
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64) (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hsp_lo : k.isU64 = true → 0x2e0 ≤ sp0.toNat)
    (hbudget : init = false → 1024 ≤ lim.maxReq ∧ lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)
    (hpc : s0.pc = C.stdioPrintAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_al : s0.spAligned = true) (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = arg0) (hx1 : s0.readReg64 .x1 = arg1)
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs → sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout k.outBytes →
      sf.sigActions = s0.sigActions → sf.tpidrEl0 = s0.tpidrEl0 →
      SepWP P target_pc sf
        ((HbStdoutInv C M γ true ∗ k.inputRes C arg0 arg1 valPtr ∗ (C.captureUsedAddr ↦₈ᵣ 0#8) ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
          (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C sf.tpidrEl0 ∗
          M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp0 4384) ∗ F) post oom) :
    SepWP P target_pc s0
      ((HbStdoutInv C M γ init ∗ k.inputRes C arg0 arg1 valPtr ∗ (C.captureUsedAddr ↦₈ᵣ 0#8) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C s0.tpidrEl0 ∗
        M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp0 4384) ∗ F) post oom := by
  dsimp only [HbThreadIdInv]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro tid; simp only [sepConj_assoc]
  rw [sepConj_left_comm (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr),
      sepConj_left_comm (StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr),
      sepConj_left_comm (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse), sepConj_left_comm (C.captureUsedAddr ↦₈ᵣ 0#8),
      sepConj_left_comm (k.inputRes C arg0 arg1 valPtr), sepConj_left_comm (HbStdoutInv C M γ init)]
  apply SepWP.pure_elim; intro htid
  have hctr : tid = 0#64 → tid.toNat + 1 < 2 ^ 64 := by rintro rfl; decide
  have htid1 : (if tid = 0#64 then tid + 1#64 else tid) = 1#64 := by rcases htid with rfl | rfl <;> rfl
  refine SepWP.weaken_pre (by sep_frame)
    (hbStdioPrint_kind_anyTid_wp M γ k init (valPtr := valPtr) (tid0 := tid) (ctr := tid)
      hc hcSys hfmt honce hcas8 hcas4 hswp4 hMem hMemmove hv hg_nz hsvc hext hctr hsp_lo hbudget
      hpc hrun hsp hsp_al hlr hx0 hx1
      fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf => ?_)
  refine SepWP.weaken_pre_frame (fun R hm => ?_) (hnext sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf)
  rw [htid1, ← htpf] at hm; dsimp only [HbThreadIdInv]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] at hm ⊢
  refine Satisfies.mono (Entails.sepExists_right 1#64 ?_) hm
  rw [pure_sepConj_of_true (Or.inr rfl)]; sep_entail

theorem hbStdioPrint_getResult_tidInv_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) (optVal : Option (BitVec 64)) (init : Bool)
    {target_pc ret_pc sp0 arg0 arg1 valPtr : BitVec 64} {lc blk : Nat} {e0 : BitVec 32} {haveLse : BitVec 8}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C) (honce : HbOnceCallCode P C)
    (hcas8 : subroutine_ok P C.std.cas8RelaxAddr (stdCas8Spec C.std.haveLseAtomicsAddr))
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64) (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hsp_lo : optVal.isSome = true → 0x2e0 ≤ sp0.toNat)
    (hbudget : init = false → 1024 ≤ lim.maxReq ∧ lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)
    (hpc : s0.pc = C.stdioPrintAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_al : s0.spAligned = true) (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = arg0) (hx1 : s0.readReg64 .x1 = arg1)
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs → sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatGetResult optVal) →
      sf.sigActions = s0.sigActions → sf.tpidrEl0 = s0.tpidrEl0 →
      SepWP P target_pc sf
        ((HbStdoutInv C M γ true ∗ hbStdioPrintInputRes C optVal arg0 arg1 valPtr ∗
          (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
          (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C sf.tpidrEl0 ∗
          M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp0 4384) ∗ F) post oom) :
    SepWP P target_pc s0
      ((HbStdoutInv C M γ init ∗ hbStdioPrintInputRes C optVal arg0 arg1 valPtr ∗
        (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C s0.tpidrEl0 ∗
        M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp0 4384) ∗ F) post oom := by
  let k : HbPrintKind := match optVal with | none => .constNl noneNlBytes | some v => .u64Nl v
  have hk_out : k.outBytes = formatGetResult optVal := by cases optVal <;> rfl
  have hk_u64 : k.isU64 = optVal.isSome := by cases optVal <;> rfl
  cases optVal with
  | none =>
    dsimp only [hbStdioPrintInputRes]; simp only [sepConj_assoc]
    rw [sepConj_left_comm (HbStdoutInv C M γ init)]; apply SepWP.pure_elim; rintro ⟨rfl, rfl⟩
    refine SepWP.weaken_pre
      (P' := (HbStdoutInv C M γ init ∗ k.inputRes C C.noneNlAddr 0x0b#64 valPtr ∗
        (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C s0.tpidrEl0 ∗
        M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp0 4384) ∗ F)
      (by dsimp only [k, HbPrintKind.inputRes]
          rw [pure_sepConj_of_true ⟨by decide, by decide, by decide, hv.noneNl_noWrap, by decide, by decide⟩]; sep_entail)
      (hbStdioPrint_kind_tidInv_wp M γ k init hc hcSys hfmt honce hcas8 hcas4 hswp4 hMem hMemmove hv hg_nz hsvc hext
        (fun h => hsp_lo (hk_u64 ▸ h)) hbudget hpc hrun hsp hsp_al hlr hx0 hx1
        fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf => ?_)
    refine SepWP.weaken_pre_frame (fun R hm => ?_) (hnext sf e1 hpcf hrunf hspf hcsf hfsf (hk_out ▸ htrf) hsigf htpf)
    dsimp only [k, HbPrintKind.inputRes, hbStdioPrintInputRes] at hm ⊢
    rw [pure_sepConj_of_true ⟨by decide, by decide, by decide, hv.noneNl_noWrap, by decide, by decide⟩] at hm
    rw [pure_sepConj_of_true ⟨rfl, rfl⟩]; sep_entail
  | some v =>
    exact hbStdioPrint_kind_tidInv_wp M γ k init hc hcSys hfmt honce hcas8 hcas4 hswp4 hMem hMemmove hv hg_nz hsvc hext
      (fun h => hsp_lo (hk_u64 ▸ h)) hbudget hpc hrun hsp hsp_al hlr hx0 hx1
      fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf =>
        hnext sf e1 hpcf hrunf hspf hcsf hfsf (hk_out ▸ htrf) hsigf htpf

/-! ## `hashbrown_cli::print_bool` (`C.printBoolAddr`) -/

private theorem cs_of_pure {s0 s1 : State} (_ : FmtPureStatePreserved s0 s1)
    (h : CalleeSavedPreserved s0 s1 := by close_cs) : CalleeSavedPreserved s0 s1 := h

/-- Continuation-passing `SepWP` specification for `hashbrown_cli::print_bool` (`C.printBoolAddr`)
    over `HbThreadIdInv C s0.tpidrEl0`. -/
theorem hbPrintBool_tidInv_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) (b : Bool) (init : Bool)
    {target_pc ret_pc sp0 : BitVec 64}
    {lc blk : Nat} {e0 : BitVec 32} {haveLse : BitVec 8}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C)
    (honce : HbOnceCallCode P C)
    (hcas8 : subroutine_ok P C.std.cas8RelaxAddr (stdCas8Spec C.std.haveLseAtomicsAddr))
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64)
    (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hbudget : init = false → 1024 ≤ lim.maxReq ∧
      lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)
    (hpc : s0.pc = C.printBoolAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_al : s0.spAligned = true) (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = if b then 1#64 else 0#64)
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs → sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatBoolResult b) →
      sf.sigActions = s0.sigActions → sf.tpidrEl0 = s0.tpidrEl0 →
      SepWP P target_pc sf
        ((HbStdoutInv C M γ true ∗ HbAdapterWriteVtableRo C ∗
          (C.trueNlAddr ↦ᵣ trueNlBytes) ∗ (C.falseNlAddr ↦ᵣ falseNlBytes) ∗
          (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
          (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C sf.tpidrEl0 ∗
          M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp0 4384) ∗ F) post oom) :
    SepWP P target_pc s0
      ((HbStdoutInv C M γ init ∗ HbAdapterWriteVtableRo C ∗
        (C.trueNlAddr ↦ᵣ trueNlBytes) ∗ (C.falseNlAddr ↦ᵣ falseNlBytes) ∗
        (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C s0.tpidrEl0 ∗
        M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp0 4384) ∗ F) post oom := by
  subst hsp
  have hlr' : s0.readReg64 (.gpr 30#5) = ret_pc := hlr
  cases b with
  | true =>
    have hx0' : s0.readReg64 (.gpr 0#5) = 1#64 := hx0
    let k : HbPrintKind := .constNl trueNlBytes
    refine sepWP_cpu_seg (mid_pc := C.stdioPrintAddr) hext ?_
    have hchunk := (hc.withSvc noSyscalls).printBool
    unpack_stdout_code hbPrintBoolChunks hchunk
    wp_steps 2; wp_steps 1; wp_steps 1; wp_steps 1; norm_jmp
    conv => repeat rw [bv64_add_sub_cancel']
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
      ⟨by simp [CpuAuxPreserved.refl s0], fun hpure1 => ?_⟩
    have hcs01 := cs_of_pure hpure1
    refine SepWP.weaken_pre
      (P' := (HbStdoutInv C M γ init ∗ k.inputRes C C.trueNlAddr 0x0b#64 0#64 ∗
        (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C _ ∗
        M.Heap γ lc blk _ ∗ (muslErrnoAddr _ ↦₃₂ e0) ∗ stackAt s0.sp 4384) ∗
        ((C.falseNlAddr ↦ᵣ falseNlBytes) ∗ F))
      (by
        dsimp only [k, HbPrintKind.inputRes, muslErrnoAddr]
        rw [heap_eq_of_std M hpure1.1, ← hpure1.1.2.2.1,
            pure_sepConj_of_true ⟨by decide, by decide, by decide, hv.trueNl_noWrap, by decide, by decide⟩]
        sep_frame)
      (hbStdioPrint_kind_tidInv_wp M γ k init (ret_pc := ret_pc)
        hc hcSys hfmt honce hcas8 hcas4 hswp4 hMem hMemmove hv hg_nz hsvc hext
        (by intro h; cases h) hbudget
        wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
        (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_al)
        wp_a wp_a wp_a
        fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf => ?_)
    have htr_all : sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatBoolResult true) := by
      rw [htrf, hpure1.1.2.1]; rfl
    refine SepWP.weaken_pre_frame (fun R hm => ?_)
      (hnext sf e1 hpcf hrunf hspf (hcs01.trans hcsf)
        (hfsf.trans hpure1.1.1) htr_all (hsigf.trans hpure1.1.2.2.2.1) (htpf.trans hpure1.1.2.2.1))
    dsimp only [k, HbPrintKind.inputRes] at hm
    rw [pure_sepConj_of_true ⟨by decide, by decide, by decide, hv.trueNl_noWrap, by decide, by decide⟩] at hm
    sep_entail
  | false =>
    have hx0' : s0.readReg64 (.gpr 0#5) = 0#64 := hx0
    let k : HbPrintKind := .constNl falseNlBytes
    refine sepWP_cpu_seg (mid_pc := C.stdioPrintAddr) hext ?_
    have hchunk := (hc.withSvc noSyscalls).printBool
    unpack_stdout_code hbPrintBoolChunks hchunk
    wp_steps 1; wp_steps 1; wp_steps 1; wp_steps 1; wp_steps 1; norm_jmp
    conv => repeat rw [bv64_add_sub_cancel']
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
      ⟨by simp [CpuAuxPreserved.refl s0], fun hpure1 => ?_⟩
    have hcs01 := cs_of_pure hpure1
    refine SepWP.weaken_pre
      (P' := (HbStdoutInv C M γ init ∗ k.inputRes C C.falseNlAddr 0x0d#64 0#64 ∗
        (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C _ ∗
        M.Heap γ lc blk _ ∗ (muslErrnoAddr _ ↦₃₂ e0) ∗ stackAt s0.sp 4384) ∗
        ((C.trueNlAddr ↦ᵣ trueNlBytes) ∗ F))
      (by
        dsimp only [k, HbPrintKind.inputRes, muslErrnoAddr]
        rw [heap_eq_of_std M hpure1.1, ← hpure1.1.2.2.1,
            pure_sepConj_of_true ⟨by decide, by decide, by decide, hv.falseNl_noWrap, by decide, by decide⟩]
        sep_frame)
      (hbStdioPrint_kind_tidInv_wp M γ k init (ret_pc := ret_pc)
        hc hcSys hfmt honce hcas8 hcas4 hswp4 hMem hMemmove hv hg_nz hsvc hext
        (by intro h; cases h) hbudget
        wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
        (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_al)
        wp_a wp_a wp_a
        fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf => ?_)
    have htr_all : sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatBoolResult false) := by
      rw [htrf, hpure1.1.2.1]; rfl
    refine SepWP.weaken_pre_frame (fun R hm => ?_)
      (hnext sf e1 hpcf hrunf hspf (hcs01.trans hcsf)
        (hfsf.trans hpure1.1.1) htr_all (hsigf.trans hpure1.1.2.2.2.1) (htpf.trans hpure1.1.2.2.1))
    dsimp only [k, HbPrintKind.inputRes] at hm
    rw [pure_sepConj_of_true ⟨by decide, by decide, by decide, hv.falseNl_noWrap, by decide, by decide⟩] at hm
    sep_entail

/-- Total-correctness `Spec` for `hashbrown_cli::print_bool` (`C.printBoolAddr`) over `HbThreadIdInv`. -/
def hbPrintBoolSpec {P : Program} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) :
    Spec (Bool × Bool × Nat × Nat × BitVec 32 × BitVec 8) where
  pre := fun (b, init, lc, blk, e0, haveLse) s0 =>
    ⌜s0.readReg64 .x0 = (if b then 1#64 else 0#64) ∧
      (init = false → 1024 ≤ lim.maxReq ∧
        lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)⌝ ∗
    HbStdoutInv C M γ init ∗ HbAdapterWriteVtableRo C ∗
    (C.trueNlAddr ↦ᵣ trueNlBytes) ∗ (C.falseNlAddr ↦ᵣ falseNlBytes) ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C s0.tpidrEl0 ∗
    M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp 4384
  post := fun (b, init, lc, blk, _, haveLse) s0 sf =>
    ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatBoolResult b) ∧
      sf.sigActions = s0.sigActions ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
    HbStdoutInv C M γ true ∗ HbAdapterWriteVtableRo C ∗
    (C.trueNlAddr ↦ᵣ trueNlBytes) ∗ (C.falseNlAddr ↦ᵣ falseNlBytes) ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C sf.tpidrEl0 ∗
    M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
    (∃∗ e1 : BitVec 32, muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt s0.sp 4384

theorem hbPrintBool_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C)
    (honce : HbOnceCallCode P C)
    (hcas8 : subroutine_ok P C.std.cas8RelaxAddr (stdCas8Spec C.std.haveLseAtomicsAddr))
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64) (hsvc : P.svc = Syscall.standard)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.printBoolAddr (hbPrintBoolSpec C M γ) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨b, init, lc, blk, e0, haveLse⟩ R s0 hpc hrun hpre hsp
  dsimp only [hbPrintBoolSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hbudget⟩, hmem⟩
  refine ⟨(HbStdoutInv C M γ init ∗ HbAdapterWriteVtableRo C ∗
    (C.trueNlAddr ↦ᵣ trueNlBytes) ∗ (C.falseNlAddr ↦ᵣ falseNlBytes) ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C s0.tpidrEl0 ∗
    M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp 4384) ∗ emp,
    by simpa [sepConj_emp, sepConj_assoc] using hmem, ?_⟩
  refine hbPrintBool_tidInv_wp M γ b init hc hcSys hfmt honce hcas8 hcas4 hswp4
    hMem hMemmove hv hg_nz hsvc hext hbudget hpc hrun rfl hsp rfl hx0
    fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf => ?_
  refine SepWP.done hpcf hrunf ⟨fun hm => ?_, hspf, hcsf⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hfsf, htrf, hsigf, htpf⟩, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_emp, sepConj_assoc] at hm ⊢
  exact Satisfies.mono (Entails.sepExists_right e1 (by sep_entail)) hm

end CaseStudies.Hashbrown.Proofs.StdCli
