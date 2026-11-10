/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.StdoutFlush
public meta import CaseStudies.Hashbrown.Proofs.StdCli.StdoutFlush
public meta import ProofLib.SepLogic.Stack

/-!
# `StdoutRaw::write_all`, `BufWriter::write_all_cold`, and `StdoutLock` Newline Path

Placement-generic `SepWP` and `subroutine_ok` specifications for `StdoutRaw::write_all`,
`BufWriter<StdoutRaw>::write_all_cold`, and the newline-triggered flush path of
`StdoutLock::write_all`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iLdr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W64 .X64 false $rt (.Offset $rn (pageLo12 $t)))
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
local macro "wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)


/-! ## `StdoutRaw::write_all` and `BufWriter<StdoutRaw>::write_all_cold` -/

theorem call_hbMemcpy {P : Program} {memcpyAddr memsetAddr target_pc ret_pc sp0 dst src : BitVec 64}
    (ro : Bool) (hMem : StdMemOps P memcpyAddr memsetAddr) {bs : List (BitVec 8)}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlen : bs.length < 2 ^ 64 := by omega)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (memRegion dst bs.length ∗ hbBytesSlice ro src bs) ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = dst → StdStatePreserved s sf →
      SepWP P target_pc sf (((dst ↦ₛ bs) ∗ hbBytesSlice ro src bs) ∗ F) post oom)
    (hpc : s.pc = memcpyAddr := by wp_arg)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp : s.sp = sp0 := by wp_arg)
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by wp_arg)
    (hx0 : s.readReg64 .x0 = dst := by wp_arg)
    (hx1 : s.readReg64 .x1 = src := by wp_arg)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length := by wp_arg) :
    SepWP P target_pc s Pre post oom := by
  cases ro
  · exact hMem.call_memcpy (F := F) hpre
      (fun sf hpc_f hrun_f hsp_f hcs_f hx0_f hstd_f =>
        hnext sf hpc_f hrun_f (hsp_f.trans hsp) hcs_f hx0_f hstd_f)
      hpc hrun hsp_align hlr hx0 hx1 hx2 hlen
  · exact hMem.call_memcpy_ro (F := F) hpre
      (fun sf hpc_f hrun_f hsp_f hcs_f hx0_f hstd_f =>
        hnext sf hpc_f hrun_f (hsp_f.trans hsp) hcs_f hx0_f hstd_f)
      hpc hrun hsp_align hlr hx0 hx1 hx2 hlen

theorem hbStdoutRawWriteAll_stdioSvc_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp0 slicePtr : BitVec 64} {bs : List (BitVec 8)}
    (ro : Bool) (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlen_lo : 1 ≤ bs.length) (hlen_max : bs.length ≤ Arm64.MAX_RW_COUNT)
    (hslice_va : slicePtr.toNat + bs.length ≤ Arm64.USER_VA_LIMIT)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ ((C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        hbBytesSlice ro slicePtr bs ∗ stackAt sp0 144) ∗ (F ∗ R)))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      sf.fs = s.fs → sf.tpidrEl0 = s.tpidrEl0 →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stdout bs →
      SepWP (P.withSvc hbStdioSvc) target_pc sf
        (((C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
          hbBytesSlice ro slicePtr bs ∗ stackAt sp0 144) ∗ F) post oom)
    (hpc : s.pc = C.stdoutRawWriteAllAddr := by wp_arg)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp : s.sp = sp0 := by wp_arg)
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by wp_arg)
    (hx0 : s.readReg64 .x0 = slicePtr := by wp_arg)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs.length := by wp_arg) :
    SepWP (P.withSvc hbStdioSvc) target_pc s Pre post oom := by
  have hcRw := (hc.withSvc hbStdioSvc).stdoutRawWriteAll
  unpack_stdout_code hbStdoutRawWriteAllChunks hcRw
  have hlen_hi : bs.length < 2 ^ 63 := by
    simp only [Arm64.MAX_RW_COUNT] at hlen_max; omega
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0' : BitVec.ofNat 64 bs.length ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h
    rw [hlen_toNat] at this; change bs.length = 0 at this; omega
  have hne0 : (BitVec.ofNat 64 bs.length == 0#64) = false := beq_false_of_ne hne0'
  have hcmn : (BitVec.ofNat 64 bs.length + 1#64 == 0#64) = false :=
    beq_false_of_ne fun h => by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_add, hlen_toNat, show (1#64).toNat = 1 from rfl,
          show (0#64).toNat = 0 from rfl, Nat.mod_eq_of_lt (by omega)] at this
      omega
  have hult_self : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 bs.length) = false := by
    simp [BitVec.ult]
  refine SepWP.weaken_pre_frame
    (P' := stackAt sp0 112 ∗ (stackAt (sp0 - 112#64) 32 ∗
      (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ hbBytesSlice ro slicePtr bs ∗ F))
    (fun R hm => by
      have hm' := hpre R hm
      rw [show (144 : Nat) = 112 + 32 from rfl, stackAt_split 112 32] at hm'
      exact (by sep_entail : _ → _) hm') ?_
  conv => arg 4; rw [← hsp, stackAt_eq_cells s.sp 14]
  unpack_cells 14
  wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; norm_jmp
  refine hbWrite_stdioSvc_wp ro hcSys (sp0 := sp0 - 112#64) (bufPtr := slicePtr) (bs := bs)
    (ret_pc := C.stdoutRawWriteAllAddr + 0x68#64) hlen_max hslice_va (by rw [hsp]; sep_frame)
    fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hfs1 htid1 htr1 => ?_
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1, ← hsp]; exact s.spAligned_sub 112#64 hsp_align
  have hx20_1 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 bs.length := by rw [hcs1.2.1]; exact wp_a
  have hx21_1 : s1.readReg64 (.gpr 21#5) = slicePtr := by rw [hcs1.2.2.1]; exact wp_a
  have hx0_1' : s1.readReg64 (.gpr 0#5) = BitVec.ofNat 64 bs.length := hx0_1
  wp_steps; wp_steps; wp_steps
  refine SepWP.weaken_pre_frame
    (P' := ((C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
      hbBytesSlice ro slicePtr bs ∗ stackAt sp0 144) ∗ F)
    (fun _ _ => by
      rw [show (144 : Nat) = 112 + 32 from rfl, stackAt_split 112 32, stackAt_eq_cells sp0 14]
      repack_cells) ?_
  exact hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun1]) wp_a
    (by unpack_cs hcs1; close_cs) wp_a
    (by simp [wp_norm, arm64_norm, hfs1])
    (by simp [wp_norm, arm64_norm, htid1])
    (by simp [wp_norm, arm64_norm, htr1])

def hbStdoutRawWriteAllSpec (C : HbCliLayout) (ro : Bool) : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (slicePtr, bs) s0 =>
    ⌜s0.readReg64 .x0 = slicePtr ∧ s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      1 ≤ bs.length ∧ bs.length ≤ Arm64.MAX_RW_COUNT ∧
      slicePtr.toNat + bs.length ≤ Arm64.USER_VA_LIMIT⌝ ∗
    ((C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ hbBytesSlice ro slicePtr bs ∗ stackAt s0.sp 144)
  post := fun (slicePtr, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout bs ∧
      FmtIoStatePreserved s0 sf ∧ HbNonVmPreserved s0 sf⌝ ∗
    ((C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ hbBytesSlice ro slicePtr bs ∗ stackAt s0.sp 144)

theorem hbStdoutRawWriteAll_ok {P : Program} {C : HbCliLayout} (ro : Bool)
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.stdoutRawWriteAllAddr (hbStdoutRawWriteAllSpec C ro) := by
  refine subroutine_ok_of_sepWP_stdioSvc hext hsvc fun ⟨slicePtr, bs⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [hbStdoutRawWriteAllSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlo, hmax, hslice_va⟩, hm⟩
  refine ⟨((C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
    hbBytesSlice ro slicePtr bs ∗ stackAt s0.sp 144) ∗ emp, by simpa [sepConj_emp] using hm, ?_⟩
  refine hbStdoutRawWriteAll_stdioSvc_wp ro hc hcSys hlo hmax hslice_va
    (by sep_frame) (fun sf hpcf hrunf hspf hcsf hx0f hfsf htidf htrf => ?_)
    hpc hrun rfl hsp rfl hx0 hx1
  refine SepWP.done hpcf hrunf ⟨fun hpr hmf => ?_, hspf, hcsf⟩
  dsimp only [hbStdoutRawWriteAllSpec]; rw [sepConj_emp] at hmf
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0f, htrf, hpr.toFmtIo hfsf htidf, hpr.toHbNonVm htidf⟩, hmf⟩

/-! ### `BufWriter<StdoutRaw>` State Bundle and `write_all_cold` -/

def hbBufWriterState (bwPtr bufPtr : BitVec 64) (pan : BitVec 8)
    (buffered : List (BitVec 8)) : SepProp :=
  (bwPtr ↦₆₄ 1024#64) ∗
  ((bwPtr + 0x08#64) ↦₆₄ bufPtr) ∗
  ((bwPtr + 0x10#64) ↦₆₄ BitVec.ofNat 64 buffered.length) ∗
  ((bwPtr + 0x18#64) ↦₈ pan) ∗
  (bufPtr ↦ₛ buffered) ∗
  memRegion (bufPtr + BitVec.ofNat 64 buffered.length) (1024 - buffered.length)

theorem bv64_sub_ofNat {a b : Nat} (hle : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  have h : BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel hle]
  rw [h, BitVec.add_sub_cancel]

theorem bv64_ule_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a ≤ b) := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem hbBufWriterState_split_append (bwPtr bufPtr : BitVec 64) (pan : BitVec 8)
    (buffered : List (BitVec 8)) (n : Nat) (hbuf : buffered.length ≤ 1024)
    (hn : n ≤ 1024 - buffered.length) :
     hbBufWriterState bwPtr bufPtr pan buffered =
      memRegion (bufPtr + BitVec.ofNat 64 buffered.length) n ∗
      ((bwPtr ↦₆₄ 1024#64) ∗ ((bwPtr + 0x08#64) ↦₆₄ bufPtr) ∗
       ((bwPtr + 0x10#64) ↦₆₄ BitVec.ofNat 64 buffered.length) ∗
       ((bwPtr + 0x18#64) ↦₈ pan) ∗ (bufPtr ↦ₛ buffered) ∗
       memRegion (bufPtr + BitVec.ofNat 64 (buffered.length + n)) (1024 - (buffered.length + n))) := by
  unfold hbBufWriterState
  rw [memRegion_split_le (bufPtr + BitVec.ofNat 64 buffered.length) n (1024 - buffered.length) hn (by omega),
      BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 - buffered.length - n = 1024 - (buffered.length + n) by omega]
  ac_rfl

private theorem hbBufWriterState_merge_append (bwPtr bufPtr : BitVec 64) (pan : BitVec 8)
    (buffered bs : List (BitVec 8)) :
    ((bwPtr ↦₆₄ 1024#64) ∗ ((bwPtr + 0x08#64) ↦₆₄ bufPtr) ∗
     ((bwPtr + 0x10#64) ↦₆₄ (BitVec.ofNat 64 buffered.length + BitVec.ofNat 64 bs.length)) ∗
     ((bwPtr + 0x18#64) ↦₈ pan) ∗
     (bufPtr ↦ₛ buffered) ∗ ((bufPtr + BitVec.ofNat 64 buffered.length) ↦ₛ bs) ∗
     memRegion (bufPtr + BitVec.ofNat 64 (buffered.length + bs.length))
       (1024 - (buffered.length + bs.length))) =
    hbBufWriterState bwPtr bufPtr pan (buffered ++ bs) := by
  unfold hbBufWriterState
  rw [List.length_append, BitVec.ofNat_add, pointsToBytes_append bufPtr buffered bs]
  ac_rfl

theorem hbBufWriterFlush_state_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp0 bwPtr bufPtr : BitVec 64} {pan0 : BitVec 8} {buffered : List (BitVec 8)}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlen_lo : 1 ≤ buffered.length) (hlen_hi : buffered.length ≤ 1024)
    (hbuf_va : bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (hbBufWriterState bwPtr bufPtr pan0 buffered ∗ stackAt sp0 144) ∗ (F ∗ R)))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      sf.fs = s.fs → sf.tpidrEl0 = s.tpidrEl0 →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stdout buffered →
      SepWP (P.withSvc hbStdioSvc) target_pc sf
        ((hbBufWriterState bwPtr bufPtr 0#8 [] ∗ stackAt sp0 144) ∗ F) post oom)
    (hpc : s.pc = C.bufWriterFlushBufAddr := by wp_arg)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp : s.sp = sp0 := by wp_arg)
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by wp_arg)
    (hx0 : s.readReg64 .x0 = bwPtr := by wp_arg) :
    SepWP (P.withSvc hbStdioSvc) target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame
    (P' := (hbBufWriterState bwPtr bufPtr pan0 buffered ∗ stackAt sp0 144) ∗ F)
    (fun R hm => by rw [sepConj_assoc]; exact hpre R hm) ?_
  dsimp only [hbBufWriterState]
  refine hbBufWriterFlushBuf_stdioSvc_wp (bufPtr := bufPtr) hc hcSys hMemmove hlen_lo hlen_hi (by omega)
    (sp0 := sp0) (ret_pc := ret_pc)
    (by dsimp only [hbBufWriterFlushBufRes]; sep_frame)
    (fun sf hpcf hrunf hspf hcsf hx0f hfsf htidf htrf => ?_)
    hpc hrun hsp hsp_align hlr hx0
  refine SepWP.weaken_pre_frame
    (P' := (hbBufWriterState bwPtr bufPtr 0#8 [] ∗ stackAt sp0 144) ∗ F)
    (fun R hm => ?_) (hnext sf hpcf hrunf hspf hcsf hx0f hfsf htidf htrf)
  dsimp only [hbBufWriterFlushBufRes] at hm
  dsimp only [hbBufWriterState, List.length_nil]
  rw [pointsToBytes_nil, emp_sepConj, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero,
      Nat.sub_zero, memRegion_split_le bufPtr buffered.length 1024 hlen_hi (by decide)]
  exact Satisfies.mono
    (by have h := pointsToBytes_entails_memRegion bufPtr buffered; sep_entail) hm

theorem hbBufWriterWriteAllCold_stdioSvc_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp0 bwPtr bufPtr slicePtr : BitVec 64} {buffered bs : List (BitVec 8)}
    (ro : Bool) (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C)
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hbs_lo : 1 ≤ bs.length) (hbs_hi : bs.length < 1024) (hbuf_hi : buffered.length ≤ 1024)
    (hbuf_va : bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (hbBufWriterState bwPtr bufPtr 0#8 buffered ∗
        hbBytesSlice ro slicePtr bs ∗ stackAt sp0 192) ∗ (F ∗ R)))
    (hnext : ∀ sf : State,
      let fl := if bs.length ≤ 1024 - buffered.length then ([] : List (BitVec 8)) else buffered
      let newBuf := if bs.length ≤ 1024 - buffered.length then buffered ++ bs else bs
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      sf.fs = s.fs → sf.tpidrEl0 = s.tpidrEl0 →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stdout fl →
      SepWP (P.withSvc hbStdioSvc) target_pc sf
        ((hbBufWriterState bwPtr bufPtr 0#8 newBuf ∗
          hbBytesSlice ro slicePtr bs ∗ stackAt sp0 192) ∗ F) post oom)
    (hpc : s.pc = C.bufWriterWriteAllColdAddr := by wp_arg)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp : s.sp = sp0 := by wp_arg)
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by wp_arg)
    (hx0 : s.readReg64 .x0 = bwPtr := by wp_arg)
    (hx1 : s.readReg64 .x1 = slicePtr := by wp_arg)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length := by wp_arg) :
    SepWP (P.withSvc hbStdioSvc) target_pc s Pre post oom := by
  subst hsp
  have hcWc := (hc.withSvc hbStdioSvc).bufWriterWriteAllCold
  unpack_stdout_code hbBufWriterWriteAllColdChunks hcWc
  have hrem_eq : 1024#64 - BitVec.ofNat 64 buffered.length = BitVec.ofNat 64 (1024 - buffered.length) :=
    bv64_sub_ofNat hbuf_hi
  have hhs_false : (1024#64).ule (BitVec.ofNat 64 bs.length) = false := by
    change BitVec.ule (BitVec.ofNat 64 1024) (BitVec.ofNat 64 bs.length) = false
    rw [bv64_ule_ofNat (by decide) (by omega)]; exact decide_eq_false (by omega)
  refine SepWP.weaken_pre_frame
    (P' := stackAt s.sp 48 ∗ (stackAt (s.sp - 48#64) 144 ∗
      hbBufWriterState bwPtr bufPtr 0#8 buffered ∗ hbBytesSlice ro slicePtr bs ∗ F))
    (fun R hm => by
      have hm' := hpre R hm
      rw [show (192 : Nat) = 48 + 144 from rfl, stackAt_split 48 144] at hm'
      exact (by sep_entail : _ → _) hm') ?_
  conv => arg 4; rw [stackAt_eq_cells s.sp 6]
  unpack_cells 6
  dsimp only [hbBufWriterState]
  wp_steps
  let Slots (vPad : BitVec 64) : SepProp :=
    ((s.sp - 48#64) ↦₆₄ s.readReg64 .fp) ∗ ((s.sp - 40#64) ↦₆₄ ret_pc) ∗
    ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ ((s.sp - 24#64) ↦₆₄ vPad) ∗
    ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5))
  have htail : ∀ (curBuf fl : List (BitVec 8)) (vPad : BitVec 64) (st : State) {Pcur : SepProp},
      curBuf.length ≤ 1024 → bs.length ≤ 1024 - curBuf.length →
      fl = (if bs.length ≤ 1024 - buffered.length then [] else buffered) →
      curBuf ++ bs = (if bs.length ≤ 1024 - buffered.length then buffered ++ bs else bs) →
      st.pc = C.std.memcpyAddr → st.status = .Running → st.sp = s.sp - 48#64 →
      st.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
      st.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
      st.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
      st.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
      st.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
      st.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
      st.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
      calleeSavedVRegs st = calleeSavedVRegs s →
      st.readReg64 Reg.lr = C.bufWriterWriteAllColdAddr + 0x6c#64 →
      st.readReg64 .x0 = bufPtr + BitVec.ofNat 64 curBuf.length →
      st.readReg64 .x1 = slicePtr → st.readReg64 .x2 = BitVec.ofNat 64 bs.length →
      st.readReg64 (.gpr 19#5) = bwPtr → st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 bs.length →
      st.readReg64 (.gpr 21#5) = BitVec.ofNat 64 curBuf.length →
      st.fs = s.fs → st.tpidrEl0 = s.tpidrEl0 →
      st.trace = s.trace ++ TraceEvent.ofBytes .stdout fl →
      (∀ R : SepProp, st.mem ⊨ Pcur ∗ R →
        st.mem ⊨ (memRegion (bufPtr + BitVec.ofNat 64 curBuf.length) bs.length ∗
          hbBytesSlice ro slicePtr bs) ∗
          ((Slots vPad ∗ stackAt (s.sp - 48#64) 144 ∗
            ((bwPtr ↦₆₄ 1024#64) ∗ ((bwPtr + 0x08#64) ↦₆₄ bufPtr) ∗
             ((bwPtr + 0x10#64) ↦₆₄ BitVec.ofNat 64 curBuf.length) ∗
             ((bwPtr + 0x18#64) ↦₈ 0#8) ∗ (bufPtr ↦ₛ curBuf) ∗
             memRegion (bufPtr + BitVec.ofNat 64 (curBuf.length + bs.length))
               (1024 - (curBuf.length + bs.length))) ∗ F) ∗ R)) →
      SepWP (P.withSvc hbStdioSvc) target_pc st Pcur post oom := by
    intro curBuf fl vPad st Pcur hcur hfit' hfl hnb hpc_t hrun_t hsp_t hcs_hi hlr_t hx0_t hx1_t hx2_t hx19_t hx20_t hx21_t hfs_t htid_t htr_t hpre_t
    have hsp_t_al : st.spAligned = true := by
      simp only [State.spAligned, hsp_t]; exact s.spAligned_sub 48#64 hsp_align
    refine call_hbMemcpy ro hMem (sp0 := s.sp - 48#64)
      (dst := bufPtr + BitVec.ofNat 64 curBuf.length) (src := slicePtr) (bs := bs)
      (ret_pc := C.bufWriterWriteAllColdAddr + 0x6c#64) (by omega) hpre_t
      (fun sm hpcm hrunm hspm hcsm hx0m hstdm => ?_)
      hpc_t hrun_t hsp_t hsp_t_al hlr_t hx0_t hx1_t hx2_t
    have hspm_al : sm.spAligned = true := by
      simp only [State.spAligned, hspm]; exact s.spAligned_sub 48#64 hsp_align
    have hx19_m : sm.readReg64 (.gpr 19#5) = bwPtr := by rw [hcsm.1]; exact hx19_t
    have hx20_m : sm.readReg64 (.gpr 20#5) = BitVec.ofNat 64 bs.length := by rw [hcsm.2.1]; exact hx20_t
    have hx21_m : sm.readReg64 (.gpr 21#5) = BitVec.ofNat 64 curBuf.length := by rw [hcsm.2.2.1]; exact hx21_t
    dsimp only [Slots]
    wp_steps; wp_steps
    refine SepWP.weaken_pre_frame
      (P' := (hbBufWriterState bwPtr bufPtr 0#8
        (if bs.length ≤ 1024 - buffered.length then buffered ++ bs else bs) ∗
        hbBytesSlice ro slicePtr bs ∗ stackAt s.sp 192) ∗ F)
      (fun _ hm => by
        rw [← hnb, ← hbBufWriterState_merge_append,
            show (192 : Nat) = 48 + 144 from rfl, stackAt_split 48 144, stackAt_eq_cells s.sp 6]
        exact (by repack_cells : _ → _) hm) ?_
    rcases hcs_hi with ⟨hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩
    exact hnext _ wp_a (by simp [wp_norm, arm64_norm, hrunm]) wp_a
      (by unpack_cs hcsm; close_cs) wp_a
      (by simp [wp_norm, arm64_norm, hstdm.1, hfs_t])
      (by simp [wp_norm, arm64_norm, hstdm.2.2.1, htid_t])
      (by rw [← hfl]; simp [wp_norm, arm64_norm, hstdm.2.1, htr_t])
  by_cases hfit : bs.length ≤ 1024 - buffered.length
  · have hule : BitVec.ule (BitVec.ofNat 64 bs.length) (BitVec.ofNat 64 (1024 - buffered.length)) = true := by
      rw [bv64_ule_ofNat (by omega) (by omega)]; exact decide_eq_true hfit
    rw [hule]; simp only [↓reduceIte]
    wp_steps; norm_jmp
    exact htail buffered [] _ _ hbuf_hi hfit (by simp [hfit]) (by simp [hfit])
      wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
      ⟨wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm]⟩
      wp_a wp_a wp_a wp_a wp_a wp_a wp_a
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, TraceEvent.ofBytes])
      (fun R hm => by
        rw [memRegion_split_le (bufPtr + BitVec.ofNat 64 buffered.length) bs.length (1024 - buffered.length) hfit (by omega),
            BitVec.add_assoc, ← BitVec.ofNat_add,
            show 1024 - buffered.length - bs.length = 1024 - (buffered.length + bs.length) by omega] at hm
        dsimp only [Slots]; sep_frame)
  · have hule : BitVec.ule (BitVec.ofNat 64 bs.length) (BitVec.ofNat 64 (1024 - buffered.length)) = false := by
      rw [bv64_ule_ofNat (by omega) (by omega)]; exact decide_eq_false hfit
    rw [hule]; simp only [Bool.false_eq_true, ↓reduceIte]
    wp_steps; norm_jmp
    refine hbBufWriterFlush_state_wp hc hcSys hMemmove (sp0 := s.sp - 48#64)
      (bwPtr := bwPtr) (bufPtr := bufPtr) (pan0 := 0#8) (buffered := buffered)
      (ret_pc := C.bufWriterWriteAllColdAddr + 0x38#64) (by omega) hbuf_hi hbuf_va
      (by dsimp only [hbBufWriterState]; sep_frame)
      fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hfs1 htid1 htr1 => ?_
    have hsp1_al : s1.spAligned = true := by
      simp only [State.spAligned, hsp1]; exact s.spAligned_sub 48#64 hsp_align
    have hx19_1 : s1.readReg64 (.gpr 19#5) = bwPtr := by rw [hcs1.1]; exact wp_a
    have hx20_1 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 bs.length := by rw [hcs1.2.1]; exact wp_a
    have hx21_1 : s1.readReg64 (.gpr 21#5) = slicePtr := by rw [hcs1.2.2.1]; exact wp_a
    have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
    rw [hbBufWriterState_split_append bwPtr bufPtr 0#8 [] bs.length (by decide) (by simpa using Nat.le_of_lt hbs_hi)]
    wp_steps; norm_jmp
    exact htail [] buffered _ _ (by decide) (by simpa using Nat.le_of_lt hbs_hi)
      (by simp [hfit]) (by simp [hfit])
      wp_a (by simp [wp_norm, arm64_norm, hrun1]) wp_a
      (by unpack_cs hcs1; exact ⟨wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm, *]⟩)
      wp_a (by simp [wp_norm, arm64_norm]) wp_a wp_a wp_a wp_a wp_a
      (by simp [wp_norm, arm64_norm, hfs1]) (by simp [wp_norm, arm64_norm, htid1])
      (by simp [wp_norm, arm64_norm, htr1])
      (by dsimp only [Slots]; sep_frame)

def hbBufWriterWriteAllColdSpec (ro : Bool) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := fun (bwPtr, bufPtr, slicePtr, buffered, bs) s0 =>
    ⌜s0.readReg64 .x0 = bwPtr ∧ s0.readReg64 .x1 = slicePtr ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
      1 ≤ bs.length ∧ bs.length < 1024 ∧ buffered.length ≤ 1024 ∧
      bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT⌝ ∗
    (hbBufWriterState bwPtr bufPtr 0#8 buffered ∗ hbBytesSlice ro slicePtr bs ∗ stackAt s0.sp 192)
  post := fun (bwPtr, bufPtr, slicePtr, buffered, bs) s0 sf =>
    let fl := if bs.length ≤ 1024 - buffered.length then ([] : List (BitVec 8)) else buffered
    let newBuf := if bs.length ≤ 1024 - buffered.length then buffered ++ bs else bs
    ⌜sf.readReg64 .x0 = 0#64 ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout fl ∧
      FmtIoStatePreserved s0 sf ∧ HbNonVmPreserved s0 sf⌝ ∗
    (hbBufWriterState bwPtr bufPtr 0#8 newBuf ∗ hbBytesSlice ro slicePtr bs ∗ stackAt s0.sp 192)

theorem hbBufWriterWriteAllCold_ok {P : Program} {C : HbCliLayout} (ro : Bool)
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C)
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.bufWriterWriteAllColdAddr (hbBufWriterWriteAllColdSpec ro) := by
  refine subroutine_ok_of_sepWP_stdioSvc hext hsvc
    fun ⟨bwPtr, bufPtr, slicePtr, buffered, bs⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [hbBufWriterWriteAllColdSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbs_lo, hbs_hi, hbuf_hi, hbuf_va⟩, hm⟩
  refine ⟨(hbBufWriterState bwPtr bufPtr 0#8 buffered ∗
    hbBytesSlice ro slicePtr bs ∗ stackAt s0.sp 192) ∗ emp, by simpa [sepConj_emp] using hm, ?_⟩
  refine hbBufWriterWriteAllCold_stdioSvc_wp ro hc hcSys hMem hMemmove hbs_lo hbs_hi hbuf_hi hbuf_va
    (by sep_frame) (fun sf hpcf hrunf hspf hcsf hx0f hfsf htidf htrf => ?_)
    hpc hrun rfl hsp rfl hx0 hx1 hx2
  refine SepWP.done hpcf hrunf ⟨fun hpr hmf => ?_, hspf, hcsf⟩
  dsimp only [hbBufWriterWriteAllColdSpec]; rw [sepConj_emp] at hmf
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0f, htrf, hpr.toFmtIo hfsf htidf, hpr.toHbNonVm htidf⟩, hmf⟩
/-! ## `StdoutLock::write_all` Newline Path -/

def hbStdoutRefCell (C : HbCliLayout) (g bufPtr : BitVec 64) (buffered : List (BitVec 8)) : SepProp :=
  (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
  ((g + 0x10#64) ↦₆₄ 0#64) ∗ hbBufWriterState (g + 0x18#64) bufPtr 0#8 buffered

theorem bv64_ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem align8_pad (p : BitVec 64) :
    ∃ pad : Nat, pad ≤ 7 ∧ ((p + 7#64) &&& (-8#64)) - p = BitVec.ofNat 64 pad := by
  have hm : (p + 7#64) &&& (-8#64) = (p + 7#64) - ((p + 7#64) &&& 7#64) :=
    BitVec.and_neg8_eq_sub_and_7 (p + 7#64)
  have hsub : ((p + 7#64) - ((p + 7#64) &&& 7#64)) - p = 7#64 - ((p + 7#64) &&& 7#64) := by bv_lin
  have hk_le : ((p + 7#64) &&& 7#64).toNat ≤ 7 := by bv_bits
  let k := ((p + 7#64) &&& 7#64).toNat
  have hk_eq : (p + 7#64) &&& 7#64 = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq; simp [k]
  refine ⟨7 - k, by omega, ?_⟩
  rw [hm, hsub, hk_eq]
  exact bv64_sub_ofNat hk_le

private theorem sub32_and15_ofNat {n pad : Nat} (hpad : pad ≤ n) (hn : n ≤ 20) :
    (BitVec.zeroExtend 64
      (BitVec.truncate 32 (BitVec.ofNat 64 n) - BitVec.truncate 32 (BitVec.ofNat 64 pad))) &&& 15#64 =
      BitVec.ofNat 64 ((n - pad) % 16) := by
  have ht : ∀ k, k ≤ 20 → BitVec.truncate 32 (BitVec.ofNat 64 k) = BitVec.ofNat 32 k := by
    intro k hk; apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (show k < 2 ^ 32 by omega)]
  have hs : BitVec.ofNat 32 n - BitVec.ofNat 32 pad = BitVec.ofNat 32 (n - pad) := by
    have h : BitVec.ofNat 32 n = BitVec.ofNat 32 (n - pad) + BitVec.ofNat 32 pad := by
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel hpad]
    rw [h, BitVec.add_sub_cancel]
  have hz : BitVec.zeroExtend 64 (BitVec.ofNat 32 (n - pad)) = BitVec.ofNat 64 (n - pad) := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (show n - pad < 2 ^ 32 by omega)]
  rw [ht n hn, ht pad (by omega), hs, hz]
  bv_bits

def hbMemrchrSlots (s : State) (ret_pc : BitVec 64) : SepProp :=
  ((s.sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((s.sp - 8#64) ↦₆₄ ret_pc)

theorem hbMemrchrEntry_to_3c_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc slicePtr : BitVec 64} {bs : List (BitVec 8)}
    (ro : Bool) (hc : HbStdoutCode P C) {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hbs_lo : 1 ≤ bs.length) (hbs_hi : bs.length ≤ 20)
    (hpc : s.pc = C.memrchrAddr) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hw0 : s.readReg32 .x0 = 0x0a#32) (hx1 : s.readReg64 .x1 = slicePtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (hbBytesSlice ro slicePtr bs ∗ stackAt s.sp 16) ∗ (F ∗ R)))
    (hbody : ∀ (r b : Nat) (st : State),
      r ≤ bs.length → (r = b ∨ (b ≤ 7 ∧ r = b + 16 ∧ 16 ≤ bs.length)) →
      st.pc = C.memrchrAddr + 0x3c#64 → st.status = .Running →
      st.sp = s.sp - 16#64 →
      st.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      st.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
      st.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
      st.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
      st.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
      st.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
      st.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
      st.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
      st.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
      st.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
      calleeSavedVRegs st = calleeSavedVRegs s →
      st.readReg64 .x0 = BitVec.ofNat 64 r →
      st.readReg64 .x1 = slicePtr →
      st.readReg64 .x2 = BitVec.ofNat 64 bs.length →
      st.readReg64 .x8 = 0x0a#64 →
      st.readReg64 .x10 = BitVec.ofNat 64 b →
      st.fs = s.fs → st.tpidrEl0 = s.tpidrEl0 → st.trace = s.trace →
      SepWP (P.withSvc hbStdioSvc) target_pc st
        (hbMemrchrSlots s ret_pc ∗ hbBytesSlice ro slicePtr bs ∗ F) post oom) :
    SepWP (P.withSvc hbStdioSvc) target_pc s Pre post oom := by
  have hcMr := (hc.withSvc hbStdioSvc).memrchr
  unpack_stdout_code hbMemrchrChunks hcMr
  obtain ⟨pad, hpad_le, hpad_eq⟩ := align8_pad slicePtr
  have hw0' : BitVec.truncate 32 (s.readReg64 (.gpr 0#5)) = 0x0a#32 := hw0
  refine SepWP.weaken_pre_frame
    (P' := stackAt s.sp 16 ∗ (hbBytesSlice ro slicePtr bs ∗ F))
    (fun R hm => by have hm' := hpre R hm; exact (by sep_entail : _ → _) hm') ?_
  conv => arg 4; rw [stackAt_eq_cells s.sp 2]
  simp only [Nat.reduceMul]
  cells_unfold
  simp only [sepExists_sepConj_left]
  iterate 2 (apply SepWP.exists_left; intro _)
  wp_steps
  by_cases hlt : bs.length < pad
  · have hult : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 pad) = true := by
      rw [bv64_ult_ofNat (by omega) (by omega)]; exact decide_eq_true hlt
    rw [hult]; simp only [↓reduceIte]
    refine SepWP.weaken_pre ?_ (hbody bs.length bs.length _ (Nat.le_refl _) (Or.inl rfl)
      wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
      ⟨wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm]⟩
      wp_a wp_a wp_a wp_a wp_a (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))
    dsimp only [hbMemrchrSlots]; sep_entail
  · have hpad : pad ≤ bs.length := by omega
    have hult : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 pad) = false := by
      rw [bv64_ult_ofNat (by omega) (by omega)]; exact decide_eq_false hlt
    have hand := sub32_and15_ofNat hpad hbs_hi
    have hsub_r : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 ((bs.length - pad) % 16) =
        BitVec.ofNat 64 (bs.length - (bs.length - pad) % 16) := bv64_sub_ofNat (by omega)
    have hult2 : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 ((bs.length - pad) % 16)) = false := by
      rw [bv64_ult_ofNat (by omega) (by omega)]; exact decide_eq_false (by omega)
    rw [hult]; simp only [Bool.false_eq_true, ↓reduceIte]
    wp_steps 5
    refine SepWP.weaken_pre ?_ (hbody (bs.length - (bs.length - pad) % 16) pad _ (by omega)
      (by by_cases h16 : bs.length - pad < 16
          · left; omega
          · right; exact ⟨hpad_le, by omega, by omega⟩)
      wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
      ⟨wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm]⟩
      wp_a wp_a wp_a wp_a wp_a (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))
    dsimp only [hbMemrchrSlots]; sep_entail

theorem bv64_ofNat_beq_zero {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = decide (n = 0) := by
  by_cases h : n = 0
  · subst h; rfl
  · simp only [decide_eq_false h, beq_eq_false_iff_ne]; intro heq
    have := congrArg BitVec.toNat heq; simp [Nat.mod_eq_of_lt hn] at this; exact h this

theorem hbMemrchr_nlEnd_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp0 slicePtr : BitVec 64} {bs : List (BitVec 8)}
    (hc : HbStdoutCode P C) {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hbs_lo : 1 ≤ bs.length) (hbs_hi : bs.length ≤ 15)
    (hlast : bs.getD (bs.length - 1) 0#8 = 0x0a#8)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ ((slicePtr ↦ᵣ bs) ∗ stackAt sp0 16) ∗ (F ∗ R)))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 1#64 → sf.readReg64 .x1 = BitVec.ofNat 64 (bs.length - 1) →
      sf.fs = s.fs → sf.tpidrEl0 = s.tpidrEl0 → sf.trace = s.trace →
      SepWP (P.withSvc hbStdioSvc) target_pc sf
        (((slicePtr ↦ᵣ bs) ∗ stackAt sp0 16) ∗ F) post oom)
    (hpc : s.pc = C.memrchrAddr := by wp_arg)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp : s.sp = sp0 := by wp_arg) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc := by wp_arg)
    (hw0 : s.readReg32 .x0 = 0x0a#32 := by wp_arg)
    (hx1 : s.readReg64 .x1 = slicePtr := by wp_arg)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length := by wp_arg) :
    SepWP (P.withSvc hbStdioSvc) target_pc s Pre post oom := by
  subst hsp
  have hcMr := (hc.withSvc hbStdioSvc).memrchr
  unpack_stdout_code hbMemrchrChunks hcMr
  refine hbMemrchrEntry_to_3c_wp true hc hbs_lo (by omega) hpc hrun hsp_align hlr hw0 hx1 hx2
    (by dsimp only [hbBytesSlice]; exact hpre)
    fun r b st0 hr_le hrb hpc0 hrun0 hsp0 hcs0 hx0_0 hx1_0 hx2_0 hx8_0 hx10_0 hfs0 htid0 htr0 => ?_
  rcases hrb with rfl | ⟨_, _, h16⟩; case inr => omega
  dsimp only [hbBytesSlice, hbMemrchrSlots]
  have hsp0_al : st0.spAligned = true := by
    simp only [State.spAligned, hsp0]; exact s.spAligned_sub 16#64 hsp_align
  have hsub_r : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 r = BitVec.ofNat 64 (bs.length - r) :=
    bv64_sub_ofNat hr_le
  have hsub_1 : BitVec.ofNat 64 bs.length - 1#64 = BitVec.ofNat 64 (bs.length - 1) :=
    bv64_sub_ofNat hbs_lo
  have hcomm : BitVec.ofNat 64 bs.length + slicePtr = slicePtr + BitVec.ofNat 64 bs.length :=
    BitVec.add_comm _ _
  have hlast' : bs.getD (Nat.sub bs.length 1) 0#8 = 0x0a#8 := hlast
  rcases hcs0 with ⟨hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩
  wp_steps 7
  by_cases hr_eq : r = bs.length
  · subst hr_eq
    simp only [Nat.sub_self, beq_self_eq_true, ↓reduceIte]
    have hnz : (BitVec.ofNat 64 bs.length == 0#64) = false := by
      rw [bv64_ofNat_beq_zero (by omega)]; exact decide_eq_false (by omega)
    have hule_self : BitVec.ule (BitVec.ofNat 64 bs.length) (BitVec.ofNat 64 bs.length) = true := by
      simp [BitVec.ule]
    have hult_self : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 bs.length) = false := by
      simp [BitVec.ult]
    wp_steps 20
    refine SepWP.weaken_pre_frame
      (P' := ((slicePtr ↦ᵣ bs) ∗ stackAt s.sp 16) ∗ F)
      (fun _ hm => by rw [stackAt_eq_cells s.sp 2]; exact (by repack_cells : _ → _) hm) ?_
    exact hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun0]) wp_a (by close_cs)
      wp_a wp_a (by simp [wp_norm, arm64_norm, hfs0])
      (by simp [wp_norm, arm64_norm, htid0]) (by simp [wp_norm, arm64_norm, htr0])
  · have hnz : (BitVec.ofNat 64 (bs.length - r) == 0#64) = false := by
      rw [bv64_ofNat_beq_zero (by omega)]; exact decide_eq_false (by omega)
    rw [hnz]; simp only [Bool.false_eq_true, ↓reduceIte]
    wp_steps 8
    refine SepWP.weaken_pre_frame
      (P' := ((slicePtr ↦ᵣ bs) ∗ stackAt s.sp 16) ∗ F)
      (fun _ hm => by rw [stackAt_eq_cells s.sp 2]; exact (by repack_cells : _ → _) hm) ?_
    exact hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun0]) wp_a (by close_cs)
      wp_a wp_a (by simp [wp_norm, arm64_norm, hfs0])
      (by simp [wp_norm, arm64_norm, htid0]) (by simp [wp_norm, arm64_norm, htr0])

def hbStdoutLockSlots (s : State) (ret_pc vPad : BitVec 64) : SepProp :=
  ((s.sp - 64#64) ↦₆₄ s.readReg64 .fp) ∗ ((s.sp - 56#64) ↦₆₄ ret_pc) ∗
  ((s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗ ((s.sp - 40#64) ↦₆₄ vPad) ∗
  ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((s.sp - 24#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
  ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5))

theorem hbStdoutLockEpilogue_14c_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc vPad ptrSlot g bufPtr slicePtr : BitVec 64} {newBuf bs fl : List (BitVec 8)}
    (ro : Bool) (hc : HbStdoutCode P C) {s st : State} {Pcur F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc_t : st.pc = C.stdoutLockWriteAllAddr + 0x14c#64) (hrun_t : st.status = .Running)
    (hsp_t : st.sp = s.sp - 64#64) (hsp_align : s.spAligned = true)
    (hcs_hi : st.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
      st.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
      st.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
      st.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
      st.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
      calleeSavedVRegs st = calleeSavedVRegs s)
    (hx0_t : st.readReg64 .x0 = 0#64) (hx22_t : st.readReg64 (.gpr 22#5) = g)
    (hfs_t : st.fs = s.fs) (htid_t : st.tpidrEl0 = s.tpidrEl0)
    (htr_t : st.trace = s.trace ++ TraceEvent.ofBytes .stdout fl)
    (hpre_t : ∀ R : SepProp, st.mem ⊨ Pcur ∗ R →
      st.mem ⊨ (hbStdoutLockSlots s ret_pc vPad ∗ stackAt (s.sp - 64#64) 192 ∗
        (ptrSlot ↦₆₄ g) ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        ((g + 0x10#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        hbBufWriterState (g + 0x18#64) bufPtr 0#8 newBuf ∗
        hbBytesSlice ro slicePtr bs ∗ F) ∗ R)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 → sf.fs = s.fs → sf.tpidrEl0 = s.tpidrEl0 →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stdout fl →
      SepWP (P.withSvc hbStdioSvc) target_pc sf
        (((ptrSlot ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr newBuf ∗ hbBytesSlice ro slicePtr bs ∗
          stackAt s.sp 256) ∗ F) post oom) :
    SepWP (P.withSvc hbStdioSvc) target_pc st Pcur post oom := by
  have hcLw := (hc.withSvc hbStdioSvc).stdoutLockWriteAll
  unpack_stdout_code hbStdoutLockWriteAllChunks hcLw
  have hsp_t_al : st.spAligned = true := by
    simp only [State.spAligned, hsp_t]; exact s.spAligned_sub 64#64 hsp_align
  refine SepWP.weaken_pre_frame
    (P' := hbStdoutLockSlots s ret_pc vPad ∗ stackAt (s.sp - 64#64) 192 ∗
      (ptrSlot ↦₆₄ g) ∗
      (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
      ((g + 0x10#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      hbBufWriterState (g + 0x18#64) bufPtr 0#8 newBuf ∗
      hbBytesSlice ro slicePtr bs ∗ F)
    (fun R hm => by have h := hpre_t R hm; exact (by sep_entail : _ → _) h) ?_
  dsimp only [hbStdoutLockSlots]
  wp_steps; wp_steps
  refine SepWP.weaken_pre_frame
    (P' := ((ptrSlot ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr newBuf ∗ hbBytesSlice ro slicePtr bs ∗
      stackAt s.sp 256) ∗ F)
    (fun _ hm => by
      dsimp only [hbStdoutRefCell]
      rw [show (256 : Nat) = 64 + 192 from rfl, stackAt_split 64 192, stackAt_eq_cells s.sp 8]
      exact (by repack_cells : _ → _) hm) ?_
  rcases hcs_hi with ⟨hc24, hc25, hc26, hc27, hc28, hcv⟩
  exact hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun_t]) wp_a
    (by close_cs) (by simp [wp_norm, arm64_norm, hx0_t])
    (by simp [wp_norm, arm64_norm, hfs_t]) (by simp [wp_norm, arm64_norm, htid_t])
    (by simp [wp_norm, arm64_norm, htr_t])

theorem hbStdoutLockEntry_to_34_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc ptrSlot g bufPtr slicePtr : BitVec 64} {buffered bs : List (BitVec 8)}
    (ro : Bool) (hc : HbStdoutCode P C) {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = C.stdoutLockWriteAllAddr) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptrSlot) (hx1 : s.readReg64 .x1 = slicePtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ ((ptrSlot ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr buffered ∗ hbBytesSlice ro slicePtr bs ∗
        stackAt s.sp 256) ∗ (F ∗ R)))
    (hbody : ∀ (vPad : BitVec 64) (st : State),
      st.pc = C.memrchrAddr → st.status = .Running →
      st.sp = s.sp - 64#64 →
      st.readReg64 Reg.lr = C.stdoutLockWriteAllAddr + 0x38#64 →
      st.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
      st.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
      st.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
      st.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
      st.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
      calleeSavedVRegs st = calleeSavedVRegs s →
      st.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length →
      st.readReg64 (.gpr 20#5) = slicePtr →
      st.readReg64 (.gpr 22#5) = g →
      st.readReg32 .x0 = 0x0a#32 →
      st.readReg64 .x1 = slicePtr →
      st.readReg64 .x2 = BitVec.ofNat 64 bs.length →
      st.fs = s.fs → st.tpidrEl0 = s.tpidrEl0 → st.trace = s.trace →
      SepWP (P.withSvc hbStdioSvc) target_pc st
        (hbStdoutLockSlots s ret_pc vPad ∗ stackAt (s.sp - 64#64) 192 ∗
          (ptrSlot ↦₆₄ g) ∗
          (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
          ((g + 0x10#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          hbBufWriterState (g + 0x18#64) bufPtr 0#8 buffered ∗
          hbBytesSlice ro slicePtr bs ∗ F) post oom) :
    SepWP (P.withSvc hbStdioSvc) target_pc s Pre post oom := by
  have hcLw := (hc.withSvc hbStdioSvc).stdoutLockWriteAll
  unpack_stdout_code hbStdoutLockWriteAllChunks hcLw
  refine SepWP.weaken_pre_frame
    (P' := stackAt s.sp 64 ∗ (stackAt (s.sp - 64#64) 192 ∗ (ptrSlot ↦₆₄ g) ∗
      hbStdoutRefCell C g bufPtr buffered ∗ hbBytesSlice ro slicePtr bs ∗ F))
    (fun R hm => by
      have hm' := hpre R hm
      rw [show (256 : Nat) = 64 + 192 from rfl, stackAt_split 64 192] at hm'
      exact (by sep_entail : _ → _) hm') ?_
  conv => arg 4; rw [stackAt_eq_cells s.sp 8]
  simp only [Nat.reduceMul]
  cells_unfold
  simp only [sepExists_sepConj_left]
  iterate 3 (apply SepWP.exists_left; intro _)
  apply SepWP.exists_left; intro vPad
  iterate 4 (apply SepWP.exists_left; intro _)
  dsimp only [hbStdoutRefCell, hbBufWriterState]
  wp_steps; norm_jmp
  refine SepWP.weaken_pre ?_ (hbody vPad _ wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a wp_a
    ⟨wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm]⟩
    wp_a wp_a wp_a wp_a wp_a wp_a (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))
  dsimp only [hbStdoutLockSlots, hbBufWriterState]; sep_entail

theorem hbStdoutLockWriteAll_nlEnd_stdioSvc_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp0 ptrSlot g bufPtr slicePtr : BitVec 64} {buffered bs : List (BitVec 8)}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C)
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hbs_lo : 1 ≤ bs.length) (hbs_hi : bs.length ≤ 15)
    (hlast : bs.getD (bs.length - 1) 0#8 = 0x0a#8) (hbuf_hi : buffered.length ≤ 1024)
    (hbuf_va : bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT)
    (hslice_va : slicePtr.toNat + bs.length ≤ Arm64.USER_VA_LIMIT)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ ((ptrSlot ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr buffered ∗ (slicePtr ↦ᵣ bs) ∗
        stackAt sp0 256) ∗ (F ∗ R)))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 → sf.fs = s.fs → sf.tpidrEl0 = s.tpidrEl0 →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stdout (buffered ++ bs) →
      SepWP (P.withSvc hbStdioSvc) target_pc sf
        (((ptrSlot ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr [] ∗ (slicePtr ↦ᵣ bs) ∗ stackAt sp0 256) ∗ F) post oom)
    (hpc : s.pc = C.stdoutLockWriteAllAddr := by wp_arg)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp : s.sp = sp0 := by wp_arg) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc := by wp_arg)
    (hx0 : s.readReg64 .x0 = ptrSlot := by wp_arg) (hx1 : s.readReg64 .x1 = slicePtr := by wp_arg)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length := by wp_arg) :
    SepWP (P.withSvc hbStdioSvc) target_pc s Pre post oom := by
  subst hsp
  have hcLw := (hc.withSvc hbStdioSvc).stdoutLockWriteAll
  unpack_stdout_code hbStdoutLockWriteAllChunks hcLw
  refine hbStdoutLockEntry_to_34_wp true hc hpc hrun hsp_align hlr hx0 hx1 hx2
    (by dsimp only [hbBytesSlice]; exact hpre)
    fun vPad st0 hpc0 hrun0 hsp0 hlr0 hcs0 hx19_0 hx20_0 hx22_0 hw0_0 hx1_0 hx2_0 hfs0 htid0 htr0 => ?_
  dsimp only [hbBytesSlice]
  have h114 : ∀ (s2 : State) (P2 : SepProp),
      s2.pc = C.stdoutLockWriteAllAddr + 0x114#64 → s2.status = .Running →
      s2.sp = s.sp - 64#64 →
      (s2.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
       s2.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
       s2.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
       s2.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
       s2.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
       calleeSavedVRegs s2 = calleeSavedVRegs s) →
      s2.readReg64 (.gpr 19#5) = 0#64 → s2.readReg64 (.gpr 20#5) = slicePtr →
      s2.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length → s2.readReg64 (.gpr 22#5) = g →
      s2.fs = s.fs → s2.tpidrEl0 = s.tpidrEl0 →
      s2.trace = s.trace ++ TraceEvent.ofBytes .stdout (buffered ++ bs) →
      (∀ R, s2.mem ⊨ P2 ∗ R → s2.mem ⊨ (hbStdoutLockSlots s ret_pc vPad ∗ stackAt (s.sp - 64#64) 192 ∗
        (ptrSlot ↦₆₄ g) ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        ((g + 0x10#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        hbBufWriterState (g + 0x18#64) bufPtr 0#8 [] ∗ (slicePtr ↦ᵣ bs) ∗ F) ∗ R) →
      SepWP (P.withSvc hbStdioSvc) target_pc s2 P2 post oom := by
    intro s2 P2 hpc2 hrun2 hsp2 hcs2 hx19_2 hx20_2 hx21_2 hx22_2 hfs2 htid2 htr2 hpre2
    have hsp2_al : s2.spAligned = true := by
      simp only [State.spAligned, hsp2]; exact s.spAligned_sub 64#64 hsp_align
    refine SepWP.weaken_pre_frame
      (P' := hbStdoutLockSlots s ret_pc vPad ∗ stackAt (s.sp - 64#64) 192 ∗
        (ptrSlot ↦₆₄ g) ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        ((g + 0x10#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        hbBufWriterState (g + 0x18#64) bufPtr 0#8 [] ∗ (slicePtr ↦ᵣ bs) ∗ F)
      (fun R hm => by have h := hpre2 R hm; exact (by sep_entail : _ → _) h) ?_
    dsimp only [hbBufWriterState, List.length_nil]
    wp_steps; norm_jmp
    refine call_hbMemcpy true hMem (sp0 := s.sp - 64#64) (dst := bufPtr)
      (src := slicePtr + BitVec.ofNat 64 bs.length) (bs := [])
      (ret_pc := C.stdoutLockWriteAllAddr + 0x140#64) (by decide)
      (fun R hm => by
        simp only [hbBytesSlice, List.length_nil, memRegion_zero, pointsToBytesRO_nil, emp_sepConj]
        sep_frame)
      (fun s3 hpc3 hrun3 hsp3 hcs23 hx0_3 hstd23 => ?_)
    have hsp3_al : s3.spAligned = true := by
      simp only [State.spAligned, hsp3]; exact s.spAligned_sub 64#64 hsp_align
    have hx19_3 : s3.readReg64 (.gpr 19#5) = 0#64 := by rw [hcs23.1]; exact wp_a
    have hx22_3 : s3.readReg64 (.gpr 22#5) = g := by rw [hcs23.2.2.2.1]; exact wp_a
    have hx23_3 : s3.readReg64 (.gpr 23#5) = 0#64 := by rw [hcs23.2.2.2.2.1]; exact wp_a
    simp only [hbBytesSlice, pointsToBytes_nil, pointsToBytesRO_nil, emp_sepConj]
    wp_steps 3
    refine hbStdoutLockEpilogue_14c_wp (ptrSlot := ptrSlot) (g := g) (bufPtr := bufPtr) (slicePtr := slicePtr)
      (newBuf := []) (bs := bs) (fl := buffered ++ bs)
      true hc wp_a (by simp [wp_norm, arm64_norm, hrun3]) wp_a hsp_align
      (by rcases hcs2 with ⟨_, _, _, _, _, _⟩; unpack_cs hcs23
          exact ⟨wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm, *]⟩)
      wp_a wp_a (by simp [wp_norm, arm64_norm, hstd23.1, hfs2])
      (by simp [wp_norm, arm64_norm, hstd23.2.2.1, htid2])
      (by simp [wp_norm, arm64_norm, hstd23.2.1, htr2])
      (fun R hm => by
        simp only [hbBufWriterState, hbBytesSlice, List.length_nil, Nat.sub_zero,
          pointsToBytes_nil, emp_sepConj]; sep_frame)
      fun sf hpcf hrunf hspf hcsf hx0f hfsf htidf htrf => ?_
    dsimp only [hbBytesSlice]
    exact hnext sf hpcf hrunf hspf hcsf hx0f hfsf htidf htrf
  have hsp0_al : st0.spAligned = true := by
    simp only [State.spAligned, hsp0]; exact s.spAligned_sub 64#64 hsp_align
  refine hbMemrchr_nlEnd_wp hc hbs_lo hbs_hi hlast (sp0 := s.sp - 64#64) (slicePtr := slicePtr) (bs := bs)
    (ret_pc := C.stdoutLockWriteAllAddr + 0x38#64)
    (fun R hm => by rw [show (192 : Nat) = 16 + 176 from rfl, stackAt_split 16 176] at hm; sep_frame)
    (fun s1 hpc1 hrun1 hsp1 hcs01 hx0_1 hx1_1 hfs1 htid1 htr1 => ?_)
    hpc0 hrun0 hsp0 hsp0_al hlr0 hw0_0 hx1_0 hx2_0
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1]; exact s.spAligned_sub 64#64 hsp_align
  have hx0_1' : s1.readReg64 (.gpr 0#5) = 1#64 := hx0_1
  have hx1_1' : s1.readReg64 (.gpr 1#5) = BitVec.ofNat 64 (bs.length - 1) := hx1_1
  have hx19_1 : s1.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length := by rw [hcs01.1]; exact hx19_0
  have hx20_1 : s1.readReg64 (.gpr 20#5) = slicePtr := by rw [hcs01.2.1]; exact hx20_0
  have hx22_1 : s1.readReg64 (.gpr 22#5) = g := by rw [hcs01.2.2.2.1]; exact hx22_0
  have hcs1 :
      s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
      s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
      s1.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
      s1.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
      s1.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s := by
    rcases hcs0 with ⟨_, _, _, _, _, _⟩; unpack_cs hcs01
    exact ⟨by simp_all, by simp_all, by simp_all, by simp_all, by simp_all, by simp_all⟩
  have hadd_1 : BitVec.ofNat 64 (bs.length - 1) + 1#64 = BitVec.ofNat 64 bs.length := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add,
        Nat.sub_add_cancel hbs_lo]
  have hult_self : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 bs.length) = false := by
    simp [BitVec.ult]
  have hsub_self : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 bs.length = 0#64 :=
    BitVec.sub_self _
  refine SepWP.weaken_pre_frame
    (P' := hbStdoutLockSlots s ret_pc vPad ∗ stackAt (s.sp - 64#64) 192 ∗
      (ptrSlot ↦₆₄ g) ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
      ((g + 0x10#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      hbBufWriterState (g + 0x18#64) bufPtr 0#8 buffered ∗ (slicePtr ↦ᵣ bs) ∗ F)
    (fun R hm => by rw [show (192 : Nat) = 16 + 176 from rfl, stackAt_split 16 176]; sep_entail) ?_
  dsimp only [hbBufWriterState]
  wp_steps 7
  by_cases hbuf0 : buffered = []
  · subst hbuf0
    simp only [List.length_nil, beq_self_eq_true, ↓reduceIte]
    wp_steps; norm_jmp
    refine hbStdoutRawWriteAll_stdioSvc_wp true hc hcSys hbs_lo
      (by simp only [Arm64.MAX_RW_COUNT]; omega) hslice_va
      (sp0 := s.sp - 64#64) (slicePtr := slicePtr) (bs := bs)
      (ret_pc := C.stdoutLockWriteAllAddr + 0xf4#64)
      (fun R hm => by
        rw [show (192 : Nat) = 144 + 48 from rfl, stackAt_split 144 48] at hm
        dsimp only [hbBytesSlice]; sep_frame)
      (fun sr hpcr hrunr hspr hcs1r hx0r hfsr htidr htrr => ?_)
    have hspr_al : sr.spAligned = true := by
      simp only [State.spAligned, hspr]; exact s.spAligned_sub 64#64 hsp_align
    have hx0r' : sr.readReg64 (.gpr 0#5) = 0#64 := hx0r
    wp_steps 1
    refine h114 _ _ wp_a (by simp [wp_norm, arm64_norm, hrunr]) wp_a
      (by rcases hcs1 with ⟨_, _, _, _, _, _⟩; unpack_cs hcs1r
          exact ⟨wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm, *]⟩)
      (by rw [State.readReg64_setPC, hcs1r.1]; exact wp_a)
      (by rw [State.readReg64_setPC, hcs1r.2.1]; exact wp_a)
      (by rw [State.readReg64_setPC, hcs1r.2.2.1]; exact wp_a)
      (by rw [State.readReg64_setPC, hcs1r.2.2.2.1]; exact wp_a)
      (by simp [wp_norm, arm64_norm, hfsr, hfs1, hfs0]) (by simp [wp_norm, arm64_norm, htidr, htid1, htid0])
      (by simp [wp_norm, arm64_norm, htrr, htr1, htr0])
      (fun R hm => by
        rw [show (192 : Nat) = 144 + 48 from rfl, stackAt_split 144 48]
        dsimp only [hbBufWriterState, hbBytesSlice, List.length_nil] at hm ⊢; sep_frame)
  · have hbuf_pos : 1 ≤ buffered.length := List.length_pos_iff.mpr hbuf0
    have hbeq0 : (BitVec.ofNat 64 buffered.length == 0#64) = false := by
      rw [bv64_ofNat_beq_zero (by omega)]; exact decide_eq_false (by omega)
    have hsub_cap : 1024#64 - BitVec.ofNat 64 buffered.length = BitVec.ofNat 64 (1024 - buffered.length) :=
      bv64_sub_ofNat hbuf_hi
    have h80 : ∀ (fl1 midBuf : List (BitVec 8)) (sm : State) (Pm : SepProp),
        1 ≤ midBuf.length → midBuf.length ≤ 1024 → fl1 ++ midBuf = buffered ++ bs →
        sm.pc = C.stdoutLockWriteAllAddr + 0x80#64 → sm.status = .Running →
        sm.sp = s.sp - 64#64 →
        (sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
         sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
         sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
         sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
         sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) →
        sm.readReg64 (.gpr 19#5) = 0#64 → sm.readReg64 (.gpr 20#5) = slicePtr →
        sm.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length → sm.readReg64 (.gpr 22#5) = g →
        sm.fs = s.fs → sm.tpidrEl0 = s.tpidrEl0 →
        sm.trace = s.trace ++ TraceEvent.ofBytes .stdout fl1 →
        (∀ R, sm.mem ⊨ Pm ∗ R → sm.mem ⊨ (hbStdoutLockSlots s ret_pc vPad ∗ stackAt (s.sp - 64#64) 192 ∗
          (ptrSlot ↦₆₄ g) ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
          ((g + 0x10#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          hbBufWriterState (g + 0x18#64) bufPtr 0#8 midBuf ∗ (slicePtr ↦ᵣ bs) ∗ F) ∗ R) →
        SepWP (P.withSvc hbStdioSvc) target_pc sm Pm post oom := by
      intro fl1 midBuf sm Pm hmlo hmhi hcat hpcm hrunm hspm hcsm hx19m hx20m hx21m hx22m hfsm htidm htrm hprem
      have hspm_al : sm.spAligned = true := by
        simp only [State.spAligned, hspm]; exact s.spAligned_sub 64#64 hsp_align
      refine SepWP.weaken_pre_frame
        (P' := hbStdoutLockSlots s ret_pc vPad ∗ stackAt (s.sp - 64#64) 192 ∗
          (ptrSlot ↦₆₄ g) ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
          ((g + 0x10#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          hbBufWriterState (g + 0x18#64) bufPtr 0#8 midBuf ∗ (slicePtr ↦ᵣ bs) ∗ F)
        (fun R hm => by have h := hprem R hm; exact (by sep_entail : _ → _) h) ?_
      wp_steps; norm_jmp
      refine hbBufWriterFlush_state_wp hc hcSys hMemmove hmlo hmhi hbuf_va
        (sp0 := s.sp - 64#64) (bwPtr := g + 0x18#64) (bufPtr := bufPtr) (pan0 := 0#8) (buffered := midBuf)
        (ret_pc := C.stdoutLockWriteAllAddr + 0x88#64)
        (fun R hm => by rw [show (192 : Nat) = 144 + 48 from rfl, stackAt_split 144 48] at hm; sep_frame)
        (fun sf1 hpcf1 hrunf1 hspf1 hcsmf1 hx0f1 hfsf1 htidf1 htrf1 => ?_)
      have hspf1_al : sf1.spAligned = true := by
        simp only [State.spAligned, hspf1]; exact s.spAligned_sub 64#64 hsp_align
      have hx0f1' : sf1.readReg64 (.gpr 0#5) = 0#64 := hx0f1
      wp_steps 2
      exact h114 _ _ wp_a (by simp [wp_norm, arm64_norm, hrunf1]) wp_a
        (by rcases hcsm with ⟨_, _, _, _, _, _⟩; unpack_cs hcsmf1
            exact ⟨wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm, *]⟩)
        (by rw [State.readReg64_setPC, hcsmf1.1]; exact wp_a)
        (by rw [State.readReg64_setPC, hcsmf1.2.1]; exact wp_a)
        (by rw [State.readReg64_setPC, hcsmf1.2.2.1]; exact wp_a)
        (by rw [State.readReg64_setPC, hcsmf1.2.2.2.1]; exact wp_a)
        (by simp [wp_norm, arm64_norm, hfsf1, hfsm]) (by simp [wp_norm, arm64_norm, htidf1, htidm])
        (by simp [wp_norm, arm64_norm, htrf1, htrm, TraceEvent.ofBytes, ← List.map_append, hcat])
        (fun R hm => by rw [show (192 : Nat) = 144 + 48 from rfl, stackAt_split 144 48]; sep_frame)
    rw [hbeq0]; simp only [Bool.false_eq_true, ↓reduceIte]
    wp_steps 4
    by_cases hfit : bs.length < 1024 - buffered.length
    · have hule : BitVec.ule (BitVec.ofNat 64 (1024 - buffered.length)) (BitVec.ofNat 64 bs.length) = false := by
        rw [bv64_ule_ofNat (by omega) (by omega)]; exact decide_eq_false (by omega)
      rw [hule]; simp only [Bool.false_eq_true, ↓reduceIte]
      wp_steps; norm_jmp
      refine call_hbMemcpy true hMem (sp0 := s.sp - 64#64)
        (dst := bufPtr + BitVec.ofNat 64 buffered.length) (src := slicePtr) (bs := bs)
        (ret_pc := C.stdoutLockWriteAllAddr + 0x78#64) (by omega)
        (fun R hm => by
          rw [memRegion_split_le (bufPtr + BitVec.ofNat 64 buffered.length) bs.length
            (1024 - buffered.length) (by omega) (by omega)] at hm
          dsimp only [hbBytesSlice]; sep_frame)
        (fun sc hpcc hrunc hspc hcs1c hx0c hstd1c => ?_)
      have hspc_al : sc.spAligned = true := by
        simp only [State.spAligned, hspc]; exact s.spAligned_sub 64#64 hsp_align
      have hx19c : sc.readReg64 (.gpr 19#5) = 0#64 := by rw [hcs1c.1]; exact wp_a
      have hx20c : sc.readReg64 (.gpr 20#5) = slicePtr := by rw [hcs1c.2.1]; exact wp_a
      have hx21c : sc.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length := by rw [hcs1c.2.2.1]; exact wp_a
      have hx22c : sc.readReg64 (.gpr 22#5) = g := by rw [hcs1c.2.2.2.1]; exact wp_a
      have hx23c : sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 buffered.length := by rw [hcs1c.2.2.2.2.1]; exact wp_a
      wp_steps 2
      refine h80 [] (buffered ++ bs) _ _ (by simp; omega) (by simp; omega) rfl
        wp_a (by simp [wp_norm, arm64_norm, hrunc]) wp_a
        (by rcases hcs1 with ⟨_, _, _, _, _, _⟩; unpack_cs hcs1c
            exact ⟨wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm, *]⟩)
        wp_a wp_a wp_a wp_a
        (by simp [wp_norm, arm64_norm, hstd1c.1, hfs1, hfs0]) (by simp [wp_norm, arm64_norm, hstd1c.2.2.1, htid1, htid0])
        (by simp [wp_norm, arm64_norm, hstd1c.2.1, htr1, htr0, TraceEvent.ofBytes])
        (fun R hm => by
          dsimp only [hbBufWriterState, hbBytesSlice] at hm ⊢
          rw [List.length_append, pointsToBytes_append, BitVec.ofNat_add, ← BitVec.add_assoc,
              show 1024 - (buffered.length + bs.length) = 1024 - buffered.length - bs.length by omega]
          sep_frame)
    · have hule : BitVec.ule (BitVec.ofNat 64 (1024 - buffered.length)) (BitVec.ofNat 64 bs.length) = true := by
        rw [bv64_ule_ofNat (by omega) (by omega)]; exact decide_eq_true (by omega)
      rw [hule]; simp only [↓reduceIte]
      wp_steps; norm_jmp
      refine hbBufWriterWriteAllCold_stdioSvc_wp true hc hcSys hMem hMemmove hbs_lo (by omega) hbuf_hi hbuf_va
        (sp0 := s.sp - 64#64) (bwPtr := g + 0x18#64) (bufPtr := bufPtr) (slicePtr := slicePtr)
        (buffered := buffered) (bs := bs) (ret_pc := C.stdoutLockWriteAllAddr + 0x1b8#64)
        (fun R hm => by dsimp only [hbBufWriterState, hbBytesSlice]; sep_frame)
        (fun sc hpcc hrunc hspc hcs1c hx0c hfsc htidc htrc => ?_)
      have hspc_al : sc.spAligned = true := by
        simp only [State.spAligned, hspc]; exact s.spAligned_sub 64#64 hsp_align
      have hx0c' : sc.readReg64 (.gpr 0#5) = 0#64 := hx0c
      wp_steps 2
      refine h80 (if bs.length ≤ 1024 - buffered.length then [] else buffered)
        (if bs.length ≤ 1024 - buffered.length then buffered ++ bs else bs) _ _
        (by split <;> (try simp) <;> omega) (by split <;> (try simp) <;> omega) (by split <;> simp)
        wp_a (by simp [wp_norm, arm64_norm, hrunc]) wp_a
        (by rcases hcs1 with ⟨_, _, _, _, _, _⟩; unpack_cs hcs1c
            exact ⟨wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm, *]⟩)
        (by rw [State.readReg64_setPC, hcs1c.1]; exact wp_a)
        (by rw [State.readReg64_setPC, hcs1c.2.1]; exact wp_a)
        (by rw [State.readReg64_setPC, hcs1c.2.2.1]; exact wp_a)
        (by rw [State.readReg64_setPC, hcs1c.2.2.2.1]; exact wp_a)
        (by simp [wp_norm, arm64_norm, hfsc, hfs1, hfs0]) (by simp [wp_norm, arm64_norm, htidc, htid1, htid0])
        (by simp [wp_norm, arm64_norm, htrc, htr1, htr0])
        (fun R hm => by dsimp only [hbBytesSlice] at hm; sep_frame)

def hbStdoutLockWriteAllNoneNlSpec (C : HbCliLayout) : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (ptrSlot, g, bufPtr) s0 =>
    ⌜s0.readReg64 .x0 = ptrSlot ∧ s0.readReg64 .x1 = C.noneNlAddr ∧ s0.readReg64 .x2 = 5#64 ∧
      bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT ∧ C.noneNlAddr.toNat + 5 ≤ Arm64.USER_VA_LIMIT⌝ ∗
    ((ptrSlot ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr [] ∗ (C.noneNlAddr ↦ᵣ noneNlBytes) ∗ stackAt s0.sp 256)
  post := fun (ptrSlot, g, bufPtr) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout noneNlBytes ∧
      FmtIoStatePreserved s0 sf ∧ HbNonVmPreserved s0 sf⌝ ∗
    ((ptrSlot ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr [] ∗ (C.noneNlAddr ↦ᵣ noneNlBytes) ∗ stackAt s0.sp 256)

theorem hbStdoutLockWriteAll_noneNl_ok {P : Program} {C : HbCliLayout}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C)
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.stdoutLockWriteAllAddr (hbStdoutLockWriteAllNoneNlSpec C) := by
  apply subroutine_ok_of_sepWP_stdioSvc hext hsvc
  intro (ptrSlot, g, bufPtr) R s0 hpc hrun hpre hsp
  dsimp only [hbStdoutLockWriteAllNoneNlSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbuf_va, hnone_va⟩, hmem⟩
  refine ⟨(ptrSlot ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr [] ∗ (C.noneNlAddr ↦ᵣ noneNlBytes) ∗ stackAt s0.sp 256,
    hmem, ?_⟩
  refine hbStdoutLockWriteAll_nlEnd_stdioSvc_wp (ptrSlot := ptrSlot) (g := g) (bufPtr := bufPtr)
    (buffered := []) (bs := noneNlBytes) (F := emp) hc hcSys hMem hMemmove
    (by decide) (by decide) (by decide) (by decide) hbuf_va hnone_va
    (fun R' hm' => by simpa [sepConj_emp, sepConj_assoc] using hm')
    (fun sf hpcf hrunf hspf hcsf hx0f hfsf htidf htrf => ?_)
    hpc hrun rfl hsp rfl hx0 hx1 hx2
  refine SepWP.done hpcf hrunf ⟨fun hpr hmf => ?_, hspf, hcsf⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0f, htrf, hpr.toFmtIo hfsf htidf, hpr.toHbNonVm htidf⟩,
    by simpa [sepConj_emp, sepConj_assoc] using hmf⟩


end CaseStudies.Hashbrown.Proofs.StdCli
