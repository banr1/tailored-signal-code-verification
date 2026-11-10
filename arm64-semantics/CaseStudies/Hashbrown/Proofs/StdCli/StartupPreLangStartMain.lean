/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.StartupPreLangStart
public import ProofLib.StdStartup.LangStartPre
public import ProofLib.SepLogic.WP.StepsProcessSyscalls
public import ProofLib.SepLogic.WP.StepsProcessLse
public import ProofLib.SepLogic.WP.StepsProcessLlsc
public import ProofLib.MallocngBridge
import ProofLib.StdStartup.StdDetect
import ProofLib.StdStartup.OutlineAtomics
import ProofLib.SyscallModels
import ProofLib.BV.Arith
import ProofLib.BV.WidthNorm
public meta import ProofLib.LiteralFetchLint

/-!
# Layout-Generic `c_main` to `userMain` Composition

Layout-generic symbolic execution from `C.std.cMainAddr` to `C.std.userMainAddr` across `c_main`,
`std::rt::lang_start_internal`, `make_handler`, `rt_sigaction`/`rt_sigprocmask`,
`sysconf(_SC_PAGESIZE)`, `lang_start::{{closure}}`, and `__rust_begin_short_backtrace`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup StdBinaryLayout

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term => `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAdr " rd:term:arg pc:term:arg t:term:arg : term => `(Instr.adr false $rd (($t) - ($pc)))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term => `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iLdr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.ldr .W64 .X64 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.str .X64 $rt (.Offset $rn (pageLo12 $t)))
local macro "iLdr32Lo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.ldr .W32 .W32 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr32Lo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.str .W32 $rt (.Offset $rn (pageLo12 $t)))
local macro "iLdr8Lo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.ldr .W32 .B8 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr8Lo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.str .B8 $rt (.Offset $rn (pageLo12 $t)))
local macro "iBl " pc:term:arg t:term:arg : term => `(Instr.bl (($t) - ($pc)))
local macro "iB " pc:term:arg t:term:arg : term => `(Instr.b (($t) - ($pc)))
local macro "hb_wp_simp" : tactic => `(tactic|
  simp (config := { decide := true }) [State.stepExclOracle, State.stepExclLoop, State.readReg32, wp_norm, arm64_norm, bv_lin_norm, *])

@[local simp] private theorem hbNonVm_w64_r (a b : State) (r : Reg) (v : BitVec 64) : HbNonVmFields a (b.writeReg64 r v) ↔ HbNonVmFields a b := by cases r <;> rfl
@[local simp] private theorem hbNonVm_w64_l (a b : State) (r : Reg) (v : BitVec 64) : HbNonVmFields (a.writeReg64 r v) b ↔ HbNonVmFields a b := by cases r <;> rfl
@[local simp] private theorem hbNonVm_w32_r (a b : State) (r : Reg) (v : BitVec 32) : HbNonVmFields a (b.writeReg32 r v) ↔ HbNonVmFields a b := by simp [State.writeReg32]
@[local simp] private theorem hbNonVm_w32_l (a b : State) (r : Reg) (v : BitVec 32) : HbNonVmFields (a.writeReg32 r v) b ↔ HbNonVmFields a b := by simp [State.writeReg32]
@[local simp] private theorem hbNonVm_pc_r (a b : State) (p : BitVec 64) : HbNonVmFields a (b.setPC p) ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_pc_l (a b : State) (p : BitVec 64) : HbNonVmFields (a.setPC p) b ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_mem_r (a b : State) (m : Memory) : HbNonVmFields a (b.setMem m) ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_mem_l (a b : State) (m : Memory) : HbNonVmFields (a.setMem m) b ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_ps_r (a b : State) (p : PState) : HbNonVmFields a (b.setPState p) ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_ps_l (a b : State) (p : PState) : HbNonVmFields (a.setPState p) b ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_adv_r (a b : State) : HbNonVmFields a b.advancePC ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_adv_l (a b : State) : HbNonVmFields a.advancePC b ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_excl_r (a b : State) : HbNonVmFields a b.stepExclOracle ↔ HbNonVmFields a b := by cases b; rfl
@[local simp] private theorem hbNonVm_excl_l (a b : State) : HbNonVmFields a.stepExclOracle b ↔ HbNonVmFields a b := by cases a; rfl
@[local simp] private theorem hbNonVm_exclLoop_r (a b : State) : HbNonVmFields a b.stepExclLoop ↔ HbNonVmFields a b := by cases b; rfl
@[local simp] private theorem hbNonVm_exclLoop_l (a b : State) : HbNonVmFields a.stepExclLoop b ↔ HbNonVmFields a b := by cases a; rfl

local macro "hb_nv_rfl " s:term : tactic => `(tactic|
  (simp only [hbNonVm_w64_r, hbNonVm_w32_r, hbNonVm_pc_r, hbNonVm_mem_r, hbNonVm_ps_r, hbNonVm_adv_r, hbNonVm_excl_r, hbNonVm_exclLoop_r]; exact HbNonVmFields.rfl $s))

private theorem sxtw_ofNat_norm {argc : Nat} (h : argc < 2 ^ 31) :
    (BitVec.ofNat 64 argc &&& 0xffffffff#64 |||
      (if (BitVec.ofNat 64 argc).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&& 0xffffffff00000000#64) = BitVec.ofNat 64 argc := by
  have h31 : (BitVec.ofNat 64 argc).getLsbD 31 = false := by
    dsimp [BitVec.getLsbD]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.testBit_lt_two_pow h
  rw [h31]; simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_and, BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (0xffffffff#64 : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

abbrev hbCMainInstrs (C : HbCliLayout) : List Instr :=
  let L := C.std; let ls := C.langStartInternalAddr
  decodeWords [0xd10083ff#32, 0x93407c02#32, 0xaa0103e3#32, 0xd503201f#32] ++
  [iAdr .x8 (L.cMainAddr + 0x10#64) L.userMainAddr, decodeWord 0xd503201f#32, iAdr .x1 (L.cMainAddr + 0x18#64) C.langStartVtableAddr] ++
  decodeWords [0x910023e0#32, 0x2a1f03e4#32, 0xa9017bfd#32, 0x910043fd#32, 0xf90007e8#32] ++ [iBl (L.cMainAddr + 0x30#64) ls]

section
arm64_proof_prelude

private theorem step_hb_cMain_to_langStart {P : Program} {C : HbCliLayout} {target_pc argvPtr : BitVec 64} {argc : Nat}
    (hc : hasInstrs P C.std.cMainAddr (hbCMainInstrs C)) (hargc : argc < 2 ^ 31)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ stackAt s.sp 0x20 ∗ (F ∗ R))
    (hpc : s.pc = C.std.cMainAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = C.std.libcStartMainStage2Addr + 0x38#64)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 argc) (hx1 : s.readReg64 .x1 = argvPtr)
    (hnext : ∀ (sf : State) (w_cm0 : BitVec 64),
      sf.pc = C.langStartInternalAddr → sf.status = .Running → sf.sp = s.sp - 0x20#64 → sf.spAligned = true →
      sf.readReg64 .lr = C.std.cMainAddr + 0x34#64 → sf.readReg64 .x29 = s.sp - 0x10#64 →
      sf.readReg64 .x0 = s.sp - 0x18#64 → sf.readReg64 .x1 = C.langStartVtableAddr →
      sf.readReg64 .x2 = BitVec.ofNat 64 argc → sf.readReg64 .x3 = argvPtr → sf.readReg64 .x4 = 0#64 →
      HbNonVmFields s sf → CalleeSavedPreserved (s.writeReg64 (.gpr 29#5) (s.sp - 0x10#64)) sf →
      SepWP P target_pc sf
        ((((s.sp - 0x20#64) ↦₆₄ w_cm0) ∗ ((s.sp - 0x18#64) ↦₆₄ C.std.userMainAddr) ∗
          ((s.sp - 0x10#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 0x08#64) ↦₆₄ (C.std.libcStartMainStage2Addr + 0x38#64))) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 0x20 ∗ F) (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have_instrs hc 0 13; clear hc
  have hlr' : s.readReg64 (.gpr 30#5) = C.std.libcStartMainStage2Addr + 0x38#64 := hlr
  have hx0' : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 argc := hx0
  have hx1' : s.readReg64 (.gpr 1#5) = argvPtr := hx1
  have hsp_sub_al : ((s.sp + 0xffffffffffffffe0#64) &&& 0xf#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align
  wp_conv_pre => rw [stackAt_eq_cells s.sp 4 (by decide)]
  unfold_stack_cells 4; wp_steps 12
  refine hb_step_bl_to (pc := C.std.cMainAddr + 48#64) (dst := C.langStartInternalAddr) (by hb_wp_simp) (by hb_wp_simp) hf_12 ?_
  refine hb_step_entail (hnext _ _ (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align)
    (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by simp only [wp_norm]; exact sxtw_ofNat_norm hargc)
    (by hb_wp_simp) (by hb_wp_simp) (by hb_nv_rfl s)
    (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, bv_lin_norm]))
    (fun R hm => by simp only [wp_norm, arm64_norm, bv_lin_norm] at hm ⊢; revert hm; sep_entail)

abbrev hbLangStartPollLoopWords : List (BitVec 32) :=
  [0x910003e8#32, 0xaa1f03fa#32, 0x12800019#32, 0xb27f051c#32, 0x8b1a0398#32, 0x9100235a#32,
   0x14000002#32, 0x9100235a#32, 0xf100835f#32, 0x54ffeea0#32, 0x78408708#32, 0x362fff88#32]
abbrev hbLangStartMid0Words : List (BitVec 32) :=
  [0x12001ee8#32, 0x52800021#32, 0x7100051f#32, 0x5400010c#32, 0x340001e8#32]

private theorem or_six_of_spAligned {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) : sp ||| 6#64 = sp + 6#64 := by
  simp only [beq_iff_eq] at h; bv_bits

@[local simp] private theorem cond_eq_subs8_32  : ConditionHolds .EQ (subsPState64 8#64 32#64) = false := by unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]
@[local simp] private theorem cond_eq_subs16_32 : ConditionHolds .EQ (subsPState64 16#64 32#64) = false := by unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]
@[local simp] private theorem cond_eq_subs24_32 : ConditionHolds .EQ (subsPState64 24#64 32#64) = false := by unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]
@[local simp] private theorem cond_eq_subs32_32 : ConditionHolds .EQ (subsPState64 32#64 32#64) = true := by unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]
@[local simp] private theorem cond_gt_neg1_1    : ConditionHolds .GT (subsPState32 0xffffffff#32 1#32) = false := by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide

private theorem step_hb_langStart_poll_loop {P : Program} {C : HbCliLayout} {target_pc mainFnSlot argvPtr : BitVec 64} {argc : Nat}
    (hloop : P.hasCode (C.langStartInternalAddr + 0x400#64) hbLangStartPollLoopWords)
    (hmid0 : P.hasCode (C.langStartInternalAddr + 0x1f8#64) hbLangStartMid0Words)
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = C.langStartInternalAddr + 0x400#64) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = mainFnSlot) (hx20 : s.readReg64 .x20 = argvPtr)
    (hx21 : s.readReg64 .x21 = C.langStartVtableAddr) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 argc)
    (hx23 : s.readReg64 .x23 = 0#64) (hx29 : s.readReg64 .x29 = s.sp + 0xa0#64)
    (hnext : ∀ sf : State,
      sf.pc = C.langStartInternalAddr + 0x244#64 → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      sf.readReg64 .x1 = 1#64 → sf.readReg64 .x19 = mainFnSlot → sf.readReg64 .x20 = argvPtr →
      sf.readReg64 .x21 = C.langStartVtableAddr → sf.readReg64 .x22 = BitVec.ofNat 64 argc →
      sf.readReg64 .x29 = s.sp + 0xa0#64 → HbNonVmFields s sf → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP P target_pc sf (((s.sp ↦₆₄ 0#64) ∗ ((s.sp + 8#64) ↦₆₄ 1#64) ∗ ((s.sp + 16#64) ↦₆₄ 2#64)) ∗ F) post oom) :
    SepWP P target_pc s (((s.sp ↦₆₄ 0#64) ∗ ((s.sp + 8#64) ↦₆₄ 1#64) ∗ ((s.sp + 16#64) ↦₆₄ 2#64)) ∗ F) post oom := by
  have hor6 : s.sp ||| 6#64 = s.sp + 6#64 := or_six_of_spAligned hsp_align
  have hx23' : s.readReg64 (.gpr 23#5) = 0#64 := hx23
  wp_conv_pre => rw [stdioPollfds_eq_bytes s.sp]
  wp_steps 24; clear hloop; wp_steps 5
  wp_conv_pre => rw [← stdioPollfds_eq_bytes s.sp]
  refine hb_step_entail (hnext _ (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align)
    (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    (by hb_nv_rfl s) (by hb_wp_simp)) (fun _ hm => hm)

@[local simp] private theorem cond_cmn1  : ConditionHolds .EQ (addsPState64 0#64 1#64) = false := by unfold addsPState64 ConditionHolds; dsimp [AddWithCarry64]
@[local simp] private theorem cond_cas0  : ConditionHolds .NE (subsPState64 0#64 0#64) = false := by unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]; decide
@[local simp] private theorem cond_poll0 : ConditionHolds .NE (addsPState32 0#32 1#32) = true := by unfold addsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide
@[local simp] private theorem tpidrEl0_w64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).tpidrEl0 = s.tpidrEl0 := rfl
@[local simp] private theorem tpidrEl0_pc (s : State) (p : BitVec 64) : (s.setPC p).tpidrEl0 = s.tpidrEl0 := rfl
@[local simp] private theorem tpidrEl0_mem (s : State) (m : Memory) : (s.setMem m).tpidrEl0 = s.tpidrEl0 := rfl

abbrev hbLangStartHeadInstrs (C : HbCliLayout) (S : HbStartupLayout) : List Instr :=
  let L := C.std; let ls := C.langStartInternalAddr
  decodeWords [0xd10403ff#32, 0xa90a7bfd#32, 0xa90b6ffc#32, 0xa90c67fa#32, 0xa90d5ff8#32, 0xa90e57f6#32, 0xa90f4ff4#32, 0x910283fd#32,
               0x2a0403f7#32, 0xaa0303f4#32, 0xaa0203f6#32, 0xaa0103f5#32, 0xaa0003f3#32, 0xd2a00000#32, 0xf2800b00#32, 0xd503201f#32,
               0xd503201f#32, 0xd53bd05b#32, 0xf8606b7c#32, 0xb500023c#32] ++
  [iAdrp .x8 (ls + 0x50#64) L.threadIdCounterAddr, decodeWord 0xaa0003f8#32, iAdrp .x25 (ls + 0x58#64) L.threadIdCounterAddr,
   iAddLo12 .x25 .x25 L.threadIdCounterAddr, iLdr64Lo12 .x26 .x8 L.threadIdCounterAddr] ++
  decodeWords [0xb100075f#32, 0x54002020#32, 0x91000741#32, 0xaa1a03e0#32, 0xaa1903e2#32, 0x9100075c#32] ++
  [iBl (ls + 0x7c#64) L.cas8RelaxAddr] ++ decodeWords [0xeb1a001f#32, 0xaa0003fa#32, 0x54fffee1#32, 0xf8386b7c#32] ++
  [iAdrp .x8 (ls + 0x90#64) S.mainThreadAddr, iStr64Lo12 .x28 .x8 S.mainThreadAddr] ++
  decodeWords [0x52800028#32, 0xa90023ff#32, 0x52800048#32, 0xf9000be8#32, 0x910003e0#32, 0x52800061#32, 0x2a1f03e2#32] ++
  [iBl (ls + 0xb4#64) L.pollAddr] ++ decodeWords [0x3100041f#32, 0x54001a21#32]

set_option maxHeartbeats 400000 in
private theorem step_hb_langStart_head {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc mainFnSlot argvPtr tp v_mt : BitVec 64} {haveLse : BitVec 8} {argc : Nat}
    (hhead : hasInstrs P C.langStartInternalAddr (hbLangStartHeadInstrs C S))
    (hloop : P.hasCode (C.langStartInternalAddr + 0x400#64) hbLangStartPollLoopWords)
    (hmid0 : P.hasCode (C.langStartInternalAddr + 0x1f8#64) hbLangStartMid0Words)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R →
      s.mem ⊨ (((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ (C.std.threadIdCounterAddr ↦₆₄ 0#64) ∗
        ((tp + 0x58#64) ↦₆₄ 0#64) ∗ (S.mainThreadAddr ↦₆₄ v_mt)) ∗ stackAt s.sp 0x140) ∗ (F ∗ R))
    (hpc : s.pc = C.langStartInternalAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = C.std.cMainAddr + 0x34#64) (hx0 : s.readReg64 .x0 = mainFnSlot) (hx1 : s.readReg64 .x1 = C.langStartVtableAddr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 argc) (hx3 : s.readReg64 .x3 = argvPtr) (hx4 : s.readReg64 .x4 = 0#64) (htp : s.tpidrEl0 = tp)
    (hcas8 : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.cas8RelaxAddr → s0.status = .Running → s0.sp = s.sp - 256#64 → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 128#64 → s0.readReg64 .x0 = 0#64 → s0.readReg64 .x1 = 1#64 → s0.readReg64 .x2 = C.std.threadIdCounterAddr →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 128#64 → s1.status = .Running → s1.sp = s0.sp →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields s0 s1 →
        SepWP P target_pc s1 (((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ (C.std.threadIdCounterAddr ↦₆₄ 1#64)) ∗ G) post oom) →
      SepWP P target_pc s0 (((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ (C.std.threadIdCounterAddr ↦₆₄ 0#64)) ∗ G) post oom)
    (hpoll : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.pollAddr → s0.status = .Running → s0.sp = s.sp - 256#64 → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 184#64 → s0.readReg64 .x0 = s0.sp → s0.readReg64 .x1 = 3#64 → s0.readReg64 .x2 = 0#64 → s0.fs = s.fs →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 184#64 → s1.status = .Running → s1.sp = s0.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields s0 s1 →
        SepWP P target_pc s1 ((((s0.sp ↦₆₄ 0#64) ∗ ((s0.sp + 8#64) ↦₆₄ 1#64) ∗ ((s0.sp + 16#64) ↦₆₄ 2#64)) ∗ stackAt s0.sp 0x40) ∗ G) post oom) →
      SepWP P target_pc s0 ((((s0.sp ↦₆₄ 0#64) ∗ ((s0.sp + 8#64) ↦₆₄ 1#64) ∗ ((s0.sp + 16#64) ↦₆₄ 2#64)) ∗ stackAt s0.sp 0x40) ∗ G) post oom)
    (hnext : ∀ sf : State,
      sf.pc = C.langStartInternalAddr + 0x244#64 → sf.status = .Running → sf.sp = s.sp - 256#64 → sf.spAligned = true →
      sf.readReg64 .x1 = 1#64 → sf.readReg64 .x19 = mainFnSlot → sf.readReg64 .x20 = argvPtr →
      sf.readReg64 .x21 = C.langStartVtableAddr → sf.readReg64 .x22 = BitVec.ofNat 64 argc →
      sf.readReg64 .x29 = s.sp - 96#64 → HbNonVmFields s sf → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP P target_pc sf
        ((((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ (C.std.threadIdCounterAddr ↦₆₄ 1#64) ∗ ((tp + 0x58#64) ↦₆₄ 1#64) ∗ (S.mainThreadAddr ↦₆₄ 1#64)) ∗
          (((s.sp - 96#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 88#64) ↦₆₄ (C.std.cMainAddr + 0x34#64)) ∗
           ((s.sp - 80#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗ ((s.sp - 72#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
           ((s.sp - 64#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((s.sp - 56#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
           ((s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((s.sp - 40#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
           ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((s.sp - 24#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
           ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5))) ∗
          cells (s.sp - 256#64) 20 ∗ stackAt (s.sp - 256#64) 0x40) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame
    (P' := (((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ (C.std.threadIdCounterAddr ↦₆₄ 0#64) ∗
      ((tp + 0x58#64) ↦₆₄ 0#64) ∗ (S.mainThreadAddr ↦₆₄ v_mt)) ∗ stackAt s.sp 0x140) ∗ F)
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have_instrs hhead 0 48; clear hhead; have hloop' := hloop; have hmid0' := hmid0; clear hloop hmid0
  have hlr' : s.readReg64 (.gpr 30#5) = C.std.cMainAddr + 0x34#64 := hlr
  have hx0' : s.readReg64 (.gpr 0#5) = mainFnSlot := hx0; have hx1' : s.readReg64 (.gpr 1#5) = C.langStartVtableAddr := hx1
  have hx2' : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 argc := hx2; have hx3' : s.readReg64 (.gpr 3#5) = argvPtr := hx3
  have hx4' : s.readReg64 (.gpr 4#5) = 0#64 := hx4
  have hsp_sub_al : ((s.sp + 0xffffffffffffff00#64) &&& 0xf#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x100#64 hsp_align
  wp_conv_pre =>
    rw [stackAt_split_cells s.sp 0x40 32 (by decide), cells_split_sub s.sp 256 96 20 12,
        cells_split_sub s.sp 256 232 3 17, ← memRegion_cells (s.sp - BitVec.ofNat 64 232) 17 (by decide)]
  unfold_stack_cells 15; wp_steps 17
  refine SepWP.step_mrs_tpidr_el0 (pc := C.langStartInternalAddr + 68#64) (by hb_wp_simp) (by hb_wp_simp) hf_17 (by wp_norm_lhs) ?_
  wp_steps 13
  refine hb_step_bl_to (pc := C.langStartInternalAddr + 124#64) (dst := C.std.cas8RelaxAddr) (by hb_wp_simp) (by hb_wp_simp) hf_31 ?_
  refine hb_step_cut fun s0 hs0 => ?_
  have ⟨hpc0, hrun0, hsp0, hsp_al0, hlr0, hx0_0, hx1_0, hx2_0⟩ :
      s0.pc = C.std.cas8RelaxAddr ∧ s0.status = .Running ∧ s0.sp = s.sp - 256#64 ∧ s0.spAligned = true ∧
      s0.readReg64 .lr = C.langStartInternalAddr + 128#64 ∧
      s0.readReg64 .x0 = 0#64 ∧ s0.readReg64 .x1 = 1#64 ∧ s0.readReg64 .x2 = C.std.threadIdCounterAddr := by
    rw [hs0]; refine ⟨by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, ?_, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp⟩
    simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x100#64 hsp_align
  have ⟨hx19_0, hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx26_0, hx27_0, hx28_0, hx29_0, hv_0⟩ :
      s0.readReg64 .x19 = mainFnSlot ∧ s0.readReg64 .x20 = argvPtr ∧ s0.readReg64 .x21 = C.langStartVtableAddr ∧
      s0.readReg64 .x22 = BitVec.ofNat 64 argc ∧ s0.readReg64 .x23 = 0#64 ∧ s0.readReg64 .x24 = 88#64 ∧
      s0.readReg64 .x26 = 0#64 ∧ s0.readReg64 .x27 = tp ∧ s0.readReg64 .x28 = 1#64 ∧
      s0.readReg64 .x29 = s.sp - 96#64 ∧ calleeSavedVRegs s0 = calleeSavedVRegs s := by
    rw [hs0]; refine ⟨by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp,
      by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp⟩
  have hnv0 : HbNonVmFields s s0 := by rw [hs0]; hb_nv_rfl s
  clear hs0 hf_0 hf_1 hf_2 hf_3 hf_4 hf_5 hf_6 hf_7 hf_8 hf_9 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16
    hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31
    hpc hlr hlr' hx0 hx0' hx1 hx1' hx2 hx2' hx3 hx3' hx4 hx4' htp
  refine SepWP.weaken_pre_frame (P' := ((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ (C.std.threadIdCounterAddr ↦₆₄ 0#64)) ∗ ?_) (fun R hm => by revert hm; sep_frame) ?_
  refine hcas8 s0 _ hpc0 hrun0 hsp0 hsp_al0 hlr0 hx0_0 hx1_0 hx2_0 fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hstd1 => ?_
  have hsp1_eq : s1.sp = s.sp - 256#64 := hsp1.trans hsp0
  have hsp_al1 : s1.spAligned = true := by rw [State.spAligned, hsp1_eq, ← hsp0]; exact hsp_al0
  rcases (CalleeSavedPreserved.iff_regs s0 s1).mp hcs1 with ⟨g19, g20, g21, g22, g23, g24, _, g26, g27, g28, g29, gv1⟩
  have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
  have hx19_1 : s1.readReg64 (.gpr 19#5) = mainFnSlot := g19.trans hx19_0; have hx20_1 : s1.readReg64 (.gpr 20#5) = argvPtr := g20.trans hx20_0
  have hx21_1 : s1.readReg64 (.gpr 21#5) = C.langStartVtableAddr := g21.trans hx21_0; have hx22_1 : s1.readReg64 (.gpr 22#5) = BitVec.ofNat 64 argc := g22.trans hx22_0
  have hx23_1 : s1.readReg64 (.gpr 23#5) = 0#64 := g23.trans hx23_0; have hx24_1 : s1.readReg64 (.gpr 24#5) = 88#64 := g24.trans hx24_0
  have hx26_1 : s1.readReg64 (.gpr 26#5) = 0#64 := g26.trans hx26_0; have hx27_1 : s1.readReg64 (.gpr 27#5) = tp := g27.trans hx27_0
  have hx28_1 : s1.readReg64 (.gpr 28#5) = 1#64 := g28.trans hx28_0; have hx29_1 : s1.readReg64 (.gpr 29#5) = s.sp - 96#64 := g29.trans hx29_0
  have hv_1 : calleeSavedVRegs s1 = calleeSavedVRegs s := gv1.trans hv_0; have hnv1 : HbNonVmFields s s1 := hnv0.trans hstd1
  have hc0 : s.sp - 256#64 = s1.sp := hsp1_eq.symm; have hc1 : s.sp - 248#64 = s1.sp + 8#64 := by rw [hsp1_eq]; bv_lin
  have hc2 : s.sp - 240#64 = s1.sp + 16#64 := by rw [hsp1_eq]; bv_lin
  clear hcas8 hsp1 hsp1_eq hcs1 g19 g20 g21 g22 g23 g24 g26 g27 g28 g29 gv1
    hpc0 hrun0 hsp0 hlr0 hx0_0 hx1_0 hx2_0 hx19_0 hx20_0 hx21_0 hx22_0 hx23_0 hx24_0 hx26_0 hx27_0 hx28_0 hx29_0 hv_0 hnv0 hstd1
  wp_conv_pre => rw [hc0, hc1, hc2]
  wp_steps 13
  refine hb_step_bl_to (pc := C.langStartInternalAddr + 180#64) (dst := C.std.pollAddr) (by hb_wp_simp) (by hb_wp_simp) hf_45 ?_
  refine hb_step_cut fun s2 hs2 => ?_
  have hsp1_val : s1.sp = s.sp - 256#64 := hc0.symm
  have ⟨hpc2, hrun2, hsp2, hsp_al2, hlr2, hx0_2, hx1_2, hx2_2, hfs2⟩ :
      s2.pc = C.std.pollAddr ∧ s2.status = .Running ∧ s2.sp = s.sp - 256#64 ∧ s2.spAligned = true ∧
      s2.readReg64 .lr = C.langStartInternalAddr + 184#64 ∧
      s2.readReg64 .x0 = s2.sp ∧ s2.readReg64 .x1 = 3#64 ∧ s2.readReg64 .x2 = 0#64 ∧ s2.fs = s.fs := by
    rw [hs2]; refine ⟨by hb_wp_simp, by hb_wp_simp, by simp [wp_norm, arm64_norm, hsp1_val],
      by simpa [State.spAligned, wp_norm, arm64_norm, hsp1_val, BitVec.sub_eq_add_neg] using hsp_sub_al,
      by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by simp [wp_norm, arm64_norm, hnv1.1]⟩
  have ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx29_2, hv_2⟩ :
      s2.readReg64 .x19 = mainFnSlot ∧ s2.readReg64 .x20 = argvPtr ∧ s2.readReg64 .x21 = C.langStartVtableAddr ∧
      s2.readReg64 .x22 = BitVec.ofNat 64 argc ∧ s2.readReg64 .x23 = 0#64 ∧
      s2.readReg64 .x29 = s.sp - 96#64 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s := by
    rw [hs2]; refine ⟨by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by simp [wp_norm, arm64_norm, hv_1]⟩
  have hnv2 : HbNonVmFields s s2 := hnv1.trans (by rw [hs2]; hb_nv_rfl s1)
  clear hs2 hf_32 hf_33 hf_34 hf_35 hf_36 hf_37 hf_38 hf_39 hf_40 hf_41 hf_42 hf_43 hf_44 hf_45
    hpc1 hrun1 hsp_al1 hx0_1 hx0_1' hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1 hx29_1 hv_1 hnv1
  wp_conv_pre => rw [← hc0, ← hsp2]
  refine SepWP.weaken_pre_frame (P' := (((s2.sp ↦₆₄ 0#64) ∗ ((s2.sp + 8#64) ↦₆₄ 1#64) ∗ ((s2.sp + 16#64) ↦₆₄ 2#64)) ∗ stackAt s2.sp 0x40) ∗ ?_) (fun R hm => by revert hm; sep_frame) ?_
  refine hpoll s2 _ hpc2 hrun2 hsp2 hsp_al2 hlr2 hx0_2 hx1_2 hx2_2 hfs2 fun s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hx0_3 hnv3 => ?_
  have hsp3_eq : s3.sp = s.sp - 256#64 := hsp3.trans hsp2
  rcases (CalleeSavedPreserved.iff_regs s2 s3).mp hcs3 with ⟨g19, g20, g21, g22, g23, _, _, _, _, _, g29, gv3⟩
  have hx0_3' : s3.readReg64 (.gpr 0#5) = 0#64 := hx0_3
  have hx19_3 : s3.readReg64 .x19 = mainFnSlot := g19.trans hx19_2; have hx20_3 : s3.readReg64 .x20 = argvPtr := g20.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = C.langStartVtableAddr := g21.trans hx21_2; have hx22_3 : s3.readReg64 .x22 = BitVec.ofNat 64 argc := g22.trans hx22_2
  have hx23_3 : s3.readReg64 .x23 = 0#64 := g23.trans hx23_2; have hx29_3 : s3.readReg64 .x29 = s.sp - 96#64 := g29.trans hx29_2
  have hv_3 : calleeSavedVRegs s3 = calleeSavedVRegs s := gv3.trans hv_2; have hnv3' : HbNonVmFields s s3 := hnv2.trans hnv3
  clear hpoll hcs3 g19 g20 g21 g22 g23 g29 gv3 hpc2 hrun2 hlr2 hx0_2 hx1_2 hx2_2 hfs2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx29_2 hv_2 hnv2 hnv3
  wp_steps 1; conv => arg 3; simp only [hx0_3', wp_norm, arm64_norm]
  wp_steps 1; refine hb_step_cut fun s4 hs4 => ?_
  have hsp4 : s4.sp = s.sp - 256#64 := by rw [hs4]; simpa [wp_norm, arm64_norm] using hsp3_eq
  have hsp4_s2 : s2.sp = s4.sp := hsp2.trans hsp4.symm
  have hx29_4 : s4.readReg64 .x29 = s4.sp + 0xa0#64 := by rw [hs4]; simp only [wp_norm, arm64_norm]; rw [hx29_3, hsp3_eq]; bv_lin
  wp_conv_pre => rw [hsp4_s2]
  refine SepWP.weaken_pre_frame (P' := ((s4.sp ↦₆₄ 0#64) ∗ ((s4.sp + 8#64) ↦₆₄ 1#64) ∗ ((s4.sp + 16#64) ↦₆₄ 2#64)) ∗ ?_) (fun R hm => by revert hm; sep_frame) ?_
  refine step_hb_langStart_poll_loop (mainFnSlot := mainFnSlot) (argvPtr := argvPtr) (argc := argc) hloop' hmid0'
    (by rw [hs4]; hb_wp_simp) (by rw [hs4]; hb_wp_simp) (by rw [hs4]; simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al3)
    (by rw [hs4]; hb_wp_simp) (by rw [hs4]; hb_wp_simp) (by rw [hs4]; hb_wp_simp) (by rw [hs4]; hb_wp_simp) (by rw [hs4]; hb_wp_simp) hx29_4
    fun sf hpc_f hrun_f hsp_f hsp_al_f hx1_f hx19_f hx20_f hx21_f hx22_f hx29_f hnv_f hv_f => ?_
  have hsp_f_eq : sf.sp = s.sp - 256#64 := hsp_f.trans hsp4; have hx29_f' : sf.readReg64 .x29 = s.sp - 96#64 := by rw [hx29_f, hsp4]; bv_lin
  have hnv_all : HbNonVmFields s sf := hnv3'.trans ((by rw [hs4]; hb_nv_rfl s3 : HbNonVmFields s3 s4).trans hnv_f)
  have hv_all : calleeSavedVRegs sf = calleeSavedVRegs s := hv_f.trans (by rw [hs4]; simpa [wp_norm, arm64_norm] using hv_3)
  have h4_0 : s4.sp = s.sp - 256#64 := hsp4; have h4_1 : s4.sp + 8#64 = s.sp - 248#64 := by rw [hsp4]; bv_lin
  have h4_2 : s4.sp + 16#64 = s.sp - 240#64 := by rw [hsp4]; bv_lin
  refine hb_step_entail (hnext sf hpc_f hrun_f hsp_f_eq hsp_al_f hx1_f hx19_f hx20_f hx21_f hx22_f hx29_f' hnv_all hv_all)
    (fun R hm => by
      rw [h4_1, h4_2, h4_0] at hm
      rw [show s.sp - 256#64 = s.sp - BitVec.ofNat 64 256 from rfl,
          cells_split_sub s.sp 256 232 3 17, ← memRegion_cells (s.sp - BitVec.ofNat 64 232) 17 (by decide)]
      fold_stack_cells)

private theorem cells_20_of_three (sp : BitVec 64) (v0 v1 v17 : BitVec 64) (F : SepProp) (m : Memory)
    (hm : m ⊨ ((sp ↦₆₄ v0) ∗ ((sp + 8#64) ↦₆₄ v1) ∗ ((sp + 0x88#64) ↦₆₄ v17) ∗ cells (sp + 16#64) 15 ∗ cells (sp + 144#64) 2) ∗ F) :
    m ⊨ cells sp 20 ∗ F := by
  rw [show (20 : Nat) = 2 + (15 + 3) from rfl, cells_split sp 2 (15 + 3), cells_split (sp + BitVec.ofNat 64 (8 * 2)) 15 3]
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd]
  rw [cells_succ sp 1, cells_succ (sp + 8#64) 0, cells_zero, cells_succ (sp + 136#64) 2]
  simp only [sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  revert hm; sep_entail

abbrev hbLangStartMid1Instrs (C : HbCliLayout) : List Instr :=
  let L := C.std; let ls := C.langStartInternalAddr; let lsm := ls + 0x1f8#64
  [decodeWord 0x528001a0#32, iBl (lsm + 0x50#64) L.signalAddr, decodeWord 0xb100041f#32, decodeWord 0x54001120#32,
   decodeWord 0x528003c0#32, iBl (lsm + 0x60#64) L.sysconfAddr, decodeWord 0x6f00e400#32,
   iAdrp .x8 (lsm + 0x68#64) L.pageSizeGlobalAddr, decodeWord 0x910003e2#32, iStr64Lo12 .x0 .x8 L.pageSizeGlobalAddr,
   decodeWord 0x52800160#32, decodeWord 0xaa1f03e1#32, iLdr64Lo12 .xzr .x8 L.pageSizeGlobalAddr] ++
  decodeWords [0xf9004bff#32, 0xad0083e0#32, 0xad0183e0#32, 0xad0283e0#32, 0xad0383e0#32, 0x3d8003e0#32] ++
  [iBl (lsm + 0x98#64) L.sigactionAddr] ++ decodeWords [0xf94003e8#32, 0xb4000108#32]

set_option maxHeartbeats 400000 in
private theorem step_hb_langStart_mid1 {P : Program} {C : HbCliLayout} {target_pc v_ps : BitVec 64}
    (hmid1 : hasInstrs P (C.langStartInternalAddr + BitVec.ofNat 64 0x244) (hbLangStartMid1Instrs C))
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R →
      s.mem ⊨ ((((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗
        ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ v_ps) ∗
        cells s.sp 20 ∗ stackAt s.sp 0x220) ∗ (F ∗ R)))
    (hpc : s.pc = C.langStartInternalAddr + 0x244#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hx1 : s.readReg64 .x1 = 1#64)
    (hsigpipe : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.signalAddr → s0.status = .Running → s0.sp = s.sp → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 588#64 →
      s0.readReg64 .x0 = 13#64 → s0.readReg64 .x1 = 1#64 → HbNonVmFields s s0 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 588#64 → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields (s0.setSigAction 13#32 (sigpipeIgnAction C.std)) s1 →
        SepWP P target_pc s1 (stackAt s.sp 0x220 ∗ G) post oom) →
      SepWP P target_pc s0 (stackAt s.sp 0x220 ∗ G) post oom)
    (hsysconf : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.sysconfAddr → s0.status = .Running → s0.sp = s.sp → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 604#64 → s0.readReg64 .x0 = 30#64 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 604#64 → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 4096#64 → HbNonVmFields s0 s1 →
        SepWP P target_pc s1 ((((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗
          ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ stackAt s.sp 0x190) ∗ G) post oom) →
      SepWP P target_pc s0 ((((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗
        ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ stackAt s.sp 0x190) ∗ G) post oom)
    (hprobe11 : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.sigactionAddr → s0.status = .Running → s0.sp = s.sp → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 660#64 →
      s0.readReg64 .x0 = 11#64 → s0.readReg64 .x1 = 0#64 → s0.readReg64 .x2 = s.sp →
      HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction C.std)) s0 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 660#64 → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields s0 s1 →
        SepWP P target_pc s1 ((((s.sp ↦₆₄ 0#64) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0#64)) ∗ stackAt s.sp 0xe0) ∗ G) post oom) →
      SepWP P target_pc s0 ((((s.sp ↦₆₄ 0#64) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0#64)) ∗ stackAt s.sp 0xe0) ∗ G) post oom)
    (hnext : ∀ sf : State,
      sf.pc = C.langStartInternalAddr + 0x2b8#64 → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction C.std)) sf →
      SepWP P target_pc sf
        ((((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗
          ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
          ((s.sp ↦₆₄ 0#64) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0#64) ∗
           cells (s.sp + 16#64) 15 ∗ cells (s.sp + 144#64) 2) ∗ stackAt s.sp 0x220) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame
    (P' := (((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
      (C.std.pageSizeGlobalAddr ↦₆₄ v_ps) ∗ cells s.sp 20 ∗ stackAt s.sp 0x220) ∗ F)
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  dsimp only [hbLangStartMid1Instrs] at hmid1
  rw [show BitVec.ofNat 64 0x244 = 0x244#64 from rfl,
      show C.langStartInternalAddr + 0x1f8#64 + 0x50#64 = (C.langStartInternalAddr + 0x244#64) + 4#64 by bv_lin,
      show C.langStartInternalAddr + 0x1f8#64 + 0x60#64 = (C.langStartInternalAddr + 0x244#64) + 20#64 by bv_lin,
      show C.langStartInternalAddr + 0x1f8#64 + 0x68#64 = (C.langStartInternalAddr + 0x244#64) + 28#64 by bv_lin,
      show C.langStartInternalAddr + 0x1f8#64 + 0x98#64 = (C.langStartInternalAddr + 0x244#64) + 76#64 by bv_lin] at hmid1
  generalize hb : C.langStartInternalAddr + 0x244#64 = b at hmid1 hpc
  have_instrs hmid1 0 22; clear hmid1; have hx1' : s.readReg64 (.gpr 1#5) = 1#64 := hx1
  wp_steps 1
  refine hb_step_bl_to (pc := b + 4#64) (dst := C.std.signalAddr) (by hb_wp_simp) (by hb_wp_simp) hf_1 ?_
  refine hb_step_cut fun s0 hs0 => ?_
  have hcs0 : CalleeSavedPreserved s s0 := by rw [hs0]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]
  have hnv0 : HbNonVmFields s s0 := by rw [hs0]; hb_nv_rfl s
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 0x220 ∗ ?_) (fun R hm => by revert hm; sep_frame) ?_
  refine hsigpipe s0 _ (by rw [hs0]; hb_wp_simp) (by rw [hs0]; hb_wp_simp) (by rw [hs0]; hb_wp_simp)
    (by rw [hs0]; simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align)
    (by rw [hs0, ← hb]; hb_wp_simp) (by rw [hs0]; hb_wp_simp) (by rw [hs0]; hb_wp_simp) hnv0
    fun s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hx0_1 hnv1 => ?_
  clear hsigpipe hs0 hf_0 hf_1 hpc hx1 hx1'
  have hpc1_b : s1.pc = b + 8#64 := by rw [hpc1, ← hb]; bv_lin
  have hcs01 : CalleeSavedPreserved s s1 := hcs0.trans hcs1
  have hnv01 : HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction C.std)) s1 :=
    HbNonVmFields.trans (s1 := s0.setSigAction 13#32 (sigpipeIgnAction C.std)) ⟨hnv0.1, hnv0.2.1, hnv0.2.2.1, by dsimp [State.setSigAction]; rw [hnv0.2.2.2.1], hnv0.2.2.2.2⟩ hnv1
  have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1; clear hpc1 hcs0 hcs1 hnv0 hnv1
  wp_steps 3
  refine hb_step_bl_to (pc := b + 20#64) (dst := C.std.sysconfAddr) (by hb_wp_simp) (by hb_wp_simp) hf_5 ?_
  refine hb_step_cut fun s2 hs2 => ?_
  have hcs12 : CalleeSavedPreserved s1 s2 := by rw [hs2]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]
  have hnv12 : HbNonVmFields s1 s2 := by rw [hs2]; hb_nv_rfl s1
  have hsp2 : s2.sp = s.sp := by rw [hs2]; simpa [wp_norm, arm64_norm] using hsp1
  wp_conv_pre => rw [stackAt_split_bottom s.sp 0x190 144 (by decide)]
  refine SepWP.weaken_pre_frame
    (P' := (((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ stackAt s.sp 0x190) ∗ ?_)
    (fun R hm => by revert hm; sep_frame) ?_
  refine hsysconf s2 _ (by rw [hs2]; hb_wp_simp) (by rw [hs2]; hb_wp_simp) hsp2
    (by rw [hs2]; simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al1)
    (by rw [hs2, ← hb]; hb_wp_simp) (by rw [hs2]; hb_wp_simp)
    fun s3 hpc3 hrun3 hsp3 hsp_al3 hcs23 hx0_3 hnv23 => ?_
  clear hsysconf hs2 hf_2 hf_3 hf_4 hf_5 hpc1_b hrun1 hsp1 hsp_al1 hx0_1 hx0_1' hsp2
  have hpc3_b : s3.pc = b + 24#64 := by rw [hpc3, ← hb]; bv_lin
  have hcs03 : CalleeSavedPreserved s s3 := hcs01.trans (hcs12.trans hcs23)
  have hnv03 : HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction C.std)) s3 := hnv01.trans (hnv12.trans hnv23)
  have hx0_3' : s3.readReg64 (.gpr 0#5) = 4096#64 := hx0_3
  have hsp_al3_raw : (s3.sp &&& 15#64 == 0#64) = true := hsp_al3; have hsp_s3 : s.sp = s3.sp := hsp3.symm
  clear hpc3 hcs01 hcs12 hcs23 hnv01 hnv12 hnv23 hsp3
  wp_conv_pre =>
    rw [show cells s.sp 20 = cells s3.sp 20 by rw [hsp_s3], show (20 : Nat) = 19 + 1 from rfl, cells_split s3.sp 19 1]
    simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat]
  generalize hc152 : cells (s3.sp + 152#64) 1 = c152
  wp_conv_pre => simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  iterate 19 (refine SepWP.exists_elim fun _ => ?_)
  wp_steps 13
  refine hb_step_bl_to (pc := b + 76#64) (dst := C.std.sigactionAddr) (by hb_wp_simp) (by hb_wp_simp) hf_19 ?_
  refine hb_step_cut fun s4 hs4 => ?_
  have hsp3_val : s3.sp = s.sp := hsp_s3.symm
  have hcs34 : CalleeSavedPreserved s3 s4 := by rw [hs4]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]
  have hnv34 : HbNonVmFields s3 s4 := by rw [hs4]; hb_nv_rfl s3
  have hsp4 : s4.sp = s.sp := by rw [hs4]; simpa [wp_norm, arm64_norm] using hsp3_val
  wp_conv_pre => rw [← hsp_s3]
  refine SepWP.weaken_pre_frame
    (P' := (((s.sp ↦₆₄ 0#64) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0#64)) ∗ stackAt s.sp 0xe0) ∗
      ((((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
        (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ (cells (s.sp + 16#64) 15 ∗ cells (s.sp + 144#64) 2) ∗
        memRegion (s.sp - 0x190#64) 176 ∗ memRegion (s.sp - 0x220#64) 144) ∗ F))
    (fun R hm => by
      rw [stackAt_split_bottom s.sp 0xe0 176 (by decide)] at hm
      rw [cells_succ (s.sp + 144#64) 1]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [hsp_s3, hc152, ← hsp_s3]
      simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
      revert hm; sep_entail) ?_
  refine hprobe11 s4 _ (by rw [hs4]; hb_wp_simp) (by rw [hs4]; hb_wp_simp) hsp4
    (by rw [hs4]; simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al3)
    (by rw [hs4, ← hb]; hb_wp_simp) (by rw [hs4]; hb_wp_simp) (by rw [hs4]; hb_wp_simp)
    (by rw [hs4]; simpa [wp_norm, arm64_norm] using hsp3_val) (hnv03.trans hnv34)
    fun s5 hpc5 hrun5 hsp5 hsp_al5 hcs45 hx0_5 hnv45 => ?_
  clear hprobe11 hs4 hf_6 hf_7 hf_8 hf_9 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19
    hpc3_b hrun3 hsp_al3 hsp_al3_raw hx0_3 hx0_3' hsp_s3 hsp3_val hc152 hsp4
  have hpc5_b : s5.pc = b + 80#64 := by rw [hpc5, ← hb]; bv_lin
  have hcs05 : CalleeSavedPreserved s s5 := hcs03.trans (hcs34.trans hcs45)
  have hnv05 : HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction C.std)) s5 := hnv03.trans (hnv34.trans hnv45)
  have hsp_al5_raw : (s5.sp &&& 15#64 == 0#64) = true := hsp_al5; have hsp_s5 : s.sp = s5.sp := hsp5.symm
  clear hpc5 hcs03 hcs34 hcs45 hnv03 hnv34 hnv45 hsp5
  wp_conv_pre => rw [hsp_s5]
  wp_steps 2
  refine hb_step_entail
    (hnext _ (by rw [← hb]; hb_wp_simp) (by hb_wp_simp) (by simpa [wp_norm, arm64_norm] using hsp_s5.symm)
      (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al5)
      (hcs05.trans (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]))
      (hnv05.trans (by hb_nv_rfl s5)))
    (fun R hm => by
      rw [← hsp_s5] at hm
      rw [stackAt_split_bottom s.sp 0x190 144 (by decide), stackAt_split_bottom s.sp 0xe0 176 (by decide)]
      revert hm; sep_entail)

abbrev hbLangStartMid2Instrs (C : HbCliLayout) (S : HbStartupLayout) : List Instr :=
  let L := C.std; let ls := C.langStartInternalAddr; let lsm := ls + 0x1f8#64
  [iAdrp .x8 (lsm + 0xc0#64) C.needAltstackAddr, iLdr8Lo12 .x8 .x8 C.needAltstackAddr,
   decodeWord 0x35000128#32, decodeWord 0x52800028#32, iAdrp .x9 (lsm + 0xd0#64) C.needAltstackAddr,
   iAddLo12 .x9 .x9 C.needAltstackAddr, decodeWord 0x089ffd28#32, decodeWord 0x52800020#32,
   iBl (lsm + 0xe0#64) C.makeStackHandlerAddr, iAdrp .x8 (lsm + 0xe4#64) C.mainAltstackAddr,
   iStr64Lo12 .x0 .x8 C.mainAltstackAddr] ++
  decodeWords [0x52800088#32, 0x910003e1#32, 0x52800160#32, 0x72a10008#32, 0xaa1f03e2#32, 0xb9008be8#32, 0xd503201f#32] ++
  [iAdr .x8 (lsm + 0x108#64) S.signalHandlerAddr, decodeWord 0xf90003e8#32, iBl (lsm + 0x110#64) L.sigactionAddr] ++
  decodeWords [0x910003e2#32, 0x528000e0#32, 0xaa1f03e1#32] ++
  [iBl (lsm + 0x120#64) L.sigactionAddr, decodeWord 0xf94003e8#32, decodeWord 0xb50002c8#32,
   iAdrp .x8 (lsm + 0x12c#64) C.needAltstackAddr, iLdr8Lo12 .x8 .x8 C.needAltstackAddr, decodeWord 0x35000128#32]

private theorem step_hb_langStart_to_makeHandler {P : Program} {C : HbCliLayout} {S : HbStartupLayout} {target_pc : BitVec 64}
    (hmid2 : hasInstrs P (C.langStartInternalAddr + BitVec.ofNat 64 0x2b8) (hbLangStartMid2Instrs C S))
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ (C.needAltstackAddr ↦₈ 0#8) ∗ (F ∗ R))
    (hpc : s.pc = C.langStartInternalAddr + 0x2b8#64) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hnext : ∀ sf : State,
      sf.pc = C.makeStackHandlerAddr → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      sf.readReg64 .lr = C.langStartInternalAddr + 732#64 → sf.readReg64 .x0 = 1#64 →
      CalleeSavedPreserved s sf → HbNonVmFields s sf →
      SepWP P target_pc sf ((C.needAltstackAddr ↦₈ 1#8) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := (C.needAltstackAddr ↦₈ 0#8) ∗ F) (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  dsimp only [hbLangStartMid2Instrs] at hmid2
  rw [show BitVec.ofNat 64 0x2b8 = 0x2b8#64 from rfl,
      show C.langStartInternalAddr + 0x1f8#64 + 0xc0#64 = C.langStartInternalAddr + 0x2b8#64 by bv_lin,
      show C.langStartInternalAddr + 0x1f8#64 + 0xd0#64 = (C.langStartInternalAddr + 0x2b8#64) + 16#64 by bv_lin,
      show C.langStartInternalAddr + 0x1f8#64 + 0xe0#64 = (C.langStartInternalAddr + 0x2b8#64) + 32#64 by bv_lin] at hmid2
  generalize hb : C.langStartInternalAddr + 0x2b8#64 = b at hmid2 hpc
  have_instrs hmid2 0 9; clear hmid2; wp_steps 6
  refine step_hb_stlrb (pc := b + 24#64) (ea := C.needAltstackAddr) (val := 1#8)
    (by hb_wp_simp) (by hb_wp_simp) hf_6 rfl (by hb_wp_simp) (by hb_wp_simp) (by wp_sep_access) ?_
  wp_steps 1
  refine hb_step_bl_to (pc := b + 32#64) (dst := C.makeStackHandlerAddr) (by hb_wp_simp) (by hb_wp_simp) hf_8 ?_
  exact hnext _ (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align) (by rw [← hb]; hb_wp_simp) (by hb_wp_simp)
    (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by hb_nv_rfl s)

set_option maxHeartbeats 400000 in
private theorem step_hb_langStart_after_makeHandler {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc altStackSp v_ma : BitVec 64} {Pin11 Pcustom11 : SepProp}
    (hmid2 : hasInstrs P (C.langStartInternalAddr + BitVec.ofNat 64 0x2b8) (hbLangStartMid2Instrs C S))
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R →
      s.mem ⊨ (((C.needAltstackAddr ↦₈ 1#8) ∗ (C.mainAltstackAddr ↦₆₄ v_ma) ∗
        ((s.sp ↦₆₄ 0#64) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0#64)) ∗
        Pin11 ∗ stackAt s.sp 0xe0) ∗ (F ∗ R)))
    (hpc : s.pc = C.langStartInternalAddr + 732#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hx0 : s.readReg64 .x0 = altStackSp)
    (hcustom11 : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.sigactionAddr → s0.status = .Running → s0.sp = s.sp → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 780#64 →
      s0.readReg64 .x0 = 11#64 → s0.readReg64 .x1 = s.sp → s0.readReg64 .x2 = 0#64 → HbNonVmFields s s0 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 780#64 → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 →
        HbNonVmFields (s0.setSigAction 11#32 (hbCustomSigAction C S)) s1 →
        SepWP P target_pc s1 (((((s.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pcustom11) ∗ stackAt s.sp 0xe0) ∗ G) post oom) →
      SepWP P target_pc s0 (((((s.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pin11) ∗ stackAt s.sp 0xe0) ∗ G) post oom)
    (hprobe7 : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.sigactionAddr → s0.status = .Running → s0.sp = s.sp → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 796#64 →
      s0.readReg64 .x0 = 7#64 → s0.readReg64 .x1 = 0#64 → s0.readReg64 .x2 = s.sp →
      HbNonVmFields (s.setSigAction 11#32 (hbCustomSigAction C S)) s0 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 796#64 → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields s0 s1 →
        SepWP P target_pc s1 ((((s.sp ↦₆₄ 0#64) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0#64)) ∗ stackAt s.sp 0xe0) ∗ G) post oom) →
      SepWP P target_pc s0 ((((s.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ stackAt s.sp 0xe0) ∗ G) post oom)
    (hnext : ∀ sf : State,
      sf.pc = C.langStartInternalAddr + 0x350#64 → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → HbNonVmFields (s.setSigAction 11#32 (hbCustomSigAction C S)) sf →
      SepWP P target_pc sf
        ((((C.needAltstackAddr ↦₈ 1#8) ∗ (C.mainAltstackAddr ↦₆₄ altStackSp) ∗
           ((s.sp ↦₆₄ 0#64) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0#64)) ∗
           Pcustom11) ∗ stackAt s.sp 0xe0) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame
    (P' := ((C.needAltstackAddr ↦₈ 1#8) ∗ (C.mainAltstackAddr ↦₆₄ v_ma) ∗
      ((s.sp ↦₆₄ 0#64) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0#64)) ∗ Pin11 ∗ stackAt s.sp 0xe0) ∗ F)
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  dsimp only [hbLangStartMid2Instrs] at hmid2
  rw [show BitVec.ofNat 64 0x2b8 = 0x2b8#64 from rfl,
      show C.langStartInternalAddr + 0x1f8#64 + 0xe4#64 = (C.langStartInternalAddr + 0x2b8#64) + 36#64 by bv_lin,
      show C.langStartInternalAddr + 0x1f8#64 + 0x108#64 = (C.langStartInternalAddr + 0x2b8#64) + 72#64 by bv_lin,
      show C.langStartInternalAddr + 0x1f8#64 + 0x110#64 = (C.langStartInternalAddr + 0x2b8#64) + 80#64 by bv_lin,
      show C.langStartInternalAddr + 0x1f8#64 + 0x120#64 = (C.langStartInternalAddr + 0x2b8#64) + 96#64 by bv_lin,
      show C.langStartInternalAddr + 0x1f8#64 + 0x12c#64 = (C.langStartInternalAddr + 0x2b8#64) + 108#64 by bv_lin] at hmid2
  rw [show C.langStartInternalAddr + 732#64 = (C.langStartInternalAddr + 0x2b8#64) + 36#64 by bv_lin] at hpc
  generalize hb : C.langStartInternalAddr + 0x2b8#64 = b at hmid2 hpc
  have_instrs hmid2 9 21; clear hmid2
  have hx0' : s.readReg64 (.gpr 0#5) = altStackSp := hx0; have hsp_al_raw : (s.sp &&& 15#64 == 0#64) = true := hsp_align
  wp_steps 11
  wp_conv_pre => rw [show b + 72#64 + (S.signalHandlerAddr - (b + 72#64)) = S.signalHandlerAddr by bv_lin]
  refine hb_step_bl_to (pc := b + 80#64) (dst := C.std.sigactionAddr) (by hb_wp_simp) (by hb_wp_simp) hf_20 ?_
  refine hb_step_cut fun s0 hs0 => ?_
  have hcs0 : CalleeSavedPreserved s s0 := by rw [hs0]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]
  have hnv0 : HbNonVmFields s s0 := by rw [hs0]; hb_nv_rfl s
  refine SepWP.weaken_pre_frame
    (P' := ((((s.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pin11) ∗ stackAt s.sp 0xe0) ∗ ?_)
    (fun R hm => by revert hm; sep_frame) ?_
  refine hcustom11 s0 _ (by rw [hs0]; hb_wp_simp) (by rw [hs0]; hb_wp_simp) (by rw [hs0]; hb_wp_simp)
    (by rw [hs0]; simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align)
    (by rw [hs0, ← hb]; hb_wp_simp) (by rw [hs0]; hb_wp_simp) (by rw [hs0]; hb_wp_simp) (by rw [hs0]; hb_wp_simp)
    hnv0 fun s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hx0_1 hnv1 => ?_
  clear hcustom11 hs0 hf_9 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hpc hx0 hx0' hsp_al_raw
  have hpc1_b : s1.pc = b + 84#64 := by rw [hpc1, ← hb]; bv_lin
  have hcs01 : CalleeSavedPreserved s s1 := hcs0.trans hcs1
  have hnv01 : HbNonVmFields (s.setSigAction 11#32 (hbCustomSigAction C S)) s1 :=
    HbNonVmFields.trans (s1 := s0.setSigAction 11#32 (hbCustomSigAction C S)) ⟨hnv0.1, hnv0.2.1, hnv0.2.2.1, by dsimp [State.setSigAction]; rw [hnv0.2.2.2.1], hnv0.2.2.2.2⟩ hnv1
  clear hpc1 hcs0 hcs1 hnv0 hnv1; wp_steps 3
  refine hb_step_bl_to (pc := b + 96#64) (dst := C.std.sigactionAddr) (by hb_wp_simp) (by hb_wp_simp) hf_24 ?_
  refine hb_step_cut fun s2 hs2 => ?_
  have hcs12 : CalleeSavedPreserved s1 s2 := by rw [hs2]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]
  have hnv12 : HbNonVmFields s1 s2 := by rw [hs2]; hb_nv_rfl s1
  have hsp2 : s2.sp = s.sp := by rw [hs2]; simpa [wp_norm, arm64_norm] using hsp1
  refine SepWP.weaken_pre_frame
    (P' := (((s.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ stackAt s.sp 0xe0) ∗ ?_)
    (fun R hm => by revert hm; sep_frame) ?_
  refine hprobe7 s2 _ (by rw [hs2]; hb_wp_simp) (by rw [hs2]; hb_wp_simp) hsp2
    (by rw [hs2]; simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al1)
    (by rw [hs2, ← hb]; hb_wp_simp) (by rw [hs2]; hb_wp_simp) (by rw [hs2]; hb_wp_simp) (by rw [hs2]; hb_wp_simp)
    (hnv01.trans hnv12) fun s3 hpc3 hrun3 hsp3 hsp_al3 hcs23 hx0_3 hnv23 => ?_
  clear hprobe7 hs2 hf_21 hf_22 hf_23 hf_24 hpc1_b hrun1 hsp1 hsp_al1 hx0_1 hsp2
  have hpc3_b : s3.pc = b + 100#64 := by rw [hpc3, ← hb]; bv_lin
  have hcs03 : CalleeSavedPreserved s s3 := hcs01.trans (hcs12.trans hcs23)
  have hnv03 : HbNonVmFields (s.setSigAction 11#32 (hbCustomSigAction C S)) s3 := hnv01.trans (hnv12.trans hnv23)
  have hsp_al3_raw : (s3.sp &&& 15#64 == 0#64) = true := hsp_al3; have hsp_s3 : s.sp = s3.sp := hsp3.symm
  clear hpc3 hcs01 hcs12 hcs23 hnv01 hnv12 hnv23 hsp3
  wp_conv_pre => rw [hsp_s3]
  wp_steps 5
  refine hb_step_entail
    (hnext _ (by rw [← hb]; hb_wp_simp) (by hb_wp_simp) (by simpa [wp_norm, arm64_norm] using hsp_s3.symm)
      (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al3)
      (hcs03.trans (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]))
      (hnv03.trans (by hb_nv_rfl s3)))
    (fun R hm => by rw [← hsp_s3] at hm; revert hm; sep_entail)

abbrev hbLangStartTailInstrs (C : HbCliLayout) (S : HbStartupLayout) : List Instr :=
  let L := C.std; let ls := C.langStartInternalAddr; let lsm := ls + 0x1f8#64
  decodeWords [0x52800088#32, 0x910003e1#32, 0x528000e0#32, 0x72a10008#32, 0xaa1f03e2#32, 0xb9008be8#32, 0xd503201f#32] ++
  [iAdr .x8 (lsm + 0x174#64) S.signalHandlerAddr, decodeWord 0xf90003e8#32, iBl (lsm + 0x17c#64) L.sigactionAddr,
   iAdrp .x8 (lsm + 0x180#64) L.argcGlobalAddr, iAddLo12 .x8 .x8 L.argcGlobalAddr] ++
  decodeWords [0xf9000116#32, 0xf9000514#32, 0xf94016a8#32, 0xaa1303e0#32, 0xd63f0100#32]

abbrev hbLangStartClosureInstrs (C : HbCliLayout) : List Instr :=
  decodeWords [0xa9bf7bfd#32, 0x910003fd#32, 0xf9400000#32] ++ [iBl (C.langStartClosureAddr + 0x0c#64) C.std.beginShortBacktraceAddr]

private theorem step_hb_langStartClosure_to_userMain {P : Program} {C : HbCliLayout} {target_pc mainFnSlot fp_ls : BitVec 64}
    (hclos : hasInstrs P C.langStartClosureAddr (hbLangStartClosureInstrs C))
    (hbsb : P.hasCode C.std.beginShortBacktraceAddr beginShortBacktraceWords)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ ((stackAt s.sp 0x20 ∗ (mainFnSlot ↦₆₄ C.std.userMainAddr)) ∗ (F ∗ R)))
    (hpc : s.pc = C.langStartClosureAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 (.gpr 0#5) = mainFnSlot) (hx29 : s.readReg64 (.gpr 29#5) = fp_ls)
    (hlr : s.readReg64 .lr = C.langStartInternalAddr + 0x394#64)
    (hnext : ∀ sf : State,
      sf.pc = C.std.userMainAddr → sf.status = .Running → sf.sp = s.sp - 32#64 → sf.spAligned = true →
      sf.readReg64 .x29 = s.sp - 32#64 → sf.readReg64 .lr = C.std.beginShortBacktraceAddr + 0x0c#64 → HbNonVmFields s sf →
      SepWP P target_pc sf
        (((((s.sp - 32#64) ↦₆₄ (s.sp - 16#64)) ∗ ((s.sp - 24#64) ↦₆₄ (C.langStartClosureAddr + 0x10#64)) ∗
           ((s.sp - 16#64) ↦₆₄ fp_ls) ∗ ((s.sp - 8#64) ↦₆₄ (C.langStartInternalAddr + 0x394#64))) ∗
          (mainFnSlot ↦₆₄ C.std.userMainAddr)) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := (stackAt s.sp 0x20 ∗ (mainFnSlot ↦₆₄ C.std.userMainAddr)) ∗ F)
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have_instrs hclos 0 4; clear hclos
  have hlr' : s.readReg64 (.gpr 30#5) = C.langStartInternalAddr + 0x394#64 := hlr
  have hsp_al_raw : (s.sp &&& 15#64 == 0#64) = true := hsp_align
  have hsp_sub16 : ((s.sp + 0xfffffffffffffff0#64) &&& 15#64 == 0#64) = true := by
    simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x10#64 hsp_align
  have hsp_sub16_al : ((s.sp - 16#64) &&& 15#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using hsp_sub16
  have hsp_sub32 : (((s.sp - 16#64) + 0xfffffffffffffff0#64) &&& 15#64 == 0#64) = true := by
    rw [show (s.sp - 16#64) + 0xfffffffffffffff0#64 = s.sp + 0xffffffffffffffe0#64 by bv_lin]
    simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align
  wp_conv_pre => rw [stackAt_eq_cells s.sp 4 (by decide)]
  unfold_stack_cells 4; wp_steps 3
  refine hb_step_bl_to (pc := C.langStartClosureAddr + 12#64) (dst := C.std.beginShortBacktraceAddr)
    (by hb_wp_simp) (by hb_wp_simp) hf_3 ?_
  wp_steps 3
  refine hb_step_entail
    (hnext _ (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
      (by simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align)
      (by hb_wp_simp) (by hb_wp_simp) (by hb_nv_rfl s))
    (fun R hm => by
      simp only [State.mem_setMem] at hm ⊢
      rw [show s.sp + 0xfffffffffffffff0#64 = s.sp - 16#64 by bv_lin] at hm; revert hm; sep_entail)

set_option maxHeartbeats 400000 in
private theorem step_hb_langStart_tail_to_userMain {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc mainFnSlot argvPtr fp_ls v_argc v_argv : BitVec 64} {argc : Nat} {Pin7 Pcustom7 : SepProp}
    (htail : hasInstrs P (C.langStartInternalAddr + BitVec.ofNat 64 0x350) (hbLangStartTailInstrs C S))
    (hclos : hasInstrs P C.langStartClosureAddr (hbLangStartClosureInstrs C))
    (hbsb : P.hasCode C.std.beginShortBacktraceAddr beginShortBacktraceWords)
    (hargv_eq : C.std.argvGlobalAddr = C.std.argcGlobalAddr + 8#64)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R →
      s.mem ⊨ ((((s.sp ↦₆₄ 0#64) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0#64)) ∗
        Pin7 ∗ stackAt s.sp 0x220 ∗ (C.std.argcGlobalAddr ↦₆₄ v_argc) ∗ (C.std.argvGlobalAddr ↦₆₄ v_argv) ∗
        ((C.langStartVtableAddr + 0x28#64) ↦₆₄ᵣ C.langStartClosureAddr) ∗ (mainFnSlot ↦₆₄ C.std.userMainAddr)) ∗ (F ∗ R)))
    (hpc : s.pc = C.langStartInternalAddr + 0x350#64) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 (.gpr 19#5) = mainFnSlot) (hx20 : s.readReg64 (.gpr 20#5) = argvPtr)
    (hx21 : s.readReg64 (.gpr 21#5) = C.langStartVtableAddr) (hx22 : s.readReg64 (.gpr 22#5) = BitVec.ofNat 64 argc)
    (hx29 : s.readReg64 (.gpr 29#5) = fp_ls)
    (hcustom7 : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.sigactionAddr → s0.status = .Running → s0.sp = s.sp → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 888#64 →
      s0.readReg64 .x0 = 7#64 → s0.readReg64 .x1 = s.sp → s0.readReg64 .x2 = 0#64 → HbNonVmFields s s0 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 888#64 → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 →
        HbNonVmFields (s0.setSigAction 7#32 (hbCustomSigAction C S)) s1 →
        SepWP P target_pc s1 (((((s.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pcustom7) ∗ stackAt s.sp 0xe0) ∗ G) post oom) →
      SepWP P target_pc s0 (((((s.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pin7) ∗ stackAt s.sp 0xe0) ∗ G) post oom)
    (hnext : ∀ sf : State,
      sf.pc = C.std.userMainAddr → sf.status = .Running → sf.sp = s.sp - 32#64 → sf.spAligned = true →
      sf.readReg64 .x29 = s.sp - 32#64 → sf.readReg64 .lr = C.std.beginShortBacktraceAddr + 0x0c#64 →
      HbNonVmFields (s.setSigAction 7#32 (hbCustomSigAction C S)) sf →
      SepWP P target_pc sf
        (((((s.sp - 32#64) ↦₆₄ (s.sp - 16#64)) ∗ ((s.sp - 24#64) ↦₆₄ (C.langStartClosureAddr + 0x10#64)) ∗
           ((s.sp - 16#64) ↦₆₄ fp_ls) ∗ ((s.sp - 8#64) ↦₆₄ (C.langStartInternalAddr + 0x394#64))) ∗
          ((s.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗
          Pcustom7 ∗ stackAt (s.sp - 32#64) 0x200 ∗
          (C.std.argcGlobalAddr ↦₆₄ BitVec.ofNat 64 argc) ∗ (C.std.argvGlobalAddr ↦₆₄ argvPtr) ∗
          ((C.langStartVtableAddr + 0x28#64) ↦₆₄ᵣ C.langStartClosureAddr) ∗ (mainFnSlot ↦₆₄ C.std.userMainAddr)) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame
    (P' := (((s.sp ↦₆₄ 0#64) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0#64)) ∗
      Pin7 ∗ stackAt s.sp 0x220 ∗ (C.std.argcGlobalAddr ↦₆₄ v_argc) ∗ (C.std.argvGlobalAddr ↦₆₄ v_argv) ∗
      ((C.langStartVtableAddr + 0x28#64) ↦₆₄ᵣ C.langStartClosureAddr) ∗ (mainFnSlot ↦₆₄ C.std.userMainAddr)) ∗ F)
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  dsimp only [hbLangStartTailInstrs] at htail
  rw [show BitVec.ofNat 64 0x350 = 0x350#64 from rfl,
      show C.langStartInternalAddr + 0x1f8#64 + 0x174#64 = (C.langStartInternalAddr + 0x350#64) + 28#64 by bv_lin,
      show C.langStartInternalAddr + 0x1f8#64 + 0x17c#64 = (C.langStartInternalAddr + 0x350#64) + 36#64 by bv_lin,
      show C.langStartInternalAddr + 0x1f8#64 + 0x180#64 = (C.langStartInternalAddr + 0x350#64) + 40#64 by bv_lin] at htail
  generalize hb : C.langStartInternalAddr + 0x350#64 = b at htail hpc
  have_instrs htail 0 17; clear htail
  have hsp_al_raw : (s.sp &&& 15#64 == 0#64) = true := hsp_align
  wp_steps 9
  wp_conv_pre =>
    rw [show b + 28#64 + (S.signalHandlerAddr - (b + 28#64)) = S.signalHandlerAddr by bv_lin,
        stackAt_split_bottom s.sp 0xe0 320 (by decide)]
  refine hb_step_bl_to (pc := b + 36#64) (dst := C.std.sigactionAddr) (by hb_wp_simp) (by hb_wp_simp) hf_9 ?_
  refine hb_step_cut fun s0 hs0 => ?_
  have hcs0 : CalleeSavedPreserved s s0 := by rw [hs0]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]
  have hnv0 : HbNonVmFields s s0 := by rw [hs0]; hb_nv_rfl s
  refine SepWP.weaken_pre_frame
    (P' := ((((s.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s.sp + 8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pin7) ∗ stackAt s.sp 0xe0) ∗ ?_)
    (fun R hm => by revert hm; sep_frame) ?_
  refine hcustom7 s0 _ (by rw [hs0]; hb_wp_simp) (by rw [hs0]; hb_wp_simp) (by rw [hs0]; hb_wp_simp)
    (by rw [hs0]; simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align)
    (by rw [hs0, ← hb]; hb_wp_simp) (by rw [hs0]; hb_wp_simp) (by rw [hs0]; hb_wp_simp) (by rw [hs0]; hb_wp_simp)
    hnv0 fun s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hx0_1 hnv1 => ?_
  clear hcustom7 hs0 hf_0 hf_1 hf_2 hf_3 hf_4 hf_5 hf_6 hf_7 hf_8 hf_9 hpc
  have hpc1_b : s1.pc = b + 40#64 := by rw [hpc1, ← hb]; bv_lin
  have hcs01 : CalleeSavedPreserved s s1 := hcs0.trans hcs1
  have hnv01 : HbNonVmFields (s.setSigAction 7#32 (hbCustomSigAction C S)) s1 :=
    HbNonVmFields.trans (s1 := s0.setSigAction 7#32 (hbCustomSigAction C S)) ⟨hnv0.1, hnv0.2.1, hnv0.2.2.1, by dsimp [State.setSigAction]; rw [hnv0.2.2.2.1], hnv0.2.2.2.2⟩ hnv1
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs01 with ⟨g19, g20, g21, g22, _, _, _, _, _, _, g29, _⟩
  have hx19_1 : s1.readReg64 (.gpr 19#5) = mainFnSlot := g19.trans hx19; have hx20_1 : s1.readReg64 (.gpr 20#5) = argvPtr := g20.trans hx20
  have hx21_1 : s1.readReg64 (.gpr 21#5) = C.langStartVtableAddr := g21.trans hx21; have hx22_1 : s1.readReg64 (.gpr 22#5) = BitVec.ofNat 64 argc := g22.trans hx22
  have hx29_1 : s1.readReg64 (.gpr 29#5) = fp_ls := g29.trans hx29
  clear hpc1 hcs0 hcs1 hcs01 hnv0 hnv1 hx0_1 g19 g20 g21 g22 g29 hx19 hx20 hx21 hx22 hx29
  wp_conv_pre => rw [hargv_eq]
  wp_steps 7
  refine hb_step_cut fun s2 hs2 => ?_
  have hsp2 : s2.sp = s.sp := by rw [hs2]; simpa [wp_norm, arm64_norm] using hsp1
  have hnv12 : HbNonVmFields s1 s2 := by rw [hs2]; hb_nv_rfl s1
  refine step_hb_langStartClosure_to_userMain (fp_ls := fp_ls) hclos hbsb (F := ?_)
    (fun R hm => by rw [hsp2]; rw [stackAt_split_bottom s.sp 0x20 192 (by decide)] at hm; revert hm; sep_frame)
    (by rw [hs2]; hb_wp_simp) (by rw [hs2]; hb_wp_simp)
    (by rw [hs2]; simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al1)
    (by rw [hs2]; hb_wp_simp) (by rw [hs2]; simp only [wp_norm, arm64_norm, hx29_1]) (by rw [hs2, ← hb]; hb_wp_simp)
    fun sf hpc_f hrun_f hsp_f hsp_al_f hx29_f hlr_f hnv2f => ?_
  refine hb_step_entail
    (hnext sf hpc_f hrun_f (by rw [hsp_f, hsp2]) hsp_al_f (by rw [hx29_f, hsp2]) hlr_f (hnv01.trans (hnv12.trans hnv2f)))
    (fun R hm => by
      rw [hsp2] at hm
      rw [hargv_eq, stackAt_split_bottom (s.sp - 32#64) 0xc0 320 (by decide),
          show (s.sp - 32#64) - BitVec.ofNat 64 (192 + 320) = s.sp - BitVec.ofNat 64 (224 + 320) by bv_lin]
      dsimp only [stackAt]; rw [show (s.sp - 32#64) - BitVec.ofNat 64 192 = s.sp - BitVec.ofNat 64 (32 + 192) by bv_lin]
      revert hm; sep_entail)

set_option maxHeartbeats 400000 in
private theorem step_hb_cMain_to_makeHandler {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc argvPtr tp v_mt v_ps : BitVec 64} {haveLse : BitVec 8} {argc : Nat}
    (hc_main : hasInstrs P C.std.cMainAddr (hbCMainInstrs C))
    (hhead : hasInstrs P C.langStartInternalAddr (hbLangStartHeadInstrs C S))
    (hloop : P.hasCode (C.langStartInternalAddr + 0x400#64) hbLangStartPollLoopWords)
    (hmid0 : P.hasCode (C.langStartInternalAddr + 0x1f8#64) hbLangStartMid0Words)
    (hmid1 : hasInstrs P (C.langStartInternalAddr + BitVec.ofNat 64 0x244) (hbLangStartMid1Instrs C))
    (hmid2 : hasInstrs P (C.langStartInternalAddr + BitVec.ofNat 64 0x2b8) (hbLangStartMid2Instrs C S)) (hargc : argc < 2 ^ 31)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R →
      s.mem ⊨ (((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ (C.std.threadIdCounterAddr ↦₆₄ 0#64) ∗
        ((tp + 0x58#64) ↦₆₄ 0#64) ∗ (S.mainThreadAddr ↦₆₄ v_mt) ∗ ((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗
        ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ v_ps) ∗ (C.needAltstackAddr ↦₈ 0#8)) ∗
        stackAt s.sp 0x340) ∗ (F ∗ R))
    (hpc : s.pc = C.std.cMainAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = C.std.libcStartMainStage2Addr + 0x38#64)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 argc) (hx1 : s.readReg64 .x1 = argvPtr) (htp : s.tpidrEl0 = tp)
    (hcas8 : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.cas8RelaxAddr → s0.status = .Running → s0.sp = s.sp - 0x120#64 → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 128#64 → s0.readReg64 .x0 = 0#64 → s0.readReg64 .x1 = 1#64 → s0.readReg64 .x2 = C.std.threadIdCounterAddr →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 128#64 → s1.status = .Running → s1.sp = s0.sp →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields s0 s1 →
        SepWP P target_pc s1 (((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ (C.std.threadIdCounterAddr ↦₆₄ 1#64)) ∗ G) post oom) →
      SepWP P target_pc s0 (((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ (C.std.threadIdCounterAddr ↦₆₄ 0#64)) ∗ G) post oom)
    (hpoll : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.pollAddr → s0.status = .Running → s0.sp = s.sp - 0x120#64 → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 184#64 → s0.readReg64 .x0 = s0.sp → s0.readReg64 .x1 = 3#64 → s0.readReg64 .x2 = 0#64 → s0.fs = s.fs →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 184#64 → s1.status = .Running → s1.sp = s0.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields s0 s1 →
        SepWP P target_pc s1 ((((s0.sp ↦₆₄ 0#64) ∗ ((s0.sp + 8#64) ↦₆₄ 1#64) ∗ ((s0.sp + 16#64) ↦₆₄ 2#64)) ∗ stackAt s0.sp 0x40) ∗ G) post oom) →
      SepWP P target_pc s0 ((((s0.sp ↦₆₄ 0#64) ∗ ((s0.sp + 8#64) ↦₆₄ 1#64) ∗ ((s0.sp + 16#64) ↦₆₄ 2#64)) ∗ stackAt s0.sp 0x40) ∗ G) post oom)
    (hsigpipe : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.signalAddr → s0.status = .Running → s0.sp = s.sp - 0x120#64 → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 588#64 → s0.readReg64 .x0 = 13#64 → s0.readReg64 .x1 = 1#64 → HbNonVmFields s s0 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 588#64 → s1.status = .Running → s1.sp = s0.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields (s0.setSigAction 13#32 (sigpipeIgnAction C.std)) s1 →
        SepWP P target_pc s1 (stackAt s0.sp 0x220 ∗ G) post oom) →
      SepWP P target_pc s0 (stackAt s0.sp 0x220 ∗ G) post oom)
    (hsysconf : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.sysconfAddr → s0.status = .Running → s0.sp = s.sp - 0x120#64 → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 604#64 → s0.readReg64 .x0 = 30#64 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 604#64 → s1.status = .Running → s1.sp = s0.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 4096#64 → HbNonVmFields s0 s1 →
        SepWP P target_pc s1 ((((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ stackAt s0.sp 0x190) ∗ G) post oom) →
      SepWP P target_pc s0 ((((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ stackAt s0.sp 0x190) ∗ G) post oom)
    (hprobe11 : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.sigactionAddr → s0.status = .Running → s0.sp = s.sp - 0x120#64 → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 660#64 → s0.readReg64 .x0 = 11#64 → s0.readReg64 .x1 = 0#64 → s0.readReg64 .x2 = s0.sp →
      HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction C.std)) s0 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 660#64 → s1.status = .Running → s1.sp = s0.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields s0 s1 →
        SepWP P target_pc s1 ((((s0.sp ↦₆₄ 0#64) ∗ ((s0.sp + 8#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x88#64) ↦₆₄ 0#64)) ∗ stackAt s0.sp 0xe0) ∗ G) post oom) →
      SepWP P target_pc s0 ((((s0.sp ↦₆₄ 0#64) ∗ ((s0.sp + 8#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x88#64) ↦₆₄ 0#64)) ∗ stackAt s0.sp 0xe0) ∗ G) post oom)
    (hnext : ∀ (sf : State) (w_cm0 : BitVec 64),
      sf.pc = C.makeStackHandlerAddr → sf.status = .Running → sf.sp = s.sp - 0x120#64 → sf.spAligned = true →
      sf.readReg64 .lr = C.langStartInternalAddr + 732#64 → sf.readReg64 .x0 = 1#64 →
      sf.readReg64 (.gpr 19#5) = s.sp - 0x18#64 → sf.readReg64 (.gpr 20#5) = argvPtr →
      sf.readReg64 (.gpr 21#5) = C.langStartVtableAddr → sf.readReg64 (.gpr 22#5) = BitVec.ofNat 64 argc →
      sf.readReg64 (.gpr 29#5) = s.sp - 0x80#64 →
      HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction C.std)) sf → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP P target_pc sf
        ((((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ (C.std.threadIdCounterAddr ↦₆₄ 1#64) ∗ ((tp + 0x58#64) ↦₆₄ 1#64) ∗ (S.mainThreadAddr ↦₆₄ 1#64) ∗
           ((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ (C.needAltstackAddr ↦₈ 1#8) ∗
           (((s.sp - 0x20#64) ↦₆₄ w_cm0) ∗ ((s.sp - 0x18#64) ↦₆₄ C.std.userMainAddr) ∗ ((s.sp - 0x10#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 0x08#64) ↦₆₄ (C.std.libcStartMainStage2Addr + 0x38#64))) ∗
           (((s.sp - 0x80#64) ↦₆₄ (s.sp - 0x10#64)) ∗ ((s.sp - 0x78#64) ↦₆₄ (C.std.cMainAddr + 0x34#64)) ∗
            ((s.sp - 0x70#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗ ((s.sp - 0x68#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗ ((s.sp - 0x60#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((s.sp - 0x58#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
            ((s.sp - 0x50#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((s.sp - 0x48#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗ ((s.sp - 0x40#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((s.sp - 0x38#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
            ((s.sp - 0x30#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((s.sp - 0x28#64) ↦₆₄ s.readReg64 (.gpr 19#5))) ∗
           (((s.sp - 0x120#64) ↦₆₄ 0#64) ∗ (((s.sp - 0x120#64) + 8#64) ↦₆₄ 0#64) ∗ (((s.sp - 0x120#64) + 0x88#64) ↦₆₄ 0#64) ∗
            cells ((s.sp - 0x120#64) + 16#64) 15 ∗ cells ((s.sp - 0x120#64) + 144#64) 2)) ∗
          stackAt (s.sp - 0x120#64) 0x220) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine step_hb_cMain_to_langStart hc_main hargc
    (fun R hm => by have h := hpre R hm; rw [stackAt_split_bottom s.sp 0x20 0x320 (by decide)] at h; revert h; sep_frame)
    hpc hrun hsp_align hlr hx0 hx1
    fun s1 w_cm0 hpc1 hrun1 hsp1 hsp_al1 hlr1 hx29_1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hnv01 hcs01 => ?_
  have hsp1_sub : s1.sp - 256#64 = s.sp - 0x120#64 := by rw [hsp1]; bv_lin
  have htp1 : s1.tpidrEl0 = tp := hnv01.2.2.1.trans htp
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs01 with ⟨g19_1, g20_1, g21_1, g22_1, g23_1, g24_1, g25_1, g26_1, g27_1, g28_1, _, gvg01⟩
  simp only [wp_norm, arm64_norm] at g19_1 g20_1 g21_1 g22_1 g23_1 g24_1 g25_1 g26_1 g27_1 g28_1 gvg01
  refine step_hb_langStart_head (v_mt := v_mt) (haveLse := haveLse) hhead hloop hmid0
    (fun R hm => by
      have hst : memRegion (s.sp - BitVec.ofNat 64 (32 + 800)) 800 = memRegion (s1.sp - BitVec.ofNat 64 (320 + 480)) 480 ∗ stackAt s1.sp 0x140 := by
        rw [← stackAt_split_bottom s1.sp 0x140 0x1e0 (by decide)]; dsimp only [stackAt]
        rw [hsp1, show (s.sp - 0x20#64) - BitVec.ofNat 64 0x320 = s.sp - BitVec.ofNat 64 (32 + 800) by bv_lin]
      rw [hst] at hm; revert hm; sep_frame)
    hpc1 hrun1 hsp_al1 hlr1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 htp1
    (fun s0 G hpc0 hrun0 hsp0 => hcas8 s0 G hpc0 hrun0 (hsp0.trans hsp1_sub))
    (fun s0 G hpc0 hrun0 hsp0 hsp_al0 hlr0 hx0_0 hx1_0 hx2_0 hfs0 => hpoll s0 G hpc0 hrun0 (hsp0.trans hsp1_sub) hsp_al0 hlr0 hx0_0 hx1_0 hx2_0 (hfs0.trans hnv01.1))
    fun s2 hpc2 hrun2 hsp2 hsp_al2 hx1_2 hx19_2 hx20_2 hx21_2 hx22_2 hx29_2 hnv12 hgv12 => ?_
  have hsp2_eq : s2.sp = s.sp - 0x120#64 := hsp2.trans hsp1_sub; have hnv02 : HbNonVmFields s s2 := hnv01.trans hnv12
  have hnv_sig02 : HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction C.std)) (s2.setSigAction 13#32 (sigpipeIgnAction C.std)) :=
    ⟨hnv02.1, hnv02.2.1, hnv02.2.2.1, by have h := hnv02.2.2.2.1; dsimp only [State.setSigAction] at h ⊢; rw [h], hnv02.2.2.2.2⟩
  refine step_hb_langStart_mid1 (v_ps := v_ps) hmid1
    (fun R hm => by
      rw [hsp2, stackAt_split_bottom (s1.sp - 256#64) 0x40 0x1e0 (by decide), show (s1.sp - 256#64) - BitVec.ofNat 64 (64 + 480) = s1.sp - BitVec.ofNat 64 (320 + 480) by bv_lin]
      revert hm; sep_frame)
    hpc2 hrun2 hsp_al2 hx1_2
    (fun s0 G hpc0 hrun0 hsp0 hsp_al0 hlr0 hx0_0 hx1_0 hnv20 hk => by
      rw [← hsp0]; refine hsigpipe s0 G hpc0 hrun0 (hsp0.trans hsp2_eq) hsp_al0 hlr0 hx0_0 hx1_0 (hnv02.trans hnv20) fun s3 hpc3 hrun3 hsp3 hsp_al3 hcs03 hx0_3 hnv03 => ?_
      rw [hsp0]; exact hk s3 hpc3 hrun3 (hsp3.trans hsp0) hsp_al3 hcs03 hx0_3 hnv03)
    (fun s0 G hpc0 hrun0 hsp0 hsp_al0 hlr0 hx0_0 hk => by
      rw [← hsp0]; refine hsysconf s0 G hpc0 hrun0 (hsp0.trans hsp2_eq) hsp_al0 hlr0 hx0_0 fun s3 hpc3 hrun3 hsp3 hsp_al3 hcs03 hx0_3 hnv03 => ?_
      rw [hsp0]; exact hk s3 hpc3 hrun3 (hsp3.trans hsp0) hsp_al3 hcs03 hx0_3 hnv03)
    (fun s0 G hpc0 hrun0 hsp0 hsp_al0 hlr0 hx0_0 hx1_0 hx2_0 hnv20 hk => by
      rw [← hsp0]; refine hprobe11 s0 G hpc0 hrun0 (hsp0.trans hsp2_eq) hsp_al0 hlr0 hx0_0 hx1_0 (hx2_0.trans hsp0.symm) (hnv_sig02.trans hnv20) fun s3 hpc3 hrun3 hsp3 hsp_al3 hcs03 hx0_3 hnv03 => ?_
      rw [hsp0]; exact hk s3 hpc3 hrun3 (hsp3.trans hsp0) hsp_al3 hcs03 hx0_3 hnv03)
    fun s3 hpc3 hrun3 hsp3 hsp_al3 hcs23 hnv23 => ?_
  refine step_hb_langStart_to_makeHandler (S := S) hmid2 (fun R hm => by revert hm; sep_frame) hpc3 hrun3 hsp_al3
    fun sf hpc_f hrun_f hsp_f hsp_al_f hlr_f hx0_f hcs3f hnv3f => ?_
  rcases (CalleeSavedPreserved.iff_regs _ _).mp (hcs23.trans hcs3f) with ⟨f19, f20, f21, f22, _, _, _, _, _, _, f29, fv⟩
  have hsp1_96 : s1.sp - 96#64 = s.sp - 0x80#64 := by rw [hsp1]; bv_lin
  refine hb_step_entail
    (hnext sf w_cm0 hpc_f hrun_f (hsp_f.trans (hsp3.trans hsp2_eq)) hsp_al_f hlr_f hx0_f
      (f19.trans hx19_2) (f20.trans hx20_2) (f21.trans hx21_2) (f22.trans hx22_2) (f29.trans (hx29_2.trans hsp1_96))
      (hnv_sig02.trans (hnv23.trans hnv3f)) (fv.trans (hgv12.trans gvg01)))
    (fun R hm => by
      rw [hsp2_eq, hsp1_96, show s1.sp - 88#64 = s.sp - 0x78#64 by rw [hsp1]; bv_lin,
          show s1.sp - 80#64 = s.sp - 0x70#64 by rw [hsp1]; bv_lin, show s1.sp - 72#64 = s.sp - 0x68#64 by rw [hsp1]; bv_lin,
          show s1.sp - 64#64 = s.sp - 0x60#64 by rw [hsp1]; bv_lin, show s1.sp - 56#64 = s.sp - 0x58#64 by rw [hsp1]; bv_lin,
          show s1.sp - 48#64 = s.sp - 0x50#64 by rw [hsp1]; bv_lin, show s1.sp - 40#64 = s.sp - 0x48#64 by rw [hsp1]; bv_lin,
          show s1.sp - 32#64 = s.sp - 0x40#64 by rw [hsp1]; bv_lin, show s1.sp - 24#64 = s.sp - 0x38#64 by rw [hsp1]; bv_lin,
          show s1.sp - 16#64 = s.sp - 0x30#64 by rw [hsp1]; bv_lin, show s1.sp - 8#64 = s.sp - 0x28#64 by rw [hsp1]; bv_lin,
          hx29_1, g28_1, g27_1, g26_1, g25_1, g24_1, g23_1, g22_1, g21_1, g20_1, g19_1] at hm
      revert hm; sep_entail)

private theorem fold_hbCallerFrames (C : HbCliLayout) (sp0 : BitVec 64)
    (w_cm0 fp_cm v28 v27 v26 v25 v24 v23 v22 v21 v20 v19 v0 v1 v17 : BitVec 64) {F : SepProp} {m : Memory}
    (hm : m ⊨
      ((((sp0 - 0x170#64) ↦₆₄ (sp0 - 0x160#64)) ∗ ((sp0 - 0x168#64) ↦₆₄ (C.langStartClosureAddr + 0x10#64)) ∗
        ((sp0 - 0x160#64) ↦₆₄ (sp0 - 0xb0#64)) ∗ ((sp0 - 0x158#64) ↦₆₄ (C.langStartInternalAddr + 0x394#64))) ∗
       (((sp0 - 0x150#64) ↦₆₄ v0) ∗ (((sp0 - 0x150#64) + 8#64) ↦₆₄ v1) ∗ (((sp0 - 0x150#64) + 0x88#64) ↦₆₄ v17) ∗
        cells ((sp0 - 0x150#64) + 16#64) 15 ∗ cells ((sp0 - 0x150#64) + 144#64) 2) ∗
       (((sp0 - 0x50#64) ↦₆₄ w_cm0) ∗ ((sp0 - 0x48#64) ↦₆₄ C.std.userMainAddr) ∗
        ((sp0 - 0x40#64) ↦₆₄ fp_cm) ∗ ((sp0 - 0x38#64) ↦₆₄ (C.std.libcStartMainStage2Addr + 0x38#64))) ∗
       (((sp0 - 0xb0#64) ↦₆₄ (sp0 - 0x40#64)) ∗ ((sp0 - 0xa8#64) ↦₆₄ (C.std.cMainAddr + 0x34#64)) ∗
        ((sp0 - 0xa0#64) ↦₆₄ v28) ∗ ((sp0 - 0x98#64) ↦₆₄ v27) ∗ ((sp0 - 0x90#64) ↦₆₄ v26) ∗ ((sp0 - 0x88#64) ↦₆₄ v25) ∗
        ((sp0 - 0x80#64) ↦₆₄ v24) ∗ ((sp0 - 0x78#64) ↦₆₄ v23) ∗ ((sp0 - 0x70#64) ↦₆₄ v22) ∗ ((sp0 - 0x68#64) ↦₆₄ v21) ∗
        ((sp0 - 0x60#64) ↦₆₄ v20) ∗ ((sp0 - 0x58#64) ↦₆₄ v19)) ∗ stackAt sp0 48) ∗ F) :
    m ⊨ HbCallerFrames C sp0 ∗ F := by
  unfold HbCallerFrames
  have h160 : stackAt (sp0 - 0xb0#64) 160 = cells (sp0 - 0x150#64) 20 := by
    rw [stackAt_eq_cells (sp0 - 0xb0#64) 20 (by decide), show (sp0 - 0xb0#64) - BitVec.ofNat 64 160 = sp0 - 0x150#64 by bv_lin]
  rw [h160, show (20 : Nat) = 2 + (15 + 3) from rfl, cells_split (sp0 - 0x150#64) 2 (15 + 3),
      cells_split ((sp0 - 0x150#64) + BitVec.ofNat 64 (8 * 2)) 15 3]
  simp only [Nat.reduceMul]
  rw [cells_succ (sp0 - 0x150#64) 1, cells_succ ((sp0 - 0x150#64) + 8#64) 0, cells_zero,
      show (sp0 - 0x150#64) + 16#64 + BitVec.ofNat 64 120 = (sp0 - 0x150#64) + 0x88#64 by bv_lin,
      cells_succ ((sp0 - 0x150#64) + 0x88#64) 2, show (sp0 - 0x150#64) + 0x88#64 + 8#64 = (sp0 - 0x150#64) + 144#64 by bv_lin]
  rw [stackAt_eq_cells (sp0 - 0x40#64) 12 (by decide)]
  simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero,
    sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  rw [show (sp0 - 0x40#64) - BitVec.ofNat 64 96 = sp0 - 0xa0#64 by bv_lin,
      show (sp0 - 0x40#64) - BitVec.ofNat 64 88 = sp0 - 0x98#64 by bv_lin,
      show (sp0 - 0x40#64) - BitVec.ofNat 64 80 = sp0 - 0x90#64 by bv_lin,
      show (sp0 - 0x40#64) - BitVec.ofNat 64 72 = sp0 - 0x88#64 by bv_lin,
      show (sp0 - 0x40#64) - BitVec.ofNat 64 64 = sp0 - 0x80#64 by bv_lin,
      show (sp0 - 0x40#64) - BitVec.ofNat 64 56 = sp0 - 0x78#64 by bv_lin,
      show (sp0 - 0x40#64) - BitVec.ofNat 64 48 = sp0 - 0x70#64 by bv_lin,
      show (sp0 - 0x40#64) - BitVec.ofNat 64 40 = sp0 - 0x68#64 by bv_lin,
      show (sp0 - 0x40#64) - BitVec.ofNat 64 32 = sp0 - 0x60#64 by bv_lin,
      show (sp0 - 0x40#64) - BitVec.ofNat 64 24 = sp0 - 0x58#64 by bv_lin,
      show (sp0 - 0x40#64) - BitVec.ofNat 64 16 = sp0 - 0x50#64 by bv_lin,
      show (sp0 - 0x40#64) - BitVec.ofNat 64 8  = sp0 - 0x48#64 by bv_lin]
  revert hm; sep_entail

private theorem fold_hbThreadIdInv_one (C : HbCliLayout) (tp : BitVec 64) {F : SepProp} {m : Memory}
    (hm : m ⊨ (((tp + 0x58#64) ↦₆₄ 1#64) ∗ (C.std.threadIdCounterAddr ↦₆₄ 1#64)) ∗ F) :
    m ⊨ HbThreadIdInv C tp ∗ F :=
  Satisfies.of_entails hm (sepConj_mono_left (hbThreadIdInv_one C tp))

private theorem fold_hbAltstackInv4k {C : HbCliLayout} {S : HbStartupLayout}
    {altBase : BitVec 64} {altRawSz : Nat} {F : SepProp} {m : Memory}
    (hbase4k : 4096 ≤ altBase.toNat) (hbaseAl : altBase.toNat % 4096 = 0)
    (hrawAl : altRawSz % 4096 = 0) (hrawLo : 12288 ≤ altRawSz)
    (hrawHi : altRawSz ≤ 524288) (hfit : altBase.toNat + altRawSz + 4096 ≤ 2 ^ 48)
    (hm : m ⊨
      ((S.threadInfoRootAddr ↦₆₄ 0#64) ∗ ((S.threadInfoRootAddr + 8#64) ↦₆₄ 0#64) ∗
       ((S.threadInfoRootAddr + 16#64) ↦₆₄ 0#64) ∗ (S.threadInfoLockAddr ↦₃₂ 0#32) ∗
       ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗ ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
       (C.mainAltstackAddr ↦₆₄ (altBase + 4096#64)) ∗
       memRegionProtNone altBase 4096 ∗ memRegion (altBase + 4096#64) altRawSz) ∗ F) :
    m ⊨ HbAltstackInv4k C S (some (altBase, altRawSz)) ∗ F := by
  dsimp only [HbAltstackInv4k]
  rw [← SepFrameInfer.pure_intro_eq ⟨hbase4k, hbaseAl, hrawAl, hrawLo, hrawHi, hfit⟩]; revert hm; sep_frame

private theorem hb_hasInstrs_withSvc {P : Program} {svc : State → State} {base : BitVec 64} {is : List Instr}
    (h : hasInstrs P base is) : hasInstrs (P.withSvc svc) base is := by
  intro i hi; rw [Program.withSvc_fetch]; exact h i hi

private theorem hb_seq_nonVm {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hext : ∀ pc, prog.externAt? pc = none) (hsvc : prog.svc = Syscall.standard)
    (h : SepWP (prog.withSvc nonVmSvc) mid s P (fun sm Pm => VmFieldsPreserved s sm → SepWP prog target sm Pm post oom)) :
    SepWP prog target s P post oom := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  rcases SepWP.to_reaches_pc h hm ((Program.withSvc_codeLoaded ..).mpr hL) with
    ⟨sm, hst1, ⟨_, hrun_m, Pm, hmm, hcont⟩ | ⟨_, hoom⟩⟩
  · rcases Steps.of_nonVm_running hext hsvc hst1 hrun_m with ⟨hst1P, hvm⟩
    obtain ⟨sf, hst2, hout⟩ := SepWP.to_reaches_pc (hcont hvm) hmm (hst1P.codeLoaded hL)
    exact ⟨sf, hst1P.trans hst2, hout⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩; exact False.elim hf

private theorem hb_done_nonVm {prog : Program} {mid : BitVec 64} {s sm : State} {Pm : SepProp} {post : State → SepProp → Prop}
    (hpc : sm.pc = mid) (hrun : sm.status = .Running) (hnext : VmFieldsPreserved s sm → post sm Pm) :
    SepWP prog mid sm Pm (fun sm' Pm' => VmFieldsPreserved s sm' → post sm' Pm') :=
  SepWP.done hpc hrun hnext

private theorem hb_nv_sas {s0 s1 : State} {sas : SigAltStack} (h : HbNonVmFields (s0.setSigAltStack sas) s1) :
    s1.fs = s0.fs ∧ s1.trace = s0.trace ∧ s1.tpidrEl0 = s0.tpidrEl0 ∧ s1.sigActions = s0.sigActions := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
private theorem hb_nv_act {s0 s1 : State} {sig : BitVec 32} {act : SigAction} (h : HbNonVmFields (s0.setSigAction sig act) s1) :
    s1.fs = s0.fs ∧ s1.trace = s0.trace ∧ s1.tpidrEl0 = s0.tpidrEl0 := ⟨h.1, h.2.1, h.2.2.1⟩

set_option maxHeartbeats 400000 in
/-- Step from `C.std.cMainAddr` (`sp = sp0 - 0x30#64`) to `C.std.userMainAddr`
    (`sp = sp0 - 0x170#64`), folding `HbCallerFrames C sp0`, `HbThreadIdInv C tp`, and
    `HbAltstackInv4k`. -/
public theorem hbCMain_to_userMain {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc sp0 argvPtr tp v_mt v_ps v_ma v_argc v_argv : BitVec 64}
    {haveLse : BitVec 8} {argc : Nat} {entries : List (BitVec 64 × BitVec 64)}
    {Pmh_in : SepProp} {Pmh_out : BitVec 64 → SepProp} {Pin11 Pcustom11 Pcustom7 : SepProp}
    (hcode : HbPreMainCode P C S)
    (hargv_eq : C.std.argvGlobalAddr = C.std.argcGlobalAddr + 8#64) (hargc : argc < 2 ^ 31)
    (hbnd : ∀ e ∈ entries, e.1 = 51#64 → e.2.toNat ≤ 524288)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R →
      s.mem ⊨ (((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ (C.std.threadIdCounterAddr ↦₆₄ 0#64) ∗
        ((tp + 0x58#64) ↦₆₄ 0#64) ∗ (S.mainThreadAddr ↦₆₄ v_mt) ∗
        ((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
        (C.std.pageSizeGlobalAddr ↦₆₄ v_ps) ∗ (C.needAltstackAddr ↦₈ 0#8) ∗ Pmh_in ∗
        (C.mainAltstackAddr ↦₆₄ v_ma) ∗ (C.std.argcGlobalAddr ↦₆₄ v_argc) ∗ (C.std.argvGlobalAddr ↦₆₄ v_argv) ∗
        ((C.langStartVtableAddr + 0x28#64) ↦₆₄ᵣ C.langStartClosureAddr) ∗
        (S.threadInfoRootAddr ↦₆₄ 0#64) ∗ ((S.threadInfoRootAddr + 8#64) ↦₆₄ 0#64) ∗
        ((S.threadInfoRootAddr + 16#64) ↦₆₄ 0#64) ∗ (S.threadInfoLockAddr ↦₃₂ 0#32) ∗
        ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗ ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
        Pin11 ∗ stackAt sp0 48 ∗ stackAt (sp0 - 0x30#64) 0x340) ∗ (F ∗ R)))
    (hpc : s.pc = C.std.cMainAddr) (hrun : s.status = .Running) (hsp : s.sp = sp0 - 0x30#64) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = C.std.libcStartMainStage2Addr + 0x38#64)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 argc) (hx1 : s.readReg64 .x1 = argvPtr) (htp : s.tpidrEl0 = tp)
    (hcas8 : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.cas8RelaxAddr → s0.status = .Running → s0.sp = s.sp - 0x120#64 → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 128#64 → s0.readReg64 .x0 = 0#64 → s0.readReg64 .x1 = 1#64 → s0.readReg64 .x2 = C.std.threadIdCounterAddr →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 128#64 → s1.status = .Running → s1.sp = s0.sp → CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields s0 s1 →
        SepWP (P.withSvc nonVmSvc) C.makeStackHandlerAddr s1 (((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ (C.std.threadIdCounterAddr ↦₆₄ 1#64)) ∗ G)
          (fun sm Pm => VmFieldsPreserved s sm → SepWP P target_pc sm Pm post oom)) →
      SepWP (P.withSvc nonVmSvc) C.makeStackHandlerAddr s0 (((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ (C.std.threadIdCounterAddr ↦₆₄ 0#64)) ∗ G)
        (fun sm Pm => VmFieldsPreserved s sm → SepWP P target_pc sm Pm post oom))
    (hpoll : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.pollAddr → s0.status = .Running → s0.sp = s.sp - 0x120#64 → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 184#64 → s0.readReg64 .x0 = s0.sp → s0.readReg64 .x1 = 3#64 → s0.readReg64 .x2 = 0#64 → s0.fs = s.fs →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 184#64 → s1.status = .Running → s1.sp = s0.sp → s1.spAligned = true → CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields s0 s1 →
        SepWP (P.withSvc nonVmSvc) C.makeStackHandlerAddr s1 ((((s0.sp ↦₆₄ 0#64) ∗ ((s0.sp + 8#64) ↦₆₄ 1#64) ∗ ((s0.sp + 16#64) ↦₆₄ 2#64)) ∗ stackAt s0.sp 0x40) ∗ G)
          (fun sm Pm => VmFieldsPreserved s sm → SepWP P target_pc sm Pm post oom)) →
      SepWP (P.withSvc nonVmSvc) C.makeStackHandlerAddr s0 ((((s0.sp ↦₆₄ 0#64) ∗ ((s0.sp + 8#64) ↦₆₄ 1#64) ∗ ((s0.sp + 16#64) ↦₆₄ 2#64)) ∗ stackAt s0.sp 0x40) ∗ G)
        (fun sm Pm => VmFieldsPreserved s sm → SepWP P target_pc sm Pm post oom))
    (hsigpipe : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.signalAddr → s0.status = .Running → s0.sp = s.sp - 0x120#64 → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 588#64 → s0.readReg64 .x0 = 13#64 → s0.readReg64 .x1 = 1#64 → HbNonVmFields s s0 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 588#64 → s1.status = .Running → s1.sp = s0.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields (s0.setSigAction 13#32 (sigpipeIgnAction C.std)) s1 →
        SepWP (P.withSvc nonVmSvc) C.makeStackHandlerAddr s1 (stackAt s0.sp 0x220 ∗ G) (fun sm Pm => VmFieldsPreserved s sm → SepWP P target_pc sm Pm post oom)) →
      SepWP (P.withSvc nonVmSvc) C.makeStackHandlerAddr s0 (stackAt s0.sp 0x220 ∗ G) (fun sm Pm => VmFieldsPreserved s sm → SepWP P target_pc sm Pm post oom))
    (hsysconf : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.sysconfAddr → s0.status = .Running → s0.sp = s.sp - 0x120#64 → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 604#64 → s0.readReg64 .x0 = 30#64 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 604#64 → s1.status = .Running → s1.sp = s0.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 4096#64 → HbNonVmFields s0 s1 →
        SepWP (P.withSvc nonVmSvc) C.makeStackHandlerAddr s1 ((((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ stackAt s0.sp 0x190) ∗ G)
          (fun sm Pm => VmFieldsPreserved s sm → SepWP P target_pc sm Pm post oom)) →
      SepWP (P.withSvc nonVmSvc) C.makeStackHandlerAddr s0 ((((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ stackAt s0.sp 0x190) ∗ G)
        (fun sm Pm => VmFieldsPreserved s sm → SepWP P target_pc sm Pm post oom))
    (hprobe11 : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.std.sigactionAddr → s0.status = .Running → s0.sp = s.sp - 0x120#64 → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 660#64 → s0.readReg64 .x0 = 11#64 → s0.readReg64 .x1 = 0#64 → s0.readReg64 .x2 = s0.sp →
      HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction C.std)) s0 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 660#64 → s1.status = .Running → s1.sp = s0.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields s0 s1 →
        SepWP (P.withSvc nonVmSvc) C.makeStackHandlerAddr s1 ((((s0.sp ↦₆₄ 0#64) ∗ ((s0.sp + 8#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x88#64) ↦₆₄ 0#64)) ∗ stackAt s0.sp 0xe0) ∗ G)
          (fun sm Pm => VmFieldsPreserved s sm → SepWP P target_pc sm Pm post oom)) →
      SepWP (P.withSvc nonVmSvc) C.makeStackHandlerAddr s0 ((((s0.sp ↦₆₄ 0#64) ∗ ((s0.sp + 8#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x88#64) ↦₆₄ 0#64)) ∗ stackAt s0.sp 0xe0) ∗ G)
        (fun sm Pm => VmFieldsPreserved s sm → SepWP P target_pc sm Pm post oom))
    (hmh : ∀ (s0 : State) (G : SepProp),
      s0.pc = C.makeStackHandlerAddr → s0.status = .Running → s0.sp = s.sp - 0x120#64 → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 732#64 → s0.readReg64 .x0 = 1#64 →
      HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction C.std)) s0 → VmFieldsPreserved s s0 →
      (∀ (s1 : State) (altBase : BitVec 64),
        4096 ≤ altBase.toNat → altBase.toNat % 4096 = 0 → altBase.toNat + (hbExpectedAltRawSz entries + 4096) ≤ 2 ^ 48 →
        s.mem.canMap altBase (hbExpectedAltRawSz entries + 4096) = true →
        s1.pc = C.langStartInternalAddr + 732#64 → s1.status = .Running → s1.sp = s0.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = altBase + 4096#64 →
        HbNonVmFields (s0.setSigAltStack { sp := altBase + 4096#64, size := BitVec.ofNat 64 (hbAltstackReqSz entries), ssFlags := 0#32 }) s1 →
        s1.physMemAvail = s.physMemAvail - (hbExpectedAltRawSz entries + 4096) → s1.brk = s.brk → s1.brkStart = s.brkStart →
        (∀ a, s1.mem.perm a = ((s.mem.mapZero altBase (hbExpectedAltRawSz entries + 4096)).setPermNonFrozen altBase 4096 Perm.protNone).perm a) →
        SepWP P target_pc s1
          (((memRegionProtNone altBase 4096 ∗ memRegion (altBase + 4096#64) (hbExpectedAltRawSz entries) ∗
             (C.needAltstackAddr ↦₈ 1#8) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
             ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ Pmh_out altBase) ∗ stackAt (s.sp - 0x120#64) 0x220) ∗ G) post oom) →
      SepWP P target_pc s0
        ((((C.needAltstackAddr ↦₈ 1#8) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
           ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ Pmh_in) ∗ stackAt (s.sp - 0x120#64) 0x220) ∗ G) post oom)
    (hcustom11 : ∀ (s_post s0 : State) (G : SepProp),
      s_post.sp = s.sp - 0x120#64 →
      s0.pc = C.std.sigactionAddr → s0.status = .Running → s0.sp = s_post.sp → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 780#64 → s0.readReg64 .x0 = 11#64 → s0.readReg64 .x1 = s_post.sp → s0.readReg64 .x2 = 0#64 → HbNonVmFields s_post s0 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 780#64 → s1.status = .Running → s1.sp = s_post.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields (s0.setSigAction 11#32 (hbCustomSigAction C S)) s1 →
        SepWP (P.withSvc nonVmSvc) C.std.userMainAddr s1
          (((((s_post.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s_post.sp + 8#64) ↦₆₄ 0#64) ∗ ((s_post.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pcustom11) ∗ stackAt s_post.sp 0xe0) ∗ G)
          (fun sm Pm => VmFieldsPreserved s_post sm → SepWP P target_pc sm Pm post oom)) →
      SepWP (P.withSvc nonVmSvc) C.std.userMainAddr s0
        (((((s_post.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s_post.sp + 8#64) ↦₆₄ 0#64) ∗ ((s_post.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pin11) ∗ stackAt s_post.sp 0xe0) ∗ G)
        (fun sm Pm => VmFieldsPreserved s_post sm → SepWP P target_pc sm Pm post oom))
    (hprobe7 : ∀ (s_post s0 : State) (G : SepProp),
      s_post.sp = s.sp - 0x120#64 → s_post.getSigAction 7#32 = s.getSigAction 7#32 →
      s0.pc = C.std.sigactionAddr → s0.status = .Running → s0.sp = s_post.sp → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 796#64 → s0.readReg64 .x0 = 7#64 → s0.readReg64 .x1 = 0#64 → s0.readReg64 .x2 = s_post.sp →
      HbNonVmFields (s_post.setSigAction 11#32 (hbCustomSigAction C S)) s0 →
      (∀ s1 : State, s1.pc = C.langStartInternalAddr + 796#64 → s1.status = .Running → s1.sp = s_post.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields s0 s1 →
        SepWP (P.withSvc nonVmSvc) C.std.userMainAddr s1
          ((((s_post.sp ↦₆₄ 0#64) ∗ ((s_post.sp + 8#64) ↦₆₄ 0#64) ∗ ((s_post.sp + 0x88#64) ↦₆₄ 0#64)) ∗ stackAt s_post.sp 0xe0) ∗ G)
          (fun sm Pm => VmFieldsPreserved s_post sm → SepWP P target_pc sm Pm post oom)) →
      SepWP (P.withSvc nonVmSvc) C.std.userMainAddr s0
        ((((s_post.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s_post.sp + 8#64) ↦₆₄ 0#64) ∗ ((s_post.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ stackAt s_post.sp 0xe0) ∗ G)
        (fun sm Pm => VmFieldsPreserved s_post sm → SepWP P target_pc sm Pm post oom))
    (hcustom7 : ∀ (s_post s1 s0 : State) (G : SepProp),
      s_post.sp = s.sp - 0x120#64 → s1.sp = s_post.sp → HbNonVmFields (s_post.setSigAction 11#32 (hbCustomSigAction C S)) s1 →
      s0.pc = C.std.sigactionAddr → s0.status = .Running → s0.sp = s1.sp → s0.spAligned = true →
      s0.readReg64 .lr = C.langStartInternalAddr + 888#64 → s0.readReg64 .x0 = 7#64 → s0.readReg64 .x1 = s1.sp → s0.readReg64 .x2 = 0#64 → HbNonVmFields s1 s0 →
      (∀ s2 : State, s2.pc = C.langStartInternalAddr + 888#64 → s2.status = .Running → s2.sp = s1.sp → s2.spAligned = true →
        CalleeSavedPreserved s0 s2 → s2.readReg64 .x0 = 0#64 → HbNonVmFields (s0.setSigAction 7#32 (hbCustomSigAction C S)) s2 →
        SepWP (P.withSvc nonVmSvc) C.std.userMainAddr s2
          (((((s1.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s1.sp + 8#64) ↦₆₄ 0#64) ∗ ((s1.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pcustom7) ∗ stackAt s1.sp 0xe0) ∗ G)
          (fun sm Pm => VmFieldsPreserved s_post sm → SepWP P target_pc sm Pm post oom)) →
      SepWP (P.withSvc nonVmSvc) C.std.userMainAddr s0
        (((((s1.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s1.sp + 8#64) ↦₆₄ 0#64) ∗ ((s1.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pcustom11) ∗ stackAt s1.sp 0xe0) ∗ G)
        (fun sm Pm => VmFieldsPreserved s_post sm → SepWP P target_pc sm Pm post oom))
    (hnext : ∀ (sf : State) (altBase : BitVec 64),
      4096 ≤ altBase.toNat → altBase.toNat % 4096 = 0 → altBase.toNat + (hbExpectedAltRawSz entries + 4096) ≤ 2 ^ 48 →
      s.mem.canMap altBase (hbExpectedAltRawSz entries + 4096) = true →
      sf.pc = C.std.userMainAddr → sf.status = .Running → sf.sp = sp0 - 0x170#64 → sf.spAligned = true →
      sf.readReg64 .x29 = sp0 - 0x170#64 → sf.readReg64 .lr = C.std.beginShortBacktraceAddr + 0x0c#64 →
      sf.fs = s.fs → sf.trace = s.trace → sf.tpidrEl0 = tp →
      sf.physMemAvail = s.physMemAvail - (hbExpectedAltRawSz entries + 4096) → sf.brk = s.brk → sf.brkStart = s.brkStart →
      (∀ a, sf.mem.perm a = ((s.mem.mapZero altBase (hbExpectedAltRawSz entries + 4096)).setPermNonFrozen altBase 4096 Perm.protNone).perm a) →
      SepWP P target_pc sf
        ((((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ HbThreadIdInv C tp ∗ (S.mainThreadAddr ↦₆₄ 1#64) ∗
           ((C.std.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
           (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ (C.needAltstackAddr ↦₈ 1#8) ∗ Pmh_out altBase ∗ Pcustom7 ∗
           (C.std.argcGlobalAddr ↦₆₄ BitVec.ofNat 64 argc) ∗ (C.std.argvGlobalAddr ↦₆₄ argvPtr) ∗
           ((C.langStartVtableAddr + 0x28#64) ↦₆₄ᵣ C.langStartClosureAddr) ∗
           HbAltstackInv4k C S (some (altBase, hbExpectedAltRawSz entries)) ∗ HbCallerFrames C sp0) ∗
          stackAt (sp0 - 0x170#64) 0x200) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  have hext : ∀ pc, P.externAt? pc = none := hcode.no_hooks; have hsvc : P.svc = Syscall.standard := hcode.svc_eq
  rcases hcode.langStart with ⟨hc_main, hhead, hloop, hmid0, hmid1, hmid2, htail, hclos, hbsb⟩
  have ⟨hrawAl, hrawLo, hrawHi⟩ := hbExpectedAltRawSz_spec hbnd
  refine hb_seq_nonVm (mid := C.makeStackHandlerAddr) hext hsvc ?_
  refine step_hb_cMain_to_makeHandler (P := P.withSvc nonVmSvc) (argvPtr := argvPtr) (tp := tp) (v_mt := v_mt) (v_ps := v_ps) (haveLse := haveLse)
    (hb_hasInstrs_withSvc hc_main) (hb_hasInstrs_withSvc hhead) hloop hmid0 (hb_hasInstrs_withSvc hmid1) (hb_hasInstrs_withSvc hmid2) hargc
    (fun R hm => by have h := hpre R hm; rw [← hsp] at h; revert h; sep_frame)
    hpc hrun hsp_align hlr hx0 hx1 htp hcas8 hpoll hsigpipe hsysconf hprobe11
    fun s_mh w_cm0 hpc_mh hrun_mh hsp_mh hsp_al_mh hlr_mh hx0_mh hx19_mh hx20_mh hx21_mh hx22_mh hx29_mh hnv_mh _ => ?_
  refine hb_done_nonVm hpc_mh hrun_mh fun hvm1 => ?_
  refine SepWP.weaken_pre_frame
    (P' := ((((C.needAltstackAddr ↦₈ 1#8) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ Pmh_in) ∗ stackAt (s.sp - 0x120#64) 0x220) ∗ ?_))
    (fun R hm => by revert hm; sep_frame) ?_
  refine hmh s_mh _ hpc_mh hrun_mh hsp_mh hsp_al_mh hlr_mh hx0_mh hnv_mh hvm1
    fun s_post altBase hbase4k hbaseAl hbaseFit hbaseMap hpc_post hrun_post hsp_post hsp_al_post hcs_post hx0_post hnv_post hphys_post hbrk_post hbrkS_post hperm_post => ?_
  have hsp_post_eq : s_post.sp = s.sp - 0x120#64 := hsp_post.trans hsp_mh
  have ⟨hfs_mh, htr_mh, htp_mh⟩ := hb_nv_act hnv_mh; have ⟨hfs_p, htr_p, htp_p, hsig_p⟩ := hb_nv_sas hnv_post
  have hsig7_post : s_post.getSigAction 7#32 = s.getSigAction 7#32 := by
    change s_post.sigActions 7#32 = s.sigActions 7#32; rw [hsig_p, hnv_mh.2.2.2.1]; simp
  refine hb_seq_nonVm (mid := C.std.userMainAddr) hext hsvc ?_
  refine step_hb_langStart_after_makeHandler (P := P.withSvc nonVmSvc) (S := S) (altStackSp := altBase + 4096#64) (v_ma := v_ma) (Pin11 := Pin11) (Pcustom11 := Pcustom11)
    (hb_hasInstrs_withSvc hmid2) (fun R hm => by rw [← hsp_post_eq, stackAt_split_bottom s_post.sp 0xe0 320 (by decide)] at hm; revert hm; sep_frame)
    hpc_post hrun_post hsp_al_post hx0_post (fun s0 G => hcustom11 s_post s0 G hsp_post_eq) (fun s0 G => hprobe7 s_post s0 G hsp_post_eq hsig7_post)
    fun s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hnv1 => ?_
  refine step_hb_langStart_tail_to_userMain (P := P.withSvc nonVmSvc) (mainFnSlot := s.sp - 0x18#64) (argvPtr := argvPtr) (fp_ls := s.sp - 0x80#64)
    (v_argc := v_argc) (v_argv := v_argv) (argc := argc) (Pin7 := Pcustom11) (Pcustom7 := Pcustom7)
    (hb_hasInstrs_withSvc htail) (hb_hasInstrs_withSvc hclos) hbsb hargv_eq
    (fun R hm => by rw [hsp1, stackAt_split_bottom s_post.sp 0xe0 320 (by decide)]; revert hm; sep_frame) hpc1 hrun1 hsp_al1
    (hcs1.readReg64_x19.trans (hcs_post.readReg64_x19.trans hx19_mh)) (hcs1.readReg64_x20.trans (hcs_post.readReg64_x20.trans hx20_mh))
    (hcs1.readReg64_x21.trans (hcs_post.readReg64_x21.trans hx21_mh)) (hcs1.readReg64_x22.trans (hcs_post.readReg64_x22.trans hx22_mh))
    (hcs1.readReg64_x29.trans (hcs_post.readReg64_x29.trans hx29_mh)) (fun s0 G => hcustom7 s_post s1 s0 G hsp_post_eq hsp1 hnv1)
    fun sf hpc_f hrun_f hsp_f hsp_al_f hx29_f hlr_f hnv_f => ?_
  refine hb_done_nonVm hpc_f hrun_f fun hvm2 => ?_
  have ⟨hfs1, htr1, htp1⟩ := hb_nv_act hnv1; have ⟨hfs_f, htr_f, htp_f⟩ := hb_nv_act hnv_f
  have hsp_f_eq : sf.sp = sp0 - 0x170#64 := by rw [hsp_f, hsp1, hsp_post_eq, hsp]; bv_lin
  have hx29_f_eq : sf.readReg64 .x29 = sp0 - 0x170#64 := by rw [hx29_f, hsp1, hsp_post_eq, hsp]; bv_lin
  have hsp1_sub : s1.sp - 32#64 = sp0 - 0x170#64 := by rw [hsp1, hsp_post_eq, hsp]; bv_lin
  refine hb_step_entail
    (hnext sf altBase hbase4k hbaseAl hbaseFit hbaseMap hpc_f hrun_f hsp_f_eq hsp_al_f hx29_f_eq hlr_f
      (hfs_f.trans (hfs1.trans (hfs_p.trans hfs_mh))) (htr_f.trans (htr1.trans (htr_p.trans htr_mh)))
      (htp_f.trans (htp1.trans (htp_p.trans (htp_mh.trans htp))))
      (hvm2.physMemAvail_eq.trans hphys_post) (hvm2.brk_eq.trans hbrk_post) (hvm2.brkStart_eq.trans hbrkS_post) (fun a => (hvm2.perm_eq a).trans (hperm_post a)))
    (fun R hm => ?_)
  rw [hsp1_sub, hsp1, hsp_post_eq,
      show s.sp - 0x20#64 = sp0 - 0x50#64 by rw [hsp]; bv_lin, show s.sp - 0x18#64 = sp0 - 0x48#64 by rw [hsp]; bv_lin,
      show s.sp - 0x10#64 = sp0 - 0x40#64 by rw [hsp]; bv_lin, show s.sp - 0x08#64 = sp0 - 0x38#64 by rw [hsp]; bv_lin,
      show s.sp - 0x80#64 = sp0 - 0xb0#64 by rw [hsp]; bv_lin, show s.sp - 0x78#64 = sp0 - 0xa8#64 by rw [hsp]; bv_lin,
      show s.sp - 0x70#64 = sp0 - 0xa0#64 by rw [hsp]; bv_lin, show s.sp - 0x68#64 = sp0 - 0x98#64 by rw [hsp]; bv_lin,
      show s.sp - 0x60#64 = sp0 - 0x90#64 by rw [hsp]; bv_lin, show s.sp - 0x58#64 = sp0 - 0x88#64 by rw [hsp]; bv_lin,
      show s.sp - 0x50#64 = sp0 - 0x80#64 by rw [hsp]; bv_lin, show s.sp - 0x48#64 = sp0 - 0x78#64 by rw [hsp]; bv_lin,
      show s.sp - 0x40#64 = sp0 - 0x70#64 by rw [hsp]; bv_lin, show s.sp - 0x38#64 = sp0 - 0x68#64 by rw [hsp]; bv_lin,
      show s.sp - 0x30#64 = sp0 - 0x60#64 by rw [hsp]; bv_lin, show s.sp - 0x28#64 = sp0 - 0x58#64 by rw [hsp]; bv_lin,
      show s.sp - 0x120#64 = sp0 - 0x150#64 by rw [hsp]; bv_lin,
      show (sp0 - 0x150#64) - 16#64 = sp0 - 0x160#64 by bv_lin, show (sp0 - 0x150#64) - 8#64 = sp0 - 0x158#64 by bv_lin,
      show (sp0 - 0x150#64) - 24#64 = sp0 - 0x168#64 by bv_lin] at hm
  sep_frame_apply (fold_hbCallerFrames C sp0 w_cm0 (s.readReg64 (.gpr 29#5)) (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 27#5))
    (s.readReg64 (.gpr 26#5)) (s.readReg64 (.gpr 25#5)) (s.readReg64 (.gpr 24#5)) (s.readReg64 (.gpr 23#5))
    (s.readReg64 (.gpr 22#5)) (s.readReg64 (.gpr 21#5)) (s.readReg64 (.gpr 20#5)) (s.readReg64 (.gpr 19#5)) S.signalHandlerAddr 0#64 0x08000004#64)
  sep_frame_apply (fold_hbAltstackInv4k (C := C) (S := S) hbase4k hbaseAl hrawAl hrawLo hrawHi (by rw [Nat.add_assoc]; exact hbaseFit))
  sep_frame_apply (fold_hbThreadIdInv_one C tp)
  revert hm; sep_entail

end

end CaseStudies.Hashbrown.Proofs.StdCli
