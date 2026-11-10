/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.BV
public import ProofLib.ProgramReflection
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.MuslStage1Init
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.SepLogic.WPp
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Placed `<String as Clone>::clone` over Budget-Threaded `mallocng`

Machine-code verification of `rustc 1.98.1` `<alloc::string::String as core::clone::Clone>::clone`
(`33` instructions, `0x00..0x84`) and `alloc::raw_vec::handle_error` (`5` instructions, `0x00..0x14`)
over `RustCliAllocBudget M`, together with `WordTree` entrypoints and 1-hop / 2-hop `B`-stub alias
lifts.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Proofs.Placed.StringCloneMallocngPlaced

open _root_.Arm64 ProofLib SepProp
open ProofLib.SepLogic
open ProofLib.ProgramReflection
open ProofLib.StdStartup
open ProofLib.StdStartup.Stage1Internal (step_str64_perm)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget RustAllocAddrs RustCliAllocBudgetEntriesBase
   FitsEvents FitsEnv NullAllowed RustLayoutOk VmPreserved OomPreserved AllocCallPreserved
   rustAllocEvents rustCliAllocBudgetSpecBase)
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (stringCloneEvents StringCloneEnv stringCloneBudgetCondSpec stringCloneNoOomSpec
   stringCloneBudgetSpec subroutine_ok_stringCloneNoOom_of_cond
   subroutine_ok_stringCloneBudget_of_noOom subroutine_ok_stringCloneBudget_of_cond
   rustAllocShimVmSpec allocMemcpyVmSpec rustHandleErrorPanicSpec RustStdAllocAuxEntries
   extHookStack_split_48 hasShimInstrs_of_wordTree checkBranchStub2
   subroutine_ok_of_branchStub subroutine_ok_of_branchStub_wordTree
   subroutine_ok_of_branchStub2 subroutine_ok_of_branchStub2_wordTree)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8 vecU8At allocHookStack LayoutOk)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open VerifiedLibraries.RustStd
  (allocCallPreserved_trans checkShimInstrsAt fetch_instr_at fetch_instr_at0
   hookFrame_eq_stackFrame4096)

private theorem bv_sub_add_cancel48 (sp : BitVec 64) : sp - 48#64 + 48#64 = sp := by bv_omega
private theorem bv_add_neg48 (sp : BitVec 64) : sp + (-48#64) = sp - 48#64 := by bv_omega
private theorem bv_add_neg16 (sp : BitVec 64) : sp + (-16#64) = sp - 16#64 := by bv_omega

@[local simp, local arm64_norm]
private theorem sigActions_setPC_eq (s : State) (pc : BitVec 64) :
    (s.setPC pc).sigActions = s.sigActions := by cases s; rfl
@[local simp, local arm64_norm]
private theorem sigActions_setMem_eq (s : State) (m : Memory) :
    (s.setMem m).sigActions = s.sigActions := by cases s; rfl
@[local simp, local arm64_norm]
private theorem sigActions_writeReg64_eq (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).sigActions = s.sigActions := by cases s; cases r <;> rfl
@[local simp, local arm64_norm]
private theorem setMem_setMem_eq (s : State) (m1 m2 : Memory) :
    (s.setMem m1).setMem m2 = s.setMem m2 := by cases s; rfl
@[local simp, local arm64_norm]
private theorem setPC_setMem_eq (s : State) (m : Memory) (pc : BitVec 64) :
    (s.setMem m).setPC pc = (s.setPC pc).setMem m := by cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_setMem_eq (s : State) (m : Memory) : (s.setMem m).mem = m := by cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_setPC_eq (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by
  cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_writeReg64_eq (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl

private theorem pool_setMem_perm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {m : Memory} (hm : m.perm = s.mem.perm) :
    A.pool lim st (s.setMem m) = A.pool lim st s :=
  A.pool_transport lim st s _ ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl,
    fun a => by cases s; exact congrFun hm a,
    by cases s; exact LibsignalBinary.Heap.FdsHiFrame.refl _⟩

private theorem step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W64 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr,
      hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 (funext fun a => by rw [Memory.perm_write64, Memory.perm_write64])) hm2

local macro "wp_str64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

local macro "wp_stp64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stp64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_cancel48 bv_add_neg48 bv_add_neg16

/-! ## 1. `liballoc` Instruction Sequences and Decode Checks -/

/-- Verbatim 33-instruction (`0x00..0x84`, `132` B) AArch64 machine code of
    `<alloc::string::String as core::clone::Clone>::clone` from `rustc 1.98.1`
    `aarch64-unknown-linux-musl` `liballoc-33b97f6bdb98e862.rlib`
    (`alloc-33b97f6bdb98e862.alloc.ca0639e201ef4727-cgu.0.rcgu.o`, symbol
    `_RNvXs4_NtCshlmZ2E5RoO1_5alloc6stringNtB5_6StringNtNtCs2kXltWtc1W_4core5clone5Clone5clone`,
    offsets `0x00..0x84`). -/
def rustStringCloneInstrs
    (fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64) : List Instr :=
  [ .stp .W64 .x29 .x30 (.PreIndex .sp (-0x30#64)), .stp .W64 .x22 .x21 (.Offset .sp 0x10#64),
    .stp .W64 .x20 .x19 (.Offset .sp 0x20#64), .addSubImm .W64 .ADD .x29 .sp 0x0#12 false,
    .ldr .W64 .X64 false .x19 (.Offset .x0 0x10#64), .logicalShift .W64 .ORR .x20 .xzr .x8 .LSL 0,
    .cbz .W64 false .x19 0x44#64, .ldr .W64 .X64 false .x22 (.Offset .x0 0x8#64),
    .bl (shimAddr - (fnAddr + 0x20#64)), .logicalShift .W64 .ORR .x0 .xzr .x19 .LSL 0,
    .moveWide .W32 .MOVZ .x1 0x1#16 0, .bl (allocAddr - (fnAddr + 0x2c#64)),
    .cbz .W64 false .x0 0x48#64, .logicalShift .W64 .ORR .x1 .xzr .x22 .LSL 0,
    .logicalShift .W64 .ORR .x2 .xzr .x19 .LSL 0, .logicalShift .W64 .ORR .x21 .xzr .x0 .LSL 0,
    .bl (memcpyAddr - (fnAddr + 0x40#64)), .stp .W64 .x19 .x21 (.Offset .x20 0x0#64),
    .str .X64 .x19 (.Offset .x20 0x10#64), .ldp .W64 false .x20 .x19 (.Offset .sp 0x20#64),
    .ldp .W64 false .x22 .x21 (.Offset .sp 0x10#64), .ldp .W64 false .x29 .x30 (.PostIndex .sp 0x30#64),
    .ret .x30, .moveWide .W32 .MOVZ .x21 0x1#16 0,
    .stp .W64 .x19 .x21 (.Offset .x20 0x0#64), .str .X64 .x19 (.Offset .x20 0x10#64),
    .ldp .W64 false .x20 .x19 (.Offset .sp 0x20#64), .ldp .W64 false .x22 .x21 (.Offset .sp 0x10#64),
    .ldp .W64 false .x29 .x30 (.PostIndex .sp 0x30#64), .ret .x30,
    .moveWide .W32 .MOVZ .x0 0x1#16 0, .logicalShift .W64 .ORR .x1 .xzr .x19 .LSL 0,
    .bl (handleErrorAddr - (fnAddr + 0x80#64)) ]

theorem rustStringCloneInstrs_length (f sh al mc he : BitVec 64) :
    (rustStringCloneInstrs f sh al mc he).length = 33 := rfl

private theorem rustStringCloneInstrs_template_eq :
    ([ 0xa9bd7bfd#32, 0xa90157f6#32, 0xa9024ff4#32, 0x910003fd#32,
       0xf9400813#32, 0xaa0803f4#32, 0xb4000233#32, 0xf9400416#32,
       0x94000000#32, 0xaa1303e0#32, 0x52800021#32, 0x94000000#32,
       0xb4000240#32, 0xaa1603e1#32, 0xaa1303e2#32, 0xaa0003f5#32,
       0x94000000#32, 0xa9005693#32, 0xf9000a93#32, 0xa9424ff4#32,
       0xa94157f6#32, 0xa8c37bfd#32, 0xd65f03c0#32, 0x52800035#32,
       0xa9005693#32, 0xf9000a93#32, 0xa9424ff4#32, 0xa94157f6#32,
       0xa8c37bfd#32, 0xd65f03c0#32, 0x52800020#32, 0xaa1303e1#32,
       0x94000000#32 ] : List (BitVec 32)).map Arm64.decode =
      (rustStringCloneInstrs 0#64 0x20#64 0x2c#64 0x40#64 0x80#64).map some := by
  decide

/-- Verbatim 5-instruction (`0x00..0x14`, `20` B) AArch64 machine code of
    `alloc::raw_vec::handle_error` from `liballoc-33b97f6bdb98e862.rlib`
    (`_RNvNtCshlmZ2E5RoO1_5alloc7raw_vec12handle_error`, offsets `0x00..0x14`). -/
def rustHandleErrorInstrs
    (fnAddr capOverflowAddr allocErrAddr : BitVec 64) : List Instr :=
  [ .stp .W64 .x29 .x30 (.PreIndex .sp (-0x10#64)),
    .addSubImm .W64 .ADD .x29 .sp 0x0#12 false,
    .cbz .W64 true .x0 0x08#64,
    .bl (capOverflowAddr - (fnAddr + 0x0c#64)),
    .bl (allocErrAddr - (fnAddr + 0x10#64)) ]

private theorem rustHandleErrorInstrs_template_eq :
    ([ 0xa9bf7bfd#32, 0x910003fd#32, 0xb5000040#32, 0x94000000#32, 0x94000000#32 ] :
        List (BitVec 32)).map Arm64.decode =
      (rustHandleErrorInstrs 0#64 0x0c#64 0x10#64).map some := by
  decide

/-! ## 2. Stack, Header, and `handle_error` Helpers -/

private theorem spAligned_sub16 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 16#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_robdd

private theorem spAligned_sub48 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 48#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_robdd

private theorem stackFrameAt16_eq (sp : BitVec 64) :
    stackFrameAt sp 16 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1)) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]

private theorem stackFrameAt48_eq (sp : BitVec 64) :
    stackFrameAt sp 48 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
        ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
        ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]

private theorem pack_stack48 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
     ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
     ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢ stackFrameAt sp 48 := by
  rw [stackFrameAt48_eq sp]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.refl _))))))

private theorem sepWP_done_let {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (h : ∀ sm, sm = s → sm.pc = mid → sm.status = .Running → SepWPp prog ret sm P Q Qp oom) :
    SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp oom) oom :=
  SepWP.done hpc hrun (h s rfl hpc hrun)

private theorem memRegion24_eq_exists_pts (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64,
        (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r2)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) from rfl,
      memRegion_split a 8 (8 + 8) (by decide),
      memRegion_split (a + 8#64) 8 8 (by decide),
      memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [sepExists_sepConj_left]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_right, sepExists_sepConj_right]

private theorem stackAt_allocHook_split16 (sp : BitVec 64) :
    stackAt sp allocHookStack =
      stackFrameAt sp 16 ∗ stackFrameAt (sp - 16#64) 4080 := by
  change Rust.hookFrame sp = _
  rw [hookFrame_eq_stackFrame4096 sp,
      show (4096 : Nat) = 16 + 4080 from rfl,
      stackFrameAt_split sp 16 4080 (by decide)]

/-- Discharge `rustHandleErrorPanicSpec` when `handle_error` is linked as compiled code (`5` insns)
    calling `capOverflowAddr` (`x0 = 0`) and `allocErrAddr` (`x0 ≠ 0`), both mapped to `Rust.panicked`. -/
theorem rustHandleErrorPanic_of_hasInstrs {P : Program}
    {fnAddr capOverflowAddr allocErrAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr (rustHandleErrorInstrs fnAddr capOverflowAddr allocErrAddr))
    (hCapExt : P.externAt? capOverflowAddr = some Rust.panicked)
    (hAllocExt : P.externAt? allocErrAddr = some Rust.panicked) :
    subroutine_ok P fnAddr rustHandleErrorPanicSpec := by
  apply subroutine_ok_of_sepWPp_init
  intro _ R s0 hpc hrun hpre hsp
  dsimp only [rustHandleErrorPanicSpec] at hpre ⊢
  refine ⟨stackFrameAt s0.sp 16, hpre, ?_⟩
  rw [stackFrameAt16_eq s0.sp]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => ?_
  have hf0 := fetch_instr_at0 hCode
  have hf1 := fetch_instr_at 1 hCode
  have hf2 := fetch_instr_at 2 hCode
  have hf3 := fetch_instr_at 3 hCode
  have hf4 := fetch_instr_at 4 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp
  have hspAl16 : decide ((s0.sp - 16#64) &&& 15#64 = 0#64) = true :=
    decide_eq_true (beq_iff_eq.mp (spAligned_sub16 hspAl0))
  by_cases hx0 : s0.readReg64 .x0 = 0#64
  · apply SepWPp.of_sepWP (mid := capOverflowAddr)
    wp_step; wp_step; wp_step; wp_step
    refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
      (by simp [arm64_norm, hrun]) fun sm hsm hpcm hrunm => ?_
    have hfs : sm.fs = s0.fs := by rw [hsm]; simp [arm64_norm]
    have htr : sm.trace = s0.trace := by rw [hsm]; simp [arm64_norm]
    clear hsm
    refine SepWPp.panic hrunm (hpcm ▸ hCapExt) fun hm => ?_
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [Rust.panicked, hfs], by simp [Rust.panicked, htr]⟩,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm⟩
  · apply SepWPp.of_sepWP (mid := allocErrAddr)
    wp_step; wp_step; wp_step
    refine SepWP.ite_true rfl (by rw [beq_false_of_ne hx0]; decide) ?_
    wp_step
    refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
      (by simp [arm64_norm, hrun]) fun sm hsm hpcm hrunm => ?_
    have hfs : sm.fs = s0.fs := by rw [hsm]; simp [arm64_norm]
    have htr : sm.trace = s0.trace := by rw [hsm]; simp [arm64_norm]
    clear hsm
    refine SepWPp.panic hrunm (hpcm ▸ hAllocExt) fun hm => ?_
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [Rust.panicked, hfs], by simp [Rust.panicked, htr]⟩,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm⟩

theorem rustHandleErrorPanic_of_wordTree {P : Program} {t : WordTree}
    (n : Nat) {fnAddr capOverflowAddr allocErrAddr : BitVec 64}
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 5 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (rustHandleErrorInstrs fnAddr capOverflowAddr allocErrAddr) = true)
    (hCapExt : P.externAt? capOverflowAddr = some Rust.panicked)
    (hAllocExt : P.externAt? allocErrAddr = some Rust.panicked) :
    subroutine_ok P fnAddr rustHandleErrorPanicSpec :=
  rustHandleErrorPanic_of_hasInstrs
    (hasShimInstrs_of_wordTree n hcode hwf hhook hok) hCapExt hAllocExt

/-! ## 3. `vecGhostAt` and `vecU8` Decomposition Helpers -/

private theorem vecGhostAt_bytes_lt_2pow63 {A : RustAlloc}
    {m : Memory} {g : VecGhost} {p : BitVec 64} {R : SepProp}
    (hm : m ⊨ vecGhostAt A g p ∗ R) :
    g.bytes.length < 2 ^ 63 := by
  unfold vecGhostAt vecU8At at hm
  have hPull :
      (vecHeader p g.cap g.ptr (BitVec.ofNat 64 g.bytes.length) ∗
        ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        (if g.cap = 0 then emp
         else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
           memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))) ∗ R =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        (vecHeader p g.cap g.ptr (BitVec.ofNat 64 g.bytes.length) ∗
          (if g.cap = 0 then emp
           else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
             memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗ R) := by
    sep_ac_rfl
  rw [hPull, satisfies_pure_sepConj] at hm
  omega

private def vecGhostPayload (A : RustAlloc) (g : VecGhost) : SepProp :=
  ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

private theorem vecGhostAt_eq_header_payload (A : RustAlloc) (g : VecGhost) (p : BitVec 64) :
    vecGhostAt A g p =
      (((p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length)) ∗
        vecGhostPayload A g) := by
  unfold vecGhostAt vecU8At vecHeader vecGhostPayload; sep_ac_rfl

private def vecGhostPayloadRest (A : RustAlloc) (g : VecGhost) : SepProp :=
  ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗ A.live g.ptr g.cap.toNat 1 ∗
  memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)

private theorem vecGhostPayload_nonempty_entails (A : RustAlloc) (g : VecGhost)
    (hpos : 0 < g.bytes.length) :
    vecGhostPayload A g ⊢ (g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A g := by
  unfold vecGhostPayload vecGhostPayloadRest; refine Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
  have hcapNe : g.cap ≠ 0 := by intro hc0; have : g.cap.toNat = 0 := by rw [hc0]; rfl
                                omega
  simp only [hcapNe, ↓reduceIte]
  have hEq :
      A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) =
      (g.ptr ↦ₛ g.bytes) ∗ (A.live g.ptr g.cap.toNat 1 ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) := by
    sep_ac_rfl
  rw [hEq]; exact sepConj_mono_right (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.of_eq (by sep_ac_rfl)))

private theorem vecGhostPayload_nonempty_pack (A : RustAlloc) (g : VecGhost)
    (hpos : 0 < g.bytes.length) :
    ((g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A g) ⊢ vecGhostPayload A g := by
  unfold vecGhostPayloadRest vecGhostPayload
  have hPull :
      (g.ptr ↦ₛ g.bytes) ∗ (⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        A.live g.ptr g.cap.toNat 1 ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        ((g.ptr ↦ₛ g.bytes) ∗ A.live g.ptr g.cap.toNat 1 ∗
          memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) := by
    sep_ac_rfl
  rw [hPull]; refine Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
  have hcapNe : g.cap ≠ 0 := by intro hc0; have : g.cap.toNat = 0 := by rw [hc0]; rfl
                                omega
  simp only [hcapNe, ↓reduceIte]; exact Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.of_eq (by sep_ac_rfl))

private theorem vecU8_empty_pack (A : RustAlloc) (ret : BitVec 64) :
    ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 1#64) ∗ ((ret + 16#64) ↦₆₄ 0#64)) ⊢ vecU8 A ret [] := by
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  have hZero : (0#64 : BitVec 64) = 0 := rfl
  simp only [hZero, ↓reduceIte, sepConj_emp, List.length_nil]
  refine Entails.trans (Entails.pure_right
    (φ := 0 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0)
    (by decide) (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

private theorem vecU8_nonempty_pack {M : AllocCostModel} (A : RustCliAllocBudget M)
    (ret newPtr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt63 : bs.length < 2 ^ 63) (hne0 : newPtr ≠ 0#64) :
    let lenBv := BitVec.ofNat 64 bs.length
    (((ret ↦₆₄ lenBv) ∗ ((ret + 8#64) ↦₆₄ newPtr) ∗ ((ret + 16#64) ↦₆₄ lenBv)) ∗
      A.live newPtr bs.length 1 ∗ (newPtr ↦ₛ bs)) ⊢ vecU8 A.repAlloc ret bs := by
  intro lenBv
  have hlenNat : lenBv.toNat = bs.length := by
    dsimp only [lenBv]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcapNe : lenBv ≠ 0 := by
    intro h0; have := congrArg BitVec.toNat h0; rw [hlenNat] at this; change bs.length = 0 at this; omega
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right lenBv (Entails.sepExists_right newPtr ?_)
  simp only [hcapNe, ↓reduceIte, hlenNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  have hLiveEq : A.repAlloc.live newPtr bs.length 1 = A.live newPtr bs.length 1 := rfl
  rw [hLiveEq]
  refine Entails.trans (Entails.pure_right (φ := bs.length ≤ bs.length ∧ bs.length < 2 ^ 63 ∧ newPtr ≠ 0)
    ⟨Nat.le_refl _, hlt63, hne0⟩ (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

/-! ## 4. Per-Segment Stepping Proofs for `<String as Clone>::clone` -/

private abbrev savedStack48 (s0 : State) : SepProp :=
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

private abbrev vecHdrPts (p : BitVec 64) (g : VecGhost) : SepProp :=
  (p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length)

private abbrev retPts (ret r0 r1 r2 : BitVec 64) : SepProp :=
  (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2)

private abbrev csUpperPreserved (s0 sm : State) : Prop :=
  ∀ r ∈ ([.x23, .x24, .x25, .x26, .x27, .x28] : List Reg), sm.readReg64 r = s0.readReg64 r

private theorem csUpperPreserved_trans {s0 sm sf : State}
    (h1 : csUpperPreserved s0 sm) (h2 : CalleeSavedPreserved sm sf) :
    csUpperPreserved s0 sf := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h2.readReg64_x23.trans (h1 .x23 (by simp))
  · exact h2.readReg64_x24.trans (h1 .x24 (by simp))
  · exact h2.readReg64_x25.trans (h1 .x25 (by simp))
  · exact h2.readReg64_x26.trans (h1 .x26 (by simp))
  · exact h2.readReg64_x27.trans (h1 .x27 (by simp))
  · exact h2.readReg64_x28.trans (h1 .x28 (by simp))

private abbrev cloneFrame0 (s0 : State) : SepProp :=
  stackFrameAt (s0.sp - 48#64 - 4096#64) 12240

private abbrev clonePost {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (p ret : BitVec 64) (g : VecGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ (cloneFrame0 s0 ∗ R)) →
      sf.mem ⊨ (stringCloneBudgetCondSpec M A lim).post (p, ret, g, st) s0 sf ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev clonePanic {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (p ret : BitVec 64) (g : VecGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ (cloneFrame0 s0 ∗ R)) →
      sf.mem ⊨ (stringCloneBudgetCondSpec M A lim).onPanic (p, ret, g, st) s0 sf ∗ R

private abbrev cloneOom (M : AllocCostModel) (lim : BudgetLimits)
    (g : VecGhost) (st : M.σ) (s0 : State) : State → SepProp :=
  fun sf => ⌜¬ FitsEvents M lim st (stringCloneEvents g) ∧ OomPreserved s0 sf⌝

/-- Empty-string fast path (`+0x5c .. +0x74`): writes `{0, 1, 0}` to `ret`, restores stack, returns. -/
private theorem clone_empty_epilogue {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (p ret : BitVec 64) (g : VecGhost) (st : M.σ)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sm : State)
    (hg_empty : g.bytes = []) (hsp0 : s0.spAligned = true)
    (hpcm : sm.pc = fnAddr + 0x5c#64) (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 48#64) (hx19 : sm.readReg64 .x19 = 0#64)
    (hx20 : sm.readReg64 .x20 = ret) (hcsm : csUpperPreserved s0 sm)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hpres : AllocCallPreserved s0 sm) (hpoolm : A.pool lim st sm = A.pool lim st s0) :
    SepWPp P (s0.readReg64 .lr) sm
      (retPts ret r0 r1 r2 ∗ savedStack48 s0 ∗
        (vecHdrPts p g ∗ vecGhostPayload A.repAlloc g) ∗
        A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) allocHookStack)
      (clonePost A lim p ret g st R s0)
      (clonePanic A lim p ret g st R s0)
      (cloneOom M lim g st s0) := by
  have hf23 := fetch_instr_at 23 hCode; have hf24 := fetch_instr_at 24 hCode
  have hf25 := fetch_instr_at 25 hCode; have hf26 := fetch_instr_at 26 hCode
  have hf27 := fetch_instr_at 27 hCode; have hf28 := fetch_instr_at 28 hCode
  have hf29 := fetch_instr_at 29 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48 : decide (sm.sp &&& 15#64 = 0#64) = true := by
    rw [hspm]; exact decide_eq_true (beq_iff_eq.mp (spAligned_sub48 hspAl0))
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  dsimp only [retPts, savedStack48, vecHdrPts]
  wp_step; wp_stp64 hf24 m1 hm1; wp_str64 hf25 m2 hm2
  wp_step; wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp [arm64_norm]) (by simp [arm64_norm, hrunm])
    fun sf hsf hpcf hrunf => ?_
  have hspf : sf.sp = s0.sp := by rw [hsf]; simp [arm64_norm]
  have hcsf : CalleeSavedPreserved s0 sf := by
    rw [hsf]
    refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using hcsm .x23 (by simp), by simpa [arm64_norm] using hcsm .x24 (by simp),
      by simpa [arm64_norm] using hcsm .x25 (by simp), by simpa [arm64_norm] using hcsm .x26 (by simp),
      by simpa [arm64_norm] using hcsm .x27 (by simp), by simpa [arm64_norm] using hcsm .x28 (by simp),
      by simp [arm64_norm], by simpa [calleeSavedVRegs, arm64_norm] using hvm⟩
  have hpresf : AllocCallPreserved s0 sf := by
    rw [hsf]; exact allocCallPreserved_trans hpres
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  have hm2_0 : m2.perm = sm.mem.perm := by
    try simp only [arm64_norm] at hm1 hm2
    exact hm2.trans hm1
  have hpoolf : A.pool lim st sf = A.pool lim st s0 := by
    rw [hsf, pool_setMem_perm A lim st _ (by simpa [arm64_norm] using hm2_0)]
    simpa [arm64_norm] using hpoolm
  clear hsf
  refine SepWPp.done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
  have hevs : stringCloneEvents g = [] := by
    unfold stringCloneEvents; simp only [hg_empty, List.length_nil, ↓reduceIte]
  dsimp only [clonePost, cloneFrame0, stringCloneBudgetCondSpec] at hmf ⊢
  rw [hevs, AllocCostModel.stepEvents_nil, hpoolf, extHookStack_split_48 s0.sp]
  have hx19' : sm.readReg64 (Reg.gpr 19#5) = 0#64 := hx19
  have hx20' : sm.readReg64 (Reg.gpr 20#5) = ret := hx20
  try simp only [hx19', hx20', BitVec.add_zero] at hmf
  have hVecEq : (vecHdrPts p g ∗ vecGhostPayload A.repAlloc g) = vecGhostAt A.repAlloc g p :=
    (vecGhostAt_eq_header_payload A.repAlloc g p).symm
  have hmf1 : sf.mem ⊨
      (vecGhostAt A.repAlloc g p ∗
        (retPts ret 0#64 1#64 0#64 ∗ A.pool lim st s0 ∗
          (savedStack48 s0 ∗
            (stackAt (s0.sp - 48#64) allocHookStack ∗ cloneFrame0 s0)))) ∗ R := by
    rw [← hVecEq]; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf
  rw [hg_empty]
  refine Satisfies.mono (sepConj_mono_left ?_) hmf1
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (vecU8_empty_pack A.repAlloc ret)
        (sepConj_mono_right (sepConj_mono_left (pack_stack48 s0.sp _ _ _ _ _ _))))) ?_
  exact Entails.pure_right hpresf (Entails.of_eq (by sep_ac_rfl))

/-- Null-return cold panic path (`+0x30` `cbz x0, +0x78` → `+0x78 .. +0x80` `bl handleErrorAddr`). -/
private theorem clone_panic_tail {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hHandleErr : subroutine_ok P handleErrorAddr rustHandleErrorPanicSpec)
    (p ret : BitVec 64) (g : VecGhost) (st : M.σ)
    (Rest R : SepProp) (s0 sf2 : State)
    (hpos : 0 < g.bytes.length) (hna : NullAllowed g.bytes.length 1)
    (hsp0 : s0.spAligned = true) (hpc2 : sf2.pc = fnAddr + 0x30#64)
    (hrun2 : sf2.status = .Running) (hsp2 : sf2.sp = s0.sp - 48#64)
    (hx0_0 : sf2.readReg64 .x0 = 0#64) (hfs2 : sf2.fs = s0.fs) (htr2 : sf2.trace = s0.trace) :
    SepWPp P (s0.readReg64 .lr) sf2
      (stackAt (s0.sp - 48#64) allocHookStack ∗ Rest)
      (clonePost A lim p ret g st R s0)
      (clonePanic A lim p ret g st R s0)
      (cloneOom M lim g st s0) := by
  have hf12 := fetch_instr_at 12 hCode; have hf30 := fetch_instr_at 30 hCode
  have hf31 := fetch_instr_at 31 hCode; have hf32 := fetch_instr_at 32 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub48 hspAl0
  rw [stackAt_allocHook_split16 (s0.sp - 48#64)]
  apply SepWPp.of_sepWP (mid := handleErrorAddr)
  wp_step; wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun2]) fun sm_pan hsm hpc_pan hrun_pan => ?_
  have hsp_pan : sm_pan.sp = s0.sp - 48#64 := by rw [hsm]; simp [arm64_norm, hsp2]
  have hfs_pan : sm_pan.fs = s0.fs := by rw [hsm]; simp [arm64_norm, hfs2]
  have htr_pan : sm_pan.trace = s0.trace := by rw [hsm]; simp [arm64_norm, htr2]
  clear hsm
  refine SepWPp.call (x := ()) (ret_pc := sm_pan.readReg64 .lr)
    (F := stackFrameAt (s0.sp - 48#64 - 16#64) 4080 ∗ Rest)
    hHandleErr hpc_pan hrun_pan
    (by simpa [State.spAligned, hsp_pan] using hspAl48b) rfl ?_
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex) ?_
    (fun _ _ _ _ _ => by
      dsimp only [rustHandleErrorPanicSpec]; exact SepWPp.pure_elim fun h => False.elim h)
    (fun _ _ _ ho => by
      dsimp only [rustHandleErrorPanicSpec] at ho
      exact False.elim (not_satisfies_false_sepConj ho))
  · intro R' hm'
    dsimp only [rustHandleErrorPanicSpec]; rw [hsp_pan]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'
  · intro sf_pan _ hmp
    dsimp only [clonePanic, cloneFrame0, rustHandleErrorPanicSpec, stringCloneBudgetCondSpec] at hmp ⊢
    have hPull :
        ((⌜sf_pan.fs = sm_pan.fs ∧ sf_pan.trace = sm_pan.trace⌝ ∗ anyHeap) ∗
          (stackFrameAt (s0.sp - 48#64 - 16#64) 4080 ∗ Rest)) ∗ (cloneFrame0 s0 ∗ R) =
        ⌜sf_pan.fs = sm_pan.fs ∧ sf_pan.trace = sm_pan.trace⌝ ∗
          ((anyHeap ∗ stackFrameAt (s0.sp - 48#64 - 16#64) 4080 ∗ Rest ∗ cloneFrame0 s0) ∗ R) := by
      sep_ac_rfl
    rw [hPull, satisfies_pure_sepConj] at hmp
    rcases hmp with ⟨⟨hfsp, htrp⟩, hrest⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpos, hna, hfsp.trans hfs_pan, htrp.trans htr_pan⟩,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hrest⟩

/-- Non-null post-alloc path (`+0x30` `cbz` fallthrough → `memcpy` → `+0x44 .. +0x58` epilogue). -/
private theorem clone_memcpy_epilogue {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (p ret newPtr : BitVec 64) (g : VecGhost) (st : M.σ)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sf2 : State)
    (hpos : 0 < g.bytes.length) (hlt63 : g.bytes.length < 2 ^ 63)
    (hsp0 : s0.spAligned = true) (hpNe0 : newPtr ≠ 0#64)
    (hpc2 : sf2.pc = fnAddr + 0x30#64) (hrun2 : sf2.status = .Running)
    (hsp2 : sf2.sp = s0.sp - 48#64) (hx0_2 : sf2.readReg64 .x0 = newPtr)
    (hx19_2 : sf2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length)
    (hx20_2 : sf2.readReg64 .x20 = ret) (hx22_2 : sf2.readReg64 .x22 = g.ptr)
    (hcs2 : csUpperPreserved s0 sf2) (hv2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hpres2 : AllocCallPreserved s0 sf2) :
    let st' := M.stepEvents (rustAllocEvents g.bytes.length 1) st
    SepWPp P (s0.readReg64 .lr) sf2
      (memRegion newPtr g.bytes.length ∗ vecGhostPayload A.repAlloc g ∗
        A.live newPtr g.bytes.length 1 ∗ A.pool lim st' sf2 ∗
        stackAt (s0.sp - 48#64) allocHookStack ∗ retPts ret r0 r1 r2 ∗
        vecHdrPts p g ∗ savedStack48 s0)
      (clonePost A lim p ret g st R s0)
      (clonePanic A lim p ret g st R s0)
      (cloneOom M lim g st s0) := by
  intro st'
  have hf12 := fetch_instr_at 12 hCode; have hf13 := fetch_instr_at 13 hCode
  have hf14 := fetch_instr_at 14 hCode; have hf15 := fetch_instr_at 15 hCode
  have hf16 := fetch_instr_at 16 hCode; have hf17 := fetch_instr_at 17 hCode
  have hf18 := fetch_instr_at 18 hCode; have hf19 := fetch_instr_at 19 hCode
  have hf20 := fetch_instr_at 20 hCode; have hf21 := fetch_instr_at 21 hCode
  have hf22 := fetch_instr_at 22 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub48 hspAl0
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (vecGhostPayload_nonempty_entails A.repAlloc g hpos))) ?_
  apply SepWPp.of_sepWP (mid := memcpyAddr)
  dsimp only [retPts, savedStack48, vecHdrPts]
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun2]) fun sm3 hsm hpc3 hrun3 => ?_
  have hsp3 : sm3.sp = s0.sp - 48#64 := by rw [hsm]; simp [arm64_norm, hsp2]
  have hlr3 : sm3.readReg64 .lr = fnAddr + 0x44#64 := by
    rw [hsm]; simp only [arm64_norm]; try bv_omega
  have hx0_3 : sm3.readReg64 .x0 = newPtr := by rw [hsm]; simp [arm64_norm, hx0_2]
  have hx1_3 : sm3.readReg64 .x1 = g.ptr := by rw [hsm]; simp [arm64_norm]
  have hx2_3 : sm3.readReg64 .x2 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm]; simp [arm64_norm]
  have hx19_3 : sm3.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm]; simp [arm64_norm, hx19_2]
  have hx20_3 : sm3.readReg64 .x20 = ret := by rw [hsm]; simp [arm64_norm, hx20_2]
  have hx21_3 : sm3.readReg64 .x21 = newPtr := by rw [hsm]; simp [arm64_norm]
  have hcs3 : csUpperPreserved s0 sm3 := by
    rw [hsm]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcs2 _ (by simp)
  have hv3 : calleeSavedVRegs sm3 = calleeSavedVRegs s0 := by
    rw [hsm]; simpa [calleeSavedVRegs, arm64_norm] using hv2
  have hpres3 : AllocCallPreserved s0 sm3 := by
    rw [hsm]; exact allocCallPreserved_trans hpres2
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  have hpool3 : A.pool lim st' sm3 = A.pool lim st' sf2 := by rw [hsm]; simp [arm64_norm]
  clear hsm
  let FrameMc :=
    vecGhostPayloadRest A.repAlloc g ∗ A.live newPtr g.bytes.length 1 ∗
    A.pool lim st' sf2 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
    retPts ret r0 r1 r2 ∗ vecHdrPts p g ∗ savedStack48 s0
  refine SepWPp.call_wpp (x := (newPtr, g.ptr, g.bytes)) (ret_pc := fnAddr + 0x44#64)
    (F := FrameMc) hMemcpy hpc3 hrun3
    (by simpa [State.spAligned, hsp3] using hspAl48b) hlr3 ?_
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ ⟨_, hp⟩ => by
      dsimp only [allocMemcpyVmSpec] at hp; exact False.elim (not_satisfies_false_sepConj hp))
    ?_
    (fun _ _ _ ho => by
      dsimp only [allocMemcpyVmSpec] at ho; exact False.elim (not_satisfies_false_sepConj ho))
  · intro R' hm'
    dsimp only [allocMemcpyVmSpec, FrameMc]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_3, hx1_3, hx2_3, Nat.lt_trans hlt63 (by decide)⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'⟩
  · intro sf3 hpc_sf3 hrun_sf3 hsp_sf3 hcs_sf3
    dsimp only [allocMemcpyVmSpec, FrameMc]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, hpres_mc, hvm_mc⟩ => ?_
    have hpool_sf3 : A.pool lim st' sf3 = A.pool lim st' sf2 :=
      (A.pool_transport lim st' sm3 sf3 hvm_mc).trans hpool3
    have hsp3' : sf3.sp = s0.sp - 48#64 := hsp_sf3.trans hsp3
    have hspAl48 : decide (sf3.sp &&& 15#64 = 0#64) = true := by
      rw [hsp3']; exact decide_eq_true (beq_iff_eq.mp hspAl48b)
    have hx19_sf3 : sf3.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
      hcs_sf3.readReg64_x19.trans hx19_3
    have hx20_sf3 : sf3.readReg64 .x20 = ret := hcs_sf3.readReg64_x20.trans hx20_3
    have hx21_sf3 : sf3.readReg64 .x21 = newPtr := hcs_sf3.readReg64_x21.trans hx21_3
    have hcs_sf3_s0 : csUpperPreserved s0 sf3 := csUpperPreserved_trans hcs3 hcs_sf3
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    dsimp only [retPts, savedStack48, vecHdrPts]
    wp_stp64 hf17 m1 hm1; wp_str64 hf18 m2 hm2
    wp_step; wp_step; wp_step; wp_step
    refine sepWP_done_let (by simp [arm64_norm]) (by simp [arm64_norm, hrun_sf3])
      fun sf hsf hpcf hrunf => ?_
    have hspf : sf.sp = s0.sp := by rw [hsf]; simp [arm64_norm]
    have hcsf : CalleeSavedPreserved s0 sf := by
      rw [hsf]
      refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
        by simpa [arm64_norm] using hcs_sf3_s0 .x23 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x24 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x25 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x26 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x27 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x28 (by simp),
        by simp [arm64_norm],
        by simpa [calleeSavedVRegs, arm64_norm] using hcs_sf3.vregs.trans hv3⟩
    have hpresf : AllocCallPreserved s0 sf := by
      rw [hsf]; exact allocCallPreserved_trans (allocCallPreserved_trans hpres3 hpres_mc)
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
    have hm2_0 : m2.perm = sf3.mem.perm := by
      try simp only [arm64_norm] at hm1 hm2
      exact hm2.trans hm1
    have hpoolf : A.pool lim st' sf = A.pool lim st' sf2 := by
      rw [hsf, pool_setMem_perm A lim st' _ (by simpa [arm64_norm] using hm2_0)]
      simpa [arm64_norm] using hpool_sf3
    clear hsf
    refine SepWPp.done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
    have hevs : stringCloneEvents g = rustAllocEvents g.bytes.length 1 := by
      unfold stringCloneEvents; simp only [Nat.ne_of_gt hpos, ↓reduceIte]
    dsimp only [clonePost, cloneFrame0, stringCloneBudgetCondSpec] at hmf ⊢
    rw [hevs]
    change sf.mem ⊨
      (⌜AllocCallPreserved s0 sf⌝ ∗ vecGhostAt A.repAlloc g p ∗
        vecU8 A.repAlloc ret g.bytes ∗ A.pool lim st' sf ∗
        stackAt s0.sp extHookStack) ∗ R
    rw [hpoolf, extHookStack_split_48 s0.sp]
    have hx19' : sf3.readReg64 (Reg.gpr 19#5) = BitVec.ofNat 64 g.bytes.length := hx19_sf3
    have hx20' : sf3.readReg64 (Reg.gpr 20#5) = ret := hx20_sf3
    have hx21' : sf3.readReg64 (Reg.gpr 21#5) = newPtr := hx21_sf3
    try simp only [hx19', hx20', hx21', BitVec.add_zero] at hmf
    let lenBv := BitVec.ofNat 64 g.bytes.length
    have hmf1 : sf.mem ⊨
        ((vecHdrPts p g ∗ ((g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A.repAlloc g)) ∗
          ((retPts ret lenBv newPtr lenBv ∗
            A.live newPtr g.bytes.length 1 ∗ (newPtr ↦ₛ g.bytes)) ∗
           A.pool lim st' sf2 ∗
           (savedStack48 s0 ∗
            (stackAt (s0.sp - 48#64) allocHookStack ∗ cloneFrame0 s0)))) ∗ R :=
      Satisfies.mono (Entails.of_eq (by dsimp only [lenBv]; sep_ac_rfl)) hmf
    refine Satisfies.mono (sepConj_mono_left ?_) hmf1
    have hGhostEnt :
        (vecHdrPts p g ∗ ((g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A.repAlloc g)) ⊢
        vecGhostAt A.repAlloc g p := by
      rw [vecGhostAt_eq_header_payload A.repAlloc g p]
      exact sepConj_mono_right (vecGhostPayload_nonempty_pack A.repAlloc g hpos)
    refine Entails.trans
      (sepConj_mono hGhostEnt
        (sepConj_mono (vecU8_nonempty_pack A ret newPtr g.bytes hpos hlt63 hpNe0)
          (sepConj_mono_right (sepConj_mono_left (pack_stack48 s0.sp _ _ _ _ _ _))))) ?_
    exact Entails.pure_right hpresf (Entails.of_eq (by sep_ac_rfl))

/-- Non-empty branch (`+0x1c .. +0x30`): loads `g.ptr`, calls `shim`, calls `__rust_alloc`, and
    dispatches to `clone_panic_tail` (`x0 = 0`) or `clone_memcpy_epilogue` (`x0 ≠ 0`). -/
private theorem clone_nonempty_branch {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {allocAddrs : RustAllocAddrs}
    {fnAddr shimAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddrs.alloc memcpyAddr handleErrorAddr))
    (hAlloc : RustCliAllocBudgetEntriesBase M A P allocAddrs)
    (hAux : RustStdAllocAuxEntries P shimAddr memcpyAddr handleErrorAddr)
    (p ret : BitVec 64) (g : VecGhost) (st : M.σ)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sm0 : State)
    (hpos : 0 < g.bytes.length) (hlt63 : g.bytes.length < 2 ^ 63) (hsp0 : s0.spAligned = true)
    (hpcm0 : sm0.pc = fnAddr + 0x1c#64) (hrunm0 : sm0.status = .Running)
    (hspm0 : sm0.sp = s0.sp - 48#64) (hx0_m0 : sm0.readReg64 .x0 = p)
    (hx19_m0 : sm0.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length)
    (hx20_m0 : sm0.readReg64 .x20 = ret) (hcsm0 : csUpperPreserved s0 sm0)
    (hvm0 : calleeSavedVRegs sm0 = calleeSavedVRegs s0)
    (hpres0 : AllocCallPreserved s0 sm0) (hpool0 : A.pool lim st sm0 = A.pool lim st s0) :
    SepWPp P (s0.readReg64 .lr) sm0
      (vecHdrPts p g ∗ vecGhostPayload A.repAlloc g ∗ A.pool lim st s0 ∗
        stackAt (s0.sp - 48#64) allocHookStack ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0)
      (clonePost A lim p ret g st R s0)
      (clonePanic A lim p ret g st R s0)
      (cloneOom M lim g st s0) := by
  have hf7 := fetch_instr_at 7 hCode; have hf8 := fetch_instr_at 8 hCode
  have hf9 := fetch_instr_at 9 hCode; have hf10 := fetch_instr_at 10 hCode
  have hf11 := fetch_instr_at 11 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub48 hspAl0
  apply SepWPp.of_sepWP (mid := shimAddr)
  dsimp only [retPts, savedStack48, vecHdrPts]
  wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrunm0]) fun sm1 hsm1 hpc1 hrun1 => ?_
  have hsp1 : sm1.sp = s0.sp - 48#64 := by rw [hsm1]; simp [arm64_norm, hspm0]
  have hlr1 : sm1.readReg64 .lr = fnAddr + 0x24#64 := by
    rw [hsm1]; simp only [arm64_norm]; try bv_omega
  have hx19_1 : sm1.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm1]; simp [arm64_norm, hx19_m0]
  have hx20_1 : sm1.readReg64 .x20 = ret := by rw [hsm1]; simp [arm64_norm, hx20_m0]
  have hx22_1 : sm1.readReg64 .x22 = g.ptr := by rw [hsm1]; simp [arm64_norm]
  have hcs1 : csUpperPreserved s0 sm1 := by
    rw [hsm1]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcsm0 _ (by simp)
  have hv1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := by
    rw [hsm1]; simpa [calleeSavedVRegs, arm64_norm] using hvm0
  have hpres1 : AllocCallPreserved s0 sm1 := by
    rw [hsm1]; exact allocCallPreserved_trans hpres0
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  have hpool1 : A.pool lim st sm1 = A.pool lim st s0 := by
    rw [hsm1]; simpa [arm64_norm] using hpool0
  clear hsm1
  let FrameShim :=
    vecHdrPts p g ∗ vecGhostPayload A.repAlloc g ∗ A.pool lim st s0 ∗
    stackAt (s0.sp - 48#64) allocHookStack ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0
  refine SepWPp.call_wpp (x := ()) (ret_pc := fnAddr + 0x24#64)
    (F := FrameShim) hAux.shim_ok hpc1 hrun1
    (by simpa [State.spAligned, hsp1] using hspAl48b) hlr1
    (fun _ hm' => by dsimp only [rustAllocShimVmSpec, FrameShim]; rw [emp_sepConj]; exact hm')
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ ⟨_, hp⟩ => by
      dsimp only [rustAllocShimVmSpec] at hp; exact False.elim (not_satisfies_false_sepConj hp))
    ?_
    (fun _ _ _ ho => by
      dsimp only [rustAllocShimVmSpec] at ho; exact False.elim (not_satisfies_false_sepConj ho))
  intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
  dsimp only [rustAllocShimVmSpec, FrameShim]
  refine SepWPp.pure_elim fun ⟨hpres_sh, hvm_sh⟩ => ?_
  have hpool_sf1 : A.pool lim st sf1 = A.pool lim st s0 :=
    (A.pool_transport lim st sm1 sf1 hvm_sh).trans hpool1
  have hsp_sf1' : sf1.sp = s0.sp - 48#64 := hsp_sf1.trans hsp1
  have hx19_sf1 : sf1.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
    hcs_sf1.readReg64_x19.trans hx19_1
  have hx20_sf1 : sf1.readReg64 .x20 = ret := hcs_sf1.readReg64_x20.trans hx20_1
  have hx22_sf1 : sf1.readReg64 .x22 = g.ptr := hcs_sf1.readReg64_x22.trans hx22_1
  have hcs_sf1_s0 : csUpperPreserved s0 sf1 := csUpperPreserved_trans hcs1 hcs_sf1
  have hpres_s0_sf1 : AllocCallPreserved s0 sf1 := allocCallPreserved_trans hpres1 hpres_sh
  apply SepWPp.of_sepWP (mid := allocAddrs.alloc)
  wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun_sf1]) fun sm2 hsm2 hpc2 hrun2 => ?_
  have hsp2 : sm2.sp = s0.sp - 48#64 := by rw [hsm2]; simp [arm64_norm, hsp_sf1']
  have hlr2 : sm2.readReg64 .lr = fnAddr + 0x30#64 := by
    rw [hsm2]; simp only [arm64_norm]; try bv_omega
  have hx0_2 : sm2.readReg64 .x0 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm2]; simp [arm64_norm]
  have hx1_2 : sm2.readReg64 .x1 = 1#64 := by rw [hsm2]; simp [arm64_norm]
  have hx19_2 : sm2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm2]; simp [arm64_norm, hx19_sf1]
  have hx20_2 : sm2.readReg64 .x20 = ret := by rw [hsm2]; simp [arm64_norm, hx20_sf1]
  have hx22_2 : sm2.readReg64 .x22 = g.ptr := by rw [hsm2]; simp [arm64_norm, hx22_sf1]
  have hcs2 : csUpperPreserved s0 sm2 := by
    rw [hsm2]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcs_sf1_s0 _ (by simp)
  have hv2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := by
    rw [hsm2]; simpa [calleeSavedVRegs, arm64_norm] using hcs_sf1.vregs.trans hv1
  have hpres2 : AllocCallPreserved s0 sm2 := by
    rw [hsm2]; exact allocCallPreserved_trans hpres_s0_sf1
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  have hpool2 : A.pool lim st sm2 = A.pool lim st s0 := by
    rw [hsm2]; simpa [arm64_norm] using hpool_sf1
  clear hsm2
  let FrameAl :=
    vecHdrPts p g ∗ vecGhostPayload A.repAlloc g ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0
  have hx0_nat : (sm2.readReg64 .x0).toNat = g.bytes.length := by
    rw [hx0_2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx1_nat : (sm2.readReg64 .x1).toNat = 1 := by rw [hx1_2]; rfl
  have hLay : RustLayoutOk g.bytes.length 1 := ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  refine SepWPp.call_wpp (x := (g.bytes.length, 1, st)) (ret_pc := fnAddr + 0x30#64)
    (F := FrameAl) (hAlloc.alloc lim) hpc2 hrun2
    (by simpa [State.spAligned, hsp2] using hspAl48b) hlr2 ?_
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ ⟨_, hp⟩ => by
      dsimp only [rustCliAllocBudgetSpecBase] at hp
      exact False.elim (not_satisfies_false_sepConj hp))
    ?_ ?_
  · intro R' hm'
    dsimp only [rustCliAllocBudgetSpecBase, FrameAl]
    rw [hsp2, hpool2, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_nat, hx1_nat, hLay⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'⟩
  · intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 hcs_sf2
    dsimp only [rustCliAllocBudgetSpecBase, FrameAl]
    rw [hsp2, sepConj_assoc]
    refine SepWPp.pure_elim fun hpres_al => ?_
    have hpres_s0_sf2 : AllocCallPreserved s0 sf2 := allocCallPreserved_trans hpres2 hpres_al
    have hsp_sf2' : sf2.sp = s0.sp - 48#64 := hsp_sf2.trans hsp2
    have hx19_sf2 : sf2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
      hcs_sf2.readReg64_x19.trans hx19_2
    have hx20_sf2 : sf2.readReg64 .x20 = ret := hcs_sf2.readReg64_x20.trans hx20_2
    have hx22_sf2 : sf2.readReg64 .x22 = g.ptr := hcs_sf2.readReg64_x22.trans hx22_2
    have hcs_s0_sf2 : csUpperPreserved s0 sf2 := csUpperPreserved_trans hcs2 hcs_sf2
    have hv_s0_sf2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 :=
      hcs_sf2.vregs.trans hv2
    by_cases hnull : sf2.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte]
      have hPullNull :
          (A.pool lim st sf2 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
            ⌜NullAllowed g.bytes.length 1⌝) ∗ FrameAl =
          ⌜NullAllowed g.bytes.length 1⌝ ∗
            (stackAt (s0.sp - 48#64) allocHookStack ∗ (A.pool lim st sf2 ∗ FrameAl)) := by
        dsimp only [FrameAl]; sep_ac_rfl
      rw [hPullNull]
      refine SepWPp.pure_elim fun hna => ?_
      exact clone_panic_tail A lim hCode hAux.handleError_ok p ret g st
        (A.pool lim st sf2 ∗ FrameAl) R s0 sf2 hpos hna hsp0
        hpc_sf2 hrun_sf2 hsp_sf2' hnull hpres_s0_sf2.1 hpres_s0_sf2.2.1
    · simp only [hnull, Bool.false_eq_true, ↓reduceIte]
      let newPtr := sf2.readReg64 .x0
      have hpNe0 : newPtr ≠ 0#64 := hnull
      have hPullOk :
          (A.pool lim (M.stepEvents (rustAllocEvents g.bytes.length 1) st) sf2 ∗
            stackAt (s0.sp - 48#64) allocHookStack ∗
            (⌜newPtr.toNat % 1 = 0⌝ ∗ A.live newPtr g.bytes.length 1 ∗
              memRegion newPtr g.bytes.length)) ∗ FrameAl =
          ⌜newPtr.toNat % 1 = 0⌝ ∗
            (memRegion newPtr g.bytes.length ∗ vecGhostPayload A.repAlloc g ∗
              A.live newPtr g.bytes.length 1 ∗
              A.pool lim (M.stepEvents (rustAllocEvents g.bytes.length 1) st) sf2 ∗
              stackAt (s0.sp - 48#64) allocHookStack ∗ retPts ret r0 r1 r2 ∗
              vecHdrPts p g ∗ savedStack48 s0) := by
        dsimp only [FrameAl, newPtr]; sep_ac_rfl
      rw [hPullOk]
      refine SepWPp.pure_elim fun _ => ?_
      exact clone_memcpy_epilogue A lim hCode hAux.memcpy_ok p ret newPtr g st
        r0 r1 r2 R s0 sf2 hpos hlt63 hsp0 hpNe0
        hpc_sf2 hrun_sf2 hsp_sf2' rfl hx19_sf2 hx20_sf2 hx22_sf2
        hcs_s0_sf2 hv_s0_sf2 hpres_s0_sf2
  · intro sf_oom R' _ ho
    dsimp only [rustCliAllocBudgetSpecBase] at ho
    rw [satisfies_pure_sepConj] at ho
    rcases ho with ⟨⟨hnfit, hoom2⟩, hFR⟩
    have hevs : stringCloneEvents g = rustAllocEvents g.bytes.length 1 := by
      unfold stringCloneEvents; simp only [Nat.ne_of_gt hpos, ↓reduceIte]
    dsimp only [cloneOom]
    rw [hevs, satisfies_pure_sepConj]
    have hoom0 : OomPreserved s0 sf_oom :=
      ⟨hoom2.1.trans hpres2.1, hoom2.2.1.trans hpres2.2.1, hoom2.2.2.trans hpres2.2.2.1⟩
    exact ⟨⟨hnfit, hoom0⟩, Satisfies.drop_left hFR⟩

/-! ## 5. Budget-Threaded `<String as Clone>::clone` Theorems and Alias Lifts -/

/-- Full conditional-OOM budget-threaded correctness of `<String as Clone>::clone` (`33` insns)
    from `hasInstrs P fnAddr (rustStringCloneInstrs ...)`. -/
theorem rustStringCloneBudgetCond_of_hasInstrs_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program}
    {allocAddrs : RustAllocAddrs}
    {fnAddr shimAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddrs.alloc memcpyAddr handleErrorAddr))
    (hAlloc : RustCliAllocBudgetEntriesBase M A P allocAddrs)
    (hAux : RustStdAllocAuxEntries P shimAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr (stringCloneBudgetCondSpec M A lim) := by
  apply subroutine_ok_of_sepWPp_pure_oom
    (φ := fun (_, _, g, st) s0 sf => ¬ FitsEvents M lim st (stringCloneEvents g) ∧ OomPreserved s0 sf)
    (by rintro ⟨_, _, _, _⟩ _ _; rfl)
  rintro ⟨p, ret, g, st⟩ R s0 hpc hrun hpre hsp0
  dsimp only [stringCloneBudgetCondSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hrest⟩
  have hlt63 : g.bytes.length < 2 ^ 63 := by
    refine vecGhostAt_bytes_lt_2pow63 (A := A.repAlloc) (m := s0.mem) (p := p)
      (R := memRegion ret 24 ∗ (A.pool lim st s0 ∗ (stackAt s0.sp extHookStack ∗ R))) ?_
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  let P0 :=
    stackFrameAt s0.sp 48 ∗ memRegion ret 24 ∗ vecGhostAt A.repAlloc g p ∗
    A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) allocHookStack
  have hm0 : s0.mem ⊨ P0 ∗ (cloneFrame0 s0 ∗ R) := by
    dsimp only [P0, cloneFrame0]
    rw [extHookStack_split_48 s0.sp] at hrest
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  refine ⟨P0, cloneFrame0 s0, hm0, ?_⟩
  dsimp only [P0]
  rw [stackFrameAt48_eq s0.sp, memRegion24_eq_exists_pts ret,
      vecGhostAt_eq_header_payload A.repAlloc g p]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 =>
    SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun st0 =>
    SepWPp.exists_elim fun st1 => SepWPp.exists_elim fun st2 =>
    SepWPp.exists_elim fun st3 => SepWPp.exists_elim fun st4 =>
    SepWPp.exists_elim fun st5 => ?_
  have hf0 := fetch_instr_at0 hCode; have hf1 := fetch_instr_at 1 hCode
  have hf2 := fetch_instr_at 2 hCode; have hf3 := fetch_instr_at 3 hCode
  have hf4 := fetch_instr_at 4 hCode; have hf5 := fetch_instr_at 5 hCode
  have hf6 := fetch_instr_at 6 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48 : decide ((s0.sp - 48#64) &&& 15#64 = 0#64) = true :=
    decide_eq_true (beq_iff_eq.mp (spAligned_sub48 hspAl0))
  by_cases hbs : g.bytes = []
  · -- Empty string (`g.bytes = []`): `cbz x19, +0x5c` branches to `+0x5c`
    have hlen0 : BitVec.ofNat 64 g.bytes.length = 0#64 := by simp [hbs]
    apply SepWPp.of_sepWP (mid := fnAddr + 0x5c#64)
    wp_stp64 hf0 m1 hm1; wp_stp64 hf1 m2 hm2; wp_stp64 hf2 m3 hm3
    wp_step; wp_step; wp_step; wp_step
    refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
      (by simp [arm64_norm, hrun]) fun sm hsm hpcm hrunm => ?_
    have hspm : sm.sp = s0.sp - 48#64 := by rw [hsm]; simp [arm64_norm]
    have hx19m : sm.readReg64 .x19 = 0#64 := by rw [hsm]; simp [arm64_norm]
    have hx20m : sm.readReg64 .x20 = ret := by rw [hsm]; simp [arm64_norm]
    have hcsm : csUpperPreserved s0 sm := by
      rw [hsm]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm]
    have hvm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      rw [hsm]; simp [calleeSavedVRegs, arm64_norm]
    have hpresm : AllocCallPreserved s0 sm := by
      rw [hsm]; exact
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
    have hm3_0 : m3.perm = s0.mem.perm := by
      try simp only [arm64_norm] at hm1 hm2 hm3
      exact hm3.trans (hm2.trans hm1)
    have hpoolm : A.pool lim st sm = A.pool lim st s0 := by
      rw [hsm, pool_setMem_perm A lim st _ (by simpa [arm64_norm] using hm3_0)]; simp [arm64_norm]
    clear hsm
    refine SepWPp.weaken_pre ?_ (clone_empty_epilogue A lim hCode p ret g st r0 r1 r2 R s0 sm
      hbs hsp0 hpcm hrunm hspm hx19m hx20m hcsm hvm hpresm hpoolm)
    exact Entails.of_eq (by
      dsimp only [retPts, savedStack48, vecHdrPts, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
      sep_ac_rfl)
  · -- Non-empty string (`0 < g.bytes.length`): `cbz x19, +0x5c` falls through to `+0x1c`
    have hpos : 0 < g.bytes.length := List.length_pos_iff.mpr hbs
    have hlenNe0 : BitVec.ofNat 64 g.bytes.length ≠ 0#64 := by
      intro h0; have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      change g.bytes.length = 0 at this; omega
    apply SepWPp.of_sepWP (mid := fnAddr + 0x1c#64)
    wp_stp64 hf0 m1 hm1; wp_stp64 hf1 m2 hm2; wp_stp64 hf2 m3 hm3
    wp_step; wp_step; wp_step; wp_step
    refine sepWP_done_let (by simp [arm64_norm, beq_false_of_ne hlenNe0]; try bv_omega)
      (by simp [arm64_norm, hrun]) fun sm0 hsm0 hpcm0 hrunm0 => ?_
    have hspm0 : sm0.sp = s0.sp - 48#64 := by rw [hsm0]; simp [arm64_norm]
    have hx0_m0 : sm0.readReg64 .x0 = p := by rw [hsm0]; simp [arm64_norm, hx0]
    have hx19_m0 : sm0.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
      rw [hsm0]; simp [arm64_norm]
    have hx20_m0 : sm0.readReg64 .x20 = ret := by rw [hsm0]; simp [arm64_norm]
    have hcsm0 : csUpperPreserved s0 sm0 := by
      rw [hsm0]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm]
    have hvm0 : calleeSavedVRegs sm0 = calleeSavedVRegs s0 := by
      rw [hsm0]; simp [calleeSavedVRegs, arm64_norm]
    have hpres0 : AllocCallPreserved s0 sm0 := by
      rw [hsm0]; exact
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
    have hm3_0 : m3.perm = s0.mem.perm := by
      try simp only [arm64_norm] at hm1 hm2 hm3
      exact hm3.trans (hm2.trans hm1)
    have hpool0 : A.pool lim st sm0 = A.pool lim st s0 := by
      rw [hsm0, pool_setMem_perm A lim st _ (by simpa [arm64_norm] using hm3_0)]; simp [arm64_norm]
    clear hsm0
    refine SepWPp.weaken_pre ?_ (clone_nonempty_branch A lim hCode hAlloc hAux p ret g st
      r0 r1 r2 R s0 sm0 hpos hlt63 hsp0 hpcm0 hrunm0 hspm0 hx0_m0 hx19_m0 hx20_m0 hcsm0 hvm0
      hpres0 hpool0)
    exact Entails.of_eq (by
      dsimp only [retPts, savedStack48, vecHdrPts, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
      sep_ac_rfl)

/-- Deterministic-event `NoOom` specialization of `<String as Clone>::clone` under `FitsEvents`. -/
theorem rustStringCloneNoOom_of_hasInstrs_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program}
    {allocAddrs : RustAllocAddrs}
    {fnAddr shimAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddrs.alloc memcpyAddr handleErrorAddr))
    (hAlloc : RustCliAllocBudgetEntriesBase M A P allocAddrs)
    (hAux : RustStdAllocAuxEntries P shimAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr (stringCloneNoOomSpec M A lim) :=
  subroutine_ok_stringCloneNoOom_of_cond
    (rustStringCloneBudgetCond_of_hasInstrs_ok A lim hCode hAlloc hAux)

/-- `StringCloneEnv` envelope specialization of `<String as Clone>::clone` under `FitsEnv`. -/
theorem rustStringCloneBudget_of_hasInstrs_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program}
    {allocAddrs : RustAllocAddrs}
    {fnAddr shimAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddrs.alloc memcpyAddr handleErrorAddr))
    (hAlloc : RustCliAllocBudgetEntriesBase M A P allocAddrs)
    (hAux : RustStdAllocAuxEntries P shimAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr (stringCloneBudgetSpec M A lim) :=
  subroutine_ok_stringCloneBudget_of_cond
    (rustStringCloneBudgetCond_of_hasInstrs_ok A lim hCode hAlloc hAux)

/-- Placement-parametric `WordTree` entrypoint for `stringCloneBudgetCondSpec`: discharges the
    `33` instructions of `<String as Clone>::clone` solely via kernel evaluation of
    `checkShimInstrsAt P.base t fnAddr (...) = true`. -/
theorem rustStringCloneBudgetCond_of_wordTree_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program} {t : WordTree}
    (n : Nat) {allocAddrs : RustAllocAddrs}
    {fnAddr shimAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 33 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddrs.alloc memcpyAddr handleErrorAddr) = true)
    (hAlloc : RustCliAllocBudgetEntriesBase M A P allocAddrs)
    (hAux : RustStdAllocAuxEntries P shimAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr (stringCloneBudgetCondSpec M A lim) :=
  rustStringCloneBudgetCond_of_hasInstrs_ok A lim
    (hasShimInstrs_of_wordTree n hcode hwf hhook hok) hAlloc hAux

/-- Placement-parametric `WordTree` entrypoint for `stringCloneBudgetSpec` (`StringCloneEnv`). -/
theorem rustStringCloneBudget_of_wordTree_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program} {t : WordTree}
    (n : Nat) {allocAddrs : RustAllocAddrs}
    {fnAddr shimAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 33 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddrs.alloc memcpyAddr handleErrorAddr) = true)
    (hAlloc : RustCliAllocBudgetEntriesBase M A P allocAddrs)
    (hAux : RustStdAllocAuxEntries P shimAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr (stringCloneBudgetSpec M A lim) :=
  subroutine_ok_stringCloneBudget_of_cond
    (rustStringCloneBudgetCond_of_wordTree_ok A lim n hcode hwf hhook hok hAlloc hAux)

/-- 1-hop `B`-stub alias lift for `stringCloneBudgetSpec` (`aliasAddr → fnAddr`). -/
theorem lsStringCloneBudget_alias_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program}
    (aliasAddr fnAddr : BitVec 64) (hStub : hasInstrs P aliasAddr [ .b (fnAddr - aliasAddr) ])
    (hTarget : subroutine_ok P fnAddr (stringCloneBudgetSpec M A lim)) :
    subroutine_ok P aliasAddr (stringCloneBudgetSpec M A lim) :=
  subroutine_ok_of_branchStub aliasAddr fnAddr hStub
    (by rintro ⟨_, _, _, _⟩ _ _; simp [stringCloneBudgetSpec]) (by rintro ⟨_, _, _, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _, _, _⟩ _ _ _; rfl) (by rintro ⟨_, _, _, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _, _, _⟩ _ _ _; rfl) hTarget

theorem lsStringCloneBudget_alias_wordTree_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program} {t : WordTree}
    (n : Nat) (aliasAddr fnAddr : BitVec 64)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t aliasAddr [ .b (fnAddr - aliasAddr) ] = true)
    (hTarget : subroutine_ok P fnAddr (stringCloneBudgetSpec M A lim)) :
    subroutine_ok P aliasAddr (stringCloneBudgetSpec M A lim) :=
  subroutine_ok_of_branchStub_wordTree n aliasAddr fnAddr hcode hwf hhook hok
    (by rintro ⟨_, _, _, _⟩ _ _; simp [stringCloneBudgetSpec]) (by rintro ⟨_, _, _, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _, _, _⟩ _ _ _; rfl) (by rintro ⟨_, _, _, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _, _, _⟩ _ _ _; rfl) hTarget

/-- 2-hop `B`-stub alias lift for `stringCloneBudgetSpec` (`snapstubAddr → aliasAddr → fnAddr`). -/
theorem lsStringCloneBudget_alias2_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program}
    (snapstubAddr aliasAddr fnAddr : BitVec 64)
    (hSnap : hasInstrs P snapstubAddr [ .b (aliasAddr - snapstubAddr) ])
    (hAlias : hasInstrs P aliasAddr [ .b (fnAddr - aliasAddr) ])
    (hTarget : subroutine_ok P fnAddr (stringCloneBudgetSpec M A lim)) :
    subroutine_ok P snapstubAddr (stringCloneBudgetSpec M A lim) :=
  subroutine_ok_of_branchStub2 snapstubAddr aliasAddr fnAddr hSnap hAlias
    (by rintro ⟨_, _, _, _⟩ _ _; simp [stringCloneBudgetSpec]) (by rintro ⟨_, _, _, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _, _, _⟩ _ _ _; rfl) (by rintro ⟨_, _, _, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _, _, _⟩ _ _ _; rfl) hTarget

theorem lsStringCloneBudget_alias2_wordTree_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program} {t : WordTree}
    (n : Nat) (snapstubAddr aliasAddr fnAddr : BitVec 64)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhookSnap : ∀ i, i < 1 → P.hookAtOff? ((snapstubAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hhookAlias : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkBranchStub2 P.base t snapstubAddr aliasAddr fnAddr = true)
    (hTarget : subroutine_ok P fnAddr (stringCloneBudgetSpec M A lim)) :
    subroutine_ok P snapstubAddr (stringCloneBudgetSpec M A lim) :=
  subroutine_ok_of_branchStub2_wordTree n snapstubAddr aliasAddr fnAddr
    hcode hwf hhookSnap hhookAlias hok
    (by rintro ⟨_, _, _, _⟩ _ _; simp [stringCloneBudgetSpec]) (by rintro ⟨_, _, _, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _, _, _⟩ _ _ _; rfl) (by rintro ⟨_, _, _, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _, _, _⟩ _ _ _; rfl) hTarget

end LibsignalBinary.Proofs.Placed.StringCloneMallocngPlaced
