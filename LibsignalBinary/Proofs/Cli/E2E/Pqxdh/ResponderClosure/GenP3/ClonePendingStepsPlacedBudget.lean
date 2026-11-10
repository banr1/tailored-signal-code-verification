/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingStepsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Sub-Segment 3A: `pending_pre_key` (Block `518`)

Deterministic allocation-event trace `clonePendingPreKeyEvents` / `ClonePendingPreKeyEnv` and
budget-threaded CPS sub-segment theorem `clonePendingPreKey_placed_ok` (`+0x1a5c → +0x1ac8`)
on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingStepsPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl lsρ lsMemcpySym)
open CryptoVerification.RustHeap (LayoutOk allocHookStack vecU8Buf)
open CryptoVerification.LibsignalTripleRatchetRepr (TailVecGhost noneCap optTailVecAt)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (chainCloneStack)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  OptPendClone cap_add_one_ne_zero cap_add_one_beq_zero_eq_false
  ofNat_ne_zero_of_pos beq_ofNat_zero_eq_false exists_tail24_decomp
  segClone_pure_eq_emp stackAt_chainClone_eq_alloc
  vecGhostAt_eq_of_nil vecGhostAt_eq_of_pos vecU8Buf_nil_eq vecU8Buf_pos_eq
)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1 (
  lsShimSym lsAllocSym call_raw_nopanic_placed lscro_of_steps_placed
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a3 (
  list_eq_nil_or_length_pos pure_elim_3
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (
  LsRetAddr624 lsRetAddr624_blockPlacement_base_add
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec
  subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget
  subroutine_ok_noAllocShim_of_sessionShimBudget
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

/-- Re-export of the Block-518 `+0x378c` OOM exit tail from `GenP3.ClonePendingStepsPlaced`. -/
abbrev oom_tail_378c_placed_ok :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a3.oom_tail_378c_placed_ok

/-! ## 1. Exact Allocator Event List & Envelope for `pending_pre_key` Clone -/

/-- Exact allocator event sequence emitted while cloning `pending_pre_key : Option TailVecGhost`
(`+0x1a5c → +0x1ac8`): `[]` when `pending = none` or `gp.vec.bytes = []`, else
`rustAllocEvents gp.vec.bytes.length 1`. -/
def clonePendingPreKeyEvents (pending : Option TailVecGhost) : List AllocEvent :=
  match pending with
  | none => []
  | some gp =>
    if gp.vec.bytes = [] then []
    else rustAllocEvents gp.vec.bytes.length 1

/-- Exact allocator event envelope for `clonePendingPreKey_placed_ok`. -/
def ClonePendingPreKeyEnv (pending : Option TailVecGhost) (evs : List AllocEvent) : Prop :=
  evs = clonePendingPreKeyEvents pending

@[simp]
theorem fitsEnv_clonePendingPreKey_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (pending : Option TailVecGhost) :
    FitsEnv M lim st (ClonePendingPreKeyEnv pending) ↔
      FitsEvents M lim st (clonePendingPreKeyEvents pending) :=
  FitsEnv.eq_iff

/-! ## 2. Block-518 Budget-Synchronized Step Helpers (`+0x1a5c → +0x1ac8`) -/

local macro "wp_steps_sync_518 " h:term:max mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException $h))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

private def memcpy4kBudgetSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack

private theorem memcpy4kBudget_of_region {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr sessionMemcpyRegionBudgetSpec) :
    subroutine_ok P addr memcpy4kBudgetSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs⟩ R s0 hp
  dsimp only [memcpy4kBudgetSpec] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨hpure, hmem⟩
  refine ⟨(dst, src, bs), stackAt s0.sp allocHookStack ∗ R, ?_, fun sf hq => ?_⟩
  · dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpy4kBudgetSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hq.2.1.1, hq.2.1.2, hq.1⟩, Satisfies.of_eq hq.2.2 (by ac_rfl)⟩

private theorem memcpy4kBudget_of_4k {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (sessionMemcpyBudgetSpec allocHookStack)) :
    subroutine_ok P addr memcpy4kBudgetSpec := by
  refine subroutine_ok_mono h (fun ⟨dst, src, bs⟩ R s0 hp => ?_)
    (fun ⟨dst, src, bs⟩ R s0 sf hq => ?_)
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec,
      memcpy4kBudgetSpec] at hp ⊢
    simpa only [sepConj_assoc] using hp
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec,
      memcpy4kBudgetSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hq.2.1.1, hq.2.1.2, hq.1⟩, hq.2.2⟩

private theorem bind_sepWP_lscro_state_placed [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_step F : SepProp} {P_step_post : State → SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ := hstep.elim hm hL
  rotate_left
  · exact False.elim (not_satisfies_false_sepConj hoom)
  have hmm' : sm.mem ⊨ (P_step_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpcm hrunm (lscro_of_steps_placed hsteps hcro) hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem pend_none_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (sp coroPtr ctxPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x1a5c#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1ac8#64) s
      (A.pool lim st s ∗ ((coroPtr + 0x1f0#64) ↦₆₄ noneCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr))
      (fun s1 P_f =>
        (P_f ⊢
          A.pool lim st s1 ∗ ((coroPtr + 0x1f0#64) ↦₆₄ noneCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr)) ∧
        s1.sp = sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = noneCap ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq
  subst hsp_bv
  dsimp only [noneCap] at *
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext ((blkPl_518).base + 0x1ac8#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

private theorem pend_some_nil_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (sp coroPtr ctxPtr cap td2 v10 v18 : BitVec 64)
    (tw0 tw1 tw3 v28 v2c : BitVec 32)
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1a5c#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1ac8#64) s
      (A.pool lim st s ∗
        ((coroPtr + 0x1f0#64) ↦₆₄ cap) ∗ ((coroPtr + 0x200#64) ↦₆₄ 0#64) ∗
        ((coroPtr + 0x208#64) ↦₃₂ tw0) ∗ ((coroPtr + 0x20c#64) ↦₃₂ tw1) ∗
        ((coroPtr + 0x210#64) ↦₆₄ td2) ∗ ((coroPtr + 0x218#64) ↦₃₂ tw3) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0x10#64) ↦₆₄ v10) ∗
        ((sp + 0x18#64) ↦₆₄ v18) ∗ ((sp + 0x28#64) ↦₃₂ v28) ∗ ((sp + 0x2c#64) ↦₃₂ v2c))
      (fun s1 P_f =>
        (P_f ⊢
          A.pool lim st s1 ∗
            ((coroPtr + 0x1f0#64) ↦₆₄ cap) ∗ ((coroPtr + 0x200#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x208#64) ↦₃₂ tw0) ∗ ((coroPtr + 0x20c#64) ↦₃₂ tw1) ∗
            ((coroPtr + 0x210#64) ↦₆₄ td2) ∗ ((coroPtr + 0x218#64) ↦₃₂ tw3) ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0x10#64) ↦₆₄ td2) ∗
            ((sp + 0x18#64) ↦₆₄ 1#64) ∗ ((sp + 0x28#64) ↦₃₂ tw3) ∗ ((sp + 0x2c#64) ↦₃₂ tw0)) ∧
        s1.sp = sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = 0#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = ctxPtr ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq
  subst hsp_bv
  have hcmn : cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
  have hcmn_beq : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext ((blkPl_518).base + 0x1ac8#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

private theorem pend_some_pos_prep_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimBudgetSpec)
    (st : M.σ) (s : State) (sp coroPtr ctxPtr cap srcPtr : BitVec 64) (len : Nat)
    (tw0 tw1 tw3 v28 v2c : BitVec 32)
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpos : 0 < len)
    (hlen_lt : len < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1a5c#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsρ lsAllocSym) s
      (A.pool lim st s ∗
        ((coroPtr + 0x1f0#64) ↦₆₄ cap) ∗
        ((coroPtr + 0x1f8#64) ↦₆₄ srcPtr) ∗
        ((coroPtr + 0x200#64) ↦₆₄ BitVec.ofNat 64 len) ∗
        ((coroPtr + 0x208#64) ↦₃₂ tw0) ∗
        ((coroPtr + 0x20c#64) ↦₃₂ tw1) ∗
        ((coroPtr + 0x218#64) ↦₃₂ tw3) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
        ((sp + 0x28#64) ↦₃₂ v28) ∗
        ((sp + 0x2c#64) ↦₃₂ v2c))
      (fun s1 P_f =>
        (P_f ⊢
          A.pool lim st s1 ∗
            ((coroPtr + 0x1f0#64) ↦₆₄ cap) ∗
            ((coroPtr + 0x1f8#64) ↦₆₄ srcPtr) ∗
            ((coroPtr + 0x200#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((coroPtr + 0x208#64) ↦₃₂ tw0) ∗
            ((coroPtr + 0x20c#64) ↦₃₂ tw1) ∗
            ((coroPtr + 0x218#64) ↦₃₂ tw3) ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((sp + 0x28#64) ↦₃₂ tw3) ∗
            ((sp + 0x2c#64) ↦₃₂ tw0)) ∧
        s1.sp = sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = BitVec.ofNat 64 len ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = srcPtr ∧
        s1.readReg64 .x22 = BitVec.ofNat 64 len ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x1a98#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq
  subst hsp_bv
  have hcmn : cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
  have hcmn_beq : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
  have hlen_ne : BitVec.ofNat 64 len ≠ 0#64 :=
    ofNat_ne_zero_of_pos hpos (Nat.lt_trans hlen_lt (by decide))
  have hlen_beq : (BitVec.ofNat 64 len == 0#64) = false :=
    beq_ofNat_zero_eq_false hpos (Nat.lt_trans hlen_lt (by decide))
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext (lsρ lsShimSym)
  wp_call hshim ()
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_518 ext (lsρ lsAllocSym)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

private theorem pend_some_pos_copy_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) memcpy4kBudgetSpec)
    (st : M.σ) (s : State) (sp coroPtr ptr' srcPtr td2 v10 v18 : BitVec 64)
    (bs : List (BitVec 8))
    (hptr : ptr' ≠ 0#64)
    (hlen_lt : bs.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1a98#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ptr')
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = srcPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 bs.length) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1ac8#64) s
      (A.pool lim st s ∗
        memRegion ptr' bs.length ∗
        (srcPtr ↦ₛ bs) ∗
        stackAt sp allocHookStack ∗
        ((coroPtr + 0x210#64) ↦₆₄ td2) ∗
        ((sp + 0x10#64) ↦₆₄ v10) ∗
        ((sp + 0x18#64) ↦₆₄ v18))
      (fun s1 P_f =>
        (P_f ⊢
          A.pool lim st s1 ∗
            (ptr' ↦ₛ bs) ∗
            (srcPtr ↦ₛ bs) ∗
            stackAt sp allocHookStack ∗
            ((coroPtr + 0x210#64) ↦₆₄ td2) ∗
            ((sp + 0x10#64) ↦₆₄ td2) ∗
            ((sp + 0x18#64) ↦₆₄ ptr')) ∧
        s1.sp = sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = BitVec.ofNat 64 bs.length ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq
  subst hsp_bv
  have hptr_beq : (ptr' == 0#64) = false := beq_eq_false_iff_ne.mpr hptr
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx0' : s.readReg64 (Reg.gpr 0#5) = ptr' := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = srcPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 bs.length := hx22
  wp_steps_sync_518 ext (lsρ lsMemcpySym)
  wp_call hmemcpy (ptr', srcPtr, bs)
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_518 ext ((blkPl_518).base + 0x1ac8#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

/-! ## 3. Budget-Threaded CPS Sub-Segment 3A: `pending_pre_key` (`+0x1a5c → +0x1ac8`) -/

private theorem clonePendingPreKey_core_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) memcpy4kBudgetSpec)
    (st : M.σ) (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (sp coroPtr ctxPtr v10 v18 : BitVec 64)
    (v28 v2c : BitVec 32)
    (pending : Option TailVecGhost) (F : SepProp)
    (hfit : FitsEnv M lim st (ClonePendingPreKeyEnv pending))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1a5c#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' d10 : BitVec 64) (w28 w2c : BitVec 32),
      s1.pc = (blkPl_518).base + 0x1ac8#64 → s1.status = .Running →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = sp → s1.spAligned = true → s1.trace = s0.trace →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x22 = pendCap' →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = ctxPtr → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool lim (M.stepEvents (clonePendingPreKeyEvents pending) st) s1 ∗
          stackAt sp chainCloneStack ∗
          optTailVecAt A.repAlloc 48 (coroPtr + 0x1f0#64) pending ∗
          OptPendClone A.repAlloc pending pendCap' pendPtr' ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((sp + 0x10#64) ↦₆₄ d10) ∗ ((sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((sp + 0x28#64) ↦₃₂ w28) ∗ ((sp + 0x2c#64) ↦₃₂ w2c) ∗ F)
        Q Qp) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool lim st s ∗ stackAt sp chainCloneStack ∗
        optTailVecAt A.repAlloc 48 (coroPtr + 0x1f0#64) pending ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0x10#64) ↦₆₄ v10) ∗ ((sp + 0x18#64) ↦₆₄ v18) ∗
        ((sp + 0x28#64) ↦₃₂ v28) ∗ ((sp + 0x2c#64) ↦₃₂ v2c) ∗ F)
      Q Qp := by
  cases pending with
  | none =>
    dsimp only [optTailVecAt, OptPendClone, clonePendingPreKeyEvents,
      AllocCostModel.stepEvents] at hnext ⊢
    simp only [sepConj_assoc]
    have hnone := pend_none_placed_wp (A := A) (lim := lim) ext st s sp coroPtr ctxPtr hpc hrun
      hsp_eq hsp_al hx19
    refine bind_sepWP_lscro_state_placed hcro hnone (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1_s, hx19_1, hx22_1, hx23_1, hx25_1, hx27_1, hx28_1,
      hx29_1, hvregs1⟩
    have hsp1_al : s1.spAligned = true := by
      simpa only [State.spAligned, hsp1, ← hsp_eq] using hsp_al
    have h_rfl : (⌜noneCap = noneCap⌝ : SepProp) = emp := segClone_pure_eq_emp rfl
    refine SepWPp.weaken_pre ?_
      (hnext s1 noneCap v18 v10 v28 v2c hpc1 hrun1 hcro1 hsp1 hsp1_al
        (htr1_s.trans htr) hx19_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1)
    rw [h_rfl]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | some gp =>
    dsimp only [optTailVecAt, OptPendClone] at hnext ⊢
    simp only [sepConj_assoc]
    refine pure_elim_3 fun htail => ?_
    obtain ⟨tw0, tw1, td2, tw3, tw4, _, htail_pts⟩ := exists_tail24_decomp htail
    have h1f8 : coroPtr + 0x1f0#64 + 8#64 = coroPtr + 0x1f8#64 := by bv_arith
    have h200 : coroPtr + 0x1f0#64 + 16#64 = coroPtr + 0x200#64 := by bv_arith
    have h208 : coroPtr + 0x1f0#64 + BitVec.ofNat 64 24 = coroPtr + 0x208#64 := by bv_arith
    have h20c : coroPtr + 0x208#64 + 4#64 = coroPtr + 0x20c#64 := by bv_arith
    have h210 : coroPtr + 0x208#64 + 8#64 = coroPtr + 0x210#64 := by bv_arith
    have h218 : coroPtr + 0x208#64 + 16#64 = coroPtr + 0x218#64 := by bv_arith
    have h21c : coroPtr + 0x208#64 + 20#64 = coroPtr + 0x21c#64 := by bv_arith
    rw [h208, htail_pts (coroPtr + 0x208#64), h20c, h210, h218, h21c]
    rcases list_eq_nil_or_length_pos gp.vec.bytes with hnil | hpos
    · have hevs : clonePendingPreKeyEvents (some gp) = [] := by
        simp [clonePendingPreKeyEvents, hnil]
      rw [vecGhostAt_eq_of_nil A.repAlloc gp.vec (coroPtr + 0x1f0#64) hnil, h1f8, h200]
      simp only [sepConj_assoc]
      refine pure_elim_3 fun ⟨hcap_lt, hptr⟩ => ?_
      have hnil_wp := pend_some_nil_placed_wp (A := A) (lim := lim) ext st s sp coroPtr ctxPtr
        gp.vec.cap td2 v10 v18 tw0 tw1 tw3 v28 v2c hcap_lt hpc hrun hsp_eq hsp_al hx19
      refine bind_sepWP_lscro_state_placed hcro hnil_wp (by sep_focus)
        fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
      rcases hregs1 with ⟨hsp1, htr1_s, hx19_1, hx22_1, hx23_1, hx25_1, hx27_1, hx28_1,
        hx29_1, hvregs1⟩
      have hsp1_al : s1.spAligned = true := by
        simpa only [State.spAligned, hsp1, ← hsp_eq] using hsp_al
      have h_rfl :
          (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length⌝ : SepProp) = emp :=
        segClone_pure_eq_emp rfl
      have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp := segClone_pure_eq_emp htail
      have h_pure2 : (⌜gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      refine SepWPp.weaken_pre ?_
        (hnext s1 0#64 1#64 td2 tw3 tw0 hpc1 hrun1 hcro1 hsp1 hsp1_al
          (htr1_s.trans htr) hx19_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1)
      rw [hevs, AllocCostModel.stepEvents,
          vecGhostAt_eq_of_nil A.repAlloc gp.vec (coroPtr + 0x1f0#64) hnil, h1f8, h200,
          h208, htail_pts (coroPtr + 0x208#64), h20c, h210, h218, h21c,
          hnil, vecU8Buf_nil_eq A.repAlloc, h_rfl, h_pure1, h_pure2]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · have hne : gp.vec.bytes ≠ [] := List.ne_nil_of_length_pos hpos
      have hevs : clonePendingPreKeyEvents (some gp) = rustAllocEvents gp.vec.bytes.length 1 := by
        simp [clonePendingPreKeyEvents, hne]
      have hfit_alloc : FitsEvents M lim st (rustAllocEvents gp.vec.bytes.length 1) :=
        hevs ▸ (fitsEnv_clonePendingPreKey_iff (some gp)).mp hfit
      have hallocNoOom := subroutine_ok_allocNoOom_of_budget halloc
      rw [vecGhostAt_eq_of_pos A.repAlloc gp.vec (coroPtr + 0x1f0#64) hpos, h1f8, h200]
      simp only [sepConj_assoc]
      refine pure_elim_3 fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
      have hlen_le63 : gp.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
      have hlay : LayoutOk gp.vec.bytes.length 1 := ⟨hpos, ⟨0, rfl⟩, hlen_le63⟩
      have hrlo : RustLayoutOk gp.vec.bytes.length 1 := ⟨hlay, by decide⟩
      have htoNat : (BitVec.ofNat 64 gp.vec.bytes.length).toNat = gp.vec.bytes.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hprep := pend_some_pos_prep_placed_wp (A := A) (lim := lim) ext hshim st s sp coroPtr
        ctxPtr gp.vec.cap gp.vec.ptr gp.vec.bytes.length tw0 tw1 tw3 v28 v2c
        hcap_lt hpos hlen_lt hpc hrun hsp_eq hsp_al hx19
      refine bind_sepWP_lscro_state_placed hcro hprep (by sep_focus)
        fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
      rcases hregs1 with ⟨hsp1, htr1_s, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1,
        hx23_1, hx25_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs1_s⟩
      have hsp1_al : s1.spAligned = true := by
        simpa only [State.spAligned, hsp1, ← hsp_eq] using hsp_al
      have htr1 : s1.trace = s0.trace := htr1_s.trans htr
      rw [stackAt_chainClone_eq_alloc sp]
      simp only [sepConj_assoc]
      have hφ : (s1.readReg64 .x0).toNat = gp.vec.bytes.length ∧
          (s1.readReg64 .x1).toNat = 1 ∧
          RustLayoutOk gp.vec.bytes.length 1 ∧
          FitsEvents M lim st (rustAllocEvents gp.vec.bytes.length 1) ∧
          LsRetAddr624 (s1.readReg64 .lr) :=
        ⟨by rw [hx0_1, htoNat], by rw [hx1_1]; rfl, hrlo, hfit_alloc,
         by rw [show s1.readReg64 .lr = (blkPl_518).base + 0x1a98#64 from hx30_1]
            exact lsRetAddr624_blockPlacement_base_add 518 0x1a98#64 (by decide) (by decide)⟩
      refine call_raw_nopanic_placed
        (spec := rustCliAllocNoOomSpec M A lim false)
        (x := (gp.vec.bytes.length, 1, st))
        (T := A.pool lim st s1 ∗ stackAt sp allocHookStack)
        hcro1 hallocNoOom hpc1 hrun1 hsp1_al hx30_1
        (by dsimp only [rustCliAllocNoOomSpec]; rw [hsp1])
        hφ (by sep_focus)
        (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hcro2 => ?_)
      have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
      rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, _, hx25_cs2, _,
        hx27_cs2, hx28_cs2, hx29_cs2, hvregs2_1⟩
      have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
      have hx21_2 : s2.readReg64 .x21 = gp.vec.ptr := hx21_cs2.trans hx21_1
      have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 gp.vec.bytes.length :=
        hx22_cs2.trans hx22_1
      have hx23_2 : s2.readReg64 .x23 = s.readReg64 .x23 := hx23_cs2.trans hx23_1
      have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hx25_cs2.trans hx25_1
      have hx27_2 : s2.readReg64 .x27 = ctxPtr := hx27_cs2.trans hx27_1
      have hx28_2 : s2.readReg64 .x28 = s.readReg64 .x28 := hx28_cs2.trans hx28_1
      have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hx29_cs2.trans hx29_1
      dsimp only [rustCliAllocNoOomSpec]
      simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      rw [hsp1, ← hevs]
      refine SepWPp.pure_elim fun ⟨hacp2, hoom, _⟩ => ?_
      have htr2_1 : s2.trace = s1.trace := hacp2.2.1
      have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
      set ptr' := s2.readReg64 .x0
      let st' := M.stepEvents (clonePendingPreKeyEvents (some gp)) st
      have hcopy := pend_some_pos_copy_placed_wp (A := A) (lim := lim) ext hmemcpy st' s2 sp
        coroPtr ptr' gp.vec.ptr td2 v10 v18 gp.vec.bytes hoom hlen_lt hpc2 hrun2 hsp2 hsp2_al
        rfl hx19_2 hx21_2 hx22_2
      refine bind_sepWP_lscro_state_placed hcro2 hcopy (by sep_focus)
        fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
      rcases hregs3 with ⟨hsp3, htr3_2, hx19_3, hx22_3, hx23_3, hx25_3, hx27_3, hx28_3,
        hx29_3, hvregs3_2⟩
      refine CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4.SepWPp.weaken_frame
        (Entails.of_eq (stackAt_chainClone_eq_alloc sp).symm) (by sep_focus) ?_
      have hsp3_al : s3.spAligned = true := by
        simpa only [State.spAligned, hsp3, ← hsp2] using hsp2_al
      have h_rfl :
          (⌜BitVec.ofNat 64 gp.vec.bytes.length =
              BitVec.ofNat 64 gp.vec.bytes.length⌝ : SepProp) = emp :=
        segClone_pure_eq_emp rfl
      have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp := segClone_pure_eq_emp htail
      have h_pure2 :
          (⌜gp.vec.bytes.length ≤ gp.vec.cap.toNat ∧ gp.vec.cap.toNat < 2 ^ 63 ∧
              gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
      refine SepWPp.weaken_pre ?_
        (hnext s3 (BitVec.ofNat 64 gp.vec.bytes.length) ptr' td2 tw3 tw0
          hpc3 hrun3 hcro3 hsp3 hsp3_al (htr3_2.trans htr2)
          hx19_3 hx22_3 (hx23_3.trans hx23_2) (hx25_3.trans hx25_2)
          (hx27_3.trans hx27_2) (hx28_3.trans hx28_2) (hx29_3.trans hx29_2)
          (hvregs3_2.trans (hvregs2_1.trans hvregs1_s)))
      have hlive_eq : A.live ptr' gp.vec.bytes.length 1 =
          A.repAlloc.live ptr' gp.vec.bytes.length 1 := rfl
      rw [vecGhostAt_eq_of_pos A.repAlloc gp.vec (coroPtr + 0x1f0#64) hpos, h1f8, h200,
          h208, htail_pts (coroPtr + 0x208#64), h20c, h210, h218, h21c,
          vecU8Buf_pos_eq A.repAlloc ptr' gp.vec.bytes hpos hlen_lt hoom,
          hlive_eq, h_rfl, h_pure1, h_pure2]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)

/-- Budget-threaded CPS sub-segment 3A (`+0x1a5c → +0x1ac8`, `pending_pre_key`) on `lsProg_518 ext`
from `noAllocShimBudgetSpec`, `rustCliAllocBudgetSpec M A lim false`, and
`sessionMemcpyRegionBudgetSpec`. -/
theorem clonePendingPreKey_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (st : M.σ) (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (sp coroPtr ctxPtr v10 v18 : BitVec 64)
    (v28 v2c : BitVec 32)
    (pending : Option TailVecGhost) (F : SepProp)
    (hfit : FitsEnv M lim st (ClonePendingPreKeyEnv pending))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1a5c#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' d10 : BitVec 64) (w28 w2c : BitVec 32),
      s1.pc = (blkPl_518).base + 0x1ac8#64 → s1.status = .Running →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = sp → s1.spAligned = true → s1.trace = s0.trace →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x22 = pendCap' →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = ctxPtr → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool lim (M.stepEvents (clonePendingPreKeyEvents pending) st) s1 ∗
          stackAt sp chainCloneStack ∗
          optTailVecAt A.repAlloc 48 (coroPtr + 0x1f0#64) pending ∗
          OptPendClone A.repAlloc pending pendCap' pendPtr' ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((sp + 0x10#64) ↦₆₄ d10) ∗ ((sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((sp + 0x28#64) ↦₃₂ w28) ∗ ((sp + 0x2c#64) ↦₃₂ w2c) ∗ F)
        Q Qp) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool lim st s ∗ stackAt sp chainCloneStack ∗
        optTailVecAt A.repAlloc 48 (coroPtr + 0x1f0#64) pending ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0x10#64) ↦₆₄ v10) ∗ ((sp + 0x18#64) ↦₆₄ v18) ∗
        ((sp + 0x28#64) ↦₃₂ v28) ∗ ((sp + 0x2c#64) ↦₃₂ v2c) ∗ F)
      Q Qp :=
  clonePendingPreKey_core_placed_ok ext hshim halloc (memcpy4kBudget_of_region hmemcpy) st s0 s
    ret Q sp coroPtr ctxPtr v10 v18 v28 v2c pending F hfit hcro hpc hrun hsp_eq hsp_al htr hx19
    hnext

/-- Variant of `clonePendingPreKey_placed_ok` accepting `sessionShimBudgetSpec` directly. -/
theorem clonePendingPreKey_placed_ok_of_sessionShim [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (st : M.σ) (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (sp coroPtr ctxPtr v10 v18 : BitVec 64)
    (v28 v2c : BitVec 32)
    (pending : Option TailVecGhost) (F : SepProp)
    (hfit : FitsEnv M lim st (ClonePendingPreKeyEnv pending))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1a5c#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' d10 : BitVec 64) (w28 w2c : BitVec 32),
      s1.pc = (blkPl_518).base + 0x1ac8#64 → s1.status = .Running →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = sp → s1.spAligned = true → s1.trace = s0.trace →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x22 = pendCap' →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = ctxPtr → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool lim (M.stepEvents (clonePendingPreKeyEvents pending) st) s1 ∗
          stackAt sp chainCloneStack ∗
          optTailVecAt A.repAlloc 48 (coroPtr + 0x1f0#64) pending ∗
          OptPendClone A.repAlloc pending pendCap' pendPtr' ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((sp + 0x10#64) ↦₆₄ d10) ∗ ((sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((sp + 0x28#64) ↦₃₂ w28) ∗ ((sp + 0x2c#64) ↦₃₂ w2c) ∗ F)
        Q Qp) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool lim st s ∗ stackAt sp chainCloneStack ∗
        optTailVecAt A.repAlloc 48 (coroPtr + 0x1f0#64) pending ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0x10#64) ↦₆₄ v10) ∗ ((sp + 0x18#64) ↦₆₄ v18) ∗
        ((sp + 0x28#64) ↦₃₂ v28) ∗ ((sp + 0x2c#64) ↦₃₂ v2c) ∗ F)
      Q Qp :=
  clonePendingPreKey_placed_ok ext (subroutine_ok_noAllocShim_of_sessionShimBudget hshim)
    halloc hmemcpy st s0 s ret Q sp coroPtr ctxPtr v10 v18 v28 v2c pending F hfit hcro hpc hrun
    hsp_eq hsp_al htr hx19 hnext

/-- Variant of `clonePendingPreKey_placed_ok` accepting `sessionShimBudgetSpec` and
`sessionMemcpyBudgetSpec allocHookStack` (matching `AllocContractsMem4KBudget` directly). -/
theorem clonePendingPreKey_placed_ok_4k [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym)
      (sessionMemcpyBudgetSpec allocHookStack))
    (st : M.σ) (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (sp coroPtr ctxPtr v10 v18 : BitVec 64)
    (v28 v2c : BitVec 32)
    (pending : Option TailVecGhost) (F : SepProp)
    (hfit : FitsEnv M lim st (ClonePendingPreKeyEnv pending))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1a5c#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' d10 : BitVec 64) (w28 w2c : BitVec 32),
      s1.pc = (blkPl_518).base + 0x1ac8#64 → s1.status = .Running →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = sp → s1.spAligned = true → s1.trace = s0.trace →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x22 = pendCap' →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = ctxPtr → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool lim (M.stepEvents (clonePendingPreKeyEvents pending) st) s1 ∗
          stackAt sp chainCloneStack ∗
          optTailVecAt A.repAlloc 48 (coroPtr + 0x1f0#64) pending ∗
          OptPendClone A.repAlloc pending pendCap' pendPtr' ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((sp + 0x10#64) ↦₆₄ d10) ∗ ((sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((sp + 0x28#64) ↦₃₂ w28) ∗ ((sp + 0x2c#64) ↦₃₂ w2c) ∗ F)
        Q Qp) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool lim st s ∗ stackAt sp chainCloneStack ∗
        optTailVecAt A.repAlloc 48 (coroPtr + 0x1f0#64) pending ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0x10#64) ↦₆₄ v10) ∗ ((sp + 0x18#64) ↦₆₄ v18) ∗
        ((sp + 0x28#64) ↦₃₂ v28) ∗ ((sp + 0x2c#64) ↦₃₂ v2c) ∗ F)
      Q Qp :=
  clonePendingPreKey_core_placed_ok ext (subroutine_ok_noAllocShim_of_sessionShimBudget hshim)
    halloc (memcpy4kBudget_of_4k hmemcpy) st s0 s ret Q sp coroPtr ctxPtr v10 v18 v28 v2c pending
    F hfit hcro hpc hrun hsp_eq hsp_al htr hx19 hnext

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingStepsPlacedBudget
