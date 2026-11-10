/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `VmPreserved` and Pool-Threaded Block-`518` Segments for `Matched.M2OkPlacedBudget`

Pool-framing combinators (`sepWP_frame_pool`, `sepWPp_lift_qp`, `sepWPp_frame_pool`,
`sepWPp_frame_pool_drop_vm`, `bind_sepWPp_nopanic_state`) and Block-`518` `VmPreserved` /
pool-threaded basic-block segment lemmas (`+0x094c .. +0x1778`) for `Matched.M2OkPlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2OkPlacedBudgetAux

noncomputable section

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.CliHandshake.RespClosurePlaced (
  blkLib_eq_518 blkPl_518 lsProg_518
)
open scoped CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  cond_ne_adds64_of_ne_neg3_std3
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

@[local simp, local wp_norm] private theorem vregs_advancePC (s : State) :
    s.advancePC.vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_setMem (s : State) (m : Memory) :
    (s.setMem m).vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_setPState (s : State) (ps : PState) :
    (s.setPState ps).vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_writeReg64 (s : State) (r : Reg) (val : BitVec 64) :
    (s.writeReg64 r val).vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_writeReg32 (s : State) (r : Reg) (val : BitVec 32) :
    (s.writeReg32 r val).vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_writeReg (s : State) (w : Width) (r : Reg) (val : BitVec 64) :
    (s.writeReg w r val).vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_applyWriteback
    (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).vregs = s.vregs := by cases wb <;> cases s <;> rfl

/-! ## `VmPreserved` and pool-framing combinators -/

theorem sepWP_frame_pool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {prog : Program} {target_pc : BitVec 64} {s : State}
    {Pre Post : SepProp} {Q : State → Prop}
    (hwp : SepWP prog target_pc s Pre
      (fun s1 P_f => (P_f ⊢ Post) ∧ VmPreserved s s1 ∧ Q s1)) :
    SepWP prog target_pc s (Pre ∗ A.pool lim st s)
      (fun s1 P_f => (P_f ⊢ Post ∗ A.pool lim st s1) ∧ Q s1) := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨s1, hsteps, hout⟩ := SepWP.to_reaches_pc hwp hm hL
  rcases hout with ⟨hpc1, hrun1, P_f, hPf, hent, hvm, hQ⟩ | ⟨_, hoom⟩
  · refine ⟨s1, hsteps, Or.inl ⟨hpc1, hrun1, P_f ∗ A.pool lim st s, ?_, ?_, hQ⟩⟩
    · rwa [sepConj_assoc]
    · rw [A.pool_of_vmPreserved hvm]
      exact sepConj_mono_left hent
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem sepWPp_lift_qp {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (fun _ _ => False)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, hok | ⟨_, _, _, hpan⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact False.elim hpan
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_frame_pool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {prog : Program} {ret : BitVec 64} {s : State}
    {Pre Post : SepProp} {Q_regs : State → Prop} {Qp : State → SepProp → Prop}
    (hwp : SepWPp prog ret s Pre
      (fun sf P_f => (P_f ⊢ Post) ∧ VmPreserved s sf ∧ Q_regs sf)
      (fun _ _ => False)) :
    SepWPp prog ret s (Pre ∗ A.pool lim st s)
      (fun sf P_f => (P_f ⊢ Post ∗ A.pool lim st sf) ∧ VmPreserved s sf ∧ Q_regs sf)
      Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hent, hvm, hregs⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hwp (A.pool lim st s ∗ R) hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f ∗ A.pool lim st s, ?_, ?_, hvm, hregs⟩⟩
    · rwa [sepConj_assoc]
    · rw [A.pool_of_vmPreserved hvm]
      exact sepConj_mono_left hent
  · exact False.elim hpan
  · exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_frame_pool_drop_vm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {prog : Program} {ret : BitVec 64} {s : State}
    {Pre Post : SepProp} {Q_regs : State → Prop} {Qp : State → SepProp → Prop}
    (hwp : SepWPp prog ret s Pre
      (fun sf P_f => (P_f ⊢ Post) ∧ VmPreserved s sf ∧ Q_regs sf)
      (fun _ _ => False)) :
    SepWPp prog ret s (Pre ∗ A.pool lim st s)
      (fun sf P_f => (P_f ⊢ Post ∗ A.pool lim st sf) ∧ Q_regs sf)
      Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hent, _, hregs⟩ | hrest⟩ :=
    sepWPp_frame_pool A lim st (Qp := Qp) hwp R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, hent, hregs⟩⟩
  · exact ⟨sf, hsteps, Or.inr hrest⟩

theorem bind_sepWPp_nopanic_state {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_stage F : SepProp} {P_stage_post : State → SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim hpan
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Block-`518` `VmPreserved` and pool-threaded basic-block segments -/

theorem p2_seg_094c_ok_vm_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x94c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x1064#64) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3e0#64) ↦₈ 0#8))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3e0#64) ↦₈ 0#8)) ∧
        VmPreserved s s1 ∧
        (s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
         s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = s.readReg64 .x21 ∧
         s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
         s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = outPtr ∧
         s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
         s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = s.readReg64 .x30)) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException (Rust.withPanics ext)))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := (blkPl_518).base + 0x1064#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm := _hnsp.toVmPreserved (by wp_norm_lhs)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame, hvm,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem p2_seg_094c_ok_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ)
    (s : State) (coroPtr outPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x94c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x1064#64) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3e0#64) ↦₈ 0#8) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3e0#64) ↦₈ 0#8) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = s.readReg64 .x30) := by
  simpa only [sepConj_assoc] using
    sepWP_frame_pool A lim st (p2_seg_094c_ok_vm_placed_wp ext s coroPtr outPtr hpc hrun hsp_align hx19)

theorem p2_seg_10cc_match_vm_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr u_a8 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x10cc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x1648#64) s
      ((s.sp + 0xa8#64) ↦₆₄ u_a8)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xa8#64) ↦₆₄ 0#64)) ∧
        VmPreserved s s1 ∧
        (s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
         s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
         s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x23 = 2#64 ∧
         s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
         s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
         s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = s.readReg64 .x30)) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 1#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException (Rust.withPanics ext)))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := (blkPl_518).base + 0x1648#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm := _hnsp.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm ⊢
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame, hvm,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem p2_seg_10cc_match_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ)
    (s : State) (coroPtr u_a8 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x10cc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x1648#64) s
      (((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xa8#64) ↦₆₄ 0#64) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x23 = 2#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = s.readReg64 .x30) :=
  sepWP_frame_pool A lim st
    (p2_seg_10cc_match_vm_placed_wp ext s coroPtr u_a8 hpc hrun hsp_align hx0 hx19)

theorem p2_seg_10cc_mismatch_vm_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x10cc#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x12fc#64) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        VmPreserved s s1 ∧
        (s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
         s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
         s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
         s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
         s1.readReg64 .x30 = s.readReg64 .x30)) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException (Rust.withPanics ext)))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := (blkPl_518).base + 0x12fc#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm := _hnsp.toVmPreserved (by wp_norm_lhs)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.refl _, hvm,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

theorem p2_seg_10cc_mismatch_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ)
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x10cc#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x12fc#64) s
      (A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30) := by
  simpa only [emp_sepConj] using
    sepWP_frame_pool A lim st (p2_seg_10cc_mismatch_vm_placed_wp ext s coroPtr hpc hrun hx0 hx19)

theorem p2_seg_1064_none_vm_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr q2 q3 q4 u_a90 : BitVec 64)
    (w0 u_920 : BitVec 32) (h1 h5 u_924 u_a98 : BitVec 16)
    (hpc : s.pc = (blkPl_518).base + 0x1064#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x370#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x12fc#64) s
      (((s.sp + 0x3e1#64) ↦₈ 0#8) ∗ ((s.sp + 0x3e2#64) ↦₃₂ w0) ∗
       ((s.sp + 0x3e6#64) ↦₁₆ h1) ∗ ((s.sp + 0x3e8#64) ↦₆₄ q2) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ q3) ∗ ((s.sp + 0x3f8#64) ↦₆₄ q4) ∗
       ((s.sp + 0x400#64) ↦₁₆ h5) ∗ ((s.sp + 0x920#64) ↦₃₂ u_920) ∗
       ((s.sp + 0x924#64) ↦₁₆ u_924) ∗ ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₁₆ u_a98))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e1#64) ↦₈ 0#8) ∗ ((s.sp + 0x3e2#64) ↦₃₂ w0) ∗
          ((s.sp + 0x3e6#64) ↦₁₆ h1) ∗ ((s.sp + 0x3e8#64) ↦₆₄ q2) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ q3) ∗ ((s.sp + 0x3f8#64) ↦₆₄ q4) ∗
          ((s.sp + 0x400#64) ↦₁₆ h5) ∗ ((s.sp + 0x920#64) ↦₃₂ w0) ∗
          ((s.sp + 0x924#64) ↦₁₆ h1) ∗ ((s.sp + 0xa90#64) ↦₆₄ q4) ∗
          ((s.sp + 0xa98#64) ↦₁₆ h5)) ∧
        VmPreserved s s1 ∧
        (s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
         s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
         s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
         s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
         s1.readReg64 .x30 = s.readReg64 .x30)) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x370#64 := hx21
  have h72 : (s.sp + 0x370#64) + 0x72#64 = s.sp + 0x3e2#64 := by bv_omega
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException (Rust.withPanics ext)))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := (blkPl_518).base + 0x12fc#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm := _hnsp.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm ⊢
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame, hvm,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

theorem p2_seg_1064_none_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ)
    (s : State) (coroPtr q2 q3 q4 u_a90 : BitVec 64)
    (w0 u_920 : BitVec 32) (h1 h5 u_924 u_a98 : BitVec 16)
    (hpc : s.pc = (blkPl_518).base + 0x1064#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x370#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x12fc#64) s
      (((s.sp + 0x3e1#64) ↦₈ 0#8) ∗ ((s.sp + 0x3e2#64) ↦₃₂ w0) ∗
       ((s.sp + 0x3e6#64) ↦₁₆ h1) ∗ ((s.sp + 0x3e8#64) ↦₆₄ q2) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ q3) ∗ ((s.sp + 0x3f8#64) ↦₆₄ q4) ∗
       ((s.sp + 0x400#64) ↦₁₆ h5) ∗ ((s.sp + 0x920#64) ↦₃₂ u_920) ∗
       ((s.sp + 0x924#64) ↦₁₆ u_924) ∗ ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₁₆ u_a98) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e1#64) ↦₈ 0#8) ∗ ((s.sp + 0x3e2#64) ↦₃₂ w0) ∗
          ((s.sp + 0x3e6#64) ↦₁₆ h1) ∗ ((s.sp + 0x3e8#64) ↦₆₄ q2) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ q3) ∗ ((s.sp + 0x3f8#64) ↦₆₄ q4) ∗
          ((s.sp + 0x400#64) ↦₁₆ h5) ∗ ((s.sp + 0x920#64) ↦₃₂ w0) ∗
          ((s.sp + 0x924#64) ↦₁₆ h1) ∗ ((s.sp + 0xa90#64) ↦₆₄ q4) ∗
          ((s.sp + 0xa98#64) ↦₁₆ h5) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30) := by
  simpa only [sepConj_assoc] using
    sepWP_frame_pool A lim st
      (p2_seg_1064_none_vm_placed_wp ext s coroPtr q2 q3 q4 u_a90 w0 u_920 h1 h5 u_924 u_a98
        hpc hrun hsp_align hx19 hx21)

theorem p2_seg_1064_some_load_vm_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr q2 q3 q4 u_a90 : BitVec 64)
    (w0 u_920 : BitVec 32) (h1 h5 u_924 u_a98 : BitVec 16)
    (hpc : s.pc = (blkPl_518).base + 0x1064#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x370#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x1094#64) s
      (((s.sp + 0x3e1#64) ↦₈ 1#8) ∗ ((s.sp + 0x3e2#64) ↦₃₂ w0) ∗
       ((s.sp + 0x3e6#64) ↦₁₆ h1) ∗ ((s.sp + 0x3e8#64) ↦₆₄ q2) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ q3) ∗ ((s.sp + 0x3f8#64) ↦₆₄ q4) ∗
       ((s.sp + 0x400#64) ↦₁₆ h5) ∗ ((s.sp + 0x920#64) ↦₃₂ u_920) ∗
       ((s.sp + 0x924#64) ↦₁₆ u_924) ∗ ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₁₆ u_a98))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e1#64) ↦₈ 1#8) ∗ ((s.sp + 0x3e2#64) ↦₃₂ w0) ∗
          ((s.sp + 0x3e6#64) ↦₁₆ h1) ∗ ((s.sp + 0x3e8#64) ↦₆₄ q2) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ q3) ∗ ((s.sp + 0x3f8#64) ↦₆₄ q4) ∗
          ((s.sp + 0x400#64) ↦₁₆ h5) ∗ ((s.sp + 0x920#64) ↦₃₂ w0) ∗
          ((s.sp + 0x924#64) ↦₁₆ h1) ∗ ((s.sp + 0xa90#64) ↦₆₄ q4) ∗
          ((s.sp + 0xa98#64) ↦₁₆ h5)) ∧
        VmPreserved s s1 ∧
        (s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
         s1.readReg64 .x8 = q3 ∧ s1.readReg64 .x9 = q2 ∧
         s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = s.sp + 0x370#64 ∧
         s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
         s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
         s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = s.readReg64 .x30)) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x370#64 := hx21
  have h72 : (s.sp + 0x370#64) + 0x72#64 = s.sp + 0x3e2#64 := by bv_omega
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException (Rust.withPanics ext)))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := (blkPl_518).base + 0x1094#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm := _hnsp.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm ⊢
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame, hvm,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem p2_seg_1064_some_load_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ)
    (s : State) (coroPtr q2 q3 q4 u_a90 : BitVec 64)
    (w0 u_920 : BitVec 32) (h1 h5 u_924 u_a98 : BitVec 16)
    (hpc : s.pc = (blkPl_518).base + 0x1064#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x370#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x1094#64) s
      (((s.sp + 0x3e1#64) ↦₈ 1#8) ∗ ((s.sp + 0x3e2#64) ↦₃₂ w0) ∗
       ((s.sp + 0x3e6#64) ↦₁₆ h1) ∗ ((s.sp + 0x3e8#64) ↦₆₄ q2) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ q3) ∗ ((s.sp + 0x3f8#64) ↦₆₄ q4) ∗
       ((s.sp + 0x400#64) ↦₁₆ h5) ∗ ((s.sp + 0x920#64) ↦₃₂ u_920) ∗
       ((s.sp + 0x924#64) ↦₁₆ u_924) ∗ ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₁₆ u_a98) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e1#64) ↦₈ 1#8) ∗ ((s.sp + 0x3e2#64) ↦₃₂ w0) ∗
          ((s.sp + 0x3e6#64) ↦₁₆ h1) ∗ ((s.sp + 0x3e8#64) ↦₆₄ q2) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ q3) ∗ ((s.sp + 0x3f8#64) ↦₆₄ q4) ∗
          ((s.sp + 0x400#64) ↦₁₆ h5) ∗ ((s.sp + 0x920#64) ↦₃₂ w0) ∗
          ((s.sp + 0x924#64) ↦₁₆ h1) ∗ ((s.sp + 0xa90#64) ↦₆₄ q4) ∗
          ((s.sp + 0xa98#64) ↦₁₆ h5) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x8 = q3 ∧ s1.readReg64 .x9 = q2 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = s.readReg64 .x30) := by
  simpa only [sepConj_assoc] using
    sepWP_frame_pool A lim st
      (p2_seg_1064_some_load_vm_placed_wp ext s coroPtr q2 q3 q4 u_a90 w0 u_920 h1 h5 u_924 u_a98
        hpc hrun hsp_align hx19 hx21)

theorem p2_seg_1094_some_store_vm_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr q2 q3 q4 d2 d3 d4 : BitVec 64)
    (w0 d0 : BitVec 32) (h1 h5 d1 d5 : BitVec 16)
    (hpc : s.pc = (blkPl_518).base + 0x1094#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = q3)
    (hx9 : s.readReg64 .x9 = q2)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x370#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 212) s
      (((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((s.sp + 0x3e0#64) ↦₃₂ d0) ∗ ((s.sp + 0x3e4#64) ↦₁₆ d1) ∗
       ((s.sp + 0x3e6#64) ↦₆₄ d2) ∗ ((s.sp + 0x3ee#64) ↦₆₄ d3) ∗
       ((s.sp + 0x3f6#64) ↦₆₄ d4) ∗ ((s.sp + 0x3fe#64) ↦₁₆ d5) ∗
       ((s.sp + 0x920#64) ↦₃₂ w0) ∗ ((s.sp + 0x924#64) ↦₁₆ h1) ∗
       ((s.sp + 0xa90#64) ↦₆₄ q4) ∗ ((s.sp + 0xa98#64) ↦₁₆ h5))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0x3e0#64) ↦₃₂ w0) ∗ ((s.sp + 0x3e4#64) ↦₁₆ h1) ∗
          ((s.sp + 0x3e6#64) ↦₆₄ q2) ∗ ((s.sp + 0x3ee#64) ↦₆₄ q3) ∗
          ((s.sp + 0x3f6#64) ↦₆₄ q4) ∗ ((s.sp + 0x3fe#64) ↦₁₆ h5) ∗
          ((s.sp + 0x920#64) ↦₃₂ w0) ∗ ((s.sp + 0x924#64) ↦₁₆ h1) ∗
          ((s.sp + 0xa90#64) ↦₆₄ q4) ∗ ((s.sp + 0xa98#64) ↦₁₆ h5)) ∧
        VmPreserved s s1 ∧
        (s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
         s1.readReg64 .x0 = msgPtr + 0xc8#64 ∧ s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧
         s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = s.sp + 0x370#64 ∧
         s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
         s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
         s1.readReg64 .x29 = s.readReg64 .x29 ∧
         s1.readReg64 .x30 = (blkPl_518).base + 0x10cc#64)) := by
  have hx8' : s.readReg64 (Reg.gpr 8#5) = q3 := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = q2 := hx9
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x370#64 := hx21
  have h76 : (s.sp + 0x370#64) + 0x76#64 = s.sp + 0x3e6#64 := by bv_omega
  have h7e : (s.sp + 0x370#64) + 0x7e#64 = s.sp + 0x3ee#64 := by bv_omega
  have h86 : (s.sp + 0x370#64) + 0x86#64 = s.sp + 0x3f6#64 := by bv_omega
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException (Rust.withPanics ext)))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := lsmpl.base 212)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm := _hnsp.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm ⊢
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame, hvm,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem p2_seg_1094_some_store_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ)
    (s : State) (coroPtr msgPtr q2 q3 q4 d2 d3 d4 : BitVec 64)
    (w0 d0 : BitVec 32) (h1 h5 d1 d5 : BitVec 16)
    (hpc : s.pc = (blkPl_518).base + 0x1094#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = q3)
    (hx9 : s.readReg64 .x9 = q2)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x370#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 212) s
      (((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((s.sp + 0x3e0#64) ↦₃₂ d0) ∗ ((s.sp + 0x3e4#64) ↦₁₆ d1) ∗
       ((s.sp + 0x3e6#64) ↦₆₄ d2) ∗ ((s.sp + 0x3ee#64) ↦₆₄ d3) ∗
       ((s.sp + 0x3f6#64) ↦₆₄ d4) ∗ ((s.sp + 0x3fe#64) ↦₁₆ d5) ∗
       ((s.sp + 0x920#64) ↦₃₂ w0) ∗ ((s.sp + 0x924#64) ↦₁₆ h1) ∗
       ((s.sp + 0xa90#64) ↦₆₄ q4) ∗ ((s.sp + 0xa98#64) ↦₁₆ h5) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0x3e0#64) ↦₃₂ w0) ∗ ((s.sp + 0x3e4#64) ↦₁₆ h1) ∗
          ((s.sp + 0x3e6#64) ↦₆₄ q2) ∗ ((s.sp + 0x3ee#64) ↦₆₄ q3) ∗
          ((s.sp + 0x3f6#64) ↦₆₄ q4) ∗ ((s.sp + 0x3fe#64) ↦₁₆ h5) ∗
          ((s.sp + 0x920#64) ↦₃₂ w0) ∗ ((s.sp + 0x924#64) ↦₁₆ h1) ∗
          ((s.sp + 0xa90#64) ↦₆₄ q4) ∗ ((s.sp + 0xa98#64) ↦₁₆ h5) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x0 = msgPtr + 0xc8#64 ∧ s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x10cc#64) := by
  simpa only [sepConj_assoc] using
    sepWP_frame_pool A lim st
      (p2_seg_1094_some_store_vm_placed_wp ext s coroPtr msgPtr q2 q3 q4 d2 d3 d4
        w0 d0 h1 h5 d1 d5 hpc hrun hsp_align hx8 hx9 hx19 hx21)

theorem p2_err_tail_a_vm_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr errTag outPtr : BitVec 64)
    (b_4f2 : BitVec 8)
    (herr_ne_neg3 : errTag ≠ 0xfffffffffffffffd#64)
    (hpc : s.pc = (blkPl_518).base + 0x1648#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx20 : s.readReg64 .x20 = errTag)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 509) s
      (((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8)) ∧
        VmPreserved s s1 ∧
        (s1.sp = s.sp ∧
         s1.trace = s.trace ∧
         s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
         s1.readReg64 .x19 = coroPtr ∧
         s1.readReg64 .x20 = errTag ∧
         s1.readReg64 .x21 = s.readReg64 .x21 ∧
         s1.readReg64 .x23 = s.readReg64 .x23 ∧
         s1.readReg64 .x24 =
           ((s.readReg64 .x23).setWidth 32).zeroExtend 64 ||| (s.readReg64 .x22 <<< 32) ∧
         s1.readReg64 .x25 = s.readReg64 .x25 ∧
         s1.readReg64 .x26 = outPtr ∧
         s1.readReg64 .x27 = s.readReg64 .x27 ∧
         s1.readReg64 .x28 = s.readReg64 .x28 ∧
         s1.readReg64 .x29 = s.readReg64 .x29 ∧
         s1.readReg64 .x30 = (blkPl_518).base + 0x1698#64 ∧
         calleeSavedVRegs s1 = calleeSavedVRegs s)) := by
  have hcond := cond_ne_adds64_of_ne_neg3_std3 herr_ne_neg3
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = errTag := hx20
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException (Rust.withPanics ext)))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := lsmpl.base 509)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm := _hnsp.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm ⊢
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame, hvm,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem p2_err_tail_a_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ)
    (s : State) (coroPtr errTag outPtr : BitVec 64)
    (b_4f2 : BitVec 8)
    (herr_ne_neg3 : errTag ≠ 0xfffffffffffffffd#64)
    (hpc : s.pc = (blkPl_518).base + 0x1648#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx20 : s.readReg64 .x20 = errTag)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 509) s
      (((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = errTag ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 =
          ((s.readReg64 .x23).setWidth 32).zeroExtend 64 ||| (s.readReg64 .x22 <<< 32) ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x1698#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  simpa only [sepConj_assoc] using
    sepWP_frame_pool A lim st
      (p2_err_tail_a_vm_placed_wp ext s coroPtr errTag outPtr b_4f2 herr_ne_neg3
        hpc hrun hsp_align hx19 hx20 hx26)

set_option linter.unusedVariables false in
theorem p2_seg6f_vm_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
      opkPacked kyberPacked ss0 v_330 v_388
      u_250 u_258 u_260 u_270 u_278 u_298 u_2a0
      u_80 u_88 u_90 u_a0 u_a8 u_b0 v_d0
      u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (opkIdIsSome u_268 u_26c u_2a8 u_b8 : BitVec 32)
    (msgVerByte b_390 b_3ac : BitVec 8)
    (hss0_ne : ss0 + 1#64 ≠ 0#64)
    (hpack_lo : (opkPacked &&& 0xff#64) = (opkIdIsSome.zeroExtend 64 &&& 0xff#64))
    (hpc : s.pc = (blkPl_518).base + 0x1698#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx22 : s.readReg64 .x22 = kyberPacked)
    (hx23 : s.readReg64 .x23 = opkIdIsSome.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = opkPacked) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x1778#64) s
      (((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗
       ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗
       ((coroPtr + 0x268#64) ↦₃₂ u_268) ∗
       ((coroPtr + 0x26c#64) ↦₃₂ u_26c) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗
       ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
       ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((s.sp + 0x80#64) ↦₆₄ u_80) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₃₂ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
       ((s.sp + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((s.sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((s.sp + 0x3b0#64) ↦₆₄ u_3b0) ∗
       ((s.sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((s.sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ u_3d0) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ u_3d8))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
          ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
          ((coroPtr + 0x250#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((coroPtr + 0x258#64) ↦₆₄ opkPacked) ∗
          ((coroPtr + 0x260#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x268#64) ↦₃₂ v_d0.truncate 32) ∗
          ((coroPtr + 0x26c#64) ↦₃₂ (s.readReg64 (Reg.gpr 11#5)).truncate 32) ∗
          ((coroPtr + 0x270#64) ↦₆₄ v_330) ∗
          ((coroPtr + 0x278#64) ↦₆₄ v_388) ∗
          ((coroPtr + 0x298#64) ↦₆₄ opkPacked) ∗
          ((coroPtr + 0x2a0#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
          ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
          ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0x90#64) ↦₆₄ v_388) ∗
          ((s.sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ v_330) ∗
          ((s.sp + 0xb0#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
          ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
          ((s.sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3b0#64) ↦₆₄ (s.sp + 0x3ac#64)) ∗
          ((s.sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0x3c0#64) ↦₆₄ (s.sp + 0x3a0#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ 8#64) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        VmPreserved s s1 ∧
        (s1.sp = s.sp ∧
         s1.trace = s.trace ∧
         s1.readReg64 .x8 = coroPtr + 0xe0#64 ∧
         s1.readReg64 .x9 = 8#64 ∧
         s1.readReg64 .x10 = msgVerByte.zeroExtend 64 ∧
         s1.readReg64 .x11 = coroPtr + 0xf8#64 ∧
         s1.readReg64 .x19 = coroPtr ∧
         s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
         s1.readReg64 .x22 = kyberPacked ∧
         s1.readReg64 .x23 = opkPacked ∧
         s1.readReg64 .x24 = opkPacked ∧
         s1.readReg64 .x25 = s.readReg64 .x25 ∧
         s1.readReg64 .x26 = v_330 ∧
         s1.readReg64 .x27 = s.sp + 0x370#64 ∧
         s1.readReg64 .x28 = s.readReg64 .x28 ∧
         s1.readReg64 .x29 = s.readReg64 .x29 ∧
         calleeSavedVRegs s1 = calleeSavedVRegs s)) := by
  have hss0_beq : (ss0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hss0_ne
  have hbfm1 : ((opkIdIsSome.zeroExtend 64 &&& 255#64) |||
    ((opkPacked >>> 8 &&& 72057594037927935#64) <<< 8)) = opkPacked := by
    revert hpack_lo; clear * -; bv_slice
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0xfffffffffffffffe#64 := hx20
  have hx22' : s.readReg64 (Reg.gpr 22#5) = kyberPacked := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = opkIdIsSome.zeroExtend 64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = opkPacked := hx24
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException (Rust.withPanics ext)))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := (blkPl_518).base + 0x1778#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm := _hnsp.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm ⊢
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame, hvm,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp only [hx19', hx20', hx22', hx23', hx24', wp_norm, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', wp_norm, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', wp_norm, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', wp_norm, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', wp_norm, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', wp_norm, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', hbfm1, wp_norm, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', hbfm1, wp_norm, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', wp_norm, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', wp_norm, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', wp_norm, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', wp_norm, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', wp_norm, arm64_norm],
    by simp only [hx19', hx20', hx22', hx23', hx24', wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

theorem p2_seg6f_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ)
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
      opkPacked kyberPacked ss0 v_330 v_388
      u_250 u_258 u_260 u_270 u_278 u_298 u_2a0
      u_80 u_88 u_90 u_a0 u_a8 u_b0 v_d0
      u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (opkIdIsSome u_268 u_26c u_2a8 u_b8 : BitVec 32)
    (msgVerByte b_390 b_3ac : BitVec 8)
    (hss0_ne : ss0 + 1#64 ≠ 0#64)
    (hpack_lo : (opkPacked &&& 0xff#64) = (opkIdIsSome.zeroExtend 64 &&& 0xff#64))
    (hpc : s.pc = (blkPl_518).base + 0x1698#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx22 : s.readReg64 .x22 = kyberPacked)
    (hx23 : s.readReg64 .x23 = opkIdIsSome.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = opkPacked) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x1778#64) s
      (((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗
       ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗
       ((coroPtr + 0x268#64) ↦₃₂ u_268) ∗
       ((coroPtr + 0x26c#64) ↦₃₂ u_26c) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗
       ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
       ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((s.sp + 0x80#64) ↦₆₄ u_80) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₃₂ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
       ((s.sp + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((s.sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((s.sp + 0x3b0#64) ↦₆₄ u_3b0) ∗
       ((s.sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((s.sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ u_3d0) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ u_3d8) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
          ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
          ((coroPtr + 0x250#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((coroPtr + 0x258#64) ↦₆₄ opkPacked) ∗
          ((coroPtr + 0x260#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x268#64) ↦₃₂ v_d0.truncate 32) ∗
          ((coroPtr + 0x26c#64) ↦₃₂ (s.readReg64 (Reg.gpr 11#5)).truncate 32) ∗
          ((coroPtr + 0x270#64) ↦₆₄ v_330) ∗
          ((coroPtr + 0x278#64) ↦₆₄ v_388) ∗
          ((coroPtr + 0x298#64) ↦₆₄ opkPacked) ∗
          ((coroPtr + 0x2a0#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
          ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
          ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0x90#64) ↦₆₄ v_388) ∗
          ((s.sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ v_330) ∗
          ((s.sp + 0xb0#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
          ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
          ((s.sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3b0#64) ↦₆₄ (s.sp + 0x3ac#64)) ∗
          ((s.sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0x3c0#64) ↦₆₄ (s.sp + 0x3a0#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ 8#64) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x9 = 8#64 ∧
        s1.readReg64 .x10 = msgVerByte.zeroExtend 64 ∧
        s1.readReg64 .x11 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x22 = kyberPacked ∧
        s1.readReg64 .x23 = opkPacked ∧
        s1.readReg64 .x24 = opkPacked ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_330 ∧
        s1.readReg64 .x27 = s.sp + 0x370#64 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  simpa only [sepConj_assoc] using
    sepWP_frame_pool A lim st
      (p2_seg6f_vm_placed_wp ext s coroPtr msgPtr remoteAddrPtr localAddrPtr
        opkPacked kyberPacked ss0 v_330 v_388
        u_250 u_258 u_260 u_270 u_278 u_298 u_2a0
        u_80 u_88 u_90 u_a0 u_a8 u_b0 v_d0
        u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
        opkIdIsSome u_268 u_26c u_2a8 u_b8
        msgVerByte b_390 b_3ac hss0_ne hpack_lo
        hpc hrun hsp_align hx19 hx20 hx22 hx23 hx24)

end

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2OkPlacedBudgetAux
