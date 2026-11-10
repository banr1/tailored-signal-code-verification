/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2AuxPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P2 Shared Error Record Teardown

Budget-threaded `[LibsignalPlacement]` counterpart of `Matched.M2Placed` on Block `518`
(`lsProg_518 (Rust.withPanics ext)`), threading `A.pool` across `+0x3588 → s0.readReg64 .x30` with
`FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2PlacedBudget

noncomputable section

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (dropSessionStructureLocal2Stack)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionRecordAt sessionStateReprAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved decryptPrekeySavedRegsAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (
  SepWPp.weaken_frame entails_replace_sub eq_of_sep_emp
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  cond_eq_adds64_of_ne_neg1_std3 memRegion_48_out_entails savedRegsAt_eq_sp_c70
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  coro_e0_3w_344_entails_368 prevSessionsEmptyAt prevSessionsEmptyAt_unpack
  sessionStateAt_split_localIk_cap sp370_4w64_w32_entails_36 stack_dropSS_to_alloc
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0 p2_err_tail_prev_dealloc_placed_wp p2_err_tail_prev_zero_placed_wp
)

alias sessionRecordAt_some_eq_prev_sess_placed :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.sessionRecordAt_some_eq_prev_sess_placed
alias prevSessionsEmptyAt_restore_record_placed :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt_restore_record_placed
alias prevSessionsEmptyAt_unpack_placed :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt_unpack_placed
alias prevSessionsEmptyAt_zero_placed :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt_zero_placed
alias coro_e0_3w_344_entails_368_placed :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.coro_e0_3w_344_entails_368_placed
alias sp370_4w64_w32_entails_36_placed :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.sp370_4w64_w32_entails_36_placed
alias sessionStateAt_split_localIk_cap_placed :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.sessionStateAt_split_localIk_cap_placed
alias lscro_of_steps_m2_placed :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.lscro_of_steps_m2_placed
alias call_raw_nopanic_m2_placed :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.call_raw_nopanic_m2_placed
alias call_lscro_nopanic_m2_placed :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.call_lscro_nopanic_m2_placed
alias call_raw_oom_steps_m2_placed :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.call_raw_oom_steps_m2_placed
alias call_lscro_oom_steps_m2_placed :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.call_lscro_oom_steps_m2_placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

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

/-! ## State-indexed `SepWPp` combinators carrying `LibsignalCodeRoLoaded` -/

theorem bind_sepWP_lscro_steps_m2_placed [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step F : SepProp} {P_step_post : State → SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc hstep hm hL
  rotate_left; · exact (not_satisfies_false_sepConj hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hsteps hpcm hrunm (lscro_of_steps_m2_placed hsteps hcro) hregs R hmm'
      (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem ret_sepWP_lscro_steps_m2_placed [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P P_step F : SepProp} {P_step_post : State → SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog ret s P_step (fun sf P_step' => (P_step' ⊢ P_step_post sf) ∧ Q_regs sf))
    (hP : P = P_step ∗ F)
    (hret : ∀ sf : State, Steps prog s sf → sf.pc = ret → sf.status = .Running →
      LibsignalCodeRoLoaded lsmpl sf.mem → Q_regs sf →
      Q sf (P_step_post sf ∗ F)) :
    SepWPp prog ret s P Q Qp :=
  bind_sepWP_lscro_steps_m2_placed hcro hstep hP fun sf hsteps hpc hrun hcro' hregs =>
    SepWPp.done hpc hrun (hret sf hsteps hpc hrun hcro' hregs)

/-! ## Budget-threaded `ErrDropSome` segment (`+0x3588 → lsmpl.base 512`) -/

/-- Pool-free `VmPreserved` `(blkPl_518).base + 0x3588 → lsmpl.base 512` segment under
`[LibsignalPlacement]`. -/
theorem p2_err_drop_ss_to_call_vm_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr ssCap : BitVec 64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (blkPl_518).base + 0x3588#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) s
      ((coroPtr + 0xf8#64) ↦₆₄ ssCap)
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ ssCap)) ∧
        VmPreserved s s1 ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x359c#64) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1_std3 hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException (Rust.withPanics ext)))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := lsmpl.base 512)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame, hvm,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

/-- Pool-threaded `(blkPl_518).base + 0x3588 → lsmpl.base 512` segment under
`[LibsignalPlacement]`. -/
theorem p2_err_drop_ss_to_call_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr ssCap : BitVec 64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (blkPl_518).base + 0x3588#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) s
      (((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x359c#64) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1_std3 hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 (Rust.withPanics ext) (lsmpl.base 512)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

/-! ## Shared error-return record teardown (`(blkPl_518).base + 0x3588 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
/-- Drops `sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt` and
`prevSessionsEmptyAt A.repAlloc coroPtr g` across `(blkPl_518).base + 0x3588 → s0.readReg64 .x30`
for arbitrary `g : RecordGhost`, producing a pure `∃ evs, FreeOnlyEvs evs ∧ ...` witness and
writing the 48-byte `Result::Err` payload `(errTag, w_22, w_370..w_390)` into `outPtr`. -/
theorem closure_err_drop_record_tail_exists_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st : M.σ) (s0 s : State)
    (sp coroPtr outPtr errTag w_370 w_378 w_380 w_388 : BitVec 64)
    (w_22 w_390 : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       ((sp + 0x370#64) ↦₆₄ w_370) ∗
       ((sp + 0x378#64) ↦₆₄ w_378) ∗
       ((sp + 0x380#64) ↦₆₄ w_380) ∗
       ((sp + 0x388#64) ↦₆₄ w_388) ∗
       ((sp + 0x390#64) ↦₃₂ w_390) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool lim st s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (P_f ⊢
            memRegion (coroPtr + 0xe0#64) 368 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
            ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
            ((outPtr + 0xc#64) ↦₆₄ w_370) ∗
            ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
            ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
            ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
            ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
            memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp dropSessionStructureLocal2Stack)) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  refine SepWPp.weaken_frame (prevSessionsEmptyAt_unpack A.repAlloc coroPtr g) (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun ⟨hprev_lt, _⟩ => ?_
  obtain ⟨R_ss, hss_fwd, hss_bwd⟩ :=
    sessionStateAt_split_localIk_cap A.repAlloc (coroPtr + 0xf8#64) recG recSt
  refine SepWPp.weaken_frame hss_fwd (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun hcap_lt => ?_
  have hcap_ne : recG.localIk.cap ≠ 0xffffffffffffffff#64 := by bv_omega
  have hto_call := p2_err_drop_ss_to_call_placed_wp (A := A) (lim := lim) ext st s coroPtr
    recG.localIk.cap hcap_ne hpc hrun hsp_align hx19
  refine bind_sepWP_lscro_steps_m2_placed hcro hto_call (by sep_focus)
    fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx0_1, hx19_1, hx22_1, hx25_1, hx26_1, hx28_1, _, hx30_1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  refine SepWPp.weaken_frame hss_bwd (by sep_focus) ?_
  refine call_lscro_nopanic_m2_placed
    (spec := dropSessionStructureLocal2Spec M A lim)
    (x := (⟨coroPtr + 0xf8#64, recG, recSt⟩, st))
    (T := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ A.pool lim st s1 ∗
      stackAt sp dropSessionStructureLocal2Stack)
    hcro1 (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hdrop_ss)
    hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
    (And.intro hx0_1 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s1.readReg64 .lr) by
      simp (config := { decide := true }) [show s1.readReg64 .lr = _ from hx30_1, wp_norm]))
    (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp1]
  sep_norm
  refine SepWPp.exists_elim fun evs_ss => ?_
  sep_norm
  refine SepWPp.pure_elim fun ⟨htr2_1, hfree_ss⟩ => ?_
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s := hvregs_cs2.trans hvregs1
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by
    rw [hsp2, ← hsp_eq]; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = w_22.zeroExtend 64 := hx22_cs2.trans (hx22_1.trans hx22)
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by
    rw [hsp2]; exact hx25_cs2.trans (hx25_1.trans hx25)
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = errTag := hx28_cs2.trans (hx28_1.trans hx28)
  rw [stack_dropSS_to_alloc sp hdss_le, savedRegsAt_eq_sp_c70 sp s0]
  refine SepWPp.weaken_frame (memRegion_48_out_entails outPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ret0 => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret2c => ?_
  by_cases hcap : g.prevCap = 0#64
  · simp only [hcap, ↓reduceIte, emp_sepConj]
    have htail := p2_err_tail_prev_zero_placed_wp (A := A) (lim := lim) ext (M.stepEvents evs_ss st)
      s2 coroPtr outPtr errTag g.prevPtr
      w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 w_390 u_ret08 u_ret2c b_2c0
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at htail
    refine ret_sepWP_lscro_steps_m2_placed hcro2 htail
      (by sep_focus)
      fun sf _ _ _ hcrof hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hvregsf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine ⟨⟨evs_ss, hfree_ss, ?_⟩, hspf, htrf.trans (htr2_1.trans htr1_s),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hvregsf.trans hvregs2_s,
      hcrof⟩
    refine Entails.trans (entails_replace_sub (coro_e0_3w_344_entails_368 coroPtr 0#64 g.prevPtr 0#64)
      (by sep_focus) rfl) ?_
    exact entails_replace_sub (sp370_4w64_w32_entails_36 sp w_370 w_378 w_380 w_388 w_390)
      (by sep_focus) (eq_of_sep_emp (by sep_focus))
  · simp only [hcap, ↓reduceIte]
    have htail := p2_err_tail_prev_dealloc_placed_wp (A := A) (lim := lim) ext hdealloc
      (M.stepEvents evs_ss st) s2 coroPtr outPtr errTag
      g.prevCap g.prevPtr w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 w_390 u_ret08 u_ret2c b_2c0 hcap hprev_lt
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at htail
    refine ret_sepWP_lscro_steps_m2_placed hcro2 htail
      (by simp only [RustCliAllocBudget.repAlloc_live]; sep_focus)
      fun sf _ _ _ hcrof hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hvregsf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    have hfree_all : FreeOnlyEvs (evs_ss ++ rustDeallocEvents (g.prevCap.toNat * 24) 8) :=
      hfree_ss.append (FreeOnlyEvs.singleton 8 (g.prevCap.toNat * 24))
    refine ⟨⟨evs_ss ++ rustDeallocEvents (g.prevCap.toNat * 24) 8, hfree_all, ?_⟩,
      hspf, htrf.trans (htr2_1.trans htr1_s),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hvregsf.trans hvregs2_s,
      hcrof⟩
    rw [M.stepEvents_append evs_ss (rustDeallocEvents (g.prevCap.toNat * 24) 8) st]
    refine Entails.trans (entails_replace_sub (coro_e0_3w_344_entails_368 coroPtr g.prevCap g.prevPtr 0#64)
      (by sep_focus) rfl) ?_
    exact entails_replace_sub (sp370_4w64_w32_entails_36 sp w_370 w_378 w_380 w_388 w_390)
      (by sep_focus) (eq_of_sep_emp (by sep_focus))

/-- Spatial `∃∗ evs, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf` presentation of
`closure_err_drop_record_tail_exists_placed_ok`. -/
theorem closure_err_drop_record_tail_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st : M.σ) (s0 s : State)
    (sp coroPtr outPtr errTag w_370 w_378 w_380 w_388 : BitVec 64)
    (w_22 w_390 : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       ((sp + 0x370#64) ↦₆₄ w_370) ∗
       ((sp + 0x378#64) ↦₆₄ w_378) ∗
       ((sp + 0x380#64) ↦₆₄ w_380) ∗
       ((sp + 0x388#64) ↦₆₄ w_388) ∗
       ((sp + 0x390#64) ↦₃₂ w_390) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool lim st s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗
          ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗
            A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ :=
    closure_err_drop_record_tail_exists_placed_ok hdealloc hdrop_ss st s0 s sp coroPtr outPtr
      errTag w_370 w_378 w_380 w_388 w_22 w_390 b_2c0 g recG recSt hcro hsp_eq hsp_lt hpc hrun
      hsp_align hx19 hx22 hx25 hx26 hx28 R hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, ⟨⟨evs, hfree, hent⟩, hrest⟩⟩ | hpan_oom
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hrest⟩⟩⟩
    refine Entails.trans hent ?_
    have hpack : A.pool lim (M.stepEvents evs st) sf ⊢
        ∃∗ evs' : List AllocEvent, ⌜FreeOnlyEvs evs'⌝ ∗
          A.pool lim (M.stepEvents evs' st) sf :=
      Entails.sepExists_right evs (Entails.pure_right hfree (Entails.refl _))
    exact entails_replace_sub hpack (by sep_focus) (by sep_ac_rfl)
  · exact ⟨sf, hsteps, Or.inr hpan_oom⟩

end

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2PlacedBudget
