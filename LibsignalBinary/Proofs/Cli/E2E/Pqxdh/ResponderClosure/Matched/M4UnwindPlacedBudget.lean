/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4UnwindPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwindPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4ErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwind
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable General-`prevCap` Stage P4 Error Unwinds

Budget-threaded `[LibsignalPlacement]` counterpart of `Matched.M4UnwindPlaced` on Block `518`
(`lsProg_518`), threading `A.pool`, `rustCliDeallocBudgetSpec`, and `dropSessionStructureLocal2Spec`
(`FreeOnlyEvs`) across `+0x550 → x30` and `+0x3588 → x30`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4UnwindPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  coro_e0_3w_344_entails_368 prevSessionsEmptyAt prevSessionsEmptyAt_unpack
)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
  VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0 p2_err_tail_prev_dealloc_placed_wp p2_err_tail_prev_zero_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlaced (
  call_nopanic_rocl_steps_frame_placed
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

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

/-! ## Preserving `StoreKit.LibsignalCodeRoLoaded` across `SepWP` and `SepWPp` -/

theorem lscro_of_steps [LibsignalPlacement] {prog : Program} {s s' : State}
    (hsteps : Steps prog s s')
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem :=
  hcro.of_keepsFrozen hsteps.keepsFrozen

theorem bind_sepWP_lscro_frame [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step F : SepProp} {P_step_post : State → SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc hstep hm hL
  rotate_left; · first | exact False.elim hoom | exact (not_satisfies_false_sepConj hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpcm hrunm (lscro_of_steps hsteps hcro) hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem call_lscro_nopanic [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp :=
  call_nopanic_rocl_steps_frame_placed hcro
    (StoreKit.subroutine_ok_rocl_of_withLsCodeRoLoaded hcall)
    hpc hrun hsp hlr hspec hφ hP
    (fun sf _ => hnext sf)
    hpan_false hexit_false hoom_false

/-! ## Budget-threaded Block-`518` error-unwind basic-block segments -/

/-- `+0x550 → +0x3588` when `ptCap = 0#64` on `lsProg_518 ext`, threading `A.pool lim st s`. -/
theorem p4_err_550_zero_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr slot ptPtr o2 o3 o4 o5 u_370 u_378 u_380 u_388 : BitVec 64)
    (o6 u_390 : BitVec 32)
    (hpc : s.pc = (blkPl_518).base + 0x550#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = slot)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext)
      ((blkPl_518).base + 0x3588#64) s
      (((coroPtr + 0x280#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       stagingCellsAt slot o2 o3 o4 o5 o6 ∗
       stagingCellsAt (s.sp + 0x370#64) u_370 u_378 u_380 u_388 u_390 ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x280#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
          stagingCellsAt slot o2 o3 o4 o5 o6 ∗
          stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  unfold stagingCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hx8' : s.readReg64 (Reg.gpr 8#5) = slot := hx8
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  wp_steps_sync_518 ext ((blkPl_518).base + 0x3588#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-- `+0x550 → +0x3588` when `ptCap = 0#64` on `lsProg_518 (Rust.withPanics ext)`. -/
theorem p4_err_550_zero_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) :
    ∀ (st : M.σ) (s : State) (coroPtr slot ptPtr o2 o3 o4 o5 u_370 u_378 u_380 u_388 : BitVec 64)
      (o6 u_390 : BitVec 32),
      s.pc = (blkPl_518).base + 0x550#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x8 = slot →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x24 = s.sp + 0x370#64 →
      SepWP (lsProg_518 (Rust.withPanics ext))
        ((blkPl_518).base + 0x3588#64) s
        (((coroPtr + 0x280#64) ↦₆₄ 0#64) ∗
         ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
         stagingCellsAt slot o2 o3 o4 o5 o6 ∗
         stagingCellsAt (s.sp + 0x370#64) u_370 u_378 u_380 u_388 u_390 ∗
         A.pool lim st s)
        (fun s1 P_f =>
          (P_f ⊢
            ((coroPtr + 0x280#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
            stagingCellsAt slot o2 o3 o4 o5 o6 ∗
            stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
            A.pool lim st s1) ∧
          s1.sp = s.sp ∧ s1.trace = s.trace ∧
          s1.readReg64 .x19 = coroPtr ∧
          s1.readReg64 .x22 = s.readReg64 .x22 ∧
          s1.readReg64 .x24 = s.sp + 0x370#64 ∧
          s1.readReg64 .x25 = s.readReg64 .x25 ∧
          s1.readReg64 .x26 = s.readReg64 .x26 ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x28 = s.readReg64 .x28 ∧
          s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p4_err_550_zero_vregs_placed_wp (Rust.withPanics ext)

/-- `+0x550 → +0x3588` when `ptCap ≠ 0#64` on `lsProg_518 ext`, threading `A.pool lim st s`
and `rustCliDeallocBudgetSpec M A lim`. -/
theorem p4_err_550_nonzero_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr slot ptCap ptPtr o2 o3 o4 o5 u_370 u_378 u_380 u_388 : BitVec 64)
    (o6 u_390 : BitVec 32)
    (hcap_nz : ptCap ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x550#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = slot)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext)
      ((blkPl_518).base + 0x3588#64) s
      (((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       stagingCellsAt slot o2 o3 o4 o5 o6 ∗
       stagingCellsAt (s.sp + 0x370#64) u_370 u_378 u_380 u_388 u_390 ∗
       A.live ptPtr ptCap.toNat 1 ∗
       memRegion ptPtr ptCap.toNat ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
          ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
          stagingCellsAt slot o2 o3 o4 o5 o6 ∗
          stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
          A.pool lim (M.stepEvents (rustDeallocEvents ptCap.toNat 1) st) s1 ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcap_beq : (ptCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_nz
  unfold stagingCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hx8' : s.readReg64 (Reg.gpr 8#5) = slot := hx8
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (ptPtr, ptCap.toNat, 1, st)
  wp_steps_sync_518 ext ((blkPl_518).base + 0x3588#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved, AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-- `+0x550 → +0x3588` when `ptCap ≠ 0#64` on `lsProg_518 (Rust.withPanics ext)`. -/
theorem p4_err_550_nonzero_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim)) :
    ∀ (st : M.σ) (s : State) (coroPtr slot ptCap ptPtr o2 o3 o4 o5 u_370 u_378 u_380 u_388 : BitVec 64)
      (o6 u_390 : BitVec 32),
      ptCap ≠ 0#64 →
      s.pc = (blkPl_518).base + 0x550#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x8 = slot →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x24 = s.sp + 0x370#64 →
      SepWP (lsProg_518 (Rust.withPanics ext))
        ((blkPl_518).base + 0x3588#64) s
        (((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
         ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
         stagingCellsAt slot o2 o3 o4 o5 o6 ∗
         stagingCellsAt (s.sp + 0x370#64) u_370 u_378 u_380 u_388 u_390 ∗
         A.live ptPtr ptCap.toNat 1 ∗
         memRegion ptPtr ptCap.toNat ∗
         A.pool lim st s ∗
         stackAt s.sp allocHookStack)
        (fun s1 P_f =>
          (P_f ⊢
            ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
            ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
            stagingCellsAt slot o2 o3 o4 o5 o6 ∗
            stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
            A.pool lim (M.stepEvents (rustDeallocEvents ptCap.toNat 1) st) s1 ∗
            stackAt s.sp allocHookStack) ∧
          s1.sp = s.sp ∧ s1.trace = s.trace ∧
          s1.readReg64 .x19 = coroPtr ∧
          s1.readReg64 .x22 = s.readReg64 .x22 ∧
          s1.readReg64 .x24 = s.sp + 0x370#64 ∧
          s1.readReg64 .x25 = s.readReg64 .x25 ∧
          s1.readReg64 .x26 = s.readReg64 .x26 ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x28 = s.readReg64 .x28 ∧
          s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p4_err_550_nonzero_vregs_placed_wp (Rust.withPanics ext) hdealloc

/-- `+0x3588 → dropSessionStructure3` (`lsmpl.base 512`) on `lsProg_518 ext`, threading `A.pool lim st s`. -/
theorem p4_err_3588_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr ssCap : BitVec 64)
    (hcap_ne : ssCap + 1#64 ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x3588#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 512) s
      (((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x359c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcur_beq : (ssCap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext (lsmpl.base 512)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-- `+0x3588 → dropSessionStructure3` (`lsmpl.base 512`) on `lsProg_518 (Rust.withPanics ext)`. -/
theorem p4_err_3588_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) :
    ∀ (st : M.σ) (s : State) (coroPtr ssCap : BitVec 64),
      ssCap + 1#64 ≠ 0#64 →
      s.pc = (blkPl_518).base + 0x3588#64 →
      s.status = .Running →
      s.readReg64 .x19 = coroPtr →
      SepWP (lsProg_518 (Rust.withPanics ext))
        (lsmpl.base 512) s
        (((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ A.pool lim st s)
        (fun s1 P_f =>
          (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ A.pool lim st s1) ∧
          s1.sp = s.sp ∧ s1.trace = s.trace ∧
          s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
          s1.readReg64 .x19 = coroPtr ∧
          s1.readReg64 .x22 = s.readReg64 .x22 ∧
          s1.readReg64 .x24 = s.readReg64 .x24 ∧
          s1.readReg64 .x25 = s.readReg64 .x25 ∧
          s1.readReg64 .x26 = s.readReg64 .x26 ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x28 = s.readReg64 .x28 ∧
          s1.readReg64 .x29 = s.readReg64 .x29 ∧
          s1.readReg64 .x30 = (blkPl_518).base + 0x359c#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p4_err_3588_vregs_placed_wp (Rust.withPanics ext)

/-- `+0x359c → retAddr` when `prevCap = 0#64` on `lsProg_518 ext`, threading `A.pool lim st s`. -/
theorem p4_err_tail_359c_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr outPtr errTag prevStatesPtr
    o2 o3 o4 o5 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 o6 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hpc : s.pc = (blkPl_518).base + 0x359c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (lsProg_518 ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       pollCellsAt outPtr u_ret0 u_ret08 u_ret0c u_ret14 u_ret1c u_ret24 u_ret2c ∗
       stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
          stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  unfold pollCellsAt stagingCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  wp_steps_sync_518 ext retAddr
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-! ## Composed general-`prevCap` Stage P4 error unwinds -/

set_option maxHeartbeats 800000 in
/-- Budget-threaded composed `(blkPl_518).base + 0x3588 → s0.readReg64 .x30` unwind on general
`prevSessionsEmptyAt A.repAlloc coroPtr g` under `[LibsignalPlacement]`, producing `FreeOnlyEvs`. -/
theorem stageP4_err_unwind_3588_prevEmpty_vregs_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (s0 s : State)
    (coroPtr outPtr errTag o2 o3 o4 o5 : BitVec 64)
    (w_22 o6 : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hsp_ub : stageP4ErrUnwindStack ≤ 2 ^ 64)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G st ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st0 s ∗
       stackAt s.sp stageP4ErrUnwindStack)
      (fun sf P_f =>
        Steps (lsProg_518 (Rust.withPanics ext)) s sf ∧
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            memRegion (s.sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt s.sp stageP4ErrUnwindStack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s.trace ∧
          ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  refine SepWPp.with_steps ?_
  refine P3P4.SepWPp.weaken_frame (p4_sessionStateAt_expose_cap_ne A.repAlloc (coroPtr + 0xf8#64) G st)
    (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hcap_ne => ?_
  have hstep1 := p4_err_3588_placed_wp (A := A) (lim := lim) ext st0 s coroPtr G.localIk.cap
    hcap_ne hpc hrun hx19
  refine bind_sepWP_lscro_frame hcro hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hlr1, hvregs1⟩
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (p4_sessionStateAt_expose_cap A.repAlloc (coroPtr + 0xf8#64) G st).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_errUnwind_to_dropSS3 s.sp hsp_ub)) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  simp only [sepConj_assoc]
  refine call_lscro_nopanic
    (x := ((⟨coroPtr + 0xf8#64, G, st⟩ : DropSessionStructureGhost), st0))
    (T := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G st ∗ A.pool lim st0 s1 ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
    hcro1 (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hDropSS3)
    hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
    (And.intro hx0_1 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s1.readReg64 .lr) by
      simp (config := { decide := true }) [show s1.readReg64 .lr = _ from hlr1, wp_norm]))
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_ss => ?_
  refine SepWPp.pure_elim fun ⟨htr2_1, hfree_ss⟩ => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_errUnwind_to_dropSS3 s.sp hsp_ub).symm) (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = w_22.zeroExtend 64 := hx22_cs2.trans (hx22_1.trans hx22)
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = errTag := hx28_cs2.trans (hx28_1.trans hx28)
  refine P3P4.SepWPp.weaken_frame (prevSessionsEmptyAt_unpack A.repAlloc coroPtr g) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hprev_lt, _⟩ => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion48_eq_exists_pollCells outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun o6_u => SepWPp.exists_elim fun o5_u =>
    SepWPp.exists_elim fun o4_u => SepWPp.exists_elim fun o3_u =>
    SepWPp.exists_elim fun o2_u => SepWPp.exists_elim fun o1_u =>
    SepWPp.exists_elim fun w0_u => ?_
  by_cases hprev_z : g.prevCap = 0#64
  · simp only [hprev_z, ↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
    have hstep3 := p2_err_tail_prev_zero_placed_wp (A := A) (lim := lim) ext
      (M.stepEvents evs_ss st0) s2 coroPtr outPtr errTag
      g.prevPtr o2 o3 o4 o5 w0_u o2_u o3_u o4_u o5_u
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 o6 o1_u o6_u b_2c0
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at hstep3
    unfold pollCellsAt stagingCellsAt
    simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hstep3 ⊢
    refine bind_sepWP_lscro_frame hcro2 hstep3 (by sep_focus)
      fun sf hpcf hrunf hcrof hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hvregsf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f,
      hx27f, hx28f, hx29f, _⟩
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    have h370 := stagingCellsAt_entails_memRegion36 (s.sp + 0x370#64) o2 o3 o4 o5 o6
    unfold stagingCellsAt at h370
    simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h370
    refine P3P4.SepWPp.weaken_frame h370 (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (coro_e0_3w_344_entails_368 coroPtr 0#64 g.prevPtr 0#64)
      (by sep_focus) ?_
    refine SepWPp.done hpcf hrunf ⟨evs_ss, hfree_ss, Entails.of_eq (by sep_ac_rfl), ?_⟩
    refine ⟨hspf, by rw [htrf, htr2_1, htr1], ?_,
      hvregsf.trans (hvregs_cs2.trans (hvregs1.trans hvregs)), hcrof⟩
    exact ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, trivial⟩
  · simp only [hprev_z, ↓reduceIte, RustCliAllocBudget.repAlloc_live, sepConj_assoc]
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub)) (by sep_focus) ?_
    have hstep3 := p2_err_tail_prev_dealloc_placed_wp (A := A) (lim := lim) ext hdealloc
      (M.stepEvents evs_ss st0) s2 coroPtr outPtr errTag
      g.prevCap g.prevPtr o2 o3 o4 o5 w0_u o2_u o3_u o4_u o5_u
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 o6 o1_u o6_u b_2c0
      hprev_z hprev_lt hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at hstep3
    unfold pollCellsAt stagingCellsAt
    simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hstep3 ⊢
    refine bind_sepWP_lscro_frame hcro2 hstep3 (by sep_focus)
      fun sf hpcf hrunf hcrof hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hvregsf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f,
      hx27f, hx28f, hx29f, _⟩
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    have h370 := stagingCellsAt_entails_memRegion36 (s.sp + 0x370#64) o2 o3 o4 o5 o6
    unfold stagingCellsAt at h370
    simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h370
    refine P3P4.SepWPp.weaken_frame h370 (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (coro_e0_3w_344_entails_368 coroPtr g.prevCap g.prevPtr 0#64)
      (by sep_focus) ?_
    have hevs_eq :
        M.stepEvents (rustDeallocEvents (g.prevCap.toNat * 24) 8) (M.stepEvents evs_ss st0) =
        M.stepEvents (evs_ss ++ rustDeallocEvents (g.prevCap.toNat * 24) 8) st0 :=
      (M.stepEvents_append evs_ss _ st0).symm
    refine SepWPp.done hpcf hrunf
      ⟨evs_ss ++ rustDeallocEvents (g.prevCap.toNat * 24) 8,
       FreeOnlyEvs.append hfree_ss (FreeOnlyEvs.singleton 8 (g.prevCap.toNat * 24)),
       by rw [← hevs_eq]; exact Entails.of_eq (by sep_ac_rfl), ?_⟩
    refine ⟨hspf, by rw [htrf, htr2_1, htr1], ?_,
      hvregsf.trans (hvregs_cs2.trans (hvregs1.trans hvregs)), hcrof⟩
    exact ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, trivial⟩

set_option maxHeartbeats 800000 in
/-- Budget-threaded composed `(blkPl_518).base + 0x550 → s0.readReg64 .x30` unwind on general
`prevSessionsEmptyAt A.repAlloc coroPtr g` under `[LibsignalPlacement]`, producing `FreeOnlyEvs`. -/
theorem stageP4_err_unwind_550_prevEmpty_vregs_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (s0 s : State)
    (coroPtr slot ptCap ptPtr outPtr errTag o2 o3 o4 o5 : BitVec 64)
    (w_22 o6 : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (g : RecordGhost) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : stageP4ErrUnwindStack ≤ 2 ^ 64)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x550#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = slot)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (ptPtr ↦ₛ pt) ∗
       (if ptCap = 0#64 then emp
        else A.live ptPtr ptCap.toNat 1 ∗
          memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       stagingCellsAt slot o2 o3 o4 o5 o6 ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G st ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st0 s ∗
       stackAt s.sp stageP4ErrUnwindStack)
      (fun sf P_f =>
        Steps (lsProg_518 (Rust.withPanics ext)) s sf ∧
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            memRegion (coroPtr + 0x280#64) 24 ∗
            memRegion slot 36 ∗
            memRegion (s.sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt s.sp stageP4ErrUnwindStack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s.trace ∧
          ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  refine SepWPp.with_steps ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion36_eq_exists_stagingCells (s.sp + 0x370#64))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_390 => SepWPp.exists_elim fun u_388 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  by_cases hcap_z : ptCap = 0#64
  · subst hcap_z
    refine P3P4.SepWPp.weaken_frame (ptextBuf_dealloc_zero A.repAlloc ptPtr pt hpt_le) (by sep_focus) ?_
    simp only [emp_sepConj, sepConj_emp, sepConj_assoc]
    have hstep0 := p4_err_550_zero_placed_wp (A := A) (lim := lim) ext st0 s coroPtr slot ptPtr
      o2 o3 o4 o5 u_370 u_378 u_380 u_388 o6 u_390
      hpc hrun hsp_align hx8 hx19 hx24
    refine bind_sepWP_lscro_frame hcro hstep0 (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hvregs1⟩
    refine P3P4.SepWPp.weaken_frame
      (coro280_words3_entails_memRegion24 coroPtr 0#64 ptPtr (BitVec.ofNat 64 pt.length))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (stagingCellsAt_entails_memRegion36 slot o2 o3 o4 o5 o6) (by sep_focus) ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have hx22_1' : s1.readReg64 .x22 = w_22.zeroExtend 64 := hx22_1.trans hx22
    have hx25_1' : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_1, hx25, hsp1]
    have hx26_1' : s1.readReg64 .x26 = outPtr := hx26_1.trans hx26
    have hx28_1' : s1.readReg64 .x28 = errTag := hx28_1.trans hx28
    have htail := stageP4_err_unwind_3588_prevEmpty_vregs_placed_ok ext hdealloc hDropSS3 st0 s0 s1
      coroPtr outPtr errTag o2 o3 o4 o5 w_22 o6 b_2c0 g G st (fun _ _ => False)
      hsp_ub hcro1 hpc1 hrun1 hsp1_align hx19_1 hx22_1' hx25_1' hx26_1' hx28_1'
      (hvregs1.trans hvregs)
    rw [hsp1] at htail
    refine SepWPp.bind_false_frame htail (by sep_focus)
      fun sf P_f hpcf hrunf ⟨_, evs_unw, hfree_unw, hentf, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hentf) ?_
    refine SepWPp.done hpcf hrunf ⟨evs_unw, hfree_unw, Entails.of_eq (by sep_ac_rfl), ?_⟩
    exact ⟨hspf, by rw [htrf, htr1], hcsf, hvregsf, hcrof⟩
  · have hpt_dealloc :
        (ptPtr ↦ₛ pt) ∗
          (if ptCap = 0#64 then emp
           else A.live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ⊢
        A.live ptPtr ptCap.toNat 1 ∗ memRegion ptPtr ptCap.toNat := by
      simpa only [RustCliAllocBudget.repAlloc_live] using
        ptextBuf_dealloc_nonzero A.repAlloc ptCap ptPtr pt hcap_z hpt_le
    refine P3P4.SepWPp.weaken_frame hpt_dealloc (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub)) (by sep_focus) ?_
    simp only [sepConj_assoc]
    have hstep0 := p4_err_550_nonzero_placed_wp (A := A) (lim := lim) ext hdealloc st0 s
      coroPtr slot ptCap ptPtr
      o2 o3 o4 o5 u_370 u_378 u_380 u_388 o6 u_390
      hcap_z hpc hrun hsp_align hx8 hx19 hx24
    refine bind_sepWP_lscro_frame hcro hstep0 (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hvregs1⟩
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (coro280_words3_entails_memRegion24 coroPtr ptCap ptPtr (BitVec.ofNat 64 pt.length))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (stagingCellsAt_entails_memRegion36 slot o2 o3 o4 o5 o6) (by sep_focus) ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have hx22_1' : s1.readReg64 .x22 = w_22.zeroExtend 64 := hx22_1.trans hx22
    have hx25_1' : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_1, hx25, hsp1]
    have hx26_1' : s1.readReg64 .x26 = outPtr := hx26_1.trans hx26
    have hx28_1' : s1.readReg64 .x28 = errTag := hx28_1.trans hx28
    have htail := stageP4_err_unwind_3588_prevEmpty_vregs_placed_ok ext hdealloc hDropSS3
      (M.stepEvents (rustDeallocEvents ptCap.toNat 1) st0) s0 s1
      coroPtr outPtr errTag o2 o3 o4 o5 w_22 o6 b_2c0 g G st (fun _ _ => False)
      hsp_ub hcro1 hpc1 hrun1 hsp1_align hx19_1 hx22_1' hx25_1' hx26_1' hx28_1'
      (hvregs1.trans hvregs)
    rw [hsp1] at htail
    refine SepWPp.bind_false_frame htail (by sep_focus)
      fun sf P_f hpcf hrunf ⟨_, evs_unw, hfree_unw, hentf, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hentf) ?_
    have hevs_eq :
        M.stepEvents evs_unw (M.stepEvents (rustDeallocEvents ptCap.toNat 1) st0) =
        M.stepEvents (rustDeallocEvents ptCap.toNat 1 ++ evs_unw) st0 :=
      (M.stepEvents_append (rustDeallocEvents ptCap.toNat 1) evs_unw st0).symm
    refine SepWPp.done hpcf hrunf
      ⟨rustDeallocEvents ptCap.toNat 1 ++ evs_unw,
       FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 ptCap.toNat) hfree_unw,
       by rw [← hevs_eq]; exact Entails.of_eq (by sep_ac_rfl), ?_⟩
    exact ⟨hspf, by rw [htrf, htr1], hcsf, hvregsf, hcrof⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4UnwindPlacedBudget
