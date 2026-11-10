/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StorePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StoreStepsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4UnwindPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4ErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveId
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsStoreSession
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsStoreSessionProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Unwind
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP4
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# Segments and `Ok` Epilogue for `Matched.M4StorePlacedBudget`

Pool-threaded Block-`518` Substage P4.4 basic-block segments (`p4_seg4a..4e_placed_wp`), framing
helpers, and the general-`prevSessionsEmptyAt` `Ok` epilogue
`stageP4_storeSession_ok_tail_prevEmpty_vregs_placed` (`+0x444 → s0.readReg64 .x30`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StorePlacedBudgetAux

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

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
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StoreStepsPlacedBudget (
  p4_seg4e_dealloc_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4UnwindPlacedBudget (
  bind_sepWP_lscro_frame call_lscro_nopanic
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.E2E.Pqxdh.ResponderClosure.extractLsb_0_32_append_32
  CryptoVerification.E2E.Pqxdh.ResponderClosure.extractLsb_32_32_append_32
  CryptoVerification.E2E.Pqxdh.ResponderClosure.setWidth_32_append_32
  CryptoVerification.E2E.Pqxdh.ResponderClosure.append_1_32_getElem_zero

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

/-! ## Budget-threaded Block-`518` Substage P4.4 basic-block segments -/

set_option maxHeartbeats 800000 in
theorem p4_seg4a_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State)
    (coroPtr remoteAddrPtr sessionStorePtr sessionStoreVt storeSessionShimAddr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x3cc#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext)) storeSessionShimAddr s
      (((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
       ((coroPtr + 0x90#64) ↦₆₄ sessionStoreVt) ∗
       ((sessionStoreVt + 0x20#64) ↦₆₄ᵣ storeSessionShimAddr) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
          ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
          ((coroPtr + 0x90#64) ↦₆₄ sessionStoreVt) ∗
          ((sessionStoreVt + 0x20#64) ↦₆₄ᵣ storeSessionShimAddr) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = sessionStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x2 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x3e0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 (Rust.withPanics ext) storeSessionShimAddr
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p4_seg4b_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr ctxPtr storeSessionFutPtr storeSessionFutVt storeSessionPollAddr
    u_2c8 u_2d0 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x3e0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = storeSessionFutPtr)
    (hx1 : s.readReg64 .x1 = storeSessionFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext)) storeSessionPollAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ u_2c8) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ u_2d0) ∗
       ((storeSessionFutVt + 0x18#64) ↦₆₄ᵣ storeSessionPollAddr) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ storeSessionFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ storeSessionFutVt) ∗
          ((storeSessionFutVt + 0x18#64) ↦₆₄ᵣ storeSessionPollAddr) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = storeSessionFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x3f8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = storeSessionFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = storeSessionFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  wp_steps_sync_518 (Rust.withPanics ext) storeSessionPollAddr
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p4_seg4c_gen_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr storeSessionFutPtr storeSessionFutVt storeSessionDropAddr w0
    o2 o3 o4 o5 u_340 u_348 u_350 u_358 : BitVec 64)
    (o1 o6 u_360 : BitVec 32)
    (hw0_ne_pend : w0 + 3#64 ≠ 0#64)
    (hdrop_nz : storeSessionDropAddr ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x3f8#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (lsProg_518 (Rust.withPanics ext)) storeSessionDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ storeSessionFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ storeSessionFutVt) ∗
       (storeSessionFutVt ↦₆₄ᵣ storeSessionDropAddr) ∗
       stagingCellsAt (s.sp + 0x340#64) u_340 u_348 u_350 u_358 u_360 ∗
       pollCellsAt (s.sp + 0x3e0#64) w0 o1 o2 o3 o4 o5 o6 ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ storeSessionFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ storeSessionFutVt) ∗
          (storeSessionFutVt ↦₆₄ᵣ storeSessionDropAddr) ∗
          stagingCellsAt (s.sp + 0x340#64) o2 o3 o4 o5 o6 ∗
          pollCellsAt (s.sp + 0x3e0#64) w0 o1 o2 o3 o4 o5 o6 ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = storeSessionFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = storeSessionFutPtr ∧
        s1.readReg64 .x22 = o1.zeroExtend 64 ∧
        s1.readReg64 .x23 = storeSessionFutVt ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x444#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp
  have hw0_beq : (w0 + 3#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_ne_pend
  have hdrop_beq : (storeSessionDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  unfold stagingCellsAt pollCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  wp_steps_sync_518 (Rust.withPanics ext) storeSessionDropAddr
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

set_option maxHeartbeats 800000 in
theorem p4_seg4d_ok_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr storeSessionFutPtr storeSessionFutVt futSize futAlign
    curStateWord0 ptextMid0 ptextMid1 u_370 u_378 : BitVec 64)
    (ptextHead ptextTail u_380 : BitVec 32)
    (hsize_nz : futSize ≠ 0#64)
    (hcur_ne : curStateWord0 + 1#64 ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x444#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = storeSessionFutPtr)
    (hx23 : s.readReg64 .x23 = storeSessionFutVt)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 512) s
      (((coroPtr + 0xf8#64) ↦₆₄ curStateWord0) ∗
       ((coroPtr + 0x280#64) ↦₃₂ ptextHead) ∗
       ((coroPtr + 0x284#64) ↦₆₄ ptextMid0) ∗
       ((coroPtr + 0x28c#64) ↦₆₄ ptextMid1) ∗
       ((coroPtr + 0x294#64) ↦₃₂ ptextTail) ∗
       ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₃₂ u_380) ∗
       A.live storeSessionFutPtr futSize.toNat futAlign.toNat ∗
       memRegion storeSessionFutPtr futSize.toNat ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf8#64) ↦₆₄ curStateWord0) ∗
          ((coroPtr + 0x280#64) ↦₃₂ ptextHead) ∗
          ((coroPtr + 0x284#64) ↦₆₄ ptextMid0) ∗
          ((coroPtr + 0x28c#64) ↦₆₄ ptextMid1) ∗
          ((coroPtr + 0x294#64) ↦₃₂ ptextTail) ∗
          ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₃₂ ptextTail) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents futSize.toNat futAlign.toNat) st) s1 ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = ptextHead.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x48c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  have hcur_beq : (curStateWord0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcur_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = storeSessionFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = storeSessionFutVt := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xfffffffffffffffe#64 := hx28
  wp_steps_sync_518 (Rust.withPanics ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (storeSessionFutPtr, futSize.toNat, futAlign.toNat, st)
  wp_steps_sync_518 (Rust.withPanics ext) (lsmpl.base 512)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved, LibsignalBinary.Heap.AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p4_seg4d_err_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr storeSessionFutPtr storeSessionFutVt futSize futAlign w0 : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hw0_ne_ok : w0 + 2#64 ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x444#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = storeSessionFutPtr)
    (hx23 : s.readReg64 .x23 = storeSessionFutVt)
    (hx28 : s.readReg64 .x28 = w0) :
    SepWP (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x550#64) s
      (((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live storeSessionFutPtr futSize.toNat futAlign.toNat ∗
       memRegion storeSessionFutPtr futSize.toNat ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents futSize.toNat futAlign.toNat) st) s1 ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x8 = s.sp + 0x340#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  have hw0_beq : (w0 + 2#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_ne_ok
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = storeSessionFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = storeSessionFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = w0 := hx28
  wp_steps_sync_518 (Rust.withPanics ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (storeSessionFutPtr, futSize.toNat, futAlign.toNat, st)
  wp_steps_sync_518 (Rust.withPanics ext) ((blkPl_518).base + 0x550#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved, LibsignalBinary.Heap.AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p4_seg4e_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr outPtr prevStatesPtr
    ptextMid0 ptextMid1 w_380 w_388
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (ptextHead w_390 u_ret08 u_ret2c : BitVec 32)
    (b_2c0 : BitVec 8)
    (hpc : s.pc = (blkPl_518).base + 0x48c#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = ptextHead.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext)) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗
       ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗
       ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗
       ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗
       ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
       ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
       ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
       ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
       ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
       ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
       ((s.sp + 0xcc8#64) ↦₆₄ savedX19) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((outPtr + 0x8#64) ↦₃₂ ptextHead) ∗
          ((outPtr + 0xc#64) ↦₆₄ ptextMid0) ∗
          ((outPtr + 0x14#64) ↦₆₄ ptextMid1) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
          ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
          ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
          ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
          ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
          ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
          ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
          ((s.sp + 0xcc8#64) ↦₆₄ savedX19) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = ptextHead.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  wp_steps_sync_518 (Rust.withPanics ext) retAddr
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

/-! ## Framing helpers for `store_session` -/

private theorem p4_fold_sret_ok_m4_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (outPtr ptCap ptPtr w_24 : BitVec 64)
    (u_384 w_2c : BitVec 32) (pt : List (BitVec 8))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64) :
    (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
    ((outPtr + 0x8#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
    ((outPtr + 0xc#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
    ((outPtr + 0x14#64) ↦₆₄
      ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
    ((outPtr + 0x1c#64) ↦₆₄ (u_384 ++ (BitVec.ofNat 64 pt.length).extractLsb' 32 32)) ∗
    ((outPtr + 0x24#64) ↦₆₄ w_24) ∗
    ((outPtr + 0x2c#64) ↦₃₂ w_2c) ∗
    (ptPtr ↦ₛ pt) ∗
    (if ptCap = 0#64 then emp
     else A.live ptPtr ptCap.toNat 1 ∗
       memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ⊢
    vecResultAt A.repAlloc outPtr (.ok pt) := by
  rw [pointsTo32_pair_out1c']
  have hreplace :
      ∀ {A B R P Q : SepProp},
        (A ⊢ B) → P = A ∗ R → B ∗ R = Q → (P ⊢ Q) := by
    intro A B R P Q hab hp hq
    rw [hp, ← hq]
    exact sepConj_mono_left hab
  have hdec := p4_fold_decResultAt_ok A.repAlloc outPtr ptCap ptPtr pt hpt_le hcap_lt hptr_nz
  try simp only [RustCliAllocBudget.repAlloc_live] at hdec
  exact Entails.trans
    (hreplace (memRegion16_out20_fold' outPtr w_24 u_384 w_2c) (by sep_focus) (by sep_ac_rfl))
    hdec

private theorem sp370_words_entails_memRegion36_m4_placed (sp v0 v1 v2 v3 : BitVec 64)
    (v4 : BitVec 32) :
    ((sp + 0x370#64) ↦₆₄ v0) ∗ ((sp + 0x378#64) ↦₆₄ v1) ∗ ((sp + 0x380#64) ↦₆₄ v2) ∗
    ((sp + 0x388#64) ↦₆₄ v3) ∗ ((sp + 0x390#64) ↦₃₂ v4) ⊢ memRegion (sp + 0x370#64) 36 := by
  have h := stagingCellsAt_entails_memRegion36 (sp + 0x370#64) v0 v1 v2 v3 v4
  unfold stagingCellsAt at h
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

theorem coro2c8_16_split_eq_m4_placed (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x2c8#64) 16 =
      ∃∗ u_2d0 : BitVec 64, ∃∗ u_2c8 : BitVec 64,
        ((coroPtr + 0x2c8#64) ↦₆₄ u_2c8) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ u_2d0) := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x2c8#64) (n := 8) (k := 8)
        (b' := coroPtr + 0x2d0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (coroPtr + 0x2c8#64),
      ProofLib.memRegion_eight (coroPtr + 0x2d0#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem coro2c8_16_fold_m4_placed (coroPtr v0 v1 : BitVec 64) :
    ((coroPtr + 0x2c8#64) ↦₆₄ v0) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ v1) ⊢
      memRegion (coroPtr + 0x2c8#64) 16 := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x2c8#64) (n := 8) (k := 8)
        (b' := coroPtr + 0x2d0#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

theorem prevSessionsEmptyAt_sessionRecordAt_fold_placed (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hExtra : SessionExtraRel G ss) :
    prevSessionsEmptyAt A coroPtr g ∗ sessionStateAt A (coroPtr + 0xf8#64) G ss.state ⊢
      sessionRecordAt A (coroPtr + 0xe0#64) ⟨g.prevCap, g.prevPtr, some G⟩ ⟨some ss⟩ := by
  unfold sessionRecordAt prevSessionsEmptyAt sessionStateReprAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono_right (Entails.pure_right hExtra (Entails.refl _))

theorem prevSessionsEmptyAt_sessionRecordAt_unfold_placed (A : RustAlloc)
    (coroPtr : BitVec 64) (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8))) :
    sessionRecordAt A (coroPtr + 0xe0#64) ⟨g.prevCap, g.prevPtr, some G⟩ ⟨some ss⟩ ⊢
      prevSessionsEmptyAt A coroPtr g ∗ sessionStateAt A (coroPtr + 0xf8#64) G ss.state := by
  unfold sessionRecordAt prevSessionsEmptyAt sessionStateReprAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono_right (Entails.pure_left fun _ => Entails.refl _)

/-! ## General-`prevSessionsEmptyAt` `Ok` epilogue (`+0x444 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
theorem stageP4_storeSession_ok_tail_prevEmpty_vregs_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A.repAlloc 0#64)
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (s0 s : State)
    (coroPtr boxPtr outPtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (g : RecordGhost) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : storeSessionCallStack kit ≤ 2 ^ 64)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x444#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = boxPtr)
    (hx23 : s.readReg64 .x23 = 0#64 + kit.storeFutVtOff)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G st ∗
       ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       (ptPtr ↦ₛ pt) ∗
       (if ptCap = 0#64 then emp
        else A.live ptPtr ptCap.toNat 1 ∗
          memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
       ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live boxPtr kit.storeBoxSize 8 ∗
       memRegion boxPtr kit.storeBoxSize ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       memRegion outPtr 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st0 s ∗
       stackAt s.sp (storeSessionCallStack kit))
      (fun sf P_f =>
        Steps (lsProg_518 (Rust.withPanics ext)) s sf ∧
        ∃ evs_tail : List AllocEvent,
          FreeOnlyEvs evs_tail ∧
          (P_f ⊢
            memRegion (coroPtr + 0xe0#64) 368 ∗
            memRegion (coroPtr + 0x280#64) 24 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            vecResultAt A.repAlloc outPtr (.ok pt) ∗
            ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
            ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            memRegion (s.sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim
              (M.stepEvents evs_tail (M.stepEvents (rustDeallocEvents kit.storeBoxSize 8) st0))
              sf ∗
            stackAt s.sp (storeSessionCallStack kit)) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s.trace ∧
          ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  refine SepWPp.with_steps ?_
  have hbox_eq : kit.storeBoxSize = (BitVec.ofNat 64 kit.storeBoxSize).toNat :=
    (Nat.mod_eq_of_lt kit.storeBoxSize_lt).symm
  have hsp_al : s.spAligned = true := hsp_align
  let ptLen := BitVec.ofNat 64 pt.length
  let st_box := M.stepEvents (rustDeallocEvents kit.storeBoxSize 8) st0
  have hst_box_eq :
      M.stepEvents
        (rustDeallocEvents (BitVec.ofNat 64 kit.storeBoxSize).toNat (8#64 : BitVec 64).toNat)
        st0 = st_box := by
    have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [← hbox_eq, h8]
  have hpt_coro :
      ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗ ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
      ((coroPtr + 0x290#64) ↦₆₄ ptLen) =
      ((coroPtr + 0x280#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
      ((coroPtr + 0x284#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((coroPtr + 0x28c#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((coroPtr + 0x294#64) ↦₃₂ ptLen.extractLsb' 32 32) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      words3_eq_head_mid_tail (coroPtr + 0x280#64) ptCap ptPtr ptLen
  have hbox_sz :
      A.live boxPtr kit.storeBoxSize 8 ∗ memRegion boxPtr kit.storeBoxSize =
      A.live boxPtr (BitVec.ofNat 64 kit.storeBoxSize).toNat (8#64 : BitVec 64).toNat ∗
        memRegion boxPtr (BitVec.ofNat 64 kit.storeBoxSize).toNat := by
    rw [← hbox_eq]; rfl
  refine P3P4.SepWPp.weaken_frame
    (p4_sessionStateAt_expose_cap_ne A.repAlloc (coroPtr + 0xf8#64) G st)
    (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hcap_ne => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpt_coro) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hbox_sz) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_split_eq' s.sp)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w_390 => SepWPp.exists_elim fun w_388 =>
    SepWPp.exists_elim fun u_384 => SepWPp.exists_elim fun u_380 =>
    SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 => ?_
  have hstep1 := p4_seg4d_ok_placed_wp (A := A) (lim := lim) ext hdealloc st0 s coroPtr boxPtr
    (0#64 + kit.storeFutVtOff) (BitVec.ofNat 64 kit.storeBoxSize) 8#64
    G.localIk.cap
    (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
    (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
    u_370 u_378 (ptCap.extractLsb' 0 32) (ptLen.extractLsb' 32 32) u_380
    kit.storeBoxSize_ne_zero hcap_ne hpc hrun hsp_al hx19 hx21 hx23 hx24 hx28
  refine bind_sepWP_lscro_frame hcro hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rw [hst_box_eq]
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, _, _, hlr1, hvregs1_0⟩
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (p4_sessionStateAt_expose_cap A.repAlloc (coroPtr + 0xf8#64) G st).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpt_coro.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (coro280_words3_entails_memRegion24 coroPtr ptCap ptPtr ptLen) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_dropSS3 kit s.sp hsp_ub)) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  simp only [sepConj_assoc]
  refine call_lscro_nopanic
    (x := ((⟨coroPtr + 0xf8#64, G, st⟩ : DropSessionStructureGhost), st_box))
    (T := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G st ∗ A.pool lim st_box s1 ∗
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
    (Entails.of_eq (stack_storeSession_to_dropSS3 kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (pointsTo32_pair_sp380' s.sp (ptLen.extractLsb' 32 32) u_384))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion48_eq_exists_pollCells outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2] using hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, _, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = (ptCap.extractLsb' 0 32).zeroExtend 64 :=
    hx22_cs2.trans hx22_1
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun o6_u => SepWPp.exists_elim fun o5_u =>
    SepWPp.exists_elim fun o3_u => SepWPp.exists_elim fun o2_u =>
    SepWPp.exists_elim fun o1_u => SepWPp.exists_elim fun o0_u =>
    SepWPp.exists_elim fun w0_u => ?_
  refine P3P4.SepWPp.weaken_frame (prevSessionsEmptyAt_unpack A.repAlloc coroPtr g) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hprev_lt, _⟩ => ?_
  by_cases hprev_z : g.prevCap = 0#64
  · simp only [hprev_z, ↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
    have hstep3 := p4_seg4e_placed_wp (A := A) (lim := lim) ext (M.stepEvents evs_ss st_box) s2
      coroPtr outPtr g.prevPtr
      (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
      (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
      (u_384 ++ ptLen.extractLsb' 32 32) w_388
      w0_u o1_u o2_u o3_u o5_u
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (ptCap.extractLsb' 0 32) w_390 o0_u o6_u b_2c0
      hpc2 hrun2 hsp2_al hx19_2 hx22_2 hx25_2 hx26_2
    rw [hsp2] at hstep3
    unfold pollCellsAt
    try simp only [BitVec.add_zero, sepConj_assoc] at hstep3
    try simp only [BitVec.add_zero, sepConj_assoc]
    refine bind_sepWP_lscro_frame hcro2 hstep3 (by sep_focus)
      fun sf hpcf hrunf hcrof hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f,
      hx27f, hx28f, hx29f, _, hvregsf_2⟩
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (p4_fold_sret_ok_m4_placed A outPtr ptCap ptPtr w_388 u_384 w_390 pt hpt_le hcap_lt hptr_nz)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (sp370_words_entails_memRegion36_m4_placed s.sp
        (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
        (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
        (u_384 ++ ptLen.extractLsb' 32 32) w_388 w_390)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (coro_e0_3w_344_entails_368 coroPtr 0#64 g.prevPtr 0#64) (by sep_focus) ?_
    refine SepWPp.done hpcf hrunf ⟨evs_ss, hfree_ss, Entails.of_eq (by sep_ac_rfl), ?_⟩
    refine ⟨hspf, by rw [htrf, htr2_1, htr1], ?_,
      hvregsf_2.trans (hvregs_cs2.trans (hvregs1_0.trans hvregs)), hcrof⟩
    exact ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, trivial⟩
  · simp only [hprev_z, ↓reduceIte, RustCliAllocBudget.repAlloc_live, sepConj_assoc]
    have hstep3 := p4_seg4e_dealloc_placed_wp (A := A) (lim := lim) ext hdealloc
      (M.stepEvents evs_ss st_box) s2 coroPtr outPtr g.prevCap g.prevPtr
      (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
      (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
      (u_384 ++ ptLen.extractLsb' 32 32) w_388
      w0_u o1_u o2_u o3_u o5_u
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (ptCap.extractLsb' 0 32) w_390 o0_u o6_u b_2c0
      hprev_z hprev_lt hpc2 hrun2 hsp2_al hx19_2 hx22_2 hx25_2 hx26_2
    rw [hsp2] at hstep3
    unfold pollCellsAt
    try simp only [BitVec.add_zero, sepConj_assoc] at hstep3
    try simp only [BitVec.add_zero, sepConj_assoc]
    refine bind_sepWP_lscro_frame hcro2 hstep3 (by sep_focus)
      fun sf hpcf hrunf hcrof hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f,
      hx27f, hx28f, hx29f, _, hvregsf_2⟩
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (p4_fold_sret_ok_m4_placed A outPtr ptCap ptPtr w_388 u_384 w_390 pt hpt_le hcap_lt hptr_nz)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (sp370_words_entails_memRegion36_m4_placed s.sp
        (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
        (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
        (u_384 ++ ptLen.extractLsb' 32 32) w_388 w_390)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (coro_e0_3w_344_entails_368 coroPtr g.prevCap g.prevPtr 0#64) (by sep_focus) ?_
    have hevs_eq :
        M.stepEvents (rustDeallocEvents (g.prevCap.toNat * 24) 8) (M.stepEvents evs_ss st_box) =
        M.stepEvents (evs_ss ++ rustDeallocEvents (g.prevCap.toNat * 24) 8) st_box :=
      (M.stepEvents_append evs_ss _ st_box).symm
    refine SepWPp.done hpcf hrunf
      ⟨evs_ss ++ rustDeallocEvents (g.prevCap.toNat * 24) 8,
       FreeOnlyEvs.append hfree_ss (FreeOnlyEvs.singleton 8 (g.prevCap.toNat * 24)),
       by rw [← hevs_eq]; exact Entails.of_eq (by sep_ac_rfl), ?_⟩
    refine ⟨hspf, by rw [htrf, htr2_1, htr1], ?_,
      hvregsf_2.trans (hvregs_cs2.trans (hvregs1_0.trans hvregs)), hcrof⟩
    exact ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, trivial⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StorePlacedBudgetAux
