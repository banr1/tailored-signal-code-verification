/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveId
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwindPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP4
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P4.1 `save_identity` Segments

Budget-threaded `[LibsignalPlacement]` counterpart of `StageP4VRegsSaveIdPlaced` on Block `518`
(`lsProg_518 ext`), threading `A.pool` and `rustCliDeallocBudgetSpec` across Substage P4.1
basic-block segments.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  pointsTo32_pair_eq pollCellsAt stagingCellsAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpec rustDeallocEvents
)
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

/-! ## Budget-threaded basic-block `SepWP` segments on `lsProg_518 ext` -/

theorem p4_seg1a_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr idStorePtr idStoreVt saveIdentityShimAddr
    remoteAddrPtr remoteIkPtr ptextMid0 ptextMid1
    u_250 u_258 u_coro284 u_coro28c v_3d0 : BitVec 64)
    (ptextHead ptextTail u_260 u_coro280 u_coro294 : BitVec 32)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (lsProg_518 ext) saveIdentityShimAddr s
      (((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0xa0#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x280#64) ↦₃₂ u_coro280) ∗
       ((coroPtr + 0x284#64) ↦₆₄ u_coro284) ∗
       ((coroPtr + 0x28c#64) ↦₆₄ u_coro28c) ∗
       ((coroPtr + 0x294#64) ↦₃₂ u_coro294) ∗
       ((idStoreVt + 0x28#64) ↦₆₄ᵣ saveIdentityShimAddr) ∗
       ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
       ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
       ((s.sp + 0x250#64) ↦₆₄ u_250) ∗
       ((s.sp + 0x258#64) ↦₆₄ u_258) ∗
       ((s.sp + 0x260#64) ↦₃₂ u_260) ∗
       ((s.sp + 0x278#64) ↦₃₂ ptextHead) ∗
       ((s.sp + 0x27c#64) ↦₆₄ ptextMid0) ∗
       ((s.sp + 0x284#64) ↦₆₄ ptextMid1) ∗
       ((s.sp + 0x28c#64) ↦₃₂ ptextTail) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0xa0#64) ↦₆₄ idStoreVt) ∗
          ((coroPtr + 0x280#64) ↦₃₂ ptextHead) ∗
          ((coroPtr + 0x284#64) ↦₆₄ ptextMid0) ∗
          ((coroPtr + 0x28c#64) ↦₆₄ ptextMid1) ∗
          ((coroPtr + 0x294#64) ↦₃₂ ptextTail) ∗
          ((idStoreVt + 0x28#64) ↦₆₄ᵣ saveIdentityShimAddr) ∗
          ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
          ((s.sp + 0x250#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x258#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x260#64) ↦₃₂ ptextTail) ∗
          ((s.sp + 0x278#64) ↦₃₂ ptextHead) ∗
          ((s.sp + 0x27c#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x284#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x28c#64) ↦₃₂ ptextTail) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧ s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x2 = remoteIkPtr ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x3564#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xfffffffffffffffe#64 := hx28
  wp_steps_sync_518 ext saveIdentityShimAddr
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

theorem p4_seg1b_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr ctxPtr saveIdFutPtr saveIdFutVt saveIdentityPollAddr
    u_2c8 u_2d0 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x3564#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = saveIdFutPtr)
    (hx1 : s.readReg64 .x1 = saveIdFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (lsProg_518 ext) saveIdentityPollAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ u_2c8) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ u_2d0) ∗
       ((saveIdFutVt + 0x18#64) ↦₆₄ᵣ saveIdentityPollAddr) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ saveIdFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ saveIdFutVt) ∗
          ((saveIdFutVt + 0x18#64) ↦₆₄ᵣ saveIdentityPollAddr) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = saveIdFutPtr ∧ s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x6c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = saveIdFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = saveIdFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  wp_steps_sync_518 ext saveIdentityPollAddr
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

theorem p4_seg1c_gen_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr saveIdFutPtr saveIdFutVt saveIdentityDropAddr w0
    w_3ec w_3f4 w_3fc w_404 u_2b0 u_2b8 u_2c0 u_2c8 : BitVec 64)
    (w_3e8 w_40c u_2d0 : BitVec 32)
    (hw0_ne_pend : w0 + 3#64 ≠ 0#64)
    (hdrop_nz : saveIdentityDropAddr ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x6c#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (lsProg_518 ext) saveIdentityDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ saveIdFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ saveIdFutVt) ∗
       (saveIdFutVt ↦₆₄ᵣ saveIdentityDropAddr) ∗
       stagingCellsAt (s.sp + 0x2b0#64) u_2b0 u_2b8 u_2c0 u_2c8 u_2d0 ∗
       pollCellsAt (s.sp + 0x3e0#64) w0 w_3e8 w_3ec w_3f4 w_3fc w_404 w_40c ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ saveIdFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ saveIdFutVt) ∗
          (saveIdFutVt ↦₆₄ᵣ saveIdentityDropAddr) ∗
          stagingCellsAt (s.sp + 0x2b0#64) w_3ec w_3f4 w_3fc w_404 w_40c ∗
          pollCellsAt (s.sp + 0x3e0#64) w0 w_3e8 w_3ec w_3f4 w_3fc w_404 w_40c ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = saveIdFutPtr ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = saveIdFutPtr ∧ s1.readReg64 .x22 = w_3e8.zeroExtend 64 ∧
        s1.readReg64 .x23 = saveIdFutVt ∧ s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x2ec#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hw0_beq : (w0 + 3#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_ne_pend
  have hdrop_beq : (saveIdentityDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp
  unfold stagingCellsAt pollCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  wp_steps_sync_518 ext saveIdentityDropAddr
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

theorem p4_seg1d_ok_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr msgPtr kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr
    saveIdFutPtr saveIdFutVt futSize futAlign u_2ac u_2b4 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2bc : BitVec 32)
    (hsize_nz : futSize ≠ 0#64)
    (hopk_ne2 : opkIdIsSome - 2#32 ≠ 0#32)
    (hpc : s.pc = (blkPl_518).base + 0x2ec#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = saveIdFutPtr)
    (hx23 : s.readReg64 .x23 = saveIdFutVt)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (lsProg_518 ext) kyberMarkUsedShimAddr s
      (((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0xd0#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗
       ((coroPtr + 0x29c#64) ↦₃₂ opkId) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
       ((coroPtr + 0x2ac#64) ↦₆₄ u_2ac) ∗
       ((coroPtr + 0x2b4#64) ↦₆₄ u_2b4) ∗
       ((coroPtr + 0x2bc#64) ↦₃₂ u_2bc) ∗
       ((kyberStoreVt + 0x28#64) ↦₆₄ᵣ kyberMarkUsedShimAddr) ∗
       ((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live saveIdFutPtr futSize.toNat futAlign.toNat ∗
       memRegion saveIdFutPtr futSize.toNat ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
          ((coroPtr + 0xd0#64) ↦₆₄ kyberStoreVt) ∗
          ((coroPtr + 0x298#64) ↦₆₄ (opkId ++ opkIdIsSome)) ∗
          ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
          ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
          ((coroPtr + 0x2ac#64) ↦₃₂ opkIdIsSome) ∗
          ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗
          ((coroPtr + 0x2b4#64) ↦₃₂ 1#32) ∗
          ((coroPtr + 0x2b8#64) ↦₃₂ kyberPreKeyId) ∗
          ((coroPtr + 0x2bc#64) ↦₃₂ signedPreKeyId) ∗
          ((kyberStoreVt + 0x28#64) ↦₆₄ᵣ kyberMarkUsedShimAddr) ∗
          ((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents futSize.toNat futAlign.toNat) st) s1 ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberStorePtr ∧
        s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧
        s1.readReg64 .x2 = signedPreKeyId.zeroExtend 64 ∧
        s1.readReg64 .x3 = msgPtr + 0xa8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x350#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  have hopk_beq : (opkIdIsSome - 2#32 == 0#32) = false := beq_eq_false_iff_ne.mpr hopk_ne2
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp
  have hpair_298 : ∀ R : SepProp,
      ((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗ (((coroPtr + 0x29c#64) ↦₃₂ opkId) ∗ R) =
      ((coroPtr + 0x298#64) ↦₆₄ (opkId ++ opkIdIsSome)) ∗ R := by
    intro R; rw [← sepConj_assoc]
    exact congrArg (· ∗ R) (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        pointsTo32_pair_eq (coroPtr + 0x298#64) opkIdIsSome opkId)
  rw [hpair_298]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = saveIdFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = saveIdFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xfffffffffffffffe#64 := hx28
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (saveIdFutPtr, futSize.toNat, futAlign.toNat, st)
  wp_steps_sync_518 ext kyberMarkUsedShimAddr
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  have hsplit_2ac :
      ((coroPtr + 684#64) ↦₆₄ (opkId ++ opkIdIsSome)) =
      ((coroPtr + 684#64) ↦₃₂ opkIdIsSome) ∗ ((coroPtr + 688#64) ↦₃₂ opkId) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      (pointsTo32_pair_eq (coroPtr + 684#64) opkIdIsSome opkId).symm
  have hsplit_2b4 :
      ((coroPtr + 692#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) =
      ((coroPtr + 692#64) ↦₃₂ 1#32) ∗ ((coroPtr + 696#64) ↦₃₂ kyberPreKeyId) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      (pointsTo32_pair_eq (coroPtr + 692#64) 1#32 kyberPreKeyId).symm
  refine ⟨by rw [hsplit_2ac, hsplit_2b4]; sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved, LibsignalBinary.Heap.AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

theorem p4_seg1d_err_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr saveIdFutPtr saveIdFutVt futSize futAlign w0 : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hw0_ne_ok : w0 + 2#64 ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x2ec#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = saveIdFutPtr)
    (hx23 : s.readReg64 .x23 = saveIdFutVt)
    (hx28 : s.readReg64 .x28 = w0) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x550#64) s
      (((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live saveIdFutPtr futSize.toNat futAlign.toNat ∗
       memRegion saveIdFutPtr futSize.toNat ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((saveIdFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((saveIdFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents futSize.toNat futAlign.toNat) st) s1 ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x8 = s.sp + 0x2b0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  have hw0_beq : (w0 + 2#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_ne_ok
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = saveIdFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = saveIdFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = w0 := hx28
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (saveIdFutPtr, futSize.toNat, futAlign.toNat, st)
  wp_steps_sync_518 ext ((blkPl_518).base + 0x550#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved, LibsignalBinary.Heap.AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdPlacedBudget
