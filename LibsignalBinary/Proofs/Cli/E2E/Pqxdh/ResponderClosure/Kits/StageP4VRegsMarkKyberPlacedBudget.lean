/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4MarkKyber
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4MarkKyberProof
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwindPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P4.2 `mark_kyber_pre_key_used` Segments

Budget-threaded `[LibsignalPlacement]` counterpart of `StageP4VRegsMarkKyberPlaced` on Block `518`
(`lsProg_518 ext`), threading `A.pool` and `rustCliDeallocBudgetSpec` across Substage P4.2
basic-block segments.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
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
  markKyberVtablesAt pollCellsAt stagingCellsAt
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

theorem p4_seg2a_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr ctxPtr kyberMarkUsedFutPtr kyberMarkUsedFutVt kyberMarkUsedPollAddr
    u_2c8 u_2d0 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x350#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = kyberMarkUsedFutPtr)
    (hx1 : s.readReg64 .x1 = kyberMarkUsedFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (lsProg_518 ext) kyberMarkUsedPollAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ u_2c8) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ u_2d0) ∗
       ((kyberMarkUsedFutVt + 0x18#64) ↦₆₄ᵣ kyberMarkUsedPollAddr) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ kyberMarkUsedFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ kyberMarkUsedFutVt) ∗
          ((kyberMarkUsedFutVt + 0x18#64) ↦₆₄ᵣ kyberMarkUsedPollAddr) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberMarkUsedFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x180#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = kyberMarkUsedFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = kyberMarkUsedFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  wp_steps_sync_518 ext kyberMarkUsedPollAddr
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

theorem p4_seg2b_gen_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr kyberMarkUsedFutPtr kyberMarkUsedFutVt kyberMarkUsedDropAddr w0
    o2 o3 o4 o5 u_2e0 u_2e8 u_2f0 u_2f8 : BitVec 64)
    (o1 o6 u_300 : BitVec 32)
    (hw0_ne_pend : w0 + 3#64 ≠ 0#64)
    (hdrop_nz : kyberMarkUsedDropAddr ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x180#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (lsProg_518 ext) kyberMarkUsedDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ kyberMarkUsedFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ kyberMarkUsedFutVt) ∗
       (kyberMarkUsedFutVt ↦₆₄ᵣ kyberMarkUsedDropAddr) ∗
       stagingCellsAt (s.sp + 0x2e0#64) u_2e0 u_2e8 u_2f0 u_2f8 u_300 ∗
       pollCellsAt (s.sp + 0x3e0#64) w0 o1 o2 o3 o4 o5 o6 ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ kyberMarkUsedFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ kyberMarkUsedFutVt) ∗
          (kyberMarkUsedFutVt ↦₆₄ᵣ kyberMarkUsedDropAddr) ∗
          stagingCellsAt (s.sp + 0x2e0#64) o2 o3 o4 o5 o6 ∗
          pollCellsAt (s.sp + 0x3e0#64) w0 o1 o2 o3 o4 o5 o6 ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberMarkUsedFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = kyberMarkUsedFutPtr ∧
        s1.readReg64 .x22 = o1.zeroExtend 64 ∧
        s1.readReg64 .x23 = kyberMarkUsedFutVt ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x38c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hw0_beq : (w0 + 3#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_ne_pend
  have hdrop_beq : (kyberMarkUsedDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp
  unfold stagingCellsAt pollCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  wp_steps_sync_518 ext kyberMarkUsedDropAddr
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

theorem p4_seg2c_some_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr preKeyStorePtr preKeyStoreVt removePreKeyShimAddr
    kyberMarkUsedFutPtr kyberMarkUsedFutVt futSize futAlign : BitVec 64)
    (opkId : BitVec 32)
    (hsize_nz : futSize ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x38c#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = kyberMarkUsedFutPtr)
    (hx23 : s.readReg64 .x23 = kyberMarkUsedFutVt)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (lsProg_518 ext) removePreKeyShimAddr s
      (((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
       ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗
       ((preKeyStoreVt + 0x28#64) ↦₆₄ᵣ removePreKeyShimAddr) ∗
       ((kyberMarkUsedFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((kyberMarkUsedFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live kyberMarkUsedFutPtr futSize.toNat futAlign.toNat ∗
       memRegion kyberMarkUsedFutPtr futSize.toNat ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
          ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
          ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
          ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗
          ((preKeyStoreVt + 0x28#64) ↦₆₄ᵣ removePreKeyShimAddr) ∗
          ((kyberMarkUsedFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((kyberMarkUsedFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents futSize.toNat futAlign.toNat) st) s1 ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = preKeyStorePtr ∧
        s1.readReg64 .x1 = opkId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x3c0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = kyberMarkUsedFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = kyberMarkUsedFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xfffffffffffffffe#64 := hx28
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (kyberMarkUsedFutPtr, futSize.toNat, futAlign.toNat, st)
  wp_steps_sync_518 ext removePreKeyShimAddr
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

theorem p4_seg2c_none_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr kyberMarkUsedFutPtr kyberMarkUsedFutVt futSize futAlign : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x38c#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = kyberMarkUsedFutPtr)
    (hx23 : s.readReg64 .x23 = kyberMarkUsedFutVt)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x3cc#64) s
      (((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗
       ((kyberMarkUsedFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((kyberMarkUsedFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live kyberMarkUsedFutPtr futSize.toNat futAlign.toNat ∗
       memRegion kyberMarkUsedFutPtr futSize.toNat ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗
          ((kyberMarkUsedFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((kyberMarkUsedFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents futSize.toNat futAlign.toNat) st) s1 ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = kyberMarkUsedFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = kyberMarkUsedFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xfffffffffffffffe#64 := hx28
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (kyberMarkUsedFutPtr, futSize.toNat, futAlign.toNat, st)
  wp_steps_sync_518 ext ((blkPl_518).base + 0x3cc#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved, LibsignalBinary.Heap.AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem p4_seg2c_err_vregs_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr kyberMarkUsedFutPtr kyberMarkUsedFutVt futSize futAlign w0 : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hw0_ne_ok : w0 + 2#64 ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x38c#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = kyberMarkUsedFutPtr)
    (hx23 : s.readReg64 .x23 = kyberMarkUsedFutVt)
    (hx28 : s.readReg64 .x28 = w0) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x550#64) s
      (((kyberMarkUsedFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((kyberMarkUsedFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live kyberMarkUsedFutPtr futSize.toNat futAlign.toNat ∗
       memRegion kyberMarkUsedFutPtr futSize.toNat ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((kyberMarkUsedFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((kyberMarkUsedFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents futSize.toNat futAlign.toNat) st) s1 ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x8 = s.sp + 0x2e0#64 ∧
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
  have hx21' : s.readReg64 (Reg.gpr 21#5) = kyberMarkUsedFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = kyberMarkUsedFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = w0 := hx28
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (kyberMarkUsedFutPtr, futSize.toNat, futAlign.toNat, st)
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

/-! ## Placed vtable introduction -/

theorem markKyberVtablesAt_placed_intro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64} (hvt : KyberPreKeyVtablesPlacedOk kpkKit)
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ markKyberVtablesAt kpkKit ∗ P :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.markKyberVtablesAt_placed_intro
    hvt hro hP

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberPlacedBudget
