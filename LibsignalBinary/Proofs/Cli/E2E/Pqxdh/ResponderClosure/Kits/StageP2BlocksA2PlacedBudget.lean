/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA2Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P2 Basic Blocks — Substage P2.3

`RustCliAllocBudget M` / `VmPreserved` basic-block lemmas for Substage P2.3 (`+0x1460 → +0x0d5c`)
on Block `518` (`stageP1ProgPlaced ext`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA2PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.LibsignalPublicApi.StoreKit
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
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
  try dsimp only [lsRustDeallocSym, lsRustAllocSym, lsRustNoAllocShimSym]
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm])
    (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## Substage P2.3 Basic Blocks (`+0x1460 -> +0xd5c`) -/

set_option maxHeartbeats 800000 in
theorem p2_seg3a_ext_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State)
    (coroPtr ctxPtr kyberFutPtr kyberFutVt kyberPollAddr u_4f8 u_500 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x1460#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = kyberFutPtr)
    (hx1 : s.readReg64 .x1 = kyberFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (stageP1ProgPlaced ext) kyberPollAddr s
      (((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((kyberFutVt + 0x18#64) ↦₆₄ᵣ kyberPollAddr) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ kyberFutVt) ∗
          ((kyberFutVt + 0x18#64) ↦₆₄ᵣ kyberPollAddr) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x998#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = kyberFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = kyberFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  wp_steps_sync_518 ext kyberPollAddr
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
theorem p2_seg3b_gen_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr kyberFutPtr kyberFutVt kyberDropAddr
    kyberPubCap kyberPubPtr kyberSecCap kyberSecPtr kyberSigCap kyberSigPtr
    v_98 v_a0 v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x998#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_ne_neg2 : kyberPubCap ≠ 0xfffffffffffffffe#64)
    (hdrop_nz : kyberDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (stageP1ProgPlaced ext) kyberDropAddr s
      (preKeyRecordOut64At (s.sp + 0x3e0#64)
         kyberPubCap kyberPubPtr 1569#64 kyberSecCap kyberSecPtr 3169#64 kyberSigCap kyberSigPtr ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗ ((coroPtr + 0x500#64) ↦₆₄ kyberFutVt) ∗
       ((kyberFutVt + 0x0#64) ↦₆₄ᵣ kyberDropAddr) ∗ ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0x3e0#64)
            kyberPubCap kyberPubPtr 1569#64 kyberSecCap kyberSecPtr 3169#64 kyberSigCap kyberSigPtr ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗ ((coroPtr + 0x500#64) ↦₆₄ kyberFutVt) ∗
          ((kyberFutVt + 0x0#64) ↦₆₄ᵣ kyberDropAddr) ∗ ((s.sp + 0x90#64) ↦₆₄ kyberSigCap) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ kyberSecCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = kyberFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = kyberSigPtr ∧
        s1.readReg64 .x21 = kyberFutPtr ∧ s1.readReg64 .x22 = 1569#64 ∧
        s1.readReg64 .x23 = kyberPubPtr ∧ s1.readReg64 .x24 = kyberFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = kyberPubCap ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xc3c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_ne2 : ConditionHolds CondCode.NE (addsPState64 kyberPubCap 2#64) = true :=
    p2_cond_ne_adds64_of_ne_neg2 hpub_ne_neg2
  have hcond_eq2 : ConditionHolds CondCode.EQ (addsPState64 kyberPubCap 2#64) = false := by
    rw [conditionHolds_eq_addsPState64]; exact beq_eq_false_iff_ne.mpr (by bv_omega)
  have hdrop_beq : (kyberDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  dsimp only [preKeyRecordOut64At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_518 ext kyberDropAddr
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨?_,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩
  try simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 1200000 in
theorem p2_seg3d1_sig0_hooks_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (st : M.σ) (s : State)
    (coroPtr msgPtr kyberPubCap kyberPubPtr kyberSecCap kyberSecPtr kyberSigPtr
    pkBuf skBuf kyberCtCap v_98 v_a0
    u_3d8 u_3e0 u_3e8 u_3f0 : BitVec 64)
    (b_4f1 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0xc74#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_nz : kyberPubCap ≠ 0#64)
    (hsec_nz : kyberSecCap ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = kyberSigPtr)
    (hx23 : s.readReg64 .x23 = kyberPubPtr)
    (hx28 : s.readReg64 .x28 = kyberPubCap) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0xd04#64) s
      (((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗ ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗ ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ kyberSecCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr) ∗
       A.live kyberPubPtr kyberPubCap.toNat 1 ∗ memRegion kyberPubPtr kyberPubCap.toNat ∗
       A.live kyberSecPtr kyberSecCap.toNat 1 ∗ memRegion kyberSecPtr kyberSecCap.toNat ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗ ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗ ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗ ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ kyberSecCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents kyberPubCap.toNat 1 ++
              rustDeallocEvents kyberSecCap.toNat 1) st) s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = 21#64 ∧
        s1.readReg64 .x1 = 1#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = msgPtr + 0x90#64 ∧ s1.readReg64 .x22 = kyberCtCap ∧
        s1.readReg64 .x23 = v_a0 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hshim := hH.shim
  have hpub_beq : (kyberPubCap == 0#64) = false := beq_eq_false_iff_ne.mpr hpub_nz
  have hsec_beq : (kyberSecCap == 0#64) = false := beq_eq_false_iff_ne.mpr hsec_nz
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym, lsRustNoAllocShimSym]
    at hdealloc hshim hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = kyberSigPtr := hx20
  have hx23' : s.readReg64 (Reg.gpr 23#5) = kyberPubPtr := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = kyberPubCap := hx28
  wp_steps_sync_518 ext (lsρ lsRustDeallocSym)
  wp_call hdealloc (kyberPubPtr, kyberPubCap.toNat, 1, st)
  try simp only [wp_norm, arm64_norm] at hsp_sf
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf])
  wp_steps_sync_518 ext (lsρ lsRustDeallocSym)
  wp_call hdealloc (kyberSecPtr, kyberSecCap.toNat, 1,
    M.stepEvents (rustDeallocEvents kyberPubCap.toNat 1) st)
  try simp only [wp_norm, arm64_norm, hsp_sf] at hsp_sf_1
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1, ← M.stepEvents_append])
  wp_steps_sync_518 ext (lsρ lsRustNoAllocShimSym)
  wp_call hshim ()
  try simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1] at hsp_sf_2
  refine ProofLib.SepWP.transport_budgetPool ?_ (by sep_focus) (hnext := ?_)
  · assumption
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1, hsp_sf_2])
  wp_steps_sync_518 ext ((blkPl_518).base + 0xd04#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨?_,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved, LibsignalBinary.Heap.AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩
  try simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1, hsp_sf_2, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

abbrev p2_seg3d1_sig0_gen_placed_wp := @p2_seg3d1_sig0_hooks_placed_wp

set_option maxHeartbeats 1200000 in
theorem p2_seg3d1_sigNz_hooks_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (st : M.σ) (s : State)
    (coroPtr msgPtr kyberPubCap kyberPubPtr kyberSecCap kyberSecPtr kyberSigCap kyberSigPtr
    pkBuf skBuf kyberCtCap v_98 v_a0
    u_3d8 u_3e0 u_3e8 u_3f0 : BitVec 64)
    (b_4f1 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0xc74#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_nz : kyberPubCap ≠ 0#64)
    (hsec_nz : kyberSecCap ≠ 0#64)
    (hsig_nz : kyberSigCap ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = kyberSigPtr)
    (hx23 : s.readReg64 .x23 = kyberPubPtr)
    (hx28 : s.readReg64 .x28 = kyberPubCap) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0xd04#64) s
      (((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗ ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗ ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ ((s.sp + 0x90#64) ↦₆₄ kyberSigCap) ∗
       ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ kyberSecCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr) ∗
       A.live kyberPubPtr kyberPubCap.toNat 1 ∗ memRegion kyberPubPtr kyberPubCap.toNat ∗
       A.live kyberSecPtr kyberSecCap.toNat 1 ∗ memRegion kyberSecPtr kyberSecCap.toNat ∗
       A.live kyberSigPtr kyberSigCap.toNat 1 ∗ memRegion kyberSigPtr kyberSigCap.toNat ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗ ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗ ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗ ((s.sp + 0x90#64) ↦₆₄ kyberSigCap) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ kyberSecCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents kyberPubCap.toNat 1 ++
              rustDeallocEvents kyberSecCap.toNat 1 ++
              rustDeallocEvents kyberSigCap.toNat 1) st) s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = 21#64 ∧
        s1.readReg64 .x1 = 1#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = msgPtr + 0x90#64 ∧ s1.readReg64 .x22 = kyberCtCap ∧
        s1.readReg64 .x23 = v_a0 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hshim := hH.shim
  have hpub_beq : (kyberPubCap == 0#64) = false := beq_eq_false_iff_ne.mpr hpub_nz
  have hsec_beq : (kyberSecCap == 0#64) = false := beq_eq_false_iff_ne.mpr hsec_nz
  have hsig_beq : (kyberSigCap == 0#64) = false := beq_eq_false_iff_ne.mpr hsig_nz
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym, lsRustNoAllocShimSym]
    at hdealloc hshim hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = kyberSigPtr := hx20
  have hx23' : s.readReg64 (Reg.gpr 23#5) = kyberPubPtr := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = kyberPubCap := hx28
  wp_steps_sync_518 ext (lsρ lsRustDeallocSym)
  wp_call hdealloc (kyberPubPtr, kyberPubCap.toNat, 1, st)
  try simp only [wp_norm, arm64_norm] at hsp_sf
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf])
  wp_steps_sync_518 ext (lsρ lsRustDeallocSym)
  wp_call hdealloc (kyberSecPtr, kyberSecCap.toNat, 1,
    M.stepEvents (rustDeallocEvents kyberPubCap.toNat 1) st)
  try simp only [wp_norm, arm64_norm, hsp_sf] at hsp_sf_1
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1, ← M.stepEvents_append])
  wp_steps_sync_518 ext (lsρ lsRustDeallocSym)
  wp_call hdealloc (kyberSigPtr, kyberSigCap.toNat, 1,
    M.stepEvents (rustDeallocEvents kyberPubCap.toNat 1 ++
      rustDeallocEvents kyberSecCap.toNat 1) st)
  try simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1] at hsp_sf_2
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1, hsp_sf_2, ← M.stepEvents_append])
  wp_steps_sync_518 ext (lsρ lsRustNoAllocShimSym)
  wp_call hshim ()
  try simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1, hsp_sf_2] at hsp_sf_3
  refine ProofLib.SepWP.transport_budgetPool ?_ (by sep_focus) (hnext := ?_)
  · assumption
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1, hsp_sf_2, hsp_sf_3])
  wp_steps_sync_518 ext ((blkPl_518).base + 0xd04#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨?_,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved, LibsignalBinary.Heap.AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩
  try simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1, hsp_sf_2, hsp_sf_3, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

abbrev p2_seg3d1_sigNz_gen_placed_wp := @p2_seg3d1_sigNz_hooks_placed_wp

set_option maxHeartbeats 800000 in
theorem p2_seg3c_hooks_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (st : M.σ) (s : State)
    (coroPtr ctxPtr kyberFutPtr kyberFutVt kyberPubCap kyberPubPtr kyberSecPtr kyberSigPtr
    u_c0 : BitVec 64)
    (kyberBoxSize : Nat)
    (hpc : s.pc = stageP1EntryPlaced + 0xc3c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_ne_neg1 : kyberPubCap ≠ 0xffffffffffffffff#64)
    (hbs_nz : BitVec.ofNat 64 kyberBoxSize ≠ 0#64)
    (hbs_lt : kyberBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = kyberSigPtr)
    (hx21 : s.readReg64 .x21 = kyberFutPtr)
    (hx22 : s.readReg64 .x22 = 1569#64)
    (hx23 : s.readReg64 .x23 = kyberPubPtr)
    (hx24 : s.readReg64 .x24 = kyberFutVt)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = kyberPubCap) :
    SepWP (stageP1ProgPlaced ext)
      (libsignalSessionLib.resolve lsmpl
        "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private") s
      (((kyberFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 kyberBoxSize) ∗
       ((kyberFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live kyberFutPtr kyberBoxSize 8 ∗
       memRegion kyberFutPtr kyberBoxSize ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr))
      (fun s1 P_f =>
        (P_f ⊢
          ((kyberFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 kyberBoxSize) ∗
          ((kyberFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents kyberBoxSize 8) st) s1 ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberPubPtr ∧
        s1.readReg64 .x1 = 1569#64 ∧
        s1.readReg64 .x2 = kyberSecPtr ∧
        s1.readReg64 .x3 = 3169#64 ∧
        s1.readReg64 .x8 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = kyberSigPtr ∧
        s1.readReg64 .x22 = 1569#64 ∧
        s1.readReg64 .x23 = kyberPubPtr ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = kyberPubCap ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xc74#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hcond_eq1 : ConditionHolds CondCode.EQ (addsPState64 kyberPubCap 1#64) = false :=
    p2_cond_eq_adds64_of_ne_neg1 hpub_ne_neg1
  have hcond_ne1 : ConditionHolds CondCode.NE (addsPState64 kyberPubCap 1#64) = true := by
    rw [conditionHolds_ne_addsPState64]; exact bne_iff_ne.mpr (by bv_omega)
  have hbs_beq : (BitVec.ofNat 64 kyberBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 kyberBoxSize).toNat = kyberBoxSize := Nat.mod_eq_of_lt hbs_lt
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = kyberSigPtr := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = kyberFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = 1569#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = kyberPubPtr := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = kyberFutVt := hx24
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = kyberPubCap := hx28
  wp_steps_sync_518 ext (lsρ lsRustDeallocSym)
  wp_call hdealloc (kyberFutPtr, kyberBoxSize, 8, st)
  try simp only [wp_norm, arm64_norm] at hsp_sf
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf])
  wp_steps_sync_518 ext
    (libsignalSessionLib.resolve lsmpl
      "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private")
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨?_,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved, LibsignalBinary.Heap.AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩
  try simp only [wp_norm, arm64_norm, hsp_sf, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

abbrev p2_seg3c_gen_placed_wp := @p2_seg3c_hooks_placed_wp

set_option maxHeartbeats 800000 in
theorem p2_seg3d2c_ext_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr errStrPtr kyberCtCap ro13 u13 u_3e0 u_3e8 u_3f8 : BitVec 64)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hpc : s.pc = stageP1EntryPlaced + 0xd38#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = errStrPtr)
    (hx8 : s.readReg64 .x8 = ro13)
    (hx9 : s.readReg64 .x9 = 0x8000000000000006#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = kyberCtCap) :
    SepWP (stageP1ProgPlaced ext)
      (libsignalSessionLib.resolve lsmpl
        "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]") s
      (((errStrPtr + 13#64) ↦₆₄ u13) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ u_3e8) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((errStrPtr + 13#64) ↦₆₄ ro13) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ 21#64) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ 21#64) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0x8000000000000018#64 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = kyberCtCap ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xd5c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hkyber_beq : (kyberCtCap == 0#64) = false := beq_eq_false_iff_ne.mpr hkyber_nz
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = errStrPtr := hx0
  have hx8' : s.readReg64 (Reg.gpr 8#5) = ro13 := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000006#64 := hx9
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = kyberCtCap := hx22
  wp_steps_sync_518 ext
    (libsignalSessionLib.resolve lsmpl
      "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")
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
theorem p2_seg3d2a_ext_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr errStrPtr ro0 ro8 : BitVec 64)
    (herr_nz : errStrPtr ≠ 0#64)
    (hpc : s.pc = stageP1EntryPlaced + 0xd08#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = errStrPtr)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (stageP1ProgPlaced ext)
      (stageP1EntryPlaced + 0xd1c#64) s
      (((lsρ "libsignal_cli_handshake:.rodata..Lanon.89") ↦₆₄ᵣ ro0) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.89" + 8#64) ↦₆₄ᵣ ro8) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((lsρ "libsignal_cli_handshake:.rodata..Lanon.89") ↦₆₄ᵣ ro0) ∗
          ((lsρ "libsignal_cli_handshake:.rodata..Lanon.89" + 8#64) ↦₆₄ᵣ ro8) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = errStrPtr ∧
        s1.readReg64 .x8 = lsρ "libsignal_cli_handshake:.rodata..Lanon.89" ∧
        s1.readReg64 .x9 = 3#64 ∧
        s1.readVReg128 0#5 = ro8 ++ ro0 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have herr_beq : (errStrPtr == 0#64) = false := beq_eq_false_iff_ne.mpr herr_nz
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsρ] at hpc ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = errStrPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext ((blkPl_518).base + 0xd1c#64)
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
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p2_seg3d2b_ext_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr errStrPtr ro0 ro8 ro13 u0 u8 u_3f0 : BitVec 64)
    (b_400 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0xd1c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = errStrPtr)
    (hx8 : s.readReg64 .x8 = lsρ "libsignal_cli_handshake:.rodata..Lanon.89")
    (hx9 : s.readReg64 .x9 = 3#64)
    (hq0 : s.readVReg128 0#5 = ro8 ++ ro0)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (stageP1ProgPlaced ext)
      (stageP1EntryPlaced + 0xd38#64) s
      (((lsρ "libsignal_cli_handshake:.rodata..Lanon.89" + 13#64) ↦₆₄ᵣ ro13) ∗
       (errStrPtr ↦₆₄ u0) ∗
       ((errStrPtr + 8#64) ↦₆₄ u8) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((s.sp + 0x400#64) ↦₈ b_400) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((lsρ "libsignal_cli_handshake:.rodata..Lanon.89" + 13#64) ↦₆₄ᵣ ro13) ∗
          (errStrPtr ↦₆₄ ro0) ∗
          ((errStrPtr + 8#64) ↦₆₄ ro8) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
          ((s.sp + 0x400#64) ↦₈ 3#8) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = errStrPtr ∧
        s1.readReg64 .x8 = ro13 ∧
        s1.readReg64 .x9 = 0x8000000000000006#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsρ] at hpc hx8 ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = errStrPtr := hx0
  have hx8' : s.readReg64 (Reg.gpr 8#5) = lsmpl.ρ "libsignal_cli_handshake:.rodata..Lanon.89" := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = 3#64 := hx9
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hq0_lo : (s.readVReg128 0#5).extractLsb' 0 64 = ro0 := by rw [hq0]; clear * -; bv_slice
  have hq0_hi : (s.readVReg128 0#5).extractLsb' 64 64 = ro8 := by rw [hq0]; clear * -; bv_slice
  wp_steps_sync_518 ext ((blkPl_518).base + 0xd38#64)
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

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA2PlacedBudget
