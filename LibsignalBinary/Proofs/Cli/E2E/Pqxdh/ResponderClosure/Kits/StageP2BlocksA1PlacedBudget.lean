/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA1
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P2 Basic Blocks — Substages P2.1 and P2.2

`RustCliAllocBudget M` / `VmPreserved` basic-block lemmas (`+0x0868 → +0x145c`) for Substages P2.1
and P2.2 on Block `518` (`stageP1ProgPlaced ext`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA1PlacedBudget

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
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.CliHandshake.RespClosurePlaced
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpec rustDeallocEvents
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
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## 1. Substage P2.1 Basic Blocks (`+0x868 -> spkLoadShimAddr`) -/

set_option maxHeartbeats 800000 in
theorem p2_seg1a_ext_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64)
    (b_4f1 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt) :
    SepWP (stageP1ProgPlaced ext) (lsmpl.base 205) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = msgPtr + 0xa8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = 4#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x8a0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx8' : s.readReg64 (Reg.gpr 8#5) = kyberStorePtr := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = msgPtr := hx9
  have hx10' : s.readReg64 (Reg.gpr 10#5) = kyberStoreVt := hx10
  have hx11' : s.readReg64 (Reg.gpr 11#5) = preKeyStorePtr := hx11
  have hx12' : s.readReg64 (Reg.gpr 12#5) = remoteAddrPtr := hx12
  have hx13' : s.readReg64 (Reg.gpr 13#5) = preKeyStoreVt := hx13
  have hx14' : s.readReg64 (Reg.gpr 14#5) = localAddrPtr := hx14
  have hx15' : s.readReg64 (Reg.gpr 15#5) = idStorePtr := hx15
  have hx16' : s.readReg64 (Reg.gpr 16#5) = idStoreVt := hx16
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = coroPtr + 0xe0#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps_sync_518 ext (lsmpl.base 205)
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
    by simp_all [wp_norm, arm64_norm]⟩
  dsimp only [processPrekeyActive10At]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
theorem p2_seg1b_ext_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr serPtr spkStorePtr spkStoreVt : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x8a0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = serPtr)
    (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx25 : s.readReg64 .x25 = 4#64) :
    SepWP (stageP1ProgPlaced ext)
      (lsmpl.base 50) s
      (A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = 4#64 ∧
        s1.readReg64 .x2 = serPtr ∧
        s1.readReg64 .x3 = 33#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = 4#64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x8c0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = serPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = 33#64 := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = coroPtr + 0xe0#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 4#64 := hx25
  wp_steps_sync_518 ext (lsmpl.base 50)
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
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 1000000 in
theorem p2_seg1c_hooks_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (st : M.σ) (s : State) (coroPtr msgPtr serPtr spkStorePtr spkStoreVt spkLoadShimAddr : BitVec 64)
    (spkId : BitVec 32)
    (hpc : s.pc = stageP1EntryPlaced + 0x8c0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = serPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (stageP1ProgPlaced ext) spkLoadShimAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
       A.live serPtr 33 1 ∗ memRegion serPtr 33 ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗ ((spkStoreVt + 0x18#64) ↦₆₄ᵣ spkLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents 33 1) st) s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
          ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗ ((spkStoreVt + 0x18#64) ↦₆₄ᵣ spkLoadShimAddr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = spkStorePtr ∧
        s1.readReg64 .x1 = spkId.zeroExtend 64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧ s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = 0#64 ∧ s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧ s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xf14#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = serPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = 33#64 := hx26
  wp_steps_sync_518 ext (lsρ lsRustDeallocSym)
  wp_call hdealloc (serPtr, 33, 1, st)
  try simp only [wp_norm, arm64_norm] at hsp_sf
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf])
  wp_steps_sync_518 ext spkLoadShimAddr
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
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩
  simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

abbrev p2_seg1c_ext_placed_wp := @p2_seg1c_hooks_placed_wp

/-! ## 2. Substage P2.2 Basic Blocks (`+0xf14 -> kyberLoadShimAddr`) -/

set_option maxHeartbeats 800000 in
theorem p2_seg2a_ext_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr ctxPtr spkFutPtr spkFutVt spkPollAddr
    v_98 v_a0 v_b0 u_4f8 u_500 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0xf14#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = spkFutPtr)
    (hx1 : s.readReg64 .x1 = spkFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (stageP1ProgPlaced ext) spkPollAddr s
      (((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((spkFutVt + 0x18#64) ↦₆₄ᵣ spkPollAddr) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗ ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
          ((spkFutVt + 0x18#64) ↦₆₄ᵣ spkPollAddr) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = spkFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧ s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = v_a0 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧ s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xf38#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = spkFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = spkFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext spkPollAddr
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
theorem p2_seg2b_gen_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr spkFutPtr spkFutVt spkDropAddr
    spkPubCap spkPubPtr spkPrivCap spkPrivPtr spkSigCap spkSigPtr
    v_98 v_a0 v_b0 u_90 u_98 u_a0 u_b0 u_b8 u_d0 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0xf38#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_ne_neg2 : spkPubCap ≠ 0xfffffffffffffffe#64)
    (hdrop_nz : spkDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (stageP1ProgPlaced ext) spkDropAddr s
      (preKeyRecordOut64At (s.sp + 0x3e0#64)
         spkPubCap spkPubPtr 33#64 spkPrivCap spkPrivPtr 32#64 spkSigCap spkSigPtr ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗ ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
       ((spkFutVt + 0x0#64) ↦₆₄ᵣ spkDropAddr) ∗ ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0x3e0#64)
            spkPubCap spkPubPtr 33#64 spkPrivCap spkPrivPtr 32#64 spkSigCap spkSigPtr ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗ ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
          ((spkFutVt + 0x0#64) ↦₆₄ᵣ spkDropAddr) ∗ ((s.sp + 0x90#64) ↦₆₄ spkSigCap) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗
          ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = spkFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x21 = spkFutPtr ∧ s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = 33#64 ∧ s1.readReg64 .x24 = spkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = 32#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = spkPubCap ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xf98#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_ne2 : ConditionHolds CondCode.NE (addsPState64 spkPubCap 2#64) = true :=
    p2_cond_ne_adds64_of_ne_neg2 hpub_ne_neg2
  have hcond_eq2 : ConditionHolds CondCode.EQ (addsPState64 spkPubCap 2#64) = false := by
    rw [conditionHolds_eq_addsPState64]; exact beq_eq_false_iff_ne.mpr (by bv_omega)
  have hdrop_beq : (spkDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
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
  wp_steps_sync_518 ext spkDropAddr
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
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 1000000 in
theorem p2_seg2c_hooks_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (st : M.σ) (s : State)
    (coroPtr spkFutPtr spkFutVt spkPubCap spkPubPtr spkPrivPtr spkSigPtr : BitVec 64)
    (spkBoxSize : Nat)
    (hpc : s.pc = stageP1EntryPlaced + 0xf98#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_ne_neg1 : spkPubCap ≠ 0xffffffffffffffff#64)
    (hbs_nz : BitVec.ofNat 64 spkBoxSize ≠ 0#64)
    (hbs_lt : spkBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx21 : s.readReg64 .x21 = spkFutPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr)
    (hx23 : s.readReg64 .x23 = 33#64)
    (hx24 : s.readReg64 .x24 = spkFutVt)
    (hx26 : s.readReg64 .x26 = 32#64)
    (hx28 : s.readReg64 .x28 = spkPubCap) :
    SepWP (stageP1ProgPlaced ext)
      (lsmpl.base 112) s
      (((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
       ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live spkFutPtr spkBoxSize 8 ∗ memRegion spkFutPtr spkBoxSize ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗ ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr))
      (fun s1 P_f =>
        (P_f ⊢
          ((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
          ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents spkBoxSize 8) st) s1 ∗
          stackAt s.sp allocHookStack ∗ ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = spkPubPtr ∧
        s1.readReg64 .x1 = 33#64 ∧ s1.readReg64 .x2 = spkPrivPtr ∧
        s1.readReg64 .x3 = 32#64 ∧ s1.readReg64 .x8 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x22 = spkPubPtr ∧ s1.readReg64 .x23 = 33#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = 32#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = spkPubCap ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xfcc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hcond_eq1 : ConditionHolds CondCode.EQ (addsPState64 spkPubCap 1#64) = false :=
    p2_cond_eq_adds64_of_ne_neg1 hpub_ne_neg1
  have hcond_ne1 : ConditionHolds CondCode.NE (addsPState64 spkPubCap 1#64) = true := by
    rw [conditionHolds_ne_addsPState64]; exact bne_iff_ne.mpr (by bv_omega)
  have hbs_beq : (BitVec.ofNat 64 spkBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 spkBoxSize).toNat = spkBoxSize := Nat.mod_eq_of_lt hbs_lt
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = spkSigPtr := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = spkFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkPubPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 33#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkFutVt := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = 32#64 := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = spkPubCap := hx28
  wp_steps_sync_518 ext (lsρ lsRustDeallocSym)
  wp_call hdealloc (spkFutPtr, spkBoxSize, 8, st)
  try simp only [wp_norm, arm64_norm] at hsp_sf
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf])
  wp_steps_sync_518 ext (lsmpl.base 112)
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
  simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

abbrev p2_seg2c_gen_placed_wp := @p2_seg2c_hooks_placed_wp

set_option maxHeartbeats 1200000 in
theorem p2_seg2d_sig0_hooks_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (st : M.σ) (s : State) (coroPtr msgPtr spkPubCap spkPubPtr spkPrivCap spkPrivPtr spkSigPtr
    kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr
    v_a0 v_b0 u_3e0 : BitVec 64)
    (kyberPreKeyId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6
     c0 c1 c2 c3 c4 c5 c6 c63 b_3e8 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6
     cw0 cw1 cw2 cw3 cw4 cw5 cw6 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0xfcc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_nz : spkPubCap ≠ 0#64)
    (hpriv_nz : spkPrivCap ≠ 0#64)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr)
    (hx28 : s.readReg64 .x28 = spkPubCap) :
    SepWP (stageP1ProgPlaced ext) kyberLoadShimAddr s
      (((s.sp + 0xa90#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x930#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       keyPair64UnalignedAt
         (coroPtr + 0x398#64) c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 ∗
       ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗ ((s.sp + 0x3e8#64) ↦₈ b_3e8) ∗
       A.live spkPubPtr spkPubCap.toNat 1 ∗ memRegion spkPubPtr spkPubCap.toNat ∗
       A.live spkPrivPtr spkPrivCap.toNat 1 ∗ memRegion spkPrivPtr spkPrivCap.toNat ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗ ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗
          keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ w6) ∗ ((s.sp + 0x3e8#64) ↦₈ b63) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents spkPubCap.toNat 1 ++
              rustDeallocEvents spkPrivCap.toNat 1) st) s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
          ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗ ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = kyberStorePtr ∧
        s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧ s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x22 = spkPubPtr ∧ s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x1460#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hpub_beq : (spkPubCap == 0#64) = false := beq_eq_false_iff_ne.mpr hpub_nz
  have hpriv_beq : (spkPrivCap == 0#64) = false := beq_eq_false_iff_ne.mpr hpriv_nz
  have hkyber_beq : (kyberCtCap == 0#64) = false := beq_eq_false_iff_ne.mpr hkyber_nz
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = spkSigPtr := hx20
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkPubPtr := hx22
  have hx28' : s.readReg64 (Reg.gpr 28#5) = spkPubCap := hx28
  dsimp only [keyPair64UnalignedAt, bytes7At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_518 ext (lsρ lsRustDeallocSym)
  wp_call hdealloc (spkPubPtr, spkPubCap.toNat, 1, st)
  try simp only [wp_norm, arm64_norm] at hsp_sf
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf])
  wp_steps_sync_518 ext (lsρ lsRustDeallocSym)
  wp_call hdealloc (spkPrivPtr, spkPrivCap.toNat, 1,
    M.stepEvents (rustDeallocEvents spkPubCap.toNat 1) st)
  try simp only [wp_norm, arm64_norm, hsp_sf] at hsp_sf_1
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1, ← M.stepEvents_append])
  wp_steps_sync_518 ext kyberLoadShimAddr
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
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩
  simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

abbrev p2_seg2d_sig0_gen_placed_wp := @p2_seg2d_sig0_hooks_placed_wp

set_option maxHeartbeats 1200000 in
theorem p2_seg2d_sigNz_hooks_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (st : M.σ) (s : State) (coroPtr msgPtr spkPubCap spkPubPtr spkPrivCap spkPrivPtr spkSigCap spkSigPtr
    kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr
    v_a0 v_b0 u_3e0 : BitVec 64)
    (kyberPreKeyId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6
     c0 c1 c2 c3 c4 c5 c6 c63 b_3e8 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6
     cw0 cw1 cw2 cw3 cw4 cw5 cw6 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0xfcc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_nz : spkPubCap ≠ 0#64)
    (hpriv_nz : spkPrivCap ≠ 0#64)
    (hsig_nz : spkSigCap ≠ 0#64)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr)
    (hx28 : s.readReg64 .x28 = spkPubCap) :
    SepWP (stageP1ProgPlaced ext) kyberLoadShimAddr s
      (((s.sp + 0xa90#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x930#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       keyPair64UnalignedAt
         (coroPtr + 0x398#64) c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 ∗
       ((s.sp + 0x90#64) ↦₆₄ spkSigCap) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗ ((s.sp + 0x3e8#64) ↦₈ b_3e8) ∗
       A.live spkPubPtr spkPubCap.toNat 1 ∗ memRegion spkPubPtr spkPubCap.toNat ∗
       A.live spkPrivPtr spkPrivCap.toNat 1 ∗ memRegion spkPrivPtr spkPrivCap.toNat ∗
       A.live spkSigPtr spkSigCap.toNat 1 ∗ memRegion spkSigPtr spkSigCap.toNat ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗ ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗
          keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          ((s.sp + 0x90#64) ↦₆₄ spkSigCap) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ w6) ∗ ((s.sp + 0x3e8#64) ↦₈ b63) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents spkPubCap.toNat 1 ++
              rustDeallocEvents spkPrivCap.toNat 1 ++
              rustDeallocEvents spkSigCap.toNat 1) st) s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
          ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗ ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = kyberStorePtr ∧
        s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧ s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x22 = spkPubPtr ∧ s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x1460#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hpub_beq : (spkPubCap == 0#64) = false := beq_eq_false_iff_ne.mpr hpub_nz
  have hpriv_beq : (spkPrivCap == 0#64) = false := beq_eq_false_iff_ne.mpr hpriv_nz
  have hsig_beq : (spkSigCap == 0#64) = false := beq_eq_false_iff_ne.mpr hsig_nz
  have hkyber_beq : (kyberCtCap == 0#64) = false := beq_eq_false_iff_ne.mpr hkyber_nz
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = spkSigPtr := hx20
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkPubPtr := hx22
  have hx28' : s.readReg64 (Reg.gpr 28#5) = spkPubCap := hx28
  dsimp only [keyPair64UnalignedAt, bytes7At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_518 ext (lsρ lsRustDeallocSym)
  wp_call hdealloc (spkPubPtr, spkPubCap.toNat, 1, st)
  try simp only [wp_norm, arm64_norm] at hsp_sf
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf])
  wp_steps_sync_518 ext (lsρ lsRustDeallocSym)
  wp_call hdealloc (spkPrivPtr, spkPrivCap.toNat, 1,
    M.stepEvents (rustDeallocEvents spkPubCap.toNat 1) st)
  try simp only [wp_norm, arm64_norm, hsp_sf] at hsp_sf_1
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1, ← M.stepEvents_append])
  wp_steps_sync_518 ext (lsρ lsRustDeallocSym)
  wp_call hdealloc (spkSigPtr, spkSigCap.toNat, 1,
    M.stepEvents (rustDeallocEvents spkPubCap.toNat 1 ++ rustDeallocEvents spkPrivCap.toNat 1) st)
  try simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1] at hsp_sf_2
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hsp_sf, hsp_sf_1, hsp_sf_2, ← M.stepEvents_append])
  wp_steps_sync_518 ext kyberLoadShimAddr
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
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩
  simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

abbrev p2_seg2d_sigNz_gen_placed_wp := @p2_seg2d_sigNz_hooks_placed_wp

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA1PlacedBudget
