/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5CallsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPathPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopATailPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlaced
meta import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common

/-!
# Budget-Threaded M5 Inner Loop A Path Builder (`M+0x8fc .. M+0x980`, Block `617`)

Budget-threaded verification of `m5_loop_a_build_path_placed` on Block `617` under `FitsEnv`,
tracking exact capacity `m5LoopAPathCap dir name` and advancing `A.pool` by `M5LoopABuildPathEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPathPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (LayoutOk vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall extHookStack memcpyName reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (pathOf)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (InMainPlaced LsCodeInv mPcPlaced mainFrameSize ownedBytes)
open CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
  (fp_eq_fsp_add fsp_fp_sub_40 m5_reg_a_placed m5_run_placed mPcPlaced_eq_blkPl pathOf_ne_nil)
open scoped CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
open CryptoVerification.SignalSession.Cli.Path.Helpers (ofNat_ne_zero)
open CryptoVerification.SpqrV1.Varint (vecU8At_of_header_rest vecU8RestAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   fitsEvents_append rustAllocEvents rustReallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5CallsPlacedBudget
  (m5_call_alloc_placed m5_call_memcpy_ro_pool_placed m5_call_reserve1_placed
   m5_call_shim_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopATailPlacedBudget
  (M5LoopATailEnv m5LoopATailCap m5LoopATailEvents m5_loop_a_slash_and_name_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget (MainMemcpyROFsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents fitsEnv_doReserve_iff)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm]
  RustCliAllocBudget.pool_setPC
  RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState
  RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32
  RustCliAllocBudget.pool_writeReg

/-- Final `String` capacity produced by `m5_loop_a_build_path_placed` (`M+0x8fc .. M+0x980`) for
non-empty `dir`. -/
def m5LoopAPathCap (dir name : List (BitVec 8)) : Nat :=
  m5LoopATailCap (reserveCap dir.length dir.length 1) dir name

/-- Deterministic allocator event list of `m5_loop_a_build_path_placed` (`M+0x8fc .. M+0x980`):
`__rust_alloc(dir.length, 1)`, `reserve1(1)` realloc, and optional `reserve1(name.length)` realloc. -/
def m5LoopABuildPathEvents (dir name : List (BitVec 8)) : List AllocEvent :=
  rustAllocEvents dir.length 1 ++
    rustReallocEvents dir.length (reserveCap dir.length dir.length 1) 1 ++
    m5LoopATailEvents (reserveCap dir.length dir.length 1) dir name

/-- Allocator event envelope of `m5_loop_a_build_path_placed`. -/
def M5LoopABuildPathEnv (dir name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  evs = m5LoopABuildPathEvents dir name

example : ∃ evs, M5LoopABuildPathEnv [0x61#8] [0x62#8] evs :=
  ⟨m5LoopABuildPathEvents [0x61#8] [0x62#8], rfl⟩

set_option maxHeartbeats 1600000 in
/-- Budget-threaded execution of `M+0x8fc .. M+0x97c` (plus `M+0x9b8 .. M+0x9d8` on reserve grow)
under `FitsEnv`, producing `ownedBytes A.repAlloc capFinal ptrFinal … (pathOf dir name)` at `M+0x980`
with `capFinal.toNat = m5LoopAPathCap dir name`. -/
theorem m5_loop_a_build_path_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {uuidParse : UuidParser}
    {hookStack resStack stk : Nat}
    {base dPathPtr c1 p1 v48 v58 v458 v460 v468 : BitVec 64}
    {dir name : List (BitVec 8)}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hfit : FitsEnv M lim st (M5LoopABuildPathEnv dir name))
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_res : mainFrameSize + resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hd_ne : dir ≠ [])
    (hpath_lt : (pathOf dir name).length < 2 ^ 32)
    (hs : InMainPlaced CodeOk s0 s 0x8fc)
    (hx27 : s.readReg64 (.gpr 27#5) = base + 40#64)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length)
    (hP : P ⊢ vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
      (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x40#64) ↦₆₄ dPathPtr) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x48#64) ↦₆₄ v48) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x58#64) ↦₆₄ v58) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x458#64) ↦₆₄ v458) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x460#64) ↦₆₄ v460) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x468#64) ↦₆₄ v468) ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
      A.pool lim st s ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent) (capFinal ptrFinal v458' v460' v468' : BitVec 64),
      M5LoopABuildPathEnv dir name evs →
      capFinal.toNat = m5LoopAPathCap dir name →
      0 < capFinal.toNat →
      (pathOf dir name).length ≤ capFinal.toNat →
      capFinal.toNat < 2 ^ 63 →
      ptrFinal ≠ 0#64 →
      InMainPlaced CodeOk s0 sm 0x980 →
      sm.fs = s.fs →
      sm.trace = s.trace →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sm.readReg64 (.gpr 21#5) = BitVec.ofNat 64 name.length →
      sm.readReg64 (.gpr 22#5) = ptrFinal →
      sm.readReg64 (.gpr 23#5) = capFinal →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (dir.length + 1) →
      sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      sm.readReg64 (.gpr 27#5) = base + 40#64 →
      sm.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (ownedBytes A.repAlloc capFinal ptrFinal (BitVec.ofNat 64 (pathOf dir name).length)
            (pathOf dir name) ∗
          vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
          (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x40#64) ↦₆₄ dPathPtr) ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x48#64) ↦₆₄ p1) ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x58#64) ↦₆₄ v58) ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x458#64) ↦₆₄ v458') ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x460#64) ↦₆₄ v460') ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x468#64) ↦₆₄ v468') ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hp_eq := pathOf_ne_nil hd_ne name
  have hp_len : (pathOf dir name).length = dir.length + 1 + name.length := by
    rw [hp_eq]; simp; omega
  have hd_pos : 0 < dir.length := List.length_pos_of_ne_nil hd_ne
  have hd_lt : dir.length < 2 ^ 32 := by m5_omega
  have hname_lt : name.length < 2 ^ 32 := by m5_omega
  have hd_toNat : (BitVec.ofNat 64 dir.length).toNat = dir.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by m5_omega)]
  have hlay0 : LayoutOk dir.length 1 := ⟨hd_pos, ⟨0, rfl⟩, by m5_omega⟩
  have off_m32 : (base + 40#64) + (-32#64) = base + 8#64 := by bv_omega
  have off_fp40 : (s0.sp - 0x60#64) - 40#64 = fsp + 0x458#64 := by
    rw [fp_eq_fsp_add s0]; exact fsp_fp_sub_40 fsp
  have off_fp40_add : (s0.sp - 0x60#64) + (-40#64) = fsp + 0x458#64 := by
    rw [← BitVec.sub_eq_add_neg]; exact off_fp40
  have off_fp24 : (s0.sp - 0x60#64) + (-24#64) = fsp + 0x468#64 := by
    rw [fp_eq_fsp_add s0]; dsimp only [fsp]; bv_omega
  have off_hdr1 :
      vecHeader base c1 p1 (BitVec.ofNat 64 name.length) =
        (base ↦₆₄ c1) ∗ ((base + 8#64) ↦₆₄ p1) ∗
          (((base + 8#64) + 8#64) ↦₆₄ BitVec.ofNat 64 name.length) := by
    unfold vecHeader
    have hb : base + 16#64 = (base + 8#64) + 8#64 := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [hb]
  let evs0 := rustAllocEvents dir.length 1
  let cap1Nat := reserveCap dir.length dir.length 1
  let evs1 := rustReallocEvents dir.length cap1Nat 1
  let evs2 := m5LoopATailEvents cap1Nat dir name
  have hevs_eq : m5LoopABuildPathEvents dir name = evs0 ++ (evs1 ++ evs2) := by
    simp only [m5LoopABuildPathEvents, evs0, evs1, evs2, cap1Nat, List.append_assoc]
  have hfit_all : LibsignalBinary.Heap.FitsEvents M lim st (evs0 ++ (evs1 ++ evs2)) := by
    rw [← hevs_eq]; exact hfit _ rfl
  have ⟨hfit0, hfit12⟩ := (fitsEvents_append M lim evs0 (evs1 ++ evs2) st).mp hfit_all
  have ⟨hfit1, hfit2⟩ := (fitsEvents_append M lim evs1 evs2 (M.stepEvents evs0 st)).mp hfit12
  refine SepWPp.weaken_pre hP ?_
  have hpc := hs.pc; have hrun := hs.run
  refine m5_run_placed hs.inv (mid := lsρ lsRustNoAllocShimSymCli)
    (P0 := ((base + 8#64) ↦₆₄ p1) ∗
      (((base + 8#64) + 8#64) ↦₆₄ BitVec.ofNat 64 name.length) ∗
      ((s.sp + 0x48#64) ↦₆₄ v48) ∗ A.pool lim st s)
    (F := (base ↦₆₄ c1) ∗ (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
      ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x58#64) ↦₆₄ v58) ∗
      ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗
      ((fsp + 0x468#64) ↦₆₄ v468) ∗ stackAt fsp (stk - mainFrameSize) ∗ F)
    (by rw [off_hdr1, hs.sp]; dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  m5_steps_sync_pool
  try simp only [State.setMem_setMem]
  apply SepWP.done
    (by
      simp only [arm64_norm, hpc, hx27, off_m32, hs.sp, mPcPlaced_eq_blkPl,
        BitVec.add_assoc, BitVec.reduceAdd]
      try m5_bv_omega)
    (by simp only [arm64_norm, hrun])
  intro hpcm1 hrunm1 hinv_m1
  refine m5_call_shim_pool_placed hA hstk_ext hstk64 hpcm1 hrunm1 hinv_m1
    (by simp only [arm64_norm, hs.sp]) (by simp only [arm64_norm, hs.fp])
    (by simp only [calleeSavedVRegs, arm64_norm, hs.vregs]) hs.spAligned
    (retOff := 0x908)
    (by simp only [arm64_norm, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd])
    (F := vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
      (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
      ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
      ((fsp + 0x58#64) ↦₆₄ v58) ∗
      ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗
      ((fsp + 0x468#64) ↦₆₄ v468) ∗ F)
    (by
      rw [off_hdr1, hs.sp]; dsimp only [fsp]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  intro s1 hs1 _hvm1 hfs1 htr1 hcsm1
  have hpc1 := hs1.pc; have hrun1 := hs1.run
  have r21_1 : s1.readReg64 (.gpr 21#5) = BitVec.ofNat 64 name.length := by
    simp only [hcsm1.2.2.1, arm64_norm]
  have r27_1 : s1.readReg64 (.gpr 27#5) = base + 40#64 :=
    hcsm1.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx27])
  have r28_1 : s1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length :=
    hcsm1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx28])
  apply m5_reg_a_placed hs1.inv (mid := lsρ lsRustAllocSymCli)
  m5_steps
  apply SepWP.done
    (by
      simp only [arm64_norm, hpc1, r28_1, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd]
      try m5_bv_omega)
    (by simp only [arm64_norm, hrun1])
  intro hpcm2 hrunm2 hinv_m2; rw [emp_sepConj]
  refine m5_call_alloc_placed hA hstk_ext hstk64 hlay0 hfit0 hpcm2 hrunm2 hinv_m2
    (by simp only [arm64_norm, hs1.sp]) (by simp only [arm64_norm, hs1.fp])
    (by simp only [calleeSavedVRegs, arm64_norm, hs1.vregs]) hs1.spAligned
    (retOff := 0x914)
    (by simp only [arm64_norm, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd])
    (by simp only [arm64_norm, r28_1, hd_toNat]) (by simp only [arm64_norm]; try rfl)
    (F := vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
      (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
      ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
      ((fsp + 0x58#64) ↦₆₄ v58) ∗
      ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗
      ((fsp + 0x468#64) ↦₆₄ v468) ∗ F)
    (by simp only [arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  intro s2 hs2 hptr0_ne _hacp2 hfs2 htr2 hcsm2
  let ptr0 := s2.readReg64 .x0
  have hptr0_beq : (s2.readReg64 .x0 == 0#64) = false := beq_false_of_ne hptr0_ne
  have hpc2 := hs2.pc; have hrun2 := hs2.run
  have r21_2 : s2.readReg64 (.gpr 21#5) = BitVec.ofNat 64 name.length :=
    hcsm2.2.2.1.trans (by simp only [arm64_norm, r21_1])
  have r27_2 : s2.readReg64 (.gpr 27#5) = base + 40#64 :=
    hcsm2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r27_1])
  have r28_2 : s2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length :=
    hcsm2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r28_1])
  refine m5_run_placed hs2.inv (mid := lsρ memcpyName)
    (P0 := (s2.sp + 0x40#64) ↦₆₄ dPathPtr)
    (F := A.pool lim (M.stepEvents evs0 st) s2 ∗ stackAt fsp (stk - mainFrameSize) ∗
      A.live ptr0 dir.length 1 ∗ memRegion ptr0 dir.length ∗
      vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
      (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
      ((fsp + 0x58#64) ↦₆₄ v58) ∗
      ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗
      ((fsp + 0x468#64) ↦₆₄ v468) ∗ F)
    (by rw [hs2.sp]; dsimp only [fsp, ptr0, evs0]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  m5_steps
  apply SepWP.done
    (by
      simp only [arm64_norm, hpc2, hptr0_beq, hs2.sp, r28_2, mPcPlaced_eq_blkPl,
        BitVec.add_assoc, BitVec.reduceAdd]
      try m5_bv_omega)
    (by simp only [arm64_norm, hrun2])
  intro hpcm3 hrunm3 hinv_m3
  refine m5_call_memcpy_ro_pool_placed (MainMemcpyROFsPlaced.of_alloc hA) hstk_ext hstk64
    hpcm3 hrunm3 hinv_m3
    (by simp only [arm64_norm, hs2.sp]) (by simp only [arm64_norm, hs2.fp])
    (by simp only [calleeSavedVRegs, arm64_norm, hs2.vregs]) hs2.spAligned
    (retOff := 0x928)
    (by simp only [arm64_norm, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd])
    (dst := ptr0) (src := dPathPtr) (bs := dir)
    (by simp only [arm64_norm]; try rfl) (by simp only [arm64_norm])
    (by simp only [arm64_norm, r28_2, hd_toNat]) (by m5_omega)
    (F := A.live ptr0 dir.length 1 ∗
      vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
      (p1 ↦ₛ name) ∗ ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
      ((fsp + 0x58#64) ↦₆₄ v58) ∗
      ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗
      ((fsp + 0x468#64) ↦₆₄ v468) ∗ F)
    (by
      rw [hs2.sp]; dsimp only [fsp]
      simp only [arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  intro s3 hs3 _hvm3 hfs3 htr3 hcsm3
  have hpc3 := hs3.pc; have hrun3 := hs3.run
  have r21_3 : s3.readReg64 (.gpr 21#5) = BitVec.ofNat 64 name.length :=
    hcsm3.2.2.1.trans (by simp only [arm64_norm, r21_2])
  have r22_3 : s3.readReg64 (.gpr 22#5) = ptr0 :=
    hcsm3.2.2.2.1.trans (by simp only [arm64_norm]; try rfl)
  have r27_3 : s3.readReg64 (.gpr 27#5) = base + 40#64 :=
    hcsm3.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r27_2])
  have r28_3 : s3.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length :=
    hcsm3.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r28_2])
  have hcap0_ne : BitVec.ofNat 64 dir.length ≠ 0#64 := ofNat_ne_zero hd_pos (by m5_omega)
  have hrest0 :
      A.live ptr0 dir.length 1 ∗ (ptr0 ↦ₛ dir) =
        vecU8RestAt A.repAlloc (BitVec.ofNat 64 dir.length) ptr0 dir := by
    simp only [vecU8RestAt, RustCliAllocBudget.repAlloc_live, BitVec.ofNat_eq_ofNat,
      hcap0_ne, ↓reduceIte, hd_toNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  refine m5_run_placed hs3.inv (mid := lsmpl.base 561)
    (P0 := ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗
      ((fsp + 0x468#64) ↦₆₄ v468) ∗ A.pool lim (M.stepEvents evs0 st) s3)
    (F := vecU8RestAt A.repAlloc (BitVec.ofNat 64 dir.length) ptr0 dir ∗
      stackAt fsp (stk - mainFrameSize) ∗
      vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
      (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
      ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
      ((fsp + 0x58#64) ↦₆₄ v58) ∗ F)
    (by
      refine Entails.trans (Entails.of_eq (Q :=
        (A.live ptr0 dir.length 1 ∗ (ptr0 ↦ₛ dir)) ∗
        (((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗
          ((fsp + 0x468#64) ↦₆₄ v468) ∗ A.pool lim (M.stepEvents evs0 st) s3 ∗
          stackAt fsp (stk - mainFrameSize) ∗
          vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
          (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
          ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
          ((fsp + 0x58#64) ↦₆₄ v58) ∗ F))
        (by dsimp only [fsp]; sep_ac_rfl)) ?_
      rw [hrest0]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  have hfp3 := hs3.fp
  m5_steps_sync_pool
  try simp only [State.setMem_setMem]
  apply SepWP.done
    (by
      simp only [arm64_norm, hpc3, hfp3, r28_3, r22_3, off_fp40, off_fp40_add, off_fp24,
        mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd]
      try m5_bv_omega)
    (by simp only [arm64_norm, hrun3])
  intro hpcm4 hrunm4 hinv_m4
  have hbound1 : reserveCap (BitVec.ofNat 64 dir.length).toNat dir.length 1 + 1 ≤ 2 ^ 63 := by
    simp only [reserveCap, hd_toNat]; m5_omega
  have hvec0 :
      ((fsp + 0x458#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        ((fsp + 0x460#64) ↦₆₄ ptr0) ∗
        ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        vecU8RestAt A.repAlloc (BitVec.ofNat 64 dir.length) ptr0 dir =
      vecU8At A.repAlloc (fsp + 0x458#64) (BitVec.ofNat 64 dir.length) ptr0 dir := by
    have h0 := vecU8At_of_header_rest A.repAlloc (fsp + 0x458#64) (BitVec.ofNat 64 dir.length)
      ptr0 dir (by rw [hd_toNat]) (by rw [hd_toNat]; m5_omega) hptr0_ne
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h0
  have hdo1 :
      doReserveEvents (DoReserveCall.mk (fsp + 0x458#64) (BitVec.ofNat 64 dir.length) ptr0 dir 1) =
        evs1 := by
    simp only [doReserveEvents, hcap0_ne, ↓reduceIte, hd_toNat, evs1, cap1Nat]
  have hfit_res1 :
      FitsEnv M lim (M.stepEvents evs0 st)
        (LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.DoReserveEnv
          (DoReserveCall.mk (fsp + 0x458#64) (BitVec.ofNat 64 dir.length) ptr0 dir 1)) := by
    rw [fitsEnv_doReserve_iff, hdo1]
    exact hfit1
  refine m5_call_reserve1_placed hc hstk_res hstk64 hbound1 hfit_res1 hpcm4 hrunm4 hinv_m4
    (by simp only [arm64_norm, hs3.sp]) (by simp only [arm64_norm, hfp3])
    (by simp only [calleeSavedVRegs, arm64_norm, hs3.vregs]) hs3.spAligned
    (retOff := 0x948)
    (by simp only [arm64_norm, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd])
    (v := fsp + 0x458#64) (curCap := BitVec.ofNat 64 dir.length) (curPtr := ptr0)
    (curBs := dir) (additional := 1)
    (by simp only [arm64_norm, hfp3, off_fp40])
    (by simp only [arm64_norm, r28_3, hd_toNat])
    (by simp only [arm64_norm]; try rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (F := vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
      (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
      ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
      ((fsp + 0x58#64) ↦₆₄ v58) ∗ F)
    (by
      refine Entails.trans (Entails.of_eq (Q :=
        (((fsp + 0x458#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
          ((fsp + 0x460#64) ↦₆₄ ptr0) ∗
          ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
          vecU8RestAt A.repAlloc (BitVec.ofNat 64 dir.length) ptr0 dir) ∗
        (A.pool lim (M.stepEvents evs0 st) _ ∗ stackAt fsp (stk - mainFrameSize) ∗
          vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
          (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
          ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
          ((fsp + 0x58#64) ↦₆₄ v58) ∗ F))
        (by dsimp only [fsp]; sep_ac_rfl)) ?_
      rw [hvec0]; dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  intro s4 ptr1 hs4 hfs4 htr4 hcsm4
  rw [hdo1]
  set cap1 : BitVec 64 :=
    BitVec.ofNat 64 (reserveCap (BitVec.ofNat 64 dir.length).toNat dir.length 1)
  have hlt64_1 : reserveCap dir.length dir.length 1 < 2 ^ 64 := by
    simp only [reserveCap]; m5_omega
  have hcap1_nat : cap1.toNat = cap1Nat := by
    simp only [cap1, cap1Nat, hd_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64_1]
  have hcap1_lt34 : cap1.toNat < 2 ^ 34 := by
    simp only [hcap1_nat, cap1Nat, reserveCap]; m5_omega
  have hcap1_ge : dir.length + 1 ≤ cap1.toNat := by
    simp only [hcap1_nat, cap1Nat, reserveCap]; m5_omega
  have hfit_tail :
      FitsEnv M lim (M.stepEvents evs1 (M.stepEvents evs0 st))
        (M5LoopATailEnv cap1.toNat dir name) := by
    intro evs hevs
    rw [show evs = evs2 by simpa only [M5LoopATailEnv, hcap1_nat, evs2] using hevs]
    exact hfit2
  exact m5_loop_a_slash_and_name_placed
    (st := M.stepEvents evs1 (M.stepEvents evs0 st)) (s := s)
    (base := base) (dPathPtr := dPathPtr) (c1 := c1) (p1 := p1)
    (cap1 := cap1) (ptr1 := ptr1) (F := ((fsp + 0x58#64) ↦₆₄ v58) ∗ F)
    hA hc hfit_tail hstk_ext hstk_res hstk64
    hd_ne hpath_lt
    hcap1_ge hcap1_lt34 hs4
    (by simp only [hfs4, arm64_norm, hfs3, hfs2, hfs1])
    (by simp only [htr4, arm64_norm, htr3, htr2, htr1])
    (by simp only [hcsm4.1, arm64_norm, hcsm3.1, hcsm2.1, hcsm1.1])
    (by simp only [hcsm4.2.1, arm64_norm, hcsm3.2.1, hcsm2.2.1, hcsm1.2.1])
    (hcsm4.2.2.1.trans (by simp only [arm64_norm, r21_3]))
    (by simp only [hcsm4.2.2.2.2.2.1, arm64_norm, hcsm3.2.2.2.2.2.1, hcsm2.2.2.2.2.2.1,
      hcsm1.2.2.2.2.2.1])
    (by simp only [hcsm4.2.2.2.2.2.2.2.1, arm64_norm, hcsm3.2.2.2.2.2.2.2.1,
      hcsm2.2.2.2.2.2.2.2.1, hcsm1.2.2.2.2.2.2.2.1])
    (hcsm4.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r27_3]))
    (hcsm4.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r28_3]))
    (by dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl))
    fun sm evs_tail capFinal ptrFinal v458' v460' v468'
      htail hcapF hc1 hc2 hc3 hc4 hsm hfs htr h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 => by
      have htail_eq : evs_tail = evs2 := by
        simpa only [M5LoopATailEnv, hcap1_nat, evs2] using htail
      have hst_eq :
          M.stepEvents evs_tail (M.stepEvents evs1 (M.stepEvents evs0 st)) =
            M.stepEvents (m5LoopABuildPathEvents dir name) st := by
        rw [htail_eq, hevs_eq, M.stepEvents_append, M.stepEvents_append]
      have hcapF_eq : capFinal.toNat = m5LoopAPathCap dir name := by
        simpa only [m5LoopAPathCap, hcap1_nat, cap1Nat] using hcapF
      refine SepWPp.weaken_pre
        (by rw [hst_eq]; dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl))
        (hnext sm (m5LoopABuildPathEvents dir name) capFinal ptrFinal v458' v460' v468'
          rfl hcapF_eq hc1 hc2 hc3 hc4 hsm hfs htr h19 h20 h21 h22 h23 h24 h25 h26 h27 h28)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPathPlacedBudget
