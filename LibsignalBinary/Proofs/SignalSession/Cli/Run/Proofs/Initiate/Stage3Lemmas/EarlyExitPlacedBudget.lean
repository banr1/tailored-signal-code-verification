/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Shared Zero-DH Unwind Exit (`[LibsignalPlacement]`)

Verifies the shared zero-DH unwind tail (`+0x1544` / `+0x1548 → +0x0350 → ret`) under
`RustCliAllocBudget M`, freeing `secretsPtr` (`192` B) and `pqspkPtr` (`1568` B) with events
`unwind1548Events` and reassembling `InitExitPostPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedTactic false
set_option maxRecDepth 200000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExitPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs hiding initSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate hiding
  InitExitPostPlaced InitPanicPostPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas hiding
  Unwind1548MemPlaced fsp_eq_sp_placed unwind_1548_placed_ok unwind_1544_placed_ok
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced initSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget
  (s3_step_to_vm_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget
  (s3_block_in_vm_placed s3_block_to_call_vm_placed s3_dealloc_stack_placed
   s3_done_call_vm s3_done_in_vm sret_err_speOwned_budget)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

/-- Allocator events along `+0x1544`/`+0x1548 → ret`: `dealloc(192, 1)` then `dealloc(1568, 1)`. -/
def unwind1548Events : List AllocEvent :=
  rustDeallocEvents 192 1 ++ rustDeallocEvents 1568 1

theorem stepEvents_unwind1548Events (M : AllocCostModel) (st : M.σ) :
    M.stepEvents (rustDeallocEvents 1568 1) (M.stepEvents (rustDeallocEvents 192 1) st) =
      M.stepEvents unwind1548Events st :=
  (M.stepEvents_append (rustDeallocEvents 192 1) (rustDeallocEvents 1568 1) st).symm

/-- Spatial footprint entering the shared zero-DH unwind tail at `+0x1548`. -/
def Unwind1548MemPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (x : InitGhost)
    (pqspkPtr secretsPtr : BitVec 64) (stk : Nat) (s0 s : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A.repAlloc x.stores StoresGhost.opened ∗
    protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    FromRecordCallees.lsLogOff ∗ A.pool lim st s ∗ initSaved s0 ∗
    A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗
    A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
    memRegion fsp 0x128 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x2e0 ∗
    ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
    memRegion (fsp + 0x438#64) 0x181 ∗
    ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) 0x37e ∗
    memRegion (fsp + 0x938#64) 0x20 ∗
    memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) ∗
    stackAt fsp (stk - cliInitiateFrame) ∗
    coinsCursorAtPlaced x.coinsP x.coins 32 ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt

private theorem unwind_locals_collapse_placed {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (pqspkPtr : BitVec 64) (u0 u1 u2 u3 : BitVec 64) (s0 : State) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    initSaved s0 ∗
      memRegion fsp 0x128 ∗
      initFreshRecAt fsp ∗
      memRegion (fsp + 0x148#64) 0x2e0 ∗
      ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
      memRegion (fsp + 0x438#64) 0x181 ∗
      ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x5ba#64) 0x37e ∗
      ((fsp + 0x938#64) ↦₆₄ u0) ∗ ((fsp + 0x940#64) ↦₆₄ u1) ∗
      ((fsp + 0x948#64) ↦₆₄ u2) ∗ ((fsp + 0x950#64) ↦₆₄ u3) ∗
      memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) ∗
      stackAt fsp (stk - cliInitiateFrame) ⊢
      stackAt s0.sp stk := by
  dsimp only
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  refine Entails.trans
    (sepConj_mono (initSaved_entails_memRegion96 s0)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (initFreshRecAt_collapse fsp)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo8_entails_memRegion1 _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (Entails.refl _)))))))))))))) ?_
  have hloc :
      memRegion fsp 0x128 ∗ memRegion (fsp + 0x128#64) 0x20 ∗
        memRegion (fsp + 0x148#64) 0x2e0 ∗ memRegion (fsp + 0x428#64) 8 ∗
        memRegion (fsp + 0x430#64) 8 ∗ memRegion (fsp + 0x438#64) 0x181 ∗
        memRegion (fsp + 0x5b9#64) 1 ∗ memRegion (fsp + 0x5ba#64) 0x37e ∗
        memRegion (fsp + 0x938#64) 8 ∗ memRegion (fsp + 0x940#64) 8 ∗
        memRegion (fsp + 0x948#64) 8 ∗ memRegion (fsp + 0x950#64) 8 ∗
        memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) =
      memRegion fsp initLocalsSize := by
    simp only [initLocalsSize, Nat.reduceAdd, Nat.reduceSub]
    rw [memRegion_merge_at (fsp + 0x950#64) 8 4920 (fsp + 0x958#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x948#64) 8 4928 (fsp + 0x950#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x940#64) 8 4936 (fsp + 0x948#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x938#64) 8 4944 (fsp + 0x940#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x5ba#64) 0x37e 4952 (fsp + 0x938#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x5b9#64) 1 5846 (fsp + 0x5ba#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x438#64) 0x181 5847 (fsp + 0x5b9#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x430#64) 8 6232 (fsp + 0x438#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x428#64) 8 6240 (fsp + 0x430#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x148#64) 0x2e0 6248 (fsp + 0x428#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x128#64) 0x20 6984 (fsp + 0x148#64) (by bv_omega) (by decide),
      memRegion_merge_at fsp 0x128 7016 (fsp + 0x128#64) (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq ?_) (stack_frame_reassemble hstk hstk64 s0)
  dsimp only [fsp] at hloc ⊢
  rw [← hloc]
  ac_rfl

private theorem s3_exit_vm_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWP (lsProg_521 (cliGhostExterns gh (cliExternsPlaced mmpl W))) ret s P (fun sf Pf =>
      VmPreserved s sf ∧ sf.trace = s.trace ∧
      (VmPreserved s sf → sf.fs.files = s.fs.files → Q sf Pf))) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  refine s3_step_to_vm_placed hh hinv (mid := ret) ?_
  dsimp only [initProgPlaced, initProgExtPlaced]
  refine SepWP.mono hwp ?_
  intro sf Pf hpcsf hrunsf ⟨hvm, htr, hQ⟩
  exact ⟨hvm, htr, fun _ _ hfs => SepWPp.done hpcsf hrunsf (hQ hvm hfs)⟩

theorem fsp_eq_sp_placed [LibsignalPlacement] {s0 s : State} {k : Nat}
    (h : InInitiatePlaced s0 s k) :
    s0.sp - BitVec.ofNat 64 cliInitiateFrame = s.sp :=
  CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas.fsp_eq_sp_placed h

set_option maxHeartbeats 1200000 in
/-- Budget-threaded zero-DH unwind exit from `+0x1548`. -/
theorem unwind_1548_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {pqspkPtr secretsPtr : BitVec 64} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hEnv : ∃ evs, InitEnv x evs ∧
      M.stepEvents (rustDeallocEvents 1568 1) (M.stepEvents (rustDeallocEvents 192 1) st) =
        M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hnone : initDef X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (_hsecNonNull : secretsPtr ≠ 0#64)
    (_hpqNonNull : pqspkPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 s 0x1548)
    (htr : s.trace = s0.trace)
    (hx25 : s.readReg64 (.gpr 25#5) = secretsPtr)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 10)
    (hx1 : s.readReg64 .x1 = 192#64)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (_hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (Unwind1548MemPlaced A lim st x pqspkPtr secretsPtr stk s0 s) Q Qp oom := by
  obtain ⟨evs, hInitEnv, hevsEq⟩ := hEnv
  have hsub_ext : extHookStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hsub64 : stk - cliInitiateFrame ≤ 2 ^ 64 := stk_sub_le_2pow64 hstk64
  dsimp only [Unwind1548MemPlaced]
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  rw [stackAt_sub_split_init fsp hsub_ext hsub64]
  refine' s3_block_to_call_vm_placed hh
    (lsρ lsRustDeallocSymCli)
    0x1554
    (Φ := fun sm =>
      sm.readReg64 .x0 = secretsPtr ∧ sm.readReg64 .x1 = 192#64 ∧
      sm.readReg64 .x2 = 1#64 ∧ sm.readReg64 (.gpr 26#5) = speWord 10)
    hctrl ?_ ?_; rotate_left 1
  · have hpc : s.pc = (blkPl_521).base + 5448#64 := hctrl.pc; have hrun := hctrl.run
    simp only [arm64_norm, wp_norm] at hx25 hx26 hx1
    dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521,
      BitVec.ofNat_eq_ofNat] at hpc ⊢
    by_vm_steps (
      wp_steps
      refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
        ⟨by simp only [*, arm64_norm, wp_norm],
         by simp only [*, arm64_norm, wp_norm],
         by wp_norm_goal,
         by simp only [*, arm64_norm, wp_norm]⟩)
  · intro sm1 hvm1 hctrl1 hpcm1 hlrm1 htrm1 ⟨hx0_1, hx1_1, hx2_1, hx26_1⟩
    have hpool1 : A.pool lim st s = A.pool lim st sm1 :=
      (A.pool_transport lim st s sm1 hvm1).symm
    refine s3_dealloc_stack_placed hh secretsPtr 192 st _ hctrl1 hpcm1 hlrm1
      hx0_1 (by rw [hx1_1]; decide) (by rw [hx2_1]; decide) lay192
      (by rw [hpool1, hctrl1.sp]; try dsimp only [fsp] at *; sep_frame) ?_
    intro s1 hctrl2 hcs1 htr1
    rw [hctrl1.sp]
    have hx26_2 : s1.readReg64 (.gpr 26#5) = speWord 10 := hcs1.2.2.2.2.2.2.2.1.trans hx26_1
    have h938 :
        memRegion (fsp + 0x938#64) 0x20 =
          memRegion (fsp + 0x938#64) 8 ∗ memRegion (fsp + 0x940#64) 8 ∗
          memRegion (fsp + 0x948#64) 8 ∗ memRegion (fsp + 0x950#64) 8 := by
      rw [memRegion_merge_at (fsp + 0x948#64) 8 8 (fsp + 0x950#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x940#64) 8 16 (fsp + 0x948#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x938#64) 8 24 (fsp + 0x940#64) (by bv_omega) (by decide)]
    rw [h938, ProofLib.memRegion_eight (fsp + 0x938#64), ProofLib.memRegion_eight (fsp + 0x940#64),
      ProofLib.memRegion_eight (fsp + 0x948#64), ProofLib.memRegion_eight (fsp + 0x950#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_elim_oom fun u0 => sepWPp_exists_elim_oom fun u1 =>
      sepWPp_exists_elim_oom fun u2 => sepWPp_exists_elim_oom fun u3 => ?_
    obtain ⟨halign, _, hfsp⟩ := hctrl2.step_ctx fsp
    refine' s3_block_to_call_vm_placed hh
      (lsρ lsRustDeallocSymCli)
      0x157c
      (Φ := fun sm =>
        sm.readReg64 .x0 = pqspkPtr ∧ sm.readReg64 .x1 = 1568#64 ∧
        sm.readReg64 .x2 = 1#64 ∧ sm.readReg64 (.gpr 26#5) = speWord 10)
      hctrl2 ?_ ?_; rotate_left 1
    · have hpc : s1.pc = (blkPl_521).base + 5460#64 := hctrl2.pc; have hrun := hctrl2.run
      dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      try dsimp only [fsp] at hfsp ⊢
      rw [hfsp]
      by_vm_steps (
        wp_steps
        refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
          ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
           by simp only [*, arm64_norm, wp_norm]⟩)
    · intro sm2 hvm2 hctrl3 hpcm2 hlrm2 htrm2 ⟨hx0_2, hx1_2, hx2_2, hx26_3⟩
      rw [← hfsp]
      let st1 := M.stepEvents (rustDeallocEvents 192 1) st
      have hpool2 : A.pool lim st1 s1 = A.pool lim st1 sm2 :=
        (A.pool_transport lim st1 s1 sm2 hvm2).symm
      refine s3_dealloc_stack_placed hh pqspkPtr 1568 st1 _ hctrl3 hpcm2 hlrm2
        hx0_2 (by rw [hx1_2]; decide) (by rw [hx2_2]; decide) lay1568
        (by rw [hpool2, hctrl3.sp]; try dsimp only [fsp, st1] at *; sep_frame) ?_
      intro s3 hctrl4 hcs3 htr3
      rw [hctrl3.sp]
      have hx26_4 : s3.readReg64 (.gpr 26#5) = speWord 10 :=
        hcs3.2.2.2.2.2.2.2.1.trans hx26_3
      have hret48 :
          memRegion x.ret 48 =
            memRegion x.ret 8 ∗ memRegion (x.ret + 8#64) 8 ∗
            memRegion (x.ret + 16#64) 8 ∗ memRegion (x.ret + 24#64) 8 ∗
            memRegion (x.ret + 32#64) 8 ∗ memRegion (x.ret + 40#64) 8 := by
        rw [memRegion_merge_at (x.ret + 32#64) 8 8 (x.ret + 40#64) (by bv_omega) (by decide),
          memRegion_merge_at (x.ret + 24#64) 8 16 (x.ret + 32#64) (by bv_omega) (by decide),
          memRegion_merge_at (x.ret + 16#64) 8 24 (x.ret + 24#64) (by bv_omega) (by decide),
          memRegion_merge_at (x.ret + 8#64) 8 32 (x.ret + 16#64) (by bv_omega) (by decide),
          memRegion_merge_at x.ret 8 40 (x.ret + 8#64) (by bv_omega) (by decide)]
      rw [hret48, ProofLib.memRegion_eight x.ret, ProofLib.memRegion_eight (x.ret + 8#64),
        ProofLib.memRegion_eight (x.ret + 16#64), ProofLib.memRegion_eight (x.ret + 24#64),
        ProofLib.memRegion_eight (x.ret + 32#64), ProofLib.memRegion_eight (x.ret + 40#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine sepWPp_exists_elim_oom fun r0 => sepWPp_exists_elim_oom fun r1 =>
        sepWPp_exists_elim_oom fun r2 => sepWPp_exists_elim_oom fun r3 =>
        sepWPp_exists_elim_oom fun r4 => sepWPp_exists_elim_oom fun r5 => ?_
      have hpool_fin {sf_cur : State} (hvm_cur : VmPreserved s3 sf_cur) :
          A.pool lim (M.stepEvents (rustDeallocEvents 1568 1) st1) s3 =
            A.pool lim (M.stepEvents evs st0) sf_cur := by
        dsimp only [st1]
        rw [hevsEq]
        exact (A.pool_transport lim (M.stepEvents evs st0) s3 sf_cur hvm_cur).symm
      refine s3_exit_vm_placed hh hctrl4.inv (ret := s0.readReg64 .lr) ?_
      have halign4 := (hctrl4.step_ctx fsp).1
      have hpc4 : s3.pc = (blkPl_521).base + 5500#64 := hctrl4.pc; have hrun4 := hctrl4.run
      have hx19_4 : s3.readReg64 (.gpr 19#5) = x.ret := hctrl4.x19.trans hx8
      have hs0sp : s0.sp = s3.sp + 7408#64 := by
        have hsp4 := hctrl4.sp
        dsimp only [cliInitiateFrame, BitVec.ofNat_eq_ofNat] at hsp4
        rw [hsp4]; bv_omega
      dsimp only [initPcPlaced, initEntryPlaced, lsProg_521, initFreshRecAt,
        initSaved, speWord, cliInitiateFrame, fsp,
        BitVec.ofNat_eq_ofNat] at hpc4 hx26_4 ⊢
      simp only [arm64_norm, wp_norm] at hx19_4 hx26_4
      conv =>
        arg 4
        simp only [Nat.reduceAdd, hs0sp,
          show s3.sp + 7408#64 - 7408#64 = s3.sp from by bv_omega,
          BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]
      by_vm_steps (
        wp_steps
        rw [show (blkPl_521).base + 5604#64 - - -4756#64 = (blkPl_521).base + 848#64 from by bv_omega]
        wp_steps
        have hsp_fin : s3.sp + 4096#64 + 3216#64 + 96#64 = s0.sp := by
          rw [hs0sp]; bv_omega
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by simp only [*, arm64_norm, wp_norm],
           by simp only [*, arm64_norm, wp_norm],
           fun hvm_fin hfs_fin => ?_⟩
        apply hpost
        refine ⟨by rw [← hs0sp]; simp only [arm64_norm, wp_norm], ?_, ?_⟩
        · refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                  by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                  by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
          simpa only [calleeSavedVRegs, arm64_norm, wp_norm] using hctrl4.vregs
        · dsimp only [initSlotSpecPlaced,
            LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, slotTrace, slotOut]
          refine Entails.sepExists_right evs
            (Entails.sepExists_right StoresGhost.opened
              (Entails.sepExists_right (.error (.untrustedIdentity x.peer.val)) ?_))
          refine Entails.pure_right ?_ ?_
          · exact ⟨hInitEnv,
                   ⟨by simp only [arm64_norm, wp_norm, htr3, htrm2, htr1, htrm1, htr]; exact List.prefix_refl _,
                    hfs_fin.trans hctrl4.files0,
                    by simp only [arm64_norm, wp_norm, htr3, htrm2, htr1, htrm1, htr]⟩,
                   (fun h => nomatch h), (fun h => nomatch h), by rw [hS, hnone]⟩
          rw [hpool_fin hvm_fin]
          generalize A.pool lim (M.stepEvents evs st0) _ = poolProp
          have hres := sret_err_speOwned_budget A x.peer.val x.ret
            (s3.readReg64 (.gpr 27#5))
            (s3.readReg64 (.gpr 25#5)) (s3.readReg64 (.gpr 28#5))
            (s3.readReg64 (.gpr 24#5)) (s3.readReg64 (.gpr 21#5))
          have hstk_re := unwind_locals_collapse_placed hstk hstk64 pqspkPtr u3 u2 u1 u0 s0
          dsimp only at hstk_re
          rw [stackAt_sub_split_init (s0.sp - BitVec.ofNat 64 cliInitiateFrame) hsub_ext hsub64]
            at hstk_re
          have htop :
              coinsCursorAtPlaced x.coinsP x.coins 32 ∗
                SpqrV1.GF.Mul2U16.tokenInitPlacedAt ⊢ anyHeap :=
            entails_anyHeap _
          refine Entails.trans (Entails.of_eq ?_)
            (sepConj_mono_right (sepConj_mono hres
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono hstk_re htop)))))))))
          dsimp only [fsp, speWord, initSaved, initFreshRecAt, cliInitiateFrame,
            State.sp, BitVec.ofNat_eq_ofNat] at hs0sp hres hstk_re ⊢
          rw [hs0sp]
          simp only [Nat.reduceAdd, BitVec.sub_eq_add_neg, BitVec.add_assoc,
            BitVec.reduceAdd, BitVec.reduceNeg, BitVec.add_zero]
          ac_rfl)

theorem unwind_1548_placed_evs_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 : M.σ} {evs_pre : List AllocEvent}
    {pqspkPtr secretsPtr : BitVec 64} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hEnv : InitEnv x (evs_pre ++ unwind1548Events))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hnone : initDef X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hpqNonNull : pqspkPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 s 0x1548)
    (htr : s.trace = s0.trace)
    (hx25 : s.readReg64 (.gpr 25#5) = secretsPtr)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 10)
    (hx1 : s.readReg64 .x1 = 192#64)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (Unwind1548MemPlaced A lim (M.stepEvents evs_pre st0) x pqspkPtr secretsPtr stk s0 s)
      Q Qp oom :=
  unwind_1548_placed_ok hh
    ⟨evs_pre ++ unwind1548Events, hEnv,
      (stepEvents_unwind1548Events M (M.stepEvents evs_pre st0)).trans
        (M.stepEvents_append evs_pre unwind1548Events st0).symm⟩
    hS hnone hstk hstk64 hx8 hsecNonNull hpqNonNull hctrl htr hx25 hx26 hx1 hpost hpanic

/-- Budget-threaded zero-DH unwind entry at `+0x1544` (`DH2`, `DH3`, `DH4`). -/
theorem unwind_1544_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {pqspkPtr secretsPtr : BitVec 64} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hEnv : ∃ evs, InitEnv x evs ∧
      M.stepEvents (rustDeallocEvents 1568 1) (M.stepEvents (rustDeallocEvents 192 1) st) =
        M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hnone : initDef X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hpqNonNull : pqspkPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 s 0x1544)
    (htr : s.trace = s0.trace)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 10)
    (hx1 : s.readReg64 .x1 = 192#64)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (((s0.sp - 0x60#64 - 0x28#64) ↦₆₄ secretsPtr) ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        FromRecordCallees.lsLogOff ∗ A.pool lim st s ∗ initSaved s0 ∗
        A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗
        A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
        memRegion fsp 0x128 ∗
        initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x2e0 ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        memRegion (fsp + 0x438#64) 0x181 ∗
        ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 0x37e ∗
        memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x1310 ∗
        memRegion (fsp + 0x1c70#64) 0x20 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt) Q Qp oom := by
  dsimp only
  have hslot : s0.sp - 0x60#64 - 0x28#64 = s.readReg64 (.gpr 29#5) - 0x28#64 := by
    change _ = s.readReg64 .fp - 0x28#64; rw [hctrl.fp]
  rw [hslot]
  refine' s3_block_in_vm_placed hh 0x1548
    (Φ := fun sm =>
      sm.readReg64 (.gpr 25#5) = secretsPtr ∧
      sm.readReg64 (.gpr 26#5) = speWord 10 ∧
      sm.readReg64 .x1 = 192#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc : s.pc = (blkPl_521).base + 5444#64 := hctrl.pc; have hrun := hctrl.run
    simp only [arm64_norm, wp_norm] at hx26 hx1
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521,
      BitVec.ofNat_eq_ofNat] at hpc ⊢
    by_vm_steps (
      wp_steps
      refine s3_done_in_vm (by wp_norm_lhs) (Entails.refl _)
        ⟨by simp only [*, arm64_norm, wp_norm],
         by simp only [*, arm64_norm, wp_norm],
         by simp only [*, arm64_norm, wp_norm]⟩)
  · intro sm hvm htrm hctrl' ⟨hx25', hx26', hx1'⟩
    rw [← hslot]
    have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_transport lim st s sm hvm).symm
    refine sepWPp_conseq_oom ?_
      (unwind_1548_placed_ok hh hEnv hS hnone hstk hstk64 hx8 hsecNonNull hpqNonNull hctrl'
        (htrm.trans htr) hx25' hx26' hx1' hpost hpanic)
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    have haddr : s0.sp - 0x60#64 - 0x28#64 = fsp + 0x1c68#64 := by
      dsimp only [fsp]; rw [cliInitiateFrame_eq]; bv_omega
    have htail :
        ((s0.sp - 0x60#64 - 0x28#64) ↦₆₄ secretsPtr) ∗ memRegion (fsp + 0x958#64) 0x1310 ∗
          memRegion (fsp + 0x1c70#64) 0x20 ⊢
          memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) := by
      rw [haddr]
      refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
      have hmerge :
          memRegion (fsp + 0x958#64) 0x1310 ∗ memRegion (fsp + 0x1c68#64) 8 ∗
            memRegion (fsp + 0x1c70#64) 0x20 =
          memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) := by
        simp only [initLocalsSize, Nat.reduceAdd, Nat.reduceSub]
        rw [memRegion_merge_at (fsp + 0x1c68#64) 8 32 (fsp + 0x1c70#64) (by bv_omega) (by decide),
          memRegion_merge_at (fsp + 0x958#64) 4880 40 (fsp + 0x1c68#64) (by bv_omega) (by decide)]
      exact Entails.of_eq (by rw [← hmerge]; ac_rfl)
    dsimp only [Unwind1548MemPlaced]
    rw [hpool]
    exact sep_replace htail (by dsimp only [fsp]; sep_frame) (by dsimp only [fsp]; sep_frame)

theorem unwind_1544_placed_evs_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 : M.σ} {evs_pre : List AllocEvent}
    {pqspkPtr secretsPtr : BitVec 64} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hEnv : InitEnv x (evs_pre ++ unwind1548Events))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hnone : initDef X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hpqNonNull : pqspkPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 s 0x1544)
    (htr : s.trace = s0.trace)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 10)
    (hx1 : s.readReg64 .x1 = 192#64)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (((s0.sp - 0x60#64 - 0x28#64) ↦₆₄ secretsPtr) ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        FromRecordCallees.lsLogOff ∗ A.pool lim (M.stepEvents evs_pre st0) s ∗ initSaved s0 ∗
        A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗
        A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
        memRegion fsp 0x128 ∗
        initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x2e0 ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        memRegion (fsp + 0x438#64) 0x181 ∗
        ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 0x37e ∗
        memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x1310 ∗
        memRegion (fsp + 0x1c70#64) 0x20 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt) Q Qp oom :=
  unwind_1544_placed_ok hh
    ⟨evs_pre ++ unwind1548Events, hEnv,
      (stepEvents_unwind1548Events M (M.stepEvents evs_pre st0)).trans
        (M.stepEvents_append evs_pre unwind1548Events st0).symm⟩
    hS hnone hstk hstk64 hx8 hsecNonNull hpqNonNull hctrl htr hx26 hx1 hpost hpanic

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExitPlacedBudget

end
