/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Shared Post-Dispatch and Error Sub-Hops for Budget-Threaded Arm `R1a`

Verifies the shared post-dispatch and error cleanup sub-hops (`+0x2d68`, `+0x2c54`, `+0x2c30`,
`+0x860`, `+0x6e0`, `+0x2bf0`, `+0x8f0`) on Block `579` supporting `R1aProofPlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (sepWPp_seq_lscro)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost speWord)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallW RunCall cliWrOk inputOf ownedBytes runResAt runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRejectPlaced Bytes InRunPlaced PanicK RunHistOk addrNameHeap init1Cells r1b_StackBounds
   rejectMem runFsp runLocalBytes runLocals runLocalsFrom runOom runPcPlaced runPcPlaced_eq
   runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunDrop (PlainSpeTag SpeOwned speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAux
  (FreeRejK r1a_CodeOk r1a_addrNameHeap_eq_owned r1a_addrNameHeap_zero r1a_bind_sepWPp_state
   r1a_group6_4 r1a_group6c r1a_group_11_2 r1a_group_5c r1a_herrSym r1a_hist_ans_step
   r1a_localsBound r1a_localsCtx r1a_localsEnd r1a_locals_drop_head r1a_locals_drop_mid
   r1a_locals_focus r1a_memRegion32_eq_words r1a_memRegion48_words r1a_memRegion_zero
   r1a_ownedBytes_zero r1a_panic_handle_error r1a_pool_setMem_write16 r1a_pool_setMem_write32
   r1a_pool_setMem_write32_2 r1a_pool_setMem_write64 r1a_pool_setMem_write64_2
   r1a_pool_setMem_write64_4 r1a_pool_setMem_write8 r1a_sepWPp_exists_pre r1a_sepWPp_weaken_pre
   r1a_words5_to_memRegion40 r1a_words6_to_memRegion48)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed r1b_call_dropSpeOwned_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (sepWP_with_vm_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (storesAt_opened_atState)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  r1a_pool_setMem_write8 r1a_pool_setMem_write16 r1a_pool_setMem_write32
  r1a_pool_setMem_write32_2 r1a_pool_setMem_write64 r1a_pool_setMem_write64_2
  r1a_pool_setMem_write64_4

scoped syntax "by_vm_open " tacticSeq : tactic
scoped elab_rules : tactic
  | `(tactic| by_vm_open $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_with_vm_oom))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_vm_open: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let nArgs := e1.consumeMData.getAppNumArgs
      let isTrapRebase (x : Lean.Expr) : Bool :=
        let x := x.consumeMData
        x.isAppOfArity ``Arm64.Program.rebase nArgs &&
          (x.getArg! 2).consumeMData.isConstOf ``LibsignalBinary.Proofs.Placed.BudgetVmSteps.trapHooks
      let prf2 := prf1.replace fun sub =>
        let s0 := sub.consumeMData
        if s0.isAppOfArity ``Arm64.Program.withSvc 2 && isTrapRebase (s0.getArg! 0) then
          some sub
        else if isTrapRebase s0 then
          some e2
        else none
      g.assign prf2

/-! ## Shared Post-Dispatch and Error Sub-Hops -/

theorem r1a_panic_step [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {g : RunCall}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hpanic : PanicK g s0 Qp)
    (hpc : s.pc = runPcPlaced 0x2d68) (hrun : s.status = .Running) (hinv : r1a_CodeOk s.mem)
    (haf : allocFailedIn s0 s) (_htr : s0.trace <+: s.trace) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s P Q Qp (runOom s0) := by
  rw [runPcPlaced_eq] at hpc
  apply sepWPp_seq_lscro (mid := lsρ r1a_herrSym) hinv
  dsimp only [runProgPlaced, lsProg_579]
  (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [r1a_herrSym, arm64_norm]) (by simp only [arm64_norm, hrun])
  intro _; apply r1a_bind_sepWPp_state; intro s1 R hm1 _hL
  have hext1 : (runProgPlaced H).externAt? s1.pc = some Rust.panicked :=
    (show s1.pc = lsρ r1a_herrSym by simp only [s1, r1a_herrSym, arm64_norm]) ▸ r1a_panic_handle_error hh
  exact ⟨Rust.panicked s1,
    Steps.step (Step.extern (by simp only [s1, arm64_norm, hrun]) hext1 (Memory.KeepsFrozen.refl _)) (Steps.refl _),
    Or.inr (Or.inl ⟨rfl, P, hm1, hpanic (Rust.panicked s1) P (Or.inr (by
      unfold allocFailedIn at haf ⊢
      rwa [show (Rust.panicked s1).trace = s.trace by simp only [Rust.panicked, s1, arm64_norm]]))⟩)⟩

theorem r1a_tail_2c54 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets} {g : RunCall} {peerV : AddrV} {dir : Bytes}
    {w : CallW} {s0 s : State} {resStack : Nat} {F_heap : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hbnd : r1b_StackBounds B resStack)
    (hpanic : PanicK g s0 Qp) (hrej : FreeRejK A lim st H g s0 resStack Q Qp)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x2c54)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx22 : s.readReg64 (.gpr 22#5) = w.w5)
    (hx24 : s.readReg64 (.gpr 24#5) = w.w4)
    (htr : s0.trace <+: s.trace) (hhans : RunHistOk g.i s0 s ∧ g.a = some none) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0)
          [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
           (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗
        ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
        runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ F_heap) Q Qp (runOom s0) := by
  have hafter_dir : ∀ (st1 : M.σ) (s1 : State),
      FreeRejK A lim st1 H g s0 resStack Q Qp →
      InRunPlaced r1a_CodeOk s0 s1 0x2c68 →
      s1.readReg64 (.gpr 19#5) = g.stores →
      s0.trace <+: s1.trace →
      RunHistOk g.i s0 s1 ∧ g.a = some none →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
        (runLocals (runFsp s0)
            [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
             (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗
          ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
          runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim st1 s1 ∗ F_heap) Q Qp (runOom s0) := by
    intro st1 s1 hrej1 hb1 hx19_1 htr1 hhans1
    have hfinish : ∀ (st2 : M.σ) (s2 : State),
        FreeRejK A lim st2 H g s0 resStack Q Qp →
        InRunPlaced r1a_CodeOk s0 s2 0x2c7c →
        s2.readReg64 (.gpr 19#5) = g.stores →
        s0.trace <+: s2.trace →
        RunHistOk g.i s0 s2 ∧ g.a = some none →
        SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
          (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st2 s2 ∗
            (runLocals (runFsp s0)
                [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
                 (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗
              runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗ F_heap)) Q Qp (runOom s0) := by
      intro st2 s2 hrej2 hb2 hx19_2 htr2 hhans2
      have hk := hrej2 s2 [] FreeOnlyEvs.nil
        ⟨hb2, hx19_2, (fun h => nomatch h), htr2, hhans2.1, hhans2.2⟩
      rw [M.stepEvents_nil] at hk
      refine r1a_sepWPp_weaken_pre ?_ hk
      have hrej0 : runLocals (runFsp s0)
          [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
           (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ⊢ runLocals (runFsp s0) [] :=
        Entails.trans (r1a_locals_drop_head _ _ _ _ _ (pointsTo64_entails_memRegion _ _))
          (r1a_locals_drop_head _ _ _ _ _ (pointsTo64_entails_memRegion _ _))
      dsimp only [rejectMem]
      rw [storesAt_opened_atState, RustCliAllocBudget.atState_pool,
        show runResAt (A.atState lim st2 s2) cliWrOk g.res (some none) =
          runResAt A.repAlloc cliWrOk g.res (some none) from rfl]
      refine Entails.trans (Entails.of_eq (show _ =
        runLocals (runFsp s0)
            [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
             (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗
          F_heap ∗
          ((runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56) ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st2 s2) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hrej0 (sepConj_mono_left (entails_anyHeap F_heap))) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    have hpc1 := hb1.pc; have := hb1.spAligned_cur; have hrun1 := hb1.run; have hsp1 := hb1.sp
    rw [runPcPlaced_eq] at hpc1
    by_cases hcap0 : w.w0 = 0#64
    · apply sepWPp_seq_lscro (mid := runPcPlaced 0x2c7c) hb1.inv
      dsimp only [runProgPlaced, lsProg_579, runLocals, runLocalsFrom, BitVec.ofNat_eq_ofNat]
      rw [← hsp1]; symm at hsp1; wp_simp_pre only [sepConj_assoc]
      (iterate 2 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp1
      apply SepWP.done
        (by simp only [runPcPlaced_eq, arm64_norm, hcap0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
        (by simp only [arm64_norm, hrun1])
      intro hinv2; apply r1a_bind_sepWPp_state; intro s2
      have hpool2 : A.pool lim st1 s1 = A.pool lim st1 s2 := by simp only [s2, arm64_norm]
      (try simp only [arm64_norm]); (try rw [hsp1]); rw [r1a_group_5c]; (try rw [r1a_memRegion_zero (runFsp s0)]); rw [hpool2]
      change SepWPp _ _ s2
        (runLocals (runFsp s0)
            [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
             (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗
          ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
          runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim st1 s2 ∗ F_heap) _ _ _
      refine r1a_sepWPp_weaken_pre ?_ (hfinish st1 s2 hrej1
        ⟨by simp only [s2, runPcPlaced_eq, arm64_norm, hcap0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
         by simp only [s2, arm64_norm, hrun1], by simp only [s2, arm64_norm, hsp1],
         by simp only [s2, arm64_norm, hb1.fp], hinv2,
         by simp only [s2, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs],
         hb1.spAligned⟩
        (by simp only [s2, arm64_norm, hx19_1]) (by simpa only [s2, arm64_norm] using htr1)
        (r1a_hist_ans_step hhans1 (by simp only [s2, arm64_norm]) (by simp only [s2, arm64_norm])))
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left (r1a_ownedBytes_zero hcap0))) ?_
      rw [emp_sepConj]; exact Entails.of_eq (by sep_ac_rfl)
    · have hne0 : (w.w0 == 0#64) = false := beq_false_of_ne hcap0
      apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hb1.inv
      dsimp only [runProgPlaced, lsProg_579, runLocals, runLocalsFrom, BitVec.ofNat_eq_ofNat]
      rw [← hsp1]; symm at hsp1; wp_simp_pre only [sepConj_assoc]
      (iterate 5 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp1
      apply SepWP.done
        (by simp only [lsRustDeallocSymCli, arm64_norm, hne0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
        (by simp only [arm64_norm, hrun1])
      intro hinv_c; apply r1a_bind_sepWPp_state; intro sc
      have hpoolc : A.pool lim st1 s1 = A.pool lim st1 sc := by simp only [sc, arm64_norm]
      (try simp only [arm64_norm]); (try rw [hsp1]); rw [r1a_group_5c]; (try rw [r1a_memRegion_zero (runFsp s0)]); rw [hpoolc]
      change SepWPp _ _ sc
        (runLocals (runFsp s0)
            [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
             (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗
          ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
          runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim st1 sc ∗ F_heap) _ _ _
      refine r1a_sepWPp_weaken_pre
        (Entails.of_eq (show _ =
          ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st1 sc ∗
            (runLocals (runFsp s0)
                [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
                 (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗
              runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗ F_heap) by sep_ac_rfl))
        (r1b_call_dealloc_ownedBytes_placed hh hbnd hinv_c
          (by simp only [sc, lsRustDeallocSymCli, arm64_norm, hne0, bne, Bool.not_false, Bool.not_true, ↓reduceIte])
          (by simp only [sc, arm64_norm, hrun1]) (by simp only [sc, arm64_norm, hsp1])
          (by simp only [sc, arm64_norm, hb1.fp])
          (by simp only [sc, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs])
          hb1.spAligned
          (by simp only [sc, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
          (by simp only [sc, arm64_norm]) (by simp only [sc, arm64_norm]) (by simp only [sc, arm64_norm])
          hcap0 hpanic fun sm hbm hcsm hfsm htrm =>
            hfinish _ sm (hrej1.dealloc w.w0.toNat 1) hbm
              (by simpa only [sc, arm64_norm, hx19_1] using hcsm.1)
              (by simpa only [htrm, sc, arm64_norm] using htr1)
              (r1a_hist_ans_step hhans1 (by simpa only [sc, arm64_norm] using htrm)
                (by simpa only [sc, arm64_norm] using congrArg (·.files) hfsm)))
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp
  rw [runPcPlaced_eq] at hpc0
  by_cases hcap4 : w.w4 = 0#64
  · apply sepWPp_seq_lscro (mid := runPcPlaced 0x2c68) hbase.inv
    dsimp only [runProgPlaced, lsProg_579]
    (iterate 1 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    apply SepWP.done
      (by simp only [runPcPlaced_eq, arm64_norm, hx24, hcap4, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
      (by simp only [arm64_norm, hrun0])
    intro hinv1; apply r1a_bind_sepWPp_state; intro s1
    have hpool1 : A.pool lim st s = A.pool lim st s1 := by simp only [s1, arm64_norm]
    rw [hpool1]
    refine r1a_sepWPp_weaken_pre (sepConj_mono_right (sepConj_mono_left (r1a_ownedBytes_zero hcap4))) ?_
    rw [emp_sepConj]
    exact hafter_dir st s1 hrej
      ⟨by simp only [s1, runPcPlaced_eq, arm64_norm, hx24, hcap4, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
       by simp only [s1, arm64_norm, hrun0], by simp only [s1, arm64_norm, hsp0],
       by simp only [s1, arm64_norm, hbase.fp], hinv1,
       by simp only [s1, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs],
       hbase.spAligned⟩
      (by simp only [s1, arm64_norm, hx19]) (by simpa only [s1, arm64_norm] using htr)
      (r1a_hist_ans_step hhans (by simp only [s1, arm64_norm]) (by simp only [s1, arm64_norm]))
  · have hne4 : (w.w4 == 0#64) = false := beq_false_of_ne hcap4
    apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hbase.inv
    dsimp only [runProgPlaced, lsProg_579]
    (iterate 5 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    apply SepWP.done
      (by simp only [lsRustDeallocSymCli, arm64_norm, hx24, hne4, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
      (by simp only [arm64_norm, hrun0])
    intro hinv_c; apply r1a_bind_sepWPp_state; intro sc
    have hpoolc : A.pool lim st s = A.pool lim st sc := by simp only [sc, arm64_norm]
    rw [hpoolc]
    refine r1a_sepWPp_weaken_pre
      (Entails.of_eq (show _ =
        ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sc ∗
          (runLocals (runFsp s0)
              [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
               (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗
            ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
            runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            runSaved s0 ∗ F_heap) by sep_ac_rfl))
      (r1b_call_dealloc_ownedBytes_placed hh hbnd hinv_c
        (by simp only [sc, lsRustDeallocSymCli, arm64_norm, hx24, hne4, bne, Bool.not_false, Bool.not_true, ↓reduceIte])
        (by simp only [sc, arm64_norm, hrun0]) (by simp only [sc, arm64_norm, hsp0])
        (by simp only [sc, arm64_norm, hbase.fp])
        (by simp only [sc, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs])
        hbase.spAligned
        (by simp only [sc, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
        (by simp only [sc, arm64_norm, hx22]) (by simp only [sc, arm64_norm, hx24]) (by simp only [sc, arm64_norm])
        hcap4 hpanic fun sm hbm hcsm hfsm htrm =>
          r1a_sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (hafter_dir _ sm (hrej.dealloc w.w4.toNat 1) hbm
              (by simpa only [sc, arm64_norm, hx19] using hcsm.1)
              (by simpa only [htrm, sc, arm64_norm] using htr)
              (r1a_hist_ans_step hhans (by simpa only [sc, arm64_norm] using htrm)
                (by simpa only [sc, arm64_norm] using congrArg (·.files) hfsm))))

theorem r1a_tail_after_spe [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets} {g : RunCall} {peerV : AddrV} {dir : Bytes}
    {meG : AddrGhost} {w : CallW} {k : SpeOwned} {s0 s : State} {resStack : Nat}
    {F_heap : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hpanic : PanicK g s0 Qp) (hrej : FreeRejK A lim st H g s0 resStack Q Qp)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x2c30)
    (hx0 : s.readReg64 .x0 = runFsp s0 + 0x4d0#64)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (htr : s0.trace <+: s.trace) (hhans : RunHistOk g.i s0 s ∧ g.a = some none) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0)
          [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
           (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4),
           (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
           (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
           (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1),
           (0x4d0, 48, speOwnedAt A.repAlloc (runFsp s0 + 0x4d0#64) k)] ∗
        addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ F_heap) Q Qp (runOom s0) := by
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp
  rw [runPcPlaced_eq] at hpc0
  apply sepWPp_seq_lscro (mid := (blkPl_553).base) hbase.inv
  dsimp only [runProgPlaced, lsProg_579]
  (iterate 1 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, hrun0])
  intro hinv_c; apply r1a_bind_sepWPp_state; intro sc0
  have hpool0 : A.pool lim st s = A.pool lim st sc0 := by simp only [sc0, arm64_norm]
  rw [hpool0]
  let cs5 :=
    [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
     (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4),
     (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
     (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
     (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)]
  have hfoc := r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (speOwnedAt A.repAlloc (runFsp s0 + 0x4d0#64) k) []
  refine r1a_sepWPp_weaken_pre
    (Entails.of_eq (by
      dsimp only [cs5] at hfoc ⊢; simp only [List.cons_append, List.nil_append] at hfoc
      rw [hfoc]
      show _ = speOwnedAt A.repAlloc (runFsp s0 + 0x4d0#64) k ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sc0 ∗
        (r1a_localsCtx (runFsp s0) 0 cs5 0x4d0 48 [] ∗
          addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
          ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ F_heap)
      sep_ac_rfl))
    (r1b_call_dropSpeOwned_placed (retOff := 0x2c34) hh hdrop hbnd hinv_c
      (by simp only [sc0, arm64_norm]) (by simp only [sc0, arm64_norm, hrun0])
      (by simp only [sc0, arm64_norm, hsp0]) (by simp only [sc0, arm64_norm, hbase.fp])
      (by simp only [sc0, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs])
      hbase.spAligned
      (by simp only [sc0, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
      (by simp only [sc0, arm64_norm, hx0]) hpanic ?_)
  intro s1 evs_d hevs_d hb1 hcs1 hfiles1 htr1
  let st1 := M.stepEvents evs_d st
  have hrej1 : FreeRejK A lim st1 H g s0 resStack Q Qp := hrej.step hevs_d
  have hx19_1 : s1.readReg64 (.gpr 19#5) = g.stores := by simpa only [sc0, arm64_norm, hx19] using hcs1.1
  have hx20_1 : s1.readReg64 (.gpr 20#5) = g.res := by simpa only [sc0, arm64_norm, hx20] using hcs1.2.1
  have hx21_1 : s1.readReg64 (.gpr 21#5) = meG.name.cap := by simpa only [sc0, arm64_norm, hx21] using hcs1.2.2.1
  have htr_01 : s0.trace <+: s1.trace := by simpa only [htr1, sc0, arm64_norm] using htr
  have hhans1 := r1a_hist_ans_step hhans (by simpa only [sc0, arm64_norm] using htr1)
    (by simpa only [sc0, arm64_norm] using hfiles1)
  clear hpc0 hrun0 hsp0 hinv_c hcs1 htr1 hfiles1 hfoc hpool0
  have hfoc' := (r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (memRegion (runFsp s0 + 0x4d0#64) 48) []).symm
  have hres_split : memRegion g.res runResSize =
      (∃∗ r0 : BitVec 64, g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    rw [← ProofLib.memRegion_eight g.res]; exact ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide)
  have hre : memRegion (runFsp s0 + 0x4d0#64) 48 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
      A.pool lim st1 s1 ∗
      (r1a_localsCtx (runFsp s0) 0 cs5 0x4d0 48 [] ∗
        addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ F_heap) =
    (memRegion (runFsp s0 + 0x4d0#64) 48 ∗ r1a_localsCtx (runFsp s0) 0 cs5 0x4d0 48 []) ∗
      memRegion g.res runResSize ∗ addrNameHeap A.repAlloc meG ∗
      ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗ ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
      memRegion g.call 56 ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
      A.pool lim st1 s1 ∗ F_heap := by sep_ac_rfl
  change SepWPp _ _ s1
    (memRegion (runFsp s0 + 0x4d0#64) 48 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
      A.pool lim st1 s1 ∗ _) _ _ _
  rw [hre, hfoc', hres_split]
  refine r1a_sepWPp_weaken_pre (sepConj_mono_left (r1a_locals_drop_mid (runFsp s0) cs5 0x4d0 48 _ [] (Entails.refl _))) ?_
  dsimp only [cs5]; simp only [List.append_nil, sepExists_sepConj_left, sepExists_sepConj_right]
  apply r1a_sepWPp_exists_pre; intro r0
  have hdrop3 : runLocals (runFsp s0) cs5 ⊢
      runLocals (runFsp s0)
        [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
         (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] :=
    Entails.trans (r1a_locals_drop_head _ _ _ _ _ (pointsTo64_entails_memRegion _ _))
      (Entails.trans (r1a_locals_drop_head _ _ _ _ _ (pointsTo64_entails_memRegion _ _))
        (r1a_locals_drop_head _ _ _ _ _ (pointsTo64_entails_memRegion _ _)))
  have hpc1 := hb1.pc; have := hb1.spAligned_cur; have hrun1 := hb1.run; have hsp1 := hb1.sp
  rw [runPcPlaced_eq] at hpc1
  by_cases hme0 : meG.name.cap = 0#64
  · apply sepWPp_seq_lscro (mid := runPcPlaced 0x2c54) hb1.inv
    dsimp only [runProgPlaced, lsProg_579, cs5, runLocals, runLocalsFrom, BitVec.ofNat_eq_ofNat]
    by_vm_open (
      rw [← hsp1, ← hx20_1]; symm at hsp1 hx20_1; wp_simp_pre only [sepConj_assoc]
      (iterate 4 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp1 hx20_1
      refine SepWP.done
        (by simp only [runPcPlaced_eq, arm64_norm, hx21_1, hme0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
        (by simp only [arm64_norm, hrun1])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv2 => ?_⟩
      apply r1a_bind_sepWPp_state; intro s2
      have hpool2 : A.pool lim st1 s1 = A.pool lim st1 s2 := (A.pool_of_vmPreserved hvm).symm
      (try simp only [arm64_norm, hx20_1]); (try rw [hsp1]); rw [r1a_group_11_2]; (try rw [r1a_memRegion_zero (runFsp s0)]); rw [hpool2]
      change SepWPp _ _ s2
        (runLocals (runFsp s0) cs5 ∗ ((g.res ↦₆₄ -1#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
          addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
          ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim st1 s2 ∗ F_heap) _ _ _
      refine r1a_sepWPp_weaken_pre ?_
        (r1a_tail_2c54 (peerV := peerV) (dir := dir) (w := w) (F_heap := F_heap)
          hh hbnd hpanic hrej1
          ⟨by simp only [s2, runPcPlaced_eq, arm64_norm, hx21_1, hme0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
           by simp only [s2, arm64_norm, hrun1], by simp only [s2, arm64_norm, hsp1],
           by simp only [s2, arm64_norm, hb1.fp], hinv2,
           by simp only [s2, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs],
           hb1.spAligned⟩
          (by simp only [s2, arm64_norm, hx19_1]) (by simp only [s2, arm64_norm]) (by simp only [s2, arm64_norm])
          (by simpa only [s2, arm64_norm] using htr_01)
          (r1a_hist_ans_step hhans1 (by simp only [s2, arm64_norm]) (by simp only [s2, arm64_norm])))
      dsimp only [runResAt]
      refine Entails.trans (sepConj_mono hdrop3 (sepConj_mono_right (sepConj_mono_left (r1a_addrNameHeap_zero hme0)))) ?_
      rw [emp_sepConj]; exact Entails.of_eq (by sep_ac_rfl)
    )
  · have hne_me : (meG.name.cap == 0#64) = false := beq_false_of_ne hme0
    apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hb1.inv
    dsimp only [runProgPlaced, lsProg_579, cs5, runLocals, runLocalsFrom, BitVec.ofNat_eq_ofNat]
    by_vm_open (
      rw [← hsp1, ← hx20_1]; symm at hsp1 hx20_1; wp_simp_pre only [sepConj_assoc]
      (iterate 8 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp1 hx20_1
      refine SepWP.done
        (by simp only [lsRustDeallocSymCli, arm64_norm, hx21_1, hne_me, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
        (by simp only [arm64_norm, hrun1])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c => ?_⟩
      apply r1a_bind_sepWPp_state; intro sc
      have hpoolc : A.pool lim st1 s1 = A.pool lim st1 sc := (A.pool_of_vmPreserved hvm).symm
      (try simp only [arm64_norm, hx20_1]); (try rw [hsp1]); rw [r1a_group_11_2]; (try rw [r1a_memRegion_zero (runFsp s0)]); rw [hpoolc]
      change SepWPp _ _ sc
        (runLocals (runFsp s0) cs5 ∗ ((g.res ↦₆₄ -1#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
          addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
          ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim st1 sc ∗ F_heap) _ _ _
      rw [r1a_addrNameHeap_eq_owned meG]
      refine r1a_sepWPp_weaken_pre
        (Entails.of_eq (show _ = ownedBytes A.repAlloc meG.name.cap meG.name.ptr (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st1 sc ∗
            (runLocals (runFsp s0) cs5 ∗ runResAt A.repAlloc cliWrOk g.res (some none) ∗
              ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗ ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
              memRegion g.call 56 ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
              (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ F_heap) by
          dsimp only [runResAt]
          sep_ac_rfl))
        (r1b_call_dealloc_ownedBytes_placed (retOff := 0x2c54) hh hbnd hinv_c
          (by simp only [sc, lsRustDeallocSymCli, arm64_norm, hx21_1, hne_me, bne, Bool.not_false, Bool.not_true, ↓reduceIte])
          (by simp only [sc, arm64_norm, hrun1]) (by simp only [sc, arm64_norm, hsp1])
          (by simp only [sc, arm64_norm, hb1.fp])
          (by simp only [sc, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs])
          hbase.spAligned
          (by simp only [sc, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
          (by simp only [sc, arm64_norm]) (by simp only [sc, arm64_norm, hx21_1]) (by simp only [sc, arm64_norm])
          hme0 hpanic fun sm hbm hcsm hfsm htrm =>
            r1a_sepWPp_weaken_pre
              (Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hdrop3)))
                (Entails.of_eq (by sep_ac_rfl)))
              (r1a_tail_2c54 (peerV := peerV) (dir := dir) (w := w) (F_heap := F_heap)
                hh hbnd hpanic (hrej1.dealloc meG.name.cap.toNat 1) hbm
                (by simpa only [sc, arm64_norm, hx19_1] using hcsm.1)
                (by simpa only [sc, arm64_norm] using hcsm.2.2.2.1)
                (by simpa only [sc, arm64_norm] using hcsm.2.2.2.2.2.1)
                (by simpa only [htrm, sc, arm64_norm] using htr_01)
                (r1a_hist_ans_step hhans1 (by simpa only [sc, arm64_norm] using htrm)
                  (by simpa only [sc, arm64_norm] using congrArg (·.files) hfsm))))
    )

theorem r1a_me_none [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets} {g : RunCall} {peerV : AddrV} {dir : Bytes}
    {w : CallW} {s0 s : State} {resStack : Nat} {F_heap : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hbnd : r1b_StackBounds B resStack)
    (hpanic : PanicK g s0 Qp) (hrej : FreeRejK A lim st H g s0 resStack Q Qp)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x860)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx22 : s.readReg64 (.gpr 22#5) = w.w5)
    (hx24 : s.readReg64 (.gpr 24#5) = w.w4)
    (htr : s0.trace <+: s.trace) (hhans : RunHistOk g.i s0 s ∧ g.a = some none) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0)
          [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
           (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] ∗
        ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ F_heap) Q Qp (runOom s0) := by
  have hres_split : memRegion g.res runResSize =
      (∃∗ r0 : BitVec 64, g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    rw [← ProofLib.memRegion_eight g.res]; exact ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide)
  rw [hres_split]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r1a_sepWPp_exists_pre; intro r0
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run
  change s.pc = (blkPl_579).base + 2144#64 at hpc0
  apply sepWPp_seq_lscro (mid := runPcPlaced 0x2c54) hbase.inv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    refine SepWP.done
      (by simp only [runPcPlaced_eq, arm64_norm, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
      (by simp only [arm64_norm, hrun0])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
    apply r1a_bind_sepWPp_state; intro s1
    have hpool1 : A.pool lim st s = A.pool lim st s1 := (A.pool_of_vmPreserved hvm).symm
    rw [hpool1]
    exact r1a_sepWPp_weaken_pre (by dsimp only [runResAt]; exact Entails.of_eq (by sep_ac_rfl))
      (r1a_tail_2c54 (peerV := peerV) (dir := dir) (w := w) (F_heap := F_heap)
        hh hbnd hpanic hrej
        ⟨by simp only [s1, runPcPlaced_eq, arm64_norm, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
         by simp only [s1, arm64_norm, hrun0], by simp only [s1, arm64_norm, hbase.sp],
         by simp only [s1, arm64_norm, hbase.fp], hinv1,
         by simp only [s1, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs],
         hbase.spAligned⟩
        (by simp only [s1, arm64_norm, hx19]) (by simp only [s1, arm64_norm, hx22]) (by simp only [s1, arm64_norm, hx24])
        (by simpa only [s1, arm64_norm] using htr)
        (r1a_hist_ans_step hhans (by simp only [s1, arm64_norm]) (by simp only [s1, arm64_norm])))
  )

theorem r1a_free_path_6e0 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets} {g : RunCall} {s0 s : State} {resStack : Nat}
    {pathCap pathPtr : BitVec 64} {pathBs : Bytes} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hbnd : r1b_StackBounds B resStack)
    (hpanic : PanicK g s0 Qp) (hne : pathCap ≠ 0)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x6e0)
    (hx1 : s.readReg64 .x1 = pathCap) (hx26 : s.readReg64 (.gpr 26#5) = pathPtr)
    (hk : ∀ sm : State, InRunPlaced r1a_CodeOk s0 sm 0x6f4 →
      sm.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) →
      sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) →
      sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      sm.trace = s.trace → sm.fs.files = s.fs.files →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sm
        (stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents pathCap.toNat 1) st) sm ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ F) Q Qp (runOom s0) := by
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run
  change s.pc = (blkPl_579).base + 1760#64 at hpc0
  apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hbase.inv
  dsimp only [runProgPlaced, lsProg_579]
  (iterate 4 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [lsRustDeallocSymCli, arm64_norm]) (by simp only [arm64_norm, hrun0])
  intro hinv_c; apply r1a_bind_sepWPp_state; intro sc
  have hpoolc : A.pool lim st s = A.pool lim st sc := by simp only [sc, arm64_norm]
  rw [hpoolc]
  refine r1b_call_dealloc_ownedBytes_placed (retOff := 0x6f0) hh hbnd hinv_c
    (by simp only [sc, lsRustDeallocSymCli, arm64_norm])
    (by simp only [sc, arm64_norm, hrun0]) (by simp only [sc, arm64_norm, hbase.sp])
    (by simp only [sc, arm64_norm, hbase.fp])
    (by simp only [sc, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs])
    hbase.spAligned
    (by simp only [sc, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
    (by simp only [sc, arm64_norm, hx26]) (by simp only [sc, arm64_norm, hx1]) (by simp only [sc, arm64_norm])
    hne hpanic fun s1 hb1 hcs1 hfs1 htr1 => ?_
  have hx26_1 : s1.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 12#5) := by
    simpa only [sc, arm64_norm] using hcs1.2.2.2.2.2.2.2.1
  have hpc1 := hb1.pc; have := hb1.spAligned_cur; have hrun1 := hb1.run
  change s1.pc = (blkPl_579).base + 1776#64 at hpc1
  apply sepWPp_seq_lscro (mid := runPcPlaced 0x6f4) hb1.inv
  dsimp only [runProgPlaced, lsProg_579]
  (iterate 1 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done
    (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
    (by simp only [arm64_norm, hrun1])
  intro hinv2; apply r1a_bind_sepWPp_state; intro s2
  have hpool2 :
      A.pool lim (M.stepEvents (rustDeallocEvents pathCap.toNat 1) st) s1 =
        A.pool lim (M.stepEvents (rustDeallocEvents pathCap.toNat 1) st) s2 := by
    simp only [s2, arm64_norm]
  rw [hpool2]
  exact hk s2
    ⟨by simp only [s2, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
     by simp only [s2, arm64_norm, hrun1], by simp only [s2, arm64_norm, hb1.sp],
     by simp only [s2, arm64_norm, hb1.fp], hinv2,
     by simp only [s2, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs],
     hb1.spAligned⟩
    (by simp only [s2, arm64_norm, hx26_1])
    (by simpa only [s2, sc, arm64_norm] using hcs1.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.2.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.2.2.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using htr1)
    (by simpa only [s2, sc, arm64_norm] using congrArg (·.files) hfs1)

theorem r1a_spe_pack_plain [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets} {g : RunCall} {peerV : AddrV} {dir : Bytes}
    {meG : AddrGhost} {w : CallW} {i : Nat} {s0 s : State} {resStack : Nat}
    {F_heap : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hpanic : PanicK g s0 Qp) (hrej : FreeRejK A lim st H g s0 resStack Q Qp)
    (hi : PlainSpeTag i) (hbase : InRunPlaced r1a_CodeOk s0 s 0x2bf0)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord i)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (htr : s0.trace <+: s.trace) (hhans : RunHistOk g.i s0 s ∧ g.a = some none) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0)
          [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
           (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4),
           (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
           (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
           (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1),
           (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)] ∗
        addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ F_heap) Q Qp (runOom s0) := by
  let cs5 :=
    [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
     (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4),
     (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
     (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
     (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)]
  have hfoc := r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (memRegion (runFsp s0 + 0x4d0#64) 48) []
  (try rw [r1a_memRegion_zero (runFsp s0)])
  change SepWPp _ _ _ (runLocals (runFsp s0) (cs5 ++ [(0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]) ∗ _) _ _ _
  rw [hfoc]
  refine r1a_sepWPp_weaken_pre (sepConj_mono_left (sepConj_mono_left (r1a_memRegion48_words (runFsp s0 + 0x4d0#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r1a_sepWPp_exists_pre; intro s0w; apply r1a_sepWPp_exists_pre; intro s1w
  apply r1a_sepWPp_exists_pre; intro s2w; apply r1a_sepWPp_exists_pre; intro s3w
  apply r1a_sepWPp_exists_pre; intro s4w; apply r1a_sepWPp_exists_pre; intro s5w
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp
  rw [runPcPlaced_eq] at hpc0
  apply sepWPp_seq_lscro (mid := runPcPlaced 0x2c30) hbase.inv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    rw [← hsp0]; symm at hsp0
    wp_simp_pre only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    (iterate 16 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    symm at hsp0
    refine SepWP.done
      (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
      (by simp only [arm64_norm, hrun0])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
    apply r1a_bind_sepWPp_state; intro s1
    have hpool1 : A.pool lim st s = A.pool lim st s1 := (A.pool_of_vmPreserved hvm).symm
    (try simp only [arm64_norm, hx12]); (try rw [hsp0]); rw [r1a_group6c, hpool1]
    refine r1a_sepWPp_weaken_pre ?_
      (r1a_tail_after_spe (peerV := peerV) (dir := dir) (meG := meG) (w := w) (k := .plain i hi) (F_heap := F_heap)
        hh hdrop hbnd hpanic hrej
        ⟨by simp only [runPcPlaced_eq, arm64_norm, s1, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
         by simp only [arm64_norm, s1, hrun0], by simp only [arm64_norm, s1, hsp0],
         by simp only [arm64_norm, s1, hbase.fp], hinv1,
         by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hbase.vregs],
         hbase.spAligned⟩
        (by simp only [arm64_norm, s1, hsp0]) (by simp only [arm64_norm, s1, hx19])
        (by simp only [arm64_norm, s1, hx20]) (by simp only [arm64_norm, s1, hx21])
        (by simpa only [arm64_norm, s1] using htr)
        (r1a_hist_ans_step hhans (by simp only [arm64_norm, s1]) (by simp only [arm64_norm, s1])))
    have hfoc' := (r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (speOwnedAt A.repAlloc (runFsp s0 + 0x4d0#64) (.plain i hi)) []).symm
    change _ ⊢ runLocals (runFsp s0) (cs5 ++ [(0x4d0, 48, speOwnedAt A.repAlloc (runFsp s0 + 0x4d0#64) (.plain i hi))]) ∗ _
    rw [← hfoc']; dsimp only [speOwnedAt]
    have hw40 := r1a_words5_to_memRegion40 (runFsp s0 + 0x4d0#64)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] at hw40 ⊢
    exact sepConj_mono_left (sepConj_mono_left (sepConj_mono_right (hw40 _ _ _ _ _)))
  )

theorem r1a_decode_err [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets} {g : RunCall} {peerV : AddrV} {dir ikB : Bytes}
    {meG : AddrGhost} {w : CallW} {ikCap ikPtr : BitVec 64} {i : Nat} {s0 s : State}
    {resStack : Nat} {F_heap : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hpanic : PanicK g s0 Qp) (hrej : FreeRejK A lim st H g s0 resStack Q Qp)
    (hi : PlainSpeTag i) (hbase : InRunPlaced r1a_CodeOk s0 s 0x8f0)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord i)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx25 : s.readReg64 (.gpr 25#5) = ikCap)
    (hx27 : s.readReg64 (.gpr 27#5) = ikPtr)
    (htr : s0.trace <+: s.trace) (hhans : RunHistOk g.i s0 s ∧ g.a = some none) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0)
          [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
           (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4),
           (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
           (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
           (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1),
           (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)] ∗
        ownedBytes A.repAlloc ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB ∗
        addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ F_heap) Q Qp (runOom s0) := by
  let cs5 :=
    [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
     (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4),
     (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
     (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
     (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)]
  have hf4d0 := r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (memRegion (runFsp s0 + 0x4d0#64) 48) []
  (try rw [r1a_memRegion_zero (runFsp s0)])
  change SepWPp _ _ _ (runLocals (runFsp s0) (cs5 ++ [(0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]) ∗ _) _ _ _
  rw [hf4d0]
  refine r1a_sepWPp_weaken_pre (sepConj_mono_left (sepConj_mono_left (r1a_memRegion48_words (runFsp s0 + 0x4d0#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r1a_sepWPp_exists_pre; intro d0; apply r1a_sepWPp_exists_pre; intro d1
  apply r1a_sepWPp_exists_pre; intro d2; apply r1a_sepWPp_exists_pre; intro d3
  apply r1a_sepWPp_exists_pre; intro d4; apply r1a_sepWPp_exists_pre; intro d5
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp
  change s.pc = (blkPl_579).base + 2288#64 at hpc0
  by_cases hik0 : ikCap = 0#64
  · apply sepWPp_seq_lscro (mid := runPcPlaced 0xcdc) hbase.inv
    dsimp only [runProgPlaced, lsProg_579]; rw [← hsp0]; symm at hsp0
    wp_simp_pre only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    (iterate 7 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    symm at hsp0
    apply SepWP.done
      (by simp only [runPcPlaced_eq, arm64_norm, hx25, hik0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
      (by simp only [arm64_norm, hrun0])
    intro hinv1; apply r1a_bind_sepWPp_state; intro s1
    have hpool1 : A.pool lim st s = A.pool lim st s1 := by simp only [s1, arm64_norm]
    (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group6c, hpool1]
    have hb1 : InRunPlaced r1a_CodeOk s0 s1 0xcdc :=
      ⟨by simp only [runPcPlaced_eq, arm64_norm, s1, hx25, hik0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
       by simp only [arm64_norm, s1, hrun0], by simp only [arm64_norm, s1, hsp0],
       by simp only [arm64_norm, s1, hbase.fp], hinv1,
       by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hbase.vregs],
       hbase.spAligned⟩
    have hpc1 := hb1.pc; have := hb1.spAligned_cur; have hrun1 := hb1.run
    change s1.pc = (blkPl_579).base + 3292#64 at hpc1
    apply sepWPp_seq_lscro (mid := runPcPlaced 0x2bf0) hb1.inv
    try dsimp only [runProgPlaced, lsProg_579]
    (iterate 4 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    apply SepWP.done
      (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
      (by simp only [arm64_norm, hrun1])
    intro hinv2; apply r1a_bind_sepWPp_state; intro s2
    have hpool2 : A.pool lim st s1 = A.pool lim st s2 := by simp only [s2, arm64_norm]
    rw [hpool2]
    refine r1a_sepWPp_weaken_pre ?_
      (r1a_spe_pack_plain (peerV := peerV) (dir := dir) (meG := meG) (w := w) (F_heap := F_heap)
        hh hdrop hbnd hpanic hrej hi
        ⟨by simp only [s2, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
         by simp only [s2, arm64_norm, hrun1], by simp only [s2, arm64_norm, hb1.sp],
         by simp only [s2, arm64_norm, hb1.fp], hinv2,
         by simp only [s2, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs],
         hb1.spAligned⟩
        (by simp only [s2, arm64_norm, s1, hx12]) (by simp only [s2, arm64_norm, s1, hx19])
        (by simp only [s2, arm64_norm, s1, hx20]) (by simp only [s2, arm64_norm, s1, hx21])
        (by simpa only [s2, arm64_norm, s1] using htr)
        (r1a_hist_ans_step hhans (by simp only [s2, arm64_norm, s1]) (by simp only [s2, arm64_norm, s1])))
    have hw48 : ((runFsp s0 + 0x4d0#64) ↦₆₄ d0) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ d1) ∗
        ((runFsp s0 + 0x4e0#64) ↦₆₄ d2) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ d3) ∗
        ((runFsp s0 + 0x4f0#64) ↦₆₄ d4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ d5) ⊢
          memRegion (runFsp s0 + 0x4d0#64) 48 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1a_words6_to_memRegion48 (runFsp s0 + 0x4d0#64) d0 d1 d2 d3 d4 d5
    refine Entails.trans (sepConj_mono (sepConj_mono_left hw48) (sepConj_mono_left (r1a_ownedBytes_zero hik0))) ?_
    rw [← hf4d0, emp_sepConj]; exact Entails.refl _
  · have hne_ik : (ikCap == 0#64) = false := beq_false_of_ne hik0
    have hw48 : ((runFsp s0 + 0x4d0#64) ↦₆₄ d0) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ d1) ∗
        ((runFsp s0 + 0x4e0#64) ↦₆₄ d2) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ d3) ∗
        ((runFsp s0 + 0x4f0#64) ↦₆₄ d4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ d5) ⊢
          memRegion (runFsp s0 + 0x4d0#64) 48 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1a_words6_to_memRegion48 (runFsp s0 + 0x4d0#64) d0 d1 d2 d3 d4 d5
    have h32 : memRegion (runFsp s0 + 0x198#64) 32 =
        (∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64,
          ((runFsp s0 + 0x198#64) ↦₆₄ t0) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ t1) ∗
          ((runFsp s0 + 0x1a8#64) ↦₆₄ t2) ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ t3)) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1a_memRegion32_eq_words (runFsp s0 + 0x198#64)
    apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hbase.inv
    have hctx_open : r1a_localsCtx (runFsp s0) 0 cs5 0x4d0 48 [] =
        memRegion (runFsp s0 + 0x198#64) 32 ∗ memRegion (runFsp s0) 0x198 ∗
          r1a_localsCtx (runFsp s0) 0x1b8 cs5 0x4d0 48 [] := by
      dsimp only [cs5, r1a_localsCtx, BitVec.ofNat_eq_ofNat]
      have hs := ProofLib.memRegion_split (runFsp s0 + 0#64) 0x198 32 (by decide)
      simp only [BitVec.add_zero, Nat.sub_self, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp] at hs ⊢
      rw [hs]; sep_ac_rfl
    rw [hctx_open, h32]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_left; intro t0; apply SepWP.exists_left; intro t1
    apply SepWP.exists_left; intro t2; apply SepWP.exists_left; intro t3
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      rw [← hsp0]; symm at hsp0
      wp_simp_pre only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      (iterate 24 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp0
      refine SepWP.done
        (by simp only [lsRustDeallocSymCli, arm64_norm, hx25, hne_ik, bne, Bool.not_false, Bool.not_true, ↓reduceIte])
        (by simp only [arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c => ?_⟩
      apply r1a_bind_sepWPp_state; intro sc
      have hpoolc : A.pool lim st s = A.pool lim st sc := (A.pool_of_vmPreserved hvm).symm
      (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group6_4, hpoolc]
      have hex4 : ∀ (a b c d : BitVec 64),
          ((runFsp s0 + 0x198#64) ↦₆₄ a) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ b) ∗
            ((runFsp s0 + 0x1a8#64) ↦₆₄ c) ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ d) ⊢
            ∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64,
              ((runFsp s0 + 0x198#64) ↦₆₄ q0) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ q1) ∗
              ((runFsp s0 + 0x1a8#64) ↦₆₄ q2) ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ q3) :=
        fun a b c d => Entails.sepExists_right a (Entails.sepExists_right b
          (Entails.sepExists_right c (Entails.sepExists_right d (Entails.refl _))))
      refine r1a_sepWPp_weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (hex4 _ _ _ _)))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply r1a_sepWPp_exists_pre; intro t0'; apply r1a_sepWPp_exists_pre; intro t1'
      apply r1a_sepWPp_exists_pre; intro t2'; apply r1a_sepWPp_exists_pre; intro t3'
      refine r1a_sepWPp_weaken_pre
        (Entails.of_eq (show _ =
          ownedBytes A.repAlloc ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sc ∗
            ((((runFsp s0 + 0x4d0#64) ↦₆₄ d0) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ d1) ∗
                ((runFsp s0 + 0x4e0#64) ↦₆₄ d2) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ d3) ∗
                ((runFsp s0 + 0x4f0#64) ↦₆₄ d4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ d5)) ∗
              (((runFsp s0 + 0x198#64) ↦₆₄ t0') ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ t1') ∗
                ((runFsp s0 + 0x1a8#64) ↦₆₄ t2') ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ t3')) ∗
              memRegion (runFsp s0) 0x198 ∗ r1a_localsCtx (runFsp s0) 0x1b8 cs5 0x4d0 48 [] ∗
              addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
              ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗ F_heap) by sep_ac_rfl))
        (r1b_call_dealloc_ownedBytes_placed (retOff := 0x950) hh hbnd hinv_c
          (by simp only [lsRustDeallocSymCli, arm64_norm, sc, hx25, hne_ik, bne, Bool.not_false, Bool.not_true, ↓reduceIte])
          (by simp only [arm64_norm, sc, hrun0]) (by simp only [arm64_norm, sc, hsp0])
          (by simp only [arm64_norm, sc, hbase.fp])
          (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, sc, hbase.vregs])
          hbase.spAligned
          (by simp only [runPcPlaced_eq, arm64_norm, sc, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
          (by simp only [arm64_norm, sc, hx27]) (by simp only [arm64_norm, sc, hx25]) (by simp only [arm64_norm, sc])
          hik0 hpanic fun sm hbm hcsm hfsm htrm => ?_)
      let stm := M.stepEvents (rustDeallocEvents ikCap.toNat 1) st
      have hrejm : FreeRejK A lim stm H g s0 resStack Q Qp := hrej.dealloc ikCap.toNat 1
      have hx19_m : sm.readReg64 (.gpr 19#5) = g.res := by simpa only [arm64_norm, sc, hx20] using hcsm.1
      have hx20_m : sm.readReg64 (.gpr 20#5) = meG.name.cap := by simpa only [arm64_norm, sc, hx21] using hcsm.2.1
      have hx22_m : sm.readReg64 (.gpr 22#5) = g.stores := by simpa only [arm64_norm, sc, hx19] using hcsm.2.2.2.1
      have hx27_m : sm.readReg64 (.gpr 27#5) = speWord i := by simpa only [arm64_norm, sc, hx12] using hcsm.2.2.2.2.2.2.2.2.1
      have htr_0m : s0.trace <+: sm.trace := by simpa only [htrm, arm64_norm, sc] using htr
      have hhans_m := r1a_hist_ans_step hhans (by simpa only [arm64_norm, sc] using htrm)
        (by simpa only [arm64_norm, sc] using congrArg (·.files) hfsm)
      have hpcm := hbm.pc; have := hbm.spAligned_cur; have hrunm := hbm.run; have hspm := hbm.sp
      change sm.pc = (blkPl_579).base + 2384#64 at hpcm
      apply sepWPp_seq_lscro (mid := runPcPlaced 0x2bf0) hbm.inv
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        rw [← hspm]; symm at hspm; wp_simp_pre only [sepConj_assoc]
        (iterate 13 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
        symm at hspm
        refine SepWP.done
          (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
          (by simp only [arm64_norm, hrunm])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm2 hinv2 => ?_⟩
        apply r1a_bind_sepWPp_state; intro s2
        have hpool2 : A.pool lim stm sm = A.pool lim stm s2 := (A.pool_of_vmPreserved hvm2).symm
        (try simp only [arm64_norm]); (try rw [hspm, hpool2])
        refine r1a_sepWPp_weaken_pre ?_
          (r1a_spe_pack_plain (peerV := peerV) (dir := dir) (meG := meG) (w := w) (F_heap := F_heap)
            hh hdrop hbnd hpanic hrejm hi
            ⟨by simp only [s2, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
             by simp only [s2, arm64_norm, hrunm], by simp only [s2, arm64_norm, hspm],
             by simp only [s2, arm64_norm, hbm.fp], hinv2,
             by simp only [s2, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbm.vregs],
             hbm.spAligned⟩
            (by simp only [s2, arm64_norm, hx27_m]) (by simp only [s2, arm64_norm, hx22_m])
            (by simp only [s2, arm64_norm, hx19_m]) (by simp only [s2, arm64_norm, hx20_m])
            (by simpa only [s2, arm64_norm] using htr_0m)
            (r1a_hist_ans_step hhans_m (by simp only [s2, arm64_norm]) (by simp only [s2, arm64_norm])))
        have hm32 : ((runFsp s0 + 0x198#64) ↦₆₄ t0') ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ t1') ∗
            ((runFsp s0 + 0x1a8#64) ↦₆₄ t2') ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ t3') ⊢
              memRegion (runFsp s0 + 0x198#64) 32 := by
          rw [h32]
          exact Entails.sepExists_right t0' (Entails.sepExists_right t1'
            (Entails.sepExists_right t2' (Entails.sepExists_right t3' (Entails.refl _))))
        refine Entails.trans (Entails.of_eq (show _ =
          (((runFsp s0 + 0x4d0#64) ↦₆₄ d0) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ d1) ∗
              ((runFsp s0 + 0x4e0#64) ↦₆₄ d2) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ d3) ∗
              ((runFsp s0 + 0x4f0#64) ↦₆₄ d4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ d5)) ∗
            ((((runFsp s0 + 0x198#64) ↦₆₄ t0') ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ t1') ∗
                ((runFsp s0 + 0x1a8#64) ↦₆₄ t2') ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ t3')) ∗
              memRegion (runFsp s0) 0x198 ∗ r1a_localsCtx (runFsp s0) 0x1b8 cs5 0x4d0 48 []) ∗
            addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
            ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
            A.pool lim stm s2 ∗ F_heap by sep_ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hw48 (sepConj_mono_left (sepConj_mono_left hm32))) ?_
        rw [← hctx_open, ← sepConj_assoc, ← hf4d0]; exact Entails.refl _
      )
    )

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
