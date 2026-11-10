/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudget
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded `signal_session::run` Arm `R3b`: `decrypt_prekey` `Ok` Tail Lemmas

Proves `r3b_recvP_from_dcc_placed` (`R+0xdcc → R+0xf8c`) and `r3b_recvP_dec_ok_placed`
(`R+0xd94 → R+0xf8c` `AtJoinPlaced`), along with `_any` and `_codeOk` variants, with deterministic
`r3bFreeMePeerEvs` deallocation event threading under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost okTagVec protocolAddressAt vecResultAt)
open CryptoVerification.RustHeap (LayoutOk vecU8)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliWrOk inputOf namedWrites runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Bytes InRunPlaced R3bCodeOk RunHistOk addrNameHeap addrUpperAt addrUpperAt_entails_memRegion
   decResAt protocolAddressAt_eq_parts r3b_calleeSavedVRegs_q0 r3b_calleeSavedVRegs_q1
   r3b_calleeSavedVRegs_q2 r3b_calleeSavedVRegs_setMem r3b_calleeSavedVRegs_setPC
   r3b_calleeSavedVRegs_setPState r3b_calleeSavedVRegs_writeReg64 r3b_extractLsb_append_hi
   r3b_extractLsb_append_lo r3b_fs_setMem r3b_fs_setPC r3b_fs_setPState r3b_fs_writeReg64
   r3b_fs_writeVReg128 r3b_hist_of_eq r3b_inRun_step r3b_mem_setPState r3b_nameHeap_dealloc
   r3b_nameHeap_zero r3b_perm r3b_perm_post r3b_readReg64_setPState r3b_sepWPp_exists_left
   r3b_sepWPp_pure_left r3b_sepWPp_weaken_pre r3b_sp_setPState r3b_split_at r3b_stOf
   r3b_stackAt_split_ge r3b_status_setPState r3b_symtab_setPState r3b_trace_setPState
   r3b_vecHeap r3b_vecHeap_cap_lt r3b_vecU8At_eq r3b_words4_entails_mem32 runFsp runLocalBytes
   runPcPlaced runPcPlaced_eq runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunSkeleton (runFrame)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudgetAux

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget
  (r3bFreeCapEvs r3bFreeMePeerEvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget
  (r3b_call_lscro r3b_dealloc_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudget
  (r3b_recvP_from_de0_placed r3b_sepWP_with_vm_oom r3b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlaced JoinKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)

scoped syntax "by_vm_open " tacticSeq : tactic
scoped elab_rules : tactic
  | `(tactic| by_vm_open $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply r3b_sepWP_with_vm_oom))
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
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm]
  runPcPlaced_eq BitVec.ofNat_eq_ofNat
  r3b_extractLsb_append_lo r3b_extractLsb_append_hi
  r3b_calleeSavedVRegs_q0 r3b_calleeSavedVRegs_q1 r3b_calleeSavedVRegs_q2
  r3b_calleeSavedVRegs_writeReg64
  r3b_calleeSavedVRegs_setPC r3b_calleeSavedVRegs_setMem r3b_calleeSavedVRegs_setPState
  r3b_readReg64_setPState r3b_sp_setPState r3b_mem_setPState r3b_status_setPState
  r3b_trace_setPState r3b_symtab_setPState r3b_fs_setPState
  r3b_fs_writeReg64 r3b_fs_writeVReg128 r3b_fs_setPC r3b_fs_setMem

/-! ## 1. `decrypt_prekey` `Ok` Tail (`r3b_recvP_from_dcc_placed`, `r3b_recvP_dec_ok_placed`) -/

set_option maxHeartbeats 800000 in
/-- Continuation from `R+0xdcc` (`R+0xdcc → R+0xde0 → R+0xf8c`, freeing `meG.name` if `cap ≠ 0`
and then `peerG.name` if `cap ≠ 0`). -/
theorem r3b_recvP_from_dcc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (pt : Bytes) (peerG meG : AddrGhost)
    {s0 s_dcc : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs_c1 : InRunPlaced R3bCodeOk s0 s_dcc 0xdcc)
    (hx19_c1 : s_dcc.readReg64 (.gpr 19#5) = g.stores)
    (hx20_c1 : s_dcc.readReg64 (.gpr 20#5) = g.res)
    (hx21_c1 : s_dcc.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28_c1 : s_dcc.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s_dcc.trace)
    (hhist : RunHistOk g.i s0 s_dcc)
    (hans : g.a = some (some (namedWrites g'.writes, pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : EnvAt g' pt (M.stepEvents (r3bFreeMePeerEvs meG peerG) st))
    (hjoin : JoinKPlacedEnv R3bCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s_dcc
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x208 ∗
        vecU8 A.repAlloc (runFsp s0 + 0x208#64) pt ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (runFsp s0 + 0x230#64) 16) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s_dcc ∗ anyHeap)
      Q Qp oom := by
  let fsp := runFsp s0
  by_cases hcapM : meG.name.cap = 0#64
  · have henv0 : EnvAt g' pt (M.stepEvents (r3bFreeCapEvs peerG.name.cap) st) := by
      simpa [r3bFreeMePeerEvs, r3bFreeCapEvs, hcapM] using henv
    have hpc1 : s_dcc.pc = runPcPlaced 0xdcc := hs_c1.pc
    rw [runPcPlaced_eq] at hpc1
    have hrun1 : s_dcc.status = .Running := hs_c1.run
    apply r3b_seq_lscro_oom (mid := runPcPlaced 0xde0) hs_c1.inv
    rw [runPcPlaced_eq]
    rw [hcapM] at hx21_c1
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, hrun1])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_d => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s_dcc (r3b_stOf hinv_d) hvm]
      have hs_d : InRunPlaced R3bCodeOk s0 (r3b_stOf hinv_d) 0xde0 :=
        r3b_inRun_step hs_c1 (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun1])
          (by simp only [r3b_stOf, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv_d
          (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
      have htr_d : (r3b_stOf hinv_d).trace = s_dcc.trace :=
        by simp only [r3b_stOf, wp_norm, arm64_norm]
      have hfs_d : (r3b_stOf hinv_d).fs = s_dcc.fs :=
        by simp only [r3b_stOf, wp_norm, arm64_norm]
      refine r3b_sepWPp_weaken_pre ?_
        (r3b_recvP_from_de0_placed g' pt peerG hh hext_le hsub64 hs_d
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19_c1])
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20_c1])
          (htr_d ▸ htr)
          (r3b_hist_of_eq htr_d (congrArg FsState.files hfs_d) hhist)
          hans hwr henv0 hjoin)
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono (r3b_nameHeap_zero A.repAlloc meG hcapM)
            (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                memRegion (fsp + 0x230#64) 16) ∗
              memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
              stackAt fsp (resStack - runFrame) ∗
              A.pool lim st (r3b_stOf hinv_d) ∗ anyHeap)))
          (by rw [emp_sepConj]))
        (by dsimp only [fsp]; sep_ac_rfl))
  · have hbeqM : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcapM
    have hbeq21 : (s_dcc.readReg64 (.gpr 21#5) == 0#64) = false := by rw [hx21_c1]; exact hbeqM
    have henv1 : EnvAt g' pt
        (M.stepEvents (r3bFreeCapEvs peerG.name.cap)
          (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st)) := by
      rw [← M.stepEvents_append]
      simpa [r3bFreeMePeerEvs, r3bFreeCapEvs, hcapM] using henv
    have hpc1 : s_dcc.pc = runPcPlaced 0xdcc := hs_c1.pc
    rw [runPcPlaced_eq] at hpc1
    have hrun1 : s_dcc.status = .Running := hs_c1.run
    have hsp1 : s_dcc.sp = fsp := hs_c1.sp
    have hsp_al1 : s_dcc.spAligned = true := hs_c1.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A.repAlloc meG hcapM))))))
    rw [show (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
          A.repAlloc.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s_dcc ∗ anyHeap) =
      ⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat ∗
          addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s_dcc ∗ anyHeap) by
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlayM
    apply r3b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hs_c1.inv
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun1])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c2 => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s_dcc (r3b_stOf hinv_c2) hvm]
      have hsp_c2 : (r3b_stOf hinv_c2).sp = s_dcc.sp :=
        by simp only [r3b_stOf, wp_norm, arm64_norm]
      have hstk_split := r3b_stackAt_split_ge s_dcc.sp hext_le hsub64
      refine r3b_call_lscro
        (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
            (resStack - runFrame - extHookStack) ∗
          anyHeap)
        (meG.name.ptr, meG.name.cap.toNat, 1, st)
        (r3b_dealloc_ok hh) hinv_c2
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun1])
        (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp_al1)
        (retAddr := runPcPlaced 0xde0)
        (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        ?_
        (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
      · dsimp only [Spec.keepsFs,
          LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        have hpure : (r3b_stOf hinv_c2).readReg64 .x0 = meG.name.ptr ∧
            ((r3b_stOf hinv_c2).readReg64 .x1).toNat = meG.name.cap.toNat ∧
            ((r3b_stOf hinv_c2).readReg64 .x2).toNat = 1 ∧
            RustLayoutOk meG.name.cap.toNat 1 ∧
            LsRetAddr624 ((r3b_stOf hinv_c2).readReg64 .lr) :=
          ⟨by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hx28_c1],
           by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hx21_c1],
           by simp only [r3b_stOf, wp_norm, arm64_norm],
           ⟨hlayM, by decide⟩,
           by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm]
              exact lsRetAddr624_blockPlacement_base_add 579 0xde0#64 (by decide) (by decide)⟩
        dsimp only [r3b_stOf] at hsp_c2
        rw [hsp_c2]
        rw [hsp1] at hstk_split ⊢
        rw [hstk_split]
        conv => rhs; rw [sepConj_assoc]
        refine Entails.pure_right hpure ?_
        exact Entails.of_eq (by dsimp only [fsp, r3b_stOf]; sep_ac_rfl)
      · dsimp only [Spec.keepsFs,
          LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        dsimp only [r3b_stOf] at hsp_c2
        rw [hsp_c2]
        rw [hsp1] at hstk_split ⊢
        simp only [← sepConj_assoc, pure_sepConj_pure]
        refine r3b_sepWPp_weaken_pre
          (P' := ⌜sm.fs = (r3b_stOf hinv_c2).fs ∧ sm.trace = (r3b_stOf hinv_c2).trace⌝ ∗
            (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                memRegion (fsp + 0x230#64) 16) ∗
              memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
              stackAt fsp (resStack - runFrame) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st) sm ∗
              anyHeap))
          (by rw [hstk_split]; dsimp only [fsp, r3b_stOf]; exact Entails.of_eq (by sep_ac_rfl)) ?_
        apply r3b_sepWPp_pure_left; rintro ⟨hfs_m, htr_m⟩
        have hs_m : InRunPlaced R3bCodeOk s0 sm 0xde0 :=
          r3b_inRun_step hs_c1 hpcm hrunm (hspm.trans hsp_c2)
            (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [wp_norm, arm64_norm])) hinv_m
            (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        have htr_m_eq : sm.trace = s_dcc.trace :=
          htr_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        have hfs_m_eq : sm.fs = s_dcc.fs :=
          hfs_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        exact r3b_recvP_from_de0_placed g' pt peerG hh hext_le hsub64 hs_m
          (hcsm.1.trans (by simp only [wp_norm, arm64_norm, hx19_c1]))
          (hcsm.2.1.trans (by simp only [wp_norm, arm64_norm, hx20_c1]))
          (htr_m_eq ▸ htr)
          (r3b_hist_of_eq htr_m_eq (congrArg FsState.files hfs_m_eq) hhist)
          hans hwr henv1 hjoin)

theorem r3b_recvP_from_dcc_placed_any [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (pt : Bytes) (peerG meG : AddrGhost)
    {s0 s_dcc : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs_c1 : InRunPlaced R3bCodeOk s0 s_dcc 0xdcc)
    (hx19_c1 : s_dcc.readReg64 (.gpr 19#5) = g.stores)
    (hx20_c1 : s_dcc.readReg64 (.gpr 20#5) = g.res)
    (hx21_c1 : s_dcc.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28_c1 : s_dcc.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s_dcc.trace)
    (hhist : RunHistOk g.i s0 s_dcc)
    (hans : g.a = some (some (namedWrites g'.writes, pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinKPlaced R3bCodeOk H A lim g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s_dcc
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x208 ∗
        vecU8 A.repAlloc (runFsp s0 + 0x208#64) pt ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (runFsp s0 + 0x230#64) 16) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s_dcc ∗ anyHeap)
      Q Qp oom :=
  r3b_recvP_from_dcc_placed (EnvAt := fun _ _ _ => True) g' pt peerG meG hh hext_le hsub64 hs_c1
    hx19_c1 hx20_c1 hx21_c1 hx28_c1 htr hhist hans hwr trivial
    (fun s' st' g'' out hat _ => hjoin s' st' g'' out hat)

set_option maxHeartbeats 800000 in
/-- `decrypt_prekey` `Ok(pt)` tail from `R+0xd94` (`R+0xd94 → R+0xdcc → R+0xde0 → R+0xf8c`
`AtJoinPlaced`). -/
theorem r3b_recvP_dec_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (pt : Bytes) (peerG meG : AddrGhost)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R3bCodeOk s0 s 0xd94)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : EnvAt g' pt (M.stepEvents (r3bFreeMePeerEvs meG peerG) st))
    (hjoin : JoinKPlacedEnv R3bCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        memRegion (runFsp s0 + 0x240#64) 0x20 ∗
        memRegion (runFsp s0 + 0x280#64) 0xa0 ∗
        decResAt A.repAlloc (runFsp s0 + 0x320#64) (.ok pt) ∗
        memRegion (runFsp s0 + 0x350#64) (runLocalBytes - 0x350) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  let fsp := runFsp s0
  have h220_split : memRegion fsp 0x220 =
      memRegion fsp 0x208 ∗
        memRegion (fsp + 0x208#64) 8 ∗ memRegion (fsp + 0x210#64) 8 ∗ memRegion (fsp + 0x218#64) 8 := by
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0x208) (k := 24) (b' := fsp + 0x208#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x208#64) (n := 8) (k := 16) (b' := fsp + 0x210#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x210#64) (n := 8) (k := 8) (b' := fsp + 0x218#64) rfl (by bv_omega) (by decide)]
  have h350_split : memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) =
      memRegion (fsp + 0x350#64) 0x30 ∗
        memRegion (fsp + 0x380#64) 8 ∗ memRegion (fsp + 0x388#64) 8 ∗
        memRegion (fsp + 0x390#64) (runLocalBytes - 0x390) := by
    rw [r3b_split_at fsp 0x350 0x30 runLocalBytes (by decide) (by decide),
        r3b_split_at fsp 0x380 8 runLocalBytes (by decide) (by decide),
        r3b_split_at fsp 0x388 8 runLocalBytes (by decide) (by decide)]
  have hprep :
      decResAt A.repAlloc (fsp + 0x320#64) (.ok pt) ∗
        (memRegion (fsp + 0x208#64) 8 ∗ memRegion (fsp + 0x210#64) 8 ∗ memRegion (fsp + 0x218#64) 8) ∗
        (memRegion (fsp + 0x380#64) 8 ∗ memRegion (fsp + 0x388#64) 8) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ∃∗ o0 : BitVec 64, ∃∗ o1 : BitVec 64, ∃∗ o2 : BitVec 64,
        ∃∗ s0w : BitVec 64, ∃∗ s1w : BitVec 64,
          ⌜cap.toNat < 2 ^ 63⌝ ∗
          ((fsp + 0x320#64) ↦₆₄ okTagVec) ∗
          ((fsp + 0x328#64) ↦₆₄ cap) ∗
          ((fsp + 0x330#64) ↦₆₄ ptr) ∗
          ((fsp + 0x338#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
          memRegion (fsp + 0x340#64) 16 ∗
          r3b_vecHeap A.repAlloc cap ptr pt ∗
          ((fsp + 0x208#64) ↦₆₄ o0) ∗ ((fsp + 0x210#64) ↦₆₄ o1) ∗ ((fsp + 0x218#64) ↦₆₄ o2) ∗
          ((fsp + 0x380#64) ↦₆₄ s0w) ∗ ((fsp + 0x388#64) ↦₆₄ s1w) ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x260#64) 32 ∗
          addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG := by
    dsimp only [decResAt, vecResultAt, vecU8]
    rw [ProofLib.memRegion_eight (fsp + 0x208#64), ProofLib.memRegion_eight (fsp + 0x210#64),
        ProofLib.memRegion_eight (fsp + 0x218#64), ProofLib.memRegion_eight (fsp + 0x380#64),
        ProofLib.memRegion_eight (fsp + 0x388#64),
        protocolAddressAt_eq_parts A.repAlloc peerG (fsp + 0x220#64),
        protocolAddressAt_eq_parts A.repAlloc meG (fsp + 0x260#64)]
    have hp_up : addrUpperAt (fsp + 0x220#64 + 16#64) peerG ⊢ memRegion (fsp + 0x230#64) 16 := by
      rw [show fsp + 0x220#64 + 16#64 = fsp + 0x230#64 by bv_omega]
      exact addrUpperAt_entails_memRegion _ _
    have hm_32 :
        ((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x260#64 + 8#64) ↦₆₄ meG.name.ptr) ∗
          addrUpperAt (fsp + 0x260#64 + 16#64) meG ⊢ memRegion (fsp + 0x260#64) 32 := by
      have hm_up : addrUpperAt (fsp + 0x260#64 + 16#64) meG ⊢ memRegion (fsp + 0x270#64) 16 := by
        rw [show fsp + 0x260#64 + 16#64 = fsp + 0x270#64 by bv_omega]
        exact addrUpperAt_entails_memRegion _ _
      rw [show fsp + 0x260#64 + 8#64 = fsp + 0x268#64 by bv_omega,
          ProofLib.memRegion_split' (b := fsp + 0x260#64) (n := 8) (k := 24)
            (b' := fsp + 0x268#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x268#64) (n := 8) (k := 16)
            (b' := fsp + 0x270#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) hm_up)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro s1w
    apply Entails.sepExists_elim; intro s0w
    apply Entails.sepExists_elim; intro o2
    apply Entails.sepExists_elim; intro o1
    apply Entails.sepExists_elim; intro o0
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    rw [r3b_vecU8At_eq A.repAlloc (fsp + 0x320#64 + 8#64) cap ptr pt]
    refine Entails.trans
      (r3b_perm
        (sepConj_mono (r3b_vecHeap_cap_lt A.repAlloc cap ptr pt)
          (sepConj_mono hp_up (sepConj_mono hm_32
            (Entails.refl (((fsp + 0x320#64) ↦₆₄ okTagVec) ∗
              ((fsp + 0x320#64 + 8#64) ↦₆₄ cap) ∗
              ((fsp + 0x320#64 + 8#64 + 8#64) ↦₆₄ ptr) ∗
              ((fsp + 0x320#64 + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
              memRegion (fsp + 0x320#64 + 32#64) 16 ∗
              ((fsp + 0x208#64) ↦₆₄ o0) ∗ ((fsp + 0x210#64) ↦₆₄ o1) ∗
              ((fsp + 0x218#64) ↦₆₄ o2) ∗
              ((fsp + 0x380#64) ↦₆₄ s0w) ∗ ((fsp + 0x388#64) ↦₆₄ s1w) ∗
              ((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x220#64 + 8#64) ↦₆₄ peerG.name.ptr) ∗
              addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG)))))
        (by ac_rfl)) ?_
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hcap_lt
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr
      (Entails.sepExists_right o0 (Entails.sepExists_right o1
        (Entails.sepExists_right o2 (Entails.sepExists_right s0w
          (Entails.sepExists_right s1w (Entails.pure_right hcap_lt ?_)))))))
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  rw [show runFsp s0 = fsp from rfl, h220_split, h350_split]
  apply r3b_sepWPp_weaken_pre
    (r3b_perm
      (sepConj_mono_left
        (Q := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗
          memRegion fsp 0x208 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          memRegion (fsp + 0x280#64) 0xa0 ∗
          memRegion (fsp + 0x350#64) 0x30 ∗
          memRegion (fsp + 0x390#64) (runLocalBytes - 0x390) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
        hprep)
      (by ac_rfl))
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro cap
  apply r3b_sepWPp_exists_left; intro ptr
  apply r3b_sepWPp_exists_left; intro o0
  apply r3b_sepWPp_exists_left; intro o1
  apply r3b_sepWPp_exists_left; intro o2
  apply r3b_sepWPp_exists_left; intro s0w
  apply r3b_sepWPp_exists_left; intro s1w
  rw [sepConj_assoc]
  apply r3b_sepWPp_pure_left; intro hcap_lt
  have hok3 : ((okTagVec + 3#64) == 0#64) = false := rfl
  have hok2 : ((okTagVec + 2#64) != 0#64) = false := rfl
  have hcap_cmn : ((cap + 1#64) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by intro h0; bv_omega)
  have hpc : s.pc = runPcPlaced 0xd94 := hs.pc
  rw [runPcPlaced_eq] at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hpack_c1 :
      (((fsp + 520#64) ↦₆₄ cap) ∗ ((fsp + 528#64) ↦₆₄ ptr) ∗
        ((fsp + 536#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗ r3b_vecHeap A.repAlloc cap ptr pt) ∗
      (((fsp + 800#64) ↦₆₄ okTagVec) ∗ ((fsp + 808#64) ↦₆₄ cap) ∗
        ((fsp + 816#64) ↦₆₄ ptr) ∗ ((fsp + 824#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (fsp + 832#64) 16 ∗
        memRegion (fsp + 576#64) 0x20 ∗ memRegion (fsp + 608#64) 32 ∗
        memRegion (fsp + 640#64) 0xa0 ∗ memRegion (fsp + 848#64) 0x30 ∗
        ((fsp + 896#64) ↦₆₄ ptr) ∗ ((fsp + 904#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (fsp + 912#64) (runLocalBytes - 0x390)) ⊢
      vecU8 A.repAlloc (fsp + 0x208#64) pt ∗ memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
    have hv :
        ((fsp + 520#64) ↦₆₄ cap) ∗ ((fsp + 528#64) ↦₆₄ ptr) ∗
          ((fsp + 536#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗ r3b_vecHeap A.repAlloc cap ptr pt ⊢
        vecU8 A.repAlloc (fsp + 0x208#64) pt := by
      dsimp only [vecU8]
      refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
      rw [r3b_vecU8At_eq A.repAlloc (fsp + 0x208#64) cap ptr pt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.refl _
    have hm320 :
        ((fsp + 800#64) ↦₆₄ okTagVec) ∗ ((fsp + 808#64) ↦₆₄ cap) ∗
          ((fsp + 816#64) ↦₆₄ ptr) ∗ ((fsp + 824#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
          memRegion (fsp + 832#64) 16 ⊢
        memRegion (fsp + 0x320#64) 48 := by
      have h32 := r3b_words4_entails_mem32 (fsp + 800#64) okTagVec cap ptr (BitVec.ofNat 64 pt.length)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h32
      rw [ProofLib.memRegion_split' (b := fsp + 0x320#64) (n := 32) (k := 16)
            (b' := fsp + 832#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left h32)
    have hm380 :
        ((fsp + 896#64) ↦₆₄ ptr) ∗ ((fsp + 904#64) ↦₆₄ BitVec.ofNat 64 pt.length) ⊢
        memRegion (fsp + 0x380#64) 16 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x380#64) (n := 8) (k := 8)
            (b' := fsp + 904#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
    have hback :
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) =
          memRegion (fsp + 576#64) 0x20 ∗
            (memRegion (fsp + 608#64) 32 ∗
              (memRegion (fsp + 640#64) 0xa0 ∗
                (memRegion (fsp + 0x320#64) 48 ∗
                  (memRegion (fsp + 848#64) 0x30 ∗
                    (memRegion (fsp + 0x380#64) 16 ∗
                      memRegion (fsp + 912#64) (runLocalBytes - 0x390)))))) := by
      rw [r3b_split_at fsp 0x240 0x20 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x260 32 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x280 0xa0 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x320 48 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x350 0x30 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x380 16 runLocalBytes (by decide) (by decide)]
    rw [hback]
    exact sepConj_mono hv
      (r3b_perm
        (r3b_perm_post
          (sepConj_mono hm320 (sepConj_mono hm380
            (Entails.refl (memRegion (fsp + 576#64) 0x20 ∗ memRegion (fsp + 608#64) 32 ∗
              memRegion (fsp + 640#64) 0xa0 ∗ memRegion (fsp + 848#64) 0x30 ∗
              memRegion (fsp + 912#64) (runLocalBytes - 0x390)))))
          (by ac_rfl))
        (by ac_rfl))
  apply r3b_seq_lscro_oom (mid := runPcPlaced 0xdcc) hs.inv
  rw [runPcPlaced_eq, ← hsp]
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c1 => ?_⟩
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    rw [← A.pool_transport lim st s (r3b_stOf hinv_c1) hvm]
    have hs_c1 : InRunPlaced R3bCodeOk s0 (r3b_stOf hinv_c1) 0xdcc :=
      r3b_inRun_step hs (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv_c1
        (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
    have hx19_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 19#5) = g.stores :=
      by simp only [r3b_stOf, wp_norm, arm64_norm, hx19]
    have hx20_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 20#5) = g.res :=
      by simp only [r3b_stOf, wp_norm, arm64_norm, hx20]
    have hx21_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 21#5) = meG.name.cap :=
      by simp only [r3b_stOf, wp_norm, arm64_norm, hx21]
    have hx28_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 28#5) = meG.name.ptr :=
      by simp only [r3b_stOf, wp_norm, arm64_norm, hx28]
    have htr_c1 : (r3b_stOf hinv_c1).trace = s.trace :=
      by simp only [r3b_stOf, wp_norm, arm64_norm]
    have hfs_c1 : (r3b_stOf hinv_c1).fs = s.fs :=
      by simp only [r3b_stOf, wp_norm, arm64_norm]
    refine r3b_sepWPp_weaken_pre ?_
      (r3b_recvP_from_dcc_placed g' pt peerG meG hh hext_le hsub64 hs_c1
        hx19_c1 hx20_c1 hx21_c1 hx28_c1
        (htr_c1 ▸ htr)
        (r3b_hist_of_eq htr_c1 (congrArg FsState.files hfs_c1) hhist)
        hans hwr henv hjoin)
    rw [hsp]
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono hpack_c1
          (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗
            runSaved s0 ∗
            memRegion fsp 0x208 ∗
            (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion (fsp + 0x230#64) 16) ∗
            stackAt fsp (resStack - runFrame) ∗
            A.pool lim st (r3b_stOf hinv_c1) ∗ anyHeap)))
        (by dsimp only [fsp]; sep_ac_rfl))
      (by dsimp only [fsp]; sep_ac_rfl))

theorem r3b_recvP_dec_ok_placed_any [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (pt : Bytes) (peerG meG : AddrGhost)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R3bCodeOk s0 s 0xd94)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinKPlaced R3bCodeOk H A lim g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        memRegion (runFsp s0 + 0x240#64) 0x20 ∗
        memRegion (runFsp s0 + 0x280#64) 0xa0 ∗
        decResAt A.repAlloc (runFsp s0 + 0x320#64) (.ok pt) ∗
        memRegion (runFsp s0 + 0x350#64) (runLocalBytes - 0x350) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom :=
  r3b_recvP_dec_ok_placed (EnvAt := fun _ _ _ => True) g' pt peerG meG hh hext_le hsub64 hs hx19
    hx20 hx21 hx28 htr hhist hans hwr trivial
    (fun s' st' g'' out hat _ => hjoin s' st' g'' out hat)


set_option maxHeartbeats 800000 in
/-- Continuation from `R+0xdcc` (`R+0xdcc → R+0xde0 → R+0xf8c`, freeing `meG.name` if `cap ≠ 0`
and then `peerG.name` if `cap ≠ 0`). -/
theorem r3b_recvP_from_dcc_placed_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (pt : Bytes) (peerG meG : AddrGhost)
    {s0 s_dcc : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs_c1 : InRunPlaced CodeOk s0 s_dcc 0xdcc)
    (hx19_c1 : s_dcc.readReg64 (.gpr 19#5) = g.stores)
    (hx20_c1 : s_dcc.readReg64 (.gpr 20#5) = g.res)
    (hx21_c1 : s_dcc.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28_c1 : s_dcc.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s_dcc.trace)
    (hhist : RunHistOk g.i s0 s_dcc)
    (hans : g.a = some (some (namedWrites g'.writes, pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : EnvAt g' pt (M.stepEvents (r3bFreeMePeerEvs meG peerG) st))
    (hjoin : JoinKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s_dcc
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x208 ∗
        vecU8 A.repAlloc (runFsp s0 + 0x208#64) pt ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (runFsp s0 + 0x230#64) 16) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s_dcc ∗ anyHeap)
      Q Qp oom := by
  let fsp := runFsp s0
  by_cases hcapM : meG.name.cap = 0#64
  · have henv0 : EnvAt g' pt (M.stepEvents (r3bFreeCapEvs peerG.name.cap) st) := by
      simpa [r3bFreeMePeerEvs, r3bFreeCapEvs, hcapM] using henv
    have hpc1 : s_dcc.pc = runPcPlaced 0xdcc := hs_c1.pc
    rw [runPcPlaced_eq] at hpc1
    have hrun1 : s_dcc.status = .Running := hs_c1.run
    apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := runPcPlaced 0xde0) hs_c1.inv
    rw [runPcPlaced_eq]
    rw [hcapM] at hx21_c1
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, hrun1])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_d => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s_dcc (r3b_stOf hinv_d) hvm]
      have hs_d : InRunPlaced CodeOk s0 (r3b_stOf hinv_d) 0xde0 :=
        r3b_inRun_step hs_c1 (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun1])
          (by simp only [r3b_stOf, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv_d
          (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
      have htr_d : (r3b_stOf hinv_d).trace = s_dcc.trace :=
        by simp only [r3b_stOf, wp_norm, arm64_norm]
      have hfs_d : (r3b_stOf hinv_d).fs = s_dcc.fs :=
        by simp only [r3b_stOf, wp_norm, arm64_norm]
      refine r3b_sepWPp_weaken_pre ?_
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudget.r3b_recvP_from_de0_placed_codeOk g' pt peerG hh hext_le hsub64 hs_d
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19_c1])
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20_c1])
          (htr_d ▸ htr)
          (r3b_hist_of_eq htr_d (congrArg FsState.files hfs_d) hhist)
          hans hwr henv0 hjoin)
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono (r3b_nameHeap_zero A.repAlloc meG hcapM)
            (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                memRegion (fsp + 0x230#64) 16) ∗
              memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
              stackAt fsp (resStack - runFrame) ∗
              A.pool lim st (r3b_stOf hinv_d) ∗ anyHeap)))
          (by rw [emp_sepConj]))
        (by dsimp only [fsp]; sep_ac_rfl))
  · have hbeqM : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcapM
    have hbeq21 : (s_dcc.readReg64 (.gpr 21#5) == 0#64) = false := by rw [hx21_c1]; exact hbeqM
    have henv1 : EnvAt g' pt
        (M.stepEvents (r3bFreeCapEvs peerG.name.cap)
          (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st)) := by
      rw [← M.stepEvents_append]
      simpa [r3bFreeMePeerEvs, r3bFreeCapEvs, hcapM] using henv
    have hpc1 : s_dcc.pc = runPcPlaced 0xdcc := hs_c1.pc
    rw [runPcPlaced_eq] at hpc1
    have hrun1 : s_dcc.status = .Running := hs_c1.run
    have hsp1 : s_dcc.sp = fsp := hs_c1.sp
    have hsp_al1 : s_dcc.spAligned = true := hs_c1.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A.repAlloc meG hcapM))))))
    rw [show (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
          A.repAlloc.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s_dcc ∗ anyHeap) =
      ⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat ∗
          addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s_dcc ∗ anyHeap) by
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlayM
    apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := lsρ lsRustDeallocSymCli) hs_c1.inv
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun1])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c2 => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s_dcc (r3b_stOf hinv_c2) hvm]
      have hsp_c2 : (r3b_stOf hinv_c2).sp = s_dcc.sp :=
        by simp only [r3b_stOf, wp_norm, arm64_norm]
      have hstk_split := r3b_stackAt_split_ge s_dcc.sp hext_le hsub64
      refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget.r3b_call_lscro_codeOk
        (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
            (resStack - runFrame - extHookStack) ∗
          anyHeap)
        (meG.name.ptr, meG.name.cap.toNat, 1, st)
        (r3b_dealloc_ok hh) hinv_c2
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun1])
        (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp_al1)
        (retAddr := runPcPlaced 0xde0)
        (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        ?_
        (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
      · dsimp only [Spec.keepsFs,
          LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        have hpure : (r3b_stOf hinv_c2).readReg64 .x0 = meG.name.ptr ∧
            ((r3b_stOf hinv_c2).readReg64 .x1).toNat = meG.name.cap.toNat ∧
            ((r3b_stOf hinv_c2).readReg64 .x2).toNat = 1 ∧
            RustLayoutOk meG.name.cap.toNat 1 ∧
            LsRetAddr624 ((r3b_stOf hinv_c2).readReg64 .lr) :=
          ⟨by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hx28_c1],
           by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hx21_c1],
           by simp only [r3b_stOf, wp_norm, arm64_norm],
           ⟨hlayM, by decide⟩,
           by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm]
              exact lsRetAddr624_blockPlacement_base_add 579 0xde0#64 (by decide) (by decide)⟩
        dsimp only [r3b_stOf] at hsp_c2
        rw [hsp_c2]
        rw [hsp1] at hstk_split ⊢
        rw [hstk_split]
        conv => rhs; rw [sepConj_assoc]
        refine Entails.pure_right hpure ?_
        exact Entails.of_eq (by dsimp only [fsp, r3b_stOf]; sep_ac_rfl)
      · dsimp only [Spec.keepsFs,
          LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        dsimp only [r3b_stOf] at hsp_c2
        rw [hsp_c2]
        rw [hsp1] at hstk_split ⊢
        simp only [← sepConj_assoc, pure_sepConj_pure]
        refine r3b_sepWPp_weaken_pre
          (P' := ⌜sm.fs = (r3b_stOf hinv_c2).fs ∧ sm.trace = (r3b_stOf hinv_c2).trace⌝ ∗
            (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                memRegion (fsp + 0x230#64) 16) ∗
              memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
              stackAt fsp (resStack - runFrame) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st) sm ∗
              anyHeap))
          (by rw [hstk_split]; dsimp only [fsp, r3b_stOf]; exact Entails.of_eq (by sep_ac_rfl)) ?_
        apply r3b_sepWPp_pure_left; rintro ⟨hfs_m, htr_m⟩
        have hs_m : InRunPlaced CodeOk s0 sm 0xde0 :=
          r3b_inRun_step hs_c1 hpcm hrunm (hspm.trans hsp_c2)
            (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [wp_norm, arm64_norm])) hinv_m
            (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        have htr_m_eq : sm.trace = s_dcc.trace :=
          htr_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        have hfs_m_eq : sm.fs = s_dcc.fs :=
          hfs_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        exact LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudget.r3b_recvP_from_de0_placed_codeOk g' pt peerG hh hext_le hsub64 hs_m
          (hcsm.1.trans (by simp only [wp_norm, arm64_norm, hx19_c1]))
          (hcsm.2.1.trans (by simp only [wp_norm, arm64_norm, hx20_c1]))
          (htr_m_eq ▸ htr)
          (r3b_hist_of_eq htr_m_eq (congrArg FsState.files hfs_m_eq) hhist)
          hans hwr henv1 hjoin)


set_option maxHeartbeats 800000 in
/-- `decrypt_prekey` `Ok(pt)` tail from `R+0xd94` (`R+0xd94 → R+0xdcc → R+0xde0 → R+0xf8c`
`AtJoinPlaced`). -/
theorem r3b_recvP_dec_ok_placed_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (pt : Bytes) (peerG meG : AddrGhost)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0xd94)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : EnvAt g' pt (M.stepEvents (r3bFreeMePeerEvs meG peerG) st))
    (hjoin : JoinKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        memRegion (runFsp s0 + 0x240#64) 0x20 ∗
        memRegion (runFsp s0 + 0x280#64) 0xa0 ∗
        decResAt A.repAlloc (runFsp s0 + 0x320#64) (.ok pt) ∗
        memRegion (runFsp s0 + 0x350#64) (runLocalBytes - 0x350) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  let fsp := runFsp s0
  have h220_split : memRegion fsp 0x220 =
      memRegion fsp 0x208 ∗
        memRegion (fsp + 0x208#64) 8 ∗ memRegion (fsp + 0x210#64) 8 ∗ memRegion (fsp + 0x218#64) 8 := by
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0x208) (k := 24) (b' := fsp + 0x208#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x208#64) (n := 8) (k := 16) (b' := fsp + 0x210#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x210#64) (n := 8) (k := 8) (b' := fsp + 0x218#64) rfl (by bv_omega) (by decide)]
  have h350_split : memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) =
      memRegion (fsp + 0x350#64) 0x30 ∗
        memRegion (fsp + 0x380#64) 8 ∗ memRegion (fsp + 0x388#64) 8 ∗
        memRegion (fsp + 0x390#64) (runLocalBytes - 0x390) := by
    rw [r3b_split_at fsp 0x350 0x30 runLocalBytes (by decide) (by decide),
        r3b_split_at fsp 0x380 8 runLocalBytes (by decide) (by decide),
        r3b_split_at fsp 0x388 8 runLocalBytes (by decide) (by decide)]
  have hprep :
      decResAt A.repAlloc (fsp + 0x320#64) (.ok pt) ∗
        (memRegion (fsp + 0x208#64) 8 ∗ memRegion (fsp + 0x210#64) 8 ∗ memRegion (fsp + 0x218#64) 8) ∗
        (memRegion (fsp + 0x380#64) 8 ∗ memRegion (fsp + 0x388#64) 8) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ∃∗ o0 : BitVec 64, ∃∗ o1 : BitVec 64, ∃∗ o2 : BitVec 64,
        ∃∗ s0w : BitVec 64, ∃∗ s1w : BitVec 64,
          ⌜cap.toNat < 2 ^ 63⌝ ∗
          ((fsp + 0x320#64) ↦₆₄ okTagVec) ∗
          ((fsp + 0x328#64) ↦₆₄ cap) ∗
          ((fsp + 0x330#64) ↦₆₄ ptr) ∗
          ((fsp + 0x338#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
          memRegion (fsp + 0x340#64) 16 ∗
          r3b_vecHeap A.repAlloc cap ptr pt ∗
          ((fsp + 0x208#64) ↦₆₄ o0) ∗ ((fsp + 0x210#64) ↦₆₄ o1) ∗ ((fsp + 0x218#64) ↦₆₄ o2) ∗
          ((fsp + 0x380#64) ↦₆₄ s0w) ∗ ((fsp + 0x388#64) ↦₆₄ s1w) ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x260#64) 32 ∗
          addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG := by
    dsimp only [decResAt, vecResultAt, vecU8]
    rw [ProofLib.memRegion_eight (fsp + 0x208#64), ProofLib.memRegion_eight (fsp + 0x210#64),
        ProofLib.memRegion_eight (fsp + 0x218#64), ProofLib.memRegion_eight (fsp + 0x380#64),
        ProofLib.memRegion_eight (fsp + 0x388#64),
        protocolAddressAt_eq_parts A.repAlloc peerG (fsp + 0x220#64),
        protocolAddressAt_eq_parts A.repAlloc meG (fsp + 0x260#64)]
    have hp_up : addrUpperAt (fsp + 0x220#64 + 16#64) peerG ⊢ memRegion (fsp + 0x230#64) 16 := by
      rw [show fsp + 0x220#64 + 16#64 = fsp + 0x230#64 by bv_omega]
      exact addrUpperAt_entails_memRegion _ _
    have hm_32 :
        ((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x260#64 + 8#64) ↦₆₄ meG.name.ptr) ∗
          addrUpperAt (fsp + 0x260#64 + 16#64) meG ⊢ memRegion (fsp + 0x260#64) 32 := by
      have hm_up : addrUpperAt (fsp + 0x260#64 + 16#64) meG ⊢ memRegion (fsp + 0x270#64) 16 := by
        rw [show fsp + 0x260#64 + 16#64 = fsp + 0x270#64 by bv_omega]
        exact addrUpperAt_entails_memRegion _ _
      rw [show fsp + 0x260#64 + 8#64 = fsp + 0x268#64 by bv_omega,
          ProofLib.memRegion_split' (b := fsp + 0x260#64) (n := 8) (k := 24)
            (b' := fsp + 0x268#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x268#64) (n := 8) (k := 16)
            (b' := fsp + 0x270#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) hm_up)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro s1w
    apply Entails.sepExists_elim; intro s0w
    apply Entails.sepExists_elim; intro o2
    apply Entails.sepExists_elim; intro o1
    apply Entails.sepExists_elim; intro o0
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    rw [r3b_vecU8At_eq A.repAlloc (fsp + 0x320#64 + 8#64) cap ptr pt]
    refine Entails.trans
      (r3b_perm
        (sepConj_mono (r3b_vecHeap_cap_lt A.repAlloc cap ptr pt)
          (sepConj_mono hp_up (sepConj_mono hm_32
            (Entails.refl (((fsp + 0x320#64) ↦₆₄ okTagVec) ∗
              ((fsp + 0x320#64 + 8#64) ↦₆₄ cap) ∗
              ((fsp + 0x320#64 + 8#64 + 8#64) ↦₆₄ ptr) ∗
              ((fsp + 0x320#64 + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
              memRegion (fsp + 0x320#64 + 32#64) 16 ∗
              ((fsp + 0x208#64) ↦₆₄ o0) ∗ ((fsp + 0x210#64) ↦₆₄ o1) ∗
              ((fsp + 0x218#64) ↦₆₄ o2) ∗
              ((fsp + 0x380#64) ↦₆₄ s0w) ∗ ((fsp + 0x388#64) ↦₆₄ s1w) ∗
              ((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x220#64 + 8#64) ↦₆₄ peerG.name.ptr) ∗
              addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG)))))
        (by ac_rfl)) ?_
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hcap_lt
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr
      (Entails.sepExists_right o0 (Entails.sepExists_right o1
        (Entails.sepExists_right o2 (Entails.sepExists_right s0w
          (Entails.sepExists_right s1w (Entails.pure_right hcap_lt ?_)))))))
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  rw [show runFsp s0 = fsp from rfl, h220_split, h350_split]
  apply r3b_sepWPp_weaken_pre
    (r3b_perm
      (sepConj_mono_left
        (Q := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗
          memRegion fsp 0x208 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          memRegion (fsp + 0x280#64) 0xa0 ∗
          memRegion (fsp + 0x350#64) 0x30 ∗
          memRegion (fsp + 0x390#64) (runLocalBytes - 0x390) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
        hprep)
      (by ac_rfl))
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro cap
  apply r3b_sepWPp_exists_left; intro ptr
  apply r3b_sepWPp_exists_left; intro o0
  apply r3b_sepWPp_exists_left; intro o1
  apply r3b_sepWPp_exists_left; intro o2
  apply r3b_sepWPp_exists_left; intro s0w
  apply r3b_sepWPp_exists_left; intro s1w
  rw [sepConj_assoc]
  apply r3b_sepWPp_pure_left; intro hcap_lt
  have hok3 : ((okTagVec + 3#64) == 0#64) = false := rfl
  have hok2 : ((okTagVec + 2#64) != 0#64) = false := rfl
  have hcap_cmn : ((cap + 1#64) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by intro h0; bv_omega)
  have hpc : s.pc = runPcPlaced 0xd94 := hs.pc
  rw [runPcPlaced_eq] at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hpack_c1 :
      (((fsp + 520#64) ↦₆₄ cap) ∗ ((fsp + 528#64) ↦₆₄ ptr) ∗
        ((fsp + 536#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗ r3b_vecHeap A.repAlloc cap ptr pt) ∗
      (((fsp + 800#64) ↦₆₄ okTagVec) ∗ ((fsp + 808#64) ↦₆₄ cap) ∗
        ((fsp + 816#64) ↦₆₄ ptr) ∗ ((fsp + 824#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (fsp + 832#64) 16 ∗
        memRegion (fsp + 576#64) 0x20 ∗ memRegion (fsp + 608#64) 32 ∗
        memRegion (fsp + 640#64) 0xa0 ∗ memRegion (fsp + 848#64) 0x30 ∗
        ((fsp + 896#64) ↦₆₄ ptr) ∗ ((fsp + 904#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (fsp + 912#64) (runLocalBytes - 0x390)) ⊢
      vecU8 A.repAlloc (fsp + 0x208#64) pt ∗ memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
    have hv :
        ((fsp + 520#64) ↦₆₄ cap) ∗ ((fsp + 528#64) ↦₆₄ ptr) ∗
          ((fsp + 536#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗ r3b_vecHeap A.repAlloc cap ptr pt ⊢
        vecU8 A.repAlloc (fsp + 0x208#64) pt := by
      dsimp only [vecU8]
      refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
      rw [r3b_vecU8At_eq A.repAlloc (fsp + 0x208#64) cap ptr pt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.refl _
    have hm320 :
        ((fsp + 800#64) ↦₆₄ okTagVec) ∗ ((fsp + 808#64) ↦₆₄ cap) ∗
          ((fsp + 816#64) ↦₆₄ ptr) ∗ ((fsp + 824#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
          memRegion (fsp + 832#64) 16 ⊢
        memRegion (fsp + 0x320#64) 48 := by
      have h32 := r3b_words4_entails_mem32 (fsp + 800#64) okTagVec cap ptr (BitVec.ofNat 64 pt.length)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h32
      rw [ProofLib.memRegion_split' (b := fsp + 0x320#64) (n := 32) (k := 16)
            (b' := fsp + 832#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left h32)
    have hm380 :
        ((fsp + 896#64) ↦₆₄ ptr) ∗ ((fsp + 904#64) ↦₆₄ BitVec.ofNat 64 pt.length) ⊢
        memRegion (fsp + 0x380#64) 16 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x380#64) (n := 8) (k := 8)
            (b' := fsp + 904#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
    have hback :
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) =
          memRegion (fsp + 576#64) 0x20 ∗
            (memRegion (fsp + 608#64) 32 ∗
              (memRegion (fsp + 640#64) 0xa0 ∗
                (memRegion (fsp + 0x320#64) 48 ∗
                  (memRegion (fsp + 848#64) 0x30 ∗
                    (memRegion (fsp + 0x380#64) 16 ∗
                      memRegion (fsp + 912#64) (runLocalBytes - 0x390)))))) := by
      rw [r3b_split_at fsp 0x240 0x20 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x260 32 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x280 0xa0 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x320 48 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x350 0x30 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x380 16 runLocalBytes (by decide) (by decide)]
    rw [hback]
    exact sepConj_mono hv
      (r3b_perm
        (r3b_perm_post
          (sepConj_mono hm320 (sepConj_mono hm380
            (Entails.refl (memRegion (fsp + 576#64) 0x20 ∗ memRegion (fsp + 608#64) 32 ∗
              memRegion (fsp + 640#64) 0xa0 ∗ memRegion (fsp + 848#64) 0x30 ∗
              memRegion (fsp + 912#64) (runLocalBytes - 0x390)))))
          (by ac_rfl))
        (by ac_rfl))
  apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := runPcPlaced 0xdcc) hs.inv
  rw [runPcPlaced_eq, ← hsp]
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c1 => ?_⟩
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    rw [← A.pool_transport lim st s (r3b_stOf hinv_c1) hvm]
    have hs_c1 : InRunPlaced CodeOk s0 (r3b_stOf hinv_c1) 0xdcc :=
      r3b_inRun_step hs (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv_c1
        (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
    have hx19_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 19#5) = g.stores :=
      by simp only [r3b_stOf, wp_norm, arm64_norm, hx19]
    have hx20_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 20#5) = g.res :=
      by simp only [r3b_stOf, wp_norm, arm64_norm, hx20]
    have hx21_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 21#5) = meG.name.cap :=
      by simp only [r3b_stOf, wp_norm, arm64_norm, hx21]
    have hx28_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 28#5) = meG.name.ptr :=
      by simp only [r3b_stOf, wp_norm, arm64_norm, hx28]
    have htr_c1 : (r3b_stOf hinv_c1).trace = s.trace :=
      by simp only [r3b_stOf, wp_norm, arm64_norm]
    have hfs_c1 : (r3b_stOf hinv_c1).fs = s.fs :=
      by simp only [r3b_stOf, wp_norm, arm64_norm]
    refine r3b_sepWPp_weaken_pre ?_
      (r3b_recvP_from_dcc_placed_codeOk g' pt peerG meG hh hext_le hsub64 hs_c1
        hx19_c1 hx20_c1 hx21_c1 hx28_c1
        (htr_c1 ▸ htr)
        (r3b_hist_of_eq htr_c1 (congrArg FsState.files hfs_c1) hhist)
        hans hwr henv hjoin)
    rw [hsp]
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono hpack_c1
          (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗
            runSaved s0 ∗
            memRegion fsp 0x208 ∗
            (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion (fsp + 0x230#64) 16) ∗
            stackAt fsp (resStack - runFrame) ∗
            A.pool lim st (r3b_stOf hinv_c1) ∗ anyHeap)))
        (by dsimp only [fsp]; sep_ac_rfl))
      (by dsimp only [fsp]; sep_ac_rfl))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudgetAux
