/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JProofPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable Arm `J` Proof

Proves `run_hop_join_placed_ok` for `JPlacedBudget.RunHopJoinPlaced` on Block `579` under
`[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JProofPlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack memcpyName sessionMemcpyRegionSpec withStack)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (RunAnswer StoresGhost)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_550)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallW LsCodeInv RunCall addrWords callAt callHeap cliWrOk inputOf namedWrites ownedBytes
   runOkAt runResAt runResSize sepWPp_seq_codeOk stackAt_split_ge storesAt)
open CryptoVerification.SignalSession.Cli.MainHops.M5MovesHelpers
  (pointsToBytes_entails_memRegion storesAt_repack storesAt_unpack storesBytes
   storesBytes_length storesHeap storesStackAt storesStackAt_eq_bytes
   vecU8_unpack_ownedBytes)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtJoinPlaced AtRejectPlaced Bytes InRunPlaced RejectKind RunHistOk RunNeeds RunSem
   joinMem rejectMem runFsp runLocalBytes runLocals runLocalsFrom runPcPlaced
   runPcPlaced_eq runProgPlaced runProgPlaced_eq runSaved)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame runNeed)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
  (AllocContractsFsPlaced.dealloc_rocl AllocContractsFsPlaced.session_memcpy_region_rocl)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JPlacedBudget
  (RunHopJoinPlaced runJoinPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JProofPlacedBudgetAux
  (j_call_lscro_jp j_call_rocl_jp j_epi_jp j_files_of_trace_eq_jp
   j_fold_call_mem_assoc_jp j_hist_of_eq_jp j_inRun_step_jp j_joinPayloadBytes_jp
   j_joinPayloadBytes_length_jp j_join_carve_locals_jp j_join_rejoin_locals_jp
   j_msb_0_jp j_msb_8000_jp j_msb_8002_jp j_msb_8003_jp j_ownedBytes_dealloc_jp
   j_ownedBytes_zero_jp j_payload_eq_parts_jp j_pull_pure_jp j_pull_pure_r_jp
   j_rejPost_jp j_sepWPp_exists_left_jp j_sepWPp_mono_post_jp j_sepWPp_pure_left_jp
   j_sepWPp_weaken_pre_jp j_slt_1_0_jp j_slt_1_1_jp j_slt_1_2_jp j_slt_1_3_jp
   j_sp_sub_96_add_96_jp j_stOf_jp j_tail_dealloc_jp j_vecU8_repack_jp
   runJoinPostPlaced_step_free)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (sepWP_with_vm_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (runNeed_bounds_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresBudget
  (dropStoresSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunHooksPlaced dropStores_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustDeallocExternSpecWithStack)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_mi_subsPState64 conditionHolds_pl_subsPState64
  conditionHolds_eq_subsPState64 conditionHolds_gt_subsPState64
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64
attribute [local simp, local arm64_norm, local wp_norm]
  j_msb_0_jp j_msb_8000_jp j_msb_8002_jp j_msb_8003_jp
  j_slt_1_0_jp j_slt_1_1_jp j_slt_1_2_jp j_slt_1_3_jp j_sp_sub_96_add_96_jp

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
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

/-! ## Pre-Dispatch Reject (`R+0x124`) -/

private theorem j_rejPre_from_174_jp [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {g : RunCall} {w : CallW} {bs : List (BitVec 8)} {s0 s : State} {resStack : Nat}
    {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hrf : runFrame ≤ resStack) (hext : extHookStack ≤ resStack)
    (h64 : resStack ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 0x174)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call) (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s) (hans : g.a = some none)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        ownedBytes A.repAlloc w.w1 w.w2 w.w3 bs ∗
        (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.stores 320 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap))
      (runJoinPostPlaced CodeOk A lim g st resStack s0) Qp (fun _ => ⌜False⌝) := by
  have hpc : s.pc = runPcPlaced 0x174 := hs.pc
  have hrun : s.status = .Running := hs.run
  by_cases hcap : w.w1 = 0
  · have hcap64 : w.w1 = 0#64 := hcap
    apply j_sepWPp_weaken_pre_jp
      (sepConj_mono_right (sepConj_mono_left (j_ownedBytes_zero_jp A.repAlloc bs hcap)))
    rw [emp_sepConj]
    apply sepWPp_seq_codeOk (mid := runPcPlaced 0x2c84) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq, runPcPlaced_eq]
    change s.pc = (blkPl_579).base + 372#64 at hpc
    rw [hcap64]
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_e
    have hpool_e : A.pool lim st s = A.pool lim st (j_stOf_jp hinv_e) := by
      simp only [j_stOf_jp, wp_norm, arm64_norm]
    have hs_e : InRunPlaced CodeOk s0 (j_stOf_jp hinv_e) 0x2c84 :=
      j_inRun_step_jp hs (by simp only [j_stOf_jp, arm64_norm, runPcPlaced_eq, *])
        (by simp only [j_stOf_jp, arm64_norm, hrun]) (by simp only [j_stOf_jp, arm64_norm])
        (by simp only [j_stOf_jp, arm64_norm]) hinv_e
        (by simp only [j_stOf_jp, calleeSavedVRegs, arm64_norm])
    refine j_sepWPp_weaken_pre_jp ?_
      (j_epi_jp hrf h64 hs_e (by simpa only [j_stOf_jp, arm64_norm] using htr)
        (j_hist_of_eq_jp (s := s) (s' := j_stOf_jp hinv_e)
          (by simp only [j_stOf_jp, arm64_norm])
          (by simp only [j_stOf_jp, arm64_norm]) hhist)
        (by decide) hans.symm)
    rw [← hcap64, hpool_e]
    exact Entails.trans (j_fold_call_mem_assoc_jp g.call w _) (Entails.of_eq (by sep_ac_rfl))
  · have hbeq : (w.w1 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    apply j_sepWPp_weaken_pre_jp
      (sepConj_mono_right (sepConj_mono_left (j_ownedBytes_dealloc_jp A.repAlloc bs hcap)))
    rw [j_pull_pure_jp]
    apply j_sepWPp_pure_left_jp; intro hlay
    apply sepWPp_seq_codeOk (mid := runPcPlaced 0x180) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq, runPcPlaced_eq]
    change s.pc = (blkPl_579).base + 372#64 at hpc
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_t
    have hpool_t : A.pool lim st s = A.pool lim st (j_stOf_jp hinv_t) := by
      simp only [j_stOf_jp, wp_norm, arm64_norm]
    have hs_t : InRunPlaced CodeOk s0 (j_stOf_jp hinv_t) 0x180 :=
      j_inRun_step_jp hs (by simp only [j_stOf_jp, arm64_norm, runPcPlaced_eq, *])
        (by simp only [j_stOf_jp, arm64_norm, hrun]) (by simp only [j_stOf_jp, arm64_norm])
        (by simp only [j_stOf_jp, arm64_norm]) hinv_t
        (by simp only [j_stOf_jp, calleeSavedVRegs, arm64_norm])
    refine j_sepWPp_weaken_pre_jp ?_
      (j_tail_dealloc_jp hh hrf hext h64 hs_t
        (ptr := w.w2) (cap := w.w1)
        (by simp only [j_stOf_jp, arm64_norm]) (by simp only [j_stOf_jp, arm64_norm]) hlay
        (by simpa only [j_stOf_jp, arm64_norm] using htr)
        (j_hist_of_eq_jp (s := s) (s' := j_stOf_jp hinv_t)
          (by simp only [j_stOf_jp, arm64_norm])
          (by simp only [j_stOf_jp, arm64_norm]) hhist)
        hans hlr_ls)
    rw [hpool_t]
    exact Entails.trans (j_fold_call_mem_assoc_jp g.call w _) (Entails.of_eq (by sep_ac_rfl))

private theorem j_rejPre_from_160_jp [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {g : RunCall} {w : CallW} {bundle : List (BitVec 8)} {s0 s : State} {resStack : Nat}
    {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hrf : runFrame ≤ resStack) (hext : extHookStack ≤ resStack)
    (h64 : resStack ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 0x160)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call) (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s) (hans : g.a = some none)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        ownedBytes A.repAlloc w.w4 w.w5 w.w6 bundle ∗
        (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.stores 320 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap))
      (runJoinPostPlaced CodeOk A lim g st resStack s0) Qp (fun _ => ⌜False⌝) := by
  have hpc : s.pc = runPcPlaced 0x160 := hs.pc
  have hrun : s.status = .Running := hs.run
  by_cases hcap : w.w4 = 0
  · have hcap64 : w.w4 = 0#64 := hcap
    apply j_sepWPp_weaken_pre_jp
      (sepConj_mono_right (sepConj_mono_left (j_ownedBytes_zero_jp A.repAlloc bundle hcap)))
    rw [emp_sepConj]
    apply sepWPp_seq_codeOk (mid := runPcPlaced 0x2c84) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq, runPcPlaced_eq]
    change s.pc = (blkPl_579).base + 352#64 at hpc
    rw [hcap64]
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_e
    have hpool_e : A.pool lim st s = A.pool lim st (j_stOf_jp hinv_e) := by
      simp only [j_stOf_jp, wp_norm, arm64_norm]
    have hs_e : InRunPlaced CodeOk s0 (j_stOf_jp hinv_e) 0x2c84 :=
      j_inRun_step_jp hs (by simp only [j_stOf_jp, arm64_norm, runPcPlaced_eq, *])
        (by simp only [j_stOf_jp, arm64_norm, hrun]) (by simp only [j_stOf_jp, arm64_norm])
        (by simp only [j_stOf_jp, arm64_norm]) hinv_e
        (by simp only [j_stOf_jp, calleeSavedVRegs, arm64_norm])
    refine j_sepWPp_weaken_pre_jp ?_
      (j_epi_jp hrf h64 hs_e (by simpa only [j_stOf_jp, arm64_norm] using htr)
        (j_hist_of_eq_jp (s := s) (s' := j_stOf_jp hinv_e)
          (by simp only [j_stOf_jp, arm64_norm])
          (by simp only [j_stOf_jp, arm64_norm]) hhist)
        (by decide) hans.symm)
    rw [← hcap64, hpool_e]
    exact Entails.trans (j_fold_call_mem_assoc_jp g.call w _) (Entails.of_eq (by sep_ac_rfl))
  · have hbeq : (w.w4 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    apply j_sepWPp_weaken_pre_jp
      (sepConj_mono_right (sepConj_mono_left (j_ownedBytes_dealloc_jp A.repAlloc bundle hcap)))
    rw [j_pull_pure_jp]
    apply j_sepWPp_pure_left_jp; intro hlay
    apply sepWPp_seq_codeOk (mid := runPcPlaced 0x180) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq, runPcPlaced_eq]
    change s.pc = (blkPl_579).base + 352#64 at hpc
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_t
    have hpool_t : A.pool lim st s = A.pool lim st (j_stOf_jp hinv_t) := by
      simp only [j_stOf_jp, wp_norm, arm64_norm]
    have hs_t : InRunPlaced CodeOk s0 (j_stOf_jp hinv_t) 0x180 :=
      j_inRun_step_jp hs (by simp only [j_stOf_jp, arm64_norm, runPcPlaced_eq, *])
        (by simp only [j_stOf_jp, arm64_norm, hrun]) (by simp only [j_stOf_jp, arm64_norm])
        (by simp only [j_stOf_jp, arm64_norm]) hinv_t
        (by simp only [j_stOf_jp, calleeSavedVRegs, arm64_norm])
    refine j_sepWPp_weaken_pre_jp ?_
      (j_tail_dealloc_jp hh hrf hext h64 hs_t
        (ptr := w.w5) (cap := w.w4)
        (by simp only [j_stOf_jp, arm64_norm]) (by simp only [j_stOf_jp, arm64_norm]) hlay
        (by simpa only [j_stOf_jp, arm64_norm] using htr)
        (j_hist_of_eq_jp (s := s) (s' := j_stOf_jp hinv_t)
          (by simp only [j_stOf_jp, arm64_norm])
          (by simp only [j_stOf_jp, arm64_norm]) hhist)
        hans hlr_ls)
    rw [hpool_t]
    exact Entails.trans (j_fold_call_mem_assoc_jp g.call w _) (Entails.of_eq (by sep_ac_rfl))

private theorem j_rejPre_init_from_134_jp [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {g : RunCall} {w : CallW} {peer : AddrV} {bundle : List (BitVec 8)}
    {s0 s : State} {resStack : Nat} {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hrf : runFrame ≤ resStack)
    (hext_sub : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hext : extHookStack ≤ resStack) (h64 : resStack ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0x134) (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (hans : g.a = some none)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        (addrWords A.repAlloc peer w.w0 w.w1 w.w2 w.w3 ∗
          ownedBytes A.repAlloc w.w4 w.w5 w.w6 bundle) ∗
        (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.stores 320 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap))
      (runJoinPostPlaced CodeOk A lim g st resStack s0) Qp (fun _ => ⌜False⌝) := by
  unfold addrWords
  have hpure_init : ∀ {P Q : Prop} {X Y Z W : SepProp},
      X ∗ (((⌜P⌝ ∗ Y) ∗ ⌜Q⌝) ∗ Z) ∗ W = ⌜P⌝ ∗ (⌜Q⌝ ∗ (X ∗ Y ∗ Z ∗ W)) := by
    intros; sep_ac_rfl
  conv => arg 4; enter [2, 1, 1]; unfold ownedBytes
  rw [hpure_init]; clear hpure_init
  apply j_sepWPp_pure_left_jp; rintro ⟨_, hle0, hlt0, _⟩
  apply j_sepWPp_pure_left_jp; intro _
  have hpc : s.pc = runPcPlaced 0x134 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  by_cases hcap0 : w.w0 = 0
  · simp only [hcap0, ↓reduceIte, emp_sepConj]
    conv => arg 4; enter [1, 1]; change g.call ↦₆₄ 0#64
    apply sepWPp_seq_codeOk (mid := runPcPlaced 0x160) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq, runPcPlaced_eq]
    change s.pc = (blkPl_579).base + 308#64 at hpc
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_160
    have hpool_160 : A.pool lim st s = A.pool lim st (j_stOf_jp hinv_160) := by
      simp only [j_stOf_jp, wp_norm, arm64_norm]
    have hs_160 : InRunPlaced CodeOk s0 (j_stOf_jp hinv_160) 0x160 :=
      j_inRun_step_jp hs (by simp only [j_stOf_jp, arm64_norm, runPcPlaced_eq, *])
        (by simp only [j_stOf_jp, arm64_norm, hrun]) (by simp only [j_stOf_jp, arm64_norm])
        (by simp only [j_stOf_jp, arm64_norm]) hinv_160
        (by simp only [j_stOf_jp, calleeSavedVRegs, arm64_norm])
    refine j_sepWPp_weaken_pre_jp ?_
      (j_rejPre_from_160_jp hh hrf hext h64 hs_160 (w := w) (bundle := bundle)
        (by simp only [j_stOf_jp, arm64_norm, hx25])
        (by simpa only [j_stOf_jp, arm64_norm] using htr)
        (j_hist_of_eq_jp (s := s) (s' := j_stOf_jp hinv_160)
          (by simp only [j_stOf_jp, arm64_norm])
          (by simp only [j_stOf_jp, arm64_norm]) hhist)
        hans hlr_ls)
    rw [show w.w0 = 0#64 from hcap0, hpool_160]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hbeq0 : (w.w0 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hmsb0 : w.w0.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by omega)
    have hpos0 : 0 < w.w0.toNat :=
      Nat.pos_of_ne_zero fun h0 => hcap0 (BitVec.eq_of_toNat_eq h0)
    have hlay0 : RustLayoutOk w.w0.toNat 1 := ⟨⟨hpos0, ⟨0, rfl⟩, by omega⟩, by decide⟩
    have hpeer_mem :
        (if w.w0 = 0 then emp
         else A.live w.w1 w.w0.toNat 1 ∗ (w.w1 ↦ₛ peer.name) ∗
           memRegion (w.w1 + BitVec.ofNat 64 peer.name.length)
             (w.w0.toNat - peer.name.length)) ⊢
        A.live w.w1 w.w0.toNat 1 ∗ memRegion w.w1 w.w0.toNat := by
      simp only [hcap0, ↓reduceIte]
      have hmerge :
          memRegion w.w1 peer.name.length ∗
            memRegion (w.w1 + BitVec.ofNat 64 peer.name.length)
              (w.w0.toNat - peer.name.length) =
          memRegion w.w1 w.w0.toNat := by
        have hsum : peer.name.length + (w.w0.toNat - peer.name.length) = w.w0.toNat :=
          Nat.add_sub_of_le hle0
        simpa only [hsum] using
          (ProofLib.memRegion_split w.w1 peer.name.length
            (w.w0.toNat - peer.name.length) (by omega)).symm
      rw [← hmerge]
      exact sepConj_mono_right
        (sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion w.w1 peer.name))
    apply j_sepWPp_weaken_pre_jp (sepConj_mono_right (sepConj_mono_left hpeer_mem))
    apply sepWPp_seq_codeOk (mid := lsρ lsRustDeallocSymCli) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq]
    change s.pc = (blkPl_579).base + 308#64 at hpc
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_da
    have hpool_da : A.pool lim st s = A.pool lim st (j_stOf_jp hinv_da) := by
      simp only [j_stOf_jp, wp_norm, arm64_norm]
    have hstk_split := stackAt_split_ge (runFsp s0) hext_sub hsub64
    refine j_call_rocl_jp
      (F := ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        ownedBytes A.repAlloc w.w4 w.w5 w.w6 bundle ∗
        runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.stores 320 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
        memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
          (resStack - runFrame - extHookStack) ∗
        anyHeap)
      (x := (w.w1, w.w0.toNat, 1, st))
      (AllocContractsFsPlaced.dealloc_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs) hinv_da
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hrun])
      (by simpa only [State.spAligned, arm64_norm] using hsp_al)
      (retAddr := runPcPlaced 0x160)
      (by simp only [arm64_norm, runPcPlaced_eq, *])
      ?_
      (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
      simp only [sepConj_assoc]
      apply Entails.pure_right
        ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hlay0,
          by simp only [j_stOf_jp, arm64_norm, runPcPlaced_eq]; exact lsRetAddr624_blockPlacement_base_add 579 0x160#64 (by decide) (by decide)⟩
      have hsp_c : (j_stOf_jp hinv_da).sp = runFsp s0 := by simp only [j_stOf_jp, arm64_norm, hsp]
      rw [hsp_c, hpool_da, hstk_split]
      exact Entails.of_eq (by sep_ac_rfl)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
      simp only [sepConj_assoc]
      apply j_sepWPp_pure_left_jp; intro hfs_m
      apply j_sepWPp_pure_left_jp; intro htr_m
      have hsp_c : (j_stOf_jp hinv_da).sp = runFsp s0 := by simp only [j_stOf_jp, arm64_norm, hsp]
      rw [hsp_c]
      have hs_m : InRunPlaced CodeOk s0 sm 0x160 :=
        j_inRun_step_jp hs hpcm hrunm (hspm.trans (by simp only [j_stOf_jp, arm64_norm]))
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [j_stOf_jp, arm64_norm])) hinv_m
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [j_stOf_jp, calleeSavedVRegs, arm64_norm]))
      have hx25_m : sm.readReg64 (.gpr 25#5) = g.call :=
        hcsm.2.2.2.2.2.2.1.trans (by simp only [j_stOf_jp, arm64_norm, hx25])
      have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [j_stOf_jp, arm64_norm])
      have hfs_tot : sm.fs = s.fs := hfs_m.trans (by simp only [j_stOf_jp, arm64_norm])
      refine j_sepWPp_mono_post_jp
        (fun _ _ => runJoinPostPlaced_step_free (FreeOnlyEvs.singleton 1 w.w0.toNat))
        (j_sepWPp_weaken_pre_jp ?_
          (j_rejPre_from_160_jp (st := M.stepEvents (rustDeallocEvents w.w0.toNat 1) st)
            (w := w) (bundle := bundle) hh hrf hext h64 hs_m hx25_m
            (htr_tot ▸ htr)
            (j_hist_of_eq_jp htr_tot (congrArg FsState.files hfs_tot) hhist)
            hans hlr_ls))
      rw [hstk_split]
      exact Entails.of_eq (by sep_ac_rfl)

private theorem j_rejPre_addr_from_134_jp [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {g : RunCall} {w : CallW} {bs : List (BitVec 8)} {s0 s : State} {resStack : Nat}
    {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hrf : runFrame ≤ resStack) (hext : extHookStack ≤ resStack)
    (h64 : resStack ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 0x134)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call) (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s) (hans : g.a = some none)
    (hw0 : w.w0 = 0x8000000000000000#64 ∨
      w.w0 = 0x8000000000000002#64 ∨ w.w0 = 0x8000000000000003#64)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        ownedBytes A.repAlloc w.w1 w.w2 w.w3 bs ∗
        (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.stores 320 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap))
      (runJoinPostPlaced CodeOk A lim g st resStack s0) Qp (fun _ => ⌜False⌝) := by
  have hpc : s.pc = runPcPlaced 0x134 := hs.pc
  have hrun : s.status = .Running := hs.run
  rcases hw0 with hw0 | hw0 | hw0 <;>
  · apply sepWPp_seq_codeOk (mid := runPcPlaced 0x174) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq, runPcPlaced_eq]
    change s.pc = (blkPl_579).base + 308#64 at hpc
    rw [hw0]; wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_174
    have hpool_174 : A.pool lim st s = A.pool lim st (j_stOf_jp hinv_174) := by
      simp only [j_stOf_jp, wp_norm, arm64_norm]
    have hs_174 : InRunPlaced CodeOk s0 (j_stOf_jp hinv_174) 0x174 :=
      j_inRun_step_jp hs (by simp only [j_stOf_jp, arm64_norm, runPcPlaced_eq, *])
        (by simp only [j_stOf_jp, arm64_norm, hrun]) (by simp only [j_stOf_jp, arm64_norm])
        (by simp only [j_stOf_jp, arm64_norm]) hinv_174
        (by simp only [j_stOf_jp, calleeSavedVRegs, arm64_norm])
    refine j_sepWPp_weaken_pre_jp ?_
      (j_rejPre_from_174_jp hh hrf hext h64 hs_174 (w := w) (bs := bs)
        (by simp only [j_stOf_jp, arm64_norm, hx25]) (by simpa only [j_stOf_jp, arm64_norm] using htr)
        (j_hist_of_eq_jp (s := s) (s' := j_stOf_jp hinv_174)
          (by simp only [j_stOf_jp, arm64_norm])
          (by simp only [j_stOf_jp, arm64_norm]) hhist) hans hlr_ls)
    rw [← hw0, hpool_174]; exact Entails.of_eq (by sep_ac_rfl)

private theorem j_rejPre_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {s0 s : State}
    {resStack : Nat} {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hrf : runFrame ≤ resStack)
    (h96 : 96 + extHookStack ≤ resStack - runFrame) (hext_sub : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hext : extHookStack ≤ resStack)
    (h64 : resStack ≤ 2 ^ 64) (hr : AtRejectPlaced CodeOk g g' .preDispatch s0 s)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (rejectMem (A.atState lim st s) g g' .preDispatch s0 resStack)
      (runJoinPostPlaced CodeOk A lim g st resStack s0) Qp (fun _ => ⌜False⌝) := by
  have hs := hr.base; dsimp only [RejectKind.pcOff] at hs
  have hpc : s.pc = runPcPlaced 0x124 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hx19 : s.readReg64 (.gpr 19#5) = g.stores := hr.x19
  obtain ⟨hx20, hx25⟩ := hr.preRegs rfl
  have hrej_eq :
      rejectMem (A.atState lim st s) g g' .preDispatch s0 resStack =
      (memRegion g.res runResSize ∗ callAt A.repAlloc g.call g.c) ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ runLocals (runFsp s0) [] ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap := rfl
  rw [hrej_eq]
  have hres_split : memRegion g.res runResSize ⊢
      ∃∗ u0 : BitVec 64, (g.res ↦₆₄ u0) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    rw [show runResSize = 8 + (runResSize - 8) from rfl,
        ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide),
        ProofLib.memRegion_eight g.res, sepExists_sepConj_left]
    exact Entails.refl _
  apply j_sepWPp_weaken_pre_jp (sepConj_mono_left (sepConj_mono_left hres_split))
  rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply j_sepWPp_exists_left_jp; intro u0
  apply sepWPp_seq_codeOk (mid := (blkPl_550).base) hs.inv
  simp only [sepConj_assoc, runProgPlaced_eq]; change s.pc = (blkPl_579).base + 292#64 at hpc
  by_vm_open (
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, hrun])
    refine ⟨by simp only [wp_norm, arm64_norm], fun hvm_c hinv_c => ?_⟩
    have hpool_c := A.pool_transport lim st s (j_stOf_jp hinv_c) hvm_c
    refine j_call_lscro_jp
      (F := runResAt A.repAlloc cliWrOk g.res (some none) ∗ callAt A.repAlloc g.call g.c ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗ anyHeap)
      (x := (⟨g.stores, g'⟩, st))
      (dropStores_placed_ok (callerProg := runProgPlaced H) (i := 579)
        hh (resStack - runFrame) h96 hsub64) hinv_c
      (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, hrun])
      (by simpa only [State.spAligned, arm64_norm] using hsp_al)
      (retAddr := runPcPlaced 0x134) (by simp only [arm64_norm, runPcPlaced_eq]) ?_
      (hnext := fun sm hsteps_ds hinv_m hpcm hrunm hspm hcsm => ?_)
    · dsimp only [dropStoresSpec, runResAt]; simp only [sepConj_assoc]
      apply Entails.pure_right ⟨by simp only [arm64_norm],
        by simp only [j_stOf_jp, arm64_norm, runPcPlaced_eq]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add 579 0x134#64 (by decide) (by decide)⟩
      have hsp_c : (j_stOf_jp hinv_c).sp = runFsp s0 := by simp only [j_stOf_jp, arm64_norm, hsp]
      rw [hsp_c, hpool_c]; exact Entails.of_eq (by sep_ac_rfl)
    · dsimp only [dropStoresSpec]
      rw [sepExists_sepConj_left]
      apply j_sepWPp_exists_left_jp; intro evs
      simp only [sepConj_assoc]
      apply j_sepWPp_pure_left_jp; rintro ⟨htr_m, hfo_evs⟩
      have hsp_c : (j_stOf_jp hinv_c).sp = runFsp s0 := by simp only [j_stOf_jp, arm64_norm, hsp]
      rw [hsp_c]
      have hs_m : InRunPlaced CodeOk s0 sm 0x134 :=
        j_inRun_step_jp hs hpcm hrunm (hspm.trans (by simp only [j_stOf_jp, arm64_norm]))
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [j_stOf_jp, arm64_norm])) hinv_m
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [j_stOf_jp, calleeSavedVRegs, arm64_norm]))
      have hx25_m : sm.readReg64 (.gpr 25#5) = g.call :=
        hcsm.2.2.2.2.2.2.1.trans (by simp only [j_stOf_jp, arm64_norm, hx25])
      have hfiles_m : sm.fs.files = s.fs.files :=
        (j_files_of_trace_eq_jp (hh.fs (runProgPlaced H) 579) hsteps_ds htr_m).trans
          (by simp only [j_stOf_jp, arm64_norm])
      have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [j_stOf_jp, arm64_norm])
      have htr_134 : s0.trace <+: sm.trace := htr_tot ▸ hr.trace
      have hhist_134 : RunHistOk g.i s0 sm := j_hist_of_eq_jp htr_tot hfiles_m hr.hist
      have hans_134 : g.a = some none := hr.ans
      apply j_sepWPp_mono_post_jp (fun _ _ => runJoinPostPlaced_step_free hfo_evs)
      unfold callAt
      rw [show (memRegion g.stores 320 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          runResAt A.repAlloc cliWrOk g.res (some none) ∗
          (∃∗ w : CallW, (g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗
            ((g.call + 16#64) ↦₆₄ w.w2) ∗ ((g.call + 24#64) ↦₆₄ w.w3) ∗
            ((g.call + 32#64) ↦₆₄ w.w4) ∗ ((g.call + 40#64) ↦₆₄ w.w5) ∗
            ((g.call + 48#64) ↦₆₄ w.w6) ∗ callHeap A.repAlloc w g.c) ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗ anyHeap) =
        (∃∗ w : CallW,
          ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
              ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
              ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
            callHeap A.repAlloc w g.c ∗
            (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.stores 320 ∗
              (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
              stackAt (runFsp s0) (resStack - runFrame) ∗
              A.pool lim (M.stepEvents evs st) sm ∗ anyHeap)) by
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        exact congrArg SepProp.sepExists (funext fun _ => by sep_ac_rfl)]
      apply j_sepWPp_exists_left_jp; intro w
      rcases hc_eq : g.c with ⟨me, n⟩ | ⟨peer, bundle⟩ | ⟨peer⟩ | ⟨peer⟩
      · dsimp only [callHeap]; unfold addrWords
        rw [← hc_eq, j_pull_pure_jp]; apply j_sepWPp_pure_left_jp; rintro ⟨hw0, _⟩
        rw [j_pull_pure_r_jp]; apply j_sepWPp_pure_left_jp; intro _
        exact j_rejPre_addr_from_134_jp hh hrf hext h64 hs_m hx25_m htr_134 hhist_134 hans_134
          (Or.inl hw0) hlr_ls
      · dsimp only [callHeap]; rw [← hc_eq]
        exact j_rejPre_init_from_134_jp hh hrf hext_sub hsub64 hext h64 hs_m hx25_m
          htr_134 hhist_134 hans_134 hlr_ls
      · dsimp only [callHeap]; unfold addrWords
        rw [← hc_eq, j_pull_pure_jp]; apply j_sepWPp_pure_left_jp; intro hw0
        rw [j_pull_pure_r_jp]; apply j_sepWPp_pure_left_jp; intro _
        exact j_rejPre_addr_from_134_jp hh hrf hext h64 hs_m hx25_m htr_134 hhist_134 hans_134
          (Or.inr (Or.inl hw0)) hlr_ls
      · dsimp only [callHeap]; unfold addrWords
        rw [← hc_eq, j_pull_pure_jp]; apply j_sepWPp_pure_left_jp; intro hw0
        rw [j_pull_pure_r_jp]; apply j_sepWPp_pure_left_jp; intro _
        exact j_rejPre_addr_from_134_jp hh hrf hext h64 hs_m hx25_m htr_134 hhist_134 hans_134
          (Or.inr (Or.inr hw0)) hlr_ls
  )

/-! ## Accept Join (`R+0xf8c → lr`) -/

private theorem j_join_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {out : Bytes}
    {s0 s : State} {resStack : Nat} {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hrf : runFrame ≤ resStack)
    (hext_sub : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (h64 : resStack ≤ 2 ^ 64) (hj : AtJoinPlaced CodeOk g g' out s0 s) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (joinMem (A.atState lim st s) g g' out s0 resStack)
      (runJoinPostPlaced CodeOk A lim g st resStack s0) Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0
  have hs := hj.base
  have hpc : s.pc = runPcPlaced 0xf8c := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hx19 : s.readReg64 (.gpr 19#5) = g.stores := hj.x19
  have hx20 : s.readReg64 (.gpr 20#5) = g.res := hj.x20
  have hmc := AllocContractsFsPlaced.session_memcpy_region_rocl
    (prog := runProgPlaced H) (i := 579) hh.allocFs
    extHookStack (Nat.le_refl _) (by decide)
  have hstk_split := stackAt_split_ge fsp hext_sub hsub64
  have hjoin_eq :
      joinMem (A.atState lim st s) g g' out s0 resStack =
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        runLocals (runFsp s0) [(0x208, 24, vecU8 A.repAlloc (runFsp s0 + 0x208#64) out)] ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap := rfl
  rw [hjoin_eq]
  dsimp only [runLocals, runLocalsFrom, Nat.sub_zero]
  have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
  rw [show runFsp s0 = fsp from rfl, hz, show BitVec.ofNat 64 (0x208 + 24) = 0x220#64 from rfl]
  apply j_sepWPp_weaken_pre_jp
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono (storesAt_unpack A.repAlloc g.stores g')
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono
        (sepConj_mono_right (sepConj_mono
          (vecU8_unpack_ownedBytes A.repAlloc (fsp + 0x208#64) out)
          (j_join_carve_locals_jp fsp))) (Entails.refl _)))))))
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply j_sepWPp_exists_left_jp; intro u610; apply j_sepWPp_exists_left_jp; intro u618
  apply j_sepWPp_exists_left_jp; intro u620; apply j_sepWPp_exists_left_jp; intro outCap
  apply j_sepWPp_exists_left_jp; intro outPtr; apply j_sepWPp_exists_left_jp; intro ws
  set outLen := BitVec.ofNat 64 out.length
  rw [storesStackAt_eq_bytes]
  apply sepWPp_seq_codeOk (mid := lsρ memcpyName) hs.inv
  simp only [sepConj_assoc, runProgPlaced_eq]
  change s.pc = (blkPl_579).base + 3980#64 at hpc
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv_mc1
  have hpool_mc1 : A.pool lim st s = A.pool lim st (j_stOf_jp hinv_mc1) := by
    simp only [j_stOf_jp, wp_norm, arm64_norm]
  refine j_call_rocl_jp
    (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesHeap A.repAlloc ws g' ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion fsp 0x208 ∗
      ((fsp + 0x208#64) ↦₆₄ outCap) ∗ ((fsp + 0x210#64) ↦₆₄ outPtr) ∗
      ((fsp + 0x218#64) ↦₆₄ outLen) ∗ ownedBytes A.repAlloc outCap outPtr outLen out ∗
      memRegion (fsp + 0x220#64) 0x2b0 ∗ ((fsp + 0x610#64) ↦₆₄ u610) ∗
      ((fsp + 0x618#64) ↦₆₄ u618) ∗ ((fsp + 0x620#64) ↦₆₄ u620) ∗
      memRegion (fsp + 0x628#64) (runLocalBytes - 0x628) ∗
      memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame)) (resStack - runFrame - extHookStack) ∗
      A.pool lim st (j_stOf_jp hinv_mc1) ∗ anyHeap)
    (x := (fsp + 0x4d0#64, g.stores, storesBytes ws)) hmc hinv_mc1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    (by simpa only [State.spAligned, arm64_norm] using hsp_al)
    (retAddr := runPcPlaced 0xf9c) (by simp only [arm64_norm, runPcPlaced_eq]) ?_
    (hnext := fun s1 _ hinv1 hpc1 hrun1 hsp1 hcs1 => ?_)
  · dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [sepConj_assoc]
    apply Entails.pure_right
      ⟨by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm, storesBytes_length]⟩
    have hsp_c : (j_stOf_jp hinv_mc1).sp = fsp := by simp only [j_stOf_jp, arm64_norm, hsp]
    rw [hsp_c, hpool_mc1, storesBytes_length, hstk_split]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec]
    simp only [sepConj_assoc]
    apply j_sepWPp_pure_left_jp; intro hfs1
    apply j_sepWPp_pure_left_jp; intro hvm1
    apply j_sepWPp_pure_left_jp; rintro ⟨_, htr1⟩
    have hsp_c : (j_stOf_jp hinv_mc1).sp = fsp := by simp only [j_stOf_jp, arm64_norm, hsp]
    rw [hsp_c, ← A.pool_transport lim st (j_stOf_jp hinv_mc1) s1 hvm1]
    have hs1 : InRunPlaced CodeOk s0 s1 0xf9c :=
      j_inRun_step_jp hs hpc1 hrun1 (hsp1.trans (by simp only [j_stOf_jp, arm64_norm]))
        (hcs1.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [j_stOf_jp, arm64_norm])) hinv1
        (hcs1.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [j_stOf_jp, calleeSavedVRegs, arm64_norm]))
    have hx20_1 : s1.readReg64 (.gpr 20#5) = g.res :=
      hcs1.2.1.trans (by simp only [j_stOf_jp, arm64_norm, hx20])
    have htr1_eq : s1.trace = s.trace := htr1.trans (by simp only [j_stOf_jp, arm64_norm])
    have hfs1_eq : s1.fs = s.fs := hfs1.trans (by simp only [j_stOf_jp, arm64_norm])
    have hsp1_eq : s1.sp = fsp := hs1.sp
    have hsp1_al : s1.spAligned = true := hs1.spAligned_cur
    have hstores_mem : (g.stores ↦ₛ storesBytes ws) ⊢ memRegion g.stores 320 := by
      have h := pointsToBytes_entails_memRegion (storesBytes ws) g.stores
        (by simp [storesBytes_length])
      rwa [storesBytes_length] at h
    apply j_sepWPp_weaken_pre_jp (sepConj_mono_right (sepConj_mono_left hstores_mem))
    apply sepWPp_seq_codeOk (mid := lsρ memcpyName) hs1.inv
    have hpcm1 : s1.pc = runPcPlaced 0xf9c := hs1.pc
    rw [runProgPlaced_eq]
    change s1.pc = (blkPl_579).base + 3996#64 at hpcm1
    by_vm_open (
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun1])
      refine ⟨by simp only [wp_norm, arm64_norm], fun hvm_mc2 hinv_mc2 => ?_⟩
      have hpool_mc2 := A.pool_transport lim st s1 (j_stOf_jp hinv_mc2) hvm_mc2
      let payload := j_joinPayloadBytes_jp ws outCap outPtr outLen
      refine j_call_rocl_jp
        (F := memRegion g.stores 320 ∗ memRegion g.call 56 ∗ storesHeap A.repAlloc ws g' ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion fsp 0x208 ∗
          ((fsp + 0x208#64) ↦₆₄ outCap) ∗ ((fsp + 0x210#64) ↦₆₄ outPtr) ∗
          ((fsp + 0x218#64) ↦₆₄ outLen) ∗ ownedBytes A.repAlloc outCap outPtr outLen out ∗
          memRegion (fsp + 0x220#64) 0x2b0 ∗ memRegion (fsp + 0x628#64) (runLocalBytes - 0x628) ∗
          memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame)) (resStack - runFrame - extHookStack) ∗
          A.pool lim st (j_stOf_jp hinv_mc2) ∗ anyHeap)
        (x := (g.res, fsp + 0x4d0#64, payload)) hmc hinv_mc2
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun1])
        (by simpa only [State.spAligned, arm64_norm] using hsp1_al)
        (retAddr := runPcPlaced 0xfc0) (by simp only [arm64_norm, runPcPlaced_eq]) ?_
        (hnext := fun s2 _ hinv2 hpc2 hrun2 hsp2 hcs2 => ?_)
      · dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec,
          sessionMemcpyRegionSpec, memcpyRegionSpec]
        simp only [sepConj_assoc]
        apply Entails.pure_right
          ⟨by simp only [arm64_norm], by simp only [arm64_norm],
            by simp only [arm64_norm, payload, j_joinPayloadBytes_length_jp, runResSize]⟩
        have hsp_c2 : (j_stOf_jp hinv_mc2).sp = fsp := by simp only [j_stOf_jp, arm64_norm, hsp1_eq]
        rw [hsp_c2, hpool_mc2]; dsimp only [payload]
        rw [j_joinPayloadBytes_length_jp,
            j_payload_eq_parts_jp (fsp + 0x4d0#64) ws outCap outPtr outLen]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by sep_ac_rfl)
      · dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec]
        simp only [sepConj_assoc]
        apply j_sepWPp_pure_left_jp; intro hfs2
        apply j_sepWPp_pure_left_jp; intro hvm2
        apply j_sepWPp_pure_left_jp; rintro ⟨_, htr2⟩
        have hsp_c2 : (j_stOf_jp hinv_mc2).sp = fsp := by simp only [j_stOf_jp, arm64_norm, hsp1_eq]
        rw [hsp_c2, ← A.pool_transport lim st (j_stOf_jp hinv_mc2) s2 hvm2]
        have hs2 : InRunPlaced CodeOk s0 s2 0xfc0 :=
          j_inRun_step_jp hs1 hpc2 hrun2 (hsp2.trans (by simp only [j_stOf_jp, arm64_norm]))
            (hcs2.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [j_stOf_jp, arm64_norm])) hinv2
            (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [j_stOf_jp, calleeSavedVRegs, arm64_norm]))
        have htr2_eq : s2.trace = s.trace :=
          (htr2.trans (by simp only [j_stOf_jp, arm64_norm])).trans htr1_eq
        have hfs2_eq : s2.fs = s.fs :=
          (hfs2.trans (by simp only [j_stOf_jp, arm64_norm])).trans hfs1_eq
        apply sepWPp_seq_codeOk (mid := runPcPlaced 0x2c84) hs2.inv
        have hpcm2 : s2.pc = runPcPlaced 0xfc0 := hs2.pc
        rw [runProgPlaced_eq, runPcPlaced_eq]
        change s2.pc = (blkPl_579).base + 4032#64 at hpcm2
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun2])
        intro hinv_e
        have hpool_e : A.pool lim st s2 = A.pool lim st (j_stOf_jp hinv_e) := by
          simp only [j_stOf_jp, wp_norm, arm64_norm]
        have hs_e : InRunPlaced CodeOk s0 (j_stOf_jp hinv_e) 0x2c84 :=
          j_inRun_step_jp hs2 (by simp only [j_stOf_jp, arm64_norm, runPcPlaced_eq, *])
            (by simp only [j_stOf_jp, arm64_norm, hrun2]) (by simp only [j_stOf_jp, arm64_norm])
            (by simp only [j_stOf_jp, arm64_norm]) hinv_e
            (by simp only [j_stOf_jp, calleeSavedVRegs, arm64_norm])
        have htr_e : (j_stOf_jp hinv_e).trace = s.trace :=
          (by simp only [j_stOf_jp, arm64_norm] : (j_stOf_jp hinv_e).trace = s2.trace).trans htr2_eq
        have hfs_e : (j_stOf_jp hinv_e).fs = s.fs :=
          (by simp only [j_stOf_jp, arm64_norm] : (j_stOf_jp hinv_e).fs = s2.fs).trans hfs2_eq
        let a' : RunAnswer := some (some (namedWrites g'.writes, out))
        have hres_repack :
            (g.res ↦ₛ payload) ∗ storesHeap A.repAlloc ws g' ∗
              ownedBytes A.repAlloc outCap outPtr outLen out ⊢
            runResAt A.repAlloc cliWrOk g.res a' := by
          dsimp only [payload, a', runResAt, runOkAt]
          rw [j_payload_eq_parts_jp g.res ws outCap outPtr outLen, ← storesStackAt_eq_bytes]
          have hok :
              (storesStackAt g.res ws ∗ storesHeap A.repAlloc ws g') ∗
                (((g.res + 0x140#64) ↦₆₄ outCap) ∗ ((g.res + 0x140#64 + 0x08#64) ↦₆₄ outPtr) ∗
                  ((g.res + 0x140#64 + 0x10#64) ↦₆₄ outLen) ∗
                  ownedBytes A.repAlloc outCap outPtr outLen out) ⊢
              storesAt A.repAlloc g.res g' ∗ vecU8 A.repAlloc (g.res + 0x140#64) out :=
            sepConj_mono (storesAt_repack A.repAlloc g.res ws g')
              (j_vecU8_repack_jp A.repAlloc (g.res + 0x140#64) outCap outPtr out)
          refine Entails.trans (Entails.of_eq ?_)
            (Entails.trans hok
              (Entails.sepExists_right g' (Entails.pure_right ⟨rfl, hj.wrOk⟩ (Entails.refl _))))
          simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl
        have hloc_rejoin := j_join_rejoin_locals_jp fsp outCap outPtr outLen ws
        refine j_sepWPp_weaken_pre_jp ?_
          (j_epi_jp (a' := a') hrf h64 hs_e (htr_e ▸ hj.trace)
            (j_hist_of_eq_jp htr_e (congrArg FsState.files hfs_e) hj.hist)
            (Option.some_ne_none _) hj.ans.symm)
        rw [hstk_split, hpool_e]
        refine Entails.trans (Entails.of_eq (show _ =
          ((g.res ↦ₛ payload) ∗ storesHeap A.repAlloc ws g' ∗
            ownedBytes A.repAlloc outCap outPtr outLen out) ∗
          (memRegion fsp 0x208 ∗ ((fsp + 0x208#64) ↦₆₄ outCap) ∗ ((fsp + 0x210#64) ↦₆₄ outPtr) ∗
            ((fsp + 0x218#64) ↦₆₄ outLen) ∗ memRegion (fsp + 0x220#64) 0x2b0 ∗
            ((fsp + 0x4d0#64) ↦ₛ payload) ∗ memRegion (fsp + 0x628#64) (runLocalBytes - 0x628)) ∗
          (memRegion g.call 56 ∗ memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
            memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
              (resStack - runFrame - extHookStack) ∗
            stackAt fsp extHookStack ∗ A.pool lim st (j_stOf_jp hinv_e) ∗ anyHeap) by
          dsimp only [payload]; sep_ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hres_repack (sepConj_mono_left hloc_rejoin)) ?_
        exact Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl)
    )

/-! ## Top-Level `run_hop_join_placed_ok` -/

theorem run_hop_join_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem}
    {needs : RunNeeds} {resStack : Nat} :
    RunHopJoinPlaced CodeOk A lim sEnvs H B S needs resStack := by
  intro g st s0 s P Qp hh hres hres64 hlr_ls hstate
  have hbnds := runNeed_bounds_placed (A := A) (lim := lim) (envs := sEnvs) hres hres64
  have hrf : runFrame ≤ resStack := by omega
  have h96 : 96 + extHookStack ≤ resStack - runFrame := by omega
  have hext_sub : extHookStack ≤ resStack - runFrame := by omega
  have hext : extHookStack ≤ resStack := by omega
  have hsub64 : resStack - runFrame ≤ 2 ^ 64 := by omega
  have h64 : resStack ≤ 2 ^ 64 := by omega
  rcases hstate with ⟨g', out, hj, rfl⟩ | ⟨g', rk, hr, rfl⟩
  · exact j_join_jp hh hrf hext_sub hsub64 h64 hj
  · cases rk with
    | preDispatch => exact j_rejPre_jp hh hrf h96 hext_sub hsub64 hext h64 hr hlr_ls
    | postDispatch => exact j_rejPost_jp hh hrf h96 hsub64 h64 hr

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JProofPlacedBudget
