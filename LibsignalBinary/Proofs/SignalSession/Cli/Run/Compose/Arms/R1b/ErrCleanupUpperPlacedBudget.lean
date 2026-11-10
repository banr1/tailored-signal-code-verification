/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupSpkRegPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupUpperPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# Budget-Threaded Upper Error Cleanup Chain for Arm `R1b` (`2a60 → 2abc`)

Verifies the upper error cleanup lemmas (`2a60 → 2a78 → 2a88 → 2a8c → 2aa8 → 2abc`, emitting
`FreeOnlyEvs`) on Block `579` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupUpperPlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRejectPlaced Init1Data PanicK RejectKind r1b_CodeOk r1b_ErrCtxPlaced r1b_SpePayload
   r1b_SpePayload_plain r1b_StackBounds r1b_bind_state_placed r1b_cells2_to_region16
   r1b_errCommon r1b_errCore r1b_fsp_align r1b_region16_to_cells rejectMem runFsp
   runPcPlaced runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunDrop (PlainSpeTag)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (r1b_errCommon_atState_eq sepWP_with_vm_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
  (r1b_cleanup_2adc_placed r1b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

local syntax "by_vm_open " tacticSeq : tactic
local elab_rules : tactic
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

private def r1b_owned3_placed (A : RustAlloc)
    (kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64)
    (kpkBs spkBs regBs : List (BitVec 8)) : SepProp :=
  ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
  ownedBytes A spkCap spkPtr spkLen spkBs ∗
  ownedBytes A regCap regPtr regLen regBs

private theorem r1b_fold_owned3_placed (A : RustAlloc)
    (kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64)
    (kpkBs spkBs regBs : List (BitVec 8)) (R : SepProp) :
    ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
      ownedBytes A spkCap spkPtr spkLen spkBs ∗
      ownedBytes A regCap regPtr regLen regBs ∗ R =
      r1b_owned3_placed A kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen
        kpkBs spkBs regBs ∗ R := by
  dsimp only [r1b_owned3_placed]; simp only [sepConj_assoc]

private def r1b_mid9_placed
    (fsp spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 : BitVec 64) : SepProp :=
  ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
  memRegion (fsp + 0x178#64) 8 ∗
  ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
  ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
  ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0)

private theorem r1b_fold_mid9_placed
    (fsp spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 : BitVec 64) (R : SepProp) :
    ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (fsp + 0x178#64) 8 ∗
      ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
      ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
      ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ∗ R =
      r1b_mid9_placed fsp spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 ∗ R := by
  dsimp only [r1b_mid9_placed]; simp only [sepConj_assoc]

private def r1b_mid7_placed (fsp spkPtr spkCap regCap regPtr : BitVec 64) : SepProp :=
  ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
  memRegion (fsp + 0x178#64) 8 ∗
  memRegion (fsp + 0x188#64) 16 ∗
  ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
  memRegion (fsp + 0x1a8#64) 16

private theorem r1b_fold_mid7_placed
    (fsp spkPtr spkCap regCap regPtr : BitVec 64) (R : SepProp) :
    ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (fsp + 0x178#64) 8 ∗
      memRegion (fsp + 0x188#64) 16 ∗
      ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
      memRegion (fsp + 0x1a8#64) 16 ∗ R =
      r1b_mid7_placed fsp spkPtr spkCap regCap regPtr ∗ R := by
  dsimp only [r1b_mid7_placed]; simp only [sepConj_assoc]

local macro "r1b_step_ctx" "(" hc:term ")" "(" hsm:term ")" "(" hinv_m:term ")" : term =>
  `(($hc).of_step
    { pc := by simp only [$hsm:term, wp_norm, arm64_norm]
      run := by simp only [$hsm:term, wp_norm, arm64_norm, ($hc).st.run]
      sp := by simpa only [$hsm:term, wp_norm, arm64_norm] using ($hc).st.sp
      fp := by simpa only [$hsm:term, wp_norm, arm64_norm] using ($hc).st.fp
      inv := $hinv_m
      vregs := by simpa only [calleeSavedVRegs, $hsm:term, wp_norm, arm64_norm] using ($hc).st.vregs
      spAligned := ($hc).st.spAligned }
    (by simp only [$hsm:term, wp_norm, arm64_norm]) (by simp only [$hsm:term, wp_norm, arm64_norm])
    (by simp only [$hsm:term, wp_norm, arm64_norm]) (by simp only [$hsm:term, wp_norm, arm64_norm])
    (by simp only [$hsm:term, wp_norm, arm64_norm]))

theorem r1b_cleanup_2abc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v11c : BitVec 32}
    {v120 v158 v188 v190 v1a8 v1b0 : BitVec 64}
    {kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2abc)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc v158 (v11c.zeroExtend 64) v1b0
          (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ v120) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq, r1b_fold_owned3_placed]
  have hpc := hc.st.pc; have hrun := hc.st.run; have hsp : s.sp = fsp := hc.st.sp
  have hinv := hc.st.inv; have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  have hal4 : (fsp + 0x11c#64) &&& 3#64 = 0#64 := by bv_bits
  change s.pc = (blkPl_579).base + 0x2abc#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2adc#64) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm; rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2adc := r1b_step_ctx (hc) (hsm) (hinv_m)
    have hr12 : sm.readReg64 (.gpr 12#5) = v158 := by simp only [hsm, wp_norm, arm64_norm]
    have hr10 : sm.readReg64 (.gpr 10#5) = v11c.zeroExtend 64 := by simp only [hsm, wp_norm, arm64_norm]
    have hr23 : sm.readReg64 (.gpr 23#5) = v1b0 := by simp only [hsm, wp_norm, arm64_norm]
    have hr27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hr16 : sm.readReg64 (.gpr 16#5) = v190 := by simp only [hsm, wp_norm, arm64_norm]
    have hr14 : sm.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 24#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hr15 : sm.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 23#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hr28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hre11c : ((fsp + 0x11c#64) ↦₃₂ v11c) ⊢ memRegion (fsp + 0x11c#64) 4 := by
      rw [ProofLib.memRegion_four]; exact Entails.sepExists_right v11c (Entails.refl _)
    have hre120 : ((fsp + 0x120#64) ↦₆₄ v120) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ⊢
        memRegion (fsp + 0x120#64) 16 := by
      rw [show fsp + 0x128#64 = (fsp + 0x120#64) + 8#64 from by bv_omega]
      exact r1b_cells2_to_region16 _ _ _
    have hre150 : ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ⊢
        memRegion (fsp + 0x150#64) 16 := by
      rw [show fsp + 0x158#64 = (fsp + 0x150#64) + 8#64 from by bv_omega]
      exact r1b_cells2_to_region16 _ _ _
    have hre190 : ((fsp + 0x190#64) ↦₆₄ v190) ⊢ memRegion (fsp + 0x190#64) 8 :=
      pointsTo64_entails_memRegion _ _
    have hre1a8 : ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ⊢
        memRegion (fsp + 0x1a8#64) 16 := by
      rw [show fsp + 0x1b0#64 = (fsp + 0x1a8#64) + 8#64 from by bv_omega]
      exact r1b_cells2_to_region16 _ _ _
    refine sepWPp_weaken_pre ?_
      (r1b_cleanup_2adc_placed (st := st) (v188 := v188)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
        hh hdrop hbnd hc_m
        (by simp only [hsm, wp_norm, arm64_norm])
        (by simp only [hsm, wp_norm, arm64_norm]) hpanic hrej)
    rw [hr12, hr10, hr23, hr27, hr16, hr14, hr15, hr28]
    rw [r1b_errCommon_atState_eq, herrCore, r1b_fold_owned3_placed]
    dsimp only [fsp] at hre11c hre120 hre150 hre190 hre1a8 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      r1b_SpePayload A.repAlloc v158 (v11c.zeroExtend 64) v1b0
        (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
        (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
      r1b_owned3_placed A.repAlloc kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen
        kpkBs spkBs regBs ∗
      (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗ anyHeap) ∗
      memRegion (runFsp s0 + 0x110#64) 8 ∗
      ((runFsp s0 + 0x11c#64) ↦₃₂ v11c) ∗
      (((runFsp s0 + 0x120#64) ↦₆₄ v120) ∗ ((runFsp s0 + 0x128#64) ↦₆₄ kpkPtr)) ∗
      (((runFsp s0 + 0x150#64) ↦₆₄ kpkCap) ∗ ((runFsp s0 + 0x158#64) ↦₆₄ v158)) ∗
      ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (runFsp s0 + 0x178#64) 8 ∗
      ((runFsp s0 + 0x188#64) ↦₆₄ v188) ∗
      ((runFsp s0 + 0x190#64) ↦₆₄ v190) ∗
      ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
      (((runFsp s0 + 0x1a8#64) ↦₆₄ v1a8) ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ v1b0)) ∗
      memRegion (runFsp s0 + 0x4d0#64) 48 by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hre11c (sepConj_mono hre120 (sepConj_mono hre150
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono hre190 (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left hre1a8))))))))))))))
  )

theorem r1b_cleanup_2abc_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v11c : BitVec 32}
    {v120 v158 v188 v190 v1a8 v1b0 : BitVec 64}
    {kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2abc)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc v158 (v11c.zeroExtend 64) v1b0
          (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ v120) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  r1b_cleanup_2abc_placed hh hdrop hbnd hc hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

private theorem r1b_cleanup_2aa8_cap0_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v11c : BitVec 32}
    {v158 v188 v190 v1a8 v1b0 : BitVec 64}
    {opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2aa8)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc v158 (v11c.zeroExtend 64) v1b0
          (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A.repAlloc 0#64 opkPtr opkLen opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ 0#64) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq, r1b_fold_owned3_placed, r1b_fold_mid9_placed]
  have hpc := hc.st.pc; have hrun := hc.st.run; have hsp : s.sp = fsp := hc.st.sp
  have hinv := hc.st.inv; have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2aa8#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2abc#64) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm; rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2abc := r1b_step_ctx (hc) (hsm) (hinv_m)
    have hr27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hr24 : sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hr23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hr28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp only [hsm, wp_norm, arm64_norm]
    refine sepWPp_weaken_pre ?_
      (r1b_cleanup_2abc_placed (st := st)
        (v11c := v11c) (v120 := opkPtr) (v158 := v158) (v188 := v188)
        (v190 := v190) (v1a8 := v1a8) (v1b0 := v1b0)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
        hh hdrop hbnd hc_m hpanic hrej)
    rw [hr27, hr24, hr23, hr28, r1b_errCommon_atState_eq, herrCore]
    dsimp only [fsp]
    rw [r1b_fold_owned3_placed, r1b_fold_mid9_placed]
    have hdrop_opk : ownedBytes A.repAlloc 0#64 opkPtr opkLen opkBs ∗ anyHeap ⊢ anyHeap :=
      entails_anyHeap _
    have hre110 : ((runFsp s0 + 0x110#64) ↦₆₄ 0#64) ⊢ memRegion (runFsp s0 + 0x110#64) 8 :=
      pointsTo64_entails_memRegion _ _
    refine Entails.trans (Entails.of_eq (show _ =
      r1b_SpePayload A.repAlloc v158 (v11c.zeroExtend 64) v1b0
        (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
        (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
      r1b_owned3_placed A.repAlloc kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen
        kpkBs spkBs regBs ∗
      (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
        (ownedBytes A.repAlloc 0#64 opkPtr opkLen opkBs ∗ anyHeap)) ∗
      ((runFsp s0 + 0x110#64) ↦₆₄ 0#64) ∗ ((runFsp s0 + 0x11c#64) ↦₃₂ v11c) ∗
      ((runFsp s0 + 0x120#64) ↦₆₄ opkPtr) ∗ ((runFsp s0 + 0x128#64) ↦₆₄ kpkPtr) ∗
      ((runFsp s0 + 0x150#64) ↦₆₄ kpkCap) ∗ ((runFsp s0 + 0x158#64) ↦₆₄ v158) ∗
      r1b_mid9_placed (runFsp s0) spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 ∗
      memRegion (runFsp s0 + 0x4d0#64) 48 by dsimp only [r1b_owned3_placed]; sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hdrop_opk)))
        (sepConj_mono_left hre110)))
  )

set_option maxHeartbeats 400000 in
private theorem r1b_cleanup_2aa8_capNe_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v11c : BitVec 32}
    {v158 v188 v190 v1a8 v1b0 : BitVec 64}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2aa8)
    (hcap : opkCap ≠ 0#64)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc v158 (v11c.zeroExtend 64) v1b0
          (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq, r1b_fold_owned3_placed, r1b_fold_mid9_placed]
  have hpc := hc.st.pc; have hrun := hc.st.run; have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs; have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  have hcap_f : (opkCap == 0#64) = false := beq_false_of_ne hcap
  change s.pc = (blkPl_579).base + 0x2aa8#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm; rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hsm_sp0 : sm.sp = runFsp s0 := by simpa only [hsm, wp_norm, arm64_norm] using hc.st.sp
    have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa only [hsm, wp_norm, arm64_norm] using hfp
    have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hvregs
    have hsm_pc : sm.pc = lsρ lsRustDeallocSymCli := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2abc := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_run : sm.status = .Running := by simp only [hsm, wp_norm, arm64_norm, hrun]
    have hsm_a0 : sm.readReg64 .x0 = opkPtr := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_a1 : sm.readReg64 .x1 = opkCap := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_a2 : sm.readReg64 .x2 = 1#64 := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_x19 : sm.readReg64 (.gpr 19#5) = g.stores := by simpa only [hsm, wp_norm, arm64_norm] using hc.x19
    have hsm_x20 : sm.readReg64 (.gpr 20#5) = g.res := by simpa only [hsm, wp_norm, arm64_norm] using hc.x20
    have hsm_x21 : sm.readReg64 (.gpr 21#5) = d.meG.name.cap := by simpa only [hsm, wp_norm, arm64_norm] using hc.x21
    have hsm_r23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_r24 : sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_r27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_r28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_fs : sm.fs = s.fs := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_tr : sm.trace = s.trace := by simp only [hsm, wp_norm, arm64_norm]
    clear hsm; rw [← hfsp_eq]
    refine sepWPp_weaken_pre (P' :=
        ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
        (r1b_SpePayload A.repAlloc v158 (v11c.zeroExtend 64) v1b0
            (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
            (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
          r1b_owned3_placed A.repAlloc kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen
            kpkBs spkBs regBs ∗
          errCore ∗ anyHeap ∗
          ((runFsp s0 + 0x110#64) ↦₆₄ opkCap) ∗ ((runFsp s0 + 0x11c#64) ↦₃₂ v11c) ∗
          ((runFsp s0 + 0x120#64) ↦₆₄ opkPtr) ∗ ((runFsp s0 + 0x128#64) ↦₆₄ kpkPtr) ∗
          ((runFsp s0 + 0x150#64) ↦₆₄ kpkCap) ∗ ((runFsp s0 + 0x158#64) ↦₆₄ v158) ∗
          r1b_mid9_placed (runFsp s0) spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 ∗
          memRegion (runFsp s0 + 0x4d0#64) 48)) ?_ ?_
    · exact Entails.of_eq (by dsimp only [r1b_owned3_placed]; sep_ac_rfl)
    refine r1b_call_dealloc_ownedBytes_placed (Q := Q)
      (cap := opkCap) (ptr := opkPtr) (len := opkLen) (bs := opkBs)
      hh hbnd hinv_m hsm_pc hsm_run hsm_sp0 hsm_fp hsm_vr hsp0 hsm_lr
      hsm_a0 hsm_a1 hsm_a2 hcap hpanic ?_
    intro s1 hin1 hcs1 hfs1 htr1
    rcases hcs1 with ⟨hc19, hc20, hc21, _, hc24, hc25, _, _, hc28, hc29, _, _⟩
    have htr1' : s1.trace = s.trace := htr1.trans hsm_tr
    have hfs1' : s1.fs = s.fs := hfs1.trans hsm_fs
    have hc_f : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s1 0x2abc :=
      { st := hin1, x19 := hc19.trans hsm_x19, x20 := hc20.trans hsm_x20,
        x21 := hc21.trans hsm_x21, trace := htr1' ▸ hc.trace,
        hist := ⟨by rw [hfs1']; exact hc.hist.1, by rw [htr1']; exact hc.hist.2⟩, ans := hc.ans }
    have hr27 : s1.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := hc28.trans hsm_r27
    have hr24 : s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := hc25.trans hsm_r24
    have hr23 : s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := hc24.trans hsm_r23
    have hr28 : s1.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := hc29.trans hsm_r28
    have hre110 : ((runFsp s0 + 0x110#64) ↦₆₄ opkCap) ⊢ memRegion (runFsp s0 + 0x110#64) 8 :=
      pointsTo64_entails_memRegion _ _
    refine sepWPp_weaken_pre ?_
      (r1b_cleanup_2abc_placed (st := M.stepEvents (rustDeallocEvents opkCap.toNat 1) st)
        (v11c := v11c) (v120 := opkPtr) (v158 := v158) (v188 := v188)
        (v190 := v190) (v1a8 := v1a8) (v1b0 := v1b0)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
        hh hdrop hbnd hc_f hpanic fun sf2 evs2 hfo2 hrej2 => ?_)
    · rw [hr27, hr24, hr23, hr28]
      rw [r1b_errCommon_atState_eq, herrCore, r1b_fold_owned3_placed, r1b_fold_mid9_placed]
      refine Entails.trans (Entails.of_eq (show _ =
        r1b_SpePayload A.repAlloc v158 (v11c.zeroExtend 64) v1b0
          (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
        r1b_owned3_placed A.repAlloc kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen
          kpkBs spkBs regBs ∗
        (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents opkCap.toNat 1) st) s1 ∗ anyHeap) ∗
        ((runFsp s0 + 0x110#64) ↦₆₄ opkCap) ∗ ((runFsp s0 + 0x11c#64) ↦₃₂ v11c) ∗
        ((runFsp s0 + 0x120#64) ↦₆₄ opkPtr) ∗ ((runFsp s0 + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((runFsp s0 + 0x150#64) ↦₆₄ kpkCap) ∗ ((runFsp s0 + 0x158#64) ↦₆₄ v158) ∗
        r1b_mid9_placed (runFsp s0) spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 ∗
        memRegion (runFsp s0 + 0x4d0#64) 48 by sep_ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hre110)))
    · rw [← M.stepEvents_append]
      exact hrej sf2 (rustDeallocEvents opkCap.toNat 1 ++ evs2)
        (FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 opkCap.toNat) hfo2) hrej2
  )

theorem r1b_cleanup_2aa8_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v11c : BitVec 32}
    {v158 v188 v190 v1a8 v1b0 : BitVec 64}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2aa8)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc v158 (v11c.zeroExtend 64) v1b0
          (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  by_cases hcap : opkCap = 0#64
  · subst hcap; exact r1b_cleanup_2aa8_cap0_placed hh hdrop hbnd hc hpanic hrej
  · exact r1b_cleanup_2aa8_capNe_placed hh hdrop hbnd hc hcap hpanic hrej

theorem r1b_cleanup_2aa8_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v11c : BitVec 32}
    {v158 v188 v190 v1a8 v1b0 : BitVec 64}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2aa8)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc v158 (v11c.zeroExtend 64) v1b0
          (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  r1b_cleanup_2aa8_placed hh hdrop hbnd hc hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

theorem r1b_cleanup_2a8c_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2a8c)
    (hi : PlainSpeTag i)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ speWord i) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq, r1b_fold_owned3_placed, ProofLib.memRegion_four (fsp + 0x11c#64),
    r1b_region16_to_cells (fsp + 0x188#64), r1b_region16_to_cells (fsp + 0x1a8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun (v1b0 : BitVec 64) =>
    SepWPp.exists_elim fun (v1a8 : BitVec 64) => SepWPp.exists_elim fun (v190 : BitVec 64) =>
    SepWPp.exists_elim fun (v188 : BitVec 64) => SepWPp.exists_elim fun (v11c : BitVec 32) => ?_
  rw [show fsp + 0x188#64 + 8#64 = fsp + 0x190#64 from by bv_omega,
    show fsp + 0x1a8#64 + 8#64 = fsp + 0x1b0#64 from by bv_omega]
  have hpc := hc.st.pc; have hrun := hc.st.run; have hsp : s.sp = fsp := hc.st.sp
  have hinv := hc.st.inv; have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  have hal4 : (fsp + 0x11c#64) &&& 3#64 = 0#64 := by bv_bits
  change s.pc = (blkPl_579).base + 0x2a8c#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2aa8#64) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm; rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2aa8 := r1b_step_ctx (hc) (hsm) (hinv_m)
    have hr27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hr24 : sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hr23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by simp only [hsm, wp_norm, arm64_norm]
    have hr28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp only [hsm, wp_norm, arm64_norm]
    let w32 : BitVec 32 :=
      BitVec.truncate 32 (s.readReg64 (Reg.gpr 8#5)) |||
        (BitVec.truncate 32 (s.readReg64 (Reg.gpr 9#5)) &&& 255#32)
    refine sepWPp_weaken_pre ?_
      (r1b_cleanup_2aa8_placed (st := st)
        (v11c := w32) (v158 := speWord i)
        (v188 := BitVec.zeroExtend 64 w32) (v190 := BitVec.zeroExtend 64 w32)
        (v1a8 := v1b0) (v1b0 := s.readReg64 (Reg.gpr 8#5) >>> 32)
        (opkCap := opkCap) (opkPtr := opkPtr) (opkLen := opkLen) (opkBs := opkBs)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
        hh hdrop hbnd hc_m hpanic hrej)
    dsimp only [w32]
    rw [hr27, hr24, hr23, hr28, r1b_errCommon_atState_eq, herrCore]
    dsimp only [fsp, r1b_owned3_placed]
    rw [← emp_sepConj (ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗ _)]
    refine Entails.trans ?_
      (sepConj_mono_left (r1b_SpePayload_plain A.repAlloc hi _ _ _ _ _ _ _ _))
    exact Entails.of_eq (by sep_ac_rfl)
  )

theorem r1b_cleanup_2a8c_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2a8c)
    (hi : PlainSpeTag i)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ speWord i) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  r1b_cleanup_2a8c_placed hh hdrop hbnd hc hi hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

theorem r1b_cleanup_2a88_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2a88)
    (hi : PlainSpeTag i)
    (hx9 : s.readReg64 (.gpr 9#5) = speWord i)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq, r1b_fold_owned3_placed, r1b_fold_mid7_placed,
    ProofLib.memRegion_eight (fsp + 0x158#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v158 => ?_
  have hpc := hc.st.pc; have hrun := hc.st.run; have hsp : s.sp = fsp := hc.st.sp
  have hinv := hc.st.inv; have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2a88#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2a8c#64) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm; rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2a8c := r1b_step_ctx (hc) (hsm) (hinv_m)
    refine sepWPp_weaken_pre ?_
      (r1b_cleanup_2a8c_placed (st := st)
        (opkCap := opkCap) (opkPtr := opkPtr) (opkLen := opkLen) (opkBs := opkBs)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
        hh hdrop hbnd hc_m hi hpanic hrej)
    rw [r1b_errCommon_atState_eq, herrCore]
    dsimp only [fsp, r1b_owned3_placed, r1b_mid7_placed]
    exact Entails.of_eq (by sep_ac_rfl)
  )

theorem r1b_cleanup_2a88_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2a88)
    (hi : PlainSpeTag i)
    (hx9 : s.readReg64 (.gpr 9#5) = speWord i)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  r1b_cleanup_2a88_placed hh hdrop hbnd hc hi hx9 hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

theorem r1b_cleanup_2a78_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2a78)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq, r1b_fold_owned3_placed, r1b_fold_mid7_placed,
    ProofLib.memRegion_eight (fsp + 0x158#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v158 => ?_
  have hpc := hc.st.pc; have hrun := hc.st.run; have hsp : s.sp = fsp := hc.st.sp
  have hinv := hc.st.inv; have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2a78#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2a8c#64) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm; rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2a8c := r1b_step_ctx (hc) (hsm) (hinv_m)
    refine sepWPp_weaken_pre ?_
      (r1b_cleanup_2a8c_placed (st := st) (i := 10)
        (opkCap := opkCap) (opkPtr := opkPtr) (opkLen := opkLen) (opkBs := opkBs)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
        hh hdrop hbnd hc_m (by decide) hpanic hrej)
    rw [r1b_errCommon_atState_eq, herrCore]
    dsimp only [fsp, speWord, r1b_owned3_placed, r1b_mid7_placed]
    exact Entails.of_eq (by sep_ac_rfl)
  )

theorem r1b_cleanup_2a78_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2a78)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  r1b_cleanup_2a78_placed hh hdrop hbnd hc hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

theorem r1b_cleanup_2a60_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2a60)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  have hsplit4d0 : memRegion (fsp + 0x4d0#64) 48 =
      memRegion (fsp + 0x4d0#64) 9 ∗ (∃∗ b4d9 : BitVec 8, (fsp + 0x4d9#64) ↦₈ b4d9) ∗
        memRegion (fsp + 0x4da#64) 38 := by
    rw [show (48 : Nat) = 9 + 39 from rfl,
      ProofLib.memRegion_split (fsp + 0x4d0#64) 9 39 (by decide),
      show fsp + 0x4d0#64 + 9#64 = fsp + 0x4d9#64 from by bv_omega,
      show (39 : Nat) = 1 + 38 from rfl,
      ProofLib.memRegion_split (fsp + 0x4d9#64) 1 38 (by decide),
      show fsp + 0x4d9#64 + 1#64 = fsp + 0x4da#64 from by bv_omega,
      ProofLib.memRegion_one (fsp + 0x4d9#64)]
  rw [hfsp_eq, r1b_fold_owned3_placed, r1b_fold_mid7_placed,
    ProofLib.memRegion_eight (fsp + 0x158#64), hsplit4d0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun (b4d9 : BitVec 8) => SepWPp.exists_elim fun (v158 : BitVec 64) => ?_
  have hpc := hc.st.pc; have hrun := hc.st.run; have hsp : s.sp = fsp := hc.st.sp
  have hinv := hc.st.inv; have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2a60#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2a8c#64) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm; rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2a8c := r1b_step_ctx (hc) (hsm) (hinv_m)
    have hre4d0 : memRegion (fsp + 0x4d0#64) 9 ∗ ((fsp + 0x4d9#64) ↦₈ b4d9) ∗
        memRegion (fsp + 0x4da#64) 38 ⊢ memRegion (fsp + 0x4d0#64) 48 := by
      rw [hsplit4d0]
      exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right b4d9 (Entails.refl _)))
    refine sepWPp_weaken_pre ?_
      (r1b_cleanup_2a8c_placed (st := st) (i := 8)
        (opkCap := opkCap) (opkPtr := opkPtr) (opkLen := opkLen) (opkBs := opkBs)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
        hh hdrop hbnd hc_m (by decide) hpanic hrej)
    rw [r1b_errCommon_atState_eq, herrCore]
    dsimp only [fsp, speWord, r1b_owned3_placed, r1b_mid7_placed] at hre4d0 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (runFsp s0 + 0x4d0#64) 9 ∗ ((runFsp s0 + 0x4d9#64) ↦₈ b4d9) ∗
        memRegion (runFsp s0 + 0x4da#64) 38) ∗
      (ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗ anyHeap) ∗
        ((runFsp s0 + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
        ((runFsp s0 + 0x120#64) ↦₆₄ opkPtr) ∗ ((runFsp s0 + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((runFsp s0 + 0x150#64) ↦₆₄ kpkCap) ∗ ((runFsp s0 + 0x158#64) ↦₆₄ speWord 8) ∗
        ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (runFsp s0 + 0x178#64) 8 ∗
        memRegion (runFsp s0 + 0x188#64) 16 ∗
        ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (runFsp s0 + 0x1a8#64) 16) by dsimp only [speWord]; sep_ac_rfl))
      (Entails.trans (sepConj_mono_left hre4d0) (Entails.of_eq (by dsimp only [speWord]; sep_ac_rfl)))
  )

theorem r1b_cleanup_2a60_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2a60)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc opkCap opkPtr opkLen opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  r1b_cleanup_2a60_placed hh hdrop hbnd hc hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupUpperPlacedBudget
